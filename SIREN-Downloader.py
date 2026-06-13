"""
明日方舟塞壬唱片下载器 (Python GUI 多线程版)
功能：
- 获取网站全部专辑，可勾选所需专辑进行下载
- 自定义歌曲命名模板，支持 {album} {title} {artist} 等变量
- 多线程并发下载，可配置最大线程数
- 可设置全局下载速度限制 (KB/s)
- 可自动为每个专辑创建子文件夹（文件夹名也经严格清理）
- 实时显示总进度、当前文件进度与下载速度
- 支持同时下载对应的 LRC 歌词
- 自动跳过已存在的文件（下载时实时检查，无需预扫描）
- 扫描目录按钮：极速扫描，将已完整下载的专辑自动勾选并锁定
- 进度条不回退，界面不卡顿
- 文件名/文件夹名：英文冒号→中文冒号，删除末尾点号和空格，过滤非法字符
- 搜索歌曲功能：独立窗口展示结果，双击勾选专辑，右键查看专辑歌曲
- 下载失败时结束后弹窗汇总错误原因
- 扫描规则：只要生成的完整文件名在对应位置存在即视为已下载
"""

import os
import re
import time
import queue
import threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import requests

# -------------------- 全局配置 --------------------
BASE_URL = "https://monster-siren.hypergryph.com"
HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
}
CHUNK_SIZE = 1024 * 8             # 下载流块大小
# -------------------------------------------------

class SpeedLimiter:
    """简单的令牌桶速度限制器"""
    def __init__(self, limit_kbps=0):
        self.limit = limit_kbps * 1024
        self.bucket = 0.0
        self.last_time = time.time()
        self.lock = threading.Lock()

    def set_limit(self, limit_kbps):
        self.limit = limit_kbps * 1024
        with self.lock:
            self.bucket = 0.0
            self.last_time = time.time()

    def acquire(self, bytes_to_add):
        if self.limit <= 0:
            return
        with self.lock:
            now = time.time()
            elapsed = now - self.last_time
            self.bucket += elapsed * self.limit
            if self.bucket > self.limit:
                self.bucket = self.limit
            self.last_time = now
            if bytes_to_add <= self.bucket:
                self.bucket -= bytes_to_add
            else:
                deficit = bytes_to_add - self.bucket
                wait_time = deficit / self.limit
                time.sleep(wait_time)
                self.bucket = 0.0
                self.last_time = time.time()

class SirenDownloader:
    def __init__(self, root):
        self.root = root
        self.root.title("塞壬唱片下载器")
        self.root.geometry("700x650")
        self.root.resizable(True, True)

        self.session = requests.Session()
        self.session.headers.update(HEADERS)
        self.albums = []
        self.album_cid_to_name = {}
        self.all_songs = []
        self.album_song_map = {}
        self.selected_albums = set()
        self.download_dir = tk.StringVar(value=os.getcwd())
        self.lyrics_flag = tk.BooleanVar(value=True)
        self.template_str = tk.StringVar(value="[{album}] {title}")
        self.skip_existing_var = tk.BooleanVar(value=True)

        self.max_workers = tk.IntVar(value=3)
        self.speed_limit_kb = tk.IntVar(value=0)
        self.create_folders = tk.BooleanVar(value=False)

        self.speed_limiter = SpeedLimiter(0)

        self.downloading = False
        self.thread_pool = []
        self.progress_queue = queue.Queue()
        self.completed_count = 0
        self.total_songs = 0
        self.current_active_task = None
        self.cancel_flag = False

        self.vars = []
        self.scanning = False
        self.cid_to_cb = {}
        self.errors = []

        self.setup_ui()
        self.load_data()

    # -------------------- UI 构建 --------------------
    def setup_ui(self):
        album_frame = ttk.LabelFrame(self.root, text="选择专辑", padding=5)
        album_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        btn_frame = ttk.Frame(album_frame)
        btn_frame.pack(fill=tk.X)
        ttk.Button(btn_frame, text="全选", command=self.select_all).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="取消全选", command=self.deselect_all).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="扫描目录", command=self.scan_directory).pack(side=tk.LEFT, padx=10)

        self.canvas = tk.Canvas(album_frame, borderwidth=0, highlightthickness=0)
        self.scrollbar = ttk.Scrollbar(album_frame, orient="vertical", command=self.canvas.yview)
        self.check_frame = ttk.Frame(self.canvas)

        self.check_frame.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.create_window((0, 0), window=self.check_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)

        def _on_mousewheel(event):
            self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        def _on_linux_scroll_up(event):
            self.canvas.yview_scroll(-1, "units")
        def _on_linux_scroll_down(event):
            self.canvas.yview_scroll(1, "units")
        self.canvas.bind("<MouseWheel>", _on_mousewheel)
        self.canvas.bind("<Button-4>", _on_linux_scroll_up)
        self.canvas.bind("<Button-5>", _on_linux_scroll_down)
        self.canvas.bind("<Enter>", lambda e: self.canvas.focus_set())

        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        setting_frame = ttk.Frame(self.root)
        setting_frame.pack(fill=tk.X, padx=10, pady=2)
        ttk.Label(setting_frame, text="命名模板:").pack(side=tk.LEFT)
        self.template_entry = ttk.Entry(setting_frame, textvariable=self.template_str, width=40)
        self.template_entry.pack(side=tk.LEFT, padx=5)
        ttk.Label(setting_frame, text="可用变量: {album} {title} {artist}").pack(side=tk.LEFT)

        dir_frame = ttk.Frame(self.root)
        dir_frame.pack(fill=tk.X, padx=10, pady=2)
        ttk.Label(dir_frame, text="保存目录:").pack(side=tk.LEFT)
        ttk.Entry(dir_frame, textvariable=self.download_dir, width=50).pack(side=tk.LEFT, padx=5)
        ttk.Button(dir_frame, text="选择...", command=self.choose_directory).pack(side=tk.LEFT)

        lrc_frame = ttk.Frame(self.root)
        lrc_frame.pack(fill=tk.X, padx=10, pady=2)
        ttk.Checkbutton(lrc_frame, text="下载歌词 (.lrc)", variable=self.lyrics_flag).pack(anchor=tk.W)
        ttk.Checkbutton(lrc_frame, text="跳过已存在的文件", variable=self.skip_existing_var).pack(anchor=tk.W, pady=2)

        ttk.Button(self.root, text="设置", command=self.open_settings).pack(pady=2)
        self.control_btn = ttk.Button(self.root, text="开始下载", command=self.start_download)
        self.control_btn.pack(pady=5)

        search_frame = ttk.Frame(self.root)
        search_frame.pack(fill=tk.X, padx=10, pady=5)
        ttk.Label(search_frame, text="搜索歌曲:").pack(side=tk.LEFT)
        self.search_entry = ttk.Entry(search_frame, width=30)
        self.search_entry.pack(side=tk.LEFT, padx=5)
        ttk.Button(search_frame, text="搜索", command=self.open_search_window).pack(side=tk.LEFT, padx=2)

        progress_frame = ttk.LabelFrame(self.root, text="下载进度", padding=5)
        progress_frame.pack(fill=tk.X, padx=10, pady=5)

        ttk.Label(progress_frame, text="总进度:").grid(row=0, column=0, sticky=tk.W)
        self.total_progress = ttk.Progressbar(progress_frame, length=400, mode='determinate')
        self.total_progress.grid(row=0, column=1, padx=5, sticky=tk.EW)
        self.total_label = ttk.Label(progress_frame, text="0/0")
        self.total_label.grid(row=0, column=2, padx=5)

        ttk.Label(progress_frame, text="当前文件:").grid(row=1, column=0, sticky=tk.W, pady=2)
        self.current_file_label = ttk.Label(progress_frame, text="等待开始", foreground="blue")
        self.current_file_label.grid(row=1, column=1, columnspan=2, sticky=tk.W, pady=2)

        self.file_progress = ttk.Progressbar(progress_frame, length=400, mode='determinate')
        self.file_progress.grid(row=2, column=0, columnspan=2, padx=5, pady=2, sticky=tk.EW)
        self.speed_label = ttk.Label(progress_frame, text="")
        self.speed_label.grid(row=2, column=2, padx=5)

        progress_frame.columnconfigure(1, weight=1)
        self.process_progress_queue()

    # -------------------- 数据加载 --------------------
    def load_data(self):
        try:
            self.albums = self._fetch_albums()
            self.all_songs = self._fetch_all_songs()
        except Exception as e:
            messagebox.showerror("加载失败", f"无法获取专辑/歌曲列表：{e}")
            return

        self.album_cid_to_name = {a['cid']: a['name'] for a in self.albums}
        self.album_song_map = {}
        for song in self.all_songs:
            cid = song['albumCid']
            self.album_song_map.setdefault(cid, []).append(song['cid'])

        self.vars = []
        self.cid_to_cb = {}
        for alb in self.albums:
            var = tk.BooleanVar(value=False)
            cb = ttk.Checkbutton(self.check_frame, text=alb['name'], variable=var,
                                 command=lambda cid=alb['cid'], v=var: self.toggle_album(cid, v))
            cb.pack(anchor=tk.W, padx=5, pady=1)
            self.vars.append((alb['cid'], var, cb))
            self.cid_to_cb[alb['cid']] = (var, cb)

    def _fetch_albums(self):
        resp = self.session.get(f"{BASE_URL}/api/albums")
        data = resp.json()
        return [{'cid': item['cid'], 'name': item['name']} for item in data['data']]

    def _fetch_all_songs(self):
        resp = self.session.get(f"{BASE_URL}/api/songs")
        data = resp.json()
        songs = []
        for item in data['data']['list']:
            songs.append({
                'cid': item['cid'],
                'name': item['name'],
                'albumCid': item['albumCid'],
                'artists': item.get('artists', [])
            })
        return songs

    # -------------------- 专辑选择交互 --------------------
    def toggle_album(self, cid, var):
        if var.get():
            self.selected_albums.add(cid)
        else:
            self.selected_albums.discard(cid)

    def select_all(self):
        for cid, var, cb in self.vars:
            if 'disabled' in cb.state():
                continue
            var.set(True)
            self.selected_albums.add(cid)

    def deselect_all(self):
        for cid, var, cb in self.vars:
            if 'disabled' in cb.state():
                continue
            var.set(False)
        self.selected_albums.clear()

    def choose_directory(self):
        path = filedialog.askdirectory()
        if path:
            self.download_dir.set(path)

    # -------------------- 设置对话框 --------------------
    def open_settings(self):
        settings_win = tk.Toplevel(self.root)
        settings_win.title("下载设置")
        settings_win.geometry("300x200")
        settings_win.resizable(False, False)
        settings_win.grab_set()
        ttk.Label(settings_win, text="最大同时下载线程数:").pack(pady=(10, 0))
        spin_threads = ttk.Spinbox(settings_win, from_=1, to=10, textvariable=self.max_workers, width=5)
        spin_threads.pack()
        ttk.Label(settings_win, text="下载速度限制 (KB/s, 0=不限):").pack(pady=(10, 0))
        spin_speed = ttk.Spinbox(settings_win, from_=0, to=99999, textvariable=self.speed_limit_kb, width=8)
        spin_speed.pack()
        ttk.Checkbutton(settings_win, text="为每个专辑创建子文件夹", variable=self.create_folders).pack(pady=(10, 5))
        ttk.Button(settings_win, text="确定", command=settings_win.destroy).pack(pady=5)

    # -------------------- 搜索功能 --------------------
    def open_search_window(self):
        keyword = self.search_entry.get().strip()
        if not keyword:
            messagebox.showinfo("提示", "请输入搜索关键词")
            return

        search_win = tk.Toplevel(self.root)
        search_win.title("搜索结果")
        search_win.geometry("550x400")
        search_win.grab_set()

        columns = ("song", "album")
        tree = ttk.Treeview(search_win, columns=columns, show="headings", height=10)
        tree.heading("song", text="歌曲")
        tree.heading("album", text="所属专辑")
        tree.column("song", width=250)
        tree.column("album", width=200)
        tree.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        keyword_lower = keyword.lower()
        for song in self.all_songs:
            if keyword_lower in song['name'].lower():
                album_name = self.album_cid_to_name.get(song['albumCid'], "未知专辑")
                tree.insert("", tk.END, values=(song['name'], album_name),
                            tags=(song['cid'], song['albumCid']))

        if not tree.get_children():
            messagebox.showinfo("无结果", "未找到匹配的歌曲")
            search_win.destroy()
            return

        def on_double_click(event):
            selected = tree.selection()
            if not selected:
                return
            item = selected[0]
            tags = tree.item(item, "tags")
            if len(tags) < 2:
                return
            album_cid = tags[1]
            if album_cid in self.cid_to_cb:
                var, cb = self.cid_to_cb[album_cid]
                if 'disabled' not in cb.state():
                    var.set(True)
                    self.selected_albums.add(album_cid)
                    messagebox.showinfo("已选择", f"专辑「{self.album_cid_to_name.get(album_cid, '')}」已勾选")
            search_win.destroy()

        tree.bind("<Double-1>", on_double_click)

        def on_right_click(event):
            selected = tree.identify_row(event.y)
            if not selected:
                return
            tree.selection_set(selected)
            item = selected
            tags = tree.item(item, "tags")
            if len(tags) < 2:
                return
            album_cid = tags[1]
            menu = tk.Menu(search_win, tearoff=0)
            menu.add_command(label="查看此专辑全部歌曲", command=lambda: self.show_album_songs(album_cid))
            menu.post(event.x_root, event.y_root)

        tree.bind("<Button-3>", on_right_click)
        ttk.Button(search_win, text="返回", command=search_win.destroy).pack(pady=5)

    def show_album_songs(self, album_cid):
        if album_cid not in self.album_song_map:
            return
        album_name = self.album_cid_to_name.get(album_cid, "未知专辑")
        song_cids = self.album_song_map[album_cid]
        songs = [song['name'] for song in self.all_songs if song['cid'] in song_cids]
        songs_text = "\n".join(songs)

        win = tk.Toplevel(self.root)
        win.title(f"专辑「{album_name}」歌曲列表")
        win.geometry("400x400")
        text_area = scrolledtext.ScrolledText(win, wrap=tk.WORD, font=("", 10))
        text_area.insert(tk.INSERT, songs_text)
        text_area.configure(state=tk.DISABLED)
        text_area.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        ttk.Button(win, text="关闭", command=win.destroy).pack(pady=5)

    # -------------------- 扫描目录 --------------------
    def scan_directory(self):
        if self.scanning or self.downloading:
            return
        self._start_scan()

    def _start_scan(self):
        save_dir = self.download_dir.get()
        if not os.path.isdir(save_dir):
            messagebox.showerror("目录错误", "保存目录不存在")
            return

        all_cids = set()
        for alb_cid in self.album_song_map:
            all_cids.update(self.album_song_map[alb_cid])

        if not all_cids:
            messagebox.showinfo("无歌曲", "无歌曲可扫描")
            return

        self.scanning = True
        self.control_btn.config(text="扫描中...", state=tk.DISABLED)
        self.current_file_label.config(text="正在扫描已下载文件...")
        self.speed_label.config(text="")

        def scan_task():
            try:
                _, _, complete_albums = self.scan_existing_files(all_cids)
            except Exception as e:
                self.root.after(0, messagebox.showerror, "扫描错误", str(e))
                self.scanning = False
                self.root.after(0, lambda: self.control_btn.config(text="开始下载", state=tk.NORMAL))
                return

            self.root.after(0, lambda: self.update_album_checkboxes(complete_albums))
            self.scanning = False
            self.root.after(0, lambda: self.control_btn.config(text="开始下载", state=tk.NORMAL))
            self.root.after(0, lambda: messagebox.showinfo("扫描结果", "扫描完成。完整专辑已自动勾选并锁定。"))
            self.root.after(0, lambda: self.current_file_label.config(text="扫描完成"))

        threading.Thread(target=scan_task, daemon=True).start()

    def scan_existing_files(self, all_cids):
        template = self.template_str.get()
        save_dir = self.download_dir.get()
        to_download = []
        already = []
        album_status = {}

        for song in self.all_songs:
            cid = song['cid']
            if cid not in all_cids:
                continue
            alb_cid = song['albumCid']
            album_name = self.album_cid_to_name.get(alb_cid, "未知专辑")
            artist_str = self._format_artists(song.get('artists', []))
            fname = self._format_filename(template, album_name, song['name'], artist_str)
            safe_name = self._sanitize_filename(fname)

            if self.create_folders.get():
                safe_album = self._sanitize_filename(album_name)
                base_path = os.path.join(save_dir, safe_album)
            else:
                base_path = save_dir

            path = os.path.join(base_path, safe_name + ".wav")
            exists = os.path.exists(path)
            if exists:
                already.append(cid)
            else:
                to_download.append(cid)
            album_status.setdefault(alb_cid, set()).add((cid, exists))

        complete_albums = []
        for alb_cid, status_set in album_status.items():
            if alb_cid not in self.album_song_map:
                continue
            all_exist = all(ex for _, ex in status_set)
            if all_exist and len(status_set) == len(self.album_song_map[alb_cid]):
                complete_albums.append(alb_cid)

        return to_download, already, complete_albums

    def update_album_checkboxes(self, complete_albums):
        for cid, var, cb in self.vars:
            if cid in complete_albums:
                var.set(True)
                cb.configure(state=tk.DISABLED)
            else:
                cb.configure(state=tk.NORMAL)
        self.selected_albums = {cid for cid, var, _ in self.vars if var.get()}

    # -------------------- 下载流程 --------------------
    def start_download(self):
        if self.downloading or self.scanning:
            return
        if not self.selected_albums:
            messagebox.showwarning("未选择专辑", "请至少勾选一个专辑")
            return
        save_dir = self.download_dir.get()
        if not os.path.isdir(save_dir):
            messagebox.showerror("目录错误", "保存目录不存在")
            return

        self.speed_limiter.set_limit(self.speed_limit_kb.get())
        self.errors = []

        self.downloading = True
        self.cancel_flag = False
        self.control_btn.config(text="取消下载")
        self.total_progress['value'] = 0
        self.file_progress['value'] = 0
        self.speed_label.config(text="")
        self.current_file_label.config(text="准备下载...")
        self.completed_count = 0
        self.current_active_task = None

        user_selected = set()
        for cid, var, cb in self.vars:
            if var.get() and 'disabled' not in cb.state():
                user_selected.add(cid)

        if not user_selected:
            messagebox.showinfo("无待下载", "所有勾选专辑已完整，或未选择任何新专辑。")
            self.downloading = False
            self.control_btn.config(text="开始下载")
            return

        all_cids = set()
        for alb_cid in user_selected:
            if alb_cid in self.album_song_map:
                all_cids.update(self.album_song_map[alb_cid])

        if not all_cids:
            messagebox.showinfo("无歌曲", "所选专辑中没有歌曲")
            self.downloading = False
            self.control_btn.config(text="开始下载")
            return

        self.total_songs = len(all_cids)
        self.total_progress['maximum'] = self.total_songs
        self.total_label.config(text=f"0/{self.total_songs}")

        self.thread_pool = []
        for cid in all_cids:
            t = threading.Thread(target=self.download_song, args=(cid,), daemon=True)
            self.thread_pool.append(t)

        semaphore = threading.BoundedSemaphore(self.max_workers.get())
        def worker_with_limit(t):
            semaphore.acquire()
            try:
                t.start()
                t.join()
            finally:
                semaphore.release()

        wrapper_threads = []
        for t in self.thread_pool:
            wt = threading.Thread(target=worker_with_limit, args=(t,), daemon=True)
            wrapper_threads.append(wt)
            wt.start()

        def monitor():
            for wt in wrapper_threads:
                wt.join()
            self.downloading = False
            self.root.after(0, self.download_finished)

        threading.Thread(target=monitor, daemon=True).start()

    def download_song(self, song_cid):
        if self.cancel_flag:
            return
        song_name = "未知歌曲"
        try:
            detail = self._get_song_detail(song_cid)
            song_name = detail['name']
        except Exception as e:
            self.progress_queue.put(('error', song_cid, f"{song_name}: 获取详情失败 ({e})"))
            return

        if not detail.get('sourceUrl'):
            self.progress_queue.put(('error', song_cid, f"{song_name}: 无下载链接"))
            return

        album_name = self.album_cid_to_name.get(detail['albumCid'], "未知专辑")
        artist_str = self._format_artists(detail.get('artists', []))
        template = self.template_str.get()
        fname = self._format_filename(template, album_name, song_name, artist_str)
        safe_name = self._sanitize_filename(fname)
        save_dir = self.download_dir.get()

        # 子文件夹处理（严格清理，捕获创建异常）
        if self.create_folders.get():
            safe_album = self._sanitize_filename(album_name)
            base_dir = os.path.join(save_dir, safe_album)
            try:
                os.makedirs(base_dir, exist_ok=True)
            except Exception as e:
                self.progress_queue.put(('error', song_cid, f"{song_name}: 无法创建文件夹 {base_dir} ({e})"))
                return
        else:
            base_dir = save_dir

        music_path = os.path.join(base_dir, safe_name + ".wav")
        lyric_path = os.path.join(base_dir, safe_name + ".lrc") if self.lyrics_flag.get() and detail.get('lyricUrl') else None

        if self.skip_existing_var.get():
            music_exists = os.path.exists(music_path)
            lyric_exists = True
            if lyric_path:
                lyric_exists = os.path.exists(lyric_path)

            if music_exists and lyric_exists:
                self.progress_queue.put(('start_file', song_cid, safe_name + " (已存在)"))
                self.progress_queue.put(('complete', song_cid, safe_name + " (已存在)"))
                return

            if not music_exists:
                self.progress_queue.put(('start_file', song_cid, safe_name + ".wav"))
                try:
                    self._download_with_progress(detail['sourceUrl'], music_path, song_cid)
                except Exception as e:
                    self.progress_queue.put(('error', song_cid, f"{song_name}: 音乐下载失败 ({e})"))
                    return
            else:
                self.progress_queue.put(('start_file', song_cid, safe_name + ".wav (已存在，跳过)"))
                self.progress_queue.put(('complete', song_cid, safe_name))
                return

            if lyric_path and not lyric_exists:
                try:
                    self._download_with_progress(detail['lyricUrl'], lyric_path, song_cid, send_progress=False)
                except Exception as e:
                    self.progress_queue.put(('error', song_cid, f"{song_name}: 歌词下载失败 ({e})"))
                    return
        else:
            self.progress_queue.put(('start_file', song_cid, safe_name + ".wav"))
            try:
                self._download_with_progress(detail['sourceUrl'], music_path, song_cid)
            except Exception as e:
                self.progress_queue.put(('error', song_cid, f"{song_name}: 音乐下载失败 ({e})"))
                return

            if lyric_path:
                try:
                    self._download_with_progress(detail['lyricUrl'], lyric_path, song_cid, send_progress=False)
                except Exception as e:
                    self.progress_queue.put(('error', song_cid, f"{song_name}: 歌词下载失败 ({e})"))
                    return

        self.progress_queue.put(('complete', song_cid, safe_name))

    def _get_song_detail(self, cid):
        url = f"{BASE_URL}/api/song/{cid}"
        resp = self.session.get(url)
        data = resp.json()['data']
        artists = data.get('artists', [])
        if isinstance(artists, str):
            artists = [artists]
        return {
            'cid': cid,
            'name': data['name'],
            'albumCid': data['albumCid'],
            'sourceUrl': data['sourceUrl'],
            'lyricUrl': data.get('lyricUrl'),
            'artists': artists
        }

    def _format_artists(self, artists):
        if not artists:
            return ""
        return ", ".join(artists)

    def _format_filename(self, template, album, title, artist):
        try:
            return template.format(album=album, title=title, artist=artist)
        except KeyError:
            return f"[{album}] {title}"

    def _sanitize_filename(self, name):
        """
        严格清理文件名/文件夹名：
        - 英文冒号 → 中文冒号
        - 移除末尾的点和空格（避免 Windows 错误）
        - 删除其他非法字符 \ / * ? " < > |
        """
        name = name.replace(':', '：')
        name = name.rstrip('. ')   # 同时去除结尾的点号和空格
        return re.sub(r'[\\/*?"<>|]', '', name)

    def _download_with_progress(self, url, save_path, task_id, send_progress=True):
        resp = self.session.get(url, stream=True, timeout=30)
        total_size = int(resp.headers.get('content-length', 0))
        downloaded = 0
        start_time = time.time()

        with open(save_path, 'wb') as f:
            for chunk in resp.iter_content(chunk_size=CHUNK_SIZE):
                if self.cancel_flag:
                    raise Exception("用户取消")
                f.write(chunk)
                downloaded += len(chunk)
                self.speed_limiter.acquire(len(chunk))

                if send_progress:
                    elapsed = time.time() - start_time
                    speed = downloaded / elapsed if elapsed > 0 else 0
                    self.progress_queue.put(('progress', task_id, {
                        'downloaded': downloaded,
                        'total': total_size,
                        'speed': speed,
                        'is_lyric': False
                    }))

    # -------------------- 进度更新 --------------------
    def process_progress_queue(self):
        try:
            while True:
                msg = self.progress_queue.get_nowait()
                self._handle_message(msg)
        except queue.Empty:
            pass
        self.root.after(100, self.process_progress_queue)

    def _handle_message(self, msg):
        msg_type = msg[0]
        task_id = msg[1]
        if msg_type == 'start_file':
            filename = msg[2]
            self.current_active_task = task_id
            self.current_file_label.config(text=filename, foreground="blue")
            self.file_progress['value'] = 0
            self.file_progress.config(mode='determinate')
            self.speed_label.config(text="")
        elif msg_type == 'progress':
            if task_id != self.current_active_task:
                return
            data = msg[2]
            if data['total'] > 0:
                self.file_progress.config(mode='determinate', maximum=data['total'], value=data['downloaded'])
            else:
                self.file_progress.config(mode='indeterminate')
                self.file_progress.start()
            speed_mb = data['speed'] / 1024 / 1024
            self.speed_label.config(text=f"{speed_mb:.1f} MB/s")
        elif msg_type == 'complete':
            self.completed_count += 1
            self.total_progress['value'] = self.completed_count
            self.total_label.config(text=f"{self.completed_count}/{self.total_songs}")
            self.file_progress['value'] = 100
            self.speed_label.config(text="完成")
            self.current_file_label.config(text=f"{msg[2]} 下载完成", foreground="green")
            self.current_active_task = None
        elif msg_type == 'error':
            self.completed_count += 1
            self.total_progress['value'] = self.completed_count
            self.total_label.config(text=f"{self.completed_count}/{self.total_songs}")
            err_msg = msg[2]
            self.current_file_label.config(text=f"错误: {err_msg}", foreground="red")
            self.file_progress['value'] = 0
            self.speed_label.config(text="")
            self.current_active_task = None
            self.errors.append(err_msg)

    def download_finished(self):
        self.downloading = False
        self.control_btn.config(text="开始下载")
        success = self.completed_count - len(self.errors)
        status_text = f"下载结束，成功: {success}/{self.total_songs}"
        if self.errors:
            status_text += f"，失败: {len(self.errors)}"
            error_list = "\n".join(self.errors)
            messagebox.showwarning("下载完成但有错误", f"{status_text}\n\n错误详情:\n{error_list}")
        else:
            messagebox.showinfo("完成", status_text)
        self.current_file_label.config(text="下载完成" if not self.errors else "部分下载失败")

    def cancel_download(self):
        self.cancel_flag = True
        self.control_btn.config(text="开始下载")
        self.downloading = False

# -------------------- 启动 --------------------
if __name__ == "__main__":
    root = tk.Tk()
    app = SirenDownloader(root)
    root.mainloop()
