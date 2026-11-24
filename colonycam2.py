import math
import os
import subprocess
import sys
import cv2
import numpy as np
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog
from PIL import Image, ImageTk


DISPLAY_W = 640
DISPLAY_H = 480

BTN_BG = "#d9d9d9"
BTN_ACTIVE_BG = "#c2c2c2"
BTN_FG = "#111111"

DEFAULT_PX_PER_MM = 10.0

DEFAULT_HELP_TEXT = """ USER GUIDE
================================================

1. CAMERA SELECTION & LIVE FEED
   - Open the "Camera" menu to select Camera Index 0, 1, or 2.
   - Click "Connect / Reconnect" to open or refresh the video stream.
   - Click "Resume Live Feed" to return to live camera preview.

2. OPENING & SAVING IMAGES ("File" Menu)
   - File > Open: Load an existing image (.png, .jpg, .bmp) for counting.
   - File > Save / Save As: Opens a Save dialog so you can choose the
     destination folder, file name, and format.

3. CALIBRATION ("Calibrate" Menu)
   - Capture or open an image containing a circular reference of known
     diameter (for example, a 90 mm Petri dish).
   - Click Calibrate > Draw Scale Circle and drag the green circle to
     match the known reference circle.
   - Click Calibrate > Set Known Diameter (mm) and enter the diameter.
   - Click Calibrate > Apply Calibration to convert the Min Colony Area
     slider (1 to 20 mm²) into pixel area using your measured scale.
   - Click Calibrate > Reset Calibration to return to the default scale.

4. CIRCLE CROP ROI ("Edit" Menu or Right Panel)
   - Click "Draw / Drag Circle" (or Edit > Draw and Drag Circle).
   - Drag inside the yellow circle to move it, drag near its edge to
     resize it, or drag outside to draw a new circle.
   - Click "Apply Circle Crop" (or Edit > Apply Circle) to isolate the
     region inside the circle so only colonies inside are counted.
   - Click "Clear Circle" (or Edit > Clear Circle) to remove the circle.

5. COLONY COUNTING & SLIDERS
   - Min Colony Area (1-20 mm²): Filters out smaller debris/noise.
   - Detection Sensitivity (C): Adjusts adaptive thresholding contrast.
     Lower C (e.g., 1-4) detects fainter colonies; higher C (e.g., 6-25)
     reduces background noise.
   - Click "Capture & Count Colonies" to freeze, detect, circle, and count
     colonies.
"""


class ColonyCounterApp:
    def __init__(self, window, window_title):
        self.window = window
        self.window.title(window_title)
        self.window.geometry("960x600")
        self.window.configure(bg="#f0f0f0")

        self.cap = None
        self.current_frame = None
        self.captured_frame = None
        self.last_processed_image = None
        self.last_saved_dir = self._get_app_dir()
        self.is_live = False
        self.after_id = None
        self.cam_index_var = tk.IntVar(value=0)

        # Calibration state: pixels per millimeter (None until calibrated)
        self.px_per_mm = None
        self.known_diameter_mm = 90.0
        self.calibration_mode = False  # True when drawing calibration circle vs crop ROI

        # Active ROI in original image coordinates: (cx, cy, r) or None
        self.crop_roi = None

        # Circle overlay state in display coordinates (DISPLAY_W x DISPLAY_H)
        self.circle_mode = False
        self.circle_center = None  # (cx, cy)
        self.circle_radius = 0.0
        self.drag_action = None    # None, "create", "move", "resize"
        self.drag_start = None     # (x, y)
        self.orig_circle = None    # (cx, cy, r)

        # Ensure help text file exists on disk
        self.help_file_path = os.path.join(self._get_app_dir(), "colony_counter_help.txt")
        self._ensure_help_file()

        # --- Top Menu Bar (File, Edit, Camera, Calibrate, Help) ---
        self.menu_bar = tk.Menu(window)

        self.file_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.file_menu.add_command(label="Open", command=self.open_image)
        self.file_menu.add_command(label="Save", command=self.prompt_save_dialog)
        self.file_menu.add_command(label="Save As", command=self.prompt_save_dialog)
        self.file_menu.add_separator()
        self.file_menu.add_command(label="Exit", command=self.on_closing)
        self.menu_bar.add_cascade(label="File", menu=self.file_menu)

        self.edit_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.edit_menu.add_command(label="Draw and Drag Circle", command=self.enable_crop_circle_tool)
        self.edit_menu.add_command(label="Apply Circle", command=self.apply_circle_crop)
        self.edit_menu.add_command(label="Clear Circle", command=self.clear_circle)
        self.menu_bar.add_cascade(label="Edit", menu=self.edit_menu)

        self.camera_menu = tk.Menu(self.menu_bar, tearoff=0)
        for idx in (0, 1, 2):
            self.camera_menu.add_radiobutton(
                label=f"Camera Index {idx}",
                variable=self.cam_index_var,
                value=idx,
                command=lambda i=idx: self.select_camera_index(i),
            )
        self.menu_bar.add_cascade(label="Camera", menu=self.camera_menu)

        self.calibrate_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.calibrate_menu.add_command(label="Draw Scale Circle", command=self.start_calibration_circle)
        self.calibrate_menu.add_command(label="Set Known Diameter (mm)", command=self.set_known_diameter_dialog)
        self.calibrate_menu.add_command(label="Apply Calibration", command=self.apply_scale_calibration)
        self.calibrate_menu.add_command(label="Reset Calibration", command=self.reset_calibration)
        self.menu_bar.add_cascade(label="Calibrate", menu=self.calibrate_menu)

        self.help_menu = tk.Menu(self.menu_bar, tearoff=0)
        self.help_menu.add_command(label="Open Help in Notepad", command=self.open_help_in_notepad)
        self.help_menu.add_command(label="About", command=self.show_about_dialog)
        self.menu_bar.add_cascade(label="Help", menu=self.help_menu)

        window.config(menu=self.menu_bar)

        # --- Main Split Layout: Left (Video + Status), Right (Controls) ---
        left_panel = tk.Frame(window, bg="#f0f0f0")
        left_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=12, pady=10)

        right_panel = tk.Frame(
            window, bg="#e6e6e6", width=275, padx=12, pady=12, relief=tk.GROOVE, bd=1
        )
        right_panel.pack(side=tk.RIGHT, fill=tk.Y, padx=(0, 12), pady=10)
        right_panel.pack_propagate(False)

        # --- Left Side: Title, Video Canvas, Count Readout ---
        self.title_label = tk.Label(
            left_panel, text="Initializing Camera...", font=("Arial", 13, "bold"), bg="#f0f0f0"
        )
        self.title_label.pack(pady=(0, 6))

        self.video_label = tk.Label(left_panel, bg="black", width=DISPLAY_W, height=DISPLAY_H)
        self.video_label.pack()

        self.video_label.bind("<ButtonPress-1>", self.on_mouse_down)
        self.video_label.bind("<B1-Motion>", self.on_mouse_drag)
        self.video_label.bind("<ButtonRelease-1>", self.on_mouse_up)

        self.lbl_count = tk.Label(
            left_panel, text="Count: --", font=("Arial", 13, "bold"), fg="#222222", bg="#f0f0f0"
        )
        self.lbl_count.pack(pady=(8, 0))

        # --- Right Side: Camera Connect Button ---
        tk.Label(
            right_panel, text="Camera", font=("Arial", 11, "bold"), bg="#e6e6e6", fg="#111111"
        ).pack(anchor="w", pady=(0, 4))

        self.btn_reconnect = self._make_grey_button(
            right_panel,
            text="Connect / Reconnect",
            command=lambda: self.connect_camera(auto_fallback=False),
        )
        self.btn_reconnect.pack(fill=tk.X, pady=(0, 10))

        # --- Right Side: Circle ROI Controls ---
        tk.Label(
            right_panel,
            text="Circle Crop ROI",
            font=("Arial", 11, "bold"),
            bg="#e6e6e6",
            fg="#111111",
        ).pack(anchor="w", pady=(0, 4))

        self.btn_draw_circle = self._make_grey_button(
            right_panel,
            text="Draw / Drag Circle",
            command=self.enable_crop_circle_tool,
        )
        self.btn_draw_circle.pack(fill=tk.X, pady=2)

        self.btn_apply_crop = self._make_grey_button(
            right_panel,
            text="Apply Circle Crop",
            command=self.apply_circle_crop,
        )
        self.btn_apply_crop.pack(fill=tk.X, pady=2)

        self.btn_clear_circle = self._make_grey_button(
            right_panel,
            text="Clear Circle",
            command=self.clear_circle,
        )
        self.btn_clear_circle.pack(fill=tk.X, pady=(2, 10))

        # --- Right Side: Calibrated Min Colony Area Slider (1 to 20 mm^2) ---
        tk.Label(
            right_panel,
            text="Min Colony Area (1-20 mm²):",
            font=("Arial", 10, "bold"),
            bg="#e6e6e6",
            fg="#111111",
        ).pack(anchor="w", pady=(0, 2))

        self.size_slider = tk.Scale(
            right_panel,
            from_=1.0,
            to=20.0,
            resolution=0.5,
            orient=tk.HORIZONTAL,
            length=235,
            bg="#e6e6e6",
            fg="#111111",
            troughcolor="#cccccc",
            highlightthickness=0,
        )
        self.size_slider.set(2.0)
        self.size_slider.pack(fill=tk.X, pady=(0, 4))

        self.lbl_scale_status = tk.Label(
            right_panel,
            text=f"Scale: Uncalibrated (est. {DEFAULT_PX_PER_MM:.1f} px/mm)",
            font=("Arial", 9),
            bg="#e6e6e6",
            fg="#333333",
            wraplength=245,
            justify=tk.LEFT,
        )
        self.lbl_scale_status.pack(anchor="w", pady=(0, 8))

        # --- Right Side: Colony Detection Sensitivity Slider (Adaptive C) ---
        tk.Label(
            right_panel,
            text="Detection Sensitivity (C):",
            font=("Arial", 10, "bold"),
            bg="#e6e6e6",
            fg="#111111",
        ).pack(anchor="w", pady=(0, 2))

        self.sensitivity_slider = tk.Scale(
            right_panel,
            from_=1,
            to=25,
            orient=tk.HORIZONTAL,
            length=235,
            bg="#e6e6e6",
            fg="#111111",
            troughcolor="#cccccc",
            highlightthickness=0,
        )
        self.sensitivity_slider.set(5)
        self.sensitivity_slider.pack(fill=tk.X, pady=(0, 12))

        # --- Right Side: Primary Action Buttons ---
        tk.Label(
            right_panel, text="Actions", font=("Arial", 11, "bold"), bg="#e6e6e6", fg="#111111"
        ).pack(anchor="w", pady=(0, 4))

        self.btn_capture = self._make_grey_button(
            right_panel,
            text="Capture & Count Colonies",
            command=self.capture_and_count,
        )
        self.btn_capture.pack(fill=tk.X, pady=3)

        self.btn_live = self._make_grey_button(
            right_panel,
            text="Resume Live Feed",
            command=self.resume_live,
        )
        self.btn_live.pack(fill=tk.X, pady=3)

        self._set_circle_controls_active(False)
        self.window.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.window.after(100, lambda: self.connect_camera(auto_fallback=True))

    def _get_app_dir(self):
        if getattr(sys, "frozen", False):
            return os.path.dirname(os.path.abspath(sys.executable))
        return os.path.dirname(os.path.abspath(__file__))

    def _ensure_help_file(self):
        if not os.path.exists(self.help_file_path):
            try:
                with open(self.help_file_path, "w", encoding="utf-8") as f:
                    f.write(DEFAULT_HELP_TEXT)
            except Exception:
                pass

    def open_help_in_notepad(self):
        self._ensure_help_file()
        try:
            subprocess.Popen(["notepad.exe", self.help_file_path])
        except Exception as exc:
            messagebox.showerror(
                "Help Error",
                f"Could not open help file in Notepad:\n{self.help_file_path}\n\n{exc}",
                parent=self.window,
            )

    def show_about_dialog(self):
        messagebox.showinfo(
            "About Colony Counter",
            "Python Microbial Colony Counter\n"
            "Features: Webcam & Image Input, Circle ROI Crop,\n"
            "Scale Calibration (1-20 mm²), Sensitivity Control & Save Dialog.\n\n"
            f"Help File: {self.help_file_path}",
            parent=self.window,
        )

    def _make_grey_button(self, parent, text, command):
        return tk.Button(
            parent,
            text=text,
            font=("Arial", 10, "bold"),
            bg=BTN_BG,
            fg=BTN_FG,
            activebackground=BTN_ACTIVE_BG,
            activeforeground=BTN_FG,
            relief=tk.RAISED,
            bd=2,
            padx=10,
            pady=6,
            command=command,
        )

    def _set_circle_controls_active(self, active):
        state = tk.NORMAL if active else tk.DISABLED
        self.btn_apply_crop.config(state=state)
        self.btn_clear_circle.config(state=state)

    def _update_scale_label(self):
        if self.px_per_mm is not None and self.px_per_mm > 0:
            self.lbl_scale_status.config(
                text=f"Calibrated: {self.px_per_mm:.2f} px/mm (Ref: {self.known_diameter_mm:g} mm)"
            )
        else:
            self.lbl_scale_status.config(
                text=f"Scale: Uncalibrated (est. {DEFAULT_PX_PER_MM:.1f} px/mm)"
            )

    def _get_min_area_px(self):
        area_mm2 = float(self.size_slider.get())
        scale = self.px_per_mm if (self.px_per_mm is not None and self.px_per_mm > 0) else DEFAULT_PX_PER_MM
        return max(1.0, area_mm2 * (scale ** 2))

    def _stop_live_loop(self):
        self.is_live = False
        if self.after_id is not None:
            try:
                self.window.after_cancel(self.after_id)
            except Exception:
                pass
            self.after_id = None

    def _release_camera(self):
        self._stop_live_loop()
        if self.cap is not None:
            try:
                if self.cap.isOpened():
                    self.cap.release()
            except Exception:
                pass
            self.cap = None

    def _try_open_index(self, idx):
        for backend in (cv2.CAP_DSHOW, cv2.CAP_ANY):
            cap = cv2.VideoCapture(idx, backend)
            if cap is not None and cap.isOpened():
                cap.set(cv2.CAP_PROP_FRAME_WIDTH, 640)
                cap.set(cv2.CAP_PROP_FRAME_HEIGHT, 480)
                cap.set(cv2.CAP_PROP_BUFFERSIZE, 1)
                for _ in range(5):
                    ret, frame = cap.read()
                    if ret and frame is not None and frame.size > 0:
                        return cap
                cap.release()
            elif cap is not None:
                cap.release()
        return None

    def select_camera_index(self, idx):
        self.cam_index_var.set(int(idx))
        self.connect_camera(auto_fallback=False)

    def connect_camera(self, auto_fallback=False):
        self._release_camera()
        selected_idx = int(self.cam_index_var.get())
        candidates = [selected_idx]
        if auto_fallback:
            for fallback_idx in (0, 1, 2):
                if fallback_idx not in candidates:
                    candidates.append(fallback_idx)

        opened_cap = None
        used_idx = None
        for idx in candidates:
            opened_cap = self._try_open_index(idx)
            if opened_cap is not None:
                used_idx = idx
                break

        if opened_cap is None:
            self.title_label.config(text="Camera Not Found / Unavailable")
            messagebox.showwarning(
                "Camera Warning",
                "Could not open webcam feed.\n\n"
                "- Check that no other app (Zoom, browser, MATLAB) is using the camera.\n"
                "- Select Camera Index 0, 1, or 2 from the Camera menu and click Connect / Reconnect.",
                parent=self.window,
            )
            return

        self.cap = opened_cap
        self.cam_index_var.set(int(used_idx))
        self.captured_frame = None
        self.last_processed_image = None
        self.crop_roi = None
        self.clear_circle()
        self.is_live = True
        self.lbl_count.config(text="Count: --")
        self.title_label.config(text=f"Live Camera Feed (Index {used_idx})")
        self.update_feed()

    def _render_preview(self, explicit_bgr=None):
        if explicit_bgr is not None:
            base_img = explicit_bgr
        else:
            base_img = (
                self.captured_frame
                if (not self.is_live and self.captured_frame is not None)
                else self.current_frame
            )
        if base_img is None:
            return

        display_img = cv2.resize(base_img, (DISPLAY_W, DISPLAY_H))

        if self.circle_center is not None and self.circle_radius > 2:
            cx, cy = int(round(self.circle_center[0])), int(round(self.circle_center[1]))
            r = int(round(self.circle_radius))
            color = (0, 255, 0) if self.calibration_mode else (0, 255, 255)
            cv2.circle(display_img, (cx, cy), r, color, 2)
            cv2.circle(display_img, (cx, cy), 4, color, -1)

        rgb_img = cv2.cvtColor(display_img, cv2.COLOR_BGR2RGB)
        img = Image.fromarray(rgb_img)
        imgtk = ImageTk.PhotoImage(image=img)
        self.video_label.imgtk = imgtk
        self.video_label.configure(image=imgtk, width=DISPLAY_W, height=DISPLAY_H)

    def update_feed(self):
        if self.is_live and self.cap is not None and self.cap.isOpened():
            ret, frame = self.cap.read()
            if ret and frame is not None and frame.size > 0:
                self.current_frame = frame.copy()
                self._render_preview()

        if self.is_live:
            self.after_id = self.window.after(30, self.update_feed)

    # --- File Menu Handlers ---
    def open_image(self):
        file_path = filedialog.askopenfilename(
            parent=self.window,
            title="Open Colony Image",
            initialdir=self.last_saved_dir,
            filetypes=[
                ("PNG Image", "*.png"),
                ("JPEG Image", "*.jpg"),
                ("Bitmap Image", "*.bmp"),
                ("All Files", "*.*"),
            ],
        )
        if not file_path:
            return

        try:
            data = np.fromfile(file_path, dtype=np.uint8)
            img = cv2.imdecode(data, cv2.IMREAD_COLOR)
        except Exception as exc:
            messagebox.showerror("Open Error", f"Failed to read image:\n{exc}", parent=self.window)
            return

        if img is None or img.size == 0:
            messagebox.showerror(
                "Open Error", "Could not decode the selected image file.", parent=self.window
            )
            return

        self._stop_live_loop()
        self.captured_frame = img
        self.last_processed_image = None
        self.last_saved_dir = os.path.dirname(file_path) or self.last_saved_dir
        self.crop_roi = None
        self.clear_circle()
        self.lbl_count.config(text="Count: --")
        self.title_label.config(text=f"Loaded: {os.path.basename(file_path)}")
        self._render_preview()

    def _get_image_to_save(self):
        if self.last_processed_image is not None:
            return self.last_processed_image
        if not self.is_live and self.captured_frame is not None:
            return self.captured_frame
        if self.current_frame is not None:
            return self.current_frame
        return None

    def _write_image_to_path(self, img, target_path):
        ext = os.path.splitext(target_path)[1].lower()
        if not ext:
            ext = ".png"
            target_path = target_path + ext

        success, encoded = cv2.imencode(ext, img)
        if not success:
            raise RuntimeError(f"Unsupported image format: {ext}")
        encoded.tofile(target_path)
        self.last_saved_dir = os.path.dirname(os.path.abspath(target_path))

    def prompt_save_dialog(self):
        img = self._get_image_to_save()
        if img is None:
            messagebox.showwarning("Save Warning", "No image available to save.", parent=self.window)
            return

        file_path = filedialog.asksaveasfilename(
            parent=self.window,
            title="Save Image",
            initialdir=self.last_saved_dir,
            initialfile="counted_result.png",
            defaultextension=".png",
            filetypes=[
                ("PNG Image", "*.png"),
                ("JPEG Image", "*.jpg"),
                ("Bitmap Image", "*.bmp"),
                ("All Files", "*.*"),
            ],
        )
        if not file_path:
            return

        try:
            self._write_image_to_path(img, file_path)
            messagebox.showinfo(
                "Saved", f"Image saved to:\n{os.path.abspath(file_path)}", parent=self.window
            )
        except Exception as exc:
            messagebox.showerror("Save Error", f"Could not save image:\n{exc}", parent=self.window)

    # --- Calibration Handlers ---
    def start_calibration_circle(self):
        if self.is_live:
            if self.current_frame is None:
                messagebox.showwarning("Warning", "No active frame available yet.", parent=self.window)
                return
            self._stop_live_loop()
            self.captured_frame = self.current_frame.copy()
            self.crop_roi = None

        if self.captured_frame is None:
            messagebox.showwarning(
                "Calibration Warning",
                "Capture or open an image with a known scale first.",
                parent=self.window,
            )
            return

        self.calibration_mode = True
        self.circle_mode = True
        if self.circle_center is None:
            self.circle_center = (DISPLAY_W / 2.0, DISPLAY_H / 2.0)
            self.circle_radius = min(DISPLAY_W, DISPLAY_H) * 0.35
        self._set_circle_controls_active(False)
        self.title_label.config(
            text="Calibration: Drag circle to match known scale, then click Calibrate > Apply Calibration"
        )
        self._render_preview()

    def set_known_diameter_dialog(self):
        val = simpledialog.askfloat(
            "Known Scale Diameter",
            "Enter known diameter of the reference circle (mm):",
            initialvalue=self.known_diameter_mm,
            minvalue=0.1,
            maxvalue=1000.0,
            parent=self.window,
        )
        if val is not None:
            self.known_diameter_mm = float(val)
            if self.circle_center is not None and self.circle_radius > 2 and self.calibration_mode:
                self.apply_scale_calibration()
            else:
                self._update_scale_label()

    def apply_scale_calibration(self):
        if self.captured_frame is None or self.circle_center is None or self.circle_radius <= 2:
            messagebox.showwarning(
                "Calibration Warning",
                "Draw a circle over the known scale first (Calibrate > Draw Scale Circle).",
                parent=self.window,
            )
            return

        if self.known_diameter_mm <= 0:
            self.set_known_diameter_dialog()
            if self.known_diameter_mm <= 0:
                return

        h, w = self.captured_frame.shape[:2]
        scale_x = w / float(DISPLAY_W)
        scale_y = h / float(DISPLAY_H)
        r_orig = self.circle_radius * ((scale_x + scale_y) / 2.0)
        diameter_px = 2.0 * r_orig

        self.px_per_mm = diameter_px / float(self.known_diameter_mm)
        self.calibration_mode = False
        self.circle_mode = False
        self.circle_center = None
        self.circle_radius = 0.0
        self._update_scale_label()
        self.title_label.config(
            text=f"Calibrated ({self.px_per_mm:.2f} px/mm for {self.known_diameter_mm:g} mm circle)"
        )
        self._render_preview()
        messagebox.showinfo(
            "Calibration Applied",
            f"Reference diameter: {self.known_diameter_mm:g} mm ({diameter_px:.1f} px)\n"
            f"Scale: {self.px_per_mm:.2f} pixels/mm\n"
            f"Min Colony Area slider now controls 1 to 20 mm².",
            parent=self.window,
        )

    def reset_calibration(self):
        self.px_per_mm = None
        self.calibration_mode = False
        self._update_scale_label()
        messagebox.showinfo(
            "Calibration Reset",
            f"Calibration cleared. Using default estimate ({DEFAULT_PX_PER_MM:.1f} px/mm).",
            parent=self.window,
        )

    # --- Circle ROI Handlers (Edit Menu + Right Panel) ---
    def enable_crop_circle_tool(self):
        if self.is_live:
            if self.current_frame is None:
                messagebox.showwarning("Warning", "No active frame available yet.", parent=self.window)
                return
            self._stop_live_loop()
            self.captured_frame = self.current_frame.copy()
            self.crop_roi = None

        if self.captured_frame is None:
            messagebox.showwarning(
                "Warning",
                "Capture or open an image first before drawing a circle.",
                parent=self.window,
            )
            return

        self.calibration_mode = False
        self.circle_mode = True
        if self.circle_center is None:
            self.circle_center = (DISPLAY_W / 2.0, DISPLAY_H / 2.0)
            self.circle_radius = min(DISPLAY_W, DISPLAY_H) * 0.35
        self._set_circle_controls_active(True)
        self.title_label.config(
            text="Drag inside circle to move, near edge to resize, or drag new circle"
        )
        self._render_preview()

    def clear_circle(self):
        self.calibration_mode = False
        self.circle_mode = False
        self.circle_center = None
        self.circle_radius = 0.0
        self.drag_action = None
        self._set_circle_controls_active(False)
        if not self.is_live and self.captured_frame is not None:
            self._render_preview()

    def on_mouse_down(self, event):
        if not self.circle_mode or self.is_live or self.captured_frame is None:
            return

        x = max(0.0, min(float(DISPLAY_W - 1), float(event.x)))
        y = max(0.0, min(float(DISPLAY_H - 1), float(event.y)))
        self.drag_start = (x, y)

        if self.circle_center is not None and self.circle_radius > 5:
            cx, cy = self.circle_center
            dist = math.hypot(x - cx, y - cy)
            if abs(dist - self.circle_radius) <= 14.0:
                self.drag_action = "resize"
                self.orig_circle = (cx, cy, self.circle_radius)
                return
            elif dist < self.circle_radius - 14.0:
                self.drag_action = "move"
                self.orig_circle = (cx, cy, self.circle_radius)
                return

        self.drag_action = "create"
        self.circle_center = (x, y)
        self.circle_radius = 5.0
        self._render_preview()

    def on_mouse_drag(self, event):
        if not self.circle_mode or self.drag_action is None or self.drag_start is None:
            return

        x = max(0.0, min(float(DISPLAY_W - 1), float(event.x)))
        y = max(0.0, min(float(DISPLAY_H - 1), float(event.y)))
        sx, sy = self.drag_start

        if self.drag_action == "create":
            self.circle_radius = max(5.0, math.hypot(x - sx, y - sy))
        elif self.drag_action == "move" and self.orig_circle is not None:
            ocx, ocy, r = self.orig_circle
            self.circle_center = (ocx + (x - sx), ocy + (y - sy))
        elif self.drag_action == "resize" and self.orig_circle is not None:
            cx, cy, _ = self.orig_circle
            self.circle_radius = max(8.0, math.hypot(x - cx, y - cy))

        self._render_preview()

    def on_mouse_up(self, event):
        self.drag_action = None
        self.drag_start = None
        self.orig_circle = None

    def apply_circle_crop(self):
        if self.captured_frame is None or self.circle_center is None or self.circle_radius <= 2:
            messagebox.showwarning(
                "Crop Warning", "Draw a valid circle on the image first.", parent=self.window
            )
            return

        h, w = self.captured_frame.shape[:2]
        scale_x = w / float(DISPLAY_W)
        scale_y = h / float(DISPLAY_H)

        cx = self.circle_center[0] * scale_x
        cy = self.circle_center[1] * scale_y
        r = self.circle_radius * ((scale_x + scale_y) / 2.0)

        self.crop_roi = (cx, cy, r)

        yy, xx = np.ogrid[:h, :w]
        mask = ((xx - cx) ** 2 + (yy - cy) ** 2) <= (r ** 2)

        cropped = np.zeros_like(self.captured_frame)
        cropped[mask] = self.captured_frame[mask]

        self.captured_frame = cropped
        self.last_processed_image = None
        self.calibration_mode = False
        self.circle_mode = False
        self.circle_center = None
        self.circle_radius = 0.0
        self._set_circle_controls_active(False)
        self.title_label.config(text="Circle Crop Applied (Ready to Count)")
        self._render_preview()

    # --- Colony Counting & Live Feed Controls ---
    def capture_and_count(self):
        if self.is_live:
            if self.current_frame is None:
                messagebox.showwarning("Warning", "No active frame available yet.", parent=self.window)
                return
            self._stop_live_loop()
            self.captured_frame = self.current_frame.copy()
            self.crop_roi = None

        if self.captured_frame is None:
            messagebox.showwarning(
                "Warning", "No captured or opened image available.", parent=self.window
            )
            return

        self.calibration_mode = False
        self.circle_mode = False
        img_to_process = self.captured_frame.copy()
        min_area_mm2 = float(self.size_slider.get())
        min_area_px = self._get_min_area_px()
        c_val = int(self.sensitivity_slider.get())
        h, w = img_to_process.shape[:2]

        inner_mask = None
        if self.crop_roi is not None:
            cx, cy, r = self.crop_roi
            yy, xx = np.ogrid[:h, :w]
            roi_mask = ((xx - cx) ** 2 + (yy - cy) ** 2) <= (r ** 2)
            r_inner = max(1.0, r - 2.0)
            inner_mask = ((xx - cx) ** 2 + (yy - cy) ** 2) <= (r_inner ** 2)

            if np.any(roi_mask):
                mean_bgr = img_to_process[roi_mask].mean(axis=0).astype(np.uint8)
                filled_for_thresh = np.empty_like(img_to_process)
                filled_for_thresh[:, :] = mean_bgr
                filled_for_thresh[roi_mask] = img_to_process[roi_mask]
            else:
                filled_for_thresh = img_to_process
        else:
            filled_for_thresh = img_to_process

        gray = cv2.cvtColor(filled_for_thresh, cv2.COLOR_BGR2GRAY)

        thresh = cv2.adaptiveThreshold(
            gray,
            255,
            cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
            cv2.THRESH_BINARY_INV,
            blockSize=31,
            C=c_val,
        )

        if inner_mask is not None:
            thresh[~inner_mask] = 0

        kernel = np.ones((3, 3), np.uint8)
        opened = cv2.morphologyEx(thresh, cv2.MORPH_OPEN, kernel)

        if inner_mask is not None:
            opened[~inner_mask] = 0

        contours, _ = cv2.findContours(opened, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)

        valid_count = 0
        for cnt in contours:
            area = cv2.contourArea(cnt)
            if area >= min_area_px:
                (x, y), radius = cv2.minEnclosingCircle(cnt)
                if inner_mask is not None:
                    cx, cy, r = self.crop_roi
                    r_inner = max(1.0, r - 2.0)
                    if math.hypot(x - cx, y - cy) > r_inner:
                        continue
                valid_count += 1
                draw_radius = max(2, int(round(radius)))
                cv2.circle(
                    img_to_process, (int(round(x)), int(round(y))), draw_radius, (255, 255, 0), 2
                )

        self.last_processed_image = img_to_process.copy()

        self.lbl_count.config(
            text=f"Count: {valid_count} Colonies (Area >= {min_area_mm2:g} mm², C={c_val})"
        )
        self.title_label.config(text="Processed Image Result")
        self._render_preview(explicit_bgr=self.last_processed_image)

    def resume_live(self):
        self.crop_roi = None
        self.last_processed_image = None
        self.clear_circle()
        if self.cap is None or not self.cap.isOpened():
            self.connect_camera(auto_fallback=True)
            return
        self.captured_frame = None
        self.is_live = True
        self.lbl_count.config(text="Count: --")
        self.title_label.config(text=f"Live Camera Feed (Index {self.cam_index_var.get()})")
        self.update_feed()

    def on_closing(self):
        self._release_camera()
        self.window.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app = ColonyCounterApp(root, "Microbial Colony Counter")
    root.mainloop()