"""ZPL Visual Editor – versione completa e funzionante con migliorie
-------------------------------------------------------------------
• Editor visuale in Tkinter per etichette Zebra
• Salvataggio/caricamento progetto (.json)
• Import di file ZPL (parser avanzato)
• Esportazione/copia/anteprima ZPL
• Snap to grid opzionale
• Copia/Incolla oggetti
• Layer management (porta avanti/indietro)
• Tasti rapidi (Canc, Ctrl+C/V, Ctrl+S, Ctrl+Z/Y)
• Undo/Redo stack
• Anteprima più realistica

testa con: 
-https://labelary.com/viewer.html
-https://www.zplprinter.com/
-https://zplpreview.com/?ref=hackernoon.com
NB: Il canvas è visualizzato a metà risoluzione (SCALE = 1.0)
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import json
import re
import copy
from dataclasses import dataclass, asdict
from typing import List, Optional, Dict, Any

# -------------------- Data model -------------------- #
@dataclass
class LabelSettings:
    width_mm: float = 100.0
    height_mm: float = 50.0
    dpi: int = 203
    border: bool = False
    orientation: str = "Portrait"  # Portrait | Landscape
    snap_to_grid: bool = False
    grid_size: int = 10

@dataclass
class ZPLObject:
    obj_type: str
    x: int
    y: int
    width: int = 0
    height: int = 0
    text: str = ""
    font_size: str = "30"
    font_type: str = "A"
    rotation: int = 0
    thickness: int = 2
    barcode_type: str = "128"
    line_thickness: int = 3
    selected: bool = False
    id: str = ""
    # Barcode params
    bar_module: int = 3
    bar_ratio: int = 2
    bar_height: int = 100
    hri_above: bool = False

    def __post_init__(self):
        if not self.id:
            import uuid
            self.id = str(uuid.uuid4())[:8]

# -------------------- Action for Undo/Redo -------------------- #
@dataclass
class Action:
    action_type: str  # add, delete, modify, move
    object_id: str
    old_state: Optional[Dict] = None
    new_state: Optional[Dict] = None

# -------------------- ZPL Parser -------------------- #
class ZPLParser:
    @staticmethod
    def parse_zpl_file(content: str) -> List[ZPLObject]:
        """Parse ZPL content and return list of ZPLObject instances"""
        objects = []
        lines = content.split('\n')
        current_x, current_y = 0, 0
        current_font_type = "A"
        current_font_size = "30"
        for line in lines:
            line = line.strip()
            if not line:
                continue
            # Field Origin ^FO
            if line.startswith('^FO'):
                coords = re.findall(r'\d+', line)
                if len(coords) >= 2:
                    current_x, current_y = int(coords[0]), int(coords[1])
            # Font ^A
            elif line.startswith('^A'):
                font_match = re.match(r'\^A([A-Z0-9]),N,(\d+)', line)
                if font_match:
                    current_font_type = font_match.group(1)
                    current_font_size = font_match.group(2)
            # Text Field ^FD
            elif line.startswith('^FD'):
                text = line[3:].replace('^FS', '')
                obj = ZPLObject("text", current_x, current_y, 100, 30, text)
                obj.font_type = current_font_type
                obj.font_size = current_font_size
                objects.append(obj)
            # Graphic Box ^GB
            elif line.startswith('^GB'):
                params = re.findall(r'\d+', line)
                if len(params) >= 2:
                    width, height = int(params[0]), int(params[1])
                    thickness = int(params[2]) if len(params) > 2 else 2
                    obj = ZPLObject("rectangle", current_x, current_y, width, height)
                    obj.thickness = thickness
                    objects.append(obj)
            # Graphic Circle ^GC
            elif line.startswith('^GC'):
                params = re.findall(r'\d+', line)
                if len(params) >= 1:
                    diameter = int(params[0])
                    thickness = int(params[1]) if len(params) > 1 else 2
                    obj = ZPLObject("circle", current_x, current_y, diameter, diameter)
                    obj.thickness = thickness
                    objects.append(obj)
            # Barcode ^B
            elif line.startswith('^B'):
                barcode_match = re.match(r'\^B([A-Z0-9]+)', line)
                if barcode_match:
                    obj = ZPLObject("barcode", current_x, current_y, 120, 60)
                    obj.barcode_type = barcode_match.group(1)
                    objects.append(obj)
        return objects

# -------------------- Editor -------------------- #
class ZPLEditor:
    SCALE = 1.0  # Canvas displayed at real resolution

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("ZPL Visual Editor – Label Designer")
        self.root.geometry("1400x900")
        self.label_settings = LabelSettings()
        self.objects: List[ZPLObject] = []
        self.selected_object: Optional[ZPLObject] = None
        self.drag_data = {"x": 0, "y": 0, "item": None}
        self.clipboard_object: Optional[ZPLObject] = None
        self.zoom = 1.0  # Fattore di zoom (1.0 = 100%)
        self._zoom_var = tk.StringVar(value=f"{int(self.zoom*100)}%")
        # Undo/Redo system
        self.undo_stack: List[List[ZPLObject]] = []
        self.redo_stack: List[List[ZPLObject]] = []
        self.max_undo_steps = 50
        
        self.setup_ui()
        self.update_canvas_size()
        self.setup_keyboard_bindings()
        self.save_state()  # Initial state

    # -------------------- UI Setup -------------------- #
    def setup_ui(self):
        main = ttk.Frame(self.root)
        main.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.setup_toolbar(main)
        content = ttk.Frame(main)
        content.pack(fill=tk.BOTH, expand=True)
        self.setup_left_panel(content)
        self.setup_canvas(content)
        self.setup_right_panel(content)
        self.setup_bottom_panel(main)

    def setup_toolbar(self, parent):
        bar = ttk.Frame(parent)
        bar.pack(fill=tk.X, pady=(0,5))
        
        # File operations
        file_frame = ttk.LabelFrame(bar, text="File")
        file_frame.pack(side=tk.LEFT, padx=(0,10))
        
        ttk.Button(file_frame, text="Nuovo", command=self.new_project).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_frame, text="Apri Progetto", command=self.import_project).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_frame, text="Salva", command=self.save_project).pack(side=tk.LEFT, padx=2)
        ttk.Button(file_frame, text="Importa ZPL", command=self.import_zpl_file).pack(side=tk.LEFT, padx=2)
        
        # Edit operations
        edit_frame = ttk.LabelFrame(bar, text="Modifica")
        edit_frame.pack(side=tk.LEFT, padx=(0,10))
        
        ttk.Button(edit_frame, text="↶ Undo", command=self.undo).pack(side=tk.LEFT, padx=2)
        ttk.Button(edit_frame, text="↷ Redo", command=self.redo).pack(side=tk.LEFT, padx=2)
        ttk.Button(edit_frame, text="Copia", command=self.copy_object).pack(side=tk.LEFT, padx=2)
        ttk.Button(edit_frame, text="Incolla", command=self.paste_object).pack(side=tk.LEFT, padx=2)
        ttk.Button(edit_frame, text="Elimina", command=self.delete_selected).pack(side=tk.LEFT, padx=2)
        
        # Layer operations
        layer_frame = ttk.LabelFrame(bar, text="Layer")
        layer_frame.pack(side=tk.LEFT, padx=(0,10))
        
        ttk.Button(layer_frame, text="⬆ Avanti", command=self.bring_forward).pack(side=tk.LEFT, padx=2)
        ttk.Button(layer_frame, text="⬇ Indietro", command=self.send_backward).pack(side=tk.LEFT, padx=2)
        
        # Settings
        settings_frame = ttk.LabelFrame(bar, text="Impostazioni")
        settings_frame.pack(side=tk.LEFT, padx=(0,10))
        
        ttk.Button(settings_frame, text="Etichetta", command=self.show_label_settings).pack(side=tk.LEFT, padx=2)
        ttk.Button(settings_frame, text="Cancella Tutto", command=self.clear_all).pack(side=tk.LEFT, padx=2)
        # Zoom controls
        zoom_frame = ttk.LabelFrame(bar, text="Zoom")
        zoom_frame.pack(side=tk.LEFT, padx=(0,10))
        ttk.Button(zoom_frame, text="➖", command=lambda: self.set_zoom(self.zoom / 1.2)).pack(side=tk.LEFT, padx=2)
        ttk.Label(zoom_frame, textvariable=self._zoom_var, width=5, anchor="center").pack(side=tk.LEFT)
        ttk.Button(zoom_frame, text="➕", command=lambda: self.set_zoom(self.zoom * 1.2)).pack(side=tk.LEFT, padx=2)

    def setup_left_panel(self, parent):
        frame = ttk.LabelFrame(parent, text="Oggetti ZPL", width=200)
        frame.pack(side=tk.LEFT, fill=tk.Y, padx=(0,5))
        frame.pack_propagate(False)
        
        items = [
            ("📝 Testo", "text"),
            ("📊 Barcode", "barcode"),
            ("🔲 Rettangolo", "rectangle"),
            ("➖ Linea", "line"),
            ("⚫ Cerchio", "circle"),
            ("🖼️ Immagine", "image")
        ]
        
        for lbl, typ in items:
            ttk.Button(frame, text=lbl, command=lambda t=typ: self.add_object(t)).pack(fill=tk.X, padx=5, pady=2)

    def setup_canvas(self, parent):
        outer = ttk.LabelFrame(parent, text="Area di Progettazione")
        outer.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,5))
        
        cont = ttk.Frame(outer)
        cont.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.canvas = tk.Canvas(cont, bg="white")
        hbar = ttk.Scrollbar(cont, orient=tk.HORIZONTAL, command=self.canvas.xview)
        vbar = ttk.Scrollbar(cont, orient=tk.VERTICAL, command=self.canvas.yview)
        
        self.canvas.configure(xscrollcommand=hbar.set, yscrollcommand=vbar.set)
        
        self.canvas.grid(row=0, column=0, sticky="nsew")
        hbar.grid(row=1, column=0, sticky="ew")
        vbar.grid(row=0, column=1, sticky="ns")
        
        cont.rowconfigure(0, weight=1)
        cont.columnconfigure(0, weight=1)
        
        # Canvas events
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<Double-Button-1>", self.on_canvas_double_click)

    def setup_right_panel(self, parent):
        self.right = ttk.LabelFrame(parent, text="Proprietà", width=280)
        self.right.pack(side=tk.RIGHT, fill=tk.Y)
        self.right.pack_propagate(False)
        
        # Info section
        info = ttk.Frame(self.right)
        info.pack(fill=tk.X, padx=5, pady=5)
        self.info_lbl = ttk.Label(info, text="Nessun oggetto selezionato", font=("Arial", 9, "italic"))
        self.info_lbl.pack()
        
        # Properties section
        self.props_frame = ttk.Frame(self.right)
        self.props_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

    def setup_bottom_panel(self, parent):
        bot = ttk.Frame(parent)
        bot.pack(fill=tk.X, pady=(5,0))
        
        box = ttk.LabelFrame(bot, text="Esportazione ZPL")
        box.pack(fill=tk.X, padx=5, pady=5)
        
        row = ttk.Frame(box)
        row.pack(pady=8)
        
        ttk.Button(row, text="💾 Salva ZPL", command=self.export_to_file).pack(side=tk.LEFT, padx=(0,10))
        ttk.Button(row, text="📋 Copia ZPL", command=self.copy_to_clipboard).pack(side=tk.LEFT)
        ttk.Button(row, text="👁️ Anteprima ZPL", command=self.preview_zpl).pack(side=tk.LEFT, padx=(10,0))
        ttk.Button(row, text="✓ Valida ZPL", command=self.validate_zpl).pack(side=tk.LEFT, padx=(10,0))
        # Nota font
        note = ttk.Label(bot, text="Nota: la visualizzazione dei font è indicativa. La stampa reale potrebbe differire dai font di sistema.", font=("Arial", 9, "italic"), foreground="gray")
        note.pack(fill=tk.X, padx=8, pady=(2, 0))

    def setup_keyboard_bindings(self):
        """Setup keyboard shortcuts"""
        self.root.bind('<Control-s>', lambda e: self.save_project())
        self.root.bind('<Control-o>', lambda e: self.import_project())
        self.root.bind('<Control-c>', lambda e: self.copy_object())
        self.root.bind('<Control-v>', lambda e: self.paste_object())
        self.root.bind('<Control-z>', lambda e: self.undo())
        self.root.bind('<Control-y>', lambda e: self.redo())
        self.root.bind('<Delete>', lambda e: self.delete_selected())
        self.root.bind('<BackSpace>', lambda e: self.delete_selected())

    # -------------- Label Settings Dialog -------------- #
    def show_label_settings(self):
        win = tk.Toplevel(self.root)
        win.title("Impostazioni Etichetta")
        win.geometry("450x400")
        win.transient(self.root)
        win.grab_set()
        
        # Helper function to add row
        def add_row(lbl, var, r, widget=ttk.Entry, **opts):
            ttk.Label(win, text=lbl).grid(row=r, column=0, sticky="w", padx=10, pady=5)
            w = widget(win, textvariable=var, **opts)
            w.grid(row=r, column=1, sticky="ew", padx=10, pady=5)
            return w
        
        # Variables
        wv = tk.DoubleVar(value=self.label_settings.width_mm)
        hv = tk.DoubleVar(value=self.label_settings.height_mm)
        dv = tk.IntVar(value=self.label_settings.dpi)
        bv = tk.BooleanVar(value=self.label_settings.border)
        ov = tk.StringVar(value=self.label_settings.orientation)
        sv = tk.BooleanVar(value=self.label_settings.snap_to_grid)
        gv = tk.IntVar(value=self.label_settings.grid_size)
        
        # Form fields
        add_row("Larghezza (mm):", wv, 0)
        add_row("Altezza (mm):", hv, 1)
        add_row("DPI:", dv, 2, widget=ttk.Combobox, values=[203, 300, 600], state="readonly")
        
        ttk.Checkbutton(win, text="Bordo etichetta", variable=bv).grid(row=3, column=0, columnspan=2, sticky="w", padx=10, pady=5)
        
        add_row("Orientamento:", ov, 4, widget=ttk.Combobox, values=["Portrait", "Landscape"], state="readonly")
        
        ttk.Checkbutton(win, text="Snap to grid", variable=sv).grid(row=5, column=0, columnspan=2, sticky="w", padx=10, pady=5)
        add_row("Dimensione griglia:", gv, 6)
        
        # Buttons
        frm = ttk.Frame(win)
        frm.grid(row=7, column=0, columnspan=2, pady=15)
        
        def apply():
            self.label_settings.width_mm = wv.get()
            self.label_settings.height_mm = hv.get()
            self.label_settings.dpi = dv.get()
            self.label_settings.border = bv.get()
            self.label_settings.orientation = ov.get()
            self.label_settings.snap_to_grid = sv.get()
            self.label_settings.grid_size = gv.get()
            self.update_canvas_size()
            win.destroy()
        
        ttk.Button(frm, text="Applica", command=apply).pack(side=tk.RIGHT, padx=5)
        ttk.Button(frm, text="Annulla", command=win.destroy).pack(side=tk.RIGHT)
        
        win.columnconfigure(1, weight=1)

    # -------------- Canvas size and grid -------------- #
    def canvas_size(self):
        """Calculate canvas size in pixels"""
        dpi = self.label_settings.dpi
        if self.label_settings.orientation == "Landscape":
            w = int(self.label_settings.height_mm * dpi / 25.4 / self.SCALE)
            h = int(self.label_settings.width_mm * dpi / 25.4 / self.SCALE)
        else:
            w = int(self.label_settings.width_mm * dpi / 25.4 / self.SCALE)
            h = int(self.label_settings.height_mm * dpi / 25.4 / self.SCALE)
        # Applica zoom solo alla visualizzazione
        return int(w * self.zoom), int(h * self.zoom)

    def update_canvas_size(self):
        """Update canvas scroll region"""
        w, h = self.canvas_size()
        self.canvas.configure(scrollregion=(0, 0, w + 50, h + 50))
        self.redraw_objects()

    def snap_to_grid(self, x, y):
        """Snap coordinates to grid if enabled"""
        if not self.label_settings.snap_to_grid:
            return x, y
        grid_size = self.label_settings.grid_size
        return round(x / grid_size) * grid_size, round(y / grid_size) * grid_size

    # -------------- Object CRUD & Rendering -------------- #
    def add_object(self, obj_type):
        """Add new object to canvas"""
        defaults = {
            "text": {"width": 100, "height": 30, "text": "Esempio", "font_size": "30", "font_type": "A"},
            "barcode": {"width": 120, "height": 60, "text": "123456789", "bar_module": 3, "bar_ratio": 2, "bar_height": 100, "hri_above": False},
            "rectangle": {"width": 80, "height": 40},
            "line": {"width": 100, "height": 0},
            "circle": {"width": 40, "height": 40},
            "image": {"width": 60, "height": 60, "text": "image.bmp"}
        }
        d = defaults.get(obj_type, {})
        x, y = self.snap_to_grid(50, 50)
        obj = ZPLObject(
            obj_type, x, y,
            d.get("width", 50),
            d.get("height", 20),
            d.get("text", ""),
            d.get("font_size", "30"),
            d.get("font_type", "A"),
            0,  # rotation
            2,  # thickness
            d.get("barcode_type", "128"),
            3,  # line_thickness
            False,  # selected
            "",
            d.get("bar_module", 3),
            d.get("bar_ratio", 2),
            d.get("bar_height", 100),
            d.get("hri_above", False)
        )
        self.objects.append(obj)
        self.select_object(obj)
        self.redraw_objects()
        self.save_state()

    def delete_selected(self):
        """Delete selected object"""
        if self.selected_object:
            self.objects.remove(self.selected_object)
            self.selected_object = None
            self.redraw_objects()
            self.update_properties_panel()
            self.save_state()

    def clear_all(self):
        """Clear all objects"""
        if messagebox.askyesno("Conferma", "Eliminare tutti gli oggetti?"):
            self.objects.clear()
            self.selected_object = None
            self.redraw_objects()
            self.update_properties_panel()
            self.save_state()

    # -------------- Canvas interaction -------------- #
    def on_canvas_click(self, e):
        """Handle canvas click"""
        self.canvas.focus_set()  # Dai focus alla canvas
        # Applica l'inverso dello zoom per la selezione
        x, y = self.canvas.canvasx(e.x) / self.zoom, self.canvas.canvasy(e.y) / self.zoom
        clicked = None
        
        # Find clicked object (reverse order for top-to-bottom selection)
        for obj in reversed(self.objects):
            if obj.x <= x <= obj.x + obj.width and obj.y <= y <= obj.y + obj.height:
                clicked = obj
                break
        
        if clicked:
            self.select_object(clicked)
            self.drag_data.update({"x": x, "y": y, "item": clicked})
        else:
            self.select_object(None)

    def on_canvas_drag(self, e):
        """Handle canvas drag"""
        if self.drag_data["item"]:
            # Applica l'inverso dello zoom per il drag
            x, y = self.canvas.canvasx(e.x) / self.zoom, self.canvas.canvasy(e.y) / self.zoom
            dx, dy = x - self.drag_data["x"], y - self.drag_data["y"]
            
            obj = self.drag_data["item"]
            new_x, new_y = self.snap_to_grid(obj.x + int(dx), obj.y + int(dy))
            obj.x, obj.y = new_x, new_y
            
            self.drag_data.update({"x": x, "y": y})
            self.redraw_objects()
            self.update_properties_panel()

    def on_canvas_release(self, e):
        """Handle canvas release"""
        if self.drag_data["item"]:
            self.save_state()  # Save state after move
        self.drag_data["item"] = None

    def on_canvas_double_click(self, e):
        """Handle double click to edit properties"""
        if self.selected_object:
            self.show_object_properties(self.selected_object)

    def select_object(self, obj):
        """Select object"""
        for o in self.objects:
            o.selected = False
        
        self.selected_object = obj
        if obj:
            obj.selected = True
        
        self.redraw_objects()
        self.update_properties_panel()

    def redraw_objects(self):
        """Redraw all objects on canvas"""
        self.canvas.delete("all")
        
        # Draw grid if enabled
        if self.label_settings.snap_to_grid:
            self.draw_grid()
        
        # Draw label border
        w, h = self.canvas_size()
        if self.label_settings.border:
            style = {"outline": "black", "width": 2}
        else:
            style = {"outline": "gray", "width": 1, "dash": (5, 5)}
        
        self.canvas.create_rectangle(0, 0, w, h, fill="white", **style)
        
        # Draw all objects
        for obj in self.objects:
            self._draw_object(obj)

    def draw_grid(self):
        """Draw grid on canvas"""
        w, h = self.canvas_size()
        grid_size = int(self.label_settings.grid_size * self.zoom)
        
        # Vertical lines
        for x in range(0, w + 1, grid_size):
            self.canvas.create_line(x, 0, x, h, fill="lightgray", width=1)
        
        # Horizontal lines
        for y in range(0, h + 1, grid_size):
            self.canvas.create_line(0, y, w, y, fill="lightgray", width=1)

    def _draw_object(self, obj):
        """Draw single object"""
        color = "red" if obj.selected else "black"
        line_width = 3 if obj.selected else 1
        zx = obj.x * self.zoom
        zy = obj.y * self.zoom
        zw = obj.width * self.zoom
        zh = obj.height * self.zoom
        if obj.obj_type == "text":
            try:
                dpi = self.label_settings.dpi
                font_px = int(obj.font_size)
                altezza_mm = font_px * 25.4 / dpi
                altezza_canvas_px = int(altezza_mm * dpi / 25.4 * self.zoom)
                size = max(8, min(200, altezza_canvas_px))
            except Exception:
                size = 12
            font_family = self.get_zpl_font_family(obj.font_type)
            # Disegna il testo normalmente
            temp = self.canvas.create_text(0, 0, text=obj.text, font=(font_family, -size), anchor="nw")
            bbox = self.canvas.bbox(temp)
            self.canvas.delete(temp)
            if bbox:
                obj.width, obj.height = int((bbox[2] - bbox[0]) / self.zoom), int((bbox[3] - bbox[1]) / self.zoom)
            # Stretch orizzontale per simulare la larghezza ZPL (es. 1.2x)
            stretch = 1.2  # Puoi regolare questo valore per avvicinarti alla stampa reale
            self.canvas.scale("text", zx, zy, stretch, 1)
            self.canvas.create_text(zx, zy, text=obj.text, font=(font_family, -size), fill=color, anchor="nw", tags="text")
            self.canvas.scale("text", zx, zy, 1/stretch, 1)  # Reset scale per i prossimi oggetti
        elif obj.obj_type == "barcode":
            self.canvas.create_rectangle(zx, zy, zx + zw, zy + zh, outline=color, width=line_width, fill="white")
            btype = obj.barcode_type
            module = max(1, int(obj.bar_module * self.zoom))
            ratio = max(2, int(obj.bar_ratio))
            # Altezza effettiva delle barre
            bar_h = zh - 15 * self.zoom
            if btype == "128":
                # Barre larghe e strette alternate
                x_pos = zx + 2 * self.zoom
                toggle = True
                while x_pos < zx + zw - 2 * self.zoom:
                    w = module * (ratio if toggle else 1)
                    self.canvas.create_rectangle(x_pos, zy+2*self.zoom, x_pos+w, zy+bar_h, fill=color, outline=color)
                    x_pos += w
                    toggle = not toggle
            elif btype == "39":
                # Barre larghe e strette alternate
                x_pos = zx + 2 * self.zoom
                toggle = True
                while x_pos < zx + zw - 2 * self.zoom:
                    w = module * (ratio if toggle else 1)
                    self.canvas.create_rectangle(x_pos, zy+2*self.zoom, x_pos+w, zy+bar_h, fill=color, outline=color)
                    x_pos += w
                    toggle = not toggle
            elif btype == "EAN13":
                # Pattern centrale e barre corte ai lati
                for i in range(0, int(zw), module*ratio):
                    h = bar_h if i < zw//3 or i > 2*zw//3 else zh-8*self.zoom
                    self.canvas.create_rectangle(zx+i, zy+2*self.zoom, zx+i+module, zy+h, fill=color, outline=color)
            elif btype == "I25":
                # Barre doppie
                x_pos = zx + 2 * self.zoom
                while x_pos < zx + zw - 2 * self.zoom:
                    self.canvas.create_rectangle(x_pos, zy+2*self.zoom, x_pos+module*2, zy+bar_h, fill=color, outline=color)
                    x_pos += module*ratio
            else:
                # Default: barre strette
                for i in range(0, int(zw), module):
                    self.canvas.create_rectangle(zx+i, zy+2*self.zoom, zx+i+1*self.zoom, zy+bar_h, fill=color, outline=color)
            # Mostra il testo sopra o sotto il barcode
            text_y = zy - 12 * self.zoom if obj.hri_above else zy + zh - 12 * self.zoom
            self.canvas.create_text(
                zx + zw // 2,
                text_y,
                text=obj.text[:20],
                font=("Courier New", int(8 * self.zoom)),
                fill=color,
                anchor="n" if not obj.hri_above else "s"
            )
        elif obj.obj_type == "rectangle":
            self.canvas.create_rectangle(zx, zy, zx + zw, zy + zh, 
                                       outline=color, width=max(1, int(obj.thickness * self.zoom)))
        elif obj.obj_type == "line":
            self.canvas.create_line(zx, zy, zx + zw, zy + zh, 
                                  fill=color, width=int(obj.line_thickness * self.zoom))
        elif obj.obj_type == "circle":
            diameter = min(zw, zh)
            self.canvas.create_oval(zx, zy, zx + zw, zy + zh, 
                                  outline=color, width=line_width)
        elif obj.obj_type == "image":
            self.canvas.create_rectangle(zx, zy, zx + zw, zy + zh, 
                                       outline=color, width=line_width, fill="lightgray")
            self.canvas.create_text(zx + zw//2, zy + zh//2, 
                                  text="IMG", fill=color, font=("Arial", int(10 * self.zoom), "bold"))
            # Show filename
            self.canvas.create_text(zx + zw//2, zy + zh//2 + 15 * self.zoom, 
                                  text=obj.text, fill=color, font=("Arial", int(8 * self.zoom)))
        
        # Draw selection handles
        if obj.selected:
            handles = [
                (zx - 3, zy - 3),
                (zx + zw + 3, zy - 3),
                (zx - 3, zy + zh + 3),
                (zx + zw + 3, zy + zh + 3)
            ]
            
            for hx, hy in handles:
                self.canvas.create_rectangle(hx - 2, hy - 2, hx + 2, hy + 2, 
                                           fill="red", outline="darkred")

    def get_zpl_font_family(self, font_type):
        """Map ZPL font types to system fonts (più differenziato)"""
        font_map = {
            "A": "Arial",
            "B": "Times New Roman",
            "C": "Courier New",
            "D": "Verdana",
            "E": "Tahoma",
            "F": "Consolas",
            "G": "Georgia",
            "H": "Comic Sans MS",
            "0": "Arial Black"
        }
        return font_map.get(font_type, "Arial")

    # -------------- Properties panel -------------- #
    def update_properties_panel(self):
        """Update properties panel for selected object"""
        # Clear existing widgets
        for widget in self.props_frame.winfo_children():
            widget.destroy()
        if not self.selected_object:
            self.info_lbl.config(text="Nessun oggetto selezionato")
            return
        obj = self.selected_object
        self.info_lbl.config(text=f"Selezionato: {obj.obj_type} (ID: {obj.id[:8]})")
        row = 0
        # Position
        self.add_property_row("X:", obj, "x", row, int)
        row += 1
        self.add_property_row("Y:", obj, "y", row, int)
        row += 1
        # Size
        if obj.obj_type == "circle":
            # Mostra solo il diametro
            def set_diameter(val):
                try:
                    d = int(val)
                    if obj.width != d or obj.height != d:
                        obj.width = d
                        obj.height = d
                        self.redraw_objects()
                except ValueError:
                    pass
            ttk.Label(self.props_frame, text="Diametro:").grid(row=row, column=0, sticky="w", padx=2, pady=2)
            var = tk.StringVar(value=str(obj.width))
            entry = ttk.Entry(self.props_frame, textvariable=var, width=12)
            entry.grid(row=row, column=1, sticky="ew", padx=2, pady=2)
            var.trace_add('write', lambda *args: set_diameter(var.get()))
            entry.bind('<FocusOut>', lambda e: self.save_state())
            row += 1
        elif obj.obj_type != "line":
            self.add_property_row("Larghezza:", obj, "width", row, int)
            row += 1
            self.add_property_row("Altezza:", obj, "height", row, int)
            row += 1
        else:
            self.add_property_row("Lunghezza X:", obj, "width", row, int)
            row += 1
            self.add_property_row("Lunghezza Y:", obj, "height", row, int)
            row += 1
        # Object-specific properties
        if obj.obj_type in ["text", "barcode", "image"]:
            self.add_property_row("Testo:", obj, "text", row, str)
            row += 1
        if obj.obj_type == "text":
            self.add_combobox_row("Font:", obj, "font_type", row, ["A", "B", "C", "D", "E", "F", "G", "H", "0"])
            row += 1
            self.add_property_row("Dimensione:", obj, "font_size", row, str)
            row += 1
        if obj.obj_type == "barcode":
            barcode_types = [
                ("128", "Code128"),
                ("39", "Code39"),
                ("93", "Code93"),
                ("I25", "Interleaved 2/5"),
                ("EAN13", "EAN-13"),
                ("EAN8", "EAN-8"),
                ("UPCA", "UPC-A"),
                ("UPCE", "UPC-E")
            ]
            self.add_combobox_row("Tipo:", obj, "barcode_type", row, [k for k, v in barcode_types])
            desc = dict(barcode_types).get(obj.barcode_type, obj.barcode_type)
            ttk.Label(self.props_frame, text=f"({desc})", foreground="gray").grid(row=row, column=2, sticky="w")
            row += 1
            # Modulo
            def set_bar_module(val):
                try:
                    v = int(val)
                    if obj.bar_module != v:
                        obj.bar_module = v
                        self.redraw_objects()
                except ValueError:
                    pass
            ttk.Label(self.props_frame, text="Modulo:").grid(row=row, column=0, sticky="w", padx=2, pady=2)
            bar_mod_var = tk.StringVar(value=str(obj.bar_module))
            bar_mod_entry = ttk.Entry(self.props_frame, textvariable=bar_mod_var, width=8)
            bar_mod_entry.grid(row=row, column=1, sticky="ew", padx=2, pady=2)
            bar_mod_var.trace_add('write', lambda *args: set_bar_module(bar_mod_var.get()))
            bar_mod_entry.bind('<FocusOut>', lambda e: self.save_state())
            row += 1
            # Rapporto
            def set_bar_ratio(val):
                try:
                    v = int(val)
                    if obj.bar_ratio != v:
                        obj.bar_ratio = v
                        self.redraw_objects()
                except ValueError:
                    pass
            ttk.Label(self.props_frame, text="Rapporto:").grid(row=row, column=0, sticky="w", padx=2, pady=2)
            bar_ratio_var = tk.StringVar(value=str(obj.bar_ratio))
            bar_ratio_entry = ttk.Entry(self.props_frame, textvariable=bar_ratio_var, width=8)
            bar_ratio_entry.grid(row=row, column=1, sticky="ew", padx=2, pady=2)
            bar_ratio_var.trace_add('write', lambda *args: set_bar_ratio(bar_ratio_var.get()))
            bar_ratio_entry.bind('<FocusOut>', lambda e: self.save_state())
            row += 1
            # Altezza (in dots)
            def set_bar_height(val):
                try:
                    v = int(val)
                    if obj.bar_height != v:
                        obj.bar_height = v
                        obj.height = v  # aggiorna anche l'altezza grafica
                        self.redraw_objects()
                except ValueError:
                    pass
            ttk.Label(self.props_frame, text="Altezza (dots):").grid(row=row, column=0, sticky="w", padx=2, pady=2)
            bar_height_var = tk.StringVar(value=str(obj.bar_height))
            bar_height_entry = ttk.Entry(self.props_frame, textvariable=bar_height_var, width=8)
            bar_height_entry.grid(row=row, column=1, sticky="ew", padx=2, pady=2)
            bar_height_var.trace_add('write', lambda *args: set_bar_height(bar_height_var.get()))
            bar_height_entry.bind('<FocusOut>', lambda e: self.save_state())
            row += 1
            # HRI sopra
            hri_var = tk.BooleanVar(value=obj.hri_above)
            def update_hri():
                obj.hri_above = hri_var.get()
                self.redraw_objects()
                self.save_state()
            chk = ttk.Checkbutton(self.props_frame, text="Testo sopra il barcode", variable=hri_var, command=update_hri)
            chk.grid(row=row, column=0, columnspan=2, sticky="w", padx=2, pady=2)
            row += 1
        if obj.obj_type == "circle":
            self.add_property_row("Spessore:", obj, "thickness", row, int)
            row += 1
        if obj.obj_type == "rectangle":
            self.add_property_row("Spessore:", obj, "thickness", row, int)
            row += 1
        if obj.obj_type == "line":
            self.add_property_row("Spessore:", obj, "line_thickness", row, int)
            row += 1
        # Rotation
        self.add_property_row("Rotazione:", obj, "rotation", row, int)
        row += 1

    def add_property_row(self, label, obj, attr, row, data_type):
        """Add a property row to the properties panel"""
        ttk.Label(self.props_frame, text=label).grid(row=row, column=0, sticky="w", padx=2, pady=2)
        
        var = tk.StringVar(value=str(getattr(obj, attr)))
        entry = ttk.Entry(self.props_frame, textvariable=var, width=12)
        entry.grid(row=row, column=1, sticky="ew", padx=2, pady=2)
        
        def update_value(*args):
            try:
                value = data_type(var.get())
                if getattr(obj, attr) != value:
                    setattr(obj, attr, value)
                    self.redraw_objects()
            except ValueError:
                pass
        
        var.trace_add('write', update_value)
        
        # Save state on focus out
        entry.bind('<FocusOut>', lambda e: self.save_state())

    def add_combobox_row(self, label, obj, attr, row, values):
        """Add a combobox row to the properties panel"""
        ttk.Label(self.props_frame, text=label).grid(row=row, column=0, sticky="w", padx=2, pady=2)
        var = tk.StringVar(value=str(getattr(obj, attr)))
        combo = ttk.Combobox(self.props_frame, textvariable=var, values=values, state="readonly", width=10)
        combo.grid(row=row, column=1, sticky="ew", padx=2, pady=2)
        def update_value(*args):
            if getattr(obj, attr) != var.get():
                setattr(obj, attr, var.get())
                self.redraw_objects()
                self.save_state()
        var.trace_add('write', update_value)

    def show_object_properties(self, obj):
        """Show detailed properties dialog"""
        win = tk.Toplevel(self.root)
        win.title(f"Proprietà {obj.obj_type}")
        win.geometry("400x500")
        win.transient(self.root)
        win.grab_set()
        
        # Create a more detailed properties editor
        notebook = ttk.Notebook(win)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # General tab
        general_frame = ttk.Frame(notebook)
        notebook.add(general_frame, text="Generale")
        
        # Position and size
        ttk.Label(general_frame, text="Posizione e Dimensioni", font=("Arial", 10, "bold")).pack(anchor="w", pady=(5,0))
        
        pos_frame = ttk.Frame(general_frame)
        pos_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(pos_frame, text="X:").grid(row=0, column=0, sticky="w")
        x_var = tk.IntVar(value=obj.x)
        ttk.Entry(pos_frame, textvariable=x_var, width=8).grid(row=0, column=1, padx=5)
        
        ttk.Label(pos_frame, text="Y:").grid(row=0, column=2, sticky="w", padx=(10,0))
        y_var = tk.IntVar(value=obj.y)
        ttk.Entry(pos_frame, textvariable=y_var, width=8).grid(row=0, column=3, padx=5)
        
        ttk.Label(pos_frame, text="W:").grid(row=1, column=0, sticky="w")
        w_var = tk.IntVar(value=obj.width)
        ttk.Entry(pos_frame, textvariable=w_var, width=8).grid(row=1, column=1, padx=5)
        
        ttk.Label(pos_frame, text="H:").grid(row=1, column=2, sticky="w", padx=(10,0))
        h_var = tk.IntVar(value=obj.height)
        ttk.Entry(pos_frame, textvariable=h_var, width=8).grid(row=1, column=3, padx=5)
        
        # Object-specific properties
        if obj.obj_type in ["text", "barcode", "image"]:
            ttk.Label(general_frame, text="Contenuto", font=("Arial", 10, "bold")).pack(anchor="w", pady=(15,5))
            text_var = tk.StringVar(value=obj.text)
            text_entry = tk.Text(general_frame, height=3, width=40)
            text_entry.pack(fill=tk.X, pady=5)
            text_entry.insert("1.0", obj.text)
        
        # Apply button
        def apply_changes():
            obj.x = x_var.get()
            obj.y = y_var.get()
            obj.width = w_var.get()
            obj.height = h_var.get()
            
            if obj.obj_type in ["text", "barcode", "image"]:
                obj.text = text_entry.get("1.0", tk.END).strip()
            
            self.redraw_objects()
            self.update_properties_panel()
            self.save_state()
            win.destroy()
        
        button_frame = ttk.Frame(win)
        button_frame.pack(pady=10)
        ttk.Button(button_frame, text="Applica", command=apply_changes).pack(side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="Annulla", command=win.destroy).pack(side=tk.RIGHT)

    # -------------- Copy/Paste -------------- #
    def copy_object(self):
        """Copy selected object to clipboard"""
        if self.selected_object:
            self.clipboard_object = copy.deepcopy(self.selected_object)
            self.clipboard_object.selected = False

    def paste_object(self):
        """Paste object from clipboard"""
        if self.clipboard_object:
            new_obj = copy.deepcopy(self.clipboard_object)
            new_obj.x += 20  # Offset to avoid overlap
            new_obj.y += 20
            new_obj.id = ""  # Reset ID to generate new one
            new_obj.__post_init__()  # Generate new ID
            
            self.objects.append(new_obj)
            self.select_object(new_obj)
            self.redraw_objects()
            self.save_state()

    # -------------- Layer Management -------------- #
    def bring_forward(self):
        """Bring selected object forward"""
        if self.selected_object:
            idx = self.objects.index(self.selected_object)
            if idx < len(self.objects) - 1:
                self.objects[idx], self.objects[idx + 1] = self.objects[idx + 1], self.objects[idx]
                self.redraw_objects()
                self.save_state()

    def send_backward(self):
        """Send selected object backward"""
        if self.selected_object:
            idx = self.objects.index(self.selected_object)
            if idx > 0:
                self.objects[idx], self.objects[idx - 1] = self.objects[idx - 1], self.objects[idx]
                self.redraw_objects()
                self.save_state()

    # -------------- Undo/Redo System -------------- #
    def save_state(self):
        """Save current state for undo/redo"""
        # Create deep copy of current objects
        state = copy.deepcopy(self.objects)
        
        # Add to undo stack
        self.undo_stack.append(state)
        
        # Limit stack size
        if len(self.undo_stack) > self.max_undo_steps:
            self.undo_stack.pop(0)
        
        # Clear redo stack when new action is performed
        self.redo_stack.clear()

    def undo(self):
        """Undo last action"""
        if len(self.undo_stack) > 1:  # Keep at least one state
            # Move current state to redo stack
            current_state = self.undo_stack.pop()
            self.redo_stack.append(current_state)
            
            # Restore previous state
            self.objects = copy.deepcopy(self.undo_stack[-1])
            self.selected_object = None
            self.redraw_objects()
            self.update_properties_panel()

    def redo(self):
        """Redo last undone action"""
        if self.redo_stack:
            # Move state from redo to undo stack
            state = self.redo_stack.pop()
            self.undo_stack.append(state)
            
            # Restore state
            self.objects = copy.deepcopy(state)
            self.selected_object = None
            self.redraw_objects()
            self.update_properties_panel()

    # -------------- File Operations -------------- #
    def new_project(self):
        """Create new project"""
        if messagebox.askyesno("Nuovo Progetto", "Creare un nuovo progetto? Le modifiche non salvate verranno perse."):
            self.objects.clear()
            self.selected_object = None
            self.undo_stack.clear()
            self.redo_stack.clear()
            self.label_settings = LabelSettings()
            self.update_canvas_size()
            self.update_properties_panel()
            self.save_state()

    def save_project(self):
        """Save project to JSON file"""
        try:
            filename = filedialog.asksaveasfilename(
                title="Salva Progetto",
                defaultextension=".json",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
            )
            
            if filename:
                project_data = {
                    "label_settings": asdict(self.label_settings),
                    "objects": [asdict(obj) for obj in self.objects]
                }
                
                with open(filename, 'w', encoding='utf-8') as f:
                    json.dump(project_data, f, indent=2, ensure_ascii=False)
                
                messagebox.showinfo("Successo", "Progetto salvato con successo!")
                
        except Exception as e:
            messagebox.showerror("Errore", f"Errore nel salvataggio: {str(e)}")

    def import_project(self):
        """Import project from JSON file"""
        try:
            filename = filedialog.askopenfilename(
                title="Apri Progetto",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
            )
            
            if filename:
                with open(filename, 'r', encoding='utf-8') as f:
                    project_data = json.load(f)
                
                # Load label settings
                if "label_settings" in project_data:
                    settings_dict = project_data["label_settings"]
                    self.label_settings = LabelSettings(**settings_dict)
                
                # Load objects
                self.objects.clear()
                if "objects" in project_data:
                    for obj_dict in project_data["objects"]:
                        obj = ZPLObject(**obj_dict)
                        self.objects.append(obj)
                
                self.selected_object = None
                self.update_canvas_size()
                self.update_properties_panel()
                self.save_state()
                
                messagebox.showinfo("Successo", "Progetto caricato con successo!")
                
        except Exception as e:
            messagebox.showerror("Errore", f"Errore nel caricamento: {str(e)}")

    def import_zpl_file(self):
        """Import ZPL file and parse objects"""
        try:
            filename = filedialog.askopenfilename(
                title="Importa File ZPL",
                filetypes=[("ZPL files", "*.zpl"), ("Text files", "*.txt"), ("All files", "*.*")]
            )
            
            if filename:
                with open(filename, 'r', encoding='utf-8') as f:
                    zpl_content = f.read()
                
                # Parse ZPL content
                parsed_objects = ZPLParser.parse_zpl_file(zpl_content)
                
                if parsed_objects:
                    # Ask user if they want to replace or append
                    if self.objects:
                        result = messagebox.askyesnocancel(
                            "Importa ZPL", 
                            "Sostituire gli oggetti esistenti?\n\nSì = Sostituisci\nNo = Aggiungi\nAnnulla = Annulla"
                        )
                        if result is None:  # Cancel
                            return
                        elif result:  # Yes - Replace
                            self.objects.clear()
                    
                    # Add parsed objects
                    self.objects.extend(parsed_objects)
                    self.selected_object = None
                    self.redraw_objects()
                    self.update_properties_panel()
                    self.save_state()
                    
                    messagebox.showinfo("Successo", f"Importati {len(parsed_objects)} oggetti dal file ZPL!")
                else:
                    messagebox.showwarning("Avviso", "Nessun oggetto riconosciuto nel file ZPL.")
                
        except Exception as e:
            messagebox.showerror("Errore", f"Errore nell'importazione ZPL: {str(e)}")

    # -------------- ZPL Generation -------------- #
    def generate_zpl(self):
        """Generate ZPL code from objects"""
        zpl = "^XA\n"  # Start format
        if self.label_settings.orientation == "Landscape":
            zpl += "^POI\n"  # Invert orientation
        skip_text_ids = set()
        for i, obj in enumerate(self.objects):
            if obj.obj_type == "barcode":
                for j, t in enumerate(self.objects):
                    if (
                        t.obj_type == "text" and
                        t.text == obj.text and
                        abs(t.x - obj.x) <= 2 and
                        abs(t.width - obj.width) <= 2 and
                        abs(t.y - (obj.y + obj.height + 5)) <= 3
                    ):
                        skip_text_ids.add(t.id)
                        break
        for obj in self.objects:
            if obj.obj_type == "text" and obj.id in skip_text_ids:
                continue
            if obj.obj_type == "barcode":
                x = int(obj.x * self.SCALE)
                y = int(obj.y * self.SCALE)
                width = int(obj.width * self.SCALE)
                height = int(obj.height * self.SCALE)
                # Esporta ^BY
                zpl += f"^FO{x},{y}\n"
                zpl += f"^BY{obj.bar_module},{obj.bar_ratio},{obj.bar_height}\n"
                hri_pos = "Y" if obj.hri_above else "N"
                # Ultimo parametro sempre Y
                if obj.barcode_type == "128":
                    zpl += f"^BCN,{height},Y,{hri_pos},Y\n"
                elif obj.barcode_type == "39":
                    zpl += f"^B3N,N,{height},Y,{hri_pos},Y\n"
                elif obj.barcode_type == "93":
                    zpl += f"^BAN,{height},Y,{hri_pos},Y\n"
                elif obj.barcode_type == "I25":
                    zpl += f"^B2N,N,{height},Y,{hri_pos},Y\n"
                elif obj.barcode_type in ["EAN13", "EAN8"]:
                    zpl += f"^BEN,{height},Y,{hri_pos},Y\n"
                elif obj.barcode_type in ["UPCA", "UPCE"]:
                    zpl += f"^BUN,{height},Y,{hri_pos},Y\n"
                zpl += f"^FD{obj.text}^FS\n"
                continue
            x = int(obj.x * self.SCALE)
            y = int(obj.y * self.SCALE)
            width = int(obj.width * self.SCALE)
            height = int(obj.height * self.SCALE)
            zpl += f"^FO{x},{y}\n"
            if obj.obj_type == "text":
                zpl += f"^A{obj.font_type},N,{obj.font_size},{obj.font_size}\n"
                if obj.rotation != 0:
                    zpl += f"^FWR\n"
                zpl += f"^FD{obj.text}^FS\n"
            elif obj.obj_type == "rectangle":
                zpl += f"^GB{width},{height},{obj.thickness}^FS\n"
            elif obj.obj_type == "line":
                if obj.width > obj.height:
                    zpl += f"^GB{width},{max(1, obj.line_thickness)},B^FS\n"
                else:
                    zpl += f"^GB{max(1, obj.line_thickness)},{height},B^FS\n"
            elif obj.obj_type == "circle":
                diameter = min(width, height)
                zpl += f"^GC{diameter},{obj.thickness}^FS\n"
            elif obj.obj_type == "image":
                if obj.text:
                    image_name = obj.text.replace('.bmp', '').replace('.BMP', '')[:8].upper()
                    zpl += f"^XG{image_name},1,1^FS\n"
        zpl += "^XZ\n"  # End format
        return zpl

    def export_to_file(self):
        """Export ZPL to file"""
        try:
            filename = filedialog.asksaveasfilename(
                title="Salva ZPL",
                defaultextension=".zpl",
                filetypes=[("ZPL files", "*.zpl"), ("Text files", "*.txt"), ("All files", "*.*")]
            )
            
            if filename:
                zpl_code = self.generate_zpl()
                with open(filename, 'w', encoding='utf-8') as f:
                    f.write(zpl_code)
                
                messagebox.showinfo("Successo", "File ZPL salvato con successo!")
                
        except Exception as e:
            messagebox.showerror("Errore", f"Errore nel salvataggio ZPL: {str(e)}")

    def copy_to_clipboard(self):
        """Copy ZPL to clipboard"""
        try:
            zpl_code = self.generate_zpl()
            self.root.clipboard_clear()
            self.root.clipboard_append(zpl_code)
            messagebox.showinfo("Successo", "ZPL copiato negli appunti!")
            
        except Exception as e:
            messagebox.showerror("Errore", f"Errore nella copia: {str(e)}")

    def preview_zpl(self):
        """Show ZPL preview in dialog"""
        try:
            zpl_code = self.generate_zpl()
            
            win = tk.Toplevel(self.root)
            win.title("Anteprima ZPL")
            win.geometry("600x500")
            win.transient(self.root)
            
            # Text widget with scrollbar
            frame = ttk.Frame(win)
            frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            
            text_widget = tk.Text(frame, wrap=tk.WORD, font=("Courier", 10))
            scrollbar = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=text_widget.yview)
            text_widget.configure(yscrollcommand=scrollbar.set)
            
            text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            
            text_widget.insert("1.0", zpl_code)
            text_widget.config(state=tk.DISABLED)
            
            # Buttons
            btn_frame = ttk.Frame(win)
            btn_frame.pack(pady=10)
            
            ttk.Button(btn_frame, text="Copia", 
                      command=lambda: self.root.clipboard_append(zpl_code)).pack(side=tk.LEFT, padx=5)
            ttk.Button(btn_frame, text="Chiudi", command=win.destroy).pack(side=tk.LEFT, padx=5)
            
        except Exception as e:
            messagebox.showerror("Errore", f"Errore nell'anteprima: {str(e)}")

    def validate_zpl(self):
        """Basic ZPL validation"""
        try:
            zpl_code = self.generate_zpl()
            
            # Basic validation checks
            errors = []
            warnings = []
            
            if not zpl_code.startswith("^XA"):
                errors.append("Il codice ZPL deve iniziare con ^XA")
            
            if not zpl_code.endswith("^XZ\n"):
                errors.append("Il codice ZPL deve terminare con ^XZ")
            
            # Check for unmatched field origins
            fo_count = zpl_code.count("^FO")
            fs_count = zpl_code.count("^FS")
            
            if fo_count != fs_count:
                warnings.append(f"Possibile squilibrio tra ^FO ({fo_count}) e ^FS ({fs_count})")
            
            # Check for empty text fields
            empty_fields = re.findall(r'\^FD\^FS', zpl_code)
            if empty_fields:
                warnings.append(f"Trovati {len(empty_fields)} campi di testo vuoti")
            
            # Show results
            message = "Validazione ZPL:\n\n"
            
            if not errors and not warnings:
                message += "✅ Il codice ZPL sembra valido!"
            else:
                if errors:
                    message += "❌ Errori trovati:\n"
                    for error in errors:
                        message += f"  • {error}\n"
                    message += "\n"
                
                if warnings:
                    message += "⚠️ Avvisi:\n"
                    for warning in warnings:
                        message += f"  • {warning}\n"
            
            if errors:
                messagebox.showerror("Validazione ZPL", message)
            elif warnings:
                messagebox.showwarning("Validazione ZPL", message)
            else:
                messagebox.showinfo("Validazione ZPL", message)
                
        except Exception as e:
            messagebox.showerror("Errore", f"Errore nella validazione: {str(e)}")

    def set_zoom(self, value):
        self.zoom = max(0.2, min(5.0, value))  # Limita tra 20% e 500%
        self._zoom_var.set(f"{int(self.zoom*100)}%")
        self.update_canvas_size()

# -------------- Main Application -------------- #
def main():
    root = tk.Tk()
    app = ZPLEditor(root)
    root.mainloop()

if __name__ == "__main__":
    main()