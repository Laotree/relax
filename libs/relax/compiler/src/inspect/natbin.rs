//! A native (rustc-built) binary read from its file: function symbols with their code bytes, and
//! its DWARF line table and inline tree when it has debug info (makepad inspect `asm ... vs=rustc`
//! and the native-baseline diff). The comparison build is made with line tables only, which
//! leaves the machine code as the plain release build makes it.
//!
//! macOS: the DWARF of a cargo build lives in `<bin>.dSYM/Contents/Resources/DWARF/<name>` (packed
//! split debug info), or -- unpacked -- in the object files the binary's debug map (N_OSO stabs)
//! names. Linux: in the ELF's own .debug_* sections.

/// One function of the binary's symbol table.
#[derive(Clone, Debug)]
pub struct NativeFn {
    /// virtual address (unslid, as in the file)
    pub addr: u64,
    pub size: u64,
    /// demangled, without the legacy `::h<hash>` suffix
    pub name: String,
}

/// One row of the line table: from `addr` until the next row's address the code is `file:line`.
#[derive(Clone, Debug)]
pub struct LineRow {
    pub addr: u64,
    /// index into `NativeBin::files`
    pub file: u32,
    pub line: u32,
    pub col: u32,
}

/// One inlined call in the inline tree: code in `ranges` is fn `name`, inlined at
/// `call_file:call_line` into its parent (the enclosing InlinedCall, else the symbol's fn).
#[derive(Clone, Debug)]
pub struct InlinedCall {
    pub ranges: Vec<(u64, u64)>,
    pub name: String,
    pub call_file: u32,
    pub call_line: u32,
    /// nesting depth below the concrete fn (1 = inlined directly into it)
    pub depth: u32,
}

pub struct NativeBin {
    pub path: String,
    pub arch: relax_backend::asm::Arch,
    /// sorted by address
    pub fns: Vec<NativeFn>,
    /// source file paths of the line table (absolute where the DWARF has a comp dir)
    pub files: Vec<String>,
    /// where the debug info came from ("dSYM", "object files", "ELF sections", "none")
    pub debug_from: String,
    data: Vec<u8>,
}

impl NativeBin {
    /// Reads the binary at `path` (thin or universal Mach-O: the host slice; ELF) and finds its debug
    /// info. Line tables and inline trees are read lazily per function (`lines`, `inlined`).
    pub fn open(path: &str) -> Result<NativeBin, String> {
        let data = std::fs::read(path).map_err(|e| format!("cannot read {}: {}", path, e))?;
        Err(format!("{}: native binary reader not implemented yet ({} bytes)", path, data.len()))
    }

    /// The functions whose demangled name is `query` or ends with `::query` (generic arguments
    /// ignored when the query has none).
    pub fn find(&self, query: &str) -> Vec<&NativeFn> {
        let _ = query;
        Vec::new()
    }

    /// The code bytes of `f`.
    pub fn code(&self, f: &NativeFn) -> &[u8] {
        let _ = f;
        &self.data[..0]
    }

    /// Line rows covering [lo, hi), sorted by address (empty without debug info).
    pub fn lines(&self, lo: u64, hi: u64) -> Vec<LineRow> {
        let _ = (lo, hi);
        Vec::new()
    }

    /// The inlined calls inside [lo, hi) (the concrete fn's inline tree), outermost first.
    pub fn inlined(&self, lo: u64, hi: u64) -> Vec<InlinedCall> {
        let _ = (lo, hi);
        Vec::new()
    }
}
