use std::alloc::{GlobalAlloc, System};
use std::sync::atomic::AtomicUsize;

#[global_allocator]
static GLOBAL: LoggingAllocator = LoggingAllocator { current: AtomicUsize::new(0) };

struct LoggingAllocator {
    current: AtomicUsize
}

unsafe impl GlobalAlloc for LoggingAllocator {

    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        if layout.size() > 100000 {
            print!("alloc {} B, current total {} B, at ", layout.size(), self.current.fetch_add(layout.size(), std::sync::atomic::Ordering::Relaxed));
            let backtrace = backtrace::Backtrace::new();
            let mut to_print = None;
            for frame in backtrace.frames() {
                for symbol in frame.symbols() {
                    let demangled_name = format!("{}", symbol.name().unwrap());
                    let mut opened_angle_brackets = 0;
                    let mut lib_name_end = demangled_name.len();
                    let mut fn_name_start = 0;
                    let mut fn_name_end = demangled_name.len();
                    for (i, c) in demangled_name.chars().enumerate() {
                        if c == '<' {
                            if opened_angle_brackets == 0 {
                                fn_name_end = i;
                            }
                            if lib_name_end == demangled_name.len() {
                                lib_name_end = i;
                            }
                            opened_angle_brackets += 1;
                        } else if c == '>' {
                            opened_angle_brackets -= 1;
                        } else if c == ':' {
                            if lib_name_end == demangled_name.len() {
                                lib_name_end = i;
                            }
                            if opened_angle_brackets == 0 {
                                fn_name_start = i;
                                fn_name_end = demangled_name.len();
                            }
                        }
                    }
                    if &demangled_name[..lib_name_end] == "fheanor" || &demangled_name[..lib_name_end] == "feanor_math" {
                        if let Some(to_print) = to_print {
                            print!("{}", to_print);
                        }
                        to_print = None;
                        if let Some((filename, lineno)) = symbol.filename().and_then(|filename| symbol.lineno().map(|lineno| (filename, lineno))) {
                            print!("{}::...::{} ({:?}:{}), ", &demangled_name[..lib_name_end], &demangled_name[fn_name_start..fn_name_end], filename.file_name().unwrap(), lineno);
                        } else {
                            print!("{}::...::{}, ", &demangled_name[..lib_name_end], &demangled_name[fn_name_start..fn_name_end]);
                        }
                    } else {
                        to_print = Some(format!("{}::...::{}, ", &demangled_name[..lib_name_end], &demangled_name[fn_name_start..fn_name_end]));
                    }
                }
            }
            println!();
        }
        return System.alloc(layout);
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        if layout.size() > 100000 {
            println!("dealloc {} B, current total {} B", layout.size(), self.current.fetch_sub(layout.size(), std::sync::atomic::Ordering::Relaxed));
        }
        return System.dealloc(ptr, layout);
    }
}
