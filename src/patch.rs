// muguet - patch.rs
// Constantin Clerc (c22dev) - 0.1

use anyhow::{bail, Context, Result};
use std::collections::HashMap;
use wasm_encoder::reencode::{utils, Error, Reencode};
use wasm_encoder::ValType::I64;
use wasmparser::{KnownCustom, Name, Parser, Payload, TypeRef};

#[derive(Clone, Copy, PartialEq)]
enum Arg {
    Local0,
    TlsBase,

    Local1Replaced,

    MissingText,
    PageMap,
    FreePageMap,
}

const HOOKS: &[(&str, &str, &[Arg])] = &[
    ("muguet_script", "GtaThread::Update(int)", &[Arg::Local0, Arg::TlsBase]),
    ("muguet_explosion", "CExplosionManager::AddExplosion(CExplosionManager::CExplosionArgs&, CProjectile*, bool)", &[Arg::Local0]),
    ("muguet_timewarp", "CTimeWarper::SetTargetTimeWarp(TW_Dir)", &[Arg::Local1Replaced]),
    ("muguet_text", "CTextFile::GetInternal(unsigned int)", &[Arg::MissingText]),
    ("muguet_pagemap", "rage::pgBase::pgBase()", &[Arg::Local0, Arg::PageMap]),
    ("muguet_free_pagemap", "rage::pgBase::Destroy()", &[Arg::FreePageMap]),
];

pub const VERSION: u32 = 14;

fn returns(args: &[Arg]) -> bool {
    args.contains(&Arg::Local1Replaced) || args.contains(&Arg::MissingText) || args.contains(&Arg::PageMap)
}

struct Patcher {
    imported_funcs: u32,
    types: u32,
    tls_global: u32,

    targets: HashMap<u32, usize>,
    exports: Vec<(String, u32)>,
    next_func: u32,
    regenerate_map: u32,
}

impl Patcher {
    fn shift(&self) -> u32 {
        HOOKS.len() as u32
    }
}

impl Reencode for Patcher {
    type Error = anyhow::Error;

    fn function_index(&mut self, f: u32) -> Result<u32, Error<Self::Error>> {
        Ok(if f >= self.imported_funcs { f + self.shift() } else { f })
    }

    fn parse_type_section(&mut self, types: &mut wasm_encoder::TypeSection, section: wasmparser::TypeSectionReader<'_>) -> Result<(), Error<Self::Error>> {
        utils::parse_type_section(self, types, section)?;

        for (_, _, args) in HOOKS {
            types.ty().function(vec![I64; args.len()], if returns(args) { vec![I64] } else { vec![] });
        }
        Ok(())
    }

    fn parse_import_section(&mut self, imports: &mut wasm_encoder::ImportSection, section: wasmparser::ImportSectionReader<'_>) -> Result<(), Error<Self::Error>> {
        utils::parse_import_section(self, imports, section)?;
        for (k, (name, _, _)) in HOOKS.iter().enumerate() {
            imports.import("env", name, wasm_encoder::EntityType::Function(self.types + k as u32));
        }
        Ok(())
    }

    fn parse_export_section(&mut self, exports: &mut wasm_encoder::ExportSection, section: wasmparser::ExportSectionReader<'_>) -> Result<(), Error<Self::Error>> {
        utils::parse_export_section(self, exports, section)?;
        for (name, f) in std::mem::take(&mut self.exports) {
            exports.export(&name, wasm_encoder::ExportKind::Func, f + self.shift());
        }
        Ok(())
    }

    fn parse_function_body(&mut self, code: &mut wasm_encoder::CodeSection, func: wasmparser::FunctionBody<'_>) -> Result<(), Error<Self::Error>> {
        let index = self.next_func;
        self.next_func += 1;
        let Some(&hook) = self.targets.get(&index) else {
            return utils::parse_function_body(self, code, func);
        };
        let mut f = self.new_function_with_parsed_locals(&func)?;
        use wasm_encoder::Instruction as I;
        let call = I::Call(self.imported_funcs + hook as u32);
        if HOOKS[hook].2 == [Arg::MissingText] {
            // only call out for the listed hashes: text lookups are hot
            for (label, _) in crate::host::MISSING_TEXT {
                f.instruction(&I::LocalGet(0)).instruction(&I::I32Const(crate::proto::joaat(label) as i32)).instruction(&I::I32Eq);
                f.instruction(&I::If(wasm_encoder::BlockType::Empty));
                f.instruction(&I::LocalGet(0)).instruction(&I::I64ExtendI32U).instruction(&call).instruction(&I::Return);
                f.instruction(&I::End);
            }
        } else if HOOKS[hook].2.contains(&Arg::PageMap) || HOOKS[hook].2.contains(&Arg::FreePageMap) {
            // These hooks run after the map is relocated or copied, respectively.
        } else {
            for arg in HOOKS[hook].2 {
                match arg {
                    Arg::Local0 => f.instruction(&I::LocalGet(0)),
                    Arg::TlsBase => f.instruction(&I::GlobalGet(self.tls_global)),
                    Arg::Local1Replaced => f.instruction(&I::LocalGet(1)).instruction(&I::I64ExtendI32U),
                    Arg::MissingText | Arg::PageMap | Arg::FreePageMap => unreachable!(),
                };
            }
            f.instruction(&call);
            if returns(HOOKS[hook].2) {
                f.instruction(&I::I32WrapI64);
                f.instruction(&I::LocalSet(1));
            }
        }
        let mut reader = func.get_operators_reader()?;
        let mut map_hooked = false;
        let mut previous = None;
        let mut relocation_guarded = false;
        let mut relocation_depth = None;
        while !reader.eof() {
            let op = reader.read()?;
            if HOOKS[hook].2.contains(&Arg::PageMap) && !relocation_guarded && matches!(op, wasmparser::Operator::Block { blockty: wasmparser::BlockType::Type(wasmparser::ValType::I64) }) {
                // Expanded maps live outside resource chunks and stay valid during defragmentation.
                f.instruction(&I::LocalGet(0)).instruction(&I::I64Const(0)).instruction(&call).instruction(&I::I32WrapI64);
                f.instruction(&I::If(wasm_encoder::BlockType::Result(I64))).instruction(&I::I64Const(0)).instruction(&I::Else);
                relocation_guarded = true;
                relocation_depth = Some(0u32);
            }
            f.instruction(&self.instruction(op.clone())?);
            if let Some(depth) = &mut relocation_depth {
                match op {
                    wasmparser::Operator::Block { .. } | wasmparser::Operator::Loop { .. } | wasmparser::Operator::If { .. } => *depth += 1,
                    wasmparser::Operator::End => *depth -= 1,
                    _ => {}
                }
                if *depth == 0 {
                    f.instruction(&I::End);
                    relocation_depth = None;
                }
            }
            if HOOKS[hook].2.contains(&Arg::PageMap) && !map_hooked && matches!(previous, Some(wasmparser::Operator::LocalTee { local_index: 1 })) && matches!(op, wasmparser::Operator::I64Store { memarg } if memarg.offset == 8) {
                f.instruction(&I::LocalGet(0)).instruction(&I::LocalGet(3)).instruction(&call).instruction(&I::LocalSet(1));
                f.instruction(&I::LocalGet(0)).instruction(&I::LocalGet(1)).instruction(&I::I64Store(wasm_encoder::MemArg { offset: 8, align: 3, memory_index: 0 }));
                map_hooked = true;
            } else if HOOKS[hook].2.contains(&Arg::FreePageMap) && matches!(op, wasmparser::Operator::Call { function_index } if function_index == self.regenerate_map) {
                f.instruction(&I::LocalGet(0)).instruction(&call);
                map_hooked = true;
            }
            previous = Some(op);
        }
        if (HOOKS[hook].2.contains(&Arg::PageMap) || HOOKS[hook].2.contains(&Arg::FreePageMap)) && (!map_hooked || HOOKS[hook].2.contains(&Arg::PageMap) && !relocation_guarded) {
            return Err(Error::UserError(anyhow::anyhow!("page map hook site not found in {}", HOOKS[hook].1)));
        }
        code.function(&f);
        Ok(())
    }
}

pub fn is_patched(wasm: &[u8]) -> bool {
    Parser::new(0).parse_all(wasm).any(|p| match p {
        Ok(Payload::ImportSection(s)) => s.into_imports().any(|i| i.is_ok_and(|i| i.name == HOOKS[0].0)),
        _ => false,
    })
}

pub fn patch(wasm: &[u8], wanted: &[(&str, &str)]) -> Result<Vec<u8>> {
    let (mut imported_funcs, mut types, mut tls_global) = (0u32, 0u32, None);
    let mut by_name: HashMap<String, u32> = HashMap::new();
    for payload in Parser::new(0).parse_all(wasm) {
        match payload? {
            Payload::TypeSection(s) => types = s.count(),
            Payload::ImportSection(s) => {
                for imp in s.into_imports() {
                    if matches!(imp?.ty, TypeRef::Func(_)) {
                        imported_funcs += 1;
                    }
                }
            }
            Payload::CustomSection(c) => {
                if let KnownCustom::Name(names) = c.as_known() {
                    for sub in names {
                        match sub? {
                            Name::Function(map) => {
                                for n in map {
                                    let n = n?;
                                    by_name.entry(n.name.to_string()).or_insert(n.index);
                                }
                            }
                            Name::Global(map) => {
                                for n in map {
                                    let n = n?;
                                    if n.name == "__tls_base" { tls_global = Some(n.index); }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        }
    }
    if by_name.contains_key(HOOKS[0].0) {
        bail!("game.wasm is already patched");
    }
    let mut targets = HashMap::new();
    for (k, (_, func, _)) in HOOKS.iter().enumerate() {
        let f = *by_name.get(*func).with_context(|| format!("{func} not found (no name section?)"))?;
        targets.insert(f, k);
    }
    let mut exports = Vec::new();
    for (export, function) in [("muguet:malloc", "emscripten_builtin_malloc"), ("muguet:free", "emscripten_builtin_free")] {
        let &index = by_name.get(function).with_context(|| format!("{function} not found (no name section?)"))?;
        exports.push((export.to_string(), index));
    }
    for (export, func) in wanted {
        match by_name.get(*func) {
            Some(&i) => exports.push((format!("mp:{export}"), i)),
            None => eprintln!("[patch] {func} not found; multiplayer will skip it"),
        }
    }
    let mut p = Patcher {
        imported_funcs,
        types,
        tls_global: tls_global.unwrap_or(1),
        targets,
        exports,
        next_func: imported_funcs,
        regenerate_map: *by_name.get("rage::pgBase::RegenerateMap(rage::datResourceMap&) const").context("resource map regeneration function not found")?,
    };
    let mut module = wasm_encoder::Module::new();
    p.parse_core_module(&mut module, Parser::new(0), wasm).map_err(|e| anyhow::anyhow!("patch game.wasm: {e:?}"))?;
    Ok(module.finish())
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasm_encoder::{ConstExpr, ExportKind, Function, Instruction as I, MemArg};

    #[test]
    fn page_map_hooks_preserve_relocation_reuse_and_cleanup_order() -> Result<()> {
        let mut module = wasm_encoder::Module::new();
        let mut types = wasm_encoder::TypeSection::new();
        types.ty().function([I64], [I64]);
        types.ty().function([I64], []);
        types.ty().function([I64, I64], []);
        types.ty().function([I64, wasm_encoder::ValType::I32], []);
        types.ty().function([wasm_encoder::ValType::I32], [I64]);
        module.section(&types).section(&wasm_encoder::ImportSection::new());
        let mut funcs = wasm_encoder::FunctionSection::new();
        for ty in [2, 1, 3, 4, 0, 1, 2, 0, 1] { funcs.function(ty); }
        module.section(&funcs);
        let mut memories = wasm_encoder::MemorySection::new();
        memories.memory(wasm_encoder::MemoryType { minimum: 1, maximum: None, memory64: true, shared: false, page_size_log2: None });
        module.section(&memories);
        let mut globals = wasm_encoder::GlobalSection::new();
        globals.global(wasm_encoder::GlobalType { val_type: I64, mutable: false, shared: false }, &ConstExpr::i64_const(0));
        module.section(&globals);
        let mut exports = wasm_encoder::ExportSection::new();
        exports.export("ctor", ExportKind::Func, 4).export("destroy", ExportKind::Func, 5).export("memory", ExportKind::Memory, 0);
        module.section(&exports);
        let mem = |offset| MemArg { offset, align: 3, memory_index: 0 };
        let mut code = wasm_encoder::CodeSection::new();
        for index in 0..9 {
            let mut f = Function::new(if index == 4 { vec![(4, I64)] } else { vec![] });
            match index {
                3 => { f.instruction(&I::I64Const(0)); }
                4 => {
                    // A stack argument store must not be mistaken for the relocated map.
                    f.instruction(&I::I64Const(400)).instruction(&I::I64Const(999)).instruction(&I::I64Store(mem(8)));
                    f.instruction(&I::I64Const(64)).instruction(&I::LocalSet(3));
                    f.instruction(&I::LocalGet(0)).instruction(&I::I64Load(mem(8))).instruction(&I::LocalSet(4));
                    f.instruction(&I::LocalGet(0)).instruction(&I::Block(wasm_encoder::BlockType::Result(I64))).instruction(&I::I64Const(1000)).instruction(&I::End);
                    f.instruction(&I::LocalGet(4)).instruction(&I::I64Add).instruction(&I::LocalTee(1)).instruction(&I::I64Store(mem(8)));
                    f.instruction(&I::LocalGet(1)).instruction(&I::I64Const(777)).instruction(&I::I64Store(mem(16)));
                    f.instruction(&I::LocalGet(0));
                }
                5 => {
                    f.instruction(&I::LocalGet(0)).instruction(&I::I64Const(3000)).instruction(&I::Call(6));
                    f.instruction(&I::LocalGet(0)).instruction(&I::I64Const(0)).instruction(&I::I64Store(mem(8)));
                }
                6 => {
                    f.instruction(&I::LocalGet(1)).instruction(&I::LocalGet(0)).instruction(&I::I64Load(mem(8))).instruction(&I::I64Load(mem(16))).instruction(&I::I64Store(mem(0)));
                }
                7 => { f.instruction(&I::I64Const(2000)); }
                _ => {}
            }
            f.instruction(&I::End);
            code.function(&f);
        }
        module.section(&code);
        let mut names = wasm_encoder::NameSection::new();
        let mut functions = wasm_encoder::NameMap::new();
        for (index, (_, name, _)) in HOOKS.iter().enumerate() { functions.append(index as u32, name); }
        functions.append(6, "rage::pgBase::RegenerateMap(rage::datResourceMap&) const");
        functions.append(7, "emscripten_builtin_malloc");
        functions.append(8, "emscripten_builtin_free");
        names.functions(&functions);
        let mut globals = wasm_encoder::NameMap::new();
        globals.append(0, "__tls_base");
        names.globals(&globals);
        module.section(&names);
        let wasm = patch(&module.finish(), &[])?;
        let engine = wasmtime::Engine::default();
        let module = wasmtime::Module::new(&engine, wasm)?;
        let mut linker = wasmtime::Linker::new(&engine);
        for import in module.imports() {
            let name = import.name().to_string();
            let wasmtime::ExternType::Func(ty) = import.ty() else { continue };
            linker.func_new("env", import.name(), ty, move |mut caller: wasmtime::Caller<'_, Vec<String>>, params, results| {
                let memory = caller.get_export("memory").unwrap().into_memory().unwrap();
                let data = memory.data(&caller);
                let value = |at| u64::from_le_bytes(data[at..at+8].try_into().unwrap());
                if name == "muguet_pagemap" {
                    assert_eq!(params[0].i64(), Some(32));
                    if params[1].i64() == Some(0) {
                        results[0] = wasmtime::Val::I64((value(40) == 4000) as i64);
                    } else {
                        assert_eq!(params[1].i64(), Some(64));
                        assert!([2000, 4000].contains(&value(40)));
                        results[0] = wasmtime::Val::I64(4000);
                    }
                } else if name == "muguet_free_pagemap" {
                    assert_eq!(params[0].i64(), Some(32));
                    assert_eq!(value(40), 4000);
                    assert_eq!(value(3000), 777);
                } else { panic!("unexpected hook {name}"); }
                caller.data_mut().push(name.clone());
                Ok(())
            })?;
        }
        let mut store = wasmtime::Store::new(&engine, Vec::new());
        let instance = linker.instantiate(&mut store, &module)?;
        let memory = instance.get_memory(&mut store, "memory").unwrap();
        memory.write(&mut store, 40, &1000u64.to_le_bytes())?;
        let ctor = instance.get_typed_func::<i64, i64>(&mut store, "ctor")?;
        assert_eq!(ctor.call(&mut store, 32)?, 32);
        assert_eq!(ctor.call(&mut store, 32)?, 32);
        assert_eq!(&memory.data(&store)[2016..2024], &[0; 8]);
        instance.get_typed_func::<i64, ()>(&mut store, "destroy")?.call(&mut store, 32)?;
        assert_eq!(store.data(), &["muguet_pagemap", "muguet_pagemap", "muguet_pagemap", "muguet_pagemap", "muguet_free_pagemap"]);
        Ok(())
    }
}
