

use super::*;

pub(crate) type Off = u32;



#[derive(Clone, Debug)]
pub(crate) enum KVal {
    
    FrameSize,
    
    
    Const(F192),
    Entry(String),
    
    
    
    
    EndSentinel,
    
    
    
    
    Local(u32),
    
    
    At(String, u32),
}

#[derive(Clone, Debug)]
pub(crate) struct LInstr {
    pub(crate) op: LOp,
    
    
    pub(crate) line: u32,
    
    
    pub(crate) hints: Vec<Hint>,
}

#[derive(Clone, Debug)]
pub(crate) enum LOp {
    
    MulNextFrame {
        a: Off,
        b: Off,
        c: Off,
    },
    Set {
        o: Off,
        k: KVal,
    },
    Xor {
        a: Off,
        b: Off,
        c: Off,
    },
    Mul {
        a: Off,
        b: Off,
        c: Off,
    },
    Deref {
        o1: Off,
        o2: Off,
        o3: Off,
        mode: DerefMode,
    },
    Jump {
        oc: Off,
        od: Off,
        of: Off,
    },
    
    
    Slot {
        x: Off,
        first: u32,
        dst: Off,
    },
    
    
    
    Keccak {
        m: [Off; 4],
        tail: Off,
        b8: Off,
        cap: Off,
        c: Off,
        in_odd: bool,
        out_odd: bool,
    },
}




#[derive(Clone, Debug)]
pub(crate) enum Hint {
    
    NextFrameAddress,
    
    
    
    AllocLoopFrames {
        ptr: Off,
        callee: String,
        count: LoopCount,
        tail: u32,
    },
    
    AllocFrame { ptr: Off, callee: String },
    
    
    
    AllocFrameMax { ptr: Off, callees: Vec<String> },
    
    
    AllocBuffer { ptr: Off, size: u32 },
    
    
    AllocBufferDyn { ptr: Off, size: Off },
    
    
    Resolved(RHint),
}

pub(crate) struct Lowered {
    pub(crate) name: String,
    pub(crate) code: Vec<LInstr>,
    pub(crate) frame_size: u32,
}






#[derive(Default)]
pub(crate) struct JumpTables {
    
    
    pub(crate) slots: Vec<KVal>,
    
    pub(crate) shared: HashMap<Vec<String>, usize>,
}





pub(crate) enum CellRun {
    Stack { base: Off, len: u32 },
    Heap { ptr: Off, lo: u32, len: u32 },
}

#[derive(Clone, Debug)]
pub(crate) enum LoopCount {
    Constant(u64),
    Bound { cell: Off, start: u64 },
}
