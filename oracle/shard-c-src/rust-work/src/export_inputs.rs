
use signatures::lean_xmss::{mock, LeafIndex, PUB_KEY_SIZE, SIG_SIZE};
use std::sync::atomic::{AtomicUsize, Ordering};

const KEY_START: LeafIndex = 3_000_000_000;
const KEY_END: LeafIndex = 3_000_000_015;
const RECORD_LEN: usize = PUB_KEY_SIZE + 32 + SIG_SIZE;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let count: usize = args[1].parse().unwrap();
    let out_path = &args[2];
    let msg: [u8; 32] = std::array::from_fn(|i| (i * 5 + 1) as u8);
    let mut raw = vec![0u8; count * RECORD_LEN];
    let n_threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8);
    let next = AtomicUsize::new(0);
    let slots: Vec<&mut [u8]> = raw.chunks_exact_mut(RECORD_LEN).collect();
    let slots_ptr = slots.into_iter().map(|s| s.as_mut_ptr() as usize).collect::<Vec<usize>>();

    std::thread::scope(|s| {
        for _ in 0..n_threads {
            let next_ref = &next;
            let ptrs = &slots_ptr;
            s.spawn(move || {
                loop {
                    let idx = next_ref.fetch_add(1, Ordering::Relaxed);
                    if idx >= count {
                        break;
                    }
                    let mut seed = [10u8; 32];
                    seed[..8].copy_from_slice(&(idx as u64).to_le_bytes());
                    let span = (KEY_END - KEY_START + 1) as usize;
                    let leaf = KEY_START + (idx % span) as LeafIndex;
                    let (sk, pk) = mock::key_gen_from_seed(seed, KEY_START, KEY_END);
                    let sig = mock::sign(&sk, &msg, leaf).expect("sign");
                    unsafe {
                        let dst = std::slice::from_raw_parts_mut(ptrs[idx] as *mut u8, RECORD_LEN);
                        dst[..PUB_KEY_SIZE].copy_from_slice(&pk.to_bytes());
                        dst[PUB_KEY_SIZE..PUB_KEY_SIZE + 32].copy_from_slice(&msg);
                        dst[PUB_KEY_SIZE + 32..].copy_from_slice(&sig.to_bytes());
                    }
                }
            });
        }
    });
    std::fs::write(out_path, &raw).unwrap();
    println!("wrote {} bytes ({} records) using {} threads", raw.len(), count, n_threads);
}
