from pathlib import Path

root = Path(__file__).resolve().parents[2]
fields = [f'a{i:02}' for i in range(25)]
rho = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
lines = ['import Spec.Keccak.Basic', '', 'namespace LeanVmXmss.Model.Keccak', '', 'structure State25 where']
lines += [f'  {f} : UInt64' for f in fields]
lines += ['  deriving Repr, BEq, DecidableEq', '', 'def State25.toSpec (s : State25) : Spec.Keccak.State :=', '  #[' + ',\n    '.join(', '.join('s.' + f for f in fields[i:i+5]) for i in range(0, 25, 5)) + ']', '', 'def State25.fromSpec (s : Spec.Keccak.State) : State25 :=', '  ⟨' + ',\n    '.join(', '.join(f's[{j}]!' for j in range(i, i+5)) for i in range(0, 25, 5)) + '⟩', '', 'def round25 (s : State25) (rc : UInt64) : State25 :=']
for x in range(5):
    lines += [f'  let c{x} := ' + ' ^^^ '.join(f's.a{i:02}' for i in range(x, 25, 5))]
for i in range(25):
    dest = i // 5 + 5 * ((2 * (i % 5) + 3 * (i // 5)) % 5)
    lines += [f'  let b{dest:02} := Spec.Keccak.rotl (s.a{i:02} ^^^ c{(i%5+4)%5} ^^^ Spec.Keccak.rotl c{(i%5+1)%5} 1) {rho[i]}']
values = []
for i in range(25):
    j = 5*(i//5)+(i%5+1)%5
    k = 5*(i//5)+(i%5+2)%5
    values += [f'(b{i:02} ^^^ ((~~~b{j:02}) &&& b{k:02}))' + (' ^^^ rc' if i == 0 else '')]
body = lines[lines.index('def round25 (s : State25) (rc : UInt64) : State25 :=') + 1:]
lines += ['  ⟨' + ',\n    '.join(values) + '⟩', '']
for lane, value in enumerate(values):
    lines += [f'@[export shard_b_keccak_lane_{lane:02}]', f'def lane{lane:02} (' + ' '.join(fields) + (' rc' if lane == 0 else ' _rc') + ' : UInt64) : UInt64 :=']
    needed = {f'b{lane:02}', f'b{5*(lane//5)+(lane%5+1)%5:02}', f'b{5*(lane//5)+(lane%5+2)%5:02}'}
    selected = [line for line in body if line.split()[1].startswith('c') or line.split()[1] in needed]
    import re
    def unroll_rot(line):
        line = line.replace('s.', '')
        line = re.sub(r'Spec.Keccak.rotl (c\d) 1', r'((\1 <<< 1) ||| (\1 >>> 63))', line)
        match = re.match(r'(  let b\d+ := )Spec.Keccak.rotl (.*) (\d+)$', line)
        if match:
            lead, arg, amount = match.groups()
            n = int(amount)
            return lead + (arg if n == 0 else f'(({arg} <<< {n}) ||| ({arg} >>> {64-n}))')
        return line
    lines += [unroll_rot(line) for line in selected]
    lines += ['  ' + value, '']
lines += ['def roundConstant : Nat → UInt64']
constants = [1,0x8082,0x800000000000808a,0x8000000080008000,0x808b,0x80000001,0x8000000080008081,0x8000000000008009,0x8a,0x88,0x80008009,0x8000000a,0x8000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,0x8000000000008002,0x8000000000000080,0x800a,0x800000008000000a,0x8000000000008081,0x8000000000008080,0x80000001,0x8000000080008008]
constants[20] = 0x8000000080008081
lines += [f'  | {i} => {hex(c)}' for i, c in enumerate(constants)]
lines += ['  | _ => 0', '', 'def rounds25 : Nat → Nat → State25 → State25', '  | 0, _, s => s', '  | n + 1, i, s => rounds25 n (i + 1) (round25 s (roundConstant i))', '', 'def keccakF1600 (s : State25) : State25 := rounds25 24 0 s', '', 'end LeanVmXmss.Model.Keccak', '']
(root / 'Model/Keccak/Registers.lean').write_text('\n'.join(lines))
