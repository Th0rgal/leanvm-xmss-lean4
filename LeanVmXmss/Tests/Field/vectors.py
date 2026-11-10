from pathlib import Path


def generate():
    mask = (1 << 64) - 1
    corners = [0, 1, 2, 1 << 63, mask, 0xF000000000000000, 0x1B, 0xAAAAAAAAAAAAAAAA, 0x5555555555555555]
    vectors = [[a, b, a ^ b, b, a, b ^ 1, a] for a in corners for b in corners]
    vectors.extend([[0, 0, 1, 0, 1, 0, 1], [0, 1, 0, 0, 0, 1, 1], [1 << 63, 0, 0, 2, 0, 0, 2], [1, 2, 3, 4, 5, 6, 7]])
    state = 0x6C65616E564D584D
    vectors.extend([[a, 0, 0, b, 0, 0, a] for a in corners for b in corners])
    for _ in range(240):
        row = []
        for _ in range(7):
            state ^= state << 13 & mask
            state ^= state >> 7
            state ^= state << 17 & mask
            state &= mask
            row.append(state)
        vectors.append(row)
    return vectors


if __name__ == '__main__':
    target = Path(__file__).resolve().parent / 'artifacts' / 'field-vectors.txt'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(''.join(' '.join(map(str, row)) + '\n' for row in generate()))
