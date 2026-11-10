from pathlib import Path
import re

root = Path(__file__).resolve().parent
source = root.parents[3] / 'references/leanVM/crates/lean_compiler/src'
destination = root / 'generated'
for path in source.rglob('*.rs'):
    relative = path.relative_to(source)
    text = path.read_text()
    text = re.sub(r'("(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\')|//[^\n]*|/\*.*?\*/',
                  lambda match: match.group(1) or '', text, flags=re.S)
    if relative.as_posix() == 'lib.rs':
        text = text.replace('Program::assemble(prog, hints, frame_size["main"])',
                            '{ export_schedule(&hints, frame_size["main"]); Program::assemble(prog, hints, frame_size["main"]) }')
        text += '\n' + (root / 'src/schedule_export.rs').read_text()
    output = destination / relative
    output.parent.mkdir(exist_ok=True, parents=True)
    output.write_text(text)
