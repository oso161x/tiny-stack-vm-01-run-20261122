// Tiny stack VM for make.fun's tiny stack ISA v1 (kit: ISA.md, vm.mjs).
// Runs each <id>/program.bin on <id>/input.bin under MAKEFUN_INPUT_DIR
// and writes <id>/stdout.bin + <id>/exit.txt under MAKEFUN_OUTPUT_DIR.
// Traps (exit code): 2 underflow, 3 overflow, 4 div by zero, 5 unknown
// opcode, 6 bad memory address, 7 call overflow, 8 RET on empty call
// stack, 9 pc outside program, 10 step limit, 11 output limit.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const SMAX = 256, CMAX = 64, MEM = 256, STEPS = 1_000_000, OUTMAX = 65_536;
const enc = new TextEncoder();

// [immediate bytes, values popped, values pushed] per opcode. The
// two-operand arithmetic / logic / compare opcodes all share [0, 2, 1].
const SPEC = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x17: [0, 1, 1], 0x1b: [0, 1, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};
function spec(op: number): [number, number, number] | null {
  return SPEC[op] ?? (((op >= 0x10 && op <= 0x16) || (op >= 0x18 && op <= 0x1a) ||
    (op >= 0x1c && op <= 0x1e) || (op >= 0x20 && op <= 0x22)) ? [0, 2, 1] : null);
}

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const d = new Int32Array(SMAX);
  let sp = 0;
  const c = new Int32Array(CMAX);
  let cp = 0;
  const m = new Int32Array(MEM);
  const out = new Uint8Array(OUTMAX);
  let olen = 0, ipos = 0, pc = 0, steps = 0;
  const done = (code: number) => ({ out: out.slice(0, olen), code });

  for (;;) {
    if (steps === STEPS) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    const s = spec(op);
    if (s === null) return done(5);
    const [imm, pops, pushes] = s;
    if (pc + imm >= n) return done(9);
    steps++;
    if (sp < pops) return done(2);
    if (sp - pops + pushes > SMAX) return done(3);
    const nx = pc + 1 + imm;
    pc = nx;

    switch (op) {
      case 0x00: return done(0);
      case 0x01: d[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02:
        d[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: d[sp] = d[sp - 1]; sp++; break;
      case 0x05: { const t = d[sp - 1]; d[sp - 1] = d[sp - 2]; d[sp - 2] = t; break; }
      case 0x06: d[sp] = d[sp - 2]; sp++; break;
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = d[sp - 3]; d[sp - 3] = d[sp - 2]; d[sp - 2] = d[sp - 1]; d[sp - 1] = a;
        break;
      }
      case 0x17: d[sp - 1] = (-d[sp - 1]) | 0; break;
      case 0x1b: d[sp - 1] = ~d[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = d[sp - 1], a = d[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // low 32 bits of the product
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        d[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = d[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === CMAX) return done(7);
        c[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return done(8);
        pc = c[--cp];
        break;
      case 0x40: {
        const addr = d[sp - 1];
        if (addr < 0 || addr >= MEM) return done(6);
        d[sp - 1] = m[addr];
        break;
      }
      case 0x41: {
        const addr = d[sp - 1], v = d[sp - 2];
        if (addr < 0 || addr >= MEM) return done(6);
        sp -= 2;
        m[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(d[sp - 1]));
        if (olen + bytes.length > OUTMAX) return done(11);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > OUTMAX) return done(11);
        out[olen++] = d[--sp] & 255;
        break;
      case 0x52:
        d[sp++] = ipos < inp.length ? inp[ipos++] : -1;
        break;
      case 0x53: return done(d[--sp] & 255);
      default: return done(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(I).sort()) {
  const prog = new Uint8Array(readFileSync(join(I, id, 'program.bin')));
  const input = new Uint8Array(readFileSync(join(I, id, 'input.bin')));
  const r = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
