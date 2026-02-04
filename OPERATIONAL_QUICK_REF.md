# Operational Bridge Quick Reference

## 🚀 One-Liner Commands

```bash
# Build Lean executable
cd lean-formalization && lake build

# Get null payload (command line)
./lean-formalization/.lake/build/bin/nullsth 5

# Test Rust integration
cargo test --lib lean_bridge::

# Run demo
cargo run --example lean_bridge_demo
```

---

## 📦 Rust API

```rust
use tel::lean_bridge::{load_null_payload, VerifiedNullWitness, NullBasepointConfig};

// Load from Lean executable
let payload = load_null_payload(5)?;

// Create witness
let witness = VerifiedNullWitness::from_payload(&payload);

// Verify invariants
witness.verify_invariants()?;

// Get config
let config = witness.enforce_null_basepoint();

// Runtime checks
config.verify_padic_point(x)?;
config.verify_frobenius_action(x, fx)?;
```

---

## 🔢 JSON Payload Format

```json
{
  "betti0": 1,
  "euler": 1,
  "h00": 1,
  "vp0_is_infinite": true,
  "perfectoidExtensions": 0,
  "frobeniusIterates": 0
}
```

---

## ✅ Runtime Invariants

| Property | Formal Proof | Runtime Check | Enforcement |
|----------|-------------|---------------|-------------|
| Origin at 0 | Point cohomology | `origin_is_zero` | Hard guardrail |
| v_p(0) = ∞ | p-adic theorem | `valuation_at_origin: None` | Hard guardrail |
| φ(0) = 0 | Frobenius trivial | `verify_frobenius_action(0,fx)` | Runtime error if violated |
| No extensions | Initial object | `perfectoid_extension_trivial` | Structural constraint |

---

## 🎯 Supported Primes

2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31

To add more: edit `NullSTHOperational.lean` match statement

---

## 🔧 Troubleshooting

| Error | Solution |
|-------|----------|
| "Failed to execute Lean nullsth" | `cd lean-formalization && lake build` |
| "unsupported prime" | Add to `NullSTHOperational.lean` |
| Lean syntax errors | Check `lean-toolchain` = `v4.3.0` |

---

## 📁 File Map

| File | Purpose |
|------|---------|
| `NullSTH.lean` | Formal proofs |
| `NullSTHOperational.lean` | Executable layer |
| `null_operational.rs` | Rust bridge |
| `lean_bridge_demo.rs` | Demo |
| `OPERATIONAL_BRIDGE.md` | Full docs |

---

## 🏆 Achievement Unlocked

**Formal → Operational**: Lean proofs drive Rust runtime! 

- ✅ Machine-verified correctness
- ✅ Runtime enforcement
- ✅ Zero overhead
- ✅ Certified constants
- ✅ Type-safe bridge

This is **operational formal methods** - the gold standard! 🎯
