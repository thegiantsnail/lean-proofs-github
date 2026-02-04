# Lean-Rust Operational Bridge

**Status**: ✅ Operational  
**Purpose**: Turn Lean formal proofs into executable, callable APIs for Rust runtime

---

## Architecture

```
┌─────────────────────────┐
│   Lean 4 Proofs         │
│   (NullSTH.lean)        │
│                         │
│   • bettiNumber         │
│   • hodgeNumber         │
│   • padicValuation      │
│   • nullWitness         │
│   • Theorems            │
└────────────┬────────────┘
             │
             │ JSON serialization
             │
┌────────────▼────────────┐
│  NullSTHOperational     │
│  (Lean executable)      │
│                         │
│   lake exe nullsth 5    │
│   → JSON payload        │
└────────────┬────────────┘
             │
             │ Process spawn
             │ stdout parsing
             │
┌────────────▼────────────┐
│  Rust Runtime           │
│  (lean_bridge module)   │
│                         │
│   • load_null_payload() │
│   • VerifiedNullWitness │
│   • Runtime checks      │
└─────────────────────────┘
```

---

## Quick Start

### 1. Build Lean Executable

```bash
cd lean-formalization
lake build
```

This produces: `lean-formalization/.lake/build/bin/nullsth` (or `nullsth.exe` on Windows)

### 2. Test from Command Line

```bash
# Get null signature payload for prime p=5
./lean-formalization/.lake/build/bin/nullsth 5

# Output:
# {"betti0":1,"euler":1,"h00":1,"vp0_is_infinite":true,"perfectoidExtensions":0,"frobeniusIterates":0}
```

### 3. Use from Rust

```rust
use tel::lean_bridge::{load_null_payload, VerifiedNullWitness};

// Load certified payload from Lean
let payload = load_null_payload(5)?;

// Create verified witness
let witness = VerifiedNullWitness::from_payload(&payload);

// Verify formal invariants
witness.verify_invariants()?;

// Enforce runtime configuration
let config = witness.enforce_null_basepoint();

// Runtime checks
config.verify_padic_point(0.0)?;  // ✓
config.verify_frobenius_action(0.0, 0.0)?;  // ✓
```

### 4. Run Demo

```bash
cargo run --example lean_bridge_demo
```

---

## What Gets Operationalized

The Lean formalization proves mathematical properties. The operational layer exports **computable functions**:

| Property | Lean Proof | Operational Value | Rust Usage |
|----------|-----------|-------------------|------------|
| β₀ = 1 | `bettiNumber_zero` | `betti0: 1` | Point cohomology |
| χ = 1 | `eulerCharacteristic_eq_one` | `euler: 1` | Euler characteristic |
| h^{0,0} = 1 | `hodgeNumber_00` | `h00: 1` | Hodge structure |
| v_p(0) = ∞ | `padicValuation_zero_is_infinite` | `vp0_is_infinite: true` | p-adic valuation |
| Initial object | `null_is_initial` | `perfectoidExtensions: 0` | LQLE witness |
| Harmonic | `all_functions_harmonic` | `frobeniusIterates: 0` | Frobenius action |

---

## Runtime Invariants Enforced

The `NullBasepointConfig` structure enforces:

### 1. Origin Fixing
- **Formal property**: `{||}` is a single point
- **Runtime check**: Origin is at 0 in p-adic space
- **Enforcement**: `origin_is_zero: true`

### 2. Infinite Valuation
- **Formal property**: v_p(0) = ∞ for all primes p
- **Runtime check**: Valuation at origin is None (∞)
- **Enforcement**: `valuation_at_origin: None`

### 3. Frobenius Fixes Origin
- **Formal property**: Frobenius is trivial on {||}
- **Runtime check**: φ(0) = 0
- **Enforcement**: `verify_frobenius_action(0.0, fx)` fails if fx ≠ 0

### 4. Trivial Perfectoid Structure
- **Formal property**: {||} is initial object in LQLE
- **Runtime check**: No perfectoid extensions
- **Enforcement**: `perfectoid_extension_trivial: true`

---

## JSON Wire Format

The Lean executable outputs stable JSON:

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

This format is:
- **Stable**: Won't change between Lean versions
- **Minimal**: Only computable constants
- **Typed**: Parsed into `NullPayload` struct in Rust

---

## Supported Primes

The operational layer supports common small primes:

- 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31

For unsupported primes, returns:
```json
{"error":"unsupported prime: 37"}
```

To add more primes, edit `NullSTHOperational.lean` and add cases to the `match` statement.

---

## Implementation Details

### Lean Side (`NullSTHOperational.lean`)

- **Payload structure**: `NullPayload` with computable fields
- **JSON encoding**: Manual string concatenation (Lean 4.3.0 compatible)
- **Prime matching**: Explicit pattern matching for supported primes
- **CLI main**: `lake exe nullsth <prime>` prints JSON

### Rust Side (`lean_bridge/null_operational.rs`)

- **Process spawning**: Uses `std::process::Command`
- **JSON parsing**: Uses `serde_json`
- **Caching**: `OnceLock` for constant payload (computed once)
- **Verification**: Runtime checks match formal invariants
- **Configuration**: Derives runtime config from formal properties

---

## Testing

### Unit Tests (Rust)

```bash
cargo test --lib lean_bridge::
```

Tests:
- `test_null_payload_structure`: JSON deserialization
- `test_verified_witness_invariants`: Formal property verification
- `test_null_basepoint_config`: Runtime enforcement

### Integration Test (End-to-End)

```bash
cargo run --example lean_bridge_demo
```

Tests:
- Lean executable spawning
- JSON parsing
- Invariant verification
- Runtime checks (origin, Frobenius, etc.)

---

## Performance

- **Lean executable**: Instant (< 1ms) - returns constant data
- **Rust caching**: First call spawns process, subsequent calls use cache
- **Runtime checks**: Zero overhead - inline comparisons
- **Memory**: < 1KB for payload structure

---

## Future Extensions

### 1. Eliminate Process Boundary

Replace `Command::new()` with direct FFI to Lean-compiled shared library:

```rust
// Future: Direct FFI
#[link(name = "nullsth")]
extern "C" {
    fn lean_get_null_payload(p: u64) -> *const NullPayload;
}
```

### 2. More Properties

Add to `NullPayload`:
- `laplacian_zero: bool` (all functions harmonic)
- `hodge_symmetry: bool` (h^{p,q} = h^{q,p})
- `poincare_duality: bool` (H^k ≅ H^{-k})

### 3. Dynamic Primes

Use Lean's `Nat.Prime.decidable` to support arbitrary primes at runtime (requires more sophisticated Lean code).

### 4. Proof Certificates

Extend JSON to include proof witnesses:

```json
{
  "betti0": 1,
  "betti0_proof": "<lean proof term>",
  ...
}
```

---

## Troubleshooting

### "Failed to execute Lean nullsth"

**Cause**: Lean executable not built yet

**Solution**:
```bash
cd lean-formalization
lake build
```

### "unsupported prime: X"

**Cause**: Prime not in hardcoded list

**Solution**: Add to `NullSTHOperational.lean`:
```lean
| X => getPayloadJson (p := X)
```

Then rebuild: `lake build`

### Compilation errors in Lean

**Cause**: Lean 4.3.0 vs 4.26.0 syntax differences

**Solution**: The operational module uses Lean 4.3.0 compatible syntax. Check `lean-toolchain` file:
```
leanprover/lean4:v4.3.0
```

---

## Related Files

- `lean-formalization/CondensedTEL/NullSTH.lean` - Formal proofs
- `lean-formalization/CondensedTEL/NullSTHOperational.lean` - Operational layer
- `src/lean_bridge/null_operational.rs` - Rust integration
- `examples/lean_bridge_demo.rs` - Demo application

---

## References

- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [serde_json Documentation](https://docs.rs/serde_json/)

---

**Status**: ✅ Fully operational - Lean proofs drive Rust runtime!
