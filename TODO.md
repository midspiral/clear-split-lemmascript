# ClearSplit — LemmaScript Limits Reached

## Pipeline limitations (still open)

### Extract phase
- **`for` loops not supported** — only `while` and `for...of`. Must use while.
- **`i++` / `i--` not supported** — must use `i = i + 1`.
- **`+=` / `-=` not supported** — must use `total = total + arr[i]`.
- **`//@ type` annotations must be before first statement** — `collectAnnotations` only reads from function node + first body statement.

### Type annotations
- **No way to annotate array element types** — `paidBy: number[]` always becomes `Array Int`. Need something like `//@ type paidBy nat[]` to get `Array Nat`.

### Nat/Int for interface fields
- **`Model.memberCount` is `Int` but should be `Nat`** — `number` always maps to `Int`. No way to annotate interface fields as `Nat`. This prevents calling `sumTo` (which takes `Nat`) with `model.memberCount` in `validExpense`. Workaround: shares-sum check is in the Lean proof as a precondition, not in the TS invariant.

### Cross-file imports
- **TS imports don't generate Lean imports** — `import { Foo } from './bar'` is ignored. Workaround: put everything in one file. See DESIGN_IMPORT.md for the planned fix.

## Fixed in this session

- ~~Array fields in interfaces lose element type~~ — fixed `typeToString` to detect arrays
- ~~`to` not escaped as Lean keyword~~ — added to `LEAN_KEYWORDS`, also escape var/param names
- ~~Type declarations emitted in wrong order~~ — fixed to use source order
- ~~Redundant `_ =>` arm in exhaustive match~~ — skip when all variants covered
- ~~Spread syntax `[...arr, e]` not supported~~ — extract as `Array.push`
- ~~Method calls in expressions not lifted~~ — selective ANF (§4.6)
- ~~Pure functions duplicate body in method~~ — wrapper `return Pure.fnName args`
- ~~`spec-pure` call classification~~ — resolve tags spec-context calls to pure fns

## Done
- Invariant on Model (`inv` predicate with `validExpense`, `validSettlement`)
- `step` preserves `inv` (proven, no sorry)
- Single-expense conservation theorem (proven)
- `expenseDelta`, `computeBalance` verified
- React app wired to verified logic

## Not yet done
- **Global conservation** — sum of all balances across all members is zero for the full model
- **Delta laws** — precise per-person balance changes from addExpense/addSettlement
- **Settlements in computeBalance** — currently only expenses, no settlement deltas
- **Shares-sum-to-amount in TS invariant** — blocked by Nat/Int issue (see above)
- **`validExpense` should check `shares.length === memberCount`** — same Nat/Int blocker
