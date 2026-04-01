# ClearSplit — LemmaScript Limits Reached

## Pipeline limitations (still open)

### Extract phase
- **`for` loops not supported** — only `while` and `for...of`. Must use while.
- **`i++` / `i--` not supported** — must use `i = i + 1`.
- **`+=` / `-=` not supported** — must use `total = total + arr[i]`.
- **`//@ type` annotations must be before first statement** — `collectAnnotations` only reads from function node + first body statement.

### Type annotations
- **No way to annotate array element types** — `paidBy: number[]` always becomes `Array Int`. Need something like `//@ type paidBy nat[]` to get `Array Nat`.

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
- ~~Nat/Int for interface fields~~ — `//@ type nat` trailing annotation on interface fields
- ~~Shares-sum-to-amount in TS invariant~~ — `validExpense` now checks `sumTo(shares, mc) === amount`
- ~~`validExpense` checks `shares.length === memberCount`~~ — included in strengthened invariant
- ~~Unified type mapping~~ — `parseTsType` replaces separate `tsTypeToLean` and `resolveTsType` paths

## Done
- Invariant on Model (`inv` with `validExpense` checking paidBy range, amount, shares length, shares sum)
- `step` preserves `inv` (proven, no sorry) — validates all conditions before accepting
- Single-expense conservation theorem (proven)
- Global conservation theorem (proven) — sum of all balances across all members is zero
- Settlement conservation theorem (proven) — from gets +amount, to gets -amount, net zero
- `expenseDelta`, `settlementDelta`, `computeBalance` verified (expenses + settlements)
- React app wired to verified logic (expenses + settlements)
- Delta laws: `add_expense_delta`, `settlement_delta_from/to/other`
- Interface field type annotations (`//@ type nat` trailing on field line)
- `validExpense` checks shares.length = memberCount and sumTo(shares) = amount
- `Model.memberCount` is `Nat` (via interface field annotation)

## Not yet done
- **Full conservation** — combine expense and settlement conservation into one theorem over the whole model
