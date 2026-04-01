# ClearSplit — Verified Expense Splitting

A group expense splitting app with formally verified balance logic, built with [LemmaScript](https://github.com/midspiral/LemmaScript) and React.

This is a greenfield reimplementation of the [Dafny ClearSplit](https://github.com/metareflection/dafny-replay/tree/main/clear-split) using LemmaScript — the TypeScript is both the implementation and the verified source. No compilation bridge, no BigNumber.js.

## Setup

**Prerequisites:** [elan](https://github.com/leanprover/elan) (Lean 4 toolchain), Node.js >= 18.

**Clone dependencies:**

```sh
git clone https://github.com/namin/loom.git -b lemma ../loom
git clone https://github.com/namin/velvet.git -b lemma ../velvet
git clone https://github.com/midspiral/LemmaScript.git ../lemmascript
```

**Install:**

```sh
npm install
cd ../lemmascript/tools && npm install
```

**Verify (first time fetches mathlib cache):**

```sh
lake build
```

**Run the web app:**

```sh
npm run dev
```

## What's Verified

### Per-Function Properties

- **`expenseDelta`** — ensures correct delta for payer vs non-payer
- **`computeBalance`** — loop invariant maintained across all expenses

### Conservation Theorem

For a single expense where shares sum to the amount, the sum of all member deltas is zero:

```lean
theorem single_expense_conservation
    (hpayer : 0 <= paidBy && paidBy < n)
    (hshares : Pure.sumTo shares n = amount) :
    sumDeltas paidBy amount shares n = 0
```

Proved by induction with two helper lemmas (`sumDeltas_no_payer`, `sumDeltas_with_payer`). No sorry.

### Model and Operations

- **`step`** — validates and applies `addExpense` / `addSettlement` actions, returning a new model
- Pure function mirror in `namespace Pure` with match on action variants

## File Structure

```
src/logic/
  logic.ts              <- Annotated TypeScript (types, pure helpers, operations)
  logic.types.lean      <- Generated: structures, Pure namespace with defs
  logic.def.lean        <- Generated: Velvet method definitions
  logic.proof.lean      <- Proofs: per-step + conservation theorem
src/
  App.tsx               <- React UI
  App.css               <- Light theme
```

## How It Works

1. Add `//@ ` annotations to TypeScript:

   ```typescript
   //@ ensures paidBy === member ==> \result === amount - share
   ```

2. Generate Lean:

   ```sh
   cd ../lemmascript
   npx tsx tools/src/lsc.ts gen /path/to/logic.ts
   ```

3. Write proofs (or let `loom_solve` handle it):

   ```lean
   prove_correct expenseDelta by
     unfold Pure.expenseDelta; loom_solve
   ```

4. Verify:
   ```sh
   lake build
   ```

The TypeScript is the source of truth. The Lean is generated from it. The React app imports the verified logic directly.

## Architecture

The key simplification over the Dafny version: **array indices instead of string maps**. Members are identified by position `[0, memberCount)`. Expenses store `shares[memberIdx]` directly. This eliminates ~350 LOC of Dafny lemmas for map/set/sequence equivalence while preserving the same conservation guarantee.

**Pure functions** (no loops, no mutation) generate both a Lean `def` in `namespace Pure` and a Velvet method wrapper (`return Pure.fnName args`). Proofs reference the pure def; other methods call the wrapper.
