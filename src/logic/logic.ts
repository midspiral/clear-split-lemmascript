/**
 * ClearSplit — verified expense splitting.
 *
 * All money is in cents (integers). Members are identified by array index [0, memberCount).
 * Key invariant: the sum of all balances is always zero (conservation).
 */

// ── Data types ──────────────────────────────────────────────

export interface Expense {
  paidBy: number;    // member index
  amount: number;    // total in cents
  shares: number[];  // shares[m] = how much member m consumed
}

export interface Settlement {
  from: number;      // member index (payer)
  to: number;        // member index (payee)
  amount: number;    // cents
}

export type Action =
  | { tag: 'addExpense'; expense: Expense }
  | { tag: 'addSettlement'; settlement: Settlement };

export interface Model {
  memberCount: number;
  expenses: Expense[];
  settlements: Settlement[];
}

// ── Pure spec helpers ───────────────────────────────────────

//@ pure
function sumTo(arr: number[], n: number): number {
  //@ type n nat
  if (n === 0) return 0;
  return sumTo(arr, n - 1) + arr[n - 1];
}

//@ pure
function expenseDelta(paidBy: number, amount: number, share: number, member: number): number {
  //@ ensures paidBy === member ==> \result === amount - share
  //@ ensures paidBy !== member ==> \result === 0 - share
  if (paidBy === member) return amount - share;
  return 0 - share;
}

//@ pure
function settlementDelta(from: number, to: number, amount: number, member: number): number {
  //@ ensures from === member ==> \result === amount
  //@ ensures to === member && from !== member ==> \result === 0 - amount
  //@ ensures from !== member && to !== member ==> \result === 0
  if (from === member) return amount;
  if (to === member) return 0 - amount;
  return 0;
}

// ── Verified operations ─────────────────────────────────────

/**
 * Compute balance for one member across all expenses.
 * Positive = owed by group. Negative = owes to group.
 */
export function computeBalance(
  paidBy: number[],
  amounts: number[],
  shares: number[],
  member: number,
  expenseCount: number,
): number {
  //@ type member nat
  //@ type expenseCount nat
  //@ type i nat
  let balance = 0;

  let i = 0;
  while (i < expenseCount) {
    //@ decreases expenseCount - i
    //@ invariant i <= expenseCount
    balance = balance + expenseDelta(paidBy[i], amounts[i], shares[i], member);
    i = i + 1;
  }

  return balance;
}

/**
 * Validate and apply an action to the model.
 * Returns the new model, or the original if the action is invalid.
 */
export function step(model: Model, action: Action): Model {
  if (action.tag === 'addExpense') {
    const e = action.expense;
    if (e.paidBy < 0) return model;
    if (e.paidBy >= model.memberCount) return model;
    if (e.amount < 0) return model;
    return { memberCount: model.memberCount, expenses: [...model.expenses, e], settlements: model.settlements };
  }
  if (action.tag === 'addSettlement') {
    const s = action.settlement;
    if (s.from < 0) return model;
    if (s.to < 0) return model;
    if (s.from >= model.memberCount) return model;
    if (s.to >= model.memberCount) return model;
    if (s.from === s.to) return model;
    if (s.amount < 0) return model;
    return { memberCount: model.memberCount, expenses: model.expenses, settlements: [...model.settlements, s] };
  }
  return model;
}
