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
  memberCount: number; //@ type nat
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

// ── Invariant predicates ────────────────────────────────────

//@ pure
function validExpense(e: Expense, memberCount: number): boolean {
  //@ type memberCount nat
  return e.paidBy >= 0 && e.paidBy < memberCount && e.amount >= 0
    && e.shares.length === memberCount && sumTo(e.shares, memberCount) === e.amount;
}

//@ pure
function allExpensesValid(expenses: Expense[], n: number, memberCount: number): boolean {
  //@ type n nat
  //@ type memberCount nat
  if (n === 0) return true;
  return validExpense(expenses[n - 1], memberCount) && allExpensesValid(expenses, n - 1, memberCount);
}

//@ pure
function validSettlement(s: Settlement, memberCount: number): boolean {
  //@ type memberCount nat
  return s.from >= 0 && s.to >= 0 && s.from < memberCount && s.to < memberCount && s.from !== s.to && s.amount >= 0;
}

//@ pure
function allSettlementsValid(settlements: Settlement[], n: number, memberCount: number): boolean {
  //@ type n nat
  //@ type memberCount nat
  if (n === 0) return true;
  return validSettlement(settlements[n - 1], memberCount) && allSettlementsValid(settlements, n - 1, memberCount);
}

//@ pure
function inv(model: Model): boolean {
  return allExpensesValid(model.expenses, model.expenses.length, model.memberCount)
    && allSettlementsValid(model.settlements, model.settlements.length, model.memberCount);
}

// ── Verified operations ─────────────────────────────────────

/**
 * Compute balance for one member across all expenses and settlements.
 * Positive = owed by group. Negative = owes to group.
 */
export function computeBalance(
  paidBy: number[],
  amounts: number[],
  shares: number[],
  settFrom: number[],
  settTo: number[],
  settAmounts: number[],
  member: number,
  expenseCount: number,
  settlementCount: number,
): number {
  //@ type member nat
  //@ type expenseCount nat
  //@ type settlementCount nat
  //@ type i nat
  //@ type j nat
  let balance = 0;

  let i = 0;
  while (i < expenseCount) {
    //@ decreases expenseCount - i
    //@ invariant i <= expenseCount
    balance += expenseDelta(paidBy[i], amounts[i], shares[i], member);
    i++;
  }

  let j = 0;
  while (j < settlementCount) {
    //@ decreases settlementCount - j
    //@ invariant j <= settlementCount
    balance += settlementDelta(settFrom[j], settTo[j], settAmounts[j], member);
    j++;
  }

  return balance;
}

/**
 * Validate and apply an action to the model.
 * Returns the new model, or the original if the action is invalid.
 */
export function step(model: Model, action: Action): Model {
  //@ requires inv(model)
  //@ ensures inv(\result)
  if (action.tag === 'addExpense') {
    const e = action.expense;
    if (e.paidBy < 0) return model;
    if (e.paidBy >= model.memberCount) return model;
    if (e.amount < 0) return model;
    if (e.shares.length !== model.memberCount) return model;
    if (sumTo(e.shares, model.memberCount) !== e.amount) return model;
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
