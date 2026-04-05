// Proofs for ClearSplit specification
// Ported from dafny-replay/clear-split/ClearSplit.dfy (adapted for array-based model)
// Proves: step preservation, single/global/settlement/full conservation, delta laws

include "logic.dfy"

// ============================================================================
// Safe array access (default 0 for out-of-bounds, like Lean's [i]!)
// ============================================================================

function GetShare(shares: seq<int>, m: nat): int {
  if m < |shares| then shares[m] else 0
}

// ============================================================================
// Step preserves invariant
// ============================================================================

// allExpensesValid over a prefix is unchanged when appending
lemma AllExpensesValidPrefix(expenses: seq<Expense>, e: Expense, n: nat, mc: nat)
  requires n <= |expenses|
  ensures allExpensesValid(expenses + [e], n, mc) == allExpensesValid(expenses, n, mc)
  decreases n
{
  if n == 0 {
  } else {
    assert (expenses + [e])[n-1] == expenses[n-1];
    AllExpensesValidPrefix(expenses, e, n-1, mc);
  }
}

// Appending a valid expense preserves allExpensesValid
lemma AllExpensesValidAppend(expenses: seq<Expense>, e: Expense, mc: nat)
  requires allExpensesValid(expenses, |expenses|, mc)
  requires validExpense(e, mc)
  ensures allExpensesValid(expenses + [e], |expenses| + 1, mc)
{
  assert |expenses + [e]| == |expenses| + 1;
  assert (expenses + [e])[|expenses|] == e;
  AllExpensesValidPrefix(expenses, e, |expenses|, mc);
}

// allSettlementsValid over a prefix is unchanged when appending
lemma AllSettlementsValidPrefix(settlements: seq<Settlement>, s: Settlement, n: nat, mc: nat)
  requires n <= |settlements|
  ensures allSettlementsValid(settlements + [s], n, mc) == allSettlementsValid(settlements, n, mc)
  decreases n
{
  if n == 0 {
  } else {
    assert (settlements + [s])[n-1] == settlements[n-1];
    AllSettlementsValidPrefix(settlements, s, n-1, mc);
  }
}

// Appending a valid settlement preserves allSettlementsValid
lemma AllSettlementsValidAppend(settlements: seq<Settlement>, s: Settlement, mc: nat)
  requires allSettlementsValid(settlements, |settlements|, mc)
  requires validSettlement(s, mc)
  ensures allSettlementsValid(settlements + [s], |settlements| + 1, mc)
{
  assert |settlements + [s]| == |settlements| + 1;
  assert (settlements + [s])[|settlements|] == s;
  AllSettlementsValidPrefix(settlements, s, |settlements|, mc);
}

// Step preserves invariant
lemma StepPreservesInv(model: Model, action: Action)
  requires inv(model)
  ensures inv(step(model, action))
{
  match action {
    case addExpense(e) =>
      if e.paidBy >= 0 && e.paidBy < model.memberCount && e.amount >= 0
         && |e.shares| == model.memberCount && sumTo(e.shares, model.memberCount) == e.amount {
        AllExpensesValidAppend(model.expenses, e, model.memberCount);
      }
    case addSettlement(s) =>
      if s.from >= 0 && s.to >= 0 && s.from < model.memberCount && s.to < model.memberCount
         && s.from != s.to && s.amount >= 0 {
        AllSettlementsValidAppend(model.settlements, s, model.memberCount);
      }
  }
}

// ============================================================================
// Single expense conservation
// ============================================================================

// Sum of expenseDelta across members [0, n) for a single expense
function SumDeltas(paidBy: int, amount: int, shares: seq<int>, n: nat): int
  decreases n
{
  if n == 0 then 0
  else SumDeltas(paidBy, amount, shares, n-1) + expenseDelta(paidBy, amount, GetShare(shares, n-1), n-1)
}

// When paidBy NOT in [0, n): sum = -sumTo(shares, n)
lemma SumDeltasNoPayer(paidBy: int, amount: int, shares: seq<int>, n: nat)
  requires n <= |shares|
  requires paidBy < 0 || paidBy >= n
  ensures SumDeltas(paidBy, amount, shares, n) == -sumTo(shares, n)
  decreases n
{
  if n == 0 {
  } else {
    SumDeltasNoPayer(paidBy, amount, shares, n-1);
    assert GetShare(shares, n-1) == shares[n-1];
  }
}

// When paidBy IS in [0, n): sum = amount - sumTo(shares, n)
lemma SumDeltasWithPayer(paidBy: int, amount: int, shares: seq<int>, n: nat)
  requires n <= |shares|
  requires 0 <= paidBy < n
  ensures SumDeltas(paidBy, amount, shares, n) == amount - sumTo(shares, n)
  decreases n
{
  if n == 0 {
    // Contradiction: 0 <= paidBy < 0
  } else if paidBy == n - 1 {
    // paidBy is the last member
    assert GetShare(shares, n-1) == shares[n-1];
    SumDeltasNoPayer(paidBy, amount, shares, n-1);
  } else {
    // paidBy is not n-1, recurse
    assert GetShare(shares, n-1) == shares[n-1];
    SumDeltasWithPayer(paidBy, amount, shares, n-1);
  }
}

// Single expense conservation: when shares sum to amount, deltas across all members = 0
lemma SingleExpenseConservation(paidBy: int, amount: int, shares: seq<int>, n: nat)
  requires n <= |shares|
  requires 0 <= paidBy < n
  requires sumTo(shares, n) == amount
  ensures SumDeltas(paidBy, amount, shares, n) == 0
{
  SumDeltasWithPayer(paidBy, amount, shares, n);
}

// ============================================================================
// Global expense conservation
// ============================================================================

// Balance for member m from one expense
function BalanceFromExpense(e: Expense, m: nat): int {
  expenseDelta(e.paidBy, e.amount, GetShare(e.shares, m), m)
}

// Balance for member m from expenses [0, k)
function BalanceFromExpenses(expenses: seq<Expense>, k: nat, m: nat): int
  requires k <= |expenses|
  decreases k
{
  if k == 0 then 0
  else BalanceFromExpenses(expenses, k-1, m) + BalanceFromExpense(expenses[k-1], m)
}

// Sum of member deltas [0, n) for one expense
function SumMemberDeltas(e: Expense, n: nat): int {
  SumDeltas(e.paidBy, e.amount, e.shares, n)
}

// Sum of balances across members [0, n) from all expenses [0, numExpenses)
function SumBalances(expenses: seq<Expense>, numExpenses: nat, n: nat): int
  requires numExpenses <= |expenses|
  decreases n
{
  if n == 0 then 0
  else SumBalances(expenses, numExpenses, n-1) + BalanceFromExpenses(expenses, numExpenses, n-1)
}

// With 0 expenses, sum is 0
lemma SumBalancesZeroExpenses(expenses: seq<Expense>, n: nat)
  ensures SumBalances(expenses, 0, n) == 0
  decreases n
{
  if n == 0 {
  } else {
    SumBalancesZeroExpenses(expenses, n-1);
  }
}

// Adding one expense to BalanceFromExpenses
lemma BalanceFromExpensesSplit(expenses: seq<Expense>, k: nat, m: nat)
  requires k < |expenses|
  ensures BalanceFromExpenses(expenses, k+1, m) == BalanceFromExpenses(expenses, k, m) + BalanceFromExpense(expenses[k], m)
{}

// Key sum-swap: sumBalances with k+1 expenses = sumBalances with k + sumMemberDeltas of expense k
lemma SumBalancesAddExpense(expenses: seq<Expense>, k: nat, n: nat)
  requires k < |expenses|
  ensures SumBalances(expenses, k+1, n) == SumBalances(expenses, k, n) + SumMemberDeltas(expenses[k], n)
  decreases n
{
  if n == 0 {
  } else {
    SumBalancesAddExpense(expenses, k, n-1);
    BalanceFromExpensesSplit(expenses, k, n-1);
  }
}

// Global expense conservation
lemma GlobalExpenseConservation(expenses: seq<Expense>, numExpenses: nat, memberCount: nat)
  requires numExpenses <= |expenses|
  requires forall i :: 0 <= i < numExpenses ==>
    0 <= expenses[i].paidBy < memberCount &&
    memberCount <= |expenses[i].shares| &&
    sumTo(expenses[i].shares, memberCount) == expenses[i].amount
  ensures SumBalances(expenses, numExpenses, memberCount) == 0
  decreases numExpenses
{
  if numExpenses == 0 {
    SumBalancesZeroExpenses(expenses, memberCount);
  } else {
    GlobalExpenseConservation(expenses, numExpenses - 1, memberCount);
    SumBalancesAddExpense(expenses, numExpenses - 1, memberCount);
    SingleExpenseConservation(
      expenses[numExpenses-1].paidBy,
      expenses[numExpenses-1].amount,
      expenses[numExpenses-1].shares,
      memberCount
    );
  }
}

// ============================================================================
// Settlement conservation
// ============================================================================

// Sum of settlementDelta across members [0, n) for one settlement
function SumSettlementDeltas(from_: int, to_: int, amount: int, n: nat): int
  decreases n
{
  if n == 0 then 0
  else SumSettlementDeltas(from_, to_, amount, n-1) + settlementDelta(from_, to_, amount, n-1)
}

// When neither from nor to is in [0, n): sum = 0
lemma SumSettlementDeltasNone(from_: int, to_: int, amount: int, n: nat)
  requires from_ < 0 || from_ >= n
  requires to_ < 0 || to_ >= n
  ensures SumSettlementDeltas(from_, to_, amount, n) == 0
  decreases n
{
  if n == 0 {
  } else {
    SumSettlementDeltasNone(from_, to_, amount, n-1);
  }
}

// When only from is in [0, n): sum = amount
lemma SumSettlementDeltasFromOnly(from_: int, to_: int, amount: int, n: nat)
  requires 0 <= from_ < n
  requires to_ < 0 || to_ >= n
  ensures SumSettlementDeltas(from_, to_, amount, n) == amount
  decreases n
{
  if n == 0 {
  } else if from_ == n - 1 {
    SumSettlementDeltasNone(from_, to_, amount, n-1);
  } else {
    SumSettlementDeltasFromOnly(from_, to_, amount, n-1);
  }
}

// When only to is in [0, n): sum = -amount
lemma SumSettlementDeltasToOnly(from_: int, to_: int, amount: int, n: nat)
  requires from_ < 0 || from_ >= n
  requires 0 <= to_ < n
  ensures SumSettlementDeltas(from_, to_, amount, n) == -amount
  decreases n
{
  if n == 0 {
  } else if to_ == n - 1 {
    SumSettlementDeltasNone(from_, to_, amount, n-1);
  } else {
    SumSettlementDeltasToOnly(from_, to_, amount, n-1);
  }
}

// Single settlement conservation: from + to cancel out
lemma SingleSettlementConservation(from_: int, to_: int, amount: int, n: nat)
  requires 0 <= from_ < n
  requires 0 <= to_ < n
  requires from_ != to_
  ensures SumSettlementDeltas(from_, to_, amount, n) == 0
  decreases n
{
  if n == 0 {
  } else if from_ == n - 1 {
    SumSettlementDeltasToOnly(from_, to_, amount, n-1);
  } else if to_ == n - 1 {
    SumSettlementDeltasFromOnly(from_, to_, amount, n-1);
  } else {
    SingleSettlementConservation(from_, to_, amount, n-1);
  }
}

// Balance for member m from one settlement
function BalanceFromSettlement(s: Settlement, m: nat): int {
  settlementDelta(s.from, s.to, s.amount, m)
}

// Balance for member m from settlements [0, k)
function BalanceFromSettlements(settlements: seq<Settlement>, k: nat, m: nat): int
  requires k <= |settlements|
  decreases k
{
  if k == 0 then 0
  else BalanceFromSettlements(settlements, k-1, m) + BalanceFromSettlement(settlements[k-1], m)
}

// Sum of settlement member deltas
function SumSettlementMemberDeltas(s: Settlement, n: nat): int {
  SumSettlementDeltas(s.from, s.to, s.amount, n)
}

// Sum of settlement balances across members [0, n)
function SumSettlementBalances(settlements: seq<Settlement>, numSett: nat, n: nat): int
  requires numSett <= |settlements|
  decreases n
{
  if n == 0 then 0
  else SumSettlementBalances(settlements, numSett, n-1) + BalanceFromSettlements(settlements, numSett, n-1)
}

lemma SumSettlementBalancesZero(settlements: seq<Settlement>, n: nat)
  ensures SumSettlementBalances(settlements, 0, n) == 0
  decreases n
{
  if n == 0 {
  } else {
    SumSettlementBalancesZero(settlements, n-1);
  }
}

lemma BalanceFromSettlementsSplit(settlements: seq<Settlement>, k: nat, m: nat)
  requires k < |settlements|
  ensures BalanceFromSettlements(settlements, k+1, m) == BalanceFromSettlements(settlements, k, m) + BalanceFromSettlement(settlements[k], m)
{}

lemma SumSettlementBalancesAdd(settlements: seq<Settlement>, k: nat, n: nat)
  requires k < |settlements|
  ensures SumSettlementBalances(settlements, k+1, n) == SumSettlementBalances(settlements, k, n) + SumSettlementMemberDeltas(settlements[k], n)
  decreases n
{
  if n == 0 {
  } else {
    SumSettlementBalancesAdd(settlements, k, n-1);
    BalanceFromSettlementsSplit(settlements, k, n-1);
  }
}

// Global settlement conservation
lemma GlobalSettlementConservation(settlements: seq<Settlement>, numSett: nat, memberCount: nat)
  requires numSett <= |settlements|
  requires forall i :: 0 <= i < numSett ==>
    0 <= settlements[i].from < memberCount &&
    0 <= settlements[i].to < memberCount &&
    settlements[i].from != settlements[i].to
  ensures SumSettlementBalances(settlements, numSett, memberCount) == 0
  decreases numSett
{
  if numSett == 0 {
    SumSettlementBalancesZero(settlements, memberCount);
  } else {
    GlobalSettlementConservation(settlements, numSett - 1, memberCount);
    SumSettlementBalancesAdd(settlements, numSett - 1, memberCount);
    SingleSettlementConservation(
      settlements[numSett-1].from,
      settlements[numSett-1].to,
      settlements[numSett-1].amount,
      memberCount
    );
  }
}

// ============================================================================
// Full conservation (expenses + settlements)
// ============================================================================

function FullBalance(expenses: seq<Expense>, numExp: nat, settlements: seq<Settlement>, numSett: nat, m: nat): int
  requires numExp <= |expenses|
  requires numSett <= |settlements|
{
  BalanceFromExpenses(expenses, numExp, m) + BalanceFromSettlements(settlements, numSett, m)
}

function SumFullBalances(expenses: seq<Expense>, numExp: nat, settlements: seq<Settlement>, numSett: nat, n: nat): int
  requires numExp <= |expenses|
  requires numSett <= |settlements|
  decreases n
{
  if n == 0 then 0
  else SumFullBalances(expenses, numExp, settlements, numSett, n-1) +
       FullBalance(expenses, numExp, settlements, numSett, n-1)
}

lemma SumFullBalancesSplit(expenses: seq<Expense>, numExp: nat, settlements: seq<Settlement>, numSett: nat, n: nat)
  requires numExp <= |expenses|
  requires numSett <= |settlements|
  ensures SumFullBalances(expenses, numExp, settlements, numSett, n) ==
          SumBalances(expenses, numExp, n) + SumSettlementBalances(settlements, numSett, n)
  decreases n
{
  if n == 0 {
  } else {
    SumFullBalancesSplit(expenses, numExp, settlements, numSett, n-1);
  }
}

// THE FULL CONSERVATION THEOREM
lemma FullConservation(expenses: seq<Expense>, numExp: nat,
                        settlements: seq<Settlement>, numSett: nat,
                        memberCount: nat)
  requires numExp <= |expenses|
  requires numSett <= |settlements|
  requires forall i :: 0 <= i < numExp ==>
    0 <= expenses[i].paidBy < memberCount &&
    memberCount <= |expenses[i].shares| &&
    sumTo(expenses[i].shares, memberCount) == expenses[i].amount
  requires forall i :: 0 <= i < numSett ==>
    0 <= settlements[i].from < memberCount &&
    0 <= settlements[i].to < memberCount &&
    settlements[i].from != settlements[i].to
  ensures SumFullBalances(expenses, numExp, settlements, numSett, memberCount) == 0
{
  SumFullBalancesSplit(expenses, numExp, settlements, numSett, memberCount);
  GlobalExpenseConservation(expenses, numExp, memberCount);
  GlobalSettlementConservation(settlements, numSett, memberCount);
}

// ============================================================================
// Delta laws
// ============================================================================

lemma SettlementDeltaFrom(from_: int, to_: int, amount: int, member: int)
  requires from_ == member
  ensures settlementDelta(from_, to_, amount, member) == amount
{}

lemma SettlementDeltaTo(from_: int, to_: int, amount: int, member: int)
  requires to_ == member
  requires from_ != member
  ensures settlementDelta(from_, to_, amount, member) == -amount
{}

lemma SettlementDeltaOther(from_: int, to_: int, amount: int, member: int)
  requires from_ != member
  requires to_ != member
  ensures settlementDelta(from_, to_, amount, member) == 0
{}

// Adding an expense changes member's balance by exactly balanceFromExpense
lemma BalanceFromExpensesPushPrefix(expenses: seq<Expense>, e: Expense, n: nat, m: nat)
  requires n <= |expenses|
  ensures BalanceFromExpenses(expenses + [e], n, m) == BalanceFromExpenses(expenses, n, m)
  decreases n
{
  if n == 0 {
  } else {
    assert (expenses + [e])[n-1] == expenses[n-1];
    BalanceFromExpensesPushPrefix(expenses, e, n-1, m);
  }
}

lemma AddExpenseDelta(expenses: seq<Expense>, e: Expense, m: nat)
  ensures BalanceFromExpenses(expenses + [e], |expenses| + 1, m) ==
          BalanceFromExpenses(expenses, |expenses|, m) + BalanceFromExpense(e, m)
{
  assert (expenses + [e])[|expenses|] == e;
  BalanceFromExpensesPushPrefix(expenses, e, |expenses|, m);
}
