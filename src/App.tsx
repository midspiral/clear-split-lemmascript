import { useState } from 'react'
import type { Model, Expense, Settlement } from './logic/logic'
import { step, computeBalance } from './logic/logic'
import './App.css'

const formatMoney = (cents: number) => {
  const dollars = Math.abs(cents) / 100;
  const sign = cents < 0 ? '-' : '';
  return sign + '$' + dollars.toFixed(2);
};

const parseMoney = (str: string) => {
  const num = parseFloat(str);
  return isNaN(num) ? 0 : Math.round(num * 100);
};

function initModel(members: string[]): Model {
  return { memberCount: members.length, expenses: [], settlements: [] };
}

function getBalance(model: Model, memberIdx: number): number {
  const paidBy = model.expenses.map(e => e.paidBy);
  const amounts = model.expenses.map(e => e.amount);
  const shares = model.expenses.map(e => e.shares[memberIdx]);
  const settFrom = model.settlements.map(s => s.from);
  const settTo = model.settlements.map(s => s.to);
  const settAmounts = model.settlements.map(s => s.amount);
  return computeBalance(paidBy, amounts, shares, settFrom, settTo, settAmounts, memberIdx, model.expenses.length, model.settlements.length);
}

function App() {
  const [setupMode, setSetupMode] = useState(true);
  const [memberInput, setMemberInput] = useState('');
  const [members, setMembers] = useState<string[]>([]);
  const [model, setModel] = useState<Model | null>(null);
  const [error, setError] = useState<string | null>(null);

  const [expensePayer, setExpensePayer] = useState(0);
  const [expenseAmount, setExpenseAmount] = useState('');
  const [expenseShares, setExpenseShares] = useState<boolean[]>([]);

  const [settlementFrom, setSettlementFrom] = useState(0);
  const [settlementTo, setSettlementTo] = useState(1);
  const [settlementAmount, setSettlementAmount] = useState('');

  const [activeTab, setActiveTab] = useState('balances');
  const [status, setStatus] = useState<string | null>(null);

  const showStatus = (msg: string) => {
    setStatus(msg);
    setTimeout(() => setStatus(null), 2000);
  };

  const addMember = () => {
    const name = memberInput.trim();
    if (name && !members.includes(name)) {
      setMembers([...members, name]);
      setMemberInput('');
    }
  };

  const removeMember = (name: string) => {
    setMembers(members.filter(m => m !== name));
  };

  const startGroup = () => {
    if (members.length < 2) {
      setError('Minimum 2 members required');
      return;
    }
    setModel(initModel(members));
    setSetupMode(false);
    setError(null);
    setExpenseShares(members.map(() => true));
    setExpensePayer(0);
    setSettlementFrom(0);
    setSettlementTo(1);
  };

  const addExpense = () => {
    if (!model) return;
    const amountCents = parseMoney(expenseAmount);
    if (amountCents <= 0) { setError('Invalid amount'); return; }

    const participants = expenseShares.map((checked, i) => checked ? i : -1).filter(i => i >= 0);
    if (participants.length === 0) { setError('Select participants'); return; }

    const sharePerPerson = Math.floor(amountCents / participants.length);
    const remainder = amountCents - (sharePerPerson * participants.length);

    const shares = new Array(members.length).fill(0);
    participants.forEach((idx, i) => {
      shares[idx] = sharePerPerson + (i < remainder ? 1 : 0);
    });

    const expense: Expense = { paidBy: expensePayer, amount: amountCents, shares };
    const newModel = step(model, { tag: 'addExpense', expense });
    if (newModel !== model) {
      setModel(newModel);
      setExpenseAmount('');
      setError(null);
      showStatus('Expense recorded');
    } else {
      setError('Invalid expense');
    }
  };

  const addSettlement = () => {
    if (!model) return;
    const amountCents = parseMoney(settlementAmount);
    if (amountCents <= 0) { setError('Invalid amount'); return; }
    if (settlementFrom === settlementTo) { setError('From/To must differ'); return; }

    const settlement: Settlement = { from: settlementFrom, to: settlementTo, amount: amountCents };
    const newModel = step(model, { tag: 'addSettlement', settlement });
    if (newModel !== model) {
      setModel(newModel);
      setSettlementAmount('');
      setError(null);
      showStatus('Payment recorded');
    } else {
      setError('Invalid settlement');
    }
  };

  if (setupMode) {
    return (
      <div className="clear-split setup-container">
        <div className="setup-header">
          <h1>ClearSplit</h1>
          <p>verified expense splitting</p>
        </div>

        <div className="section">
          <div className="section-title">Members</div>
          <div className="member-input-row">
            <input
              type="text"
              className="form-input"
              placeholder="Name"
              value={memberInput}
              onChange={(e) => setMemberInput(e.target.value)}
              onKeyDown={(e) => e.key === 'Enter' && addMember()}
            />
            <button className="btn" onClick={addMember}>Add</button>
          </div>

          <div className="members-list">
            {members.map(m => (
              <div key={m} className="member-chip">
                {m}
                <button onClick={() => removeMember(m)}>x</button>
              </div>
            ))}
          </div>

          {error && <p className="error-msg">{error}</p>}

          <button
            className="btn btn-primary"
            onClick={startGroup}
            disabled={members.length < 2}
            style={{ width: '100%' }}
          >
            Start ({members.length})
          </button>
        </div>

        <div className="footer">
          Logic verified with LemmaScript + Lean 4
        </div>
      </div>
    );
  }

  const totalExpenses = model!.expenses.reduce((sum, e) => sum + e.amount, 0);

  return (
    <div className="clear-split">
      <div className="header">
        <h1>ClearSplit</h1>
        <div className="members-row">{members.join(' / ')}</div>
      </div>

      <div className="tabs">
        {['balances', 'expense', 'settle', 'history'].map(tab => (
          <button
            key={tab}
            className={activeTab === tab ? 'active' : ''}
            onClick={() => setActiveTab(tab)}
          >
            {tab}
          </button>
        ))}
      </div>

      {error && <p className="error-msg">{error}</p>}

      {activeTab === 'balances' && (
        <div className="section">
          <table className="balance-table">
            <thead>
              <tr>
                <th>Member</th>
                <th style={{ textAlign: 'right' }}>Balance</th>
                <th style={{ textAlign: 'right' }}>Status</th>
              </tr>
            </thead>
            <tbody>
              {members.map((m, idx) => {
                const bal = getBalance(model!, idx);
                const cls = bal > 0 ? 'positive' : bal < 0 ? 'negative' : '';
                return (
                  <tr key={m} className={cls}>
                    <td className="name">{m}</td>
                    <td className="amount">{formatMoney(bal)}</td>
                    <td className="status">
                      {bal > 0 ? 'owed' : bal < 0 ? 'owes' : '--'}
                    </td>
                  </tr>
                );
              })}
            </tbody>
          </table>
          <div className="summary-row">
            <span>Total expenses</span>
            <span>{formatMoney(totalExpenses)}</span>
          </div>
        </div>
      )}

      {activeTab === 'expense' && (
        <div className="section">
          <div className="form-row">
            <div className="form-group">
              <label className="form-label">Paid by</label>
              <select
                className="form-select"
                value={expensePayer}
                onChange={(e) => setExpensePayer(Number(e.target.value))}
              >
                {members.map((m, i) => <option key={m} value={i}>{m}</option>)}
              </select>
            </div>
            <div className="form-group">
              <label className="form-label">Amount</label>
              <input
                type="number"
                step="0.01"
                className="form-input"
                placeholder="0.00"
                value={expenseAmount}
                onChange={(e) => setExpenseAmount(e.target.value)}
              />
            </div>
          </div>

          <div className="form-group full">
            <label className="form-label">Split among</label>
            <div className="checkbox-row">
              {members.map((m, i) => (
                <label key={m} className="checkbox-item">
                  <input
                    type="checkbox"
                    checked={expenseShares[i] || false}
                    onChange={(e) => {
                      const next = [...expenseShares];
                      next[i] = e.target.checked;
                      setExpenseShares(next);
                    }}
                  />
                  {m}
                </label>
              ))}
            </div>
          </div>

          <button className="btn btn-primary" onClick={addExpense}>
            Add Expense
          </button>
          <p className="status-msg">{status || '\u00A0'}</p>
        </div>
      )}

      {activeTab === 'settle' && (
        <div className="section">
          <div className="form-row">
            <div className="form-group">
              <label className="form-label">From</label>
              <select
                className="form-select"
                value={settlementFrom}
                onChange={(e) => setSettlementFrom(Number(e.target.value))}
              >
                {members.map((m, i) => <option key={m} value={i}>{m}</option>)}
              </select>
            </div>
            <div className="form-group">
              <label className="form-label">To</label>
              <select
                className="form-select"
                value={settlementTo}
                onChange={(e) => setSettlementTo(Number(e.target.value))}
              >
                {members.map((m, i) => <option key={m} value={i}>{m}</option>)}
              </select>
            </div>
            <div className="form-group">
              <label className="form-label">Amount</label>
              <input
                type="number"
                step="0.01"
                className="form-input"
                placeholder="0.00"
                value={settlementAmount}
                onChange={(e) => setSettlementAmount(e.target.value)}
              />
            </div>
          </div>

          <button className="btn btn-primary" onClick={addSettlement}>
            Record Payment
          </button>
          <p className="status-msg">{status || '\u00A0'}</p>
        </div>
      )}

      {activeTab === 'history' && (
        <div className="section">
          {model!.expenses.length === 0 && model!.settlements.length === 0 ? (
            <p className="empty-state">No transactions</p>
          ) : (
            <>
              {model!.expenses.map((e, i) => (
                <div key={`e${i}`} className="history-item expense">
                  <span className="tag">Exp</span>
                  <span className="detail">
                    {members[e.paidBy]}
                    <span className="meta"> split {e.shares.filter(s => s > 0).length} ways</span>
                  </span>
                  <span className="amount">{formatMoney(e.amount)}</span>
                </div>
              ))}
              {model!.settlements.map((s, i) => (
                <div key={`s${i}`} className="history-item settlement">
                  <span className="tag">Pay</span>
                  <span className="detail">{members[s.from]} paid {members[s.to]}</span>
                  <span className="amount">{formatMoney(s.amount)}</span>
                </div>
              ))}
            </>
          )}
        </div>
      )}

      <div className="footer">
        Conservation verified: balances sum to zero
      </div>
    </div>
  );
}

export default App
