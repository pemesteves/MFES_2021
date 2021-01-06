sig Account {}

abstract sig Transaction { 
    amount: Int
}

-- A transaction is either a deposit or a withdrawal
sig Deposit, Withdrawal extends Transaction {} 

sig Client {
    accounts: some Account, -- a client can access several accounts (1 or more)
    withdrawPrivileges: set Account, -- but can’t withdraw from all of them (0..*)
    balance: Account set -> lone Int, -- the amount each account currently has   
    transactions: Account one -> set Transaction -- a list of all account movements
}

pred invariants[c: Client] {
    -- the balance of an account should never be lower than 0
    all i: c.balance[Account] | i >= 0

    -- a client can only withdraw from accounts she has access to
    c.withdrawPrivileges in c.accounts

    -- a client only has balance from accounts she has access to
    c.balance.Int in c.accounts
}

-- transaction t withdraws quantity q from account a of client c,
-- resulting in a new state c1
pred withdraw[c, c1: Client, a: Account, qty: Int, t: Transaction] {
    -- pre-conditions (without using predicate invariants)
    a in c.accounts
    a in c.withdrawPrivileges
    c1 = c
    qty > 0
    qty <= c.balance[a]

    -- post-conditions (without using predicate invariants)
    t.amount = 0 - qty
    c1.balance[a] = c.balance[a] - qty 
    c1.transactions = c.transactions + a -> t
}

-- gives the total balance of a client c
fun totalBalance[c: Client] : Int {
    {sum i: c.balance[Account] | i}
}

assert withdraw_preserves_invariants {
    all c, c1: Client, account: Account, qty: Int, t: Transaction |
        -- if one withdraws from a consistent client
        (invariants[c] and withdraw[c, c1, account, qty, t]) =>
        -- one ends up with a new consistent client state
        (invariants[c1])
}
check withdraw_preserves_invariants 