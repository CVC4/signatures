import Cdclt.Quant

open proof
open proof.sort proof.term
open rules
open quantRules


def u1 := atom 1
def u2 := atom 2
def x := (const 60 u1)
def f1 := const 61 (arrow u1 u1)
def t1  := const 62 u1
def t2 := const 63 u2
def p1 := const 64 (arrow u1 boolSort)

def myquant := qforall 60 (f1 • x) -- this binds the variable
def myquant2 := qforall 60 x -- this binds the variable

theorem testInst1 : thHolds myquant → thHolds (f1 • t1) :=
λ s0 : thHolds myquant =>
show thHolds (f1 • t1) from instForall t1 s0

-- should not go through since t2 has different type from x
-- theorem testInst2 : thHolds myquant → thHolds (f1 • t2) :=
-- λ s0 : thHolds myquant =>
-- show thHolds (f1 • t2) from instForall t2 s0
