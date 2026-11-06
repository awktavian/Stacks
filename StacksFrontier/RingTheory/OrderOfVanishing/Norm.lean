module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Lattice.Defs
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.OrdIntBasics
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.CokerLenDevissage
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.BaseChangeDetNorm
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.LocalizationLengthSum
public import StacksFrontier.RingTheory.OrderOfVanishing.Norm.InertiaDegreeFormula

/-!
# The order of vanishing of a norm

All rings are commutative with unit. The data is a ring map `A → B` in which `A` is a Noetherian
local domain of Krull dimension `1` and `A ⊆ B` is a finite extension of domains, so `A → B` is
injective, `B` is an integral domain, and `B` is finite as an `A`-module. Write `K = Frac A` and
`L = Frac B` for the fraction fields, so that `L/K` is a finite field extension.

The main result: for `y ∈ L*` with `x = Nm_{L/K}(y) ∈ K*`, and `m₁, …, m_n` the maximal ideals of
the semi-local ring `B`,

`ord_A(x) = ∑_{i=1}^{n} [κ(mᵢ) : κ(m_A)] · ord_{B_{mᵢ}}(y)`.
-/

@[expose] public section


open Ring

