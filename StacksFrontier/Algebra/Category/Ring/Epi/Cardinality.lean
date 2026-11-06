module

public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cardinality bound for an epimorphism of rings

All rings are commutative with unit and all ring maps are unital. For a ring map `f : R → S`
we regard `S` as an `R`-algebra and form the tensor product `S ⊗[R] S`.

A ring map `f : R → S` is an *epimorphism* if it is an epimorphism in the category of
commutative rings, i.e. for every ring `T` and every pair of ring maps `g₁, g₂ : S → T`,
`g₁ ∘ f = g₂ ∘ f` implies `g₁ = g₂`. Equivalently, the two `R`-algebra maps
`λ : S → S ⊗[R] S`, `g ↦ g ⊗ 1` and `ρ : S → S ⊗[R] S`, `g ↦ 1 ⊗ g` coincide, that is
`g ⊗ 1 = 1 ⊗ g` in `S ⊗[R] S` for every `g : S`.

## Main results

* `epi_iff_tmul`: the categorical and tensor-product formulations of "epimorphism" agree.
* `epi_card_le`: if `f : R → S` is an epimorphism of rings then `|S| ≤ |R|`, equivalently
  there is an injection `S → R`.

The proof of the bound goes through an equational criterion: for each `g : S` with
`g ⊗ 1 = 1 ⊗ g` there are `n : ℕ`, a matrix `X` over `R` and vectors `y z : Fin n → S` with
`g = ∑ i, ∑ j, X i j • (y i * z j)` and every column combination `∑ i, X i j • y i` and row
combination `∑ j, X i j • z j` in the image of `f`. The resulting *associated triple*
`(n, X, U, V) : EpiTriple R` determines `g`, so `g ↦ (n, X, U, V)` is injective; the sigma
type of triples has cardinality at most `|R|` when `R` is infinite, and for finite `R` the
map `f` is outright surjective.

## References

* [Stacks, Tag 04VY](https://stacks.math.columbia.edu/tag/04VY)
* [Stacks, Tag 04W0](https://stacks.math.columbia.edu/tag/04W0)
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

/-! ### The tensor-product characterization of an epimorphism

The categorical epimorphism property of `f : R → S` is equivalent to the assertion that the two
`R`-algebra coprojections `λ ρ : S → S ⊗_R S`, `λ g = g ⊗ 1`, `ρ g = 1 ⊗ g`, agree.
-/

/-- One coprojection equals the other on the image of `f`: for `r : R`,
`f r ⊗ₜ 1 = 1 ⊗ₜ f r`. -/
theorem tmul_algebraMap (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    (letI := f.toAlgebra; ((f r) ⊗ₜ[R] (1 : S) : S ⊗[R] S) = (1 : S) ⊗ₜ[R] (f r)) := by
  let := f.toAlgebra
  have hr : f r = algebraMap R S r := by rw [RingHom.algebraMap_toAlgebra]
  rw [hr, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

/-- The categorical notion of epimorphism of commutative rings is equivalent to the
tensor-product characterization `g ⊗ 1 = 1 ⊗ g` for all `g : S`, where `S` is viewed as an
`R`-algebra via `f`. -/
theorem epi_iff_tmul (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔
      (letI := f.toAlgebra; ∀ g : S, (g ⊗ₜ[R] (1 : S) : S ⊗[R] S) = (1 : S) ⊗ₜ[R] g) := by
  let := f.toAlgebra
  have hf : CommRingCat.ofHom (algebraMap R S) = CommRingCat.ofHom f := by
    ext r; rw [RingHom.algebraMap_toAlgebra]
  rw [← hf, CommRingCat.epi_iff_epi, Algebra.isEpi_iff_forall_one_tmul_eq]
  exact forall_congr' fun _ => eq_comm

/-! ### The cardinality bound

For each `g : S` with `g ⊗ 1 = 1 ⊗ g` there are `n : ℕ`, `X : Matrix (Fin n) (Fin n) R` and
`y z : Fin n → S` with `g = ∑_{i,j} X i j • (y i * z j)` whose column combinations
`∑_i X i j • y i` and row combinations `∑_j X i j • z j` lie in the image of `f`. The associated
`n`-triple `(X, U, V)`, with `U` and `V` preimages of these combinations, determines `g`.
-/

/-- The type of associated `n`-triples `(n, P, U, V)`: an `n × n` matrix `P` over `R` together
with a row `U` and a column `V` over `R`. -/
abbrev EpiTriple (R : Type u) [CommRing R] : Type u :=
  Σ n : ℕ, Matrix (Fin n) (Fin n) R × (Fin n → R) × (Fin n → R)

open TensorProduct LinearMap Function Submodule Finsupp in
/-- `VanishesTrivially R m n` holds as soon as the canonical element
`∑ i, single i 1 ⊗ₜ n i` of `(ι →₀ R) ⊗ N` lies in the range of
`rTensor N (ker (linearCombination R m)).subtype`. -/
theorem vanishesTrivially_of_en_mem_range
    (R : Type*) [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ι : Type*} [Fintype ι] (m : ι → M) (n : ι → N)
    (hrange : (∑ i, (Finsupp.single i (1 : R)) ⊗ₜ[R] n i)
        ∈ range (rTensor N (ker (Finsupp.linearCombination R m)).subtype)) :
    TensorProduct.VanishesTrivially R m n := by
  classical
  set G : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R m with hG
  have G_basis_eq (i : ι) : G (Finsupp.single i 1) = m i := by simp [hG]
  set en : (ι →₀ R) ⊗[R] N := ∑ i, Finsupp.single i 1 ⊗ₜ n i with hen
  obtain ⟨kn, hkn⟩ := hrange
  obtain ⟨ma, rfl : kn = ∑ kj ∈ ma, kj.fst ⊗ₜ[R] kj.snd⟩ := exists_finset kn
  refine .of_fintype (κ := ma) (fun i ⟨⟨kj, _⟩, _⟩ ↦ (kj : ι →₀ R) i) (fun ⟨⟨_, yj⟩, _⟩ ↦ yj) ?_ ?_
  · intro i
    apply_fun finsuppScalarLeft R N ι at hkn
    apply_fun (· i) at hkn
    symm at hkn
    simp only [map_sum, finsuppScalarLeft_apply_tmul, zero_smul, Finsupp.single_zero,
      Finsupp.sum_single_index, one_smul, Finsupp.finsetSum_apply, Finsupp.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, rTensor_tmul, coe_subtype, Finsupp.sum_apply,
      Finsupp.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, ite_not, en] at hkn
    simp only [Finset.univ_eq_attach,
      Finset.sum_attach ma (fun x ↦ (x.fst : ι →₀ R) i • x.snd)]
    rw [hkn]
    refine Finset.sum_congr rfl (fun x _ ↦ ?_)
    split
    · next h'x => rw [h'x, zero_smul]
    · rfl
  · rintro ⟨⟨⟨k, hk⟩, _⟩, _⟩
    simpa only [hG, linearCombination_apply, zero_smul, implies_true, Finsupp.sum_fintype] using
      mem_ker.mp hk

/-- The equational criterion for an arbitrary generating family. Let `y : J → N` generate `N`
and let `m : J →₀ M` satisfy `∑_{j ∈ m.support} (m j) ⊗ y j = 0` in `M ⊗_R N`. Then there are
finitely many `x_i ∈ M` and finitely supported coefficient vectors `a_i ∈ (J →₀ R)` with
`m j = ∑_i (a_i j) • x_i` for every `j`, and `∑_j (a_i j) • y_j = 0` (i.e.
`linearCombination R y (a_i) = 0`) for every `i`. -/
theorem equationalCriterion_infinitary
    (R : Type u) [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {J : Type u} (y : J → N)
    (hy : Submodule.span R (Set.range y) = ⊤) (m : J →₀ M)
    (hmn : (m.sum fun j mj => mj ⊗ₜ[R] y j) = 0) :
    ∃ (k : ℕ) (x : Fin k → M) (a : Fin k → (J →₀ R)),
      (∀ j, m j = ∑ i, (a i j) • x i) ∧
      (∀ i, Finsupp.linearCombination R y (a i) = 0) := by
  classical
  set π : (J →₀ R) →ₗ[R] N := Finsupp.linearCombination R y with hπdef
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, hπdef, Finsupp.range_linearCombination]; exact hy
  have hex : Function.Exact (π.ker.subtype) π := LinearMap.exact_subtype_ker_map π
  have hker := LinearMap.exact_iff.mp (rTensor_exact (M := ↥(LinearMap.ker π))
    (N := (J →₀ R)) (P := N) (f := (LinearMap.ker π).subtype) (g := π) M hex hπ)
  set u : (J →₀ R) ⊗[R] M := m.sum (fun j mj => Finsupp.single j (1 : R) ⊗ₜ[R] mj) with hu
  have huker : u ∈ (LinearMap.rTensor M π).ker := by
    rw [LinearMap.mem_ker, hu, Finsupp.sum, map_sum]
    have hstep : (∑ j ∈ m.support, (LinearMap.rTensor M π) (Finsupp.single j (1 : R) ⊗ₜ[R] m j))
        = ∑ j ∈ m.support, (y j) ⊗ₜ[R] m j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [LinearMap.rTensor_tmul, hπdef, Finsupp.linearCombination_single, one_smul]
    rw [hstep]
    have hcomm : (∑ j ∈ m.support, (y j) ⊗ₜ[R] m j)
        = (TensorProduct.comm R M N) (m.sum fun j mj => mj ⊗ₜ[R] y j) := by
      rw [Finsupp.sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [TensorProduct.comm_tmul]
    rw [hcomm, hmn, map_zero]
  rw [hker] at huker
  obtain ⟨w, hw⟩ := huker
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset w
  set k := s.card with hk
  let e : Fin k ≃ s := (s.equivFin).symm
  refine ⟨k, fun i => ((e i).val.snd : M), fun i => ((e i).val.fst : J →₀ R), ?_, ?_⟩
  · intro j
    have hlhs : (TensorProduct.finsuppScalarLeft R M J) u = m := by
      rw [hu, Finsupp.sum, map_sum]
      rw [show (∑ j ∈ m.support, (TensorProduct.finsuppScalarLeft R M J) (Finsupp.single j (1:R)
          ⊗ₜ[R] m j))
            = ∑ j ∈ m.support, Finsupp.single j (m j) from ?_]
      · rw [← Finsupp.sum]; exact Finsupp.sum_single m
      · apply Finset.sum_congr rfl
        intro j _
        rw [TensorProduct.finsuppScalarLeft_apply_tmul]
        simp [Finsupp.sum_single_index]
    have hrhs : (TensorProduct.finsuppScalarLeft R M J) u
        = ∑ p ∈ s, (TensorProduct.finsuppScalarLeft R M J) ((p.fst : J →₀ R) ⊗ₜ[R] p.snd) := by
      rw [← hw, hs, map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [LinearMap.rTensor_tmul]
      rfl
    have hmeq : m = ∑ p ∈ s,
        (TensorProduct.finsuppScalarLeft R M J) ((p.fst : J →₀ R) ⊗ₜ[R] p.snd) := by
      rw [← hlhs, hrhs]
    have hmj := congrFun (congrArg (DFunLike.coe) hmeq) j
    rw [Finsupp.finsetSum_apply] at hmj
    simp only [TensorProduct.finsuppScalarLeft_apply_tmul_apply] at hmj
    rw [hmj]
    symm
    rw [Equiv.sum_comp e
      (fun q : s => (((q : (↥π.ker) × M).fst : J →₀ R) j) • (q : (↥π.ker) × M).snd)]
    exact Finset.sum_attach s (fun p => ((p.fst : J →₀ R) j) • p.snd)
  · exact fun i => LinearMap.mem_ker.mp (e i).val.fst.property

/-- The equational criterion with prescribed generators on both sides. Let `x : I → M` and
`y : J → N` generate `M` and `N`, and let `m : J →₀ M` satisfy `∑_j m_j ⊗ y_j = 0`. Then there is
a finitely supported coefficient family `a : I →₀ (J →₀ R)` with
  (1) `m_j = ∑_i a_{i,j} • x_i` for all `j ∈ J`, and
  (2) `∑_j a_{i,j} • y_j = 0` for all `i ∈ I`. -/
theorem equationalCriterion_bilateral
    (R : Type u) [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {I J : Type u} (x : I → M) (y : J → N)
    (hx : Submodule.span R (Set.range x) = ⊤)
    (hy : Submodule.span R (Set.range y) = ⊤) (m : J →₀ M)
    (hmn : (m.sum fun j mj => mj ⊗ₜ[R] y j) = 0) :
    ∃ a : I →₀ (J →₀ R),
      (∀ j, m j = (a.sum fun i ai => (ai j) • x i)) ∧
      (∀ i, Finsupp.linearCombination R y (a i) = 0) := by
  classical
  obtain ⟨k, x', a', hi, hii⟩ := equationalCriterion_infinitary R y hy m hmn
  have hxp : ∀ p : Fin k, ∃ c : I →₀ R, (c.sum fun l r => r • x l) = x' p := by
    intro p
    rw [← Finsupp.mem_span_range_iff_exists_finsupp, hx]
    exact Submodule.mem_top
  choose c hc using hxp
  set a : I →₀ (J →₀ R) :=
    Finset.univ.sum (fun p : Fin k => Finsupp.mapRange (· • a' p) (by simp) (c p)) with ha
  have happly : ∀ i, a i = ∑ p : Fin k, (c p i) • a' p := by
    intro i
    rw [ha, Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finsupp.mapRange_apply]
  refine ⟨a, ?_, ?_⟩
  · intro j
    set b : I →₀ R := a.mapRange (fun ai => ai j) (by simp) with hb
    have hbval : b = ∑ p : Fin k, (a' p j) • (c p) := by
      ext i
      rw [hb, Finsupp.mapRange_apply, happly i, Finsupp.finsetSum_apply]
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
        Finsupp.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_comm]
    have hRHS : (a.sum fun i ai => (ai j) • x i) = b.sum fun i r => r • x i := by
      rw [hb]
      rw [Finsupp.sum_mapRange_index (by intro i; rw [zero_smul])]
    rw [hi j, hRHS]
    symm
    have : b.sum (fun i r => r • x i) = Finsupp.linearCombination R x b := by
      rw [Finsupp.linearCombination_apply]
    rw [this, hbval, map_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [map_smul, Finsupp.linearCombination_apply, hc p]
  · intro i
    rw [happly i, map_sum]
    apply Finset.sum_eq_zero
    intro p _
    rw [map_smul, hii p, smul_zero]

/-- `g` has a matrix factorization with rows and columns landing in `f(R)`: there are `n`, a
matrix `X` over `R`, vectors `y z : Fin n → S`, and `R`-preimages `U V` of the column and row
combinations, with `g = ∑_{i,j} X_{ij} • (y_i z_j)`. -/
def HasMF (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S) (g : S) : Prop :=
  letI := f.toAlgebra
  ∃ (n : ℕ) (X : Matrix (Fin n) (Fin n) R) (y z : Fin n → S) (U V : Fin n → R),
    g = ∑ i, ∑ j, X i j • (y i * z j) ∧
    (∀ j, f (U j) = ∑ i, X i j • y i) ∧
    (∀ i, f (V i) = ∑ j, X i j • z j)

/-- Each element `f r` of the image of `f` has a matrix factorization. -/
theorem HasMF_algebraMap (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    HasMF R S f (f r) := by
  let := f.toAlgebra
  refine ⟨1, !![r], ![1], ![1], ![r], ![r], ?_, ?_, ?_⟩ <;>
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

/-- Elements with a matrix factorization are closed under addition. -/
theorem HasMF_add (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S) (g g' : S)
    (hg : HasMF R S f g) (hg' : HasMF R S f g') : HasMF R S f (g + g') := by
  let := f.toAlgebra
  obtain ⟨n, X, y, z, U, V, hval, hcol, hrow⟩ := hg
  obtain ⟨n', X', y', z', U', V', hval', hcol', hrow'⟩ := hg'
  have hs : ∀ F : Fin (n + n') → S, ∑ i, F i =
      ∑ a, F (finSumFinEquiv (Sum.inl a)) + ∑ b, F (finSumFinEquiv (Sum.inr b)) := fun F => by
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  refine ⟨n + n', fun i j => Sum.elim
      (fun a => Sum.elim (fun b => X a b) (fun _ => 0) (finSumFinEquiv.symm j))
      (fun a => Sum.elim (fun _ => 0) (fun b => X' a b) (finSumFinEquiv.symm j))
      (finSumFinEquiv.symm i),
    fun i => Sum.elim y y' (finSumFinEquiv.symm i),
    fun i => Sum.elim z z' (finSumFinEquiv.symm i),
    fun i => Sum.elim U U' (finSumFinEquiv.symm i),
    fun i => Sum.elim V V' (finSumFinEquiv.symm i), ?_, ?_, ?_⟩
  · rw [hval, hval', hs]
    simp [hs]
  · intro j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with b | b
    · simp [hs, hcol b]
    · simp [hs, hcol' b]
  · intro i
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    rcases s with a | a
    · simp [hs, hrow a]
    · simp [hs, hrow' a]

/-- Elements with a matrix factorization are closed under negation. -/
theorem HasMF_neg (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S) (g : S)
    (hg : HasMF R S f g) : HasMF R S f (-g) := by
  let := f.toAlgebra
  obtain ⟨n, X, y, z, U, V, hval, hcol, hrow⟩ := hg
  refine ⟨n, -X, y, z, -U, -V, ?_, ?_, ?_⟩
  · rw [hval]
    simp only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]
  · intro j
    rw [Pi.neg_apply, map_neg, hcol j]
    simp only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]
  · intro i
    rw [Pi.neg_apply, map_neg, hrow i]
    simp only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]

/-- If `f` satisfies the epi relation `a ⊗ 1 = 1 ⊗ a` for every `a : S`, then for every `g : S`
there is `c : R` such that `-g + f c` has a matrix factorization. -/
theorem epiRelation_hasMF_neg (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (g : S)
    (hepi : letI := f.toAlgebra; ∀ a : S, (a ⊗ₜ[R] (1 : S) : S ⊗[R] S) = (1 : S) ⊗ₜ[R] a) :
    ∃ c : R, HasMF R S f (-g + f c) := by
  classical
  let := f.toAlgebra
  have hsmul : ∀ (r : R) (s : S), r • s = f r * s := by
    intro r s; rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  by_cases hg1 : g = 1
  · refine ⟨1, ?_⟩
    have hval : -g + f 1 = f 0 := by rw [hg1, map_one, map_zero]; ring
    rw [hval]; exact HasMF_algebraMap R S f 0
  have hspan : Submodule.span R (Set.range (id : S → S)) = ⊤ := by
    rw [Set.range_id, Submodule.span_univ]
  set m : S →₀ S := Finsupp.single 1 g + Finsupp.single g (-1) with hm
  have hmn : (m.sum fun j mj => mj ⊗ₜ[R] (id j)) = 0 := by
    have key : (m.sum fun j mj => mj ⊗ₜ[R] (id j))
        = (Finsupp.single (1:S) g).sum (fun j mj => mj ⊗ₜ[R] (id j))
          + (Finsupp.single g (-1:S)).sum (fun j mj => mj ⊗ₜ[R] (id j)) := by
      apply Finsupp.sum_add_index' (h := fun j mj => mj ⊗ₜ[R] (id j))
      · intro j; simp
      · intro j mj1 mj2; rw [TensorProduct.add_tmul]
    rw [key, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    simp only [id]
    rw [hepi g, TensorProduct.neg_tmul]; abel
  obtain ⟨a, h1, h2⟩ := equationalCriterion_bilateral R (id : S → S) (id : S → S) hspan hspan m hmn
  set T : Finset S :=
    insert 1 (insert g (a.support ∪ a.support.biUnion (fun i => (a i).support))) with hT
  have h1mem : (1:S) ∈ T := by simp [hT]
  have hgmem : g ∈ T := by simp [hT]
  have hsuppa : a.support ⊆ T := by
    intro i hi; simp only [hT, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
    right; right; left; exact hi
  have hsuppai : ∀ i ∈ a.support, (a i).support ⊆ T := by
    intro i hi s hs
    simp only [hT, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
    right; right; right; exact ⟨i, hi, hs⟩
  have hzero : ∀ i s, s ∉ T → a i s = 0 := by
    intro i s hs
    by_cases hi : i ∈ a.support
    · exact Finsupp.notMem_support_iff.mp (fun hcon => hs (hsuppai i hi hcon))
    · have : a i = 0 := Finsupp.notMem_support_iff.mp hi
      rw [this]; rfl
  set K : Finset S := T.erase 1 with hK
  have hTeq : T = insert 1 K := by rw [hK, Finset.insert_erase h1mem]
  have h1notK : (1:S) ∉ K := Finset.notMem_erase 1 T
  have hgK : g ∈ K := Finset.mem_erase.mpr ⟨hg1, hgmem⟩
  have hmK : ∀ j ∈ K, m j = if g = j then (-1:S) else 0 := by
    intro j hj
    have hjne1 : j ≠ (1:S) := fun h => h1notK (h ▸ hj)
    rw [hm, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      ite_eq_right (fun h => hjne1 h.symm), zero_add]
  have lemA : ∀ s, (∑ i ∈ K, (a i s) • i) = m s - (a 1 s) • (1:S) := by
    intro s
    have hms : m s = ∑ i ∈ T, (a i s) • i := by
      rw [h1 s, Finsupp.sum_of_support_subset a hsuppa (fun i ai => (ai s) • (id i))
        (by intro i _; simp)]
      simp [id]
    rw [hTeq, Finset.sum_insert h1notK] at hms
    rw [hms]; ring
  have lemB : ∀ i₀, (∑ j ∈ K, (a i₀ j) • j) = -((a i₀ 1) • (1:S)) := by
    intro i₀
    have hsum0 : (∑ j ∈ T, (a i₀ j) • j) = 0 := by
      have hh := h2 i₀
      rw [Finsupp.linearCombination_apply] at hh
      simp only [id] at hh
      rw [Finsupp.sum_of_support_subset (a i₀) (s := T) ?_ (fun s r => r • s)
        (by intro s _; simp)] at hh
      · exact hh
      · intro s hs
        by_contra hc
        exact (Finsupp.mem_support_iff.mp hs) (hzero i₀ s hc)
    rw [hTeq, Finset.sum_insert h1notK] at hsum0
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum0
  have valeq : (∑ i ∈ K, ∑ j ∈ K, (a i j) • (i * j)) = -g + f (a 1 1) := by
    rw [Finset.sum_comm]
    have inner : ∀ j ∈ K, (∑ i ∈ K, (a i j) • (i * j)) = (m j - (a 1 j) • (1:S)) * j := by
      intro j _
      rw [← lemA j, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _; rw [hsmul, hsmul, mul_assoc]
    rw [Finset.sum_congr rfl inner]
    have hmj : ∀ j ∈ K, (m j - (a 1 j) • (1:S)) * j
        = (if g = j then (-1:S) else 0) * j - f (a 1 j) * j := by
      intro j hj
      rw [hmK j hj, hsmul, mul_one, sub_mul]
    rw [Finset.sum_congr rfl hmj, Finset.sum_sub_distrib]
    have hfirst : (∑ j ∈ K, (if g = j then (-1:S) else 0) * j) = -g := by
      rw [Finset.sum_eq_single g]
      · rw [ite_eq_left rfl]; ring
      · intro j _ hjne; rw [ite_eq_right (fun h => hjne h.symm)]; ring
      · intro h; exact absurd hgK h
    have hsecond : (∑ j ∈ K, f (a 1 j) * j) = -(f (a 1 1)) := by
      have := lemB 1
      rw [hsmul, mul_one] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro j _; rw [hsmul]
    rw [hfirst, hsecond]; ring
  set n := K.card with hn
  let e : Fin n ≃ ↥K := (K.equivFin).symm
  have hsum1 : ∀ (ψ : S → S), (∑ i : Fin n, ψ ((e i : ↥K) : S)) = ∑ i ∈ K, ψ i := fun ψ =>
    (Equiv.sum_comp e fun i : ↥K => ψ (i : S)).trans (Finset.sum_attach K fun i => ψ (i : S))
  refine ⟨a 1 1, n, fun i j => a (e i) (e j), fun i => ((e i : ↥K) : S),
    fun i => ((e i : ↥K) : S),
    fun j => (if ((e j : ↥K):S) = g then (-1:R) else 0) - a 1 ((e j : ↥K):S),
    fun i => -(a ((e i : ↥K):S) 1), ?_, ?_, ?_⟩
  · rw [← valeq]
    rw [hsum1 (fun s => ∑ j : Fin n, (a s (e j)) • (s * ((e j:↥K):S)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsum1 (fun s => (a i s) • (i * s))]
  · intro j
    rw [hsum1 (fun s => (a s (e j)) • s)]
    rw [lemA ((e j:↥K):S), hmK _ (e j).property, hsmul, mul_one, map_sub]
    congr 1
    by_cases hjg : ((e j:↥K):S) = g
    · rw [ite_eq_left hjg, ite_eq_left hjg.symm, map_neg, map_one]
    · rw [ite_eq_right hjg, ite_eq_right (fun h => hjg h.symm), map_zero]
  · intro i
    rw [hsum1 (fun s => (a (e i) s) • s)]
    rw [lemB ((e i:↥K):S), map_neg, hsmul, mul_one]

/-- For `g` satisfying the epimorphism relation `g ⊗ 1 = 1 ⊗ g`, there is a matrix factorization:
`n`, `X : Matrix (Fin n) (Fin n) R`, `y z : Fin n → S` and `U V : Fin n → R` (preimages under `f`
of the row `YX` and column `XZ`), such that

* `g = ∑ i, ∑ j, X i j • (y i * z j)`,
* `∀ j, f (U j) = ∑ i, X i j • y i`,
* `∀ i, f (V i) = ∑ j, X i j • z j`. -/
theorem exists_matrix_factorization (R S : Type u) [CommRing R] [CommRing S]
    (f : R →+* S)
    (g : S)
    (hepi : letI := f.toAlgebra; ∀ a : S, (a ⊗ₜ[R] (1 : S) : S ⊗[R] S) = (1 : S) ⊗ₜ[R] a) :
    letI := f.toAlgebra;
    ∃ (n : ℕ) (X : Matrix (Fin n) (Fin n) R) (y z : Fin n → S) (U V : Fin n → R),
      g = ∑ i, ∑ j, X i j • (y i * z j) ∧
      (∀ j, f (U j) = ∑ i, X i j • y i) ∧
      (∀ i, f (V i) = ∑ j, X i j • z j) := by
  let := f.toAlgebra
  obtain ⟨c, hc⟩ := epiRelation_hasMF_neg R S f g hepi
  have hsum : HasMF R S f (f c + -(-g + f c)) :=
    HasMF_add R S f (f c) (-(-g + f c)) (HasMF_algebraMap R S f c) (HasMF_neg R S f _ hc)
  rwa [show f c + -(-g + f c) = g by ring] at hsum

/-- A chosen associated triple of `g`: the data `(n, X, U, V)` of a matrix factorization of `g`
given by `exists_matrix_factorization`. -/
noncomputable def assocTriple (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (g : S) (hepi : letI := f.toAlgebra; ∀ a : S, (a ⊗ₜ[R] (1 : S) : S ⊗[R] S) = (1 : S) ⊗ₜ[R] a) :
    EpiTriple R :=
  letI := f.toAlgebra
  let h := exists_matrix_factorization R S f g hepi
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩

/-- The associated triple `assocTriple R S f g hg` is built from a matrix
factorization of `g`: there are factorization data `(n, X, y, z, U, V)` whose
bundled `(n, X, U, V)` is exactly `assocTriple R S f g hg`, and which satisfy the
three factorization identities. -/
theorem assocTriple_spec (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (g : S) (hepi : letI := f.toAlgebra; ∀ a : S, (a ⊗ₜ[R] (1 : S) : S ⊗[R] S) = (1 : S) ⊗ₜ[R] a) :
    letI := f.toAlgebra;
    ∃ (n : ℕ) (X : Matrix (Fin n) (Fin n) R) (y z : Fin n → S) (U V : Fin n → R),
      assocTriple R S f g hepi = ⟨n, X, U, V⟩ ∧
      g = ∑ i, ∑ j, X i j • (y i * z j) ∧
      (∀ j, f (U j) = ∑ i, X i j • y i) ∧
      (∀ i, f (V i) = ∑ j, X i j • z j) := by
  let := f.toAlgebra
  refine ⟨(exists_matrix_factorization R S f g hepi).choose,
    (exists_matrix_factorization R S f g hepi).choose_spec.choose,
    (exists_matrix_factorization R S f g hepi).choose_spec.choose_spec.choose,
    (exists_matrix_factorization R S f g hepi).choose_spec.choose_spec.choose_spec.choose,
    (exists_matrix_factorization R S f g
        hepi).choose_spec.choose_spec.choose_spec.choose_spec.choose,
    (exists_matrix_factorization R S f g
        hepi).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose,
    rfl, ?_⟩
  exact (exists_matrix_factorization R S f g
      hepi).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

/-- If `g` and `g'` (both satisfying the epi relation) have the same associated triple, then
`g = g'`. -/
theorem assocTriple_injective (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (g g' : S)
    (hepi : letI := f.toAlgebra; ∀ a : S, (a ⊗ₜ[R] (1 : S) : S ⊗[R] S) = (1 : S) ⊗ₜ[R] a)
    (h : assocTriple R S f g hepi = assocTriple R S f g' hepi) :
    g = g' := by
  let := f.toAlgebra
  obtain ⟨n, X, y, z, U, V, htriple, hgeq, hU, hV⟩ := assocTriple_spec R S f g hepi
  obtain ⟨n', X', y', z', U', V', htriple', hgeq', hU', hV'⟩ := assocTriple_spec R S f g' hepi
  rw [htriple, htriple'] at h
  have hnn : n = n' := congrArg Sigma.fst h
  subst hnn
  simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
  obtain ⟨hXeq, hUeq, hVeq⟩ := h
  subst hXeq; subst hUeq; subst hVeq
  have hcol : ∀ (y z : Fin n → S) j, ∑ i, X i j • (y i * z j) = (∑ i, X i j • y i) * z j := by
    intro y z j; simp only [Finset.sum_mul, smul_mul_assoc]
  have hrow : ∀ (y z : Fin n → S) i, ∑ j, X i j • (y i * z j) = y i * ∑ j, X i j • z j := by
    intro y z i; simp only [Finset.mul_sum, mul_smul_comm]
  have hgM : g = ∑ i, ∑ j, X i j • (y' i * z j) := by
    rw [hgeq, Finset.sum_comm, Finset.sum_comm (f := fun i j => X i j • (y' i * z j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcol, hcol, ← hU j, ← hU' j]
  have hg'M : g' = ∑ i, ∑ j, X i j • (y' i * z j) := by
    rw [hgeq']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow, hrow, ← hV i, ← hV' i]
  rw [hgM, hg'M]

/-- For infinite `R`, the type `EpiTriple R` of associated triples has cardinality at most
`|R|`. -/
theorem mk_epiTriple_le_of_infinite (R : Type u) [CommRing R] [Infinite R] :
    Cardinal.mk (EpiTriple R) ≤ Cardinal.mk R := by
  have hR : Cardinal.aleph0 ≤ Cardinal.mk R := Cardinal.aleph0_le_mk R
  have hsummand : ∀ n : ℕ,
      Cardinal.mk (Matrix (Fin n) (Fin n) R × (Fin n → R) × (Fin n → R)) ≤ Cardinal.mk R := by
    intro n
    have hmat : Cardinal.mk (Matrix (Fin n) (Fin n) R) = Cardinal.mk R ^ (n*n) := by
      rw [Matrix, Cardinal.mk_arrow, Cardinal.mk_arrow]
      simp [pow_mul]
    have harr : Cardinal.mk (Fin n → R) = Cardinal.mk R ^ n := by
      rw [Cardinal.mk_arrow]; simp
    rw [Cardinal.mk_prod, Cardinal.mk_prod, hmat, harr]
    simp only [Cardinal.lift_id]
    have h1 : Cardinal.mk R ^ (n*n) ≤ Cardinal.mk R := Cardinal.power_nat_le hR
    have h2 : Cardinal.mk R ^ n ≤ Cardinal.mk R := Cardinal.power_nat_le hR
    have hmul : Cardinal.mk R * Cardinal.mk R = Cardinal.mk R := Cardinal.mul_eq_self hR
    calc Cardinal.mk R ^ (n*n) * (Cardinal.mk R ^ n * Cardinal.mk R ^ n)
        ≤ Cardinal.mk R * (Cardinal.mk R * Cardinal.mk R) := by gcongr
      _ = Cardinal.mk R := by rw [hmul, hmul]
  unfold EpiTriple
  rw [Cardinal.mk_sigma]
  calc (Cardinal.sum fun n => Cardinal.mk (Matrix (Fin n) (Fin n) R × (Fin n → R) × (Fin n → R)))
      ≤ Cardinal.sum (fun _ : ℕ => Cardinal.mk R) := Cardinal.sum_le_sum _ _ hsummand
    _ = Cardinal.aleph0 * Cardinal.mk R := by
        rw [Cardinal.sum_const]; simp
    _ = Cardinal.mk R := Cardinal.aleph0_mul_eq hR

/-- Nakayama's lemma for a nilpotent ideal: if `I` is a nilpotent ideal and `N` a submodule
with `⊤ = N ⊔ I • ⊤`, then `N = ⊤`. -/
@[ega "0 7.1.13" "special case",
  sga "3 III 4.6.4" "more general",
  sga "3 VIB 6.2.2" "cokernel vanishing",
  sga "3 VIII 6.2" "nilpotent Nakayama step"]
theorem fg_top_of_sup_smul_top {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (N : Submodule R M)
    (hsup : (⊤ : Submodule R M) = N ⊔ I • ⊤) : N = ⊤ := by
  obtain ⟨c, hc⟩ := hI
  have key : ∀ k, (⊤ : Submodule R M) = N ⊔ (I^k) • (⊤ : Submodule R M) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : I^n • (⊤ : Submodule R M) ≤ N ⊔ (I^(n+1)) • (⊤ : Submodule R M) := by
        have : I^n • (⊤ : Submodule R M) = I^n • (N ⊔ I • ⊤) := by rw [← hsup]
        rw [this, Submodule.smul_sup]
        apply sup_le
        · exact le_sup_of_le_left Submodule.smul_le_right
        · have heq : I^n • (I • (⊤ : Submodule R M)) = I^(n+1) • (⊤ : Submodule R M) := by
            rw [pow_succ, mul_smul]
          rw [heq]; exact le_sup_right
      refine le_antisymm ?_ le_top
      calc (⊤ : Submodule R M) = N ⊔ (I^n) • (⊤ : Submodule R M) := ih
        _ ≤ N ⊔ (I^(n+1)) • (⊤ : Submodule R M) := sup_le le_sup_left hstep
  have := key c
  rw [hc] at this
  simp at this
  exact this.symm

/-- A `k`-linear functional separating `1` from an element outside the image of
`algebraMap k A`: if no `c : k` satisfies `algebraMap k A c = t`, there is `φ : A →ₗ[k] k`
with `φ 1 = 0` and `φ t = 1`. -/
theorem exists_linearMap_one_eq_zero_of_forall_algebraMap_ne (k A : Type u) [Field k]
    [CommRing A] [Algebra k A] [Nontrivial A] {t : A} (ht : ∀ c : k, algebraMap k A c ≠ t) :
    ∃ φ : A →ₗ[k] k, φ 1 = 0 ∧ φ t = 1 := by
  have hnm : t ∉ Submodule.span k {(1 : A)} := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    exact ht c (by rwa [Algebra.algebraMap_eq_smul_one])
  obtain ⟨φ, hφ, hφt⟩ :=
    LinearMap.exists_extend_of_notMem (0 : Submodule.span k {(1 : A)} →ₗ[k] k) hnm 1
  exact ⟨φ, by simpa using DFunLike.congr_fun hφ ⟨1, Submodule.mem_span_singleton_self _⟩, hφt⟩

/-- The epi relation `a ⊗ 1 = 1 ⊗ a` for a `k`-algebra `A` over a field `k` forces
`algebraMap k A` to be surjective. -/
private theorem surjective_algebraMap_of_tmul_eq (k A : Type u) [Field k] [CommRing A]
    [Algebra k A]
    (hepi : ∀ a : A, (a ⊗ₜ[k] (1 : A) : A ⊗[k] A) = (1 : A) ⊗ₜ[k] a) :
    Function.Surjective (algebraMap k A) := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · exact fun a => ⟨0, Subsingleton.elim _ _⟩
  · by_contra hns
    obtain ⟨t, ht⟩ : ∃ t : A, ∀ c : k, algebraMap k A c ≠ t := by
      by_contra h; push Not at h; exact hns h
    obtain ⟨φ, hφ1, hφt⟩ := exists_linearMap_one_eq_zero_of_forall_algebraMap_ne k A ht
    have happ := congrArg (TensorProduct.lift ((LinearMap.lsmul k A).comp φ)) (hepi t)
    simp only [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply, hφ1, hφt,
      one_smul, zero_smul] at happ
    exact one_ne_zero happ

/-- An epimorphism of fields `k → A` (here `A` is a `k`-algebra that is a field, with the epi
relation `a ⊗ 1 = 1 ⊗ a`) is surjective. -/
@[ega "0 21.1.6.1" "special case"]
theorem isEpi_field_surjective (k A : Type u) [Field k] [Field A] [Algebra k A]
    (hepi : ∀ a : A, (a ⊗ₜ[k] (1 : A) : A ⊗[k] A) = (1 : A) ⊗ₜ[k] a) :
    Function.Surjective (algebraMap k A) :=
  surjective_algebraMap_of_tmul_eq k A hepi

/-! ### The finite case: residues modulo the Jacobson radical

Let `f : R → S` be a ring epimorphism with `R` finite, and write `J = (⊥ : Ideal R).jacobson`
for the Jacobson radical of `R`. The induced map `R → S / (J • S)` is surjective
(`epi_residue_surjective`), so `S / (J • S)` is a finitely generated `R`-module
(`epi_quotient_jacobson_fg`), and since `J` is nilpotent `S` is a finite `R`-module
(`epi_module_finite_of_finite`).
-/

/-- A ring epimorphism `g : k → A` out of a field `k`, with `A` an arbitrary commutative ring,
is surjective. -/
@[sga "3 VIIB 1.3" "special case"]
theorem isEpi_field_surjective' (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (hepi : ∀ a : A, (a ⊗ₜ[k] (1 : A) : A ⊗[k] A) = (1 : A) ⊗ₜ[k] a) :
    Function.Surjective (algebraMap k A) :=
  surjective_algebraMap_of_tmul_eq k A hepi

/-- If `g : A → B` is a ring epimorphism and `I ≤ A` an ideal, then the induced map
`A ⧸ I → B ⧸ (I.map g)` is a ring epimorphism. -/
theorem epi_quotient_baseChange (A B : Type u) [CommRing A] [CommRing B] (g : A →+* B)
    (hg : Epi (CommRingCat.ofHom g)) (I : Ideal A) :
    Epi (CommRingCat.ofHom (Ideal.quotientMap (I.map g) g Ideal.le_comap_map)) := by
  have hqB : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (I.map g))) :=
    ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  have hsq : (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      (CommRingCat.ofHom (Ideal.quotientMap (I.map g) g Ideal.le_comap_map)) =
      (CommRingCat.ofHom g) ≫ (CommRingCat.ofHom (Ideal.Quotient.mk (I.map g))) := by
    ext a
    simp [Ideal.quotientMap_mk]
  exact epi_of_epi_fac hsq

/-- A ring epimorphism `g : ∏ k_i → C` out of a finite product of fields is surjective. -/
theorem epi_product_field_surjective (ι : Type u) [Finite ι]
    (k : ι → Type u) [∀ i, Field (k i)] (C : Type u) [CommRing C]
    (g : (∀ i, k i) →+* C) (hg : Epi (CommRingCat.ofHom g)) :
    Function.Surjective g := by
  classical
  have := Fintype.ofFinite ι
  set ε : ι → C := fun i => g (Pi.single i 1) with hε
  have hεcoi : CompleteOrthogonalIdempotents ε :=
    (CompleteOrthogonalIdempotents.single k).map g
  set φ : C →+* (∀ i, C ⧸ Ideal.span {1 - ε i}) :=
    RingHom.pi (fun i => Ideal.Quotient.mk (Ideal.span {1 - ε i})) with hφ
  have hφbij : Function.Bijective φ := hεcoi.bijective_pi
  have hsec : ∀ i, Function.RightInverse (Pi.single i) (Pi.evalRingHom k i) := by
    intro i x; simp
  have hker : ∀ i, RingHom.ker (Pi.evalRingHom k i) ≤
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {1 - ε i})).comp g) := by
    intro i y hy
    rw [RingHom.mem_ker] at hy ⊢
    simp only [Pi.evalRingHom_apply] at hy
    have hey : (Pi.single i 1 : ∀ j, k j) * y = 0 := by
      ext j; by_cases hj : j = i
      · subst hj; simp [hy]
      · simp [Pi.single_eq_of_ne hj]
    have hy2 : y = (1 - Pi.single i 1) * y := by
      have h0 : y - (Pi.single i 1) * y = (1 - Pi.single i 1) * y := by ring
      rw [← h0, hey, sub_zero]
    have hgy : g y = (1 - g (Pi.single i 1)) * g y := by
      conv_lhs => rw [hy2]; rw [map_mul, map_sub, map_one]
    rw [RingHom.comp_apply, hgy, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  set gi : ∀ i, k i →+* (C ⧸ Ideal.span {1 - ε i}) := fun i =>
    (Pi.evalRingHom k i).liftOfRightInverse (Pi.single i) (hsec i)
      ⟨(Ideal.Quotient.mk (Ideal.span {1 - ε i})).comp g, hker i⟩ with hgi
  have hgi_comp : ∀ i (y : ∀ j, k j),
      gi i (y i) = (Ideal.Quotient.mk (Ideal.span {1 - ε i})) (g y) := by
    intro i y
    have := RingHom.liftOfRightInverse_comp_apply (Pi.evalRingHom k i) (Pi.single i) (hsec i)
      ⟨(Ideal.Quotient.mk (Ideal.span {1 - ε i})).comp g, hker i⟩ y
    simpa [hgi] using this
  have hgi_epi : ∀ i, Epi (CommRingCat.ofHom (gi i)) := by
    intro i
    have hsq : (CommRingCat.ofHom (Pi.evalRingHom k i)) ≫ (CommRingCat.ofHom (gi i))
        = (CommRingCat.ofHom g) ≫
          (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - ε i}))) :=
      CommRingCat.hom_ext (RingHom.ext (hgi_comp i))
    have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - ε i}))) :=
      ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
    exact epi_of_epi_fac hsq
  have hgi_surj : ∀ i, Function.Surjective (gi i) := by
    intro i
    let : Algebra (k i) (C ⧸ Ideal.span {1 - ε i}) := (gi i).toAlgebra
    have htmul := (epi_iff_tmul (k i) (C ⧸ Ideal.span {1 - ε i}) (gi i)).mp (hgi_epi i)
    have hsurj := isEpi_field_surjective' (k i) (C ⧸ Ideal.span {1 - ε i}) htmul
    intro c
    obtain ⟨x, hx⟩ := hsurj c
    exact ⟨x, by rw [← hx]; rfl⟩
  intro c
  choose a ha using fun i => hgi_surj i ((Ideal.Quotient.mk (Ideal.span {1 - ε i})) c)
  refine ⟨a, hφbij.left ?_⟩
  ext i
  show φ (g a) i = φ c i
  simp only [hφ, RingHom.pi_apply]
  rw [← hgi_comp i a, ha i]

/-- If `B` is a finite reduced commutative ring and `g : B → C` is a ring epimorphism, then `g`
is surjective. -/
theorem epi_finite_reduced_surjective (B C : Type u) [CommRing B] [CommRing C]
    [Finite B] [IsReduced B] (g : B →+* C) (hg : Epi (CommRingCat.ofHom g)) :
    Function.Surjective g := by
  classical
  have : IsArtinianRing B := inferInstance
  have : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let hF : ∀ I : MaximalSpectrum B, Field (B ⧸ I.asIdeal) := fun I => by
    have : I.asIdeal.IsMaximal := I.isMaximal; exact Ideal.Quotient.field _
  set e := IsArtinianRing.equivPi B with he
  have key : Function.Surjective (⇑(g.comp e.symm.toRingHom)) := by
    refine epi_product_field_surjective (MaximalSpectrum B) (fun I => B ⧸ I.asIdeal) C
      (g.comp e.symm.toRingHom) ?_
    have hsymm : Epi (CommRingCat.ofHom (e.symm.toRingHom)) :=
      ConcreteCategory.epi_of_surjective _ e.symm.surjective
    rw [CommRingCat.ofHom_comp]
    infer_instance
  intro c
  obtain ⟨y, hy⟩ := key c
  exact ⟨e.symm y, hy⟩

/-- For a ring epimorphism `f : R → S` with `R` finite and `J = (⊥ : Ideal R).jacobson`, the
induced map `R → S / (J • S)` is surjective: every `s : S` differs from some `f r` by an
element of `J • ⊤`. -/
theorem epi_residue_surjective (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) [Finite R] :
    letI := f.toAlgebra
    ∀ s : S, ∃ r : R, s - f r ∈ ((⊥ : Ideal R).jacobson) • (⊤ : Submodule R S) := by
  let := f.toAlgebra
  set J : Ideal R := (⊥ : Ideal R).jacobson with hJ
  have : Finite (R ⧸ J) := Quotient.finite _
  have : IsReduced (R ⧸ J) := by
    have : IsArtinianRing R := inferInstance
    rw [hJ, ← Ideal.isRadical_iff_quotient_reduced, IsArtinianRing.jacobson_eq_radical]
    exact Ideal.radical_isRadical _
  have hβepi : Epi (CommRingCat.ofHom (Ideal.quotientMap (J.map f) f Ideal.le_comap_map)) :=
    epi_quotient_baseChange R S f hf J
  have hβsurj : Function.Surjective (Ideal.quotientMap (J.map f) f Ideal.le_comap_map) :=
    epi_finite_reduced_surjective (R ⧸ J) (S ⧸ J.map f) _ hβepi
  intro s
  obtain ⟨b, hb⟩ := hβsurj (Ideal.Quotient.mk (J.map f) s)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨r, ?_⟩
  have hqm : Ideal.quotientMap (J.map f) f Ideal.le_comap_map (Ideal.Quotient.mk J r)
      = Ideal.Quotient.mk (J.map f) (f r) := Ideal.quotientMap_mk
  rw [hqm] at hb
  have hmem : s - f r ∈ J.map f := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hb, sub_self]
  rw [Ideal.smul_top_eq_map]
  exact hmem

/-- For a ring epimorphism `f : R → S` with `R` finite, the quotient `S / (J • S)` by the
Jacobson radical `J = (⊥ : Ideal R).jacobson` of `R` is a finitely generated `R`-module:
there is a finitely generated `N ≤ S` with `⊤ = N ⊔ J • ⊤`. -/
theorem epi_quotient_jacobson_fg (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) [Finite R] :
    letI := f.toAlgebra
    ∃ N : Submodule R S, N.FG ∧
      (⊤ : Submodule R S) = N ⊔ ((⊥ : Ideal R).jacobson) • ⊤ := by
  let := f.toAlgebra
  set J : Ideal R := (⊥ : Ideal R).jacobson with hJ
  have hsurj := epi_residue_surjective R S f hf
  refine ⟨Submodule.span R {(1 : S)}, Submodule.fg_span_singleton _, ?_⟩
  refine le_antisymm ?_ le_top
  intro s _
  obtain ⟨r, hr⟩ := hsurj s
  have h1 : f r ∈ Submodule.span R {(1 : S)} := by
    have he : (f r : S) = r • (1 : S) := by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]
    rw [he]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  simpa using Submodule.add_mem_sup h1 hr

/-- If `R` is finite and `f : R → S` is a ring epimorphism, then `S` is module-finite over `R`
(via the algebra structure induced by `f`). -/
theorem epi_module_finite_of_finite (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) [Finite R] :
    letI := f.toAlgebra; Module.Finite R S := by
  let := f.toAlgebra
  have : IsArtinianRing R := inferInstance
  obtain ⟨N, hNfg, hNsup⟩ := epi_quotient_jacobson_fg R S f hf
  rw [Module.finite_def, ← fg_top_of_sup_smul_top _ IsArtinianRing.isNilpotent_jacobson_bot N hNsup]
  exact hNfg

/-- If `f : R → S` is an epimorphism of rings and `R` is finite, then `|S| ≤ |R|`. -/
theorem epi_card_le_of_finite (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) [Finite R] :
    Cardinal.mk S ≤ Cardinal.mk R := by
  let := f.toAlgebra
  have hfin : Module.Finite R S := epi_module_finite_of_finite R S f hf
  have hRfin : (CommRingCat.Hom.hom (CommRingCat.ofHom f)).Finite := by
    simp only [CommRingCat.hom_ofHom]
    exact hfin
  have hsurj : Function.Surjective ⇑f := by
    have := RingHom.surjective_of_epi_of_finite (CommRingCat.ofHom f) (by simpa using hRfin)
    simpa using this
  exact Cardinal.mk_le_of_surjective hsurj

/-- If `f : R → S` is an epimorphism of commutative rings, then `|S| ≤ |R|`. -/
@[stacks 04W0]
theorem epi_card_le (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Cardinal.mk S ≤ Cardinal.mk R := by
  let := f.toAlgebra
  have htmul : ∀ g : S, (g ⊗ₜ[R] (1 : S) : S ⊗[R] S) = (1 : S) ⊗ₜ[R] g :=
    (epi_iff_tmul R S f).mp hf
  rcases finite_or_infinite R with hR | hR
  · exact epi_card_le_of_finite R S f hf
  · calc Cardinal.mk S ≤ Cardinal.mk (EpiTriple R) :=
          Cardinal.mk_le_of_injective (f := fun g : S => assocTriple R S f g htmul)
            fun g g' h => assocTriple_injective R S f g g' htmul h
      _ ≤ Cardinal.mk R := mk_epiTriple_le_of_infinite R

/-!
### The equational criterion for `g ⊗ 1 = 1 ⊗ g`

Let `φ : R → S` be a homomorphism of commutative rings, rendered by an `Algebra R S`
instance with `φ = algebraMap R S`, and let `g : S`. The `R`-action on `S` used in the tensor
product `S ⊗[R] S` is the one induced by `φ`.

`tmul_one_eq_one_tmul_iff`: for `g : S` the following are equivalent.

1. `g ⊗ 1 = 1 ⊗ g` in `S ⊗[R] S`;
2. there are an `n : ℕ`, elements `yᵢ, zⱼ : S` and scalars `xᵢⱼ : R` for `i, j : Fin n` with
   * `g = ∑ i, ∑ j, φ (xᵢⱼ) * yᵢ * zⱼ`,
   * `∑ i, φ (xᵢⱼ) * yᵢ ∈ φ(R)` for every `j`,
   * `∑ j, φ (xᵢⱼ) * zⱼ ∈ φ(R)` for every `i`.

The two directions are `tmul_one_eq_one_tmul_of_sum_repr` and
`exists_sum_repr_of_tmul_one_eq_one_tmul`.
-/

@[expose] public section

open TensorProduct in
/-- If `g = ∑ i, ∑ j, φ (xᵢⱼ) * yᵢ * zⱼ` with every column sum `∑ i, φ (xᵢⱼ) * yᵢ` and every
row sum `∑ j, φ (xᵢⱼ) * zⱼ` in the image of `φ`, then `g ⊗ 1 = 1 ⊗ g` in `S ⊗[R] S`. -/
theorem tmul_one_eq_one_tmul_of_sum_repr (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (g :
  S)
    (h : ∃ (n : ℕ) (y z : Fin n → S) (x : Fin n → Fin n → R),
      g = ∑ i, ∑ j, (algebraMap R S (x i j)) * y i * z j ∧
      (∀ j, ∃ r : R, ∑ i, (algebraMap R S (x i j)) * y i = algebraMap R S r) ∧
      (∀ i, ∃ r : R, ∑ j, (algebraMap R S (x i j)) * z j = algebraMap R S r)) :
    g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g := by
  obtain ⟨n, y, z, x, hgeq, hb, hc⟩ := h
  set T : S ⊗[R] S := ∑ i, ∑ j, (x i j) • (y i ⊗ₜ[R] z j) with hT
  choose r hr using hb
  choose s hs using hc
  have h1T : (1 : S) ⊗ₜ[R] g = T := by
    rw [hT]
    have e1 : ∀ i j, (x i j) • (y i ⊗ₜ[R] z j)
        = (algebraMap R S (x i j) * y i) ⊗ₜ[R] z j := by
      intro i j
      rw [smul_tmul', Algebra.smul_def]
    simp only [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ j, (∑ i, (algebraMap R S (x i j) * y i) ⊗ₜ[R] z j)
        = (∑ i, algebraMap R S (x i j) * y i) ⊗ₜ[R] z j := by
      intro j; rw [sum_tmul]
    simp only [e2]
    simp only [hr]
    have e3 : ∀ j, (algebraMap R S (r j)) ⊗ₜ[R] z j
        = (1 : S) ⊗ₜ[R] (algebraMap R S (r j) * z j) := by
      intro j
      have h : (algebraMap R S (r j)) ⊗ₜ[R] z j = (r j • (1:S)) ⊗ₜ[R] z j := by
        rw [Algebra.smul_def, mul_one]
      rw [h, smul_tmul, Algebra.smul_def]
    simp only [e3]
    rw [← tmul_sum]
    congr 1
    rw [hgeq, Finset.sum_comm]
    congr 1; ext j
    rw [← hr j, Finset.sum_mul]
  have hgT : g ⊗ₜ[R] (1 : S) = T := by
    rw [hT]
    have e1 : ∀ i j, (x i j) • (y i ⊗ₜ[R] z j)
        = (y i) ⊗ₜ[R] (algebraMap R S (x i j) * z j) := by
      intro i j
      rw [← tmul_smul, Algebra.smul_def]
    simp only [e1]
    have e2 : ∀ i, (∑ j, (y i) ⊗ₜ[R] (algebraMap R S (x i j) * z j))
        = (y i) ⊗ₜ[R] (∑ j, algebraMap R S (x i j) * z j) := by
      intro i; rw [tmul_sum]
    simp only [e2]
    simp only [hs]
    have e3 : ∀ i, (y i) ⊗ₜ[R] (algebraMap R S (s i))
        = (algebraMap R S (s i) * y i) ⊗ₜ[R] (1 : S) := by
      intro i
      have h : (y i) ⊗ₜ[R] (algebraMap R S (s i)) = (y i) ⊗ₜ[R] (s i • (1:S)) := by
        rw [Algebra.smul_def, mul_one]
      rw [h, tmul_smul, smul_tmul', Algebra.smul_def]
    simp only [e3]
    rw [← sum_tmul]
    congr 1
    rw [hgeq]
    congr 1; ext i
    rw [← hs i, Finset.sum_mul]
    congr 1; ext j
    ring
  rw [hgT, h1T]

/-! ### The substantive direction

Assume `g ⊗ 1 = 1 ⊗ g`. For a finite set `D` of elements of `S` containing `1` and a coefficient
matrix `c` over `D`, the relation yields

* a coordinate relation `(if d = 1 then g else 0) - (if d = g then 1 else 0) = ∑ d' ∈ D,
  c d d' • d'`,
* a column relation `∑ d ∈ D.erase 1, c d d' • d = φ (- c 1 d')`,
* a row relation `∑ d' ∈ D.erase 1, c d d' • d' = φ (- [d = g] - c d 1)`,

from which `exists_matrix_factorization_of_coordRelations` produces the witnesses of
condition (2).
-/

open TensorProduct Classical in
/-- Given the finite square relation data of the Altman–Kleiman criterion — a finite set `D`
of generators with `1 ∈ D`, a coefficient matrix `c`, and the coordinate, column and row
relations — assemble the explicit witnesses `(n, y, z, x)` realising `g` as in condition (2)
of `tmul_one_eq_one_tmul_iff`. -/
theorem exists_matrix_factorization_of_coordRelations (R S : Type*) [CommRing R] [CommRing S]
  [Algebra R S] (g : S)
    (D : Finset S) (c : S → S → R) (h1D : (1 : S) ∈ D)
    (Coord' : ∀ d : S, (if d = 1 then g else 0) - (if d = g then (1:S) else 0)
       = ∑ d' ∈ D, (c d d') • d')
    (col : ∀ d' : S, ∑ d ∈ D.erase 1, (c d d') • d = (algebraMap R S (- c 1 d')))
    (row : ∀ d ∈ D.erase 1, ∑ d' ∈ D.erase 1, (c d d') • d'
      = algebraMap R S (- (if d = g then (1:R) else 0) - c d 1)) :
    (∃ (n : ℕ) (y z : Fin n → S) (x : Fin n → Fin n → R),
      g = ∑ i, ∑ j, (algebraMap R S (x i j)) * y i * z j ∧
      (∀ j, ∃ r : R, ∑ i, (algebraMap R S (x i j)) * y i = algebraMap R S r) ∧
      (∀ i, ∃ r : R, ∑ j, (algebraMap R S (x i j)) * z j = algebraMap R S r)) := by
  set E := D.erase 1 with hE
  set Ω := Option {d : S // d ∈ E} with hΩ
  let Y : Ω → S := fun o => match o with | none => 1 | some d => d.val
  let rr : R := (if (1:S) = g then (1:R) else 0) + c 1 1
  let X : Ω → Ω → R := fun o o' => match o, o' with
    | none, none => rr | some d, some d' => - c d.val d'.val | _, _ => 0
  let colval : Ω → R := fun o' => match o' with | none => rr | some d' => c 1 d'.val
  let rowval : Ω → R := fun o => match o with
    | none => rr | some d => (if d.val = g then (1:R) else 0) + c d.val 1
  have hneg : ∀ w : S → R, ∑ d ∈ E, algebraMap R S (- w d) * d = -∑ d ∈ E, w d • d := by
    intro w
    simp only [map_neg, neg_mul, Algebra.smul_def, Finset.sum_neg_distrib]
  have colEq : ∀ o', ∑ o, (algebraMap R S (X o o')) * Y o = algebraMap R S (colval o') := by
    intro o'; cases o' with
    | none =>
      rw [Fintype.sum_option]; simp only [X, Y, colval]
      rw [Finset.sum_eq_zero (by intro d _; simp [])]; simp
    | some d' =>
      rw [Fintype.sum_option]; simp only [X, Y, colval]
      rw [show (algebraMap R S 0) * 1 = 0 by simp, zero_add, Finset.sum_coe_sort E
        (fun d => algebraMap R S (- c d d'.val) * d)]
      rw [hneg fun d => c d d'.val, col d'.val, map_neg, neg_neg]
  have rowEq : ∀ o, ∑ o', (algebraMap R S (X o o')) * Y o' = algebraMap R S (rowval o) := by
    intro o; cases o with
    | none =>
      rw [Fintype.sum_option]; simp only [X, Y, rowval]
      rw [Finset.sum_eq_zero (by intro d _; simp [])]; simp
    | some d =>
      rw [Fintype.sum_option]; simp only [X, Y, rowval]
      rw [show (algebraMap R S 0) * 1 = 0 by simp, zero_add, Finset.sum_coe_sort E
        (fun d' => algebraMap R S (- c d.val d') * d')]
      rw [hneg (c d.val), row d.val d.property, map_sub, map_neg, map_add]; ring
  have hOmega : g = ∑ o : Ω, ∑ o' : Ω, (algebraMap R S (X o o')) * Y o * Y o' := by
    rw [Finset.sum_comm]
    have step : ∀ o' : Ω, ∑ o : Ω, (algebraMap R S (X o o')) * Y o * Y o'
        = Y o' * algebraMap R S (colval o') := by
      intro o'; rw [← colEq o', Finset.mul_sum]
      apply Finset.sum_congr rfl; intro o _; ring
    simp_rw [step]
    rw [Fintype.sum_option]
    simp only [Y, colval]
    rw [Finset.sum_coe_sort E (fun d' => d' * algebraMap R S (c 1 d'))]
    have hcoe : ∑ d' ∈ E, d' * algebraMap R S (c 1 d') = ∑ d' ∈ E, (c 1 d') • d' := by
      apply Finset.sum_congr rfl; intro d' _; rw [Algebra.smul_def]; ring
    rw [hcoe, show E = D.erase 1 from rfl, Finset.sum_erase_eq_sub h1D, ← Coord' 1,
      Algebra.smul_def, one_mul]
    simp only [rr, map_add]
    split_ifs with h1g <;> push_cast <;> simp
  set e := Fintype.equivFin Ω with he
  refine ⟨Fintype.card Ω, fun i => Y (e.symm i), fun i => Y (e.symm i),
    fun i j => X (e.symm i) (e.symm j), ?_, ?_, ?_⟩
  · change g = ∑ i, ∑ j, (algebraMap R S (X (e.symm i) (e.symm j))) * Y (e.symm i) * Y (e.symm j)
    rw [hOmega, Fintype.sum_equiv e.symm
      (fun i => ∑ j, algebraMap R S (X (e.symm i) (e.symm j)) * Y (e.symm i) * Y (e.symm j))
      (fun o => ∑ o', algebraMap R S (X o o') * Y o * Y o')
      (fun i => Fintype.sum_equiv e.symm _
        (fun o' => algebraMap R S (X (e.symm i) o') * Y (e.symm i) * Y o') (fun j => rfl))]
  · intro j
    refine ⟨colval (e.symm j), ?_⟩
    change ∑ i, algebraMap R S (X (e.symm i) (e.symm j)) * Y (e.symm i) = _
    rw [Fintype.sum_equiv e.symm _ (fun o => algebraMap R S (X o (e.symm j)) * Y o) (fun i => rfl)]
    exact colEq _
  · intro i
    refine ⟨rowval (e.symm i), ?_⟩
    change ∑ j, algebraMap R S (X (e.symm i) (e.symm j)) * Y (e.symm j) = _
    rw [Fintype.sum_equiv e.symm _ (fun o' => algebraMap R S (X (e.symm i) o') * Y o')
      (fun i => rfl)]
    exact rowEq _

open TensorProduct Classical in
/-- If `g ⊗ 1 = 1 ⊗ g` in `S ⊗[R] S`, then `g = ∑ i, ∑ j, φ (xᵢⱼ) * yᵢ * zⱼ` for some
`yᵢ, zⱼ : S` and `xᵢⱼ : R` whose column sums `∑ i, φ (xᵢⱼ) * yᵢ` and row sums
`∑ j, φ (xᵢⱼ) * zⱼ` all lie in the image of `φ`. -/
theorem exists_sum_repr_of_tmul_one_eq_one_tmul (R S : Type*) [CommRing R] [CommRing S] [Algebra R
  S] (g : S)
    (h : g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g) :
    (∃ (n : ℕ) (y z : Fin n → S) (x : Fin n → Fin n → R),
      g = ∑ i, ∑ j, (algebraMap R S (x i j)) * y i * z j ∧
      (∀ j, ∃ r : R, ∑ i, (algebraMap R S (x i j)) * y i = algebraMap R S r) ∧
      (∀ i, ∃ r : R, ∑ j, (algebraMap R S (x i j)) * z j = algebraMap R S r)) := by
  let F := S →₀ R
  let π : F →ₗ[R] S := Finsupp.linearCombination R (id : S → S)
  have hπ : Function.Surjective π := Finsupp.linearCombination_id_surjective R S
  have hπs : ∀ s : S, π (Finsupp.single s 1) = s := by
    intro s; rw [Finsupp.linearCombination_single]; simp
  have hex2 := rTensor_exact (M := ↥(LinearMap.ker π)) (N := F) (P := S)
    (f := (LinearMap.ker π).subtype) (g := π) S (LinearMap.exact_subtype_ker_map π) hπ
  let e0 : F ⊗[R] S := (Finsupp.single (1:S) 1) ⊗ₜ[R] g - (Finsupp.single g 1) ⊗ₜ[R] (1:S)
  have he : LinearMap.rTensor S π e0 = 0 := by
    simp only [e0, map_sub, LinearMap.rTensor_tmul, hπs]; rw [← h]; ring
  obtain ⟨q, hq⟩ := (hex2 e0).mp he
  obtain ⟨Tfs, hTfs⟩ := TensorProduct.exists_finset q
  have hΦe : (TensorProduct.finsuppScalarLeft R S S) e0
      = Finsupp.single (1:S) g - Finsupp.single g (1:S) := by
    rw [show e0 = (Finsupp.single (1:S) 1) ⊗ₜ[R] g - (Finsupp.single g 1) ⊗ₜ[R] (1:S) from rfl,
      map_sub, TensorProduct.finsuppScalarLeft_apply_tmul,
      TensorProduct.finsuppScalarLeft_apply_tmul]
    simp [Finsupp.sum_single_index]
  have hrel : Finsupp.single (1:S) g - Finsupp.single g (1:S)
      = ∑ p ∈ Tfs, TensorProduct.finsuppScalarLeft R S S ((↑p.fst : F) ⊗ₜ[R] p.snd) := by
    rw [← hΦe, ← hq, hTfs, map_sum, map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [LinearMap.rTensor_tmul]; rfl
  have hk : ∀ p ∈ Tfs, π (↑p.fst : F) = 0 := fun p _ => p.fst.property
  set D : Finset S :=
    insert 1 (insert g (Tfs.biUnion (fun p => insert p.snd (↑p.fst : F).support)))
    with hD
  have h1D : (1:S) ∈ D := by rw [hD]; exact Finset.mem_insert_self _ _
  have hD2 : ∀ p ∈ Tfs, p.snd ∈ D := by
    intro p hp; rw [hD]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_insert_self _ _⟩
  have hDsupp : ∀ p ∈ Tfs, (↑p.fst : F).support ⊆ D := by
    intro p hp s hs; rw [hD]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_insert_of_mem hs⟩
  have Coord : ∀ s : S, (if s = 1 then g else 0) - (if s = g then (1:S) else 0)
      = ∑ p ∈ Tfs, ((↑p.fst : F) s) • p.snd := by
    intro s
    have key := congrArg (fun (f : S →₀ S) => f s) hrel
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply, Finsupp.finsetSum_apply,
      TensorProduct.finsuppScalarLeft_apply_tmul_apply] at key
    rw [show (s = 1) = (1 = s) from propext eq_comm, show (s = g) = (g = s) from propext eq_comm,
        key]
  have Ker : ∀ p ∈ Tfs, ∑ s ∈ D, ((↑p.fst : F) s) • s = 0 := by
    intro p hp
    rw [← hk p hp, Finsupp.linearCombination_apply, Finsupp.sum,
      ← Finset.sum_subset (hDsupp p hp)
        (fun x _ hx => by rw [Finsupp.notMem_support_iff.mp hx, zero_smul])]
    rfl
  set c : S → S → R :=
    fun d d' => ∑ p ∈ Tfs.filter (fun p => p.snd = d'), (↑p.fst : F) d with hc
  have Coord' : ∀ d : S, (if d = 1 then g else 0) - (if d = g then (1:S) else 0)
      = ∑ d' ∈ D, (c d d') • d' := by
    intro d
    rw [Coord d, ← Finset.sum_fiberwise_of_maps_to hD2 (fun p => ((↑p.fst : F) d) • p.snd)]
    apply Finset.sum_congr rfl
    intro d' hd'
    rw [hc]; dsimp only; rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).right]
  have Ker' : ∀ d' : S, ∑ d ∈ D, (c d d') • d = 0 := by
    intro d'
    rw [hc]; dsimp only
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun p hp => Ker p (Finset.mem_filter.mp hp).left
  have col : ∀ d' : S, ∑ d ∈ D.erase 1, (c d d') • d = (algebraMap R S (- c 1 d')) := by
    intro d'
    rw [Finset.sum_erase_eq_sub h1D, Ker' d']
    simp [Algebra.smul_def]
  have row : ∀ d ∈ D.erase 1, ∑ d' ∈ D.erase 1, (c d d') • d'
      = algebraMap R S (- (if d = g then (1:R) else 0) - c d 1) := by
    intro d hd
    have hne : d ≠ 1 := (Finset.mem_erase.mp hd).left
    rw [Finset.sum_erase_eq_sub h1D, ← Coord' d, ite_eq_right hne, Algebra.smul_def, map_sub,
        map_neg]
    split_ifs with hdg <;> simp []
  exact exists_matrix_factorization_of_coordRelations R S g D c h1D Coord' col row

open TensorProduct in
/-- For `g : S`, the identity `g ⊗ 1 = 1 ⊗ g` in `S ⊗[R] S` holds if and only if
`g = ∑ i, ∑ j, φ (xᵢⱼ) * yᵢ * zⱼ` for some `yᵢ, zⱼ : S` and `xᵢⱼ : R` whose column sums
`∑ i, φ (xᵢⱼ) * yᵢ` and row sums `∑ j, φ (xᵢⱼ) * zⱼ` all lie in the image of `φ`. -/
@[stacks 04VY]
theorem tmul_one_eq_one_tmul_iff (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (g : S) :
    (g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g) ↔
    (∃ (n : ℕ) (y z : Fin n → S) (x : Fin n → Fin n → R),
      g = ∑ i, ∑ j, (algebraMap R S (x i j)) * y i * z j ∧
      (∀ j, ∃ r : R, ∑ i, (algebraMap R S (x i j)) * y i = algebraMap R S r) ∧
      (∀ i, ∃ r : R, ∑ j, (algebraMap R S (x i j)) * z j = algebraMap R S r)) :=
  ⟨exists_sum_repr_of_tmul_one_eq_one_tmul R S g, tmul_one_eq_one_tmul_of_sum_repr R S g⟩
