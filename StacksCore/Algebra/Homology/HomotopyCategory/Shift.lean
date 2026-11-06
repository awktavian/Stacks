module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import StacksCore.Tactic.StacksAttribute

/-! # The shift functor on complexes

Stacks tags 011G (cochain complexes) and 011A (chain complexes): the `k`-shifted complex `A[k]`,
with `A[k]^n = A^{n+k}` and `d_{A[k]} = (-1)^k d_A`, together with `f[k]` on morphisms.

Unlike every pair in §12.13, these two do **not** collapse to one declaration. Mathlib shifts
cochain complexes only -- there is no `HasShift (ChainComplex C ℤ) ℤ` instance, and
`ComplexShape.down ℤ` does not occur in the library at all -- so 011G is recorded against
`CochainComplex.shiftFunctor` while 011A is defined here, mirroring it.

The conventions agree with the Stacks project exactly, in both cases: the shift is given for every
`k : ℤ` at once rather than for `k = 1` and iterated, so the `(-1)^k` sign is definitional, and it
depends on `k` alone and never on the degree.

The chain-complex side mirrors the whole of Mathlib's cochain construction: the functor, the
identifications `shiftFunctorZero'` and `shiftFunctorAdd'`, and the `HasShift` instance built from
them by `hasShiftMk`, so that `A⟦k⟧` parses for a chain complex and still means the `A[k]` above.
The three coherence fields of `ShiftMkCore` are discharged by their `cat_disch` auto-parameters,
which needs `XIsoOfEq` to be a local `simp` lemma -- without that the `eqToHom`s in `assoc_hom_app`
and friends never cancel. Tags 011B to 011F build on this instance.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

add_to_stacks 011G "the definition; Mathlib gives the shift for every `k : ℤ` at once, not for
`k = 1` iterated, so the `(-1)^k` sign is definitional rather than derived."
  CochainComplex.shiftFunctor

add_to_stacks 011G "the `HasShift` instance, which is what makes the notation `A⟦k⟧` available and
packages the shifts of all `k` together."
  CochainComplex.instHasShiftInt

add_to_stacks 011G "clause 1: `A[k]^n = A^{n+k}`, on the nose."
  CochainComplex.shiftFunctor_obj_X

add_to_stacks 011G "clause 2: `d_{A[k]}^n = (-1)^k d_A^{n+k}`, where the sign is `Int.negOnePow k`
in `ℤˣ` because `(-1 : ℤ)^k` does not exist for negative `k`. It depends on `k` and not on `n`,
as in the Stacks project."
  CochainComplex.shiftFunctor_obj_d

add_to_stacks 011G "the last sentence, `f[k]^n = f^{k+n}`; Mathlib writes the index as `n + k`,
which is the same integer but not the same term, so the two spellings have different syntactic
types."
  CochainComplex.shiftFunctor_map_f

namespace ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The `n`-shifted chain complex `K[n]`, which is `K.X (i + n)` in degree `i` and whose
differentials are those of `K` multiplied by `(-1)^n`. -/
abbrev shiftComplex (n : ℤ) (K : ChainComplex C ℤ) : ChainComplex C ℤ where
  X i := K.X (i + n)
  d i j := n.negOnePow • K.d (i + n) (j + n)
  shape i j h := by rw [K.shape (i + n) (j + n) (by
    change ¬ j + 1 = i at h; lia : ¬ (j + n + 1 = i + n)), smul_zero]
  d_comp_d' i j k hij hjk := by
    rw [Units.smul_def, Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
      K.d_comp_d, smul_zero, smul_zero]

/-- The `n`-shifted morphism `φ[n] : K[n] ⟶ L[n]`, which is `φ.f (i + n)` in degree `i`. -/
@[implicit_reducible, simps]
def shiftComplexMap (n : ℤ) {K L : ChainComplex C ℤ} (φ : K ⟶ L) :
    shiftComplex C n K ⟶ shiftComplex C n L where
  f i := φ.f (i + n)
  comm' i j hij := by simp

/-- **Stacks 011A.** The shift functor by `n : ℤ` on `ChainComplex C ℤ`, sending a chain complex
`K` to the complex which is `K.X (i + n)` in degree `i` and whose differentials are those of `K`
multiplied by `(-1)^n`.

This mirrors `CochainComplex.shiftFunctor`, which Mathlib has and which is tag 011G; the two
definitions differ only in the complex shape and in the arithmetic discharging `shape`. -/
@[stacks 011A "the definition, together with its three `@[simps]` clauses below"]
abbrev shiftFunctor (n : ℤ) : ChainComplex C ℤ ⥤ ChainComplex C ℤ where
  obj := shiftComplex C n
  map := shiftComplexMap C n

instance (n : ℤ) : (shiftFunctor C n).Additive where

instance (n : ℤ) {R : Type*} [Ring R] [Linear R C] :
    Functor.Linear R (shiftFunctor C n) where

variable {C}

/-- The canonical isomorphism `((shiftFunctor C n).obj K).X i ≅ K.X m` when `m = i + n`. -/
@[implicit_reducible, simp]
def shiftFunctorObjXIso (K : ChainComplex C ℤ) (n i m : ℤ) (hm : m = i + n) :
    (shiftComplex C n K).X i ≅ K.X m := K.XIsoOfEq hm.symm

section

variable (C)

/-- The shift functor by `n` on `ChainComplex C ℤ` identifies to the identity
functor when `n = 0`. -/
@[implicit_reducible, simps!]
def shiftFunctorZero' (n : ℤ) (h : n = 0) :
    shiftFunctor C n ≅ 𝟭 _ where
  hom := {
    app K := { f i := (shiftFunctorObjXIso K n i i (by rw [h, add_zero])).hom }
    naturality {K L} f := by ext; simp [XIsoOfEq_hom_naturality]}
  inv :=
  { app K := { f i := (shiftFunctorObjXIso K n i i (by rw [h, add_zero])).inv }
    naturality {K L} f := by ext; simp [XIsoOfEq_inv_naturality]}

/-- The compatibility of the shift functors on `ChainComplex C ℤ` with respect
to the addition of integers. -/
@[implicit_reducible, simps!]
def shiftFunctorAdd' (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂) :
    shiftFunctor C n₁₂ ≅ shiftFunctor C n₁ ⋙ shiftFunctor C n₂ where
  hom :=
  { app K :=
    { f i := (K.shiftFunctorObjXIso n₁₂ i (i + n₂ + n₁) (by rw [← h, add_assoc, add_comm n₁])).hom
      comm' i j hij := by simp [smul_smul, ← h, Int.negOnePow_add, mul_comm]}
    naturality {K L} f := by ext; simp [XIsoOfEq_hom_naturality] }
  inv := {
    app K :=
    { f i := (K.shiftFunctorObjXIso n₁₂ i (i + n₂ + n₁) (by rw [← h, add_assoc, add_comm n₁])).inv
      comm' i j hij := by simp [smul_smul, ← h, Int.negOnePow_add, mul_comm] }
    naturality {K L} f := by ext; simp [XIsoOfEq_inv_naturality] }

attribute [local simp] XIsoOfEq

instance instHasShiftInt : HasShift (ChainComplex C ℤ) ℤ := hasShiftMk _ _ {
  F := shiftFunctor C
  zero := shiftFunctorZero' C 0 rfl
  add := fun n₁ n₂ => shiftFunctorAdd' C n₁ n₂ (n₁ + n₂) rfl
}

instance (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.down ℤ)) n).Additive :=
  inferInstanceAs <| (ChainComplex.shiftFunctor C n).Additive

instance (n : ℤ) {R : Type*} [Ring R] [Linear R C] :
    Functor.Linear R
      (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.down ℤ)) n) where

end

@[simp]
lemma shiftFunctor_obj_X' (K : ChainComplex C ℤ) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (ChainComplex C ℤ) n).obj K).X p = K.X (p + n) := rfl

@[simp]
lemma shiftFunctor_map_f' {K L : ChainComplex C ℤ} (φ : K ⟶ L) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (ChainComplex C ℤ) n).map φ).f p = φ.f (p + n) := rfl

@[simp]
lemma shiftFunctor_obj_d' (K : ChainComplex C ℤ) (n i j : ℤ) :
    ((CategoryTheory.shiftFunctor (ChainComplex C ℤ) n).obj K).d i j =
      n.negOnePow • K.d _ _ := rfl

lemma shiftFunctorAdd_inv_app_f (K : ChainComplex C ℤ) (a b n : ℤ) :
    ((shiftFunctorAdd (ChainComplex C ℤ) a b).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := rfl

lemma shiftFunctorAdd_hom_app_f (K : ChainComplex C ℤ) (a b n : ℤ) :
    ((shiftFunctorAdd (ChainComplex C ℤ) a b).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := by
  tauto

lemma shiftFunctorAdd'_inv_app_f' (K : ChainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd' (ChainComplex C ℤ) a b ab h).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_inv_app_f]

lemma shiftFunctorAdd'_hom_app_f' (K : ChainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd' (ChainComplex C ℤ) a b ab h).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_hom_app_f]

lemma shiftFunctorZero_inv_app_f (K : ChainComplex C ℤ) (n : ℤ) :
    ((CategoryTheory.shiftFunctorZero (ChainComplex C ℤ) ℤ).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_zero])).hom := rfl

lemma shiftFunctorZero_hom_app_f (K : ChainComplex C ℤ) (n : ℤ) :
    ((CategoryTheory.shiftFunctorZero (ChainComplex C ℤ) ℤ).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_zero])).hom := by
  tauto

lemma XIsoOfEq_shift (K : ChainComplex C ℤ) (n : ℤ) {p q : ℤ} (hpq : p = q) :
    (K⟦n⟧).XIsoOfEq hpq = K.XIsoOfEq (show p + n = q + n by rw [hpq]) := rfl

variable (C)

lemma shiftFunctorAdd'_eq (a b c : ℤ) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (ChainComplex C ℤ) a b c h =
      shiftFunctorAdd' C a b c h := by
  ext
  simp only [shiftFunctorAdd'_hom_app_f', XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f]

lemma shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (ChainComplex C ℤ) a b = shiftFunctorAdd' C a b _ rfl := by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd'_eq]

lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (ChainComplex C ℤ) ℤ = shiftFunctorZero' C 0 rfl := by
  ext
  rw [shiftFunctorZero_hom_app_f, shiftFunctorZero'_hom_app_f]

-- `shortComplexFunctor'` needs to unfold so a `K.XIsoOfEq` supplied where a
-- `(shiftFunctor n ⋙ eval i).obj K ≅ _` is expected is type-correct at `implicit` transparency,
-- which is what lets the rest of the section go through with no `set_option backward.*`.
-- Mathlib now marks both `eval` and `shortComplexFunctor'` `@[implicit_reducible]` itself
-- (`Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean`), and re-setting a status a
-- declaration already has is an error, so the local attribute is removed rather than retargeted.

/-- Shifting chain complexes by `n` and evaluating in a degree `i` identifies
to the evaluation in degree `i'` when `i + n = i'`.

The hypothesis is `i + n = i'` and not `n + i = i'`: the shift is `K.X (i + n)`, so in this
orientation `K.XIsoOfEq hi` already *is* the required component, with no arithmetic in between
and nothing for the elaborator to bridge definitionally. -/
@[simps!]
def shiftEval (n i i' : ℤ) (hi : i + n = i') :
    (CategoryTheory.shiftFunctor (ChainComplex C ℤ) n) ⋙
      HomologicalComplex.eval C (ComplexShape.down ℤ) i ≅
      HomologicalComplex.eval C (ComplexShape.down ℤ) i' where
  hom := {
    app K := (K.XIsoOfEq hi).hom
    naturality {K L} f := by simp [XIsoOfEq_hom_naturality f hi]
  }
  inv := {
    app K := (K.XIsoOfEq hi).inv
    naturality {K L} f := by simp [XIsoOfEq_inv_naturality f hi]
  }
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

section ShiftSequence

open Limits

attribute [local simp] XIsoOfEq_hom_naturality smul_smul

/-- The natural isomorphism `(K⟦n⟧).sc' i j k ≅ K.sc' i' j' k'` when `i + n = i'`, `j + n = j'`
and `k + n = k'`. The outer two components carry the shift sign `(-1)^n`, the middle one does
not; that is what makes the identification of homology below sign-free. -/
@[simps!]
def shiftShortComplexFunctor' (n i j k i' j' k' : ℤ)
    (hi : i + n = i') (hj : j + n = j') (hk : k + n = k') :
    CategoryTheory.shiftFunctor (ChainComplex C ℤ) n ⋙ shortComplexFunctor' C _ i j k ≅
      shortComplexFunctor' C _ i' j' k' :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk
      (n.negOnePow • ((shiftEval C n i i' hi).app K))
      ((shiftEval C n j j' hj).app K) (n.negOnePow • ((shiftEval C n k k' hk).app K))
      (by simp [Units.smul_def]) (by simp))
      (fun f ↦ by ext <;> simp)

/-- The natural isomorphism `(K⟦n⟧).sc i ≅ K.sc i'` when `i + n = i'`. -/
@[simps!]
noncomputable def shiftShortComplexFunctorIso (n i i' : ℤ) (hi : i + n = i') :
    CategoryTheory.shiftFunctor (ChainComplex C ℤ) n ⋙ shortComplexFunctor C _ i ≅
      shortComplexFunctor C _ i' :=
  shiftShortComplexFunctor' C n _ i _ _ i' _
    (by simp only [prev]; lia) hi (by simp only [next]; lia)

variable [CategoryWithHomology C]

/-- **Stacks 011B.** For `k : ℤ` the identification `H_{i+k}(A_•) = H_i(A[k]_•)` coming from
`A_{i+k} = A[k]_i`, as an isomorphism of functors.

As for its cochain twin 011H, Mathlib's direction is the opposite of the Stacks project's: the
`hom` component runs `H_a(K[n]) ⟶ H_{a'}(K)` for `a + n = a'`, so the arrow the Stacks project
writes is `inv`. Being an isomorphism it carries the tag either way.

No sign enters, even though the shift multiplies differentials by `(-1)^k`: in
`shiftShortComplexFunctor'` the sign sits on the outer two terms and homology is the subquotient
cut out by the middle one. -/
@[stacks 011B "the identification; the Stacks arrow `H_{i+k}(A_•) → H_i(A[k]_•)` is its `inv`"]
noncomputable def shiftIso (n a a' : ℤ) (ha' : a + n = a') :
    CategoryTheory.shiftFunctor (ChainComplex C ℤ) n ⋙
        homologyFunctor C (ComplexShape.down ℤ) a ≅
      homologyFunctor C (ComplexShape.down ℤ) a' :=
  Functor.isoWhiskerLeft _ (homologyFunctorIso C (ComplexShape.down ℤ) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (shiftShortComplexFunctorIso C n a a' ha')
      (ShortComplex.homologyFunctor C) ≪≫
    (homologyFunctorIso C (ComplexShape.down ℤ) a').symm

end ShiftSequence

section HomologyShift

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/-- The comparison `(K⟦n⟧).sc i ⟶ K.sc i'` of short complexes underlying the identification of
011B, as a morphism rather than as a component of a natural isomorphism.

Declaring it at this spelling is what lets the lemmas below be manipulated by `rw` and `simp`:
`NatIso.app` produces `(shiftFunctor _ n ⋙ shortComplexFunctor _ _ i).obj K`, while
`HomologicalComplex.sc` produces `(K⟦n⟧).sc i`, and the two are definitionally but not
syntactically equal. -/
noncomputable def shiftScHom (K : ChainComplex C ℤ) (n i i' : ℤ) (hi : i + n = i') :
    (K⟦n⟧).sc i ⟶ K.sc i' := (shiftShortComplexFunctorIso C n i i' hi).hom.app K

omit [CategoryWithHomology C] in
/-- The middle component of `shiftScHom` is the unsigned re-indexing. This is the reason 011B and
011E are sign-free: the `(-1)^n` of the shift sits on `τ₁` and `τ₃`, and homology is the
subquotient cut out by `τ₂`. -/
@[simp]
lemma shiftScHom_τ₂ (K : ChainComplex C ℤ) (n i i' : ℤ) (hi : i + n = i') :
    (K.shiftScHom n i i' hi).τ₂ = (K.XIsoOfEq hi).hom :=
  shiftShortComplexFunctorIso_hom_app_τ₂ C n i i' hi K

/-- The identification `H_i(K[n]) ≅ H_{i+n}(K)` of 011B, at a fixed complex.

This is `shiftIso` evaluated at `K`, declared so that its source is spelled `(K⟦n⟧).homology a`
rather than `(shiftFunctor _ n ⋙ homologyFunctor _ a).obj K`. Stating 011E against this rather
than against `Functor.shiftIso` is what makes it independent of a
`(homologyFunctor C (ComplexShape.down ℤ) 0).ShiftSequence ℤ` instance, which the chain side does
not have. -/
noncomputable def homologyShiftIso (K : ChainComplex C ℤ) (n a a' : ℤ) (ha' : a + n = a') :
    (K⟦n⟧).homology a ≅ K.homology a' :=
  (shiftIso C n a a' ha').app K

lemma homologyShiftIso_hom (K : ChainComplex C ℤ) (n a a' : ℤ) (ha' : a + n = a') :
    (K.homologyShiftIso n a a' ha').hom =
      ShortComplex.homologyMap (K.shiftScHom n a a' ha') := by
  simp only [homologyShiftIso, shiftScHom, shiftIso, Iso.app_hom, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    homologyFunctorIso_hom_app, homologyFunctorIso_inv_app, ShortComplex.homologyFunctor_map,
    Category.id_comp]
  -- `rw [comp_id]` will not fire here: the identity's object carries the functor spelling while
  -- the arrow carries the `sc` one. `exact` unifies at default transparency.
  exact (Category.id_comp _).trans (Category.comp_id _)

-- the unprimed `shortComplexFunctor` is a separate declaration from the `'` one made
-- `implicit_reducible` at the top of this section, and is needed here as well
attribute [local implicit_reducible] HomologicalComplex.shortComplexFunctor in
/-- The identification of 011B carries the class of a cycle of `K⟦n⟧` to the class of its
transport to `K`. This is the chain twin of `CochainComplex.liftCycles_shift_homologyπ`, turned to
the `hom` direction, and it is the one lemma 011E rests on.

**This proof is definitional, not lemma-driven.** It unfolds `liftCycles`, `homologyπ`, `homology`
and `cycles` and closes by `rfl`, so it depends on the *shape* of Mathlib's homology API rather
than on any stated property of it; the two `implicit_reducible` attributes are what let
`ShortComplex.liftCycles_comp_cyclesMap_assoc` fire, and dropping either turns the `rfl` into a
bare mismatch with no diagnostic. A Mathlib bump that reshapes `HomologicalComplex.homology` will
break this and nothing else here. -/
@[reassoc]
lemma liftCycles_homologyπ_homologyShiftIso (K : ChainComplex C ℤ) {A : C} {n i : ℤ}
    (f : A ⟶ (K⟦n⟧).X i) (j : ℤ) (hj : (ComplexShape.down ℤ).next i = j)
    (hf : f ≫ (K⟦n⟧).d i j = 0) (i' : ℤ) (hi' : i + n = i') (j' : ℤ)
    (hj' : (ComplexShape.down ℤ).next i' = j') :
    (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i ≫ (K.homologyShiftIso n i i' hi').hom =
      K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' hi'.symm).hom) j' hj' (by
        simp only [ChainComplex.next] at hj hj'
        obtain rfl : i' = i + n := hi'.symm
        obtain rfl : j = i - 1 := hj.symm
        obtain rfl : j' = i - 1 + n := by lia
        rw [shiftFunctor_obj_d'] at hf
        simpa [Linear.comp_units_smul, Units.smul_def] using hf) ≫
        K.homologyπ i' := by
  simp [homologyShiftIso_hom, HomologicalComplex.liftCycles, HomologicalComplex.homologyπ,
    HomologicalComplex.homology, HomologicalComplex.cycles]

end HomologyShift

end ChainComplex
