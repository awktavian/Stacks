module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Endomorphism rings under fully faithful functors

A fully faithful functor `F` induces an isomorphism `End X ≃ End (F.obj X)`. Mathlib records
the multiplicative version `CategoryTheory.Functor.FullyFaithful.mulEquivEnd`; this file upgrades
it to a ring isomorphism (for additive functors between preadditive categories) and to an
`R`-algebra isomorphism (for `R`-linear functors between `R`-linear categories).
-/

@[expose] public section

namespace CategoryTheory.Functor.FullyFaithful

open CategoryTheory.Linear

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {F : C ⥤ D} [F.Additive] (hF : F.FullyFaithful) (X : C)

/-- `mulEquivEnd` as an isomorphism between endomorphism rings. -/
@[simps!]
noncomputable def ringEquivEnd : End X ≃+* End (F.obj X) where
  __ := hF.mulEquivEnd X
  map_add' x y := by
    apply End.ext
    simp

/-- `mulEquivEnd` as an isomorphism between endomorphism algebras. -/
@[simps!]
noncomputable def algEquivEnd (R : Type*) [CommSemiring R] [CategoryTheory.Linear R C]
    [CategoryTheory.Linear R D] [F.Linear R] : End X ≃ₐ[R] End (F.obj X) where
  __ := hF.ringEquivEnd X
  commutes' r := by
    simp only [RingEquiv.toEquiv_eq_coe, Algebra.algebraMap_eq_smul_one,
      Equiv.toFun_as_coe, EquivLike.coe_coe]
    show (hF.mulEquivEnd X) (r • (1 : End X)) = r • (1 : End (F.obj X))
    apply End.ext
    simp [End.one_asHom, End.smul_asHom]

end CategoryTheory.Functor.FullyFaithful
