module

public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Algebra.Equiv

/-!
# The center of a category is an invariant of its linear structure

Mathlib defines the center `CatCenter C` of a category `C` as the endomorphism monoid
`End (𝟭 C)` of its identity functor, and, when `C` is `R`-linear, a ring morphism
`CategoryTheory.Linear.toCatCenter : R →+* CatCenter C`. Since `CatCenter C` is commutative,
that morphism makes `CatCenter C` an `R`-algebra; this file records that algebra structure and
shows that it is transported along any `R`-linear equivalence of categories.

The transport is purely formal: an element of the center is conjugated by the equivalence, and
no structure beyond additivity and `R`-linearity of the equivalence is used. In particular a
triangulated equivalence is far more than is needed.

## Main definitions

* `CategoryTheory.CatCenter.instAlgebra`: the `R`-algebra structure on `CatCenter C` carried by
  an `R`-linear preadditive category `C`.
* `CategoryTheory.CatCenter.whiskerFunctor`: the endomorphism `F ⟶ F` of a functor `F : C ⥤ D`
  obtained by applying `F` to a central element of `C`.
* `CategoryTheory.CatCenter.transport`: the element of `CatCenter D` attached to an element of
  `CatCenter C` and an equivalence `C ≌ D`.
* `CategoryTheory.CatCenter.transportEquiv`: `transport` as a bijection, with the transport
  along the inverse equivalence as its inverse.
* `CategoryTheory.CatCenter.transportAlgEquiv`: `transport` along an `R`-linear equivalence as
  an isomorphism of `R`-algebras.

## Main results

* `CategoryTheory.CatCenter.transport_app_functor`: the transported element is computed on the
  image of `E.functor` by applying `E.functor`.
* `CategoryTheory.CatCenter.ext_of_equivalence`: two central elements of `D` that agree on the
  image of an equivalence `E : C ≌ D` are equal.

## Implementation notes

`transport` is defined as a composite of natural transformations in the functor category
`D ⥤ D`, namely `E.counitIso.inv ≫ whiskerLeft E.inverse (whiskerFunctor E.functor z) ≫
E.counitIso.hom`, so that its naturality is inherited rather than proved. Its value on objects
is `transport_app`, which holds by `rfl`.

The inverse of `transportEquiv` is given by the honest formula `transport E.symm`, not by
inverting a bijection; both round trips are instances of the single lemma
`transport_transport_symm`, applied to `E` and to `E.symm`.

## References

* [Stacks Project, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD), for which this file
  supplies the transport-of-structure step.
-/

@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ u₁ u₂

namespace CatCenter

section Algebra

variable (R : Type*) [CommRing R] (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear R C]

open scoped IsMulCommutative in
/-- The center of an `R`-linear category is an `R`-algebra: `Linear.toCatCenter` is a ring
morphism `R →+* CatCenter C`, and `CatCenter C` is commutative. -/
instance instAlgebra : Algebra R (CatCenter C) :=
  (Linear.toCatCenter R C).toAlgebra' fun _ _ => mul_comm _ _

variable {C}

/-- The image of `r : R` in the center of an `R`-linear category acts on each object by
multiplication by `r`. -/
lemma algebraMap_app (r : R) (X : C) : (algebraMap R (CatCenter C) r).app X = r • 𝟙 X := rfl

end Algebra

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A central element `z` of `C` induces an endomorphism of any functor `F : C ⥤ D`, whose
component at `X` is `F.map (z.app X)`. -/
@[simps]
def whiskerFunctor (F : C ⥤ D) (z : CatCenter C) : F ⟶ F where
  app X := F.map (z.app X)
  naturality _ _ f := by rw [← F.map_comp, ← F.map_comp, z.naturality]

/-- The central element of `D` obtained from a central element of `C` by conjugating with an
equivalence `E : C ≌ D`. -/
def transport (E : C ≌ D) (z : CatCenter C) : CatCenter D :=
  End.of (E.counitIso.inv ≫ Functor.whiskerLeft E.inverse (whiskerFunctor E.functor z) ≫
    E.counitIso.hom)

variable (E : C ≌ D)

/-- The component of the transport of `z` at `Y` is the conjugate of
`E.functor.map (z.app (E.inverse.obj Y))` by the counit of `E`. -/
lemma transport_app (z : CatCenter C) (Y : D) :
    (transport E z).app Y =
      E.counitInv.app Y ≫ E.functor.map (z.app (E.inverse.obj Y)) ≫ E.counit.app Y := rfl

/-- On the image of `E.functor`, conjugation by `E` is simply the action of `E.functor`. -/
lemma transport_app_functor (z : CatCenter C) (X : C) :
    (transport E z).app (E.functor.obj X) = E.functor.map (z.app X) := by
  have hn : E.unit.app X ≫ z.app (E.inverse.obj (E.functor.obj X)) = z.app X ≫ E.unit.app X :=
    z.naturality _
  rw [transport_app, E.counitInv_app_functor, E.counit_app_functor, ← E.functor.map_comp,
    ← E.functor.map_comp, ← assoc, hn]
  simp

/-- An equivalence `E : C ≌ D` is essentially surjective, so a central element of `D` is
determined by its components on the image of `E.functor`. -/
lemma ext_of_equivalence {w₁ w₂ : CatCenter D}
    (h : ∀ X : C, w₁.app (E.functor.obj X) = w₂.app (E.functor.obj X)) : w₁ = w₂ := by
  refine CatCenter.ext _ _ fun Y => ?_
  have e : Y ≅ E.functor.obj (E.inverse.obj Y) := (E.counitIso.app Y).symm
  refine (cancel_mono e.hom).1 ?_
  rw [← w₁.naturality e.hom, ← w₂.naturality e.hom, h]

/-- Conjugating by `E.symm` and then by `E` is the identity. Applied to `E.symm` this is also
the other round trip, since `E.symm.symm = E`. -/
lemma transport_transport_symm (w : CatCenter D) : transport E (transport E.symm w) = w := by
  refine ext_of_equivalence E fun X => ?_
  have hc : (E.inverse ⋙ E.functor).map (w.app (E.functor.obj X)) ≫
      E.counit.app (E.functor.obj X) =
      E.counit.app (E.functor.obj X) ≫ w.app (E.functor.obj X) := E.counit.naturality _
  rw [transport_app_functor, transport_app]
  show E.functor.map
    (E.unit.app X ≫ E.inverse.map (w.app (E.functor.obj X)) ≫ E.unitInv.app X) = _
  rw [E.functor.map_comp, E.functor.map_comp, ← E.counitInv_app_functor, ← E.counit_app_functor,
    ← Functor.comp_map, hc]
  simp

/-- Conjugation by an equivalence is a bijection between the centers, with conjugation by the
inverse equivalence as its inverse. -/
@[simps]
def transportEquiv : CatCenter C ≃ CatCenter D where
  toFun := transport E
  invFun := transport E.symm
  left_inv z := transport_transport_symm E.symm z
  right_inv w := transport_transport_symm E w

/-- Transport along an equivalence sends the unit of `CatCenter C` to the unit of `CatCenter D`. -/
lemma transport_one : transport E 1 = 1 :=
  CatCenter.ext _ _ fun _ => by simp [transport_app]

/-- Transport along an equivalence is multiplicative. -/
lemma transport_mul (x y : CatCenter C) :
    transport E (x * y) = transport E x * transport E y :=
  CatCenter.ext _ _ fun _ => by simp [transport_app, CatCenter.mul_app]

section Preadditive

variable [Preadditive C] [Preadditive D] [E.functor.Additive]

/-- Transport along an additive equivalence sends `0` to `0`. -/
lemma transport_zero : transport E 0 = 0 :=
  CatCenter.ext _ _ fun _ => by simp [transport_app]

/-- Transport along an additive equivalence is additive. -/
lemma transport_add (x y : CatCenter C) :
    transport E (x + y) = transport E x + transport E y :=
  CatCenter.ext _ _ fun _ => by simp [transport_app, CatCenter.app_add]

variable (R : Type*) [CommRing R] [Linear R C] [Linear R D] [E.functor.Linear R]

omit [E.functor.Additive] in
/-- Transport along an `R`-linear equivalence commutes with the algebra maps from `R`. -/
lemma transport_algebraMap (r : R) :
    transport E (algebraMap R (CatCenter C) r) = algebraMap R (CatCenter D) r :=
  CatCenter.ext _ _ fun Y => by
    rw [transport_app, algebraMap_app, algebraMap_app, E.functor.map_smul]
    simp

/-- **Transport of structure for the center of a linear category.** An `R`-linear additive
equivalence `E : C ≌ D` induces an isomorphism `CatCenter C ≃ₐ[R] CatCenter D` of
`R`-algebras. -/
def transportAlgEquiv : CatCenter C ≃ₐ[R] CatCenter D :=
  { transportEquiv E with
    map_mul' := transport_mul E
    map_add' := transport_add E
    commutes' := transport_algebraMap E R }

/-- The algebra isomorphism `transportAlgEquiv E R` acts as `transport E`. -/
@[simp]
lemma transportAlgEquiv_apply (z : CatCenter C) : transportAlgEquiv E R z = transport E z := rfl

end Preadditive

end CatCenter

end CategoryTheory

end
