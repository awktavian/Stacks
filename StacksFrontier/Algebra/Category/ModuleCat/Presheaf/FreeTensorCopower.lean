module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# The tensor product of a free presheaf of modules is a copower

Let `R` be a presheaf of commutative rings on a category `C`, let `E` be a presheaf of types and
let `N` be a presheaf of `R`-modules. The free presheaf of modules `R[E]` on `E` is sectionwise
the free module on the sections of `E`, so tensoring it with `N` is sectionwise
`(E(X) →₀ R(X)) ⊗_{R(X)} N(X) ≅ E(X) →₀ N(X)`: the tensor product `R[E] ⊗_R N` is the *copower*
of `N` by `E`, the presheaf of abelian groups whose sections over `X` are the finitely supported
families of sections of `N` indexed by `E(X)`.

This is the presheaf-level half of the projection formula `g_{n!}Z ⊗_Z F ≅ bar_n(F)` of
Stacks 0D9E: there `E` is the presheaf of simplices, `R[E]` is the free presheaf whose
sheafification is `g_{n!}Z`, and the copower of `F` by the simplices is the presheaf whose
sheafification is the degree-`n` term of the simplex-coefficient resolution. Sheafification
carries the isomorphism proved here to the sheaf-level statement, by the compatibility of
sheafification with tensor products of Stacks 0GMW.

## Main definitions

* `CategoryTheory.copowerRestriction`, `.copowerPresheafObj`, `.copowerPresheafMap` and
  `.copowerPresheaf`: the copower of a presheaf of abelian groups by a presheaf of types, its
  restriction maps, and the whole thing as a functor of the presheaf of abelian groups.
* `CategoryTheory.freeTensorCopowerIsoApp`: the sectionwise identification out of which the main
  result is assembled.
* `CategoryTheory.finsuppCoproductIso`: the finitely supported families indexed by a type are the
  coproduct of that many copies, as an isomorphism of abelian groups. This is what identifies a
  copower with a direct sum.

## Main results

* `CategoryTheory.freeTensorCopowerIso`: **`R[E] ⊗_R N` is the copower of `N` by `E`**, as an
  isomorphism of the underlying presheaves of abelian groups.
* `CategoryTheory.freeTensorCopowerIso_hom_app_freeMk_tmul`: the value of that isomorphism on the
  tensor of a generator of `R[E]` with a section of `N`, which pins it down.
* `CategoryTheory.freeTensorMap_freeMk_tmul`: the restriction maps of `R[E] ⊗_R N` on the tensor
  of a generator with a section, which is what makes that isomorphism natural.

## Implementation notes

The copower is taken with finitely supported families rather than with a coproduct in the
category of presheaves of abelian groups, because the free module `ModuleCat.free` out of which
`PresheafOfModules.freeObj` is built is itself finitely supported families, so the sectionwise
isomorphism is `TensorProduct.finsuppScalarLeft` with nothing in between.
`CategoryTheory.finsuppCoproductIso` is the bridge to the coproduct description, which is the
shape the simplex-coefficient resolution is written in.

The isomorphism is stated between the *underlying presheaves of abelian groups* rather than
between presheaves of modules. That is the form the application needs — the module structure is
used only to get at the tensor product, and is dropped as soon as the comparison with
sheafification has been made — and it avoids writing restriction of scalars into the restriction
maps of the copower, which the presheaf-of-modules form would require.

The computations on the restriction maps are made by `show` and `rw` rather than by `simp`: the
finitely supported families over the sections of a presheaf of abelian groups carry their
additive structure through `AddCommGrpCat.of`, and `simp` does not match its lemmas about
`Finsupp.mapDomain` and `Finsupp.mapRange` against that spelling, while `show` is checked up to
definitional equality and goes through.

## References

* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace CategoryTheory

/-! ### The copower of a presheaf of abelian groups by a presheaf of types -/

section Copower

variable {C : Type u} [Category.{v} C] (E : Cᵒᵖ ⥤ Type u)

/-- The restriction map of the copower of a presheaf of abelian groups `G` by a presheaf of types
`E` along an arrow `f`: it restricts the coefficients along `G` and reindexes the summands along
`E`. -/
def copowerRestriction (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    AddCommGrpCat.of (E.obj X →₀ (G.obj X : Type u)) ⟶
      AddCommGrpCat.of (E.obj Y →₀ (G.obj Y : Type u)) :=
  AddCommGrpCat.ofHom
    ((Finsupp.mapDomain.addMonoidHom (ConcreteCategory.hom (E.map f))).comp
      (Finsupp.mapRange.addMonoidHom (AddCommGrpCat.Hom.hom (G.map f))))

/-- A restriction map of the copower sends the summand of a section `m` of `G` labelled by `e` to
the summand of the restriction of `m` labelled by the restriction of `e`. -/
@[simp] theorem copowerRestriction_single (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (e : E.obj X) (m : (G.obj X : Type u)) :
    AddCommGrpCat.Hom.hom (copowerRestriction E G f) (Finsupp.single e m) =
      Finsupp.single (ConcreteCategory.hom (E.map f) e)
        (AddCommGrpCat.Hom.hom (G.map f) m) := by
  show Finsupp.mapDomain (ConcreteCategory.hom (E.map f))
      (Finsupp.mapRange (AddCommGrpCat.Hom.hom (G.map f)) (map_zero _) (Finsupp.single e m)) = _
  rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]

/-- The copower of a presheaf of abelian groups `G` by a presheaf of types `E`: over an object `X`
its sections are the finitely supported families of sections of `G` indexed by `E(X)`. -/
def copowerPresheafObj (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (E.obj X →₀ (G.obj X : Type u))
  map f := copowerRestriction E G f
  map_id X := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    rw [copowerRestriction_single]
    change Finsupp.single (ConcreteCategory.hom (E.map (𝟙 X)) e)
        (AddCommGrpCat.Hom.hom (G.map (𝟙 X)) m) = Finsupp.single e m
    rw [E.map_id, G.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    rw [AddCommGrpCat.hom_comp]
    change AddCommGrpCat.Hom.hom (copowerRestriction E G (f ≫ g)) (Finsupp.single e m) =
      AddCommGrpCat.Hom.hom (copowerRestriction E G g)
        (AddCommGrpCat.Hom.hom (copowerRestriction E G f) (Finsupp.single e m))
    rw [copowerRestriction_single, copowerRestriction_single, copowerRestriction_single,
      E.map_comp, G.map_comp]
    rfl

/-- The restriction maps of the copower are `copowerRestriction`. -/
@[simp] theorem copowerPresheafObj_map (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (copowerPresheafObj E G).map f = copowerRestriction E G f :=
  rfl

/-- The copower of a morphism of presheaves of abelian groups: it acts on the coefficients and
leaves the labels alone. -/
def copowerPresheafMap {G H : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (α : G ⟶ H) :
    copowerPresheafObj E G ⟶ copowerPresheafObj E H where
  app X := AddCommGrpCat.ofHom
    (Finsupp.mapRange.addMonoidHom (AddCommGrpCat.Hom.hom (α.app X)))
  naturality X Y f := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    have h : AddCommGrpCat.Hom.hom (α.app Y) (AddCommGrpCat.Hom.hom (G.map f) m) =
        AddCommGrpCat.Hom.hom (H.map f) (AddCommGrpCat.Hom.hom (α.app X) m) :=
      congrArg (fun k => AddCommGrpCat.Hom.hom k m) (α.naturality f)
    change AddCommGrpCat.Hom.hom
        (AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom
          (AddCommGrpCat.Hom.hom (α.app Y))))
        (AddCommGrpCat.Hom.hom (copowerRestriction E G f) (Finsupp.single e m)) =
      AddCommGrpCat.Hom.hom (copowerRestriction E H f)
        (AddCommGrpCat.Hom.hom
          (AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom
            (AddCommGrpCat.Hom.hom (α.app X)))) (Finsupp.single e m))
    rw [copowerRestriction_single]
    change Finsupp.mapRange (AddCommGrpCat.Hom.hom (α.app Y)) (map_zero _)
        (Finsupp.single (ConcreteCategory.hom (E.map f) e)
          (AddCommGrpCat.Hom.hom (G.map f) m)) =
      AddCommGrpCat.Hom.hom (copowerRestriction E H f)
        (Finsupp.mapRange (AddCommGrpCat.Hom.hom (α.app X)) (map_zero _) (Finsupp.single e m))
    rw [Finsupp.mapRange_single, Finsupp.mapRange_single, copowerRestriction_single]
    exact congrArg (Finsupp.single (ConcreteCategory.hom (E.map f) e)) h

/-- The value of the copower of a morphism on the summand labelled by `e`. -/
@[simp] theorem copowerPresheafMap_app_single {G H : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (α : G ⟶ H)
    (X : Cᵒᵖ) (e : E.obj X) (m : (G.obj X : Type u)) :
    AddCommGrpCat.Hom.hom ((copowerPresheafMap E α).app X) (Finsupp.single e m) =
      Finsupp.single e (AddCommGrpCat.Hom.hom (α.app X) m) := by
  show Finsupp.mapRange (AddCommGrpCat.Hom.hom (α.app X)) (map_zero _) (Finsupp.single e m) = _
  rw [Finsupp.mapRange_single]

/-- The copower by a presheaf of types, as a functor of the presheaf of abelian groups. -/
def copowerPresheaf : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj G := copowerPresheafObj E G
  map α := copowerPresheafMap E α
  map_id G := by
    apply NatTrans.ext
    funext X
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    change Finsupp.mapRange (AddCommGrpCat.Hom.hom ((𝟙 G : G ⟶ G).app X)) (map_zero _)
        (Finsupp.single e m) = Finsupp.single e m
    rw [Finsupp.mapRange_single]
    rfl
  map_comp {G H K} α β := by
    apply NatTrans.ext
    funext X
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    change Finsupp.mapRange (AddCommGrpCat.Hom.hom ((α ≫ β).app X)) (map_zero _)
        (Finsupp.single e m) =
      Finsupp.mapRange (AddCommGrpCat.Hom.hom (β.app X)) (map_zero _)
        (Finsupp.mapRange (AddCommGrpCat.Hom.hom (α.app X)) (map_zero _) (Finsupp.single e m))
    rw [Finsupp.mapRange_single, Finsupp.mapRange_single, Finsupp.mapRange_single]
    rfl

end Copower

/-! ### The tensor product of a free presheaf of modules -/

section FreeTensor

attribute [local instance] Classical.propDecidable

variable {C : Type u} [Category.{v} C] (E : Cᵒᵖ ⥤ Type u) (R : Cᵒᵖ ⥤ CommRingCat.{u})
  (N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

/-- Over an object `X`, the tensor product of the free presheaf of modules on `E` with `N` is the
copower of the sections of `N` by the sections of `E`: the free module on a set, tensored with a
module, is the copower of that module by the set. -/
def freeTensorCopowerIsoApp (X : Cᵒᵖ) :
    ((PresheafOfModules.toPresheaf _).obj (PresheafOfModules.freeObj E ⊗ N)).obj X ≅
      (copowerPresheafObj E ((PresheafOfModules.toPresheaf _).obj N)).obj X :=
  AddEquiv.toAddCommGrpIso
    (TensorProduct.finsuppScalarLeft (R.obj X : Type u) (N.obj X : Type u)
      (E.obj X)).toAddEquiv

/-- The inverse of the sectionwise identification sends the summand of a section `m` labelled by
`e` to the tensor of the generator `e` with `m`. -/
theorem freeTensorCopowerIsoApp_inv_single (X : Cᵒᵖ) (e : E.obj X)
    (m : (N.obj X : Type u)) :
    AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N X).inv (Finsupp.single e m) =
      ModuleCat.freeMk (R := (R.obj X : Type u)) e ⊗ₜ[(R.obj X : Type u)] m :=
  TensorProduct.finsuppScalarLeft_symm_apply_single e m

/-- The sectionwise identification sends the tensor of the generator `e` with a section `m` to the
summand of `m` labelled by `e`. This pins it down: the tensors of generators with sections
generate. -/
theorem freeTensorCopowerIsoApp_hom_freeMk_tmul (X : Cᵒᵖ) (e : E.obj X)
    (m : (N.obj X : Type u)) :
    AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N X).hom
        (ModuleCat.freeMk (R := (R.obj X : Type u)) e ⊗ₜ[(R.obj X : Type u)] m) =
      Finsupp.single e m := by
  show (TensorProduct.finsuppScalarLeft (R.obj X : Type u) (N.obj X : Type u) (E.obj X))
      (Finsupp.single e 1 ⊗ₜ[(R.obj X : Type u)] m) = _
  rw [TensorProduct.finsuppScalarLeft_apply_tmul,
    Finsupp.sum_single_index (by rw [zero_smul, Finsupp.single_zero]), one_smul]

/-- The restriction map of `R[E] ⊗_R N` on the tensor of a generator with a section: it restricts
the generator along `E` and the section along `N`. -/
theorem freeTensorMap_freeMk_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (e : E.obj X)
    (m : (N.obj X : Type u)) :
    ModuleCat.Hom.hom ((PresheafOfModules.freeObj E ⊗ N).map f)
        (ModuleCat.freeMk (R := (R.obj X : Type u)) e ⊗ₜ[(R.obj X : Type u)] m) =
      ModuleCat.freeMk (R := (R.obj Y : Type u)) (ConcreteCategory.hom (E.map f) e)
        ⊗ₜ[(R.obj Y : Type u)] ModuleCat.Hom.hom (N.map f) m :=
  (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul f _ m).trans
    (congrArg (fun z => z ⊗ₜ[(R.obj Y : Type u)] ModuleCat.Hom.hom (N.map f) m)
      (ModuleCat.freeDesc_apply _ e))

/-- **The tensor product of a free presheaf of modules is a copower.** For a presheaf of types
`E` and a presheaf of `R`-modules `N`, the underlying presheaf of abelian groups of `R[E] ⊗_R N`
is the copower of the underlying presheaf of `N` by `E`. -/
def freeTensorCopowerIso :
    (PresheafOfModules.toPresheaf _).obj (PresheafOfModules.freeObj E ⊗ N) ≅
      copowerPresheafObj E ((PresheafOfModules.toPresheaf _).obj N) :=
  NatIso.ofComponents (freeTensorCopowerIsoApp E R N) (by
    intro X Y f
    refine (Iso.inv_comp_eq (freeTensorCopowerIsoApp E R N X)).mp ?_
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro e m
    have h1 : AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N X).inv
          (Finsupp.single e m) = _ :=
      freeTensorCopowerIsoApp_inv_single E R N X e m
    have h2 : AddCommGrpCat.Hom.hom
          (((PresheafOfModules.toPresheaf _).obj (PresheafOfModules.freeObj E ⊗ N)).map f)
          (ModuleCat.freeMk (R := (R.obj X : Type u)) e ⊗ₜ[(R.obj X : Type u)] m) = _ :=
      freeTensorMap_freeMk_tmul E R N f e m
    have h3 : AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N Y).hom
          (ModuleCat.freeMk (R := (R.obj Y : Type u)) (ConcreteCategory.hom (E.map f) e)
            ⊗ₜ[(R.obj Y : Type u)] ModuleCat.Hom.hom (N.map f) m) = _ :=
      freeTensorCopowerIsoApp_hom_freeMk_tmul E R N Y _ _
    have h4 := copowerRestriction_single E ((PresheafOfModules.toPresheaf _).obj N) f e m
    refine Eq.trans (congrArg (AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N Y).hom)
      (Eq.trans (congrArg (AddCommGrpCat.Hom.hom
        (((PresheafOfModules.toPresheaf _).obj (PresheafOfModules.freeObj E ⊗ N)).map f)) h1)
        h2)) ?_
    exact h3.trans h4.symm)

/-- The value of the identification on the tensor of a generator of `R[E]` with a section of `N`:
it is the summand of that section labelled by that generator. -/
theorem freeTensorCopowerIso_hom_app_freeMk_tmul (X : Cᵒᵖ) (e : E.obj X)
    (m : (N.obj X : Type u)) :
    AddCommGrpCat.Hom.hom ((freeTensorCopowerIso E R N).hom.app X)
        (ModuleCat.freeMk (R := (R.obj X : Type u)) e ⊗ₜ[(R.obj X : Type u)] m) =
      Finsupp.single e m :=
  freeTensorCopowerIsoApp_hom_freeMk_tmul E R N X e m

end FreeTensor

/-! ### Finitely supported families as a coproduct -/

section FinsuppCoproduct

/-- The finitely supported families of elements of an abelian group `A` indexed by a type `I` are
the coproduct of `I` copies of `A`: the `i`th leg is the summand labelled by `i`. -/
def finsuppCoproductIso (I : Type u) (A : AddCommGrpCat.{u}) :
    (∐ fun _ : I => A) ≅ AddCommGrpCat.of (I →₀ (A : Type u)) where
  hom := Sigma.desc fun i => AddCommGrpCat.ofHom (Finsupp.singleAddHom i)
  inv := AddCommGrpCat.ofHom
    (Finsupp.liftAddHom fun i => AddCommGrpCat.Hom.hom (Sigma.ι (fun _ : I => A) i))
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun i => ?_
    apply AddCommGrpCat.hom_ext
    ext a
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp]
    change AddCommGrpCat.Hom.hom
        (AddCommGrpCat.ofHom
          (Finsupp.liftAddHom fun j => AddCommGrpCat.Hom.hom (Sigma.ι (fun _ : I => A) j)))
        (AddCommGrpCat.Hom.hom
          (Sigma.ι (fun _ : I => A) i ≫
            Sigma.desc fun j => AddCommGrpCat.ofHom (Finsupp.singleAddHom j)) a) = _
    rw [Sigma.ι_desc]
    change Finsupp.liftAddHom
        (fun j => AddCommGrpCat.Hom.hom (Sigma.ι (fun _ : I => A) j))
        (Finsupp.single i a) = _
    rw [Finsupp.liftAddHom_apply_single]
    rfl
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro i a
    rw [AddCommGrpCat.hom_comp]
    change AddCommGrpCat.Hom.hom (Sigma.desc fun j => AddCommGrpCat.ofHom (Finsupp.singleAddHom j))
        (Finsupp.liftAddHom
          (fun j => AddCommGrpCat.Hom.hom (Sigma.ι (fun _ : I => A) j)) (Finsupp.single i a)) = _
    rw [Finsupp.liftAddHom_apply_single]
    have h := congrArg (fun k => AddCommGrpCat.Hom.hom k a)
      (Sigma.ι_desc (fun j => AddCommGrpCat.ofHom (Finsupp.singleAddHom (M := (A : Type u)) j)) i)
    rw [AddCommGrpCat.hom_comp] at h
    exact h

/-- The `i`th leg of the coproduct is the summand labelled by `i`. -/
@[simp] theorem sigma_ι_comp_finsuppCoproductIso_hom (I : Type u) (A : AddCommGrpCat.{u})
    (i : I) :
    Sigma.ι (fun _ : I => A) i ≫ (finsuppCoproductIso I A).hom =
      AddCommGrpCat.ofHom (Finsupp.singleAddHom i) :=
  Sigma.ι_desc _ _

end FinsuppCoproduct

end CategoryTheory

end
