module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Lifting an additive functor on abelian sheaves to sheaves of `Λ`-modules

Let `Λ` be a ring and let `G` be an additive functor from abelian sheaves on a site `(C₁, J₁)`
to abelian sheaves on a site `(C₂, J₂)`. This file lifts `G` to a functor on sheaves of
`Λ`-modules, together with the identification of the lift with `G` on underlying abelian
sheaves.

A sheaf of `Λ`-modules `F` carries, for every `a : Λ`, multiplication by `a` as an endomorphism
of its underlying abelian sheaf `A`, and `a ↦ (a • ·)` is a ring map `Λ → End A`. An additive
functor carries that to a ring map `Λ → End (G A)`, which is exactly a `Λ`-module structure on
the sections of `G A` compatible with the restriction maps; and `G A` is a sheaf, so the
resulting presheaf of `Λ`-modules is a sheaf as well.

## Main definitions

* `Stacks.ModuleCatLift.ofEndAction` — a functor to abelian groups together with an action of
  `Λ` on it, read as a functor to `Λ`-modules, with `Stacks.ModuleCatLift.ofEndActionMap` on
  morphisms and `Stacks.ModuleCatLift.sheafOfEndAction` the sheaf version.
* `Stacks.ModuleCatLift.sheafScalarEnd` — multiplication by a scalar on the abelian sheaf
  underlying a sheaf of `Λ`-modules.
* `Stacks.ModuleCatLift.moduleLift` — the lift of an additive functor between categories of
  abelian sheaves to the categories of sheaves of `Λ`-modules.

## Main results

* `Stacks.ModuleCatLift.moduleLift_comp_sheafCompose` and
  `Stacks.ModuleCatLift.moduleLiftForgetIso`: forgetting the `Λ`-module structure of the lift
  gives the original functor applied to the underlying abelian sheaves, on the nose.

## Implementation notes

The coefficient ring `Λ` is an arbitrary ring, not a commutative one. One might expect
commutativity to be needed in order for multiplication by `a : Λ` on a sheaf of `Λ`-modules to
be a morphism, but no morphism of `Λ`-modules is required here: multiplication by `a` is used
only as an endomorphism of the *underlying abelian sheaf*, which is Mathlib's
`ModuleCat.smulNatTrans`, a ring map `Λ →+* End (forget₂ (ModuleCat Λ) AddCommGrpCat)` for any
ring `Λ`.

The sheaf condition is transferred with `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp` along
`forget₂ (ModuleCat Λ) AddCommGrpCat`, which reflects limits of every size by
`ModuleCat.forget₂AddCommGroup_reflectsLimitOfSize`. Unlike
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` this incurs no size condition relating the
module universe to the universes of the site, which matters for the small étale sites: there
the coefficient universe is pinned to a cutoff that has nothing to do with the universes of the
site itself.

The proofs below all reduce to the underlying abelian morphisms, which
`CategoryTheory.ObjectProperty.ι` and `forget₂ (ModuleCat Λ) AddCommGrpCat` do faithfully, and
are then `rfl`; the only one with content is `sheafScalarEnd_naturality`, which is
`ModuleCat.smul_naturality`, i.e. `Λ`-linearity of a morphism of sheaves of `Λ`-modules. In
particular the comparison of the lift with the original functor is an equality of functors, not
merely an isomorphism: the presheaf of abelian groups underlying `ofEndAction` is definitionally
the presheaf it was built from, and `CategoryTheory.Presheaf.IsSheaf` is a `Prop`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w r u₁ v₁ u₂ v₂ u₃ v₃

namespace Stacks.ModuleCatLift

/-- The map an additive functor induces on endomorphism rings. -/
public def mapEndRingHom {D₁ : Type u₁} [Category.{v₁} D₁] [Preadditive D₁] {D₂ : Type u₂}
    [Category.{v₂} D₂] [Preadditive D₂] (H : D₁ ⥤ D₂) [H.Additive] (Z : D₁) :
    End Z →+* End (H.obj Z) where
  toFun e := .of (H.map e.asHom)
  map_one' := End.ext (H.map_id Z)
  map_mul' _ _ := End.ext (H.map_comp _ _)
  map_zero' := End.ext (H.map_zero Z Z)
  map_add' _ _ := End.ext H.map_add

/-- Whiskering on the left, as a map of endomorphism rings of a functor. -/
public def whiskerLeftEndRingHom {K : Type u₁} [Category.{v₁} K] {A : Type u₂}
    [Category.{v₂} A] {Bc : Type u₃} [Category.{v₃} Bc] [Preadditive Bc] (P : K ⥤ A)
    (H : A ⥤ Bc) : End H →+* End (P ⋙ H) where
  toFun α := .of (Functor.whiskerLeft P α.asHom)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

section Presheaf

variable (Λ : Type r) [Ring Λ] {K : Type u₁} [Category.{v₁} K]

/-- An action of `Λ` on a functor to abelian groups, evaluated at an object. -/
public def appEnd {P : K ⥤ AddCommGrpCat.{w}} (φ : Λ →+* End P) (U : K) :
    Λ →+* End (P.obj U) :=
  (mapEndRingHom ((evaluation K AddCommGrpCat.{w}).obj U) P).comp φ

/-- The action `appEnd φ U` sends `a` to the component at `U` of `φ a`. -/
@[simp]
public lemma appEnd_apply {P : K ⥤ AddCommGrpCat.{w}} (φ : Λ →+* End P) (U : K) (a : Λ) :
    appEnd Λ φ U a = .of ((φ a).asHom.app U) :=
  rfl

/-- A functor to abelian groups together with an action of `Λ` on it, read as a functor to
`Λ`-modules: the sections at `U` are the sections of `P` at `U` with the `Λ`-action `φ`
evaluated at `U`, and the restriction maps are those of `P`, which are `Λ`-linear by
naturality of `φ`. -/
public def ofEndAction (P : K ⥤ AddCommGrpCat.{w}) (φ : Λ →+* End P) : K ⥤ ModuleCat.{w} Λ where
  obj U := ModuleCat.mkOfSMul (appEnd Λ φ U)
  map g := ModuleCat.homMk (P.map g) fun a => (φ a).asHom.naturality g
  map_id U := (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (by
    change P.map (𝟙 U) = 𝟙 _
    rw [P.map_id])
  map_comp g h := (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (by
    change P.map (g ≫ h) = P.map g ≫ P.map h
    rw [P.map_comp])

/-- The functor to abelian groups underlying `ofEndAction` is the functor it was built
from. -/
public lemma ofEndAction_comp_forget₂ (P : K ⥤ AddCommGrpCat.{w}) (φ : Λ →+* End P) :
    ofEndAction Λ P φ ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} = P :=
  rfl

/-- The abelian group homomorphism underlying `(ofEndAction P φ).map g` is `P.map g`. -/
@[simp]
public lemma forget₂_map_ofEndAction_map (P : K ⥤ AddCommGrpCat.{w}) (φ : Λ →+* End P)
    {U V : K} (g : U ⟶ V) :
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map ((ofEndAction Λ P φ).map g) = P.map g :=
  rfl

/-- A morphism of functors to abelian groups commuting with the actions of `Λ`, read as a
morphism of functors to `Λ`-modules. -/
public def ofEndActionMap {P Q : K ⥤ AddCommGrpCat.{w}} (φ : Λ →+* End P) (ψ : Λ →+* End Q)
    (α : P ⟶ Q) (hα : ∀ a : Λ, (φ a).asHom ≫ α = α ≫ (ψ a).asHom) :
    ofEndAction Λ P φ ⟶ ofEndAction Λ Q ψ where
  app U := ModuleCat.homMk (α.app U) fun a => (NatTrans.congr_app (hα a) U).symm
  naturality U V g := (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map_injective (by
    change P.map g ≫ α.app V = α.app U ≫ Q.map g
    exact α.naturality g)

/-- The abelian group homomorphism underlying the component at `U` of `ofEndActionMap φ ψ α hα`
is `α.app U`. -/
@[simp]
public lemma forget₂_map_ofEndActionMap_app {P Q : K ⥤ AddCommGrpCat.{w}} (φ : Λ →+* End P)
    (ψ : Λ →+* End Q) (α : P ⟶ Q) (hα : ∀ a : Λ, (φ a).asHom ≫ α = α ≫ (ψ a).asHom) (U : K) :
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map ((ofEndActionMap Λ φ ψ α hα).app U) =
      α.app U :=
  rfl

end Presheaf

section Sheaf

variable (Λ : Type r) [Ring Λ] {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- A sheaf of abelian groups together with an action of `Λ` on it, read as a sheaf of
`Λ`-modules. The sheaf condition is reflected by `forget₂ (ModuleCat Λ) AddCommGrpCat`. -/
public def sheafOfEndAction (F : Sheaf J AddCommGrpCat.{w}) (φ : Λ →+* End F) :
    Sheaf J (ModuleCat.{w} Λ) where
  obj := ofEndAction Λ F.obj ((mapEndRingHom (sheafToPresheaf J AddCommGrpCat.{w}) F).comp φ)
  property :=
    Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) F.property

/-- Morphisms of a full subcategory identify with morphisms of the ambient category; this is
that identification as a map of endomorphism rings. -/
public def homMkEndRingHom {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (P : ObjectProperty D) (Z : P.FullSubcategory) : End Z.obj →+* End Z where
  toFun e := .of (ObjectProperty.homMk e.asHom)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Multiplication by a scalar on the presheaf of abelian groups underlying a presheaf of
`Λ`-modules. -/
public def presheafScalarEnd {K : Type u₂} [Category.{v₂} K] (P : K ⥤ ModuleCat.{w} Λ) :
    Λ →+* End (P ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
  (whiskerLeftEndRingHom P (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).comp
    (ModuleCat.smulNatTrans Λ)

/-- The component at `U` of `presheafScalarEnd P a` is multiplication by `a` on `P.obj U`. -/
@[simp]
public lemma presheafScalarEnd_app {K : Type u₂} [Category.{v₂} K] (P : K ⥤ ModuleCat.{w} Λ)
    (a : Λ) (U : K) : (presheafScalarEnd Λ P a).asHom.app U = ((P.obj U).smul a).asHom :=
  rfl

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- Multiplication by a scalar on the abelian sheaf underlying a sheaf of `Λ`-modules. This is
a ring map for any ring `Λ`: its values are endomorphisms of the underlying abelian sheaf, not
morphisms of sheaves of `Λ`-modules. -/
public def sheafScalarEnd (F : Sheaf J (ModuleCat.{w} Λ)) :
    Λ →+* End ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F) :=
  (homMkEndRingHom _ _).comp (presheafScalarEnd Λ F.obj)

/-- The morphism of presheaves underlying `sheafScalarEnd F a` is `presheafScalarEnd F.obj a`. -/
@[simp]
public lemma sheafScalarEnd_hom (F : Sheaf J (ModuleCat.{w} Λ)) (a : Λ) :
    (sheafScalarEnd Λ J F a).asHom.hom = (presheafScalarEnd Λ F.obj a).asHom :=
  rfl

/-- A morphism of sheaves of `Λ`-modules commutes with multiplication by a scalar on the
underlying abelian sheaves: this is its `Λ`-linearity. -/
public lemma sheafScalarEnd_naturality {F₁ F₂ : Sheaf J (ModuleCat.{w} Λ)} (φ : F₁ ⟶ F₂)
    (a : Λ) :
    (sheafScalarEnd Λ J F₁ a).asHom ≫
        (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ =
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ ≫
        (sheafScalarEnd Λ J F₂ a).asHom := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  show ((F₁.obj.obj U).smul a).asHom ≫
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map (φ.hom.app U) =
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map (φ.hom.app U) ≫ ((F₂.obj.obj U).smul a).asHom
  exact (ModuleCat.smul_naturality (φ.hom.app U) a).symm

end Sheaf

section Lift

variable (Λ : Type r) [Ring Λ] {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂}
  [Category.{v₂} C₂] (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  [J₁.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J₂.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  (G : Sheaf J₁ AddCommGrpCat.{w} ⥤ Sheaf J₂ AddCommGrpCat.{w}) [G.Additive]

/-- The action of `Λ` on the image under an additive functor `G` of the abelian sheaf
underlying a sheaf of `Λ`-modules. -/
public def liftScalarEnd (F : Sheaf J₁ (ModuleCat.{w} Λ)) :
    Λ →+* End (G.obj ((sheafCompose J₁
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F)) :=
  (mapEndRingHom G _).comp (sheafScalarEnd Λ J₁ F)

/-- The sheaf of `Λ`-modules whose underlying abelian sheaf is `G` applied to the abelian sheaf
underlying `F`. -/
public def moduleLiftObj (F : Sheaf J₁ (ModuleCat.{w} Λ)) : Sheaf J₂ (ModuleCat.{w} Λ) :=
  sheafOfEndAction Λ J₂ _ (liftScalarEnd Λ J₁ J₂ G F)

/-- The abelian sheaf underlying `moduleLiftObj G F` is `G` applied to the abelian sheaf
underlying `F`. -/
@[simp]
public lemma sheafCompose_obj_moduleLiftObj (F : Sheaf J₁ (ModuleCat.{w} Λ)) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
        (moduleLiftObj Λ J₁ J₂ G F) =
      G.obj ((sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj F) :=
  rfl

/-- The morphism of sheaves of `Λ`-modules whose underlying morphism of abelian sheaves is `G`
applied to the underlying morphism of `φ`; it is `Λ`-linear because `φ` is. -/
public def moduleLiftMap {F₁ F₂ : Sheaf J₁ (ModuleCat.{w} Λ)} (φ : F₁ ⟶ F₂) :
    moduleLiftObj Λ J₁ J₂ G F₁ ⟶ moduleLiftObj Λ J₁ J₂ G F₂ :=
  ObjectProperty.homMk (ofEndActionMap Λ _ _
    (G.map ((sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ)).hom
    fun a => congrArg InducedCategory.Hom.hom
      (((G.map_comp _ _).symm.trans (congrArg G.map
        (sheafScalarEnd_naturality Λ J₁ φ a))).trans (G.map_comp _ _)))

/-- The morphism of abelian sheaves underlying `moduleLiftMap G φ` is `G` applied to the morphism
of abelian sheaves underlying `φ`. -/
@[simp]
public lemma sheafCompose_map_moduleLiftMap {F₁ F₂ : Sheaf J₁ (ModuleCat.{w} Λ)} (φ : F₁ ⟶ F₂) :
    (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        (moduleLiftMap Λ J₁ J₂ G φ) =
      G.map ((sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map φ) :=
  rfl

/-- **The lift of an additive functor on abelian sheaves to sheaves of `Λ`-modules.** The
underlying abelian sheaf of `moduleLift G F` is `G` applied to the underlying abelian sheaf of
`F`, and its `Λ`-action is the image under `G` of multiplication by scalars on that sheaf. -/
public def moduleLift : Sheaf J₁ (ModuleCat.{w} Λ) ⥤ Sheaf J₂ (ModuleCat.{w} Λ) where
  obj := moduleLiftObj Λ J₁ J₂ G
  map := moduleLiftMap Λ J₁ J₂ G
  map_id _ := (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
    simp only [sheafCompose_map_moduleLiftMap, CategoryTheory.Functor.map_id]
    rfl)
  map_comp _ _ := (sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map_injective (by
    simp only [sheafCompose_map_moduleLiftMap, CategoryTheory.Functor.map_comp]
    rfl)

/-- Forgetting the `Λ`-module structure of the lift of `G` gives `G` on the underlying abelian
sheaves, on the nose. -/
public lemma moduleLift_comp_sheafCompose :
    moduleLift Λ J₁ J₂ G ⋙
        sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) =
      sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙ G :=
  rfl

/-- **The lift is a lift:** forgetting the `Λ`-module structure of `moduleLift G F` gives `G`
applied to the abelian sheaf underlying `F`. The isomorphism is the identity, the two
composites being the same functor. -/
public def moduleLiftForgetIso :
    moduleLift Λ J₁ J₂ G ⋙
        sheafCompose J₂ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≅
      sheafCompose J₁ (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙ G :=
  eqToIso (moduleLift_comp_sheafCompose Λ J₁ J₂ G)

end Lift

end Stacks.ModuleCatLift

end
