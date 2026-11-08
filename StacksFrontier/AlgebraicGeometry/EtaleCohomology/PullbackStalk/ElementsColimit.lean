module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Colimits over a category of elements, and isomorphisms of the indexing functor

Let `P, Q : C ⥤ Type u` be isomorphic functors. Their categories of elements are then
equivalent, and the equivalence commutes with the projections to `C` on the nose. Since an
equivalence is final, the colimit of a presheaf `F` on `C` restricted along the projection from
`P.Elements` agrees with the colimit of its restriction along the projection from `Q.Elements`.
Assembling these over all `F` gives an isomorphism of the "stalk" functors
`(whiskeringLeft _ _ _).obj (CategoryOfElements.π _).op ⋙ colim`, and restricting along
`sheafToPresheaf` gives the corresponding statement for sheaves. In particular two points of a
site with isomorphic fibre functors have isomorphic fibre functors on presheaves and on sheaves.

## Main definitions

* `CategoryTheory.CategoryOfElements.equivalenceOfNatIso` — the equivalence of categories of
  elements.
* `CategoryTheory.CategoryOfElements.presheafColimIsoOfNatIso` and
  `CategoryTheory.CategoryOfElements.sheafColimIsoOfNatIso` — the isomorphisms of stalk
  functors on presheaves and on sheaves.

## Main results

* `CategoryTheory.CategoryOfElements.ι_presheafColimIsoOfNatIso_hom` and
  `CategoryTheory.CategoryOfElements.ι_sheafColimIsoOfNatIso_hom` — the comparison sends the
  canonical map from the sections at an element to the canonical map at the transported
  element.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w v' u'

namespace CategoryTheory.CategoryOfElements

variable {C : Type v} [Category.{w} C] {P Q : C ⥤ Type u}

/-- An isomorphism of functors to types induces an equivalence of their categories of
elements. -/
public def equivalenceOfNatIso (e : P ≅ Q) : P.Elements ≌ Q.Elements where
  functor := NatTrans.mapElements e.hom
  inverse := NatTrans.mapElements e.inv
  unitIso := NatIso.ofComponents (fun X =>
    Functor.Elements.isoMk (Iso.refl X.1) (by simp)) (by
      intro X Y f
      apply Functor.Elements.hom_ext
      cat_disch)
  counitIso := NatIso.ofComponents (fun X =>
    Functor.Elements.isoMk (Iso.refl X.1) (by simp)) (by
      intro X Y f
      apply Functor.Elements.hom_ext
      cat_disch)

variable [HasColimitsOfShape P.Elementsᵒᵖ (Type (u + 1))]
  [HasColimitsOfShape Q.Elementsᵒᵖ (Type (u + 1))]

/-- The stalk functor on presheaves given by taking the colimit over a category of elements
depends on the indexing functor only through its isomorphism class. -/
public def presheafColimIsoOfNatIso (e : P ≅ Q) :
    (Functor.whiskeringLeft P.Elementsᵒᵖ Cᵒᵖ (Type (u + 1))).obj
        (CategoryOfElements.π P).op ⋙ colim ≅
      (Functor.whiskeringLeft Q.Elementsᵒᵖ Cᵒᵖ (Type (u + 1))).obj
        (CategoryOfElements.π Q).op ⋙ colim :=
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft Q.Elementsᵒᵖ Cᵒᵖ (Type (u + 1))).obj (CategoryOfElements.π Q).op)
    (Functor.Final.colimIso (equivalenceOfNatIso e).op.functor)

/-- The comparison of stalk functors on presheaves sends the germ of a section at an element to
its germ at the transported element. -/
@[reassoc]
public lemma ι_presheafColimIsoOfNatIso_hom (e : P ≅ Q) (F : Cᵒᵖ ⥤ Type (u + 1))
    (X : P.Elementsᵒᵖ) :
    colimit.ι ((CategoryOfElements.π P).op ⋙ F) X ≫
        (presheafColimIsoOfNatIso e).hom.app F =
      colimit.ι ((CategoryOfElements.π Q).op ⋙ F)
        ((equivalenceOfNatIso e).op.functor.obj X) :=
  Functor.Final.ι_colimitIso_hom (equivalenceOfNatIso e).op.functor
    ((CategoryOfElements.π Q).op ⋙ F) X

/-- The stalk functor on sheaves given by taking the colimit over a category of elements
depends on the indexing functor only through its isomorphism class. -/
public def sheafColimIsoOfNatIso (J : GrothendieckTopology C) (e : P ≅ Q) :
    (sheafToPresheaf J (Type (u + 1)) ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π P).op ⋙ colim) ≅
    (sheafToPresheaf J (Type (u + 1)) ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Q).op ⋙ colim) :=
  Functor.isoWhiskerLeft (sheafToPresheaf J (Type (u + 1))) (presheafColimIsoOfNatIso e)

/-- The comparison of stalk functors on sheaves sends the germ of a section at an element to
its germ at the transported element. -/
public lemma ι_sheafColimIsoOfNatIso_hom (J : GrothendieckTopology C) (e : P ≅ Q)
    (F : Sheaf J (Type (u + 1))) (V : P.Elements) :
    colimit.ι ((CategoryOfElements.π P).op ⋙ F.obj) (Opposite.op V) ≫
      (sheafColimIsoOfNatIso J e).hom.app F =
    colimit.ι ((CategoryOfElements.π Q).op ⋙ F.obj)
      (Opposite.op ((CategoryOfElements.map e.hom).obj V)) :=
  ι_presheafColimIsoOfNatIso_hom e F.obj (Opposite.op V)

end CategoryTheory.CategoryOfElements

/-! ### Two points with isomorphic fibres have isomorphic fibre functors -/

namespace CategoryTheory.GrothendieckTopology.Point

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryOfElements

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{u, u} A]

/-- Two points of a site with isomorphic fibre functors have isomorphic fibre functors on
presheaves. -/
public def presheafFiberIsoOfFiberIso (Φ Ψ : Point.{u} J) (e : Φ.fiber ≅ Ψ.fiber) :
    Φ.presheafFiber (A := A) ≅ Ψ.presheafFiber :=
  Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft Ψ.fiber.Elementsᵒᵖ Cᵒᵖ A).obj (CategoryOfElements.π Ψ.fiber).op)
    (Functor.Final.colimIso (equivalenceOfNatIso e).op.functor)

/-- Two points of a site with isomorphic fibre functors have isomorphic fibre functors on
sheaves. -/
public def sheafFiberIsoOfFiberIso (Φ Ψ : Point.{u} J) (e : Φ.fiber ≅ Ψ.fiber) :
    Φ.sheafFiber (A := A) ≅ Ψ.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafFiberIsoOfFiberIso Φ Ψ e)

/-- The comparison of fibre functors induced by an isomorphism of fibre functors carries the germ
of a section at a lift of the one point to its germ at the corresponding lift of the other. -/
public theorem toPresheafFiber_presheafFiberIsoOfFiberIso (Φ Ψ : Point.{u} J)
    (e : Φ.fiber ≅ Ψ.fiber) (P : Cᵒᵖ ⥤ A) (V : C) (v : Φ.fiber.obj V) :
    Φ.toPresheafFiber V v P ≫ (presheafFiberIsoOfFiberIso Φ Ψ e (A := A)).hom.app P =
      Ψ.toPresheafFiber V (e.hom.app V v) P :=
  Functor.Final.ι_colimitIso_hom (equivalenceOfNatIso e).op.functor
    ((CategoryOfElements.π Ψ.fiber).op ⋙ P) (Opposite.op (Φ.fiber.elementsMk V v))

/-- `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberIsoOfFiberIso` for
the inverse comparison. -/
public theorem toPresheafFiber_presheafFiberIsoOfFiberIso_inv (Φ Ψ : Point.{u} J)
    (e : Φ.fiber ≅ Ψ.fiber) (P : Cᵒᵖ ⥤ A) (V : C) (y : Ψ.fiber.obj V) :
    Ψ.toPresheafFiber V y P ≫ (presheafFiberIsoOfFiberIso Φ Ψ e (A := A)).inv.app P =
      Φ.toPresheafFiber V (e.inv.app V y) P := by
  have h := toPresheafFiber_presheafFiberIsoOfFiberIso Φ Ψ e P V (e.inv.app V y)
  have hy : e.hom.app V (e.inv.app V y) = y :=
    congrFun (congrArg (fun k => (ConcreteCategory.hom k : _ → _))
      (NatTrans.congr_app e.inv_hom_id V)) y
  rw [hy] at h
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end CategoryTheory.GrothendieckTopology.Point


end
