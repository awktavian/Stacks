module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by an initial object along an open immersion

Let `X` be a topological space and let `j : U → X` be the inclusion of an open subset.
For a category `C` with an initial object `e` and a presheaf `F` on `U` with values in
`C`, the *extension of `F` by `e`* is the presheaf on `X` given by

* `V ↦ F(V)` when `V ⊆ U`,
* `V ↦ e` when `V ⊄ U`,

with the obvious restriction maps. When `C` admits sheafification, the extension by `e`
of a sheaf on `U` is the sheafification of this presheaf.

## Main definitions

* `TopCat.Presheaf.extendByInitial`: the presheaf `j_{p!} F` above.
* `TopCat.Presheaf.extendByInitialFunctor`: `j_{p!}` as a functor `PSh(U) ⥤ PSh(X)`.
* `TopCat.Presheaf.restrictToOpen`: the restriction functor `j_p : PSh(X) ⥤ PSh(U)`,
  `(j_p G)(W) = G(j(W))`.
* `TopCat.Presheaf.extendByInitialSheafify`: the sheafification `j_!` of `j_{p!}`.
* `TopCat.Presheaf.extendByInitialSheaf`: `j_! : Sh(U) ⥤ Sh(X)`.

The restriction functor `j^{-1} : Sh(X) ⥤ Sh(U)` on sheaves is Mathlib's
`TopologicalSpace.Opens.sheafRestrict`.

## Main results

* `TopCat.Presheaf.extendByInitialAdjunction`: `j_{p!}` is left adjoint to `j_p`.
* `TopCat.Presheaf.extendByInitialSheafAdjunction`: `j_!` is left adjoint to `j^{-1}`.
* `TopCat.Presheaf.restrictExtendByInitialIso`: `j_p ∘ j_{p!} ≅ 𝟭`, i.e. the extension by
  `e` of a presheaf on `U` restricts back to that presheaf.
* `TopCat.Presheaf.restrictExtendByInitialSheafIso`: `j^{-1} ∘ j_! ≅ 𝟭`, the same statement
  for sheaves.
* `TopCat.Presheaf.extendByInitialSheafFullyFaithful`: `j_!` is fully faithful.
* `TopCat.Presheaf.ExtensionByInitial.isInitialStalkExtendByInitial` and
  `TopCat.Presheaf.isInitialStalkExtendByInitialSheafify`: the stalk of `j_{p!}F`, resp. of
  `j_!F`, at a point outside `U` is an initial object (`∅` for sheaves of sets, and a zero
  object when `C` has one, which is `TopCat.Presheaf.isZero_stalk_extendByInitialSheafify`).
* `TopCat.Presheaf.ExtensionByInitial.stalkExtendByInitialIso` and
  `TopCat.Presheaf.stalkExtendByInitialSheafifyIso`: at a point of `U` the stalk of `j_{p!}F`,
  resp. of `j_!F`, is the stalk of `F`.

Since the zero object of a category of algebraic structures (abelian groups, modules over
a ring, …) is in particular initial, this covers the classical *extension by zero*.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

namespace ExtensionByInitial

variable {C : Type u} [Category.{v} C] [HasInitial C] {X : TopCat.{w}} (U : Opens X)

/-- The open subset `U` of `X`, viewed as a topological space via the subspace topology.
The open immersion `j : U → X` is `U.inclusion'`. -/
abbrev sp : TopCat.{w} := (Opens.toTopCat X).obj U

variable (F : Presheaf C (sp U))

open Classical in
/-- The value of the extension by an initial object at an open `V ⊆ X`: the sections of `F`
over `j⁻¹ V` if `V ⊆ U`, and the initial object otherwise. -/
noncomputable def obj (V : (Opens X)ᵒᵖ) : C :=
  if V.unop ≤ U then F.obj (op ((Opens.map U.inclusion').obj V.unop)) else ⊥_ C

/-- On an open contained in `U`, the extension by an initial object has the sections of `F`. -/
lemma obj_of_le {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    obj U F V = F.obj (op ((Opens.map U.inclusion').obj V.unop)) := by
  rw [obj, ite_eq_left hV]

/-- On an open not contained in `U`, the sections of the extension by an initial object are
the chosen initial object `⊥_ C` itself. -/
lemma obj_of_not_le {V : (Opens X)ᵒᵖ} (hV : ¬ V.unop ≤ U) : obj U F V = ⊥_ C := by
  rw [obj, ite_eq_right hV]

/-- On an open not contained in `U`, the extension by an initial object is initial. -/
noncomputable def isInitial_obj {V : (Opens X)ᵒᵖ} (hV : ¬ V.unop ≤ U) :
    IsInitial (obj U F V) := by
  rw [obj_of_not_le U F hV]; exact initialIsInitial

/-- Two maps out of the extension by an initial object agree if they agree on opens in `U`. -/
private lemma ext_of_le {V : (Opens X)ᵒᵖ} {Y : C} {f g : obj U F V ⟶ Y}
    (h : V.unop ≤ U → f = g) : f = g := by
  by_cases hV : V.unop ≤ U
  · exact h hV
  · exact (isInitial_obj U F hV).hom_ext _ _

open Classical in
/-- The restriction maps of the extension by an initial object. -/
noncomputable def map {V' V : (Opens X)ᵒᵖ} (f : V' ⟶ V) : obj U F V' ⟶ obj U F V :=
  if hV' : V'.unop ≤ U then
    eqToHom (obj_of_le U F hV') ≫
      F.map ((Opens.map U.inclusion').map (homOfLE f.unop.le)).op ≫
      eqToHom (obj_of_le U F (f.unop.le.trans hV')).symm
  else (isInitial_obj U F hV').to _

/-- The restriction maps of the extension by an initial object preserve identities. -/
lemma map_id (V : (Opens X)ᵒᵖ) : map U F (𝟙 V) = 𝟙 (obj U F V) := by
  refine ext_of_le U F fun hV ↦ ?_
  rw [map, dite_eq_left hV, show ((Opens.map U.inclusion').map (homOfLE (𝟙 V).unop.le)).op =
    𝟙 _ from Subsingleton.elim _ _]
  simp

/-- The restriction maps of the extension by an initial object are compatible with
composition. -/
lemma map_comp {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) :
    map U F (f ≫ g) = map U F f ≫ map U F g := by
  refine ext_of_le U F fun hV ↦ ?_
  have hW : W.unop ≤ U := f.unop.le.trans hV
  rw [map, map, map, dite_eq_left hV, dite_eq_left hV, dite_eq_left hW]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Functor.map_comp_assoc, ← op_comp, ← Functor.map_comp]
  congr 2

end ExtensionByInitial

open ExtensionByInitial

variable {C : Type u} [Category.{v} C] [HasInitial C] {X : TopCat.{w}} (U : Opens X)

/-- **Extension by an initial object.** For `j : U → X` the inclusion of an open subset,
`C` a category with initial object `e`, and `F` a presheaf on `U` with values in `C`, this is
the presheaf `j_{p!}F` on `X` with `j_{p!}F(V) = F(V)` for `V ⊆ U` and `j_{p!}F(V) = e`
otherwise, with the obvious restriction maps.

When `C` is a category of algebraic structures its zero object is initial, so this is the
classical extension by zero of an abelian presheaf; and the initial object of `Type` is the
empty type, so this is also the extension by the empty set of a presheaf of sets. -/
@[stacks 00A4 "(1), (3)", stacks 00A2 "(1)", implicit_reducible]
noncomputable def extendByInitial (F : Presheaf C (sp U)) : Presheaf C X where
  obj V := obj U F V
  map f := map U F f
  map_id V := map_id U F V
  map_comp f g := map_comp U F f g

/-- The restriction maps of `extendByInitial U F` are the maps `ExtensionByInitial.map U F`. -/
lemma extendByInitial_map (F : Presheaf C (sp U)) {V' V : (Opens X)ᵒᵖ} (f : V' ⟶ V) :
    (extendByInitial U F).map f = map U F f :=
  rfl

namespace ExtensionByInitial

variable {U}

/-- On an open contained in `U`, `extendByInitial U F` has the sections of `F` over the
corresponding open of `U`. -/
lemma extendByInitial_obj_of_le (F : Presheaf C (sp U)) {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    (extendByInitial U F).obj V = F.obj (op ((Opens.map U.inclusion').obj V.unop)) :=
  obj_of_le U F hV

/-- The image functor on opens attached to the open embedding `j : U → X`. -/
noncomputable abbrev imF (U : Opens X) : Opens (sp U) ⥤ Opens X := U.isOpenEmbedding.functor

/-- The image under `j` of an open subset of `U` is contained in `U`. -/
lemma imF_le (U : Opens X) (W : Opens (sp U)) : (imF U).obj W ≤ U := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- For `V ⊆ U`, the image under `j` of the preimage `j⁻¹ V` is `V` again. -/
lemma imF_map_eq {U : Opens X} {V : Opens X} (hV : V ≤ U) :
    (imF U).obj ((Opens.map U.inclusion').obj V) = V := by
  rw [Opens.functor_map_eq_inf, inf_of_le_left hV]

/-- The extension by an initial object recovers `F` on the image of an open of `U`. -/
lemma obj_imF (F : Presheaf C (sp U)) (W : Opens (sp U)) :
    obj U F (op ((imF U).obj W)) = F.obj (op W) := by
  rw [obj_of_le U F (imF_le U W)]
  exact congrArg (fun Z ↦ F.obj (op Z)) (Opens.map_functor_eq W)

variable (U)

open Classical in
/-- The component at `V` of `j_{p!}η` for a morphism `η : F ⟶ G` of presheaves on `U`. -/
noncomputable def appMap {F G : Presheaf C (sp U)} (η : F ⟶ G) (V : (Opens X)ᵒᵖ) :
    obj U F V ⟶ obj U G V :=
  if hV : V.unop ≤ U then
    eqToHom (obj_of_le U F hV) ≫ η.app (op ((Opens.map U.inclusion').obj V.unop)) ≫
      eqToHom (obj_of_le U G hV).symm
  else (isInitial_obj U F hV).to _

/-- The components `appMap U η` commute with the restriction maps of the extension. -/
lemma appMap_naturality {F G : Presheaf C (sp U)} (η : F ⟶ G) {V' V : (Opens X)ᵒᵖ}
    (f : V' ⟶ V) :
    map U F f ≫ appMap U η V = appMap U η V' ≫ map U G f := by
  refine ext_of_le U F fun hV' ↦ ?_
  have hV : V.unop ≤ U := f.unop.le.trans hV'
  simp only [map, appMap, dite_eq_left hV, dite_eq_left hV']
  have hnat := η.naturality ((Opens.map U.inclusion').map (homOfLE f.unop.le)).op
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% hnat]

/-- `j_{p!}η : j_{p!}F ⟶ j_{p!}G`. -/
noncomputable def mapNat {F G : Presheaf C (sp U)} (η : F ⟶ G) :
    extendByInitial U F ⟶ extendByInitial U G where
  app V := appMap U η V
  naturality _ _ f := appMap_naturality U η f

/-- The components of `mapNat U η` are the maps `appMap U η`. -/
lemma mapNat_app {F G : Presheaf C (sp U)} (η : F ⟶ G) (V : (Opens X)ᵒᵖ) :
    (mapNat U η).app V = appMap U η V :=
  rfl

/-- `j_{p!}` sends the identity of `F` to the identity of `j_{p!}F`, componentwise. -/
lemma appMap_id (F : Presheaf C (sp U)) (V : (Opens X)ᵒᵖ) :
    appMap U (𝟙 F) V = 𝟙 (obj U F V) := by
  refine ext_of_le U F fun hV ↦ ?_
  have h : (𝟙 F : F ⟶ F).app (op ((Opens.map U.inclusion').obj V.unop)) = 𝟙 _ := rfl
  rw [appMap, dite_eq_left hV, h]
  simp

/-- `j_{p!}` is compatible with composition of morphisms of presheaves, componentwise. -/
lemma appMap_comp {F G H : Presheaf C (sp U)} (η : F ⟶ G) (θ : G ⟶ H) (V : (Opens X)ᵒᵖ) :
    appMap U (η ≫ θ) V = appMap U η V ≫ appMap U θ V := by
  refine ext_of_le U F fun hV ↦ ?_
  have h : (η ≫ θ).app (op ((Opens.map U.inclusion').obj V.unop))
      = η.app (op ((Opens.map U.inclusion').obj V.unop))
        ≫ θ.app (op ((Opens.map U.inclusion').obj V.unop)) := rfl
  rw [appMap, appMap, appMap, dite_eq_left hV, dite_eq_left hV, dite_eq_left hV, h]
  simp

end ExtensionByInitial

/-- **Extension by an initial object, as a functor.** `j_{p!} : PSh(U) ⥤ PSh(X)`. -/
@[stacks 00A4 "(1), (3)", stacks 00A2 "(1)", implicit_reducible]
noncomputable def extendByInitialFunctor : Presheaf C (sp U) ⥤ Presheaf C X where
  obj F := extendByInitial U F
  map η := mapNat U η
  map_id F := NatTrans.ext <| funext fun V ↦ appMap_id U F V
  map_comp η θ := NatTrans.ext <| funext fun V ↦ appMap_comp U η θ V

/-- `extendByInitialFunctor U` acts on morphisms by `mapNat U`. -/
lemma extendByInitialFunctor_map {F G : Presheaf C (sp U)} (η : F ⟶ G) :
    (extendByInitialFunctor U).map η = mapNat U η :=
  rfl

/-- The restriction functor `j_p : PSh(X) ⥤ PSh(U)` for `j : U → X` the inclusion of an
open subset: `(j_p G)(W) = G(j(W))`. -/
@[ega "0 3.1.5"]
noncomputable abbrev restrictToOpen : Presheaf C X ⥤ Presheaf C (sp U) :=
  (Functor.whiskeringLeft _ _ _).obj (imF U).op

namespace ExtensionByInitial

/-- For `V ⊆ U`, the image under `j` of `j⁻¹ V` is `V` again, in `(Opens X)ᵒᵖ`. -/
lemma imF_map_op_eq {U : Opens X} {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    (op ((imF U).obj ((Opens.map U.inclusion').obj V.unop)) : (Opens X)ᵒᵖ) = V :=
  congrArg op (imF_map_eq hV)

/-- **`j_p j_{p!} F = F`** at a fixed presheaf `F`: the extension by an initial object
restricts back to `F`. -/
noncomputable def restrictExtendIso (F : Presheaf C (sp U)) :
    (restrictToOpen U).obj (extendByInitial U F) ≅ F :=
  NatIso.ofComponents (fun W ↦ eqToIso (obj_imF F W.unop)) (fun {W W'} g ↦ by
    simp only [eqToIso.hom, Functor.whiskeringLeft_obj_obj, Functor.comp_map, Functor.op_map,
      extendByInitial_map]
    rw [map]
    simp only [Functor.op_obj, unop_op]
    rw [dite_eq_left (imF_le U W.unop)]
    have hW : (Opens.map U.inclusion').obj ((imF U).obj W.unop) = W.unop :=
      Opens.map_functor_eq W.unop
    have hW' : (Opens.map U.inclusion').obj ((imF U).obj W'.unop) = W'.unop :=
      Opens.map_functor_eq W'.unop
    have hmap : ((Opens.map U.inclusion').map (homOfLE ((imF U).map g.unop).op.unop.le)).op
        = eqToHom (by rw [hW]) ≫ g ≫ eqToHom (by rw [hW']) := Subsingleton.elim _ _
    rw [hmap]
    simp [eqToHom_map])

/-- Forward direction of the adjunction bijection: restrict a map `j_{p!}F ⟶ G` to the
opens of `U`, using `j_p j_{p!} F = F`. -/
noncomputable def homEquivFun {F : Presheaf C (sp U)} {G : Presheaf C X}
    (α : extendByInitial U F ⟶ G) : F ⟶ (restrictToOpen U).obj G :=
  (restrictExtendIso U F).inv ≫ (restrictToOpen U).map α

/-- The component of `homEquivFun U α` at an open `W` of `U` is the component of `α` at the
image `j(W)`, read through the identification `j_{p!}F(j W) = F(W)`. -/
lemma homEquivFun_app {F : Presheaf C (sp U)} {G : Presheaf C X}
    (α : extendByInitial U F ⟶ G) (W : (Opens (sp U))ᵒᵖ) :
    (homEquivFun U α).app W
      = eqToHom (obj_imF F W.unop).symm ≫ α.app (op ((imF U).obj W.unop)) :=
  rfl

open Classical in
/-- The component at `V` of the backward direction of the adjunction bijection. -/
noncomputable def homEquivInvApp {F : Presheaf C (sp U)} {G : Presheaf C X}
    (β : F ⟶ (restrictToOpen U).obj G) (V : (Opens X)ᵒᵖ) : obj U F V ⟶ G.obj V :=
  if hV : V.unop ≤ U then
    eqToHom (obj_of_le U F hV) ≫ β.app (op ((Opens.map U.inclusion').obj V.unop)) ≫
      eqToHom (congrArg G.obj (imF_map_op_eq hV))
  else (isInitial_obj U F hV).to _

/-- The components `homEquivInvApp U β` commute with the restriction maps. -/
lemma homEquivInvApp_naturality {F : Presheaf C (sp U)} {G : Presheaf C X}
    (β : F ⟶ (restrictToOpen U).obj G) {V' V : (Opens X)ᵒᵖ} (f : V' ⟶ V) :
    map U F f ≫ homEquivInvApp U β V = homEquivInvApp U β V' ≫ G.map f := by
  refine ext_of_le U F fun hV' ↦ ?_
  have hV : V.unop ≤ U := f.unop.le.trans hV'
  rw [map, homEquivInvApp, homEquivInvApp, dite_eq_left hV', dite_eq_left hV', dite_eq_left hV]
  have hnat := β.naturality ((Opens.map U.inclusion').map (homOfLE f.unop.le)).op
  have hsq : ((restrictToOpen U).obj G).map
        ((Opens.map U.inclusion').map (homOfLE f.unop.le)).op
        ≫ eqToHom (congrArg G.obj (imF_map_op_eq hV))
      = eqToHom (congrArg G.obj (imF_map_op_eq hV')) ≫ G.map f := by
    simp only [Functor.whiskeringLeft_obj_obj, Functor.comp_map]
    rw [← eqToHom_map G (imF_map_op_eq hV), ← eqToHom_map G (imF_map_op_eq hV'),
      ← G.map_comp, ← G.map_comp]
    exact congrArg G.map (Subsingleton.elim _ _)
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% hnat, hsq]

/-- Backward direction of the adjunction bijection: extend a map `F ⟶ j_p G` by the unique
maps out of the initial object. -/
noncomputable def homEquivInv {F : Presheaf C (sp U)} {G : Presheaf C X}
    (β : F ⟶ (restrictToOpen U).obj G) : extendByInitial U F ⟶ G where
  app V := homEquivInvApp U β V
  naturality _ _ f := homEquivInvApp_naturality U β f

/-- The components of `homEquivInv U β` are the maps `homEquivInvApp U β`. -/
lemma homEquivInv_app {F : Presheaf C (sp U)} {G : Presheaf C X}
    (β : F ⟶ (restrictToOpen U).obj G) (V : (Opens X)ᵒᵖ) :
    (homEquivInv U β).app V = homEquivInvApp U β V :=
  rfl

/-- `homEquivInv` is a left inverse of `homEquivFun`: a morphism `j_{p!}F ⟶ G` is determined by
its restriction to the opens inside `U`. -/
lemma homEquivInv_homEquivFun {F : Presheaf C (sp U)} {G : Presheaf C X}
    (α : extendByInitial U F ⟶ G) : homEquivInv U (homEquivFun U α) = α := by
  apply NatTrans.ext; funext V
  rw [homEquivInv_app]
  refine ext_of_le U F fun hV ↦ ?_
  rw [homEquivInvApp, dite_eq_left hV, homEquivFun_app]
  have hnat := α.naturality (eqToHom (imF_map_op_eq hV))
  rw [eqToHom_map, eqToHom_map] at hnat
  simp only [Category.assoc]
  rw [← hnat]
  simp

/-- `homEquivInv` is a right inverse of `homEquivFun`: extending a morphism `F ⟶ j_p G` to
`j_{p!}F ⟶ G` and restricting it again returns the original morphism. -/
lemma homEquivFun_homEquivInv {F : Presheaf C (sp U)} {G : Presheaf C X}
    (β : F ⟶ (restrictToOpen U).obj G) : homEquivFun U (homEquivInv U β) = β := by
  apply NatTrans.ext; funext W
  rw [homEquivFun_app, homEquivInv_app, homEquivInvApp, dite_eq_left (imF_le U W.unop)]
  have q : (op ((Opens.map U.inclusion').obj ((imF U).obj W.unop)) : (Opens (sp U))ᵒᵖ) = W :=
    congrArg op (Opens.map_functor_eq W.unop)
  have hnat := β.naturality (eqToHom q)
  rw [eqToHom_map] at hnat
  have hkey : ((restrictToOpen U).obj G).map (eqToHom q)
      = eqToHom (congrArg G.obj (imF_map_op_eq (imF_le U W.unop))) := by
    simp only [Functor.whiskeringLeft_obj_obj, Functor.comp_map]
    rw [eqToHom_map, eqToHom_map]
  rw [hkey] at hnat
  rw [← hnat]
  simp

end ExtensionByInitial

/-- **The extension-by-zero/restriction adjunction, presheaf level.** For `j : U → X` the
inclusion of an open subset, `j_{p!}` is a left adjoint of the restriction functor `j_p`. -/
@[stacks 00A5 "(1)",
  stacks 00A3 "(1) j_{p!} is a left adjoint to the restriction functor j_p",
  sga "4 IV 11.3.1" "presheaf, constant ring"]
noncomputable def extendByInitialAdjunction :
    extendByInitialFunctor (C := C) U ⊣ restrictToOpen U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G ↦
        { toFun := homEquivFun U
          invFun := homEquivInv U
          left_inv := homEquivInv_homEquivFun U
          right_inv := homEquivFun_homEquivInv U }
      homEquiv_naturality_left_symm := fun {F' F G} f g ↦ by
        apply NatTrans.ext; funext V
        simp only [Equiv.coe_fn_symm_mk, TopCat.Presheaf.comp_app, homEquivInv_app,
          extendByInitialFunctor_map, mapNat_app]
        by_cases hV : V.unop ≤ U
        · rw [homEquivInvApp, homEquivInvApp, appMap, dite_eq_left hV, dite_eq_left hV,
            dite_eq_left hV, TopCat.Presheaf.comp_app]
          simp
        · exact (isInitial_obj U F' hV).hom_ext _ _
      homEquiv_naturality_right := fun {F G G'} f g ↦ by
        simp only [Equiv.coe_fn_mk, homEquivFun]
        rw [Functor.map_comp, Category.assoc] }

/-- **`j_p j_{p!} = id`.** The extension by an initial object of a presheaf on `U` restricts
back to that presheaf, naturally in the presheaf. -/
@[stacks 00A5 "(4)", stacks 00A3 "(4) on presheaves on U we have j_p j_{p!} = id"]
noncomputable def restrictExtendByInitialIso :
    extendByInitialFunctor (C := C) U ⋙ restrictToOpen U ≅ 𝟭 (Presheaf C (sp U)) :=
  NatIso.ofComponents (fun F ↦ restrictExtendIso U F) (fun {F F'} η ↦ by
    apply NatTrans.ext; funext W
    simp only [TopCat.Presheaf.comp_app, Functor.comp_map, extendByInitialFunctor_map,
      Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app, mapNat_app, restrictExtendIso,
      NatIso.ofComponents_hom_app, eqToIso.hom, Functor.op_obj, Functor.id_map]
    rw [appMap, dite_eq_left (imF_le U W.unop)]
    have q : (op ((Opens.map U.inclusion').obj ((imF U).obj W.unop)) : (Opens (sp U))ᵒᵖ) = W :=
      congrArg op (Opens.map_functor_eq W.unop)
    have hnat := η.naturality (eqToHom q)
    rw [eqToHom_map, eqToHom_map] at hnat
    simp only [unop_op, Category.assoc, eqToHom_trans]
    rw [← hnat]
    simp)

/-! ### Restriction as a left adjoint

For an open immersion `j`, restriction sits in an adjoint triple `j_! ⊣ j^{-1} ⊣ j_*`, and the
pushforward `j_*` is fully faithful. -/

section Pushforward

namespace ExtensionByInitial

/-- Restriction to the opens of `U` is a left adjoint of the pushforward `j_*`: the poset
adjunction `imF U ⊣ Opens.map j`, whiskered into presheaves. -/
noncomputable def restrictToOpenPushforwardAdjunction :
    restrictToOpen (C := C) U ⊣ Presheaf.pushforward C U.inclusion' :=
  Adjunction.whiskerLeft C (U.isOpenEmbedding.isOpenMap.adjunction.op)

/-- For an open immersion `j`, the presheaf pushforward `j_*` is fully faithful. -/
noncomputable def pushforwardFullyFaithful :
    (Presheaf.pushforward C U.inclusion').FullyFaithful := by
  have : Mono U.inclusion' := (TopCat.mono_iff_injective _).2 Subtype.val_injective
  have hladj : IsIso (Adjunction.whiskerLeft C
      (U.isOpenEmbedding.isOpenMap.adjunction.op)).counit := by
    have happ : ∀ F, IsIso ((Adjunction.whiskerLeft C
        (U.isOpenEmbedding.isOpenMap.adjunction.op)).counit.app F) := by
      intro F
      have happ2 : ∀ z, IsIso (((Adjunction.whiskerLeft C
          (U.isOpenEmbedding.isOpenMap.adjunction.op)).counit.app F).app z) := by
        intro z
        rw [Adjunction.whiskerLeft_counit_app_app]
        exact Functor.map_isIso F _
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  exact @Adjunction.fullyFaithfulROfIsIsoCounit _ _ _ _ _ _ _ hladj

/-- For an open immersion `j`, the sheaf pushforward `j_*` is fully faithful. -/
noncomputable def sheafPushforwardFullyFaithful :
    (Sheaf.pushforward C U.inclusion').FullyFaithful := by
  have hcomp : (Sheaf.pushforward C U.inclusion' ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) C).FullyFaithful :=
    (fullyFaithfulSheafToPresheaf _ C).comp (pushforwardFullyFaithful (C := C) U)
  letI hF : (sheafToPresheaf (Opens.grothendieckTopology X) C).Faithful := inferInstance
  exact @Functor.FullyFaithful.ofCompFaithful _ _ _ _ _ _ _ _ hF hcomp

/-- `j^{-1} ⊣ j_*` on sheaves, obtained by restricting the presheaf-level adjunction along the
fully faithful inclusions of sheaves into presheaves. -/
noncomputable def sheafRestrictPushforwardAdjunction :
    Opens.sheafRestrict (C := C) U ⊣ Sheaf.pushforward C U.inclusion' :=
  Adjunction.restrictFullyFaithful (restrictToOpenPushforwardAdjunction U)
    (fullyFaithfulSheafToPresheaf _ C) (fullyFaithfulSheafToPresheaf _ C)
    (Iso.refl _) (Iso.refl _)

end ExtensionByInitial

end Pushforward

section Sheafify

variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- **Extension by an initial object for sheaves.** The extension `j_! F` of a sheaf `F` on
`U` is the sheafification of the presheaf `j_{p!}F`.

For a category of algebraic structures the initial object is the zero object, so this is the
classical extension by zero of a sheaf; for `C = Type` the initial object is the empty type, so
this is the extension by the empty set. -/
@[stacks 00A4 "(2)", stacks 00A2 "(2)", implicit_reducible, sga "4 III 1.9.2" "more general"]
noncomputable def extendByInitialSheafify :
    Presheaf C (sp U) ⥤ TopCat.Sheaf C X :=
  extendByInitialFunctor U ⋙ presheafToSheaf (Opens.grothendieckTopology X) C

/-- **Extension by an initial object, as a functor on sheaves.** `j_! : Sh(U) ⥤ Sh(X)` sends a
sheaf `F` on `U` to the sheafification of `j_{p!}F`. -/
@[stacks 00A4 "(2)", stacks 00A2 "(2)", implicit_reducible, sga "4 III 5.3" "opens of a top. space"]
noncomputable def extendByInitialSheaf : TopCat.Sheaf C (sp U) ⥤ TopCat.Sheaf C X :=
  sheafToPresheaf _ _ ⋙ extendByInitialSheafify U

/-- **The extension-by-zero/restriction adjunction, sheaf level.** `j_!` is a left adjoint of
the restriction functor `j^{-1} : Sh(X) ⥤ Sh(U)`, i.e.
`Mor_{Sh(X)}(j_!F, G) = Mor_{Sh(U)}(F, G|_U)` bifunctorially.

Here `j^{-1}` is `TopologicalSpace.Opens.sheafRestrict U`, which is `G ↦ (W ↦ G(j(W)))` with no
sheafification. -/
@[stacks 00A5 "(2)",
  stacks 00A3 "(2) j_! is a left adjoint to restriction on sheaves",
  sga "4 III 5.3" "j_! ⊣ j^*, opens site",
  sga "4 IV 11.3.1" "sheaves on a space",
  sga "4 XVII 5.1.1" "topological spaces"]
noncomputable def extendByInitialSheafAdjunction :
    extendByInitialSheaf U ⊣ Opens.sheafRestrict (C := C) U :=
  Adjunction.restrictFullyFaithful
    ((extendByInitialAdjunction U).comp (sheafificationAdjunction _ C))
    (fullyFaithfulSheafToPresheaf _ C) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

namespace ExtensionByInitial

/-- **The adjoint triple of an open immersion**, `j_! ⊣ j^{-1} ⊣ j_*` on sheaves. -/
noncomputable def openImmersionTriple :
    Adjunction.Triple (extendByInitialSheaf U) (Opens.sheafRestrict (C := C) U)
      (Sheaf.pushforward C U.inclusion') :=
  ⟨extendByInitialSheafAdjunction U, sheafRestrictPushforwardAdjunction U⟩

/-- The unit of `j_! ⊣ j^{-1}` is invertible. -/
theorem isIso_unit_extendByInitialSheafAdjunction :
    IsIso (extendByInitialSheafAdjunction (C := C) U).unit := by
  rw [show (extendByInitialSheafAdjunction (C := C) U) = (openImmersionTriple U).adj₁ from rfl,
    (openImmersionTriple U).isIso_unit_iff_isIso_counit]
  have := (sheafPushforwardFullyFaithful (C := C) U).full
  have := (sheafPushforwardFullyFaithful (C := C) U).faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

end ExtensionByInitial

/-- **`j^{-1} j_! = id`.** The extension by an initial object of a sheaf on `U` restricts back
to that sheaf, naturally in the sheaf. This is the unit of `j_! ⊣ j^{-1}`, inverted. -/
@[stacks 00A5 "(5)", stacks 00A3 "(5) on sheaves on U we have j^{-1} j_! = id"]
noncomputable def restrictExtendByInitialSheafIso :
    extendByInitialSheaf U ⋙ Opens.sheafRestrict (C := C) U ≅ 𝟭 _ :=
  haveI := ExtensionByInitial.isIso_unit_extendByInitialSheafAdjunction (C := C) U
  (asIso (extendByInitialSheafAdjunction (C := C) U).unit).symm

/-- `j_! : Sh(U) ⥤ Sh(X)` is fully faithful. -/
@[stacks 00A8, sga "4 IV 11.3.1" "special case"]
noncomputable def extendByInitialSheafFullyFaithful :
    (extendByInitialSheaf (C := C) U).FullyFaithful :=
  (ExtensionByInitial.openImmersionTriple U).fullyFaithfulEquiv.symm
    (ExtensionByInitial.sheafPushforwardFullyFaithful U)

end Sheafify

/-! ### Stalks of the extension by an initial object -/

section Stalks

variable {C : Type u} [Category.{v} C] [HasInitial C] [HasColimits.{v} C] {X : TopCat.{v}}
  (U : Opens X)

namespace ExtensionByInitial

/-- A colimit of a diagram all of whose values are initial objects is again initial. -/
noncomputable def isInitialColimit {J : Type v} [Category.{v} J] (D : J ⥤ C) [HasColimit D]
    (hD : ∀ j, IsInitial (D.obj j)) : IsInitial (colimit D) :=
  IsInitial.ofUniqueHom
    (fun Y ↦ colimit.desc D
      { pt := Y
        ι := { app := fun j ↦ (hD j).to Y
               naturality := fun _ _ _ ↦ (hD _).hom_ext _ _ } })
    (fun _ _ ↦ colimit.hom_ext fun j ↦ (hD j).hom_ext _ _)

/-- **The stalk of `j_{p!}F` at a point outside `U` is initial.** For presheaves of sets this
reads `(j_{p!}F)_x = ∅`. -/
noncomputable def isInitialStalkExtendByInitial (F : Presheaf C (sp U)) {x : X} (hx : x ∉ U) :
    IsInitial ((extendByInitial U F).stalk x) := by
  change IsInitial (colimit ((OpenNhds.inclusion x).op ⋙ extendByInitial U F))
  exact isInitialColimit _ fun V ↦ isInitial_obj U F fun hle ↦ hx (hle V.unop.2)

/-- **The stalk of `j_{p!}F` at a point of `U` is the stalk of `F`.** -/
noncomputable def stalkExtendByInitialIso (F : Presheaf C (sp U)) (x : sp U) :
    (extendByInitial U F).stalk (U.inclusion' x) ≅ F.stalk x :=
  stalkPullbackIso C U.inclusion' (extendByInitial U F) x ≪≫
    (stalkFunctor C x).mapIso
      (U.isOpenEmbedding.isOpenMap.pullbackObjIso (extendByInitial U F) ≪≫
        restrictExtendIso U F)

end ExtensionByInitial

section SheafifyStalks

variable [HasTerminal C] [HasWeakSheafify (Opens.grothendieckTopology X) C]

namespace ExtensionByInitial

/-- **Sheafification does not change stalks.** The unit `P ⟶ P^#` of the sheafification
adjunction induces an isomorphism on every stalk. -/
noncomputable def stalkSheafifyIso (P : Presheaf C X) (x : X) :
    P.stalk x ≅
      stalk ((sheafToPresheaf (Opens.grothendieckTopology X) C).obj
        ((presheafToSheaf (Opens.grothendieckTopology X) C).obj P)) x := by
  have h : IsIso ((stalkFunctor C x).map
      ((sheafificationAdjunction (Opens.grothendieckTopology X) C).unit.app P)) := by
    rw [sheafificationAdjunction_unit_app]
    exact stalkFunctor_map_unit_toSheafify_isIso x C P
  exact @asIso _ _ _ _ _ h

omit [HasInitial C] in
/-- The forward map of `TopCat.Presheaf.ExtensionByInitial.stalkSheafifyIso` is the map on stalks
induced by the sheafification unit `P ⟶ P^#`. -/
theorem stalkSheafifyIso_hom (P : Presheaf C X) (x : X) :
    (stalkSheafifyIso P x).hom =
      (stalkFunctor C x).map (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) :=
  rfl

end ExtensionByInitial

open ExtensionByInitial in
/-- The stalk of `j_!F` at a point `x ∉ U` is an initial object.
For sheaves of sets the initial object is `∅`, so this is `(j_!F)_x = ∅`; for abelian sheaves
it is the zero object. -/
@[stacks 00A3 "(3) the stalk of j_!F at x ∉ U is initial (∅ for sheaves of sets)"]
noncomputable def isInitialStalkExtendByInitialSheafify (F : Presheaf C (sp U)) {x : X}
    (hx : x ∉ U) :
    IsInitial (((extendByInitialSheafify U).obj F).presheaf.stalk x) :=
  IsInitial.ofIso (isInitialStalkExtendByInitial U F hx) (stalkSheafifyIso (extendByInitial U F) x)

/-- When the value category has a zero object — as the categories of abelian groups and of
modules do — the stalk of `j_!F` at a point `x ∉ U` is a *zero* object. -/
@[stacks 00A5 "(3)", sga "4 III 1.9.2" "stalk at x∉Y is zero"]
theorem isZero_stalk_extendByInitialSheafify [HasZeroObject C] (F : Presheaf C (sp U)) {x : X}
    (hx : x ∉ U) :
    IsZero (((extendByInitialSheafify U).obj F).presheaf.stalk x) :=
  (isZero_zero C).of_iso ((isInitialStalkExtendByInitialSheafify U F hx).uniqueUpToIso
    HasZeroObject.zeroIsInitial)

open ExtensionByInitial in
/-- The stalk of `j_!F` at a point `j(x)` with `x ∈ U` is the stalk of `F` at `x`. -/
@[stacks 00A5 "(3)", stacks 00A3 "(3) the stalk of j_!F at a point of U is the stalk of F"]
noncomputable def stalkExtendByInitialSheafifyIso (F : Presheaf C (sp U)) (x : sp U) :
    ((extendByInitialSheafify U).obj F).presheaf.stalk (U.inclusion' x) ≅ F.stalk x :=
  (stalkSheafifyIso (extendByInitial U F) (U.inclusion' x)).symm ≪≫
    stalkExtendByInitialIso U F x

end SheafifyStalks

end Stalks

/-- For a presheaf of sets `F` on `U`, the stalk of `j_!F` at a point outside `U` is empty:
`(j_!F)_x = ∅`. -/
@[stacks 00A8,
  stacks 00A3 "(3) for sheaves of sets: (j_!F)_x = ∅ for x ∉ U",
  sga "4 III 1.9.2" "more general"]
theorem isEmpty_stalk_extendByInitialSheafify {X : TopCat.{u}} (U : Opens X)
    (F : Presheaf (Type u) (sp U)) {x : X} (hx : x ∉ U) :
    IsEmpty (stalk ((extendByInitialSheafify U).obj F).presheaf x) :=
  Function.isEmpty ((isInitialStalkExtendByInitialSheafify U F hx).to PEmpty)

end TopCat.Presheaf
