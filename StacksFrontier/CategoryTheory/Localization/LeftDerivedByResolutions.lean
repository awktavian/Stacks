module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.GuitartExact.KanExtension

@[expose] public noncomputable section

/-!
# A resolving subcategory computes the localization, and the left derived functors

Let `W` be a class of morphisms of a category `C` admitting a right calculus of fractions, and
let `P` be a class of objects which *resolves* `C`: every object of `C` receives a morphism of
`W` from an object satisfying `P`. Then the inclusion of the objects satisfying `P` induces an
equivalence of localized categories, and it is a left derivability structure.

The consequences are the ones a derived functor is built from. A functor which inverts the
morphisms of `W` between objects satisfying `P` has a pointwise total left derived functor; the
counit of that derived functor is invertible on every object satisfying `P`; conversely, a
comparison which is invertible on the objects satisfying `P` already exhibits its functor as the
total left derived functor; and two such comparisons are related by a unique isomorphism
compatible with them.

Two auxiliary observations are recorded for their own sake: a right calculus of fractions on `W`
restricts to one on the morphisms of `W` between objects satisfying `P`, corrected by resolving
the auxiliary object that `W` returns; and the same correction shows the category of
`P`-resolutions of an object is connected, which is what makes the derivability structure work.

## Main definitions

* `CategoryTheory.LeftDerivedByResolutions.inclusionLocalizerMorphism`: the inclusion of a class
  of objects, as a morphism of localizers.
* `CategoryTheory.LeftDerivedByResolutions.inclusionLocalizedFunctor`: the induced functor on the
  localized categories.

## Main results

* `CategoryTheory.LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism`: a
  resolving class of objects computes the localization.
* `CategoryTheory.LeftDerivedByResolutions.isLeftDerivabilityStructure_inclusionLocalizerMorphism`:
  and does so as a left derivability structure.
* `CategoryTheory.LeftDerivedByResolutions.hasLeftResolutions_inclusionLocalizerMorphism_iff`:
  the instance `(inclusionLocalizerMorphism W P).HasLeftResolutions` that the results below take
  is the condition that every object of `C` receives a morphism of `W` from an object
  satisfying `P`.
* `CategoryTheory.LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_hasLeftResolutions`:
  existence of the pointwise total left derived functor.
* `CategoryTheory.LeftDerivedByResolutions.isIso_app_of_hasLeftResolutions`: its counit is
  invertible on the resolving class.
* `CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_app_of_hasLeftResolutions`:
  the converse criterion.
* `CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_hasLeftResolutions`:
  such a left derived functor is absolute — it stays a left derived functor after composition
  with any functor out of its target, which is what a derived adjunction requires of it.
* `CategoryTheory.LeftDerivedByResolutions.exists_leftDerivedIso_of_hasLeftResolutions`:
  uniqueness of the comparison between two left derived functors computed on the resolving class.
* `CategoryTheory.LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι` and
  `isConnected_leftResolution`: the two corrections that make the above work.

Each of the five results on derived functors is also stated under its former name
(`hasPointwiseLeftDerivedFunctor_of_resolutions`, `isIso_app_of_resolutions`,
`isLeftDerivedFunctor_of_isIso_on_resolutions`, `isLeftDerivedFunctor_postcomp_of_resolutions`,
`exists_leftDerivedIso_of_resolutions`), taking that condition as an explicit hypothesis `hP`.

## Implementation notes

This is deliberately generic: nothing here mentions modules, complexes or tensor products. It is
stated for an arbitrary category with a right calculus of fractions and an arbitrary resolving
class of objects, so that every construction of a left derived functor by resolutions — K-flat
resolutions of complexes of modules being the case of interest — can cite it instead of
re-deriving it. Anything found elsewhere in the tree proving these statements again is a
duplicate of this file.

The analogue for a *left* calculus of fractions is false: correcting the auxiliary object would
need a morphism of `W` *into* an object satisfying `P`, which resolutions do not provide.

Everything is public, including the auxiliary lemmas, because under the module system the
exposed body of a public definition may not mention a private declaration, so the whole chain
below a public result has to be public too.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.LocalizerMorphism

namespace CategoryTheory.LeftDerivedByResolutions

universe v₁ v₂ v₃ u₁ u₂ u₃

section Abstract

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

/-- Along a left derivability structure `Φ`, the functor `F` has a pointwise left derived
functor at `Φ.functor.obj X` if and only if `Φ.functor ⋙ F` has one at `X`.

This is the left analogue of Mathlib's
`LocalizerMorphism.hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure`,
obtained by applying `TwoSquare.hasPointwiseRightKanExtensionAt_iff` to the transposed 2-square,
which is Guitart exact by definition of a left derivability structure. -/
public lemma hasPointwiseLeftDerivedFunctorAt_iff_of_isLeftDerivabilityStructure
    (Φ : LocalizerMorphism W₁ W₂) [Φ.IsLeftDerivabilityStructure] (F : C₂ ⥤ H) (X : C₁) :
    (Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctorAt W₁ X ↔
      F.HasPointwiseLeftDerivedFunctorAt W₂ (Φ.functor.obj X) := by
  have hw : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).inv :=
    IsLeftDerivabilityStructure.guitartExact'
  have := (TwoSquare.guitartExact_iff_initial ((Φ.catCommSq W₁.Q W₂.Q).iso).inv).1 hw
    (W₁.Q.obj X)
  let e : W₂.Q.obj (Φ.functor.obj X) ≅ (Φ.localizedFunctor W₁.Q W₂.Q).obj (W₁.Q.obj X) :=
    ((Φ.catCommSq W₁.Q W₂.Q).iso).app X
  rw [F.hasPointwiseLeftDerivedFunctorAt_iff W₂.Q W₂ (Φ.functor.obj X),
    (Φ.functor ⋙ F).hasPointwiseLeftDerivedFunctorAt_iff W₁.Q W₁ X,
    TwoSquare.hasPointwiseRightKanExtensionAt_iff ((Φ.catCommSq W₁.Q W₂.Q).iso).inv F
      (W₁.Q.obj X),
    Functor.hasPointwiseRightKanExtensionAt_iff_of_iso W₂.Q F e]

/-- If `Φ` is a left derivability structure which derives `F`, i.e. `Φ.functor ⋙ F` inverts `W₁`,
then `F` has a pointwise left derived functor with respect to `W₂`.

This is the left analogue of
`CategoryTheory.LocalizerMorphism.Derives.hasPointwiseRightDerivedFunctor`. -/
public lemma hasPointwiseLeftDerivedFunctor_of_derives
    (Φ : LocalizerMorphism W₁ W₂) [Φ.IsLeftDerivabilityStructure] (F : C₂ ⥤ H)
    (h : Φ.Derives F) : F.HasPointwiseLeftDerivedFunctor W₂ := by
  intro X₂
  have L : Φ.LeftResolution X₂ := Classical.arbitrary _
  rw [← F.hasPointwiseLeftDerivedFunctorAt_iff_of_mem W₂ L.w L.hw,
    ← hasPointwiseLeftDerivedFunctorAt_iff_of_isLeftDerivabilityStructure Φ F L.X₁]
  exact (Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ h) L.X₁


/-- On a resolving object, the counit of a derived functor is invertible. -/
public lemma isIso_app_of_derives
    (Φ : LocalizerMorphism W₁ W₂) [Φ.IsLeftDerivabilityStructure] (F : C₂ ⥤ H)
    (h : Φ.Derives F) {D : Type*} [Category D]
    (L : C₂ ⥤ D) [L.IsLocalization W₂] (LF : D ⥤ H)
    (α : L ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W₂] (X : C₁) :
    IsIso (α.app (Φ.functor.obj X)) := by
  have := hasPointwiseLeftDerivedFunctor_of_derives Φ F h
  let E := (RightExtension.mk LF α).compTwoSquare
    ((Φ.catCommSq W₁.Q L).iso).inv
  have : E.left.IsLeftDerivedFunctor E.hom W₁ :=
    ⟨((LF.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor α W₂).compTwoSquare
      ((Φ.catCommSq W₁.Q L).iso).inv).isRightKanExtension⟩
  have : IsIso E.hom := Functor.isIso_of_isLeftDerivedFunctor_of_inverts E.left E.hom h
  have : IsIso (E.hom.app X) := inferInstance
  simpa [E, RightExtension.compTwoSquare] using this


/-- A functor is full as soon as it is full on the objects in the image of an essentially
surjective functor. -/
public lemma full_of_essSurj {D₁ : Type u₂} {D₂ : Type u₃} [Category.{v₂} D₁]
    [Category.{v₃} D₂] {C : Type u₁} [Category.{v₁} C]
    (E : C ⥤ D₁) [E.EssSurj] (G : D₁ ⥤ D₂)
    (h : ∀ (X Y : C) (f : G.obj (E.obj X) ⟶ G.obj (E.obj Y)),
      ∃ a : E.obj X ⟶ E.obj Y, G.map a = f) :
    G.Full where
  map_surjective {X Y} f := by
    obtain ⟨a, ha⟩ := h (E.objPreimage X) (E.objPreimage Y)
      (G.map (E.objObjPreimageIso X).hom ≫ f ≫ G.map (E.objObjPreimageIso Y).inv)
    refine ⟨(E.objObjPreimageIso X).inv ≫ a ≫ (E.objObjPreimageIso Y).hom, ?_⟩
    rw [G.map_comp, G.map_comp, ha]
    simp [← G.map_comp]

/-- A functor is faithful as soon as it is faithful on the objects in the image of an
essentially surjective functor. -/
public lemma faithful_of_essSurj {D₁ : Type u₂} {D₂ : Type u₃} [Category.{v₂} D₁]
    [Category.{v₃} D₂] {C : Type u₁} [Category.{v₁} C]
    (E : C ⥤ D₁) [E.EssSurj] (G : D₁ ⥤ D₂)
    (h : ∀ (X Y : C) (f₁ f₂ : E.obj X ⟶ E.obj Y), G.map f₁ = G.map f₂ → f₁ = f₂) :
    G.Faithful where
  map_injective {X Y} f₁ f₂ hf := by
    simpa using h (E.objPreimage X) (E.objPreimage Y)
      ((E.objObjPreimageIso X).hom ≫ f₁ ≫ (E.objObjPreimageIso Y).inv)
      ((E.objObjPreimageIso X).hom ≫ f₂ ≫ (E.objObjPreimageIso Y).inv)
      (by rw [G.map_comp, G.map_comp, G.map_comp, G.map_comp, hf])

/-- The image under a localizer morphism `Φ` of a right fraction for `W₁` is a right fraction
for `W₂`. -/
public abbrev imageRightFraction (Φ : LocalizerMorphism W₁ W₂) {X Y : C₁}
    (φ : W₁.RightFraction X Y) :
    W₂.RightFraction (Φ.functor.obj X) (Φ.functor.obj Y) :=
  MorphismProperty.RightFraction.mk (Φ.functor.map φ.s) (Φ.map _ φ.hs) (Φ.functor.map φ.f)

/-- The functor induced by a localizer morphism on the localized categories sends the morphism
described by a right fraction to the morphism described by the image right fraction. -/
public lemma imageRightFraction_map (Φ : LocalizerMorphism W₁ W₂)
    {D₁ : Type*} {D₂ : Type*} [Category D₁] [Category D₂]
    (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G)
    {X Y : C₁} (φ : W₁.RightFraction X Y) :
    (imageRightFraction Φ φ).map L₂ (Localization.inverts _ _) =
      e.hom.app X ≫ G.map (φ.map L₁ (Localization.inverts _ _)) ≫ e.inv.app Y := by
  have : IsIso (L₂.map (imageRightFraction Φ φ).s) :=
    Localization.inverts L₂ W₂ _ (Φ.map _ φ.hs)
  rw [← cancel_epi (L₂.map (imageRightFraction Φ φ).s),
    MorphismProperty.RightFraction.map_s_comp_map]
  dsimp only [imageRightFraction]
  have hnats : (Φ.functor ⋙ L₂).map φ.s ≫ e.hom.app X
      = e.hom.app φ.X' ≫ (L₁ ⋙ G).map φ.s := e.hom.naturality φ.s
  have hnatf : (Φ.functor ⋙ L₂).map φ.f ≫ e.hom.app Y
      = e.hom.app φ.X' ≫ (L₁ ⋙ G).map φ.f := e.hom.naturality φ.f
  dsimp only [Functor.comp_map] at hnats hnatf
  rw [← Category.assoc, hnats, Category.assoc, ← G.map_comp_assoc,
    MorphismProperty.RightFraction.map_s_comp_map φ L₁ _, ← Category.assoc, ← hnatf]
  simp

end Abstract

section Resolutions

variable {C : Type u₁} [Category.{v₁} C]

/-- The inclusion of a class of objects `P` of `C`, as a localizer morphism between the class of
morphisms of `P` which belong to `W` and `W` itself. -/
public abbrev inclusionLocalizerMorphism (W : MorphismProperty C) (P : ObjectProperty C) :
    LocalizerMorphism (W.inverseImage P.ι) W where
  functor := P.ι
  map _ _ _ h := h

/-- The inclusion of `P` has left resolutions (`LocalizerMorphism.HasLeftResolutions`) if and only
if every object of `C` receives a morphism of `W` from an object satisfying `P`. -/
public lemma hasLeftResolutions_inclusionLocalizerMorphism_iff (W : MorphismProperty C)
    (P : ObjectProperty C) :
    (inclusionLocalizerMorphism W P).HasLeftResolutions ↔
      ∀ X : C, ∃ (Y : C) (_ : P Y) (s : Y ⟶ X), W s := by
  refine ⟨fun h X => ?_, fun hP X => ?_⟩
  · obtain ⟨R⟩ := h X
    exact ⟨R.X₁.obj, R.X₁.property, R.w, R.hw⟩
  · obtain ⟨Y, hY, s, hs⟩ := hP X
    exact ⟨{ X₁ := ⟨Y, hY⟩, w := s, hw := hs }⟩

/-- If `W` has a right calculus of fractions and every object of `C` admits a morphism of `W`
from an object satisfying `P`, then the category of `P`-resolutions of an object `X` is
connected: two resolutions `Y ⟶ X` and `Y' ⟶ X` are compared by turning the left fraction they
form into a right fraction, which produces `T ⟶ Y` in `W` and `T ⟶ Y'` over `X`, and then
resolving `T`. -/
public lemma isConnected_leftResolution (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (P : ObjectProperty C)
    [(inclusionLocalizerMorphism W P).HasLeftResolutions] (X : C) :
    IsConnected ((inclusionLocalizerMorphism W P).LeftResolution X) := by
  refine zigzag_isConnected (fun L L' ↦ ?_)
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk L.w L'.w L'.hw).exists_rightFraction
  dsimp only at hψ
  obtain ⟨M⟩ := ‹(inclusionLocalizerMorphism W P).HasLeftResolutions› ψ.X'
  let N : (inclusionLocalizerMorphism W P).LeftResolution X :=
    LeftResolution.mk (Φ := inclusionLocalizerMorphism W P) (X₁ := M.X₁) (M.w ≫ ψ.s ≫ L.w)
      (W.comp_mem _ _ M.hw (W.comp_mem _ _ ψ.hs L.hw))
  let a : N ⟶ L := LeftResolution.Hom.mk (ObjectProperty.homMk (M.w ≫ ψ.s)) (by simp [N])
  let b : N ⟶ L' := LeftResolution.Hom.mk (ObjectProperty.homMk (M.w ≫ ψ.f)) (by simp [N, hψ])
  exact Zigzag.of_inv_hom a b

/-- Under the same assumptions, every arrow of `C` admits a `P`-resolution: resolve its target,
turn the resulting left fraction into a right fraction, and resolve the auxiliary object of that
right fraction. -/
public lemma hasLeftResolutions_arrow (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (P : ObjectProperty C)
    [(inclusionLocalizerMorphism W P).HasLeftResolutions] :
    (inclusionLocalizerMorphism W P).arrow.HasLeftResolutions := by
  intro a
  obtain ⟨Q⟩ := ‹(inclusionLocalizerMorphism W P).HasLeftResolutions› a.right
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk a.hom Q.w Q.hw).exists_rightFraction
  dsimp only at hψ
  obtain ⟨M⟩ := ‹(inclusionLocalizerMorphism W P).HasLeftResolutions› ψ.X'
  exact ⟨{ X₁ := Arrow.mk (ObjectProperty.homMk (M.w ≫ ψ.f) : M.X₁ ⟶ Q.X₁)
           w := Arrow.homMk (M.w ≫ ψ.s) Q.w
             (show (M.w ≫ ψ.s) ≫ a.hom = (M.w ≫ ψ.f) ≫ Q.w by simp [hψ])
           hw := ⟨W.comp_mem _ _ M.hw ψ.hs, Q.hw⟩ }⟩

/-- Precomposing two equal composites in `C` with a common morphism `w` gives equal composites in
the full subcategory on `P`. -/
private lemma homMk_comp_eq {P : ObjectProperty C} {A B₁ B₂ Y : P.FullSubcategory} {Z : C}
    (w : A.obj ⟶ Z) {t₁ : Z ⟶ B₁.obj} {t₂ : Z ⟶ B₂.obj} {f₁ : B₁ ⟶ Y} {f₂ : B₂ ⟶ Y}
    (h : t₁ ≫ P.ι.map f₁ = t₂ ≫ P.ι.map f₂) :
    ObjectProperty.homMk (w ≫ t₁) ≫ f₁ = ObjectProperty.homMk (w ≫ t₂) ≫ f₂ := by
  apply P.ι.map_injective
  change (w ≫ t₁) ≫ P.ι.map f₁ = (w ≫ t₂) ≫ P.ι.map f₂
  rw [Category.assoc, Category.assoc, h]

/-- If `W` has a right calculus of fractions and every object of `C` admits a morphism of `W`
from an object satisfying `P`, then the class of morphisms of `P` which belong to `W` again has a
right calculus of fractions: both axioms are those of `W`, corrected by resolving the auxiliary
object that `W` hands back.

The analogous statement for a *left* calculus of fractions is false: correcting the auxiliary
object would need a morphism of `W` *into* an object satisfying `P`. -/
public lemma hasRightCalculusOfFractions_inverseImage_ι (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (P : ObjectProperty C)
    [(inclusionLocalizerMorphism W P).HasLeftResolutions] :
    (W.inverseImage P.ι).HasRightCalculusOfFractions := by
  refine { toIsMultiplicative := inferInstance, exists_rightFraction := ?_, ext := ?_ }
  · intro X Y φ
    obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk (P.ι.map φ.f) (P.ι.map φ.s)
      φ.hs).exists_rightFraction
    dsimp only at hψ
    obtain ⟨M⟩ := ‹(inclusionLocalizerMorphism W P).HasLeftResolutions› ψ.X'
    refine ⟨MorphismProperty.RightFraction.mk (X' := M.X₁)
      (ObjectProperty.homMk (M.w ≫ ψ.s)) (W.comp_mem _ _ M.hw ψ.hs)
      (ObjectProperty.homMk (M.w ≫ ψ.f)), ?_⟩
    exact homMk_comp_eq M.w hψ
  · intro X Y Y' f₁ f₂ s hs h
    obtain ⟨Z, t, ht, hteq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
      (P.ι.map f₁) (P.ι.map f₂) (P.ι.map s) hs (by rw [← P.ι.map_comp, ← P.ι.map_comp, h])
    obtain ⟨M⟩ := ‹(inclusionLocalizerMorphism W P).HasLeftResolutions› Z
    refine ⟨M.X₁, ObjectProperty.homMk (M.w ≫ t), W.comp_mem _ _ M.hw ht, ?_⟩
    exact homMk_comp_eq M.w hteq

/-- The functor induced by the inclusion of the objects satisfying `P` on the localized
categories. -/
public noncomputable abbrev inclusionLocalizedFunctor (W : MorphismProperty C)
    (P : ObjectProperty C) :
    (W.inverseImage P.ι).Localization ⥤ W.Localization :=
  (inclusionLocalizerMorphism W P).localizedFunctor (W.inverseImage P.ι).Q W.Q

/-- The inclusion of a class of objects which resolves every object of `C` is a localized
equivalence, provided `W` has a right calculus of fractions.

Essential surjectivity is `LocalizerMorphism.essSurj_of_hasLeftResolutions`. Fullness and
faithfulness are the source's observation that a right fraction between two objects satisfying
`P` can itself be resolved: every morphism of `W.Localization` between objects satisfying `P` is
described by a right fraction (`Localization.exists_rightFraction`), whose auxiliary object may
be replaced by a resolution of it, and two right fractions with the same image are related by a
zigzag (`MorphismProperty.RightFraction.map_eq_iff`) whose apex may likewise be resolved. -/
public lemma isLocalizedEquivalence_inclusionLocalizerMorphism (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (P : ObjectProperty C)
    [(inclusionLocalizerMorphism W P).HasLeftResolutions] :
    (inclusionLocalizerMorphism W P).IsLocalizedEquivalence := by
  have hcof := hasRightCalculusOfFractions_inverseImage_ι W P
  have e : (inclusionLocalizerMorphism W P).functor ⋙ W.Q ≅
      (W.inverseImage P.ι).Q ⋙ inclusionLocalizedFunctor W P :=
    ((inclusionLocalizerMorphism W P).catCommSq (W.inverseImage P.ι).Q W.Q).iso
  have hE : (W.inverseImage P.ι).Q.EssSurj :=
    Localization.essSurj (W.inverseImage P.ι).Q (W.inverseImage P.ι)
  have hfull : (inclusionLocalizedFunctor W P).Full := by
    refine full_of_essSurj (W.inverseImage P.ι).Q _ (fun X₀ Y₀ h => ?_)
    obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction W.Q W
      (e.hom.app X₀ ≫ h ≫ e.inv.app Y₀)
    obtain ⟨M⟩ := ‹(inclusionLocalizerMorphism W P).HasLeftResolutions› ψ.X'
    have hmem : (W.inverseImage P.ι) (ObjectProperty.homMk (M.w ≫ ψ.s) : M.X₁ ⟶ X₀) :=
      W.comp_mem _ _ M.hw ψ.hs
    refine ⟨(MorphismProperty.RightFraction.mk
      (ObjectProperty.homMk (M.w ≫ ψ.s) : M.X₁ ⟶ X₀) hmem
      (ObjectProperty.homMk (M.w ≫ ψ.f))).map (W.inverseImage P.ι).Q
        (Localization.inverts _ _), ?_⟩
    have key : (imageRightFraction (inclusionLocalizerMorphism W P)
        (MorphismProperty.RightFraction.mk
          (ObjectProperty.homMk (M.w ≫ ψ.s) : M.X₁ ⟶ X₀) hmem
          (ObjectProperty.homMk (M.w ≫ ψ.f)))).map W.Q (Localization.inverts _ _)
        = ψ.map W.Q (Localization.inverts _ _) := by
      rw [MorphismProperty.RightFraction.map_eq_iff]
      exact ⟨P.ι.obj M.X₁, 𝟙 _, M.w, by simp, by simp,
        by simpa using W.comp_mem _ _ M.hw ψ.hs⟩
    rw [imageRightFraction_map (inclusionLocalizerMorphism W P) (W.inverseImage P.ι).Q W.Q
      (inclusionLocalizedFunctor W P) e, ← hψ] at key
    rw [← cancel_mono (e.inv.app Y₀)]
    simpa using key
  have hfaith : (inclusionLocalizedFunctor W P).Faithful := by
    refine faithful_of_essSurj (W.inverseImage P.ι).Q _ (fun X₀ Y₀ f₁ f₂ hf => ?_)
    obtain ⟨φ₁, h₁⟩ :=
      Localization.exists_rightFraction (W.inverseImage P.ι).Q (W.inverseImage P.ι) f₁
    obtain ⟨φ₂, h₂⟩ :=
      Localization.exists_rightFraction (W.inverseImage P.ι).Q (W.inverseImage P.ι) f₂
    have key : (imageRightFraction (inclusionLocalizerMorphism W P) φ₁).map W.Q
          (Localization.inverts _ _)
        = (imageRightFraction (inclusionLocalizerMorphism W P) φ₂).map W.Q
          (Localization.inverts _ _) := by
      rw [imageRightFraction_map (inclusionLocalizerMorphism W P) (W.inverseImage P.ι).Q W.Q
          (inclusionLocalizedFunctor W P) e,
        imageRightFraction_map (inclusionLocalizerMorphism W P) (W.inverseImage P.ι).Q W.Q
          (inclusionLocalizedFunctor W P) e, ← h₁, ← h₂, hf]
    rw [MorphismProperty.RightFraction.map_eq_iff] at key
    obtain ⟨Z, t₁, t₂, hs, hff, ht⟩ := key
    dsimp only [imageRightFraction] at hs hff ht
    obtain ⟨M⟩ := ‹(inclusionLocalizerMorphism W P).HasLeftResolutions› Z
    rw [h₁, h₂, MorphismProperty.RightFraction.map_eq_iff]
    refine ⟨M.X₁, ObjectProperty.homMk (M.w ≫ t₁), ObjectProperty.homMk (M.w ≫ t₂), ?_, ?_, ?_⟩
    · exact homMk_comp_eq M.w hs
    · exact homMk_comp_eq M.w hff
    · show W ((M.w ≫ t₁) ≫ P.ι.map φ₁.s)
      rw [Category.assoc]
      exact W.comp_mem _ _ M.hw ht
  have hes : (inclusionLocalizedFunctor W P).EssSurj := by
    have := (inclusionLocalizerMorphism W P).essSurj_of_hasLeftResolutions W.Q
    refine ⟨fun Y => ?_⟩
    obtain ⟨X, ⟨eX⟩⟩ := Functor.EssSurj.mem_essImage
      (F := (inclusionLocalizerMorphism W P).functor ⋙ W.Q) Y
    exact ⟨(W.inverseImage P.ι).Q.obj X, ⟨(e.app X).symm ≪≫ eX⟩⟩
  exact ⟨{ faithful := hfaith, full := hfull, essSurj := hes }⟩

/-- The inclusion of a class of objects which resolves every object of `C` is a left
derivability structure, provided `W` has a right calculus of fractions: this is
`LocalizerMorphism.IsLeftDerivabilityStructure.mk'`, whose three hypotheses are
`isConnected_leftResolution`, `hasLeftResolutions_arrow` and
`isLocalizedEquivalence_inclusionLocalizerMorphism`. -/
public lemma isLeftDerivabilityStructure_inclusionLocalizerMorphism (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (P : ObjectProperty C)
    [(inclusionLocalizerMorphism W P).HasLeftResolutions] :
    (inclusionLocalizerMorphism W P).IsLeftDerivabilityStructure := by
  have h₁ : ∀ X, IsConnected ((inclusionLocalizerMorphism W P).LeftResolution X) :=
    isConnected_leftResolution W P
  have h₂ : (inclusionLocalizerMorphism W P).arrow.HasLeftResolutions :=
    hasLeftResolutions_arrow W P
  have h₃ := isLocalizedEquivalence_inclusionLocalizerMorphism W P
  exact IsLeftDerivabilityStructure.mk' _


/-- A resolving class on which a functor inverts weak equivalences computes its
pointwise left derived functor. -/
public lemma hasPointwiseLeftDerivedFunctor_of_hasLeftResolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C) [(inclusionLocalizerMorphism W P).HasLeftResolutions]
    {H : Type*} [Category H] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s)) :
    F.HasPointwiseLeftDerivedFunctor W := by
  have := isLeftDerivabilityStructure_inclusionLocalizerMorphism W P
  exact hasPointwiseLeftDerivedFunctor_of_derives (inclusionLocalizerMorphism W P) F
    (fun X Y s hs => hF (P.ι.map s) hs X.property Y.property)

/-- `hasPointwiseLeftDerivedFunctor_of_hasLeftResolutions`, with the existence of resolutions as
the explicit hypothesis `hP` instead of an instance. -/
public lemma hasPointwiseLeftDerivedFunctor_of_resolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C) (_ : P Y) (s : Y ⟶ X), W s)
    {H : Type*} [Category H] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s)) :
    F.HasPointwiseLeftDerivedFunctor W :=
  have := (hasLeftResolutions_inclusionLocalizerMorphism_iff W P).2 hP
  hasPointwiseLeftDerivedFunctor_of_hasLeftResolutions W P F hF

/-- The comparison to an underived functor is invertible on the resolving class. -/
public lemma isIso_app_of_hasLeftResolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C) [(inclusionLocalizerMorphism W P).HasLeftResolutions]
    {H D : Type*} [Category H] [Category D] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s))
    (L : C ⥤ D) [L.IsLocalization W] (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor α W] (X : C) (hX : P X) : IsIso (α.app X) := by
  have := isLeftDerivabilityStructure_inclusionLocalizerMorphism W P
  exact isIso_app_of_derives (inclusionLocalizerMorphism W P) F
    (fun X Y s hs => hF (P.ι.map s) hs X.property Y.property) L LF α ⟨X, hX⟩

/-- `isIso_app_of_hasLeftResolutions`, with the existence of resolutions as the explicit
hypothesis `hP` instead of an instance. -/
public lemma isIso_app_of_resolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C) (_ : P Y) (s : Y ⟶ X), W s)
    {H D : Type*} [Category H] [Category D] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s))
    (L : C ⥤ D) [L.IsLocalization W] (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor α W] (X : C) (hX : P X) : IsIso (α.app X) :=
  have := (hasLeftResolutions_inclusionLocalizerMorphism_iff W P).2 hP
  isIso_app_of_hasLeftResolutions W P F hF L LF α X hX


/-- A comparison which is invertible on a resolving class is a left derived functor. -/
public lemma isLeftDerivedFunctor_of_isIso_app_of_hasLeftResolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C) [(inclusionLocalizerMorphism W P).HasLeftResolutions]
    {H D : Type*} [Category H] [Category D] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s))
    (L : C ⥤ D) [L.IsLocalization W] (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hα : ∀ X : C, P X → IsIso (α.app X)) : LF.IsLeftDerivedFunctor α W := by
  have hP := (hasLeftResolutions_inclusionLocalizerMorphism_iff W P).1 inferInstance
  have := hasPointwiseLeftDerivedFunctor_of_hasLeftResolutions W P F hF
  let G := F.totalLeftDerived L W
  let β := F.totalLeftDerivedCounit L W
  let φ := G.leftDerivedLift β W LF α
  have hφ : IsIso φ := by
    refine (NatTrans.isIso_iff_isIso_app _).2 fun Y => ?_
    have := Localization.essSurj L W
    obtain ⟨X, hX, s, hs⟩ := hP (L.objPreimage Y)
    let e : L.obj X ≅ Y := Localization.isoOfHom L W s hs ≪≫ L.objObjPreimageIso Y
    rw [NatTrans.isIso_app_iff_of_iso φ e.symm]
    have := isIso_app_of_hasLeftResolutions W P F hF L G β X hX
    have := hα X hX
    rw [← isIso_comp_right_iff (φ.app (L.obj X)) (β.app X)]
    simp only [φ, leftDerived_fac_app]
    infer_instance
  exact (G.isLeftDerivedFunctor_iff_isIso_leftDerivedLift β W LF α).2 hφ

/-- `isLeftDerivedFunctor_of_isIso_app_of_hasLeftResolutions`, with the existence of resolutions
as the explicit hypothesis `hP` instead of an instance. -/
public lemma isLeftDerivedFunctor_of_isIso_on_resolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C) (_ : P Y) (s : Y ⟶ X), W s)
    {H D : Type*} [Category H] [Category D] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s))
    (L : C ⥤ D) [L.IsLocalization W] (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    (hα : ∀ X : C, P X → IsIso (α.app X)) : LF.IsLeftDerivedFunctor α W :=
  have := (hasLeftResolutions_inclusionLocalizerMorphism_iff W P).2 hP
  isLeftDerivedFunctor_of_isIso_app_of_hasLeftResolutions W P F hF L LF α hα


/-- **A left derived functor computed by resolutions is absolute.** If `α` exhibits `LF` as the
left derived functor of `F`, and `F` inverts the weak equivalences between objects of a
resolving class `P`, then for *every* functor `G` out of the target the composite `LF ⋙ G` is
the left derived functor of `F ⋙ G`, with the whiskered comparison.

This is what a derived adjunction asks of its left derived functor
(`CategoryTheory.Adjunction.derived` needs both derived functors to be absolute), and it is the
reason absoluteness is formal for a functor derived by resolutions and not formal in general:
the comparison of `F ⋙ G` is invertible on `P` because the comparison of `F` is, and a functor
carries an isomorphism to an isomorphism. -/
public lemma isLeftDerivedFunctor_postcomp_of_hasLeftResolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C) [(inclusionLocalizerMorphism W P).HasLeftResolutions]
    {H D : Type*} [Category H] [Category D] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s))
    (L : C ⥤ D) [L.IsLocalization W] (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor α W] {H' : Type*} [Category H'] (G : H ⥤ H') :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G) W := by
  have hFG : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso ((F ⋙ G).map s) := by
    intro X Y s hs hX hY
    have := hF s hs hX hY
    dsimp only [Functor.comp_map]
    infer_instance
  refine isLeftDerivedFunctor_of_isIso_app_of_hasLeftResolutions W P (F ⋙ G) hFG L (LF ⋙ G) _
    (fun X hX => ?_)
  have := isIso_app_of_hasLeftResolutions W P F hF L LF α X hX
  rw [show ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G).app X
      = G.map (α.app X) by simp]
  infer_instance

/-- `isLeftDerivedFunctor_postcomp_of_hasLeftResolutions`, with the existence of resolutions as
the explicit hypothesis `hP` instead of an instance. -/
public lemma isLeftDerivedFunctor_postcomp_of_resolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C) (_ : P Y) (s : Y ⟶ X), W s)
    {H D : Type*} [Category H] [Category D] (F : C ⥤ H)
    (hF : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (F.map s))
    (L : C ⥤ D) [L.IsLocalization W] (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor α W] {H' : Type*} [Category H'] (G : H ⥤ H') :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G) W :=
  have := (hasLeftResolutions_inclusionLocalizerMorphism_iff W P).2 hP
  isLeftDerivedFunctor_postcomp_of_hasLeftResolutions W P F hF L LF α G


/-- Comparisons computed on a resolving class give the canonical isomorphism of derived
functors, with its compatibility with the two counits. -/
public lemma exists_leftDerivedIso_of_hasLeftResolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C) [(inclusionLocalizerMorphism W P).HasLeftResolutions]
    {H D : Type*} [Category H] [Category D] (U V : C ⥤ H) (e : U ≅ V)
    (hU : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (U.map s))
    (L : C ⥤ D) [L.IsLocalization W] (F G : D ⥤ H)
    (α : L ⋙ F ⟶ U) (β : L ⋙ G ⟶ V) [F.IsLeftDerivedFunctor α W]
    (hβ : ∀ X : C, P X → IsIso (β.app X)) :
    ∃ E : F ≅ G, whiskerLeft L E.hom ≫ β = α ≫ e.hom := by
  have hV : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (V.map s) := by
    intro X Y s hs hX hY
    have := hU s hs hX hY
    rw [← NatIso.naturality_2 e.symm s]
    dsimp
    infer_instance
  have := isLeftDerivedFunctor_of_isIso_app_of_hasLeftResolutions W P V hV L G β hβ
  exact ⟨leftDerivedNatIso F G α β W e, leftDerivedNatTrans_fac F G α β W e.hom⟩

/-- `exists_leftDerivedIso_of_hasLeftResolutions`, with the existence of resolutions as the
explicit hypothesis `hP` instead of an instance. -/
public lemma exists_leftDerivedIso_of_resolutions
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C) (_ : P Y) (s : Y ⟶ X), W s)
    {H D : Type*} [Category H] [Category D] (U V : C ⥤ H) (e : U ≅ V)
    (hU : ∀ {X Y : C} (s : X ⟶ Y), W s → P X → P Y → IsIso (U.map s))
    (L : C ⥤ D) [L.IsLocalization W] (F G : D ⥤ H)
    (α : L ⋙ F ⟶ U) (β : L ⋙ G ⟶ V) [F.IsLeftDerivedFunctor α W]
    (hβ : ∀ X : C, P X → IsIso (β.app X)) :
    ∃ E : F ≅ G, whiskerLeft L E.hom ≫ β = α ≫ e.hom :=
  have := (hasLeftResolutions_inclusionLocalizerMorphism_iff W P).2 hP
  exists_leftDerivedIso_of_hasLeftResolutions W P U V e hU L F G α β hβ

end Resolutions

end CategoryTheory.LeftDerivedByResolutions

end
