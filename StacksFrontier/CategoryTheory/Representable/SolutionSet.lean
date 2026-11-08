module

public import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Corepresentability from a solution set

Stacks 0AHN: let `C` have all small limits and let `F : C ⥤ Type v` preserve them. If there is a
family `x : I → C` with elements `f i : F.obj (x i)` such that every `g : F.obj y` has the form
`F.map φ (f i)` for some `i` and some `φ : x i ⟶ y`, then `F` is corepresentable.

The corepresenting object is built by refining the family to a single universal element.
`exists_surjective_pair` takes the limit of the family viewed inside the category of elements
`F.Elements`, giving one pair `(xLim, fLim)` that still hits every element;
`exists_wide_equalizer_pair` then cuts `xLim` down along the wide equalizer of all
endomorphisms of `xLim` fixing `fLim`, and `exists_equalizer_lift` shows that this makes
`φ ↦ F.map φ fX` injective as well as surjective. `corepresentableBy_of_bijective` packages the
resulting bijection as `F.CorepresentableBy X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

namespace IsCorepresentable_SolutionSet

/-- A limit-preserving functor sends the projection of a limit to the component of the element
built by `Types.Limit.mk` from a compatible family. -/
private theorem map_limit_π_preservesLimitIso_inv_mk
    {C : Type u} [Category.{v} C] {J : Type v} [Category.{v} J] [HasLimitsOfShape J C]
    (F : C ⥤ Type v) [PreservesLimitsOfShape J F] (D : J ⥤ C)
    (u : ∀ j, (D ⋙ F).obj j) (hu : ∀ (j j' : J) (h : j ⟶ j'), (D ⋙ F).map h (u j) = u j')
    (j : J) :
    F.map (limit.π D j) ((preservesLimitIso F D).inv (Types.Limit.mk (D ⋙ F) u hu)) = u j :=
  (ConcreteCategory.congr_hom (preservesLimitIso_inv_π F D j) _).trans
    (Types.Limit.π_mk (D ⋙ F) u hu j)

/-- A solution set can be replaced by a single pair `(xLim, fLim)` from which every element of
`F` is obtained, namely the limit of the family inside the category of elements. -/
lemma exists_surjective_pair
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    {I : Type v} (x : I → C) (f : ∀ i, F.obj (x i))
    (hsurj : ∀ (y : C) (g : F.obj y), ∃ i, ∃ φ : x i ⟶ y, F.map φ (f i) = g) :
    ∃ (xLim : C) (fLim : F.obj xLim),
      ∀ (Y : C) (g : F.obj Y), ∃ φ : xLim ⟶ Y, F.map φ fLim = g := by
  -- `F.elementsMk`, not the anonymous constructor: `⟨x i, f i⟩` elaborates at the unfolded
  -- sigma type, and instance search can no longer unfold `F.Elements` to match it, so the
  -- `Category (InducedCategory ..)` instance is not found.
  let ι : InducedCategory F.Elements (fun i : I => F.elementsMk (x i) (f i)) ⥤ F.Elements :=
    inducedFunctor _
  let D := ι ⋙ CategoryOfElements.π F
  have coh : ∀ (i j : InducedCategory F.Elements (fun i : I => F.elementsMk (x i) (f i)))
      (h : i ⟶ j), (D ⋙ F).map h (f i) = f j := fun i j h => (ι.map h).map_val
  refine ⟨limit D, (preservesLimitIso F D).inv (Types.Limit.mk (D ⋙ F) f coh), ?_⟩
  intros Y g
  obtain ⟨i, φᵢ, hφ⟩ := hsurj Y g
  refine ⟨limit.π D i ≫ φᵢ, ?_⟩
  rw [Functor.map_comp_apply, map_limit_π_preservesLimitIso_inv_mk F D f coh, hφ]

/-- The wide equalizer of all endomorphisms fixing `fLim` absorbs any such endomorphism. -/
lemma wide_equalizer_comp_self
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v)
    (xLim : C) (fLim : F.obj xLim)
    (α : xLim ⟶ xLim) (hα : F.map α fLim = fLim) :
    haveI : HasWideEqualizer
        (Subtype.val : { β : xLim ⟶ xLim // F.map β fLim = fLim } → (xLim ⟶ xLim)) :=
      inferInstance
    wideEqualizer.ι
        (Subtype.val : { β : xLim ⟶ xLim // F.map β fLim = fLim } → (xLim ⟶ xLim)) ≫ α =
      wideEqualizer.ι
        (Subtype.val : { β : xLim ⟶ xLim // F.map β fLim = fLim } → (xLim ⟶ xLim)) := by
  set S : Type v := { β : xLim ⟶ xLim // F.map β fLim = fLim }
  let idS : S := ⟨𝟙 xLim, by simp⟩
  let αS : S := ⟨α, hα⟩
  simpa [αS, idS] using
    wideEqualizer.condition (Subtype.val : S → (xLim ⟶ xLim)) αS idS

/-- Lift `fLim` along the wide equalizer of a family of endomorphisms fixing it. -/
lemma lift_compatible_element_inhabited
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    (xLim : C) (fLim : F.obj xLim)
    (S : Type v) [Inhabited S] (g : S → (xLim ⟶ xLim))
    (hfix : ∀ s, F.map (g s) fLim = fLim) :
    haveI : HasWideEqualizer g := inferInstance
    ∃ fX : F.obj (wideEqualizer g), F.map (wideEqualizer.ι g) fX = fLim := by
  -- Build a coherent family of elements in `parallelFamily g ⋙ F`, namely
  -- `fLim` at both `zero` and `one`. Coherence at the `line s` morphism follows from `hfix`.
  let famVal : ∀ j, (parallelFamily g ⋙ F).obj j :=
    fun j => match j with
      | WalkingParallelFamily.zero => fLim
      | WalkingParallelFamily.one => fLim
  have famCoh : ∀ (j j' : WalkingParallelFamily S) (h : j ⟶ j'),
      (parallelFamily g ⋙ F).map h (famVal j) = famVal j' := by
    rintro j j' h
    match h with
    | WalkingParallelFamily.Hom.id j =>
        rw [WalkingParallelFamily.hom_id, Functor.map_id, types_id_apply]
    | WalkingParallelFamily.Hom.line j =>
        rw [Functor.comp_map, parallelFamily_map_left]
        exact hfix j
  exact ⟨(preservesLimitIso F (parallelFamily g)).inv (Types.Limit.mk _ famVal famCoh),
    map_limit_π_preservesLimitIso_inv_mk F (parallelFamily g) famVal famCoh
      WalkingParallelFamily.zero⟩

/-- Variant of `lift_compatible_element_inhabited` requiring only `Nonempty`. -/
lemma lift_compatible_element
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    (xLim : C) (fLim : F.obj xLim)
    (S : Type v) [hS : Nonempty S] (g : S → (xLim ⟶ xLim))
    (hfix : ∀ s, F.map (g s) fLim = fLim) :
    haveI : HasWideEqualizer g := inferInstance
    ∃ fX : F.obj (wideEqualizer g), F.map (wideEqualizer.ι g) fX = fLim := by
  have : Inhabited S := Classical.inhabited_of_nonempty hS
  exact lift_compatible_element_inhabited F xLim fLim S g hfix

/-- Refine `(xLim, fLim)` so that every endomorphism fixing `fLim` is absorbed by `e`. -/
lemma exists_wide_equalizer_pair
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    (xLim : C) (fLim : F.obj xLim) :
    ∃ (X : C) (e : X ⟶ xLim) (fX : F.obj X),
      Mono e ∧
      F.map e fX = fLim ∧
      (∀ (α : xLim ⟶ xLim), F.map α fLim = fLim → e ≫ α = e) := by
  set S : Type v := { α : xLim ⟶ xLim // F.map α fLim = fLim }
  have : Nonempty S := ⟨⟨𝟙 xLim, by simp⟩⟩
  let g : S → (xLim ⟶ xLim) := Subtype.val
  obtain ⟨fX, hfX⟩ := lift_compatible_element F xLim fLim S g (fun s => s.property)
  refine ⟨wideEqualizer g, wideEqualizer.ι g, fX, wideEqualizer.ι_mono, hfX, ?_⟩
  intro α hα
  exact wide_equalizer_comp_self F xLim fLim α hα

/-- Lift an equation `F.map a fX = F.map b fX` across the equalizer of `a` and `b`. -/
lemma exists_equalizer_lift
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    {X Y : C} (a b : X ⟶ Y) (fX : F.obj X) (hab : F.map a fX = F.map b fX) :
    ∃ (X'' : C) (e' : X'' ⟶ X) (f'' : F.obj X''),
      Mono e' ∧ e' ≫ a = e' ≫ b ∧ F.map e' f'' = fX := by
  have hLim : IsLimit (Fork.ofι (F.map (equalizer.ι a b))
      (show F.map (equalizer.ι a b) ≫ F.map a = F.map (equalizer.ι a b) ≫ F.map b by
        rw [← F.map_comp, ← F.map_comp, equalizer.condition])) :=
    isLimitMapConeForkEquiv F _ (isLimitOfPreserves F (equalizerIsEqualizer a b))
  let s : Fork (F.map a) (F.map b) :=
    Fork.ofι (↾fun _ : PUnit.{v + 1} => fX) (by ext _; exact hab)
  obtain ⟨lift, hlift⟩ := Fork.IsLimit.lift' hLim s.ι s.condition
  refine ⟨equalizer a b, equalizer.ι a b, lift PUnit.unit, equalizer.ι_mono,
    equalizer.condition a b, ?_⟩
  have := ConcreteCategory.congr_hom hlift PUnit.unit
  simpa [s, Fork.ofι, Fork.ι] using this

/-- Given a surjective universal pair, refine to a bijective one. -/
lemma exists_bijective_of_surjective_pair
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    (xLim : C) (fLim : F.obj xLim)
    (hsurj_xLim : ∀ (Y : C) (g : F.obj Y), ∃ φ : xLim ⟶ Y, F.map φ fLim = g) :
    ∃ (X : C) (fX : F.obj X),
      (∀ (Y : C) (g : F.obj Y), ∃ φ : X ⟶ Y, F.map φ fX = g) ∧
      (∀ (Y : C) (a b : X ⟶ Y), F.map a fX = F.map b fX → a = b) := by
  obtain ⟨X, e, fX, e_mono, hfX, he_comp⟩ := exists_wide_equalizer_pair F xLim fLim
  refine ⟨X, fX, ?_, ?_⟩
  · intro Y g
    obtain ⟨ψ, hψ⟩ := hsurj_xLim Y g
    refine ⟨e ≫ ψ, ?_⟩
    rw [Functor.map_comp_apply, hfX]
    exact hψ
  · intro Y a b hab
    obtain ⟨X'', e', f'', _, hef, hef''⟩ := exists_equalizer_lift F a b fX hab
    obtain ⟨ψ, hψ⟩ := hsurj_xLim X'' f''
    have h_eα : e ≫ (ψ ≫ e' ≫ e) = e := by
      refine he_comp _ ?_
      rw [Functor.map_comp_apply, Functor.map_comp_apply, hψ, hef'', hfX]
    have h_split : e ≫ ψ ≫ e' = 𝟙 X := by
      refine (cancel_mono e).mp ?_
      rw [Category.id_comp, Category.assoc, Category.assoc]
      exact h_eα
    have : IsSplitEpi e' := IsSplitEpi.mk' ⟨e ≫ ψ, by rw [Category.assoc]; exact h_split⟩
    exact (cancel_epi e').mp hef

/-- Combine the constructions to produce a fully universal pair `(X, fX)`. -/
lemma exists_universal_pair
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    {I : Type v} (x : I → C) (f : ∀ i, F.obj (x i))
    (hsurj : ∀ (y : C) (g : F.obj y), ∃ i, ∃ φ : x i ⟶ y, F.map φ (f i) = g) :
    ∃ (X : C) (fX : F.obj X),
      (∀ (Y : C) (g : F.obj Y), ∃ φ : X ⟶ Y, F.map φ fX = g) ∧
      (∀ (Y : C) (a b : X ⟶ Y), F.map a fX = F.map b fX → a = b) := by
  obtain ⟨xLim, fLim, hxLim⟩ := exists_surjective_pair F x f hsurj
  exact exists_bijective_of_surjective_pair F xLim fLim hxLim

/-- Naturality of the candidate hom-equivalence `φ ↦ F.map φ fX`. -/
lemma map_naturality
    {C : Type u} [Category.{v} C] (F : C ⥤ Type v)
    {X : C} (fX : F.obj X) {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    F.map (f ≫ g) fX = F.map g (F.map f fX) := by
  rw [F.map_comp]
  rfl

/-- Assemble a `CorepresentableBy` from a bijective universal element. -/
noncomputable def corepresentableBy_of_bijective
    {C : Type u} [Category.{v} C] (F : C ⥤ Type v)
    (X : C) (fX : F.obj X)
    (hsurj : ∀ (Y : C) (g : F.obj Y), ∃ φ : X ⟶ Y, F.map φ fX = g)
    (hinj : ∀ (Y : C) (a b : X ⟶ Y), F.map a fX = F.map b fX → a = b) :
    F.CorepresentableBy X where
  homEquiv {Y} :=
    { toFun := fun φ => F.map φ fX
      invFun := fun g => (hsurj Y g).choose
      left_inv := fun φ => hinj Y _ _ (hsurj Y (F.map φ fX)).choose_spec
      right_inv := fun g => (hsurj Y g).choose_spec }
  homEquiv_comp _ _ := map_naturality F fX _ _

end IsCorepresentable_SolutionSet

open IsCorepresentable_SolutionSet

/-- **Stacks 0AHN** (Brown representability criterion).

Let `C` be a category with all (small) limits and `F : C ⥤ Type v` a functor that
preserves limits. Suppose there is a family `{xᵢ}` of objects together with elements
`fᵢ ∈ F xᵢ` such that for every `y : C` and every `g ∈ F y` there exists an `i` and
a morphism `φ : xᵢ ⟶ y` with `F.map φ fᵢ = g`. Then `F` is corepresentable. -/
@[stacks 0AHN, sga "4 I 8.12.8.1" "Sufficiency direction"]
theorem isCorepresentable_of_solutionSet
    {C : Type u} [Category.{v} C] [HasLimitsOfSize.{v, v} C]
    (F : C ⥤ Type v) [PreservesLimitsOfSize.{v, v} F]
    {I : Type v} (x : I → C) (f : ∀ i, F.obj (x i))
    (hsurj : ∀ (y : C) (g : F.obj y), ∃ i, ∃ φ : x i ⟶ y, F.map φ (f i) = g) :
    F.IsCorepresentable := by
  obtain ⟨X, fX, hS, hI⟩ := exists_universal_pair F x f hsurj
  exact ⟨X, ⟨corepresentableBy_of_bijective F X fX hS hI⟩⟩

end CategoryTheory
