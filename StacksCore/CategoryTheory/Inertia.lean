module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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

/-!
# Relative inertia (Stacks 034H, 034I)

The canonical relative-inertia category `I_{S/S'}` of a functor `F : S ⥤ S'`
(the "1-morphism of fibred categories over `C`" in Stacks Section 4.34), together
with its forgetful functor `π : I_{S/S'} ⥤ S` and structure functor to a base `C`.

This is the single shared vocabulary used by the Section 4.34 results
(Tags 042H forgetful map, 04Z3 neutral section, 04Z4 functoriality, 04Z5
comparison) and by the inertia 2-fibre-product statements; it replaces the
per-tag local copies that predated this consolidation.

An object is a pair `(x, α)` with `α : Aut x` an automorphism of `x` lying over
the identity, i.e. `F(α) = id_{F(x)}`. A morphism `(x, α) → (y, β)` is a morphism
`φ : x ⟶ y` of `S` with the square commuting: `φ ≫ β = α ≫ φ` (diagrammatically
`β ∘ φ = φ ∘ α`, matching Stacks). Composition and identities are those of `S`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {S' : Type u₃} [Category.{v₃} S']

/-! #### Compatibility shims for the `Aut` API

Upstream Mathlib restructured `CategoryTheory.Aut` to carry the single field `asIso`
(the former `hom`/`inv` fields were removed). The statements below use the
projections `Aut.hom` / `Aut.inv`; these shims restore them definitionally. -/

universe u v

namespace Aut

/-- The underlying morphism of an automorphism. -/
protected def hom {C : Type u} [Category.{v} C] {X : C} (f : Aut X) : X ⟶ X := f.asIso.hom

/-- The inverse morphism of an automorphism. -/
protected def inv {C : Type u} [Category.{v} C] {X : C} (f : Aut X) : X ⟶ X := f.asIso.inv

/-- An automorphism composed with its inverse is the identity. -/
protected lemma hom_inv_id {C : Type u} [Category.{v} C] {X : C} (f : Aut X) :
    f.hom ≫ f.inv = 𝟙 X := f.asIso.hom_inv_id

/-- The inverse of an automorphism composed with it is the identity. -/
protected lemma inv_hom_id {C : Type u} [Category.{v} C] {X : C} (f : Aut X) :
    f.inv ≫ f.hom = 𝟙 X := f.asIso.inv_hom_id

end Aut

/-- **Stacks 034I.** An object of the relative inertia category `I_{S/S'}` for a
functor `F : S ⥤ S'`: a pair `(x, α)` with `α : Aut x` such that `F(α) = id_{F(x)}`.
The relative inertia `I_{S/S'}` (and the absolute inertia `I_S = I_{S/C}`) is the
fibred category built from this structure. -/
@[stacks 034I]
structure RelativeInertia (F : S ⥤ S') where
  /-- The underlying object `x` of `S`. -/
  obj : S
  /-- The automorphism `α : x → x`. -/
  auto : Aut obj
  /-- The condition `F(α) = id_{F(x)}`. -/
  cond : F.map auto.hom = 𝟙 (F.obj obj)

/-- Since `α` is an automorphism, the condition `F(α) = id` automatically yields
`F(α⁻¹) = id` as well. -/
lemma RelativeInertia.cond_inv {F : S ⥤ S'} (X : RelativeInertia F) :
    F.map X.auto.inv = 𝟙 (F.obj X.obj) := by
  have h : F.map X.auto.hom ≫ F.map X.auto.inv = 𝟙 (F.obj X.obj) := by
    rw [← F.map_comp, X.auto.hom_inv_id, F.map_id]
  rw [X.cond, Category.id_comp] at h
  exact h

/-- A morphism `(x, α) → (y, β)` of `I_{S/S'}`: a morphism `φ : x ⟶ y` of `S` such
that the square commutes, i.e. `φ ≫ β = α ≫ φ` (diagrammatically, `β ∘ φ = φ ∘ α`). -/
structure RelativeInertiaHom (F : S ⥤ S') (X Y : RelativeInertia F) where
  /-- The underlying morphism `φ : x → y` of `S`. -/
  hom : X.obj ⟶ Y.obj
  /-- The commuting-square condition `β ∘ φ = φ ∘ α`. -/
  comm : hom ≫ Y.auto.hom = X.auto.hom ≫ hom

@[ext]
lemma RelativeInertiaHom.ext {F : S ⥤ S'} {X Y : RelativeInertia F}
    {f g : RelativeInertiaHom F X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; simp_all

/-- The identity morphism of `I_{S/S'}` on `(x, α)`: the identity `id_x` of `S`
(which preserves the commuting-square condition). -/
def RelativeInertiaHom.id (F : S ⥤ S') (X : RelativeInertia F) :
    RelativeInertiaHom F X X where
  hom := 𝟙 X.obj
  comm := by simp

/-- Composition of morphisms of `I_{S/S'}` is composition in `S` (which preserves the
commuting-square condition). -/
def RelativeInertiaHom.comp (F : S ⥤ S') {X Y Z : RelativeInertia F}
    (f : RelativeInertiaHom F X Y) (g : RelativeInertiaHom F Y Z) :
    RelativeInertiaHom F X Z where
  hom := f.hom ≫ g.hom
  comm := by rw [Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc]

/-- The relative inertia category `I_{S/S'}`: identities and composition are those
of `S`. -/
instance (F : S ⥤ S') : Category (RelativeInertia F) where
  Hom X Y := RelativeInertiaHom F X Y
  id X := RelativeInertiaHom.id F X
  comp f g := RelativeInertiaHom.comp F f g
  id_comp f := by
    apply RelativeInertiaHom.ext; simp [RelativeInertiaHom.id, RelativeInertiaHom.comp]
  comp_id f := by
    apply RelativeInertiaHom.ext; simp [RelativeInertiaHom.id, RelativeInertiaHom.comp]
  assoc f g h := by apply RelativeInertiaHom.ext; simp [RelativeInertiaHom.comp]

@[simp] lemma RelativeInertia.id_hom (F : S ⥤ S') (X : RelativeInertia F) :
    (𝟙 X : RelativeInertiaHom F X X).hom = 𝟙 X.obj := rfl

@[simp] lemma RelativeInertia.comp_hom (F : S ⥤ S') {X Y Z : RelativeInertia F}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The forgetful functor `π : I_{S/S'} ⥤ S`, `(x, α) ↦ x`, `φ ↦ φ` (Stacks 042H,
Equation 4.34.2.1). -/
def RelativeInertia.π (F : S ⥤ S') : RelativeInertia F ⥤ S where
  obj X := X.obj
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] lemma RelativeInertia.π_obj (F : S ⥤ S') (X : RelativeInertia F) :
    (RelativeInertia.π F).obj X = X.obj := rfl

@[simp] lemma RelativeInertia.π_map (F : S ⥤ S') {X Y : RelativeInertia F} (f : X ⟶ Y) :
    (RelativeInertia.π F).map f = f.hom := rfl

/-- The structure functor `p_I : I_{S/S'} ⥤ C` of a category over `C`,
`(x, α) ↦ p(x)`, `φ ↦ p(φ)`. Equal to `π ⋙ p`. -/
def relativeInertiaStruct (F : S ⥤ S') (p : S ⥤ C) : RelativeInertia F ⥤ C where
  obj X := p.obj X.obj
  map f := p.map f.hom
  map_id := by intro X; simp
  map_comp := by intro X Y Z f g; simp

lemma relativeInertiaStruct_eq (F : S ⥤ S') (p : S ⥤ C) :
    relativeInertiaStruct F p = RelativeInertia.π F ⋙ p := rfl

/-- The (absolute) inertia `I_S = I_{S/C}` of a fibred category `p : S ⥤ C`,
obtained from `RelativeInertia` with `S' = C` and `F = p`. Its objects are pairs
`(x, α)` with `p(α) = id`. -/
abbrev AbsoluteInertia (p : S ⥤ C) := RelativeInertia p

end CategoryTheory
