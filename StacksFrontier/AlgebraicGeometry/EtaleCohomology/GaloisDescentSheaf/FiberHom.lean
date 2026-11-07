module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Maps out of the fibres of a point of a site

Let `Φ` be a point of a site `(C, J)`, with fibre functor `Φ.fiber : C ⥤ Type w`, and let `M` be
a set. The presheaf `U ↦ (Φ.fiber.obj U → M)` is a sheaf. Equivalently, the fibre functor carries
covering families to effective epimorphic families of sets.

If moreover a family of natural endomorphisms of `Φ.fiber` is given, indexed by a type `G` which
also acts on `M`, then the maps commuting with those actions form a subpresheaf, and it is a sheaf
as well. Over a field `K` with absolute Galois group `G` at a geometric point, this is the sheaf
`U ↦ Hom_G(Φ.fiber.obj U, M)` attached to a continuous `G`-set `M` in [Stacks, Tag 03QT].

## Main definitions

* `Stacks.Sites.Point.fiberHomPresheaf` — the presheaf `U ↦ (Φ.fiber.obj U → M)`.
* `Stacks.Sites.Point.fiberHomSheaf` — the same, as a sheaf.
* `Stacks.Sites.Point.equivariantFiberHomPresheaf` — its subpresheaf of equivariant maps.
* `Stacks.Sites.Point.equivariantFiberHomSheaf` — the same, as a sheaf.

## Main results

* `Stacks.Sites.Point.fiberHom_ext` — a map out of the fibre of `U` is determined by its
  restrictions to the fibres of a covering family of `U`.
* `Stacks.Sites.Point.isSheaf_fiberHomPresheaf` — the presheaf of maps out of the fibres is a
  sheaf.
* `Stacks.Sites.Point.isSheaf_equivariantFiberHomPresheaf` — the presheaf of equivariant maps
  out of the fibres is a sheaf.

## References

* [Stacks Project, Tag 00ZT](https://stacks.math.columbia.edu/tag/00ZT), points of a site
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v₁ u₁ u₂

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

namespace Point

variable (Φ : J.Point.{w})

/-- The presheaf on a site whose sections over `U` are the maps from the fibre of a point `Φ`
at `U` to a fixed set `M`, with restriction given by composing with the map of fibres. -/
def fiberHomPresheaf (M : Type w') : Cᵒᵖ ⥤ Type max w w' where
  obj U := Φ.fiber.obj U.unop → M
  map f := ↾ fun g x => g (Φ.fiber.map f.unop x)
  map_id _ := by ext g x; simp
  map_comp _ _ := by ext g x; simp

/-- The sections of `Stacks.Sites.Point.fiberHomPresheaf Φ M` over `U` are the maps from the fibre
of `Φ` at `U` to `M`. -/
@[simp]
theorem fiberHomPresheaf_obj (M : Type w') (U : Cᵒᵖ) :
    (fiberHomPresheaf Φ M).obj U = (Φ.fiber.obj U.unop → M) :=
  rfl

/-- Restriction in `Stacks.Sites.Point.fiberHomPresheaf Φ M` along `f` precomposes a map with the
map of fibres induced by `f`. -/
@[simp]
theorem fiberHomPresheaf_map_apply {M : Type w'} {U V : Cᵒᵖ} (f : U ⟶ V)
    (g : (fiberHomPresheaf Φ M).obj U) (x : Φ.fiber.obj V.unop) :
    (fiberHomPresheaf Φ M).map f g x = g (Φ.fiber.map f.unop x) :=
  rfl

variable {Φ}

/-- **Two lifts of one element of a fibre give the same value.** If two members `f₁`, `f₂` of a
sieve map elements `y₁`, `y₂` of their fibres to the same element of the fibre of the target,
then a compatible family of maps out of the fibres takes the same value on `y₁` and `y₂`. -/
theorem fiberHom_apply_eq_of_map_eq {X : C} {R : Sieve X} {M : Type w'}
    {x : Presieve.FamilyOfElements (fiberHomPresheaf Φ M) R.arrows} (hx : x.Compatible)
    {Y₁ Y₂ : C} {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} (h₁ : R f₁) (h₂ : R f₂)
    {y₁ : Φ.fiber.obj Y₁} {y₂ : Φ.fiber.obj Y₂}
    (hy : Φ.fiber.map f₁ y₁ = Φ.fiber.map f₂ y₂) :
    x f₁ h₁ y₁ = x f₂ h₂ y₂ := by
  let α₁ : Φ.fiber.elementsMk Y₁ y₁ ⟶ Φ.fiber.elementsMk X (Φ.fiber.map f₁ y₁) := ⟨f₁, rfl⟩
  let α₂ : Φ.fiber.elementsMk Y₂ y₂ ⟶ Φ.fiber.elementsMk X (Φ.fiber.map f₁ y₁) := ⟨f₂, hy.symm⟩
  obtain ⟨Z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
  have h' := congrFun (hx q₁.1 q₂.1 h₁ h₂ (congrArg Functor.Elements.Hom.hom fac)) Z.2
  simp only [fiberHomPresheaf_map_apply, unop_op, Quiver.Hom.unop_op] at h'
  rwa [CategoryOfElements.map_snd q₁, CategoryOfElements.map_snd q₂] at h'

variable (Φ)

/-- **A map out of a fibre is determined by its restrictions along a covering sieve.** Two maps
out of the fibre at `X` which agree after restriction along every member of a covering sieve are
equal. -/
theorem fiberHom_ext {X : C} {R : Sieve X} (hR : R ∈ J X) {M : Type w'}
    {g₁ g₂ : (fiberHomPresheaf Φ M).obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f →
      (fiberHomPresheaf Φ M).map f.op g₁ = (fiberHomPresheaf Φ M).map f.op g₂) :
    g₁ = g₂ := by
  funext p
  obtain ⟨Y, f, hf, y, hy⟩ := Φ.jointly_surjective R hR p
  rw [← hy]
  exact congrFun (h f hf) y

/-- **The presheaf of maps out of the fibres of a point of a site is a sheaf.** -/
theorem isSheaf_fiberHomPresheaf (M : Type w') :
    Presieve.IsSheaf J (fiberHomPresheaf Φ M) := by
  classical
  intro X R hR x hx
  choose Y f hf y hy using fun p : Φ.fiber.obj X => Φ.jointly_surjective R hR p
  refine ⟨fun p => x (f p) (hf p) (y p), fun V g hg => ?_, fun g hg => ?_⟩
  · funext v
    exact fiberHom_apply_eq_of_map_eq hx (hf _) hg ((hy _).trans rfl)
  · refine fiberHom_ext Φ hR fun V k hk => ?_
    rw [hg k hk]
    funext v
    exact (fiberHom_apply_eq_of_map_eq hx (hf _) hk ((hy _).trans rfl)).symm

/-- The sheaf of maps out of the fibres of a point of a site. -/
def fiberHomSheaf (M : Type w') : Sheaf J (Type max w w') :=
  ⟨fiberHomPresheaf Φ M, (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_fiberHomPresheaf Φ M)⟩

/-- The underlying presheaf of `Stacks.Sites.Point.fiberHomSheaf Φ M` is
`Stacks.Sites.Point.fiberHomPresheaf Φ M`. -/
@[simp]
theorem fiberHomSheaf_obj (M : Type w') : (fiberHomSheaf Φ M).obj = fiberHomPresheaf Φ M :=
  rfl

section Equivariant

variable {G : Type u₂} (ρ : G → ∀ ⦃U : C⦄, Φ.fiber.obj U → Φ.fiber.obj U)
  (hρ : ∀ (σ : G) ⦃U V : C⦄ (f : U ⟶ V) (p : Φ.fiber.obj U),
    Φ.fiber.map f (ρ σ p) = ρ σ (Φ.fiber.map f p))
  {M : Type w'} (μ : G → M → M)

/-- The subpresheaf of `Stacks.Sites.Point.fiberHomPresheaf` whose sections over `U` are the
maps out of the fibre at `U` which intertwine a family `ρ` of natural endomorphisms of the
fibre functor with a family `μ` of endomorphisms of `M`. -/
def equivariantFiberHomPresheaf : Cᵒᵖ ⥤ Type max w w' where
  obj U := {g : Φ.fiber.obj U.unop → M // ∀ (σ : G) (p : Φ.fiber.obj U.unop),
    g (ρ σ p) = μ σ (g p)}
  map f := ↾ fun g => ⟨fun p => g.1 (Φ.fiber.map f.unop p), fun σ p => by
    change g.1 (Φ.fiber.map f.unop (ρ σ p)) = μ σ (g.1 (Φ.fiber.map f.unop p))
    rw [hρ σ f.unop p, g.2 σ]⟩
  map_id _ := by ext g p; simp
  map_comp _ _ := by ext g p; simp

/-- Restriction in `Stacks.Sites.Point.equivariantFiberHomPresheaf` along `f` precomposes the
underlying map with the map of fibres induced by `f`. -/
@[simp]
theorem equivariantFiberHomPresheaf_map_apply_val {U V : Cᵒᵖ} (f : U ⟶ V)
    (g : (equivariantFiberHomPresheaf Φ ρ hρ μ).obj U) (p : Φ.fiber.obj V.unop) :
    ((equivariantFiberHomPresheaf Φ ρ hρ μ).map f g).1 p = g.1 (Φ.fiber.map f.unop p) :=
  rfl

/-- **The presheaf of equivariant maps out of the fibres of a point of a site is a sheaf.** -/
theorem isSheaf_equivariantFiberHomPresheaf :
    Presieve.IsSheaf J (equivariantFiberHomPresheaf Φ ρ hρ μ) := by
  classical
  intro X R hR x hx
  have hx' : Presieve.FamilyOfElements.Compatible
      (P := fiberHomPresheaf Φ M) (R := R.arrows) (fun _ f hf => (x f hf).1) :=
    fun _ _ _ g₁ g₂ _ _ h₁ h₂ hcomm => congrArg Subtype.val (hx g₁ g₂ h₁ h₂ hcomm)
  obtain ⟨t, ht, uniq⟩ := isSheaf_fiberHomPresheaf Φ M R hR _ hx'
  have htf : ∀ ⦃V : C⦄ (f : V ⟶ X) (hf : R f) (p : Φ.fiber.obj V),
      t (Φ.fiber.map f p) = (x f hf).1 p := fun _ f hf p => congrFun (ht f hf) p
  have hequiv : ∀ (σ : G) (p : Φ.fiber.obj X), t (ρ σ p) = μ σ (t p) := by
    intro σ p
    obtain ⟨V, f, hf, q, hq⟩ := Φ.jointly_surjective R hR p
    rw [← hq, ← hρ σ f q, htf f hf, htf f hf, (x f hf).2 σ q]
  refine ⟨⟨t, hequiv⟩, fun V f hf => ?_, fun g hg => ?_⟩
  · exact Subtype.ext (funext (htf f hf))
  · exact Subtype.ext (uniq _ fun V f hf => congrArg Subtype.val (hg f hf))

/-- The sheaf of equivariant maps out of the fibres of a point of a site. -/
def equivariantFiberHomSheaf : Sheaf J (Type max w w') :=
  ⟨equivariantFiberHomPresheaf Φ ρ hρ μ, (isSheaf_iff_isSheaf_of_type _ _).2
    (isSheaf_equivariantFiberHomPresheaf Φ ρ hρ μ)⟩

/-- The underlying presheaf of `Stacks.Sites.Point.equivariantFiberHomSheaf Φ ρ hρ μ` is
`Stacks.Sites.Point.equivariantFiberHomPresheaf Φ ρ hρ μ`. -/
@[simp]
theorem equivariantFiberHomSheaf_obj :
    (equivariantFiberHomSheaf Φ ρ hρ μ).obj = equivariantFiberHomPresheaf Φ ρ hρ μ :=
  rfl

end Equivariant

end Point

end Stacks.Sites

end
