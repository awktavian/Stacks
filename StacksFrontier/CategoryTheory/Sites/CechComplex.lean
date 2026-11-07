module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Čech complex of a family of objects, degreewise

Mathlib's `CategoryTheory.cechComplexFunctor` sends a presheaf `P : Cᵒᵖ ⥤ A` to the Čech
cochain complex associated with a family `U : ι → C`, but it is built through several layers
of abstraction (formal coproducts, their Čech simplicial object, and the alternating coface
map complex) and nothing is proved about the resulting complex. This file supplies the
degreewise description, the formula for the differential, and the augmentation by the
sections over the terminal object.

## Main definitions

* `inter U x` is the product of the objects `U (x a)` for `a : Fin m`, the formal
  "intersection" of the members of the family selected by the tuple `x`.
* `interMap U x h` is the reindexing map `inter U x ⟶ inter U (x ∘ h)`.
* `π U P n x` is the projection of the degree `n` term of the Čech complex onto the factor
  indexed by `x : Fin (n + 1) → ι`, and `lift U P` is the corresponding universal map.
* `face U P n i` is the `i`-th restriction map from degree `n` to degree `n + 1`.
* `Stacks.Cohomology.CechZero.aug U P hT` is the map from the sections over a terminal object
  `T`, presented by an `IsTerminal` witness `hT`, into degree `0`, and
  `Stacks.Cohomology.CechZero.augFork U P hT` packages it as a fork of the first
  differential.

## Main results

* `isLimitFan` says that the degree `n` term of the Čech complex is the product, indexed by
  `x : Fin (n + 1) → ι`, of the values `P.obj (op (inter U x))`, with projections `π U P n x`.
* `d_eq` and `d_comp_π` give the explicit formula for the Čech differential: the alternating
  sum of the restrictions along the face maps. `d_zero_comp_π` is the degree `0` case, the
  difference of the two restrictions to a pairwise intersection.
* `Stacks.Cohomology.CechZero.aug_comp_d` says that the augmentation is a cycle in degree `0`;
  hence `Stacks.Cohomology.CechZero.homologyZeroIso` identifies the degree `0` homology with
  the sections over the terminal object as soon as the augmentation is a kernel of the first
  differential.
* `inter_eq_iInf`, `inter_eq_single`, `inter_eq_inf` and `terminal_eq_top` identify these
  constructions in a complete lattice, for instance the lattice of open sets of a
  topological space: the products are infima and the terminal object is `⊤`.

## Implementation notes

The degree `n` term of the Čech complex is *definitionally* the product
`∏ᶜ (fun x : Fin (n + 1) → ι ↦ P.obj (op (inter U x)))`, because `ToType ⦋n⦌` reduces to
`Fin (n + 1)` and `FormalCoproduct.power` is defined by exactly this formula. All the
definitions below therefore take the definitionally correct value and only ascribe the type
that mentions `cechComplexFunctor`. The price is that Mathlib's simp lemmas for products do
not apply syntactically, so the basic lemmas are proved by `exact`ing the corresponding
product lemma rather than by `simp`, and composite statements are assembled in term mode
rather than by `rw`.

The Čech complex of Mathlib is the one associated with the Čech nerve of
`∐ i, U i ⟶ ⊤_ C`: the objects appearing in degree `n` are plain products in `C`, not fibre
products over a base. This is the correct complex for a covering of the terminal object,
which is the situation of a covering of a topological space by open sets. Accordingly the
augmentation is by the sections over the terminal object.

The augmentation takes the terminal object as an `IsTerminal` witness rather than reading it
off a `HasTerminal` instance. On a slice site the terminal object one wants is `Over.mk (𝟙 V)`
on the nose, so that the open underlying it is `V` definitionally and no transport of sections
along an equality of opens is needed downstream; `terminalIsTerminal` recovers the `⊤_ C`
case. `CategoryTheory.Limits.IsTerminal` has no `comp_from`, only `HasTerminal` does, so the
one identity needed in `aug_comp_d` comes from `IsTerminal.hom_ext` instead.

The identification of the degree `0` homology with the sections over the terminal object is
stated conditionally on the augmentation being a kernel of the first differential, which is
exactly the sheaf condition for the covering family; deducing that hypothesis from Mathlib's
sheaf condition is not done here.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v' u u'

namespace Stacks.CategoryTheory.CechComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [HasFiniteProducts C] {ι : Type w} (U : ι → C)

/-! ### Intersections of the members of the family -/

/-- `inter U x` is the product of the objects `U (x a)` for `a : Fin m`. It is the formal
"intersection" of the members of the family `U` selected by the tuple `x`; for a family of
open subsets of a topological space it is their intersection, see `inter_eq_iInf`. -/
noncomputable def inter {m : ℕ} (x : Fin m → ι) : C :=
  ∏ᶜ fun a ↦ U (x a)

/-- The projection of `inter U x` onto the factor `U (x a)`. -/
noncomputable def interπ {m : ℕ} (x : Fin m → ι) (a : Fin m) : inter U x ⟶ U (x a) :=
  Pi.π _ a

/-- `inter U x` is the product of the objects `U (x a)`, with projections `interπ U x`. -/
noncomputable def isLimitInterFan {m : ℕ} (x : Fin m → ι) :
    IsLimit (Fan.mk (inter U x) (interπ U x)) :=
  productIsProduct _

/-- Two morphisms into `inter U x` agree as soon as they agree after composing with every
projection. -/
@[ext]
theorem inter_hom_ext {m : ℕ} {x : Fin m → ι} {T : C} {f g : T ⟶ inter U x}
    (h : ∀ a, f ≫ interπ U x a = g ≫ interπ U x a) : f = g :=
  Pi.hom_ext _ _ h

/-- The morphism into `inter U x` determined by a family of morphisms into the factors. -/
noncomputable def interLift {m : ℕ} {x : Fin m → ι} {T : C} (f : ∀ a, T ⟶ U (x a)) :
    T ⟶ inter U x :=
  Pi.lift f

/-- The morphism `interLift U f`, composed with the projection onto `U (x a)`, is `f a`. -/
@[reassoc (attr := simp)]
theorem interLift_comp_interπ {m : ℕ} {x : Fin m → ι} {T : C} (f : ∀ a, T ⟶ U (x a)) (a) :
    interLift U f ≫ interπ U x a = f a :=
  Pi.lift_comp_π _ _

/-- The reindexing morphism `inter U x ⟶ inter U (x ∘ h)` induced by a map of index sets
`h : Fin m' → Fin m`. For open subsets of a topological space this is the inclusion of an
intersection into a larger one taken over fewer indices. -/
noncomputable def interMap {m m' : ℕ} (x : Fin m → ι) (h : Fin m' → Fin m) :
    inter U x ⟶ inter U (x ∘ h) :=
  interLift U fun a ↦ interπ U x (h a)

/-- The reindexing morphism `interMap U x h`, composed with the projection indexed by `a`, is
the projection of `inter U x` indexed by `h a`. -/
@[reassoc (attr := simp)]
theorem interMap_comp_interπ {m m' : ℕ} (x : Fin m → ι) (h : Fin m' → Fin m) (a : Fin m') :
    interMap U x h ≫ interπ U (x ∘ h) a = interπ U x (h a) :=
  interLift_comp_interπ U _ a

/-- Reindexing along the identity is the identity. -/
@[simp]
theorem interMap_id {m : ℕ} (x : Fin m → ι) : interMap U x id = 𝟙 _ :=
  inter_hom_ext U fun a ↦
    (interMap_comp_interπ U x id a).trans (Category.id_comp _).symm

/-- Reindexing along a composite `h ∘ h'` is the composite of the reindexing morphisms. -/
@[reassoc]
theorem interMap_comp {m m' m'' : ℕ} (x : Fin m → ι) (h : Fin m' → Fin m)
    (h' : Fin m'' → Fin m') :
    interMap U x (h ∘ h') = interMap U x h ≫ interMap U (x ∘ h) h' :=
  inter_hom_ext U fun a ↦
    (interMap_comp_interπ U x (h ∘ h') a).trans
      (((interMap_comp_interπ U x h (h' a)).symm.trans
          (congrArg (interMap U x h ≫ ·)
            (interMap_comp_interπ U (x ∘ h) h' a).symm)).trans
        (Category.assoc _ _ _).symm)

/-! ### The degreewise description of the Čech complex -/

variable [Preadditive A] (P : Cᵒᵖ ⥤ A)

omit [HasProducts.{w} A] [HasFiniteProducts C] in
/-- The differential of the alternating coface map complex of a cosimplicial object is the
alternating sum of its coface maps. Mathlib states this for the alternating *face* map
complex of a simplicial object only. -/
@[sga "4 XVII 5.5.3" "partial"]
theorem alternatingCofaceMapComplex_obj_d (X : CosimplicialObject A) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex A).obj X).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i := by
  simp [AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]

/-- The projection of the degree `n` term of the Čech complex of `U` onto the factor
indexed by the tuple `x : Fin (n + 1) → ι`, namely the sections of `P` over `inter U x`. -/
noncomputable def π (n : ℕ) (x : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).obj P).X n ⟶ P.obj (op (inter U x)) :=
  Pi.π _ x

/-- **Degreewise description of the Čech complex.** The degree `n` term of the Čech complex
of `U` is the product, indexed by the tuples `x : Fin (n + 1) → ι`, of the sections of `P`
over `inter U x`, with projections `π U P n`. -/
noncomputable def isLimitFan (n : ℕ) :
    IsLimit (Fan.mk (((cechComplexFunctor U).obj P).X n) (π U P n)) :=
  productIsProduct _

/-- Two morphisms into the degree `n` term of the Čech complex agree as soon as they agree
after composing with every projection. -/
@[ext]
theorem hom_ext {n : ℕ} {T : A} {f g : T ⟶ ((cechComplexFunctor U).obj P).X n}
    (h : ∀ x, f ≫ π U P n x = g ≫ π U P n x) : f = g :=
  Pi.hom_ext _ _ h

/-- The morphism into the degree `n` term of the Čech complex determined by a family of
morphisms into the sections of `P` over the objects `inter U x`. -/
noncomputable def lift {n : ℕ} {T : A}
    (f : ∀ x : Fin (n + 1) → ι, T ⟶ P.obj (op (inter U x))) :
    T ⟶ ((cechComplexFunctor U).obj P).X n :=
  Pi.lift f

/-- The morphism `lift U P f`, composed with the projection indexed by `x`, is `f x`. -/
@[reassoc (attr := simp)]
theorem lift_comp_π {n : ℕ} {T : A} (f : ∀ x : Fin (n + 1) → ι, T ⟶ P.obj (op (inter U x)))
    (x : Fin (n + 1) → ι) : lift U P f ≫ π U P n x = f x :=
  Pi.lift_comp_π _ _

/-- The `i`-th restriction map from degree `n` to degree `n + 1` of the Čech complex: its
component at the tuple `y : Fin (n + 2) → ι` is the restriction of a section over
`inter U (y ∘ i.succAbove)`, that is, over the intersection in which the `i`-th index of `y`
has been omitted. -/
noncomputable def face (n : ℕ) (i : Fin (n + 2)) :
    ((cechComplexFunctor U).obj P).X n ⟶ ((cechComplexFunctor U).obj P).X (n + 1) :=
  lift U P fun y ↦ π U P n (y ∘ i.succAbove) ≫ P.map (interMap U y i.succAbove).op

/-- The component of `face U P n i` at the tuple `y` is the restriction from
`inter U (y ∘ i.succAbove)` to `inter U y`. -/
@[reassoc (attr := simp)]
theorem face_comp_π (n : ℕ) (i : Fin (n + 2)) (y : Fin (n + 2) → ι) :
    face U P n i ≫ π U P (n + 1) y =
      π U P n (y ∘ i.succAbove) ≫ P.map (interMap U y i.succAbove).op :=
  lift_comp_π U P _ y

/-- The coface maps of the cosimplicial object underlying the Čech complex, composed with a
projection, are the restrictions along the face maps of the family. -/
theorem δ_comp_π (n : ℕ) (i : Fin (n + 2)) (y : Fin (n + 2) → ι) :
    ((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj P).δ i ≫ π U P (n + 1) y =
      π U P n (y ∘ i.succAbove) ≫ P.map (interMap U y i.succAbove).op := by
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map]
  exact Pi.lift_comp_π _ _

/-- The coface maps of the cosimplicial object underlying the Čech complex are the
restriction maps `face`. -/
theorem δ_eq_face (n : ℕ) (i : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj P).δ i = face U P n i :=
  hom_ext U P (n := n + 1) fun y ↦
    (δ_comp_π U P n i y).trans (face_comp_π U P n i y).symm

/-- **The Čech differential.** The differential from degree `n` to degree `n + 1` is the
alternating sum of the restriction maps `face U P n i`. -/
theorem d_eq (n : ℕ) :
    ((cechComplexFunctor U).obj P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • face U P n i :=
  (alternatingCofaceMapComplex_obj_d
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P) n).trans
    (Finset.sum_congr rfl fun i _ ↦
      congrArg (fun z ↦ (-1 : ℤ) ^ (i : ℕ) • z) (δ_eq_face U P n i))

/-- **The Čech differential, componentwise.** Composed with the projection indexed by
`y : Fin (n + 2) → ι`, the differential from degree `n` to degree `n + 1` is the alternating
sum of the restrictions along the face maps `Fin.succAbove i`. -/
theorem d_comp_π (n : ℕ) (y : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ π U P (n + 1) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (π U P n (y ∘ i.succAbove) ≫ P.map (interMap U y i.succAbove).op) := by
  rw [d_eq, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [Preadditive.zsmul_comp, face_comp_π]

/-- **The Čech differential in degree `0`.** It is the difference of the two restriction
maps: the component at `y : Fin 2 → ι` is the restriction from `U (y 1)` minus the
restriction from `U (y 0)`, both to `inter U y`. -/
theorem d_zero_comp_π (y : Fin 2 → ι) :
    ((cechComplexFunctor U).obj P).d 0 1 ≫ π U P 1 y =
      π U P 0 (fun _ ↦ y 1) ≫ P.map (interMap U y fun _ ↦ 1).op -
        π U P 0 (fun _ ↦ y 0) ≫ P.map (interMap U y fun _ ↦ 0).op := by
  have h₀ : (0 : Fin 2).succAbove = fun _ : Fin 1 ↦ (1 : Fin 2) :=
    funext (Fin.forall_fin_one.2 rfl)
  have h₁ : (1 : Fin 2).succAbove = fun _ : Fin 1 ↦ (0 : Fin 2) :=
    funext (Fin.forall_fin_one.2 rfl)
  rw [d_comp_π, Fin.sum_univ_two, h₀, h₁]
  simp [sub_eq_add_neg, Function.comp_def]

/-! ### The case of a complete lattice

For a family of open subsets of a topological space, or more generally in a complete lattice
viewed as a category, the products occurring in the Čech complex are infima and the terminal
object is the top element. -/

section CompleteLattice

variable {L : Type u} [CompleteLattice L]

/-- In a complete lattice, the terminal object is the top element. -/
theorem terminal_eq_top [HasTerminal L] : (⊤_ L) = ⊤ :=
  le_antisymm le_top (leOfHom (terminal.from ⊤))

variable [HasFiniteProducts L] {ι : Type w} (V : ι → L)

/-- In a complete lattice, the object `inter V x` is the infimum of the `V (x a)`. -/
theorem inter_eq_iInf {m : ℕ} (x : Fin m → ι) : inter V x = ⨅ a, V (x a) :=
  le_antisymm (le_iInf fun a ↦ leOfHom (interπ V x a))
    (leOfHom (interLift V fun a ↦ homOfLE (iInf_le _ a)))

/-- The degree `0` intersections: in a complete lattice, `inter V x` for a single index is
the corresponding member of the family. -/
theorem inter_eq_single (x : Fin 1 → ι) : inter V x = V (x 0) :=
  (inter_eq_iInf V x).trans (iInf_unique _)

/-- The degree `1` intersections: in a complete lattice, `inter V y` for a pair of indices
is the infimum of the two corresponding members of the family. -/
theorem inter_eq_inf (y : Fin 2 → ι) : inter V y = V (y 0) ⊓ V (y 1) :=
  (inter_eq_iInf V y).trans
    (le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
      (le_iInf (Fin.forall_fin_two.2 ⟨inf_le_left, inf_le_right⟩)))

end CompleteLattice

end Stacks.CategoryTheory.CechComplex

namespace Stacks.Cohomology.CechZero

open Stacks.CategoryTheory.CechComplex

/-! ### The augmentation at a chosen terminal object -/

section Aug

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [HasFiniteProducts C] [Preadditive A]
  {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A) {T : C} (hT : IsTerminal T)

/-- **The augmentation of the Čech complex at a chosen terminal object.** The map from the
sections of `P` over `T` to the degree-`0` term of the Čech complex of `U`, given on each
factor by restriction along the unique morphism to `T`. -/
noncomputable def aug : P.obj (op T) ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  lift U P fun x ↦ P.map (hT.from (inter U x)).op

/-- The component of the augmentation at the tuple `x` is the restriction from `T` to
`inter U x`. -/
@[reassoc (attr := simp)]
theorem aug_comp_π (x : Fin 1 → ι) :
    aug U P hT ≫ π U P 0 x = P.map (hT.from (inter U x)).op :=
  lift_comp_π U P _ x

/-- The augmentation lands in the degree-`0` cycles: the two restrictions appearing in the
degree-`0` differential agree, because both are induced by a morphism to a terminal object. -/
theorem aug_comp_d : aug U P hT ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 := by
  refine hom_ext U P (n := 1) fun y ↦ ?_
  have key : ∀ i : Fin 2, aug U P hT ≫ ((-1 : ℤ) ^ (i : ℕ) •
      (π U P 0 (y ∘ i.succAbove) ≫ P.map (interMap U y i.succAbove).op)) =
      (-1 : ℤ) ^ (i : ℕ) • P.map (hT.from (inter U y)).op := fun i ↦ by
    rw [Preadditive.comp_zsmul, ← Category.assoc, aug_comp_π, ← P.map_comp, ← op_comp,
      hT.hom_ext (interMap U y i.succAbove ≫ hT.from (inter U (y ∘ i.succAbove)))
        (hT.from (inter U y))]
  rw [Limits.zero_comp, Category.assoc, d_comp_π, Preadditive.comp_sum,
    Finset.sum_congr rfl fun i _ ↦ key i, Fin.sum_univ_two]
  simp

/-- The augmentation, viewed as a fork of the first Čech differential. The Čech description of
`H⁰` is the assertion that this fork is a limit. -/
noncomputable def augFork : KernelFork (((cechComplexFunctor U).obj P).d 0 1) :=
  KernelFork.ofι (aug U P hT) (aug_comp_d U P hT)

/-- The inclusion of the fork `augFork U P hT` is the augmentation. -/
@[simp]
theorem augFork_ι : (augFork U P hT).ι = aug U P hT := rfl

/-- **`H⁰` of the Čech complex.** If the augmentation at a terminal object `T` is a kernel of
the first Čech differential — which for a sheaf and a covering family is the sheaf
condition — then the degree-`0` homology of the Čech complex is the object of sections over
`T`. -/
noncomputable def homologyZeroIso [((cechComplexFunctor U).obj P).HasHomology 0]
    (h : IsLimit (augFork U P hT)) :
    ((cechComplexFunctor U).obj P).homology 0 ≅ P.obj (op T) :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫
    IsLimit.conePointUniqueUpToIso
      (((cechComplexFunctor U).obj P).cyclesIsKernel 0 1 (by simp)) h

end Aug

end Stacks.Cohomology.CechZero

end
