module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Approximating a pair by pairs of finite type over `ℤ`

Fix a commutative ring `A` and a finitely generated ideal `I ⊆ A`. An *approximation* of the
pair `(A, I)` is a pair `(A₀, I₀)` with `A₀ ⊆ A` a `ℤ`-subalgebra of finite type and `I₀ ⊆ A₀`
an ideal with `I₀ A = I`, and a morphism of approximations is an inclusion `A₀ ⊆ A₀'` with
`I₀' = I₀ A₀'` — the same notion of morphism of pairs as on the category of all pairs, namely
`J₀ = Ideal.map φ I₀`.

This file constructs that indexing category and proves the facts which the proof of Stacks 099D
asserts and leaves unproved ("the category of these `(A₀, I₀) → (A, I)` is filtered (details
omitted)", "moreover `colim A₀ = A`"):

* the approximations of `(A, I)` are a **filtered** index category — a directed partial order,
  nonempty as soon as `I` is finitely generated;
* `A` is the **colimit** of the `A₀` and `I` is the colimit of the `I₀`, compatibly, both
  colimits being directed unions of subobjects of `A`;
* the assignment is **functorial**: a ring map `φ : A → B` with `J = IB` carries an approximation
  of `(A, I)` to an approximation of `(B, J)`, monotonically, and these transports compose on the
  nose.

Filteredness is the step with content. Given two approximations `(A₀, I₀)` and `(A₀', I₀')`, the
subalgebra `A₀ ⊔ A₀'` need not dominate either of them *as a pair*: a morphism out of `(A₀, I₀)`
must carry `I₀` onto the whole ideal at the target, so the ideal at the target is forced to be
`I₀ A₀''` and must simultaneously equal `I₀' A₀''`. The two ideals `I₀ A` and `I₀' A` do agree —
both are `I` — so each generator of `I₀'` is an `A`-combination of generators of `I₀` and
conversely; adjoining the finitely many coefficients of these finitely many relations to
`A₀ ⊔ A₀'` produces a subalgebra, still of finite type over `ℤ`, over which the two ideals have
become equal. This is `Stacks.PairApproximation.PairApprox.exists_ge_ge`.

The ideal of an approximation is automatically finitely generated, `A₀` being a `ℤ`-algebra of
finite type and hence Noetherian; no finiteness hypothesis on `I₀` is carried.

## Main definitions

* `Stacks.PairApproximation.PairApprox` — an approximation of `(A, I)` by a pair of finite type
  over `ℤ`.
* the `PartialOrder` instance on `Stacks.PairApproximation.PairApprox A I` — `p ≤ q` is a
  morphism of pairs from `p` to `q` over `(A, I)`.
* `Stacks.PairApproximation.PairApprox.ofSpanningSet` — the approximation cut out by a subalgebra
  containing a generating set of `I`.
* `Stacks.PairApproximation.PairApprox.transport` — the functoriality: the image of an
  approximation of `(A, I)` under a ring map `φ : A → B` with `J = IB`.
* `Stacks.PairApproximation.PairApprox.transportFunctor` — the same transport, as a functor
  between the index categories.

## Main results

* `Stacks.PairApproximation.PairApprox.exists_ge_ge`, and the `IsDirected` instance — any two
  approximations are dominated by a third.
* `Stacks.PairApproximation.PairApprox.nonempty`,
  `Stacks.PairApproximation.PairApprox.isFiltered` — **the index category is filtered.**
* `Stacks.PairApproximation.PairApprox.iSup_sub`,
  `Stacks.PairApproximation.PairApprox.existsUnique_ringHom` — **`A = colim A₀`**, as a directed
  union and as a universal property.
* `Stacks.PairApproximation.PairApprox.iUnion_ideal` — **`I = colim I₀`**, compatibly with the
  previous: the union of the `I₀`, taken inside `A`, is `I`.
* `Stacks.PairApproximation.PairApprox.transport_monotone`,
  `Stacks.PairApproximation.PairApprox.transport_transport`,
  `Stacks.PairApproximation.PairApprox.transport_id` — functoriality in the pair, strictly.
* `Stacks.PairApproximation.PairApprox.transportFunctor_comp`,
  `Stacks.PairApproximation.PairApprox.transportFunctor_id` — the same, as an equality of
  functors: the transports compose **on the nose**, with no coherence isomorphism.

## Implementation notes

The index is a *partial order*, not a general comma category: an approximation is a subalgebra of
`A` together with an ideal, and a morphism is the inclusion. The source's index category is the
comma category of all pair maps `(A₀, I₀) → (A, I)` from pairs with `A₀` of the form
`ℤ[x₁, …, x_n]/J`; every such map factors through its image, which is a `ℤ`-subalgebra of `A` of
finite type, so the order used here is the full subcategory on the images, and it is cofinal.
Taking it instead of the comma category buys three things: the index is a type in the same
universe as `A`, so colimits over it exist with no skeleton argument; filteredness reduces to
directedness; and the transport along a ring map is strictly functorial, the image of a
subalgebra under a composite being the composite of the images.

`A = colim A₀` is recorded twice. `iSup_sub` says the approximating subalgebras have supremum
`⊤`, which is what "directed union" means here, and `existsUnique_ringHom` turns that into the
universal property of the colimit, so that no particular model of the colimit need be chosen; the
proof of the latter is `Subalgebra.iSupLift`, with uniqueness from the covering property
`exists_mem_sub`. Compatibility of the two colimit statements is automatic in this form: both
sides are computed inside `A`, so `I = colim I₀` is literally the statement that the union of the
`I₀` is `I`.

No `@[stacks]` attribute is attached. This file is infrastructure for tag 099D — the indexing
category of the colimit its proof takes over — and not a clause of its statement, which is about
the complexes `K(A, I)`, their augmentations and their transition maps.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 00QY](https://stacks.math.columbia.edu/tag/00QY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.PairApproximation

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- **An approximation of the pair `(A, I)` by a pair of finite type over `ℤ`.** A `ℤ`-subalgebra
`sub ⊆ A` of finite type together with an ideal `ideal ⊆ sub` generating `I` in `A`.

These are the objects of the index category over which the proof of Stacks 099D takes its
colimit, with the inclusion `sub ⊆ A` playing the role of the structure map `(A₀, I₀) → (A, I)`
and `map_ideal` of the requirement `I₀ A = I` on it. -/
structure PairApprox (A : Type u) [CommRing A] (I : Ideal A) where
  /-- The approximating subalgebra `A₀ ⊆ A`. -/
  sub : Subalgebra ℤ A
  /-- `A₀` is of finite type over `ℤ`. -/
  sub_fg : sub.FG
  /-- The approximating ideal `I₀ ⊆ A₀`. -/
  ideal : Ideal sub
  /-- `I₀` generates `I`. -/
  map_ideal : Ideal.map sub.val ideal = I

namespace PairApprox

variable {I : Ideal A} {J : Ideal B} {K : Ideal C}

/-! ### Elementary lemmas on inclusions of subalgebras -/

private theorem inclusion_eq_id (S : Subalgebra ℤ A) (h : S ≤ S) :
    Subalgebra.inclusion h = AlgHom.id ℤ S :=
  AlgHom.ext fun _ => Subtype.ext rfl

private theorem inclusion_comp {S T U : Subalgebra ℤ A} (hST : S ≤ T) (hTU : T ≤ U) :
    (Subalgebra.inclusion hTU).comp (Subalgebra.inclusion hST) =
      Subalgebra.inclusion (hST.trans hTU) :=
  AlgHom.ext fun _ => Subtype.ext rfl

private theorem map_eq_self_of_apply_eq {R : Type*} [CommRing R] {f : R →ₐ[ℤ] R}
    (h : ∀ x, f x = x) (L : Ideal R) : L.map f = L := by
  rw [show f = AlgHom.id ℤ R from AlgHom.ext h, Ideal.map_idₐ]

private theorem map_toIntAlgHom (φ : A →+* B) (L : Ideal A) :
    L.map φ.toIntAlgHom = L.map φ := rfl

/-- Two approximations with the same subalgebra, the second ideal being the image of the first
under the inclusion, are equal. -/
private theorem eq_of_sub_eq {p q : PairApprox A I} (h : p.sub = q.sub)
    (e : q.ideal = p.ideal.map (Subalgebra.inclusion h.le)) : p = q := by
  obtain ⟨ps, phfg, pi, pm⟩ := p
  obtain ⟨qs, qhfg, qi, qm⟩ := q
  obtain rfl : ps = qs := h
  simp only [inclusion_eq_id, Ideal.map_idₐ] at e
  subst e
  rfl

/-! ### The index category -/

/-- **The index category of the approximations of `(A, I)`.** A morphism `p ≤ q` is an inclusion
`p.sub ⊆ q.sub` carrying `p.ideal` onto `q.ideal`, which is the condition `J₀ = Ideal.map φ I₀`
defining a morphism of pairs; the morphisms over `(A, I)` are then exactly the inclusions, so the
index is a partial order. -/
instance instPartialOrder : PartialOrder (PairApprox A I) where
  le p q := ∃ h : p.sub ≤ q.sub, q.ideal = p.ideal.map (Subalgebra.inclusion h)
  le_refl p := ⟨le_rfl, by rw [inclusion_eq_id, Ideal.map_idₐ]⟩
  le_trans p q r := by
    rintro ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    exact ⟨h₁.trans h₂, by rw [e₂, e₁, Ideal.map_mapₐ, inclusion_comp]⟩
  le_antisymm p q := by
    obtain ⟨ps, phfg, pi, pm⟩ := p
    obtain ⟨qs, qhfg, qi, qm⟩ := q
    rintro ⟨h₁, e₁⟩ ⟨h₂, -⟩
    obtain rfl : ps = qs := le_antisymm h₁ h₂
    simp only [inclusion_eq_id, Ideal.map_idₐ] at e₁
    subst e₁
    rfl

/-- `p ≤ q` if and only if `p.sub ≤ q.sub` and the ideal of `q` is the image of the ideal of `p`
under the inclusion. -/
theorem le_def {p q : PairApprox A I} :
    p ≤ q ↔ ∃ h : p.sub ≤ q.sub, q.ideal = p.ideal.map (Subalgebra.inclusion h) := Iff.rfl

/-- If `p ≤ q`, then the subalgebra of `p` is contained in that of `q`. -/
theorem sub_le_sub {p q : PairApprox A I} (h : p ≤ q) : p.sub ≤ q.sub := (le_def.1 h).1

/-! ### Approximations cut out by a subalgebra -/

/-- **The approximation cut out by a subalgebra containing a generating set of `I`.** If `D` is a
`ℤ`-subalgebra of `A` of finite type and `s ⊆ D` generates `I`, the ideal of `D` generated by `s`
is an approximating ideal. -/
def ofSpanningSet (D : Subalgebra ℤ A) (hD : D.FG) (s : Set A) (hs : s ⊆ (D : Set A))
    (hspan : Ideal.span s = I) : PairApprox A I where
  sub := D
  sub_fg := hD
  ideal := Ideal.span (D.val ⁻¹' s)
  map_ideal := by
    rw [Ideal.map_span,
      Set.image_preimage_eq_of_subset (fun y hy => ⟨⟨y, hs hy⟩, rfl⟩), hspan]

/-- The subalgebra underlying `ofSpanningSet D hD s hs hspan` is `D`. -/
@[simp]
theorem ofSpanningSet_sub (D : Subalgebra ℤ A) (hD : D.FG) (s : Set A) (hs : s ⊆ (D : Set A))
    (hspan : Ideal.span s = I) : (ofSpanningSet D hD s hs hspan).sub = D := rfl

/-- The ideal of `ofSpanningSet D hD s hs hspan` is the ideal of `D` generated by the elements of
`D` lying in `s`. -/
@[simp]
theorem ofSpanningSet_ideal (D : Subalgebra ℤ A) (hD : D.FG) (s : Set A) (hs : s ⊆ (D : Set A))
    (hspan : Ideal.span s = I) :
    (ofSpanningSet D hD s hs hspan).ideal = Ideal.span (D.val ⁻¹' s) := rfl

/-- The approximations of `(A, I)` are nonempty as soon as `I` is finitely generated: take for
`A₀` the subalgebra generated by a finite generating set of `I`. -/
theorem nonempty (hI : I.FG) : Nonempty (PairApprox A I) := by
  obtain ⟨s, hs⟩ := hI
  exact ⟨ofSpanningSet (Algebra.adjoin ℤ (s : Set A)) (Subalgebra.fg_adjoin_finset s) (s : Set A)
    Algebra.subset_adjoin hs⟩

/-- Every element of `A` lies in the approximating subalgebra of some approximation: adjoin it to
the subalgebra generated by a finite generating set of `I`. -/
theorem exists_mem_sub (hI : I.FG) (a : A) : ∃ p : PairApprox A I, a ∈ p.sub := by
  obtain ⟨s, hs⟩ := hI
  refine ⟨ofSpanningSet (Algebra.adjoin ℤ (insert a (s : Set A)))
    (Subalgebra.fg_def.2 ⟨insert a (s : Set A), s.finite_toSet.insert a, rfl⟩) (s : Set A)
    (fun y hy => Algebra.subset_adjoin (Set.mem_insert_of_mem a hy)) hs, ?_⟩
  exact Algebra.subset_adjoin (Set.mem_insert a _)

/-! ### Finite generation of the approximating ideal -/

/-- The approximating subalgebra of an approximation is a Noetherian ring, being of finite type
over `ℤ`. -/
theorem isNoetherianRing_sub (p : PairApprox A I) : IsNoetherianRing p.sub :=
  isNoetherianRing_of_fg p.sub_fg

/-- The approximating ideal is finitely generated, by a family indexed by a `Fin n`. -/
theorem exists_fin_span (p : PairApprox A I) :
    ∃ (n : ℕ) (f : Fin n → p.sub), Ideal.span (Set.range f) = p.ideal := by
  have := p.isNoetherianRing_sub
  exact Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian p.ideal)

/-- A finite family generating the approximating ideal generates `I` after passing to `A`. -/
theorem span_range_val (p : PairApprox A I) {n : ℕ} {f : Fin n → p.sub}
    (hf : Ideal.span (Set.range f) = p.ideal) :
    Ideal.span (Set.range fun i => ((f i : p.sub) : A)) = I := by
  rw [show (Set.range fun i => ((f i : p.sub) : A)) = p.sub.val '' Set.range f by
    rw [← Set.range_comp]; rfl, ← Ideal.map_span, hf, p.map_ideal]

/-! ### Directedness -/

/-- If the value of `y : D` is an `A`-combination of the values of `x : Fin n → D` all of whose
coefficients lie in `D`, then `y` lies in the ideal of `D` generated by the `x i`. -/
private theorem mem_span_of_coeff_mem {D : Subalgebra ℤ A} {n : ℕ} (x : Fin n → D) (y : D)
    (c : Fin n → A) (hc : ∀ i, c i ∈ D) (h : (y : A) = ∑ i, c i * ((x i : D) : A)) :
    y ∈ Ideal.span (Set.range x) := by
  refine Ideal.mem_span_range_iff_exists_fun.2 ⟨fun i => ⟨c i, hc i⟩, Subtype.ext ?_⟩
  push_cast
  exact h.symm

/-- **Any two approximations are dominated by a third.** This is the filteredness that the proof
of Stacks 099D leaves to the reader.

Write `I` both as the ideal generated by the images of a finite family of generators of `p.ideal`
and as the one generated by a finite family of generators of `q.ideal`. Each generator on one
side is an `A`-combination of the generators on the other; adjoining to `p.sub ⊔ q.sub` the
finitely many coefficients of these finitely many relations gives a subalgebra `D` of finite type
over which the two ideals `p.ideal D` and `q.ideal D` coincide, and `D` with that common ideal
dominates both `p` and `q`. -/
theorem exists_ge_ge (p q : PairApprox A I) : ∃ r : PairApprox A I, p ≤ r ∧ q ≤ r := by
  classical
  obtain ⟨m, f, hf⟩ := p.exists_fin_span
  obtain ⟨n, g, hg⟩ := q.exists_fin_span
  have hspans : Ideal.span (Set.range fun j => ((g j : q.sub) : A)) =
      Ideal.span (Set.range fun i => ((f i : p.sub) : A)) :=
    (q.span_range_val hg).trans (p.span_range_val hf).symm
  -- the coefficients expressing each `g j` through the `f i`, and conversely
  have hc : ∀ j, ∃ c : Fin m → A, ∑ i, c i * ((f i : p.sub) : A) = ((g j : q.sub) : A) := by
    intro j
    refine Ideal.mem_span_range_iff_exists_fun.1 ?_
    rw [← hspans]
    exact Ideal.subset_span (Set.mem_range_self j)
  have hd : ∀ i, ∃ d : Fin n → A, ∑ j, d j * ((g j : q.sub) : A) = ((f i : p.sub) : A) := by
    intro i
    refine Ideal.mem_span_range_iff_exists_fun.1 ?_
    rw [hspans]
    exact Ideal.subset_span (Set.mem_range_self i)
  choose c hcEq using hc
  choose d hdEq using hd
  -- the subalgebra generated by `p.sub`, `q.sub` and those coefficients
  set T : Set A := Set.range (fun x : Fin n × Fin m => c x.1 x.2) ∪
    Set.range (fun x : Fin m × Fin n => d x.1 x.2)
  set D : Subalgebra ℤ A := p.sub ⊔ q.sub ⊔ Algebra.adjoin ℤ T
  have hDfg : D.FG :=
    (p.sub_fg.sup q.sub_fg).sup
      (Subalgebra.fg_def.2 ⟨T, (Set.finite_range _).union (Set.finite_range _), rfl⟩)
  have hpD : p.sub ≤ D := le_sup_left.trans le_sup_left
  have hqD : q.sub ≤ D := le_sup_right.trans le_sup_left
  have hTD : T ⊆ (D : Set A) := fun _ hx =>
    (le_sup_right : Algebra.adjoin ℤ T ≤ D) (Algebra.subset_adjoin hx)
  have hcD : ∀ j i, c j i ∈ D := fun j i => hTD (Or.inl ⟨(j, i), rfl⟩)
  have hdD : ∀ i j, d i j ∈ D := fun i j => hTD (Or.inr ⟨(i, j), rfl⟩)
  -- over `D` the two ideals agree
  have hFD : Ideal.span (Set.range fun i => Subalgebra.inclusion hpD (f i)) =
      Ideal.span (Set.range fun j => Subalgebra.inclusion hqD (g j)) := by
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      exact mem_span_of_coeff_mem _ _ (d i) (hdD i) (hdEq i).symm
    · rintro _ ⟨j, rfl⟩
      exact mem_span_of_coeff_mem _ _ (c j) (hcD j) (hcEq j).symm
  refine ⟨{ sub := D
            sub_fg := hDfg
            ideal := p.ideal.map (Subalgebra.inclusion hpD)
            map_ideal := by
              rw [Ideal.map_mapₐ,
                show D.val.comp (Subalgebra.inclusion hpD) = p.sub.val from
                  AlgHom.ext fun _ => rfl,
                p.map_ideal] }, le_def.2 ⟨hpD, rfl⟩, le_def.2 ⟨hqD, ?_⟩⟩
  show p.ideal.map (Subalgebra.inclusion hpD) = q.ideal.map (Subalgebra.inclusion hqD)
  rw [← hf, ← hg, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
  exact hFD

/-- The approximations of a pair are directed: any two lie below a common one. -/
instance instIsDirected : IsDirected (PairApprox A I) (· ≤ ·) :=
  ⟨fun p q => exists_ge_ge p q⟩

/-- **The approximations of a pair form a filtered category.** With the inclusions of
approximations as morphisms, the index category of the colimit in the proof of Stacks 099D is
filtered: it is a nonempty directed partial order. -/
theorem isFiltered (hI : I.FG) : IsFiltered (PairApprox A I) :=
  have := nonempty (I := I) hI
  inferInstance

/-! ### `A = colim A₀` and `I = colim I₀` -/

/-- **`A = colim A₀`, as a directed union.** The approximating subalgebras have supremum `A`. -/
theorem iSup_sub (hI : I.FG) : ⨆ p : PairApprox A I, p.sub = ⊤ :=
  eq_top_iff.2 fun a _ => by
    obtain ⟨p, hp⟩ := exists_mem_sub hI a
    exact le_iSup (fun p : PairApprox A I => p.sub) p hp

/-- **`A = colim A₀`, as a universal property.** A family of ring maps out of the approximating
subalgebras, compatible with the inclusions, extends uniquely to a ring map out of `A`. -/
theorem existsUnique_ringHom (hI : I.FG) {T : Type*} [Ring T]
    (F : ∀ p : PairApprox A I, p.sub →+* T)
    (hF : ∀ {p q : PairApprox A I} (h : p ≤ q) (x : p.sub),
      F q (Subalgebra.inclusion (sub_le_sub h) x) = F p x) :
    ∃! G : A →+* T, ∀ (p : PairApprox A I) (x : p.sub), G (x : A) = F p x := by
  have := nonempty (I := I) hI
  have hdir : Directed (· ≤ ·) (fun p : PairApprox A I => p.sub) :=
    Monotone.directed_le fun _ _ => sub_le_sub
  have hcompat : ∀ (p q : PairApprox A I) (h : p.sub ≤ q.sub),
      (F p).toIntAlgHom = ((F q).toIntAlgHom).comp (Subalgebra.inclusion h) := by
    intro p q h
    obtain ⟨r, h₁, h₂⟩ := exists_ge_ge p q
    refine AlgHom.ext fun x => ?_
    have e₃ : Subalgebra.inclusion (sub_le_sub h₂) (Subalgebra.inclusion h x) =
        Subalgebra.inclusion (sub_le_sub h₁) x := Subtype.ext rfl
    simp only [RingHom.toIntAlgHom_coe, AlgHom.coe_comp, Function.comp_apply]
    rw [← hF h₁ x, ← hF h₂ (Subalgebra.inclusion h x), e₃]
  obtain ⟨G, hGval⟩ : ∃ G : (⊤ : Subalgebra ℤ A) →ₐ[ℤ] T,
      ∀ (p : PairApprox A I) (x : p.sub), G ⟨(x : A), trivial⟩ = F p x :=
    ⟨Subalgebra.iSupLift (fun p : PairApprox A I => p.sub) hdir
        (fun p => (F p).toIntAlgHom) hcompat ⊤ (by rw [iSup_sub hI]),
      fun _ x => Subalgebra.iSupLift_mk (K := fun p : PairApprox A I => p.sub)
        (T := (⊤ : Subalgebra ℤ A)) x trivial⟩
  refine ⟨{ toFun := fun a => G ⟨a, trivial⟩
            map_one' := map_one G
            map_mul' := fun a b => map_mul G ⟨a, trivial⟩ ⟨b, trivial⟩
            map_zero' := map_zero G
            map_add' := fun a b => map_add G ⟨a, trivial⟩ ⟨b, trivial⟩ },
    fun p x => hGval p x, fun G' hG' => ?_⟩
  refine RingHom.ext fun a => ?_
  obtain ⟨p, hp⟩ := exists_mem_sub hI a
  exact (hG' p ⟨a, hp⟩).trans (hGval p ⟨a, hp⟩).symm

/-- **`I = colim I₀`, compatibly with `A = colim A₀`.** The union of the approximating ideals,
taken inside `A`, is `I`. -/
theorem iUnion_ideal (hI : I.FG) :
    (⋃ p : PairApprox A I, p.sub.val '' (p.ideal : Set p.sub)) = (I : Set A) := by
  classical
  refine Set.Subset.antisymm (Set.iUnion_subset fun p => ?_) fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    have h : p.sub.val y ∈ Ideal.map p.sub.val p.ideal := Ideal.mem_map_of_mem _ hy
    rwa [p.map_ideal] at h
  · obtain ⟨n, v, hv⟩ : ∃ (n : ℕ) (v : Fin n → A), Ideal.span (Set.range v) = I :=
      Submodule.fg_iff_exists_fin_generating_family.1 hI
    have hx' : x ∈ Ideal.span (Set.range v) := by rwa [hv]
    obtain ⟨cf, hcf⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx'
    set T : Set A := Set.range v ∪ Set.range cf
    set D : Subalgebra ℤ A := Algebra.adjoin ℤ T
    have hvD : ∀ i, v i ∈ D := fun i => Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)
    have hcfD : ∀ i, cf i ∈ D := fun i => Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
    have hrange : Set.range v ⊆ (D : Set A) := Set.range_subset_iff.2 hvD
    have hxD : x ∈ D := by
      rw [← hcf]
      exact sum_mem fun i _ => mul_mem (hcfD i) (hvD i)
    have hmem : (⟨x, hxD⟩ : D) ∈ Ideal.span (Set.range fun i => (⟨v i, hvD i⟩ : D)) :=
      mem_span_of_coeff_mem _ _ cf hcfD hcf.symm
    refine Set.mem_iUnion.2 ⟨ofSpanningSet D
      (Subalgebra.fg_def.2 ⟨T, (Set.finite_range v).union (Set.finite_range cf), rfl⟩)
      (Set.range v) hrange hv, ⟨x, hxD⟩, ?_, rfl⟩
    exact Ideal.span_mono (fun _ hy => by
      obtain ⟨i, rfl⟩ := hy
      exact ⟨i, rfl⟩) hmem

/-! ### Functoriality in the pair -/

/-- A ring map restricted to a subalgebra and its image. -/
def restrictToImage (φ : A →ₐ[ℤ] B) (D : Subalgebra ℤ A) : D →ₐ[ℤ] D.map φ :=
  (φ.comp D.val).codRestrict _ fun x => Subalgebra.mem_map.2 ⟨(x : A), x.2, rfl⟩

/-- `restrictToImage φ D` sends an element `x` of `D` to `φ x`. -/
@[simp]
theorem coe_restrictToImage (φ : A →ₐ[ℤ] B) (D : Subalgebra ℤ A) (x : D) :
    ((restrictToImage φ D x : D.map φ) : B) = φ (x : A) := rfl

/-- **Functoriality in the pair.** A ring map `φ : A → B` with `J = IB` carries an approximation
of `(A, I)` to one of `(B, J)`: take the image subalgebra and the image ideal. -/
def transport (φ : A →+* B) (hJ : J = I.map φ) (p : PairApprox A I) : PairApprox B J where
  sub := p.sub.map φ.toIntAlgHom
  sub_fg := p.sub_fg.map _
  ideal := p.ideal.map (restrictToImage φ.toIntAlgHom p.sub)
  map_ideal := by
    rw [Ideal.map_mapₐ,
      show (p.sub.map φ.toIntAlgHom).val.comp (restrictToImage φ.toIntAlgHom p.sub) =
        φ.toIntAlgHom.comp p.sub.val from AlgHom.ext fun _ => rfl,
      ← Ideal.map_mapₐ, p.map_ideal, map_toIntAlgHom, hJ]

/-- The subalgebra of `transport φ hJ p` is the image under `φ` of the subalgebra of `p`. -/
@[simp]
theorem transport_sub (φ : A →+* B) (hJ : J = I.map φ) (p : PairApprox A I) :
    (transport φ hJ p).sub = p.sub.map φ.toIntAlgHom := rfl

/-- The ideal of `transport φ hJ p` is the image of the ideal of `p` under the restriction
`restrictToImage φ.toIntAlgHom p.sub`. -/
@[simp]
theorem transport_ideal (φ : A →+* B) (hJ : J = I.map φ) (p : PairApprox A I) :
    (transport φ hJ p).ideal = p.ideal.map (restrictToImage φ.toIntAlgHom p.sub) := rfl

/-- The transport of approximations along a ring map is monotone: it is a functor between the
index categories. -/
theorem transport_monotone (φ : A →+* B) (hJ : J = I.map φ) :
    Monotone (transport φ hJ : PairApprox A I → PairApprox B J) := by
  rintro p q h
  obtain ⟨h₀, e⟩ := le_def.1 h
  have hle₀ : p.sub.map φ.toIntAlgHom ≤ q.sub.map φ.toIntAlgHom := Subalgebra.map_mono h₀
  have key : q.ideal.map (restrictToImage φ.toIntAlgHom q.sub) =
      (p.ideal.map (restrictToImage φ.toIntAlgHom p.sub)).map (Subalgebra.inclusion hle₀) := by
    rw [e, Ideal.map_mapₐ, Ideal.map_mapₐ]
    congr 1
  exact le_def.2 ⟨hle₀, key⟩

/-- **The transports compose on the nose.** The image of a subalgebra under a composite is the
composite of the images, so the functors of `transport` compose strictly — which is what makes
the colimit over the approximations a strictly functorial construction on pairs. -/
theorem transport_transport (φ : A →+* B) (ψ : B →+* C) (hJ : J = I.map φ) (hK : K = J.map ψ)
    (p : PairApprox A I) :
    transport ψ hK (transport φ hJ p) =
      transport (ψ.comp φ) (by rw [hK, hJ, Ideal.map_map]) p := by
  have hsub : (p.sub.map φ.toIntAlgHom).map ψ.toIntAlgHom =
      p.sub.map (ψ.comp φ).toIntAlgHom := by
    rw [Subalgebra.map_map,
      show ψ.toIntAlgHom.comp φ.toIntAlgHom = (ψ.comp φ).toIntAlgHom from
        AlgHom.ext fun _ => rfl]
  have key : p.ideal.map (restrictToImage (ψ.comp φ).toIntAlgHom p.sub) =
      ((p.ideal.map (restrictToImage φ.toIntAlgHom p.sub)).map
        (restrictToImage ψ.toIntAlgHom (p.sub.map φ.toIntAlgHom))).map
          (Subalgebra.inclusion hsub.le) := by
    rw [Ideal.map_mapₐ, Ideal.map_mapₐ]
    congr 1
  exact eq_of_sub_eq hsub key

/-- The transport along the identity is the identity. -/
theorem transport_id (p : PairApprox A I) :
    transport (RingHom.id A) (Ideal.map_id I).symm p = p := by
  have hsub : p.sub.map (RingHom.id A).toIntAlgHom = p.sub := by
    rw [show (RingHom.id A).toIntAlgHom = AlgHom.id ℤ A from AlgHom.ext fun _ => rfl,
      Subalgebra.map_id]
  have key : p.ideal = (p.ideal.map (restrictToImage (RingHom.id A).toIntAlgHom p.sub)).map
      (Subalgebra.inclusion hsub.le) := by
    rw [Ideal.map_mapₐ]
    exact (map_eq_self_of_apply_eq (fun _ => Subtype.ext rfl) _).symm
  exact eq_of_sub_eq hsub key

/-- **The transport, as a functor of index categories.** This is the functoriality which makes
the colimit over the approximations a construction indexed by the *pair*, rather than by a pair
together with extra choices. -/
def transportFunctor (φ : A →+* B) (hJ : J = I.map φ) :
    PairApprox A I ⥤ PairApprox B J :=
  (transport_monotone φ hJ).functor

/-- On objects, `transportFunctor φ hJ` acts as `transport φ hJ`. -/
@[simp]
theorem transportFunctor_obj (φ : A →+* B) (hJ : J = I.map φ) (p : PairApprox A I) :
    (transportFunctor φ hJ).obj p = transport φ hJ p := rfl

/-- **The transport functors compose strictly.** -/
theorem transportFunctor_comp (φ : A →+* B) (ψ : B →+* C) (hJ : J = I.map φ)
    (hK : K = J.map ψ) :
    transportFunctor φ hJ ⋙ transportFunctor ψ hK =
      transportFunctor (ψ.comp φ) (by rw [hK, hJ, Ideal.map_map]) :=
  CategoryTheory.Functor.ext (transport_transport φ ψ hJ hK) fun _ _ _ => by subsingleton

/-- **The transport functor along the identity is the identity.** -/
theorem transportFunctor_id :
    transportFunctor (RingHom.id A) (Ideal.map_id I).symm = 𝟭 (PairApprox A I) :=
  CategoryTheory.Functor.ext transport_id fun _ _ _ => by subsingleton

end PairApprox

end Stacks.PairApproximation

end
