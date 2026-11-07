module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality

/-!
# The two spectral sequences of a double complex, as functors of the double complex

Let `𝒜` be an abelian category in which the total complex of every double complex
`K^{•,•}` of cochain complexes exists. The total complex `Tot(K^{•,•})` carries two
decreasing filtrations,
```
F_I^p Tot^n = ⨁_{i + j = n, i ≥ p} K^{i,j},        F_{II}^p Tot^n = ⨁_{i + j = n, j ≥ p} K^{i,j},
```
and hence two spectral sequences ([Stacks, Tag 012M], [Stacks, Tag 0130]). Both filtrations and
both spectral sequences are *functorial* in `K^{•,•}`: a morphism of double complexes carries
each step of either filtration of its total complex into the corresponding step, and the
spectral sequence of a filtered complex is functorial in the filtered complex by
[Stacks, Tag 012O]. This file assembles that into honest functors.

This is one of the pieces feeding the Čech-to-cohomology spectral sequence of [Stacks, Tag
01ES]. **Tag 01ES itself is not stated in this file**, and nothing here carries the tag: it is
registered in `CechSpectralSequence/Assembled.lean` as
`Stacks.Cohomology.CechSpectral.cechSpectralSequence`
(`@[stacks 01ES, sga "4 V 3.2" "ringed space, open cover"]`). The route from this file to the
tag runs through `DoubleComplexNaturality.lean` and `FirstQuadrantDoubleComplex.lean`, whose
def-form `HomologicalComplex₂.e₂SpectralSequence₂Functor` refines `totalSpectralSequence₂Functor`
and `totalE₂SpectralSequence₂Functor` of this file, and on into the sequence and second-page
identifications of `SequenceAndSecondPage.lean` and the abutment of `AbutmentIsCohomology.lean`;
see the implementation notes for the per-item mapping.

## Main definitions

* `filteredSpectralSequenceFunctor`: the spectral sequence of a filtered cochain complex, as a
  functor `FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ ⥤ CohomologicalSpectralSequence 𝒜 0`.
* `totalFiltrationFunctor`: the total complex filtered by a weight `w` increasing along both
  differentials, as a functor of the double complex.
* `totalSpectralSequenceFunctor`, `totalSpectralSequence₁Functor`,
  `totalSpectralSequence₂Functor`: the spectral sequence of the total complex filtered by `w`,
  resp. by the first and the second coordinate, as a functor of the double complex.
* `restrictR₀`: a spectral sequence presented from the page `r₀` gives one presented from any
  later page `r₀'`, functorially.
* `totalE₂SpectralSequence₁Functor`, `totalE₂SpectralSequence₂Functor`: the two spectral
  sequences of a double complex, presented from their second page.
* `subcomplexMap`, `totalFiltrationStepMap`, `totalFiltrationMap`: the morphisms underlying
  these functors.

## Main results

* `totalProjector_total_map`: a morphism of double complexes commutes with the projectors of the
  total complexes onto any set of summands, in the sense that it carries the image of one
  projector into the image of the other. This is the whole content of the functoriality of the
  filtrations.
* `totalSpectralSequence₁Functor_obj`, `totalSpectralSequence₂Functor_obj`: the value of either
  functor at `K^{•,•}` is the spectral sequence of `Tot(K^{•,•})` filtered by the first, resp.
  second, coordinate, i.e. the one whose pages [Stacks, Tag 0130] identifies and whose
  convergence [Stacks, Tag 0132] establishes.
* `totalSpectralSequence₁Functor_pageTwo`, `totalSpectralSequence₂Functor_pageTwo`: the second
  pages of the two functors are `'E_2^{p,q} = H^p_I(H^q_{II}(K^{•,•}))` and
  `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))`, which is [Stacks, Tag 0130] (5) and (6) for the
  canonical, functorial spectral sequences.
* `totalSpectralSequence₂Functor_isBounded`: [Stacks, Tag 0132] for the canonical, functorial
  second spectral sequence of a double complex with finite antidiagonals.

## Implementation notes

* The hypothesis that every double complex has a total complex is the typeclass assumption
  `∀ K, K.HasTotal (ComplexShape.up ℤ)` used by Mathlib's `HomologicalComplex₂.totalFunctor`;
  it holds as soon as `𝒜` has countable coproducts. Without it there is no functor, only the
  objectwise construction already available as `HomologicalComplex₂.totalFiltration`.
* The steps of the filtration are the images of the projectors of `Tot^n` onto the summands of
  large weight, so a morphism of double complexes induces a morphism of steps as soon as it
  commutes with those projectors up to the image, which is `totalProjector_total_map`. The
  morphism on filtered objects is then `FilteredObject.homMk`, whose naturality in `p` is
  automatic because the inclusions of the steps are monomorphisms.
* The identifications of the pages in [Stacks, Tag 0130] and the convergence statement of
  [Stacks, Tag 0132] are `Nonempty`-valued, so they say nothing about naturality of the
  comparisons. What [Stacks, Tag 01ES] therefore needs beyond this file — items (a)-(c),
  not stated *here*, are each proved elsewhere in the module:
  (a) a `def`-form refinement of `HomologicalComplex₂.exists_iso_pages_totalFiltration₂`
  producing a *natural* isomorphism `''E_2^{p,q} ≅ H^p_{II}(H^q_I(K^{•,•}))`, supplied as
  `Stacks.Cohomology.CechSpectral.cechPageTwoIso` (`SequenceAndSecondPage.lean`); (b) likewise
  for the abutment, a `def`-form refinement of
  `HomologicalComplex₂.isBounded_and_converges_totalFiltration₂`, supplied as
  `Stacks.Cohomology.CechSpectral.cechAbutment` (`AbutmentIsCohomology.lean`); and (c) a
  comparison of a `CohomologicalSpectralSequence` carried on `ℤ × ℤ` with an
  `E₂CohomologicalSpectralSequenceNat` carried on `ℕ × ℕ`, which needs the first-quadrant
  vanishing of the pages and does not follow from `restrictR₀` alone; the comparison is
  supplied objectwise by `CategoryTheory.SpectralSequence.natRestrictE₂Comp`
  (`Algebra/Homology/SpectralSequence/NatRestrict.lean`), which is what
  `SequenceAndSecondPage.lean` consumes, while the functor-level
  `Stacks.Cohomology.CechSpectral.totalE₂SpectralSequenceNat₂Functor` of
  `FirstQuadrantPieces.lean` — a version whose hypothesis demands first-quadrant vanishing
  of *every* double complex over the ambient category — is not usable there, as
  `FirstQuadrantDoubleComplex.lean` records. The route
  from here to 01ES also needs the Čech double complex of an injective resolution to be
  functorial in the sheaf, for which
  `CochainComplex.filteredSpectralSequenceMap_hom_eq_of_filteredHomotopic` is the available
  input. With these ingredients the tag is registered as
  `Stacks.Cohomology.CechSpectral.cechSpectralSequence` in `Assembled.lean`.

## References

* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 012O](https://stacks.math.columbia.edu/tag/012O)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂ Opposite

universe v u

namespace Stacks.Cohomology.CechSpectral

variable {C : Type u} [Category.{v} C] [Abelian C]

section Subcomplex

variable {I : Type*} {c : ComplexShape I} {L L' : HomologicalComplex C c}

/-- A morphism `f : L ⟶ L'` of homological complexes which carries each subobject `F n ⊆ L.X n`
into `F' n ⊆ L'.X n` induces a morphism of the subcomplexes these families cut out. -/
noncomputable def subcomplexMap (f : L ⟶ L')
    (F : ∀ n, Subobject (L.X n)) (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j))
    (F' : ∀ n, Subobject (L'.X n)) (hF' : ∀ i j, (F' j).Factors ((F' i).arrow ≫ L'.d i j))
    (hf : ∀ n, (F' n).Factors ((F n).arrow ≫ f.f n)) :
    HomologicalComplex.subcomplexOfSubobjects L F hF ⟶
      HomologicalComplex.subcomplexOfSubobjects L' F' hF' where
  f n := (F' n).factorThru ((F n).arrow ≫ f.f n) (hf n)
  comm' i j _ := by
    rw [← cancel_mono (F' j).arrow]
    dsimp only [HomologicalComplex.subcomplexOfSubobjects]
    simp only [Category.assoc, Subobject.factorThru_arrow, Subobject.factorThru_arrow_assoc]
    rw [f.comm]

/-- The morphism of subcomplexes induced by `f` is, in each degree, the restriction of `f`. -/
@[reassoc (attr := simp)]
lemma subcomplexMap_f_arrow (f : L ⟶ L')
    (F : ∀ n, Subobject (L.X n)) (hF : ∀ i j, (F j).Factors ((F i).arrow ≫ L.d i j))
    (F' : ∀ n, Subobject (L'.X n)) (hF' : ∀ i j, (F' j).Factors ((F' i).arrow ≫ L'.d i j))
    (hf : ∀ n, (F' n).Factors ((F n).arrow ≫ f.f n)) (n : I) :
    (subcomplexMap f F hF F' hF' hf).f n ≫ (F' n).arrow = (F n).arrow ≫ f.f n :=
  Subobject.factorThru_arrow _ _ (hf n)

end Subcomplex

section Bicomplex

variable {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]

/-- A morphism `φ : K^{•,•} ⟶ L^{•,•}` of double complexes carries the image of the projector of
`Tot(K^{•,•})^n` onto the summands satisfying `P` into the image of the corresponding projector
of `Tot(L^{•,•})^n`: composing with the target projector does not change `Tot(φ)` restricted to
those summands. -/
lemma totalProjector_total_map (φ : K ⟶ L) (P : ℤ → ℤ → Prop) [∀ i j, Decidable (P i j)]
    (n : ℤ) :
    K.totalProjector P n ≫ (total.map φ (ComplexShape.up ℤ)).f n ≫ L.totalProjector P n =
      K.totalProjector P n ≫ (total.map φ (ComplexShape.up ℤ)).f n := by
  refine total.hom_ext _ fun i j h => ?_
  rw [ι_totalProjector_assoc, ι_totalProjector_assoc]
  split_ifs with hP
  · rw [ιTotal_map_assoc, ιTotal_map, ι_totalProjector, ite_eq_left hP]
  · rw [zero_comp, zero_comp]

variable (w : ℤ → ℤ → ℤ) (h₁ : ∀ i j, w i j ≤ w (i + 1) j) (h₂ : ∀ i j, w i j ≤ w i (j + 1))

/-- The morphism `F_w^p Tot(K^{•,•}) ⟶ F_w^p Tot(L^{•,•})` of filtration steps induced by a
morphism `φ : K^{•,•} ⟶ L^{•,•}` of double complexes. -/
noncomputable def totalFiltrationStepMap (φ : K ⟶ L) (p : ℤ) :
    K.totalFiltrationStep w h₁ h₂ p ⟶ L.totalFiltrationStep w h₁ h₂ p :=
  subcomplexMap (total.map φ (ComplexShape.up ℤ)) _ _ _ _ fun n =>
    imageSubobject_factors_arrow_comp_of_comp_eq _ _ _ (totalProjector_total_map φ _ n)

/-- On the `p`-th filtration step in degree `n`, the morphism induced by `φ` is the restriction
of `Tot(φ)`. -/
@[reassoc (attr := simp)]
lemma totalFiltrationStepMap_f_arrow (φ : K ⟶ L) (p n : ℤ) :
    (totalFiltrationStepMap w h₁ h₂ φ p).f n ≫
        (imageSubobject (L.totalProjector (fun i j => p ≤ w i j) n)).arrow =
      (imageSubobject (K.totalProjector (fun i j => p ≤ w i j) n)).arrow ≫
        (total.map φ (ComplexShape.up ℤ)).f n :=
  subcomplexMap_f_arrow _ _ _ _ _ _ _

/-- The morphism of filtered complexes `Tot(K^{•,•}) ⟶ Tot(L^{•,•})`, for the filtrations by the
weight `w`, induced by a morphism `φ : K^{•,•} ⟶ L^{•,•}` of double complexes. -/
noncomputable def totalFiltrationMap (φ : K ⟶ L) :
    K.totalFiltration w h₁ h₂ ⟶ L.totalFiltration w h₁ h₂ :=
  FilteredObject.homMk (total.map φ (ComplexShape.up ℤ))
    (fun p => totalFiltrationStepMap w h₁ h₂ φ p.unop) fun p => by
      ext n
      exact totalFiltrationStepMap_f_arrow w h₁ h₂ φ p.unop n

/-- The underlying morphism of complexes of `totalFiltrationMap` is `Tot(φ)`. -/
@[simp]
lemma totalFiltrationMap_hom (φ : K ⟶ L) :
    (totalFiltrationMap w h₁ h₂ φ).hom = total.map φ (ComplexShape.up ℤ) := rfl

variable (C)
variable [∀ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
  K.HasTotal (ComplexShape.up ℤ)]

/-- The total complex of a double complex, filtered by a weight `w` which increases along both
differentials, as a functor of the double complex. -/
noncomputable def totalFiltrationFunctor :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      FilteredObject (CochainComplex C ℤ) ℤᵒᵖ where
  obj K := K.totalFiltration w h₁ h₂
  map φ := totalFiltrationMap w h₁ h₂ φ
  map_id K := by ext; simp
  map_comp φ ψ := by ext; simp

end Bicomplex

/-- **[Stacks, Tag 012O] for filtered complexes, as a functor.** The spectral sequence
`(E_r, d_r)_{r ≥ 0}` of a filtered cochain complex, together with the morphism of spectral
sequences induced by a morphism of filtered complexes. -/
noncomputable def filteredSpectralSequenceFunctor :
    FilteredObject (CochainComplex C ℤ) ℤᵒᵖ ⥤ CohomologicalSpectralSequence C 0 where
  obj M := CochainComplex.filteredSpectralSequence M
  map φ := CochainComplex.filteredSpectralSequenceMap φ
  map_id := CochainComplex.filteredSpectralSequenceMap_id
  map_comp := CochainComplex.filteredSpectralSequenceMap_comp

section Functor

variable (C)
variable [∀ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
  K.HasTotal (ComplexShape.up ℤ)]

/-- The spectral sequence of the total complex of a double complex filtered by a weight `w`
which increases along both differentials, as a functor of the double complex. -/
noncomputable def totalSpectralSequenceFunctor (w : ℤ → ℤ → ℤ)
    (h₁ : ∀ i j, w i j ≤ w (i + 1) j) (h₂ : ∀ i j, w i j ≤ w i (j + 1)) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      CohomologicalSpectralSequence C 0 :=
  totalFiltrationFunctor C w h₁ h₂ ⋙ filteredSpectralSequenceFunctor

/-- The first spectral sequence `('E_r, 'd_r)` of a double complex, that of the total complex
filtered by the first coordinate, as a functor of the double complex. -/
noncomputable def totalSpectralSequence₁Functor :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      CohomologicalSpectralSequence C 0 :=
  totalSpectralSequenceFunctor C (fun i _ => i) (fun _ _ => by omega) fun _ _ => le_rfl

/-- The second spectral sequence `(''E_r, ''d_r)` of a double complex, that of the total complex
filtered by the second coordinate, as a functor of the double complex. -/
noncomputable def totalSpectralSequence₂Functor :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      CohomologicalSpectralSequence C 0 :=
  totalSpectralSequenceFunctor C (fun _ j => j) (fun _ _ => le_rfl) fun _ _ => by omega

/-- The first spectral sequence of a double complex is the spectral sequence of its total
complex filtered by the first coordinate; so [Stacks, Tag 0130] identifies its pages and
[Stacks, Tag 0132] gives its convergence. -/
lemma totalSpectralSequence₁Functor_obj
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    (totalSpectralSequence₁Functor C).obj K =
      CochainComplex.filteredSpectralSequence K.totalFiltration₁ := rfl

/-- The second spectral sequence of a double complex is the spectral sequence of its total
complex filtered by the second coordinate; so [Stacks, Tag 0130] identifies its pages and
[Stacks, Tag 0132] gives its convergence. -/
lemma totalSpectralSequence₂Functor_obj
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    (totalSpectralSequence₂Functor C).obj K =
      CochainComplex.filteredSpectralSequence K.totalFiltration₂ := rfl

/-- **[Stacks, Tag 0130] (5) for the functorial first spectral sequence.** The second page of
`totalSpectralSequence₁Functor` at `K^{•,•}` is `'E_2^{p,q} = H^p_I(H^q_{II}(K^{•,•}))`. -/
theorem totalSpectralSequence₁Functor_pageTwo
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    Nonempty ((((totalSpectralSequence₁Functor C).obj K).page 2 zero_le_two).X (p, q) ≅
      (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology p) := by
  obtain ⟨e, -, hδ, -, -, -⟩ := CochainComplex.exists_iso_spectralSequence_page
    K.totalFiltration₁ _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  obtain ⟨-, -, h2⟩ := K.exists_iso_pages_totalFiltration₁ _ (fun _ _ => rfl) _
    (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) ((totalSpectralSequence₁Functor C).obj K) e hδ
  exact h2 p q

/-- **[Stacks, Tag 0130] (6) for the functorial second spectral sequence.** The second page of
`totalSpectralSequence₂Functor` at `K^{•,•}` is `''E_2^{p,q} = H^p_{II}(H^q_I(K^{•,•}))`. -/
theorem totalSpectralSequence₂Functor_pageTwo
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p q : ℤ) :
    Nonempty ((((totalSpectralSequence₂Functor C).obj K).page 2 zero_le_two).X (p, q) ≅
      (K.homology q).homology p) := by
  obtain ⟨e, -, hδ, -, -, -⟩ := CochainComplex.exists_iso_spectralSequence_page
    K.totalFiltration₂ _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  obtain ⟨-, -, h2⟩ := K.exists_iso_pages_totalFiltration₂ _ (fun _ _ => rfl) _
    (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) ((totalSpectralSequence₂Functor C).obj K) e hδ
  exact h2 p q

/-- **[Stacks, Tag 0132] for the functorial second spectral sequence.** If every antidiagonal of
`K^{•,•}` has only finitely many nonzero terms, then the second spectral sequence of
`K^{•,•}` is bounded: each antidiagonal of its zeroth page has finitely many nonzero terms, and
at each bidegree the differentials vanish from some page on. -/
theorem totalSpectralSequence₂Functor_isBounded
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    (∀ n : ℤ, {p : ℤ |
      ¬ IsZero ((((totalSpectralSequence₂Functor C).obj K).page 0).X (p, n - p))}.Finite) ∧
    ∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (((totalSpectralSequence₂Functor C).obj K).page r hr).d (p, q) (p + r, q - r + 1) = 0 := by
  obtain ⟨e, -, -, -, -, -⟩ := CochainComplex.exists_iso_spectralSequence_page
    K.totalFiltration₂ _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  obtain ⟨c₁, -, c₃, -, -⟩ := K.isBounded_and_converges_totalFiltration₂ hK _ (fun _ _ => rfl) _
    (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ => rfl)
    ((totalSpectralSequence₂Functor C).obj K) e
  exact ⟨c₁, c₃⟩

end Functor

section Restrict

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ r₀' : ℤ}

/-- A spectral sequence presented from the page `r₀`, read as one presented from a later page
`r₀'`: the pages and the identifications of a page's homology with the next page are those of
the original from `r₀'` on. This is a functor, since a morphism of spectral sequences is a
family of morphisms of pages. -/
def restrictR₀ (h : r₀ ≤ r₀') : SpectralSequence C c r₀ ⥤ SpectralSequence C c r₀' where
  obj E :=
    { page r hr := E.page r (h.trans hr)
      iso r r' pq hrr' hr := E.iso r r' pq hrr' (h.trans hr) }
  map f :=
    { hom r hr := f.hom r (h.trans hr)
      comm r r' pq hrr' hr := f.comm r r' pq hrr' (h.trans hr) }

/-- The pages of a restricted spectral sequence are the pages of the original. -/
@[simp]
lemma restrictR₀_obj_page (h : r₀ ≤ r₀') (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀' ≤ r) :
    ((restrictR₀ h).obj E).page r hr = E.page r (h.trans hr) := rfl

end Restrict

section SecondPage

variable (C)
variable [∀ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
  K.HasTotal (ComplexShape.up ℤ)]

/-- The first spectral sequence of a double complex, presented from its second page, as a
functor of the double complex. -/
noncomputable def totalE₂SpectralSequence₁Functor :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      E₂CohomologicalSpectralSequence C :=
  totalSpectralSequence₁Functor C ⋙ restrictR₀ (by omega)

/-- The second spectral sequence of a double complex, presented from its second page, as a
functor of the double complex. -/
noncomputable def totalE₂SpectralSequence₂Functor :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⥤
      E₂CohomologicalSpectralSequence C :=
  totalSpectralSequence₂Functor C ⋙ restrictR₀ (by omega)

end SecondPage

end Stacks.Cohomology.CechSpectral

end
