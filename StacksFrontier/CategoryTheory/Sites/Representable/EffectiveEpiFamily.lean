module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksCore.Tactic.StacksAttribute

/-! # Effective epimorphic families

Stacks 00WP defines, in an *arbitrary* category `C`, when a family of morphisms
`{X i ⟶ B}` is an effective epimorphic family: all `X i ⟶ B` must be representable
morphisms (Stacks 001X, i.e. all their base changes exist), and for every object `Y` the
diagram of sets
`Mor(B, Y) → ∏ᵢ Mor(X i, Y) ⇉ ∏₍ᵢ,ⱼ₎ Mor(X i ×_B X j, Y)`
must be an equalizer.  The family is a *universal* effective epimorphic family when every
base change of it is again an effective epimorphic family.

Mathlib has the pullback-free reformulation `CategoryTheory.EffectiveEpiFamily` ("the
generated sieve is effective epimorphic"), but neither the representability requirement nor
the pullback-stable variant.  This file gives the two Stacks definitions and identifies the
first one with Mathlib's notion.

The remainder of the file is the fpqc application (Stacks 023Q): every fpqc covering of
schemes is a universal effective epimorphic family, which on the Mathlib side is
`AlgebraicGeometry.Scheme.instSubcanonicalFpqcTopology`, the statement that the fpqc
topology is subcanonical.

## Main results

* `StacksEffectiveEpi.IsRepresentableFamily`: all members of the family are representable
  morphisms (Stacks 001X).
* `StacksEffectiveEpi.IsEffectiveEpiFamily`: the Stacks 00WP equalizer condition.
* `StacksEffectiveEpi.IsUniversalEffectiveEpiFamily`: the pullback-stable variant of
  Stacks 00WP.
* `StacksEffectiveEpi.IsRepresentableFamily.isEffectiveEpiFamily_iff`: for a representable
  family the Stacks condition is exactly `CategoryTheory.EffectiveEpiFamily`.
* `isEffectiveEpiFamily_of_isFpqcCovering`: an fpqc covering of schemes is an effective
  epimorphic family in the sense of Stacks 00WP.

Tags covered: 00WP, 023Q.
-/

@[expose] public section

namespace StacksEffectiveEpi

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] {I : Type w} {B : C} (X : I → C) (π : ∀ i, X i ⟶ B)

/-- **Stacks 00WP, representability requirement.** Every morphism of the family
`{X i ⟶ B}` is a *representable* morphism in the sense of Stacks 001X: for every
`Z ⟶ B` the fibre product `Z ×_B X i` exists. -/
def IsRepresentableFamily : Prop := ∀ i, HasPullbacksAlong (π i)

/-- **Stacks 00WP.** A family `{X i ⟶ B}` in a category `C` is an *effective epimorphic
family* if it is representable and if for every object `Y` the diagram
`Mor(B, Y) → ∏ᵢ Mor(X i, Y) ⇉ ∏₍ᵢ,ⱼ₎ Mor(X i ×_B X j, Y)` is an equalizer.

The equalizer condition is spelled out as: a family `g i : X i ⟶ Y` whose two restrictions
to any fibre product `X i ×_B X j` agree extends uniquely to `B`.  Both halves of the
equalizer property are contained in the `∃!`: uniqueness says that
`Mor(B, Y) → ∏ᵢ Mor(X i, Y)` is injective, existence says that its image is the set of
compatible families.  Fibre products are referred to through `IsPullback`, so that the
condition does not depend on a choice of pullbacks; representability guarantees that at
least one such square exists for every pair `(i, j)`. -/
@[stacks 00WP,
  sga "3 IV 1.3" "effective epimorphism",
  sga "3 IV 1.13" "effective epi family",
  sga "4 I 10.3" "effective epi family"]
def IsEffectiveEpiFamily : Prop :=
  IsRepresentableFamily X π ∧
    ∀ (Y : C) (g : ∀ i, X i ⟶ Y),
      (∀ (i j : I) (Z : C) (a : Z ⟶ X i) (b : Z ⟶ X j), IsPullback a b (π i) (π j) →
          a ≫ g i = b ≫ g j) →
        ∃! t : B ⟶ Y, ∀ i, π i ≫ t = g i

/-- **Stacks 00WP.** A family `{X i ⟶ B}` is a *universal effective epimorphic family* if it
is representable and if for every morphism `h : V ⟶ B` the base-changed family
`{X i ×_B V ⟶ V}` is an effective epimorphic family. -/
@[stacks 00WP,
  sga "3 IV 1.3" "universal eff. epi",
  sga "3 IV 1.13" "universal variant",
  sga "4 I 10.3" "univ. eff. epi family",
  sga "4 II 2.5" "univ. effective epi fam",
  sga "3 IV 3.3.3.1" "Singleton case",
  sga "3 IV 3.4.2",
  sga "3 IX 5.4"]
def IsUniversalEffectiveEpiFamily : Prop :=
  IsRepresentableFamily X π ∧
    ∀ ⦃V : C⦄ (h : V ⟶ B) (X' : I → C) (π' : ∀ i, X' i ⟶ V) (p : ∀ i, X' i ⟶ X i),
      (∀ i, IsPullback (π' i) (p i) h (π i)) → IsEffectiveEpiFamily X' π'

/-- Taking the base change along the identity of `B` shows that a universal effective
epimorphic family is in particular an effective epimorphic family. -/
@[sga "3 IV 1.3" "partial", sga "3 IV 3.4.2" "more general", sga "4 I 10.3" "partial"]
theorem IsUniversalEffectiveEpiFamily.isEffectiveEpiFamily
    (h : IsUniversalEffectiveEpiFamily X π) : IsEffectiveEpiFamily X π :=
  h.2 (𝟙 B) X π (fun _ => 𝟙 _) fun _ => IsPullback.of_id_snd

/-- A representable family has all pairwise fibre products, i.e. the presieve it generates
satisfies Mathlib's `Presieve.HasPairwisePullbacks`. -/
theorem IsRepresentableFamily.hasPairwisePullbacks (hrep : IsRepresentableFamily X π) :
    (Presieve.ofArrows X π).HasPairwisePullbacks where
  has_pullbacks := by
    rintro _ _ _ ⟨i⟩ _ ⟨j⟩
    exact hrep j (π i)

/-- For a representable family, agreeing on all fibre products `X i ×_B X j` is the same as
Mathlib's compatibility condition for the representable presheaf `Mor(-, Y)`, which is
phrased over all commutative squares.  This is `Presieve.Arrows.pullbackCompatible_iff`
transported to arbitrary pullback squares. -/
theorem IsRepresentableFamily.compatible_iff (hrep : IsRepresentableFamily X π)
    {Y : C} (g : ∀ i, X i ⟶ Y) :
    (∀ (i j : I) (Z : C) (a : Z ⟶ X i) (b : Z ⟶ X j), IsPullback a b (π i) (π j) →
        a ≫ g i = b ≫ g j) ↔ Presieve.Arrows.Compatible (yoneda.obj Y) π g := by
  have := hrep.hasPairwisePullbacks X π
  rw [Presieve.Arrows.pullbackCompatible_iff]
  exact ⟨fun h i j => h i j _ _ _ (IsPullback.of_hasPullback (π i) (π j)),
    fun h i j Z a b hab =>
      (Presieve.Arrows.pullbackCompatible_iff (yoneda.obj Y) π g).mpr h i j Z a b hab.w⟩

/-- **Stacks 00WP versus Mathlib.** For a representable family the equalizer condition of
Stacks 00WP is exactly `CategoryTheory.EffectiveEpiFamily`.

Indeed `EffectiveEpiFamily` says that the generated sieve is effective epimorphic
(`Sieve.effectiveEpimorphic_family`), which means that every representable presheaf
`Mor(-, Y)` satisfies the sheaf condition for the presieve
(`Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda`); unwinding that sheaf
condition for a family of arrows (`Presieve.isSheafFor_arrows_iff`) gives the `∃!` of
Stacks 00WP. -/
@[sga "4 I 10.3" "special case"]
theorem IsRepresentableFamily.isEffectiveEpiFamily_iff (hrep : IsRepresentableFamily X π) :
    IsEffectiveEpiFamily X π ↔ EffectiveEpiFamily X π := by
  rw [← Sieve.effectiveEpimorphic_family,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  refine ⟨fun h Y => ?_, fun h => ⟨hrep, fun Y g hg => ?_⟩⟩
  · rw [Presieve.isSheafFor_arrows_iff]
    intro x hx
    exact h.2 Y x ((hrep.compatible_iff X π x).mpr hx)
  · exact (Presieve.isSheafFor_arrows_iff ..).mp (h Y) g ((hrep.compatible_iff X π g).mp hg)

end StacksEffectiveEpi

open CategoryTheory Limits AlgebraicGeometry

-- Main Definition(s)

/-- **Definition 3 (fpqc covering, Tag 022B).**
A family `{ f i : T' i ⟶ T }` is an *fpqc covering* if each `f i` is flat, and for every
affine open `U ⊆ T` there is a finite index list `a : Fin n → ι` and affine opens
`V j ⊆ T' (a j)` whose images under `f (a j)` cover `U`. -/
structure IsFpqcCoveringFamily {ι : Type*} {T : Scheme} (T' : ι → Scheme)
    (f : ∀ i, T' i ⟶ T) : Prop where
  /-- Each morphism of the family is flat. -/
  flat : ∀ i, Flat (f i)
  /-- The quasi-compactness/surjectivity condition: every affine open of `T` is covered by
  finitely many images of affine opens of the sources. -/
  covers : ∀ U : T.Opens, IsAffineOpen U →
    ∃ (n : ℕ) (a : Fin n → ι) (V : ∀ j, (T' (a j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
      (⋃ j, (f (a j)).base '' (V j : Set (T' (a j)))) = (U : Set T)

/-- The explicit equalizer / sheaf condition of **Definition 1(2)** for a fixed target
scheme `S`: the representable presheaf `Hom(-, S)` satisfies descent along
`{ f i : T' i ⟶ T }`, namely

* (uniqueness) two morphisms `T ⟶ S` agreeing after precomposition with every `f i`
  coincide; and
* (gluing) any family `φ i : T' i ⟶ S` whose restrictions to the fibre products agree
  glues to a morphism `ψ : T ⟶ S` with `f i ≫ ψ = φ i`.

This is the `Scheme`-valued specialisation of the equalizer condition in
`StacksEffectiveEpi.IsEffectiveEpiFamily`, written with the chosen pullbacks. -/
def IsSheafConditionFor {ι : Type*} {T : Scheme} (T' : ι → Scheme)
    (f : ∀ i, T' i ⟶ T) (S : Scheme) : Prop :=
  (∀ ψ ψ' : T ⟶ S, (∀ i, f i ≫ ψ = f i ≫ ψ') → ψ = ψ') ∧
  (∀ φ : ∀ i, T' i ⟶ S,
    (∀ i j, pullback.fst (f i) (f j) ≫ φ i = pullback.snd (f i) (f j) ≫ φ j) →
    ∃ ψ : T ⟶ S, ∀ i, f i ≫ ψ = φ i)

/-- **Definition 2 (Universal effective epimorphism, Tag 00WP).**
A family `{ f i : T' i ⟶ T }` is a *universal effective epimorphism* if for every base
`{ pr₂ : T' i ×_T V ⟶ V }` satisfies the sheaf condition `IsSheafConditionFor`.

This is the `Scheme`-valued specialisation of
`StacksEffectiveEpi.IsUniversalEffectiveEpiFamily`, written with the chosen base changes. -/
@[sga "3 IV 1.13" "special case",
  sga "3 IV 1.3" "special case",
  sga "3 IX 5.4",
  sga "4 I 10.3" "special case",
  sga "4 II 2.5" "special case"]
def IsUniversalEffectiveEpi {ι : Type*} {T : Scheme} (T' : ι → Scheme)
    (f : ∀ i, T' i ⟶ T) : Prop :=
  ∀ {V : Scheme} (g : V ⟶ T) (S : Scheme),
    IsSheafConditionFor (fun i => pullback (f i) g) (fun i => pullback.snd (f i) g) S

/-- **Bridge (compatibility translation).** The pullback-compatibility condition on
a family `φ i : T' i ⟶ S` implies Mathlib's `Presieve.Arrows.Compatible` for the
representable presheaf `yoneda.obj S`.  Standard: any `(Z, gi, gj)` with
`gi ≫ f i = gj ≫ f j` factors through the pullback `T' i ×_T T' j` via `pullback.lift`,
along which the two restrictions of `φ` agree by hypothesis. -/
theorem isFpqc_arrows_compatible_of_pullback
    {ι : Type*} {T : Scheme} {T' : ι → Scheme} (f : ∀ i, T' i ⟶ T) {S : Scheme}
    (φ : ∀ i, T' i ⟶ S)
    (hφ : ∀ i j, pullback.fst (f i) (f j) ≫ φ i = pullback.snd (f i) (f j) ≫ φ j) :
    Presieve.Arrows.Compatible (yoneda.obj S) f φ := by
  exact (Presieve.Arrows.pullbackCompatible_iff (yoneda.obj S) f φ).mpr hφ

/-- **Bridge (equalizer ⟸ sheaf).** If the representable presheaf `yoneda.obj S` satisfies the
sheaf condition for the presieve `Presieve.ofArrows T' f`, then the explicit equalizer condition
`IsSheafConditionFor T' f S` holds.  This is `Presieve.isSheafFor_arrows_iff` unpacked: uniqueness
is the uniqueness half of the `∃!`, gluing is its existence half, and the pullback-compatibility is
fed in through `isFpqc_arrows_compatible_of_pullback`. -/
theorem isSheafConditionFor_of_isSheafFor_ofArrows
    {ι : Type*} {T : Scheme} (T' : ι → Scheme) (f : ∀ i, T' i ⟶ T) (S : Scheme)
    (h : Presieve.IsSheafFor (yoneda.obj S) (Presieve.ofArrows T' f)) :
    IsSheafConditionFor T' f S := by
  rw [Presieve.isSheafFor_arrows_iff] at h
  refine ⟨fun ψ ψ' hψ => ?_, fun φ hφ => ?_⟩
  · have hcomp : Presieve.Arrows.Compatible (yoneda.obj S) f (fun i => f i ≫ ψ) := by
      intro i j Z gi gj hgij
      simp only [yoneda_obj_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op]
      rw [← Category.assoc, ← Category.assoc, hgij]
    obtain ⟨t, _, huniq⟩ := h _ hcomp
    rw [huniq ψ (fun i => rfl), huniq ψ' (fun i => (hψ i).symm)]
  · exact (h φ (isFpqc_arrows_compatible_of_pullback f φ hφ)).exists

set_option backward.isDefEq.respectTransparency false in
/-- **Bridge (covering membership).** The fpqc-covering data produces a covering sieve of
the fpqc topology: `Sieve.ofArrows T' f ∈ fpqcTopology T`.

Argument: `fpqcTopology = Scheme.propQCTopology @Flat` (`fpqcTopology_eq_propQCTopology`), whose
generating precoverage is `qcPrecoverage ⊓ precoverage @Flat`, and a presieve belonging to a
generating precoverage generates a covering sieve (`Precoverage.generate_mem_toGrothendieck`).  The
quasi-compactness factor holds because the `covers` field of `IsFpqcCoveringFamily` says exactly
that every affine open of `T` is covered by finitely many images of affine — hence quasi-compact —
opens of the sources; the flat factor holds because each `f i` is flat and the family is jointly
surjective, both read off from `hf`.

Passing through the generating precoverage rather than `Scheme.Cover.mem_propQCTopology` is what
keeps the index type `ι` in an arbitrary universe: the latter would require `ι : Type u`. -/
theorem IsFpqcCoveringFamily.ofArrows_mem_fpqcTopology
    {ι : Type*} {T : Scheme} {T' : ι → Scheme} {f : ∀ i, T' i ⟶ T}
    (hf : IsFpqcCoveringFamily T' f) :
    Sieve.ofArrows T' f ∈ AlgebraicGeometry.Scheme.fpqcTopology T := by
  -- `fpqcTopology = propQCTopology @Flat = (propQCPrecoverage @Flat).toGrothendieck`.
  -- A presieve in the generating precoverage generates a covering sieve
  -- (`Precoverage.generate_mem_toGrothendieck`), which avoids any universe descent on `ι`.
  -- `propQCPrecoverage @Flat = qcPrecoverage ⊓ precoverage @Flat`; we verify each factor.
  rw [AlgebraicGeometry.Scheme.fpqcTopology_eq_propQCTopology, Sieve.ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  refine ⟨?_, ?_⟩
  · -- quasi-compact part: the canonical (universe-correct) pre-0-hypercover of the presieve is a
    -- `QuasiCompactCover` because every affine open is covered by finitely many affine images.
    have hqc : QuasiCompactCover (Presieve.ofArrows T' f).preZeroHypercover := by
      refine ⟨?_⟩
      intro U hU
      obtain ⟨n, a, V, hVaff, hcov⟩ := hf.covers U hU
      refine IsCompactOpenCovered.of_iUnion_eq_of_finite (κ := Fin n)
        (fun j => (f (a j)).base '' (V j : Set (T' (a j)))) hcov fun j => ?_
      -- index the canonical hypercover by the arrow `f (a j)`; retype `V j` at its source
      let idx : (Presieve.ofArrows T' f).preZeroHypercover.I₀ :=
        ⟨⟨T' (a j), f (a j)⟩, Presieve.ofArrows.mk (a j)⟩
      let V' : ((Presieve.ofArrows T' f).preZeroHypercover.X idx).Opens := V j
      exact IsCompactOpenCovered.image
        (f := fun x => ⇑((Presieve.ofArrows T' f).preZeroHypercover.f x)) (i := idx) V'
        (hVaff j).isCompact
    have hmem := PreZeroHypercoverFamily.presieve.mk
      (P := AlgebraicGeometry.Scheme.qcCoverFamily) (Presieve.ofArrows T' f).preZeroHypercover hqc
    rwa [Presieve.presieve₀_preZeroHypercover] at hmem
  · -- flatness + joint surjectivity of the family
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ?_, hf.flat⟩
    obtain ⟨W, hWaff, hxW, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    obtain ⟨n, a, V, hVaff, hcov⟩ := hf.covers W hWaff
    have hmem : (x : T) ∈ (⋃ j, (f (a j)).base '' (V j : Set (T' (a j)))) := by rwa [hcov]
    obtain ⟨j, y, -, hy⟩ := Set.mem_iUnion.mp hmem
    exact ⟨a j, y, hy⟩

/-- **Bridge (representable presheaf is fpqc-local).** `yoneda.obj S` is a sheaf for the
presieve `Presieve.ofArrows T' f` of an fpqc covering.  This is the direct payoff of
Mathlib's `instSubcanonicalFpqcTopology`:
`Subcanonical.isSheaf_of_isRepresentable` makes `yoneda.obj S` an fpqc sheaf, and
`Presieve.IsSheaf.isSheafFor` applies it to the covering presieve, whose generated sieve
lies in the topology by `IsFpqcCoveringFamily.ofArrows_mem_fpqcTopology`. -/
@[sga "1 XI 4.8" "partial", sga "3 IV 6.3.1" "(iii)"]
theorem IsFpqcCoveringFamily.isSheafFor_yoneda
    {ι : Type*} {T : Scheme} {T' : ι → Scheme} {f : ∀ i, T' i ⟶ T}
    (hf : IsFpqcCoveringFamily T' f) (S : Scheme) :
    Presieve.IsSheafFor (yoneda.obj S) (Presieve.ofArrows T' f) := by
  have hsheaf : Presieve.IsSheaf AlgebraicGeometry.Scheme.fpqcTopology (yoneda.obj S) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj S)
  -- `Sieve.generate (ofArrows T' f) = Sieve.ofArrows T' f` definitionally.
  exact hsheaf.isSheafFor (Presieve.ofArrows T' f) hf.ofArrows_mem_fpqcTopology

-- Main Statement(s)

/-- **Unpacked form of Tag 023Q.**
For every fpqc covering `{ f i : T' i ⟶ T }` and every target scheme `S`, the representable
functor `Hom(-, S)` satisfies the sheaf condition along the covering itself:

* (uniqueness) `ψ, ψ' : T ⟶ S` with `f i ≫ ψ = f i ≫ ψ'` for all `i` are equal;
* (existence/gluing) a compatible family `φ i : T' i ⟶ S` glues to a morphism `T ⟶ S`. -/
@[sga "1 VIII 5.2" "more general",
  sga "1 XI 4.8" "partial",
  sga "3 IV 6.3.1" "(iii), fpqc case (T1)",
  sga "3 X 4.3" "partial",
  sga "4 VII 4.2" "special case"]
theorem isSheafConditionFor_of_isFpqcCovering
    {ι : Type*} {T : Scheme} (T' : ι → Scheme) (f : ∀ i, T' i ⟶ T)
    (hf : IsFpqcCoveringFamily T' f) (S : Scheme) :
    IsSheafConditionFor T' f S :=
  -- The whole content is the two bridge lemmas: translate Mathlib's `IsSheafFor` of the
  -- covering presieve into the explicit equalizer condition.
  isSheafConditionFor_of_isSheafFor_ofArrows T' f S (hf.isSheafFor_yoneda S)

/-- **Base change of an fpqc covering is an fpqc covering.** Along any `g : V ⟶ T`, the
family `{ pullback.snd (f i) g : T' i ×_T V ⟶ V }` is again an fpqc covering of `V`.

Argument: each `pullback.snd (f i) g` is flat because flatness of morphisms of schemes is
stable under base change (`MorphismProperty.StableUnderBaseChange` for `@Flat`, or the
`Flat` instance for pullback projections of a flat map).  The covering axiom is preserved
because, for an affine open `U ⊆ V`, pulling back the affine cover of `g '' U`-meeting
opens through the pullback squares produces a finite affine cover of `U`; equivalently the
base change of a quasi-compact jointly-surjective flat family is again one (this is exactly
the stability statement underlying `Scheme.propQCPrecoverage` being a coverage / pretopology
closed under pullback). -/
@[sga "3 III 0.13" "special case"]
theorem IsFpqcCoveringFamily.baseChange
    {ι : Type*} {T : Scheme} {T' : ι → Scheme} {f : ∀ i, T' i ⟶ T}
    (hf : IsFpqcCoveringFamily T' f) {V : Scheme} (g : V ⟶ T) :
    IsFpqcCoveringFamily (fun i => pullback (f i) g) (fun i => pullback.snd (f i) g) := by
  -- Flatness: `inferInstance` via `Flat.instSndScheme` (flat stable under base change).
  -- Covering: package the original family as a `PreZeroHypercover` of `T`, show it is a
  -- `QuasiCompactCover` (from `hf.covers`), base change it along `g` (`pullback₂`, which is
  -- again a `QuasiCompactCover` by `instPullback₂Scheme`), and read off the affine cover of
  -- each affine open `U ⊆ V` via `exists_isAffineOpen_of_isCompact`.
  refine ⟨fun i => ?_, ?_⟩
  · have := hf.flat i
    infer_instance
  · let 𝒰 : PreZeroHypercover T := ⟨ι, T', f⟩
    have hqc : QuasiCompactCover 𝒰 := by
      rw [quasiCompactCover_iff]
      intro U hU
      obtain ⟨n, a, W, hWaff, hcov⟩ := hf.covers U hU
      exact IsCompactOpenCovered.of_finite (f := fun i => ⇑(𝒰.f i)) a W
        (fun j => (hWaff j).isCompact) hcov
    exact fun U hU =>
      QuasiCompactCover.exists_isAffineOpen_of_isCompact (𝒰.pullback₂ g) hU.isCompact

/-- **Main statement (Stacks Tag 023Q).**
Every fpqc covering of schemes is a universal effective epimorphism in the category of
schemes. -/
@[stacks 023Q "every fpqc covering family of schemes is a universal effective epimorphism, in \
the unpacked equalizer form of Stacks 00WP: along every base change of the family, a morphism \
to any scheme is determined by, and glues from, a pullback-compatible family on the members",
  sga "1 VIII 5.3" "more general",
  sga "3 IV 3.4" "more general",
  sga "3 IV 6.3.1" "(iii), fpqc case (T1)",
  sga "3 IX 5.4" "more general",
  sga "3 XI 3.9" "partial"]
theorem isUniversalEffectiveEpi_of_isFpqcCovering
    {ι : Type*} {T : Scheme} (T' : ι → Scheme) (f : ∀ i, T' i ⟶ T)
    (hf : IsFpqcCoveringFamily T' f) :
    IsUniversalEffectiveEpi T' f :=
  -- For any base change `g : V ⟶ T`, the base-changed family is again an fpqc covering
  -- (`IsFpqcCoveringFamily.baseChange`), so the unpacked sheaf condition applies to it directly.
  fun g S => isSheafConditionFor_of_isFpqcCovering _ _ (hf.baseChange g) S

/-- **Stacks 00WP for fpqc coverings.** An fpqc covering of schemes is an effective
epimorphic family in the sense of Stacks 00WP, stated for an arbitrary category.

Representability is automatic because the category of schemes has all fibre products, and
the equalizer condition is `isSheafConditionFor_of_isFpqcCovering` read at the chosen
pullbacks. -/
@[sga "1 XI 4.8" "partial", sga "3 X 4.3" "partial", sga "3 XI 3.9" "partial"]
theorem isEffectiveEpiFamily_of_isFpqcCovering {ι : Type*} {T : Scheme} (T' : ι → Scheme)
    (f : ∀ i, T' i ⟶ T) (hf : IsFpqcCoveringFamily T' f) :
    StacksEffectiveEpi.IsEffectiveEpiFamily T' f := by
  have hrep : StacksEffectiveEpi.IsRepresentableFamily T' f := fun _ _ => inferInstance
  refine ⟨hrep, fun S g hg => ?_⟩
  exact (Presieve.isSheafFor_arrows_iff ..).mp (hf.isSheafFor_yoneda S) g
    ((hrep.compatible_iff T' f g).mp hg)
