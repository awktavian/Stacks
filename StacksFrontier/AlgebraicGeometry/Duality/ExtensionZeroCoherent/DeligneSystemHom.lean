module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProCategory
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# Maps out of a Deligne system

Let `j : U ⟶ X` be an open immersion of Noetherian schemes. A *Deligne system* is an inverse
system `(K_n)` in `D^b_{Coh}(𝒪_X)` isomorphic to `(𝓘^n 𝓕^•)` for a bounded complex `𝓕^•` of
coherent `𝒪_X`-modules and a quasi-coherent ideal sheaf `𝓘` with `V(𝓘) = X ∖ U`. Because the
transition maps of `(𝓘^n 𝓕^•)` restrict to isomorphisms on `U`, the restricted system
`(K_n|_U)` is constant; its value `K` is an object of `D^b_{Coh}(𝒪_U)`, and Stacks 0G2H
identifies

`colim_n Hom_X(K_n, L) = Hom_U(K, L|_U)`

for every `L` in `D^b_{Coh}(𝒪_X)`. This file sets up the geometry of that statement: the
category `D^b_{Coh}(𝒪_X)`, the structure of a Deligne system, the pro-object of
`Pro-D^b_{Coh}(𝒪_X)` it determines, and the canonical restriction transformation
`colim_n Mor_X(K_n, -) ⟶ Mor_U(K, (-)|_U)` whose bijectivity is the displayed identification.
It then derives from that identification the pro-category form of Stacks 0G2H and the unique
lifting of morphisms of Stacks 0G4L(1).

## Main definitions

* `AlgebraicGeometry.BoundedCoherentDerived`: the category `D^b_{Coh}(𝒪_X)`.
* `AlgebraicGeometry.restrictBoundedCoherent`: the restriction `j^*` on it.
* `AlgebraicGeometry.DeligneSystem`: a Deligne system, with its ideal-power presentation.
* `AlgebraicGeometry.DeligneSystem.proObject`: the pro-object of `Pro-D^b_{Coh}(𝒪_X)` it
  determines.
* `AlgebraicGeometry.DeligneSystem.restrictionNatTrans`: the canonical restriction
  transformation `colim_n Mor_X(K_n, -) ⟶ Mor_U(K, (-)|_U)`.
* `AlgebraicGeometry.DeligneSystem.Value`: the value on `U` of the restricted system together
  with the identification of Stacks 0G2H for it.

## Main results

* `AlgebraicGeometry.DeligneSystem.restrictionNatTrans_app_ι`: the restriction transformation
  sends the class of `g : K_n ⟶ L` to the restriction of `g` to `U`, read through the
  identification of `K` with `K_n|_U`. This is what pins it down as *the* canonical map of the
  source.
* `AlgebraicGeometry.DeligneSystem.Value.homProEquiv`: **Stacks 0G2H** in the pro-category —
  morphisms of pro-objects from `(K_n)` to the constant pro-object at `L` are the morphisms
  `K ⟶ L|_U`.
* `AlgebraicGeometry.DeligneSystem.Value.proHomEquiv`: **Stacks 0G4L(1)** — every morphism
  `K ⟶ L` on `U` is the restriction of a unique morphism of pro-systems `(K_n) ⟶ (L_n)`.
* `AlgebraicGeometry.DeligneSystem.Value.proHomDiagramIso_inv_app_apply`: at each stage of that
  bijection the morphism produced is the one restricting to the given `α`.
* `CategoryTheory.Pro.natToLiftedIndex_final`: `ℕ` is cofinal in the index category used by
  `CategoryTheory.Pro.coyonedaColim` for an inverse sequence.

## Implementation notes

**What is assumed.** The identification of Stacks 0G2H is carried as the field
`AlgebraicGeometry.DeligneSystem.Value.isIso_restrictionNatTrans` of a structure, that is, it
is *supplied as data*: its proof in the source is a dévissage on `L` followed by an Artin-Rees
induction resting on the first display of [Stacks, Tag 01YB], and is not formalized here. This
is the same device by which `CategoryTheory.DeligneSystemAssignment` carries it for Stacks
0G4N. What the field assumes is the bijectivity of one explicitly constructed, canonically
characterized transformation, so nothing is hidden in its shape; and both results below are
proofs from it, following the argument of the source.

**The index category.** `CategoryTheory.Pro.coyonedaColim` takes the colimit over a copy of
`ℕᵒᵖ` lifted into the morphism universe of the ambient category, so `colim_n Hom_X(K_n, L)` is
literally a colimit over that lifted copy. `CategoryTheory.Pro.natToLiftedIndex` exhibits `ℕ`
as a cofinal subdiagram of it, which is what makes the colimit the one indexed by the natural
numbers.

**Universes.** `AlgebraicGeometry.BoundedCoherentDerived` is the full subcategory of the
derived category of `𝒪_X`-modules taken with `CategoryTheory.HasDerivedCategory.standard`, the
localization in the larger universe; this is the choice under which the derived category of a
scheme is available at all.

## References

* [Stacks Project, Tag 0G2G](https://stacks.math.columbia.edu/tag/0G2G)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] HasDerivedCategory.standard

universe v u

namespace CategoryTheory.Pro

/-- An object of the index category of a lifted inverse sequence, read in `ℕᵒᵖ`. It is spelled
the way `CategoryTheory.Pro.liftedInverseSequence` reduces, so that the term of the latter at
`i` is the term of the inverse sequence at this index. -/
public abbrev liftedIndexValue (i : ULiftHom.{v} (ULift.{v} ℕᵒᵖ)) : ℕᵒᵖ :=
  ULift.downFunctor.obj (ULiftHom.down.obj i)

/-- A morphism of the index category of a lifted inverse sequence, read in `ℕᵒᵖ`. -/
public abbrev liftedIndexValueMap {i i' : ULiftHom.{v} (ULift.{v} ℕᵒᵖ)} (f : i ⟶ i') :
    liftedIndexValue i ⟶ liftedIndexValue i' :=
  ULift.downFunctor.map (ULiftHom.down.map f)

/-- The index of a lifted inverse sequence, read in `ℕᵒᵖ`. -/
public abbrev liftedIndexDown (i : (ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ) : ℕᵒᵖ :=
  liftedIndexValue (unop i)

/-- A transition of the index category of a lifted inverse sequence, read in `ℕᵒᵖ`. -/
public abbrev liftedIndexDownMap {i i' : (ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ} (f : i ⟶ i') :
    liftedIndexDown i' ⟶ liftedIndexDown i :=
  liftedIndexValueMap f.unop

/-- `ℕ`, as a diagram in the opposite of the index category of a lifted inverse sequence. -/
public def natToLiftedIndex : ℕ ⥤ (ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ where
  obj n := op (liftedIndexObj n)
  map f := (liftedIndexHom (leOfHom f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `ℕ` is cofinal in the index category of a lifted inverse sequence: every object of the
latter is the lift of a natural number. -/
public instance natToLiftedIndex_final : (natToLiftedIndex.{v}).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun ⟨⟨⟨n⟩⟩⟩ => ⟨n, ⟨𝟙 _⟩⟩)
    fun s s' => ⟨_, 𝟙 _, by cases s; cases s'; rfl⟩

/-- The index category of a lifted inverse sequence is connected: it is equivalent to the
cofiltered category `ℕᵒᵖ`. -/
public instance isConnected_liftedSequenceIndex :
    IsConnected (ULiftHom.{v} (ULift.{v} ℕᵒᵖ)) :=
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  have : IsConnected (ℕᵒᵖ) := isConnected_op
  isConnected_of_equivalent (ULiftHomULiftCategory.equiv ℕᵒᵖ)

end CategoryTheory.Pro

namespace AlgebraicGeometry

/-- `D^b_{Coh}(𝒪_X)` as a property of objects of `D(𝒪_X)`: cohomologically bounded, with
coherent cohomology sheaves. -/
public abbrev boundedCoherentDerived (X : Scheme.{u}) :=
  DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent)

/-- The bounded derived category `D^b_{Coh}(𝒪_X)` of `𝒪_X`-modules with coherent cohomology. -/
public abbrev BoundedCoherentDerived (X : Scheme.{u}) :=
  (boundedCoherentDerived X).FullSubcategory

variable {U X : Scheme.{u}}

/-- Restriction `j^* : D^b_{Coh}(𝒪_X) ⥤ D(𝒪_U)` along an open immersion `j : U ⟶ X`. -/
public abbrev restrictBoundedCoherent (j : U ⟶ X) [IsOpenImmersion j] :
    BoundedCoherentDerived X ⥤ DerivedCategory U.Modules :=
  (boundedCoherentDerived X).ι ⋙ (Scheme.Modules.restrictFunctor j).mapDerivedCategory

/-- A **Deligne system** along an open immersion `j : U ⟶ X` of Noetherian schemes, after
[Stacks, Section 0G2G]: an inverse system `(K_n)` in `D^b_{Coh}(𝒪_X)` identified with the
system `(𝓘^n 𝓕^•)` of ideal-power subcomplexes of a bounded complex `𝓕^•` of coherent
`𝒪_X`-modules, for a quasi-coherent ideal sheaf `𝓘` cutting out `X ∖ U`. -/
public structure DeligneSystem (j : U ⟶ X) [IsOpenImmersion j] [IsNoetherian X] where
  /-- A quasi-coherent sheaf of ideals on `X`. -/
  idealSheaf : X.IdealSheafData
  /-- Its vanishing locus is the complement of `U`. -/
  support_idealSheaf : (idealSheaf.support : Set X) = (Set.range j.base)ᶜ
  /-- A complex of `𝒪_X`-modules. -/
  complex : CochainComplex X.Modules ℤ
  /-- Its terms are coherent. -/
  isCoherent_complex : ∀ i : ℤ, (complex.X i).IsCoherent
  /-- It vanishes in low degrees. -/
  exists_isStrictlyGE : ∃ a : ℤ, complex.IsStrictlyGE a
  /-- It vanishes in high degrees. -/
  exists_isStrictlyLE : ∃ b : ℤ, complex.IsStrictlyLE b
  /-- The subcomplexes `𝓘^n 𝓕^•`, with their canonical inclusions and transitions. -/
  powers : IdealPowerComplexSystem idealSheaf complex
  /-- The inverse system `(K_n)` in `D^b_{Coh}(𝒪_X)`. -/
  system : ℕᵒᵖ ⥤ BoundedCoherentDerived X
  /-- `(K_n)` is the system of the `𝓘^n 𝓕^•` in the derived category. -/
  representation : system ⋙ (boundedCoherentDerived X).ι ≅
    Functor.ofOpSequence powers.transition ⋙ DerivedCategory.Q

namespace DeligneSystem

variable {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X] (D : DeligneSystem j)

/-- The pro-object of `Pro-D^b_{Coh}(𝒪_X)` determined by a Deligne system. -/
public abbrev proObject : ProSeq (BoundedCoherentDerived X) := ProSeq.of D.system

/-- The functor of points of the pro-object of a Deligne system is
`L ↦ colim_n Hom_X(K_n, L)`. -/
public lemma points_proObject :
    D.proObject.points = Pro.coyonedaColim (Pro.liftedInverseSequence D.system) :=
  rfl

section Restriction

variable (K : BoundedCoherentDerived U)
  (e : D.system ⋙ restrictBoundedCoherent j ≅
    (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K))

/-- The cocone, in the category of functors on `D^b_{Coh}(𝒪_X)`, whose leg at the stage `n`
restricts a morphism `K_n ⟶ L` to `U` and reads its source through the identification `e` of
`K_n|_U` with `K`. -/
public def restrictionLeg (i : (ULiftHom.{u + 1} (ULift.{u + 1} ℕᵒᵖ))ᵒᵖ) :
    coyoneda.obj (op (D.system.obj (Pro.liftedIndexDown i))) ⟶
      restrictBoundedCoherent j ⋙
        coyoneda.obj (op ((boundedCoherentDerived U).ι.obj K)) :=
  coyonedaEquiv.symm (e.inv.app (Pro.liftedIndexDown i))

/-- The leg of the restriction cocone at the stage `n` sends `g : K_n ⟶ L` to the restriction
of `g` to `U`, precomposed with the identification of `K` with `K_n|_U`. -/
public lemma restrictionLeg_app_apply (i : (ULiftHom.{u + 1} (ULift.{u + 1} ℕᵒᵖ))ᵒᵖ)
    (L : BoundedCoherentDerived X)
    (g : D.system.obj (Pro.liftedIndexDown i) ⟶ L) :
    (D.restrictionLeg K e i).app L g =
      e.inv.app (Pro.liftedIndexDown i) ≫ (restrictBoundedCoherent j).map g :=
  rfl

/-- The naturality of `e` makes the restriction maps of
`AlgebraicGeometry.DeligneSystem.restrictionLeg` compatible with the transitions of the
system. -/
public lemma restrictionLeg_naturality
    {i i' : (ULiftHom.{u + 1} (ULift.{u + 1} ℕᵒᵖ))ᵒᵖ} (f : i ⟶ i') :
    coyoneda.map (D.system.map (Pro.liftedIndexDownMap f)).op ≫
        D.restrictionLeg K e i' = D.restrictionLeg K e i := by
  have h : e.inv.app (Pro.liftedIndexDown i) =
      e.inv.app (Pro.liftedIndexDown i') ≫ (restrictBoundedCoherent j).map
        (D.system.map (Pro.liftedIndexDownMap f)) :=
    (Category.id_comp _).symm.trans (e.inv.naturality (Pro.liftedIndexDownMap f))
  ext L g
  change e.inv.app (Pro.liftedIndexDown i') ≫ (restrictBoundedCoherent j).map
      (D.system.map (Pro.liftedIndexDownMap f) ≫ g) =
    e.inv.app (Pro.liftedIndexDown i) ≫ (restrictBoundedCoherent j).map g
  rw [Functor.map_comp, ← Category.assoc, ← h]

public def restrictionCocone :
    Cocone ((Pro.liftedInverseSequence D.system).op ⋙ coyoneda) where
  pt := restrictBoundedCoherent j ⋙ coyoneda.obj (op ((boundedCoherentDerived U).ι.obj K))
  ι :=
    { app := fun i => D.restrictionLeg K e i
      naturality := fun _ _ f =>
        (D.restrictionLeg_naturality K e f).trans (Category.comp_id _).symm }

/-- The canonical restriction transformation
`colim_n Mor_X(K_n, -) ⟶ Mor_U(K, (-)|_U)`: on the class of a morphism `g : K_n ⟶ L` it is the
restriction of `g` to `U`, with its source read through the identification `e` of the restricted
system with the constant system at `K`. Its bijectivity at every `L` is the content of
[Stacks, Tag 0G2H]. -/
public def restrictionNatTrans :
    Pro.coyonedaColim (Pro.liftedInverseSequence D.system) ⟶
      restrictBoundedCoherent j ⋙
        coyoneda.obj (op ((boundedCoherentDerived U).ι.obj K)) :=
  colimit.desc _ (D.restrictionCocone K e)

/-- **The restriction transformation is the restriction map.** On the class of
`g : K_n ⟶ L` in `colim_n Hom_X(K_n, L)` it is `K ≅ K_n|_U ⟶ L|_U`. -/
public lemma restrictionNatTrans_app_ι (i : (ULiftHom.{u + 1} (ULift.{u + 1} ℕᵒᵖ))ᵒᵖ)
    (L : BoundedCoherentDerived X)
    (g : (Pro.liftedInverseSequence D.system).obj (unop i) ⟶ L) :
    (D.restrictionNatTrans K e).app L
        ((colimit.ι ((Pro.liftedInverseSequence D.system).op ⋙ coyoneda) i).app L g) =
      e.inv.app (Pro.liftedIndexDown i) ≫ (restrictBoundedCoherent j).map g := by
  have h : (colimit.ι ((Pro.liftedInverseSequence D.system).op ⋙ coyoneda) i) ≫
      D.restrictionNatTrans K e = D.restrictionLeg K e i :=
    colimit.ι_desc (D.restrictionCocone K e) i
  exact (congrFun (congrArg (fun t => t.app L) h) g).trans
    (D.restrictionLeg_app_apply K e i L g)

end Restriction

/-- The **value on `U`** of a Deligne system `(K_n)` — the value of the constant system
`(K_n|_U)` — together with the identification of [Stacks, Tag 0G2H] for it.

The field `isIso_restrictionNatTrans` *assumes* that identification: it says that the canonical
restriction map `colim_n Hom_X(K_n, L) ⟶ Hom_U(K, L|_U)` of
`AlgebraicGeometry.DeligneSystem.restrictionNatTrans` is bijective for every `L`, which is the
assertion of the tag. The tag is now proved in the repository, as
`AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans` (`@[stacks 0G2H]`,
`ExtensionZeroCoherent/DeligneSystemCoreCoherent.lean`); its conclusion is definitionally this
field's type. The identification is nevertheless still carried as data here, because that
theorem's file lies downstream in the import order, so it cannot be cited at the structure;
values are built downstream, where it can be — `DeligneSystem.valueOfIso` of
`ExtensionZeroCoherent/ExtensionByZeroOpenImmersion.lean` supplies the field with exactly
that theorem. -/
public structure Value where
  /-- The object `K` of `D^b_{Coh}(𝒪_U)`. -/
  obj : BoundedCoherentDerived U
  /-- The restricted system `(K_n|_U)` is the constant system with value `K`. -/
  constIso : D.system ⋙ restrictBoundedCoherent j ≅
    (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj obj)
  /-- **Stacks 0G2H**, as data: `colim_n Hom_X(K_n, L) = Hom_U(K, L|_U)`, the map being the
  restriction map `AlgebraicGeometry.DeligneSystem.restrictionNatTrans`.  The proved theorem
  `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans` (`@[stacks 0G2H]`,
  `DeligneSystemCoreCoherent.lean`) inhabits this type; it lives downstream of this structure
  in the import order, so the field stays data here and the theorem is supplied where values
  are built. -/
  isIso_restrictionNatTrans : IsIso (D.restrictionNatTrans obj constIso)

namespace Value

variable {D} (V : D.Value)

/-- The identification of [Stacks, Tag 0G2H] as an isomorphism of functors:
`colim_n Mor_X(K_n, -) ≅ Mor_U(K, (-)|_U)`. -/
public def homIso :
    Pro.coyonedaColim (Pro.liftedInverseSequence D.system) ≅
      restrictBoundedCoherent j ⋙
        coyoneda.obj (op ((boundedCoherentDerived U).ι.obj V.obj)) :=
  haveI := V.isIso_restrictionNatTrans
  asIso (D.restrictionNatTrans V.obj V.constIso)

/-- **Stacks Project, Tag 0G2H**, in the pro-category. For a Deligne system `(K_n)` along an
open immersion `j : U ⟶ X` of Noetherian schemes, with value `K` on `U`, and for every object
`L` of `D^b_{Coh}(𝒪_X)`, the morphisms of pro-objects from `(K_n)` to the constant pro-object
at `L` are the morphisms `K ⟶ L|_U`:

`colim_n Hom_X(K_n, L) = Hom_U(K, L|_U)`.

The left-hand side is the functor of points of the pro-object `(K_n)` at `L`, which is
`colim_n Hom_X(K_n, L)` by `AlgebraicGeometry.DeligneSystem.points_proObject`, and which is the
set of morphisms of pro-objects into the constant pro-object at `L` by the co-Yoneda lemma,
`CategoryTheory.ProSeq.homConstEquiv`; the identification with the right-hand side is the
restriction map, by `AlgebraicGeometry.DeligneSystem.restrictionNatTrans_app_ι`. -/
-- NO 0G2H attribute: `homProEquiv` is derived from `Value.isIso_restrictionNatTrans`,
-- which is Tag 0G2H's own conclusion carried as data, so tagging this would be circular.
-- Tag 0G2H IS proved in this repository, as
-- `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans` (`@[stacks 0G2H]`,
-- `ExtensionZeroCoherent/DeligneSystemCoreCoherent.lean:124`): from the `i = 0` core
-- `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_bijective`
-- (`@[stacks 01YB "first display"]`, Coherent/HomColimit/FirstDisplaySurjectivity.lean:356)
-- through the truncation case `DeligneSystem.restrictionLifting_truncGELE` and the core
-- principle `DeligneSystem.isIso_restrictionNatTrans_of_core`. The attribute stays with that
-- theorem.
public def homProEquiv (L : BoundedCoherentDerived X) :
    (D.proObject ⟶ ProSeq.const.obj L) ≃
      ((boundedCoherentDerived U).ι.obj V.obj ⟶ (restrictBoundedCoherent j).obj L) :=
  (ProSeq.homConstEquiv D.proObject L).trans (V.homIso.app L).toEquiv

section Lifting

variable {E : DeligneSystem j} (W : E.Value)

/-- The identification of [Stacks, Tag 0G2H] for `(K_n)`, evaluated on the system `(L_m)` of a
second Deligne system: it identifies the diagram `m ↦ colim_n Hom_X(K_n, L_m)` with the constant
diagram at `Hom_U(K, L)`, because `(L_m|_U)` is the constant system at `L`. -/
public def proHomDiagramIso :
    Pro.liftedInverseSequence E.system ⋙
        Pro.coyonedaColim (Pro.liftedInverseSequence D.system) ≅
      (Functor.const (ULiftHom.{u + 1} (ULift.{u + 1} ℕᵒᵖ))).obj
        ((boundedCoherentDerived U).ι.obj V.obj ⟶
          (boundedCoherentDerived U).ι.obj W.obj) :=
  NatIso.ofComponents
    (fun i => V.homIso.app (E.system.obj (Pro.liftedIndexValue i)) ≪≫
      (coyoneda.obj (op ((boundedCoherentDerived U).ι.obj V.obj))).mapIso
        (W.constIso.app (Pro.liftedIndexValue i)))
    (by
      intro i i' f
      have h2 : (restrictBoundedCoherent j).map
            (E.system.map (Pro.liftedIndexValueMap f)) ≫
            W.constIso.hom.app (Pro.liftedIndexValue i') =
          W.constIso.hom.app (Pro.liftedIndexValue i) :=
        (W.constIso.hom.naturality (Pro.liftedIndexValueMap f)).trans (Category.comp_id _)
      have key : (restrictBoundedCoherent j ⋙
            coyoneda.obj (op ((boundedCoherentDerived U).ι.obj V.obj))).map
              (E.system.map (Pro.liftedIndexValueMap f)) ≫
            (coyoneda.obj (op ((boundedCoherentDerived U).ι.obj V.obj))).map
              (W.constIso.hom.app (Pro.liftedIndexValue i')) =
          (coyoneda.obj (op ((boundedCoherentDerived U).ι.obj V.obj))).map
            (W.constIso.hom.app (Pro.liftedIndexValue i)) := by
        rw [Functor.comp_map, ← Functor.map_comp, h2]
      change (Pro.coyonedaColim (Pro.liftedInverseSequence D.system)).map
            (E.system.map (Pro.liftedIndexValueMap f)) ≫
          (V.homIso.hom.app (E.system.obj (Pro.liftedIndexValue i')) ≫
            (coyoneda.obj (op ((boundedCoherentDerived U).ι.obj V.obj))).map
              (W.constIso.hom.app (Pro.liftedIndexValue i'))) =
        V.homIso.hom.app (E.system.obj (Pro.liftedIndexValue i)) ≫
          (coyoneda.obj (op ((boundedCoherentDerived U).ι.obj V.obj))).map
            (W.constIso.hom.app (Pro.liftedIndexValue i))
      rw [← Category.assoc, V.homIso.hom.naturality (E.system.map (Pro.liftedIndexValueMap f)),
        Category.assoc, key])

/-- At the stage `m`, the identification `proHomDiagramIso` carries a morphism `α : K ⟶ L` on
`U` to the class in `colim_n Hom_X(K_n, L_m)` whose restriction to `U` is `α` followed by the
identification `L ≅ L_m|_U`. This is what makes the bijection of
`AlgebraicGeometry.DeligneSystem.Value.proHomEquiv` the restriction map of the tag. -/
public lemma proHomDiagramIso_inv_app_apply (i : ULiftHom.{u + 1} (ULift.{u + 1} ℕᵒᵖ))
    (α : (boundedCoherentDerived U).ι.obj V.obj ⟶
      (boundedCoherentDerived U).ι.obj W.obj) :
    (V.proHomDiagramIso W).inv.app i α =
      V.homIso.inv.app (E.system.obj (Pro.liftedIndexValue i))
        (α ≫ W.constIso.inv.app (Pro.liftedIndexValue i)) :=
  rfl

/-- **Stacks Project, Tag 0G4L(1)**. Let `j : U ⟶ X` be an open immersion of Noetherian
schemes, let `(K_n)` and `(L_m)` be Deligne systems and let `K` and `L` be the values of the
constant systems `(K_n|_U)` and `(L_m|_U)`. Then every morphism `α : K ⟶ L` on `U` is the
restriction of a unique morphism of pro-systems `(K_n) ⟶ (L_m)` in `D^b_{Coh}(𝒪_X)`.

This is the argument of the source: morphisms of pro-systems are the morphisms of the
pro-objects they determine (Stacks 0G2X, which is `CategoryTheory.ProSeq.ofHomEquiv`), that is
`lim_m colim_n Hom_X(K_n, L_m)`; by Stacks 0G2H each term of the limit is `Hom_U(K, L_m|_U)`,
and `(L_m|_U)` is the constant system at `L`, so the limit is over a constant diagram on a
connected index category and equals `Hom_U(K, L)`. -/
@[stacks 0G4L "lift_morphisms; the identification of 0G2H supplied as data"]
public def proHomEquiv :
    (D.proObject ⟶ E.proObject) ≃
      ((boundedCoherentDerived U).ι.obj V.obj ⟶
        (boundedCoherentDerived U).ι.obj W.obj) :=
  (ProSeq.ofHomEquiv D.system E.system).trans
    ((HasLimit.isoOfNatIso (V.proHomDiagramIso W) ≪≫
      (limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone _ _)).toEquiv)

end Lifting

end Value

end DeligneSystem

end AlgebraicGeometry
