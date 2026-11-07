module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueModulesAreAcyclic
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives

/-!
# Pushforwards of injective modules are acyclic for sections

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `I` be an injective `O_X`-module.
Then `f_* I` is right acyclic for sections over every open subset of `Y`, and its
positive-degree Čech cohomology vanishes for every open covering of `Y`.

## Main definitions

No new definitions are introduced.

## Main results

* `pushforward_injective_rightAcyclic` gives right acyclicity for sections over every open
  subset. This is part (2) of the tag and is proved unconditionally.
* `pushforward_injective_cechCohomology_isZero_of_flasqueCechVanishing` gives the
  positive-degree Čech-cohomology vanishing of part (1), conditionally on the Čech
  acyclicity of flasque abelian sheaves.

## Implementation notes

Pushforward is the existing `RingedSpaceModuleAdjunction.modulePushforward`, and sections
over an open are the existing `SheafOfModules.evaluation` functor. The category of sheaves
of modules is Grothendieck abelian, hence has enough injectives, so the right derived
functor exists without any additional hypothesis.

The common engine is `modulePushforward_underlying_isFlasque`: the underlying abelian sheaf
of `f_* I` is flasque, because restriction maps of `I` are surjective by
`injective_restriction_surjective` and pushforward is computed by taking preimages of
opens. Part (2) then follows from `rightAcyclic_evaluation_of_isFlasque`.

Part (1) is stated with the Čech acyclicity of flasque abelian sheaves — Stacks Tag 09SZ —
as an explicit hypothesis `hFlasqueCech`, rather than tagged as a formalization of the
tag. That input is available in this development as
`Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque` (Stacks Tag 09SZ,
`CechAcyclicity/FlasqueCechVanishing.lean`); discharging `hFlasqueCech` with it turns this
result into part (1) verbatim, and that discharge is registered as
`pushforward_injective_cechCohomology_isZero` (`@[stacks 01EX "part (1)"]`) in
`CechAcyclicity/PushforwardOfAnInjectiveCechVanishing.lean`. This file keeps the
conditional form above: the hypothesis it carries is now a derived input, not an
assumption the development still owes.

## References

* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

noncomputable section

namespace Stacks.Cohomology.PushforwardAcyclic

attribute [local instance] HasDerivedCategory.standard

/-- Sheaves of modules on a ringed space form an abelian category. -/
local instance sheafOfModules_abelian (X : RingedSpace.{u, u}) :
    Abelian (SheafOfModules.{u} (structureSheafRing X)) := inferInstance

/-- The underlying abelian sheaf of the pushforward of an injective module is flasque. -/
@[ega "0 12.1.7" "partial", ega "0 12.2.4" "partial"]
theorem modulePushforward_underlying_isFlasque
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I] :
    TopCat.Presheaf.IsFlasque (X := TopCat.of Y.carrier)
      ((SheafOfModules.toSheaf (structureSheafRing Y)).obj
        ((RingedSpaceModuleAdjunction.modulePushforward f).obj I)).obj := by
  refine ⟨fun {U V} i => (AddCommGrpCat.epi_iff_surjective _).2 fun s => ?_⟩
  have hY : V.unop ≤ U.unop := leOfHom i.unop
  have hX : ((RingedSpaceModuleAdjunction.opensMap f).obj V.unop) ≤
      ((RingedSpaceModuleAdjunction.opensMap f).obj U.unop) := fun _ hx => hY hx
  obtain ⟨t, ht⟩ := InjectiveRestriction.injective_restriction_surjective
    (structureSheafRing X) I hX s
  refine ⟨t, ?_⟩
  show (I.val.presheaf.map
    (((RingedSpaceModuleAdjunction.opensMap f).map (homOfLE hY)).op)) t = s
  simpa [RingedSpaceModuleAdjunction.modulePushforward,
    RingedSpaceModuleAdjunction.structureSheafHom] using ht

/-- **Stacks 01EX, part (2).** The pushforward of an injective module is right acyclic for
the sections functor on every open subset. -/
@[stacks 01EX "part (2)"]
public theorem pushforward_injective_rightAcyclic
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I]
    (V : Opens Y.carrier) :
    (SheafOfModules.evaluation (structureSheafRing Y) (op V)).rightAcyclic
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj I) := by
  let R := structureSheafRing Y
  let P := (RingedSpaceModuleAdjunction.modulePushforward f).obj I
  let ev := SheafOfModules.evaluation R (op V)
  let : ev.Additive := Stacks.Cohomology.FlasqueAcyclic.evaluation_additive R (op V)
  let : (ev.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules R)) :=
    Functor.HasRightDerivedFunctor.mk' ev.rightDerivedFunctorPlus ev.rightDerivedFunctorPlusUnit
  exact Stacks.Cohomology.FlasqueAcyclic.rightAcyclic_evaluation_of_isFlasque R P V
    (modulePushforward_underlying_isFlasque f I)

/-- **Stacks 01EX, part (1)**, conditionally on the Čech acyclicity of flasque abelian
sheaves. Given that a flasque abelian sheaf on `Y` has vanishing positive-degree Čech
cohomology — Stacks Tag 09SZ, supplied here as the hypothesis `hFlasqueCech` — the
positive-degree Čech cohomology of the pushforward of an injective module vanishes for
every family of opens, and hence for every open covering. -/
public theorem pushforward_injective_cechCohomology_isZero_of_flasqueCechVanishing
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (hFlasqueCech : ∀ (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Y.carrier)),
      G.IsFlasque → ∀ {K : Type u} (W : K → Opens Y.carrier) (q : ℕ), 0 < q →
        IsZero (((cechComplexFunctor W).obj G.obj).homology q))
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I]
    {J : Type u} (U : J → Opens Y.carrier) (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor U).obj
      ((RingedSpaceModuleAdjunction.modulePushforward f).obj I).val.presheaf).homology p) :=
  hFlasqueCech ((SheafOfModules.toSheaf (structureSheafRing Y)).obj
    ((RingedSpaceModuleAdjunction.modulePushforward f).obj I))
    (modulePushforward_underlying_isFlasque f I) U p hp

end Stacks.Cohomology.PushforwardAcyclic

end

end
