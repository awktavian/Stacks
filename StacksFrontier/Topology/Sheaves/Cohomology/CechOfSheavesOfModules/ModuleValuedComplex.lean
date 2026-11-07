module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Flasque
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto

/-!
# The module-valued Čech complex of a sheaf of modules

For a cover of an open `V` of a topological space carrying a sheaf of rings `R`, this file
builds the Čech complex of a sheaf of `R`-modules as a complex of modules over the ring of
sections `R(V)`, functorially in the sheaf of modules, and records that the abelian sheaf
underlying an injective sheaf of modules is flasque.

## Main definitions

* `SectionRing` is the ring of sections of the structure sheaf on an open subset.
* `coverObject` regards a member of a cover of `V` as an object of the slice over `V`.
* `sectionsPresheafFunctor` sends a sheaf of modules to its restriction to opens over `V`,
  regarded as a presheaf of modules over `R(V)`; `sectionsPresheaf` is its object part.
* `cechComplexFunctorOfCover` is the module-valued Čech complex of a cover of `V`, as a
  functor `SheafOfModules R ⥤ CochainComplex (ModuleCat (SectionRing R V)) ℕ`;
  `cechComplex` is its object part.

## Main results

* `underlying_isFlasque`: the abelian sheaf underlying an injective sheaf of modules is
  flasque.
* `cechComplexFunctorOfCover_obj`: the functorial Čech complex has `cechComplex` as its
  object part.

## Implementation notes

The cover is viewed in the slice category over the open it covers. Consequently all terms
of the Čech complex and all its differentials are linear over the ring of sections on that
open. This is the module-valued complex used in the canonical comparison from Čech
cohomology to derived sections. The universes of the space, structure ring, modules, and
cover are separate; the cover universe is small relative to the module universe so that
its products exist.

The Čech complex is built functorially, as the composite of `sectionsPresheafFunctor` with
Mathlib's `cechComplexFunctor`, so that its `map_id` and `map_comp` are those of a functor
composition rather than hand-supplied. `cechComplexFunctorOfCover_obj` identifies its
object part with `cechComplex`. The functorial form is what an effaceability argument for
derived sections consumes: it needs the complex as a functor on sheaves of modules, not
merely objectwise.

Neither half of Stacks Tag 01EP is proved in this file, so no declaration here carries the
tag. The positive-degree vanishing for an injective sheaf of modules reduces to the Čech
acyclicity of flasque abelian sheaves, Stacks Tag 09SZ — now available in this development
as `Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque`
(`CechAcyclicity/FlasqueCechVanishing.lean`); `underlying_isFlasque` supplies the
flasqueness input that reduction needs. Both halves of the tag are registered elsewhere:
the positive-degree half as
`Stacks.Cohomology.CechSheaf.isZero_cechComplex_homology_of_injective`
(`InjectiveVanishing.lean`, `@[stacks 01EP "positive degrees"]`), and the degree-zero
identification of Čech cohomology with sections as
`Stacks.Cohomology.CechSheaf.existsUnique_cechRestrictionHomologyMap`
(`DegreeZeroUniqueIsomorphism.lean`, `@[stacks 01EP "degree zero"]`).

### Degree zero

The degree-zero statement is that restriction to the cover induces a unique isomorphism
from sections on `V` to `(cechComplex V U hU I).homology 0` compatible with the inclusion
into opcycles. Its proof exhibits the restriction map as a kernel of the first Čech
differential, and *that mathematics is now proved*, in
`StacksDraft.Ch20.Sec17.Tag01EPZero`: `CechSheaf.isIso_kernelLift_cechAugmentation` is the
kernel statement, `isLimit_augmentedKernelFork` its `IsLimit (KernelFork …)` form, and
`CechSheaf.homologyZeroIso` the resulting isomorphism.

The obstruction this paragraph used to describe — that the proof manipulates `X 0` and
`X 1` against the cosimplicial power objects `_ ^⦋0⦌` and `_ ^⦋1⦌`, which are definitionally
but not syntactically equal, so that nothing matches without
`backward.isDefEq.respectTransparency` — was real, and the way out was the reformulation it
anticipated rather than the option. The augmentation is stated on the side the complex is
*built* on, where it is literally the Čech `lift` of the restriction maps; the whole argument
is then elementwise through the `mcomp`/`mmk`/`md` layer, so `X n` is never matched against
`_ ^⦋n⦌` at all.

What this paragraph describes is not the kernel argument but a change of scalars. The tag's
degree-zero clause is stated about `SheafOfModules.evaluation R (op V)`, whereas the
augmentation above lives on `sectionsPresheaf V I` at the terminal object of the slice.
Those carry the same underlying group, with `R(V)`-actions differing by restriction of
scalars along a map that is provably but not syntactically the identity;
`ModuleCat.restrictScalarsId'App` is the intended comparison. That comparison is carried
out in `DegreeZeroUniqueIsomorphism.lean`, which composes `CechSheaf.homologyZeroIso` with
`CechSheaf.sectionsTerminalFunctorIso` and registers the degree-zero clause of the tag.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

universe uX uR uM uI

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

namespace Stacks.Cohomology.CechSheaf

/-- The abelian sheaf underlying an injective sheaf of modules is flasque. -/
@[sga "4 V 4.6" "special case"]
public theorem underlying_isFlasque
    {X : Type uX} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
    (I : SheafOfModules.{uM} R) [Injective I] :
    TopCat.Sheaf.IsFlasque (X := TopCat.of X)
      (F := ⟨((SheafOfModules.toSheaf R).obj I).obj,
        ((SheafOfModules.toSheaf R).obj I).property⟩) := by
  refine ⟨fun {U V} i ↦ (AddCommGrpCat.epi_iff_surjective _).2 ?_⟩
  show Function.Surjective (I.val.presheaf.map i)
  have h : unop V ≤ unop U := leOfHom i.unop
  rw [Subsingleton.elim i (homOfLE h).op]
  exact Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective R I h

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uI} [UnivLE.{uI, uM}]

/-- The ring of sections of the structure sheaf on an open subset. -/
public abbrev SectionRing (R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR})
    (V : Opens X) := R.obj.obj (op V)

/-- A member of a cover of `V`, regarded as an object of the slice category over `V`. -/
public def coverObject {V : Opens X} (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (i : ι) : Over V :=
  Over.mk (homOfLE (show U i ≤ V from hU ▸ le_iSup U i))

/-- Restriction to opens over `V`, regarded as a presheaf of modules over `R(V)`, as a
functor in the sheaf of modules. -/
public noncomputable def sectionsPresheafFunctor (V : Opens X) :
    SheafOfModules.{uM} R ⥤ ((Over V)ᵒᵖ ⥤ ModuleCat.{uM} (SectionRing R V)) :=
  SheafOfModules.overFunctor R V ⋙
    SheafOfModules.forget (R.over V) ⋙
      PresheafOfModules.forgetToPresheafModuleCat
        (op (Over.mk (𝟙 V))) (Over.mkIdTerminal.op)

/-- A sheaf of `R`-modules, restricted to opens over `V` and regarded as a presheaf
of modules over `R(V)`. -/
public noncomputable def sectionsPresheaf (V : Opens X) (I : SheafOfModules.{uM} R) :
    (Over V)ᵒᵖ ⥤ ModuleCat.{uM} (SectionRing R V) :=
  (sectionsPresheafFunctor V).obj I

/-- The module-valued Čech complex of the cover `U` of `V`, as a functor in the sheaf of
modules. Its `map_id` and `map_comp` are those of a composite of functors. -/
public noncomputable def cechComplexFunctorOfCover
    (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) :
    SheafOfModules.{uM} R ⥤ CochainComplex (ModuleCat.{uM} (SectionRing R V)) ℕ :=
  sectionsPresheafFunctor V ⋙
    CategoryTheory.cechComplexFunctor (fun i ↦ coverObject U hU i)

/-- The module-valued Čech complex of `I` for the cover `U` of `V`. -/
public noncomputable def cechComplex
    (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (I : SheafOfModules.{uM} R) :
    CochainComplex (ModuleCat.{uM} (SectionRing R V)) ℕ :=
  (CategoryTheory.cechComplexFunctor (fun i ↦ coverObject U hU i)).obj
    (sectionsPresheaf V I)

/-- The functorial Čech complex has `cechComplex` as its object part. -/
@[simp]
public theorem cechComplexFunctorOfCover_obj
    (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (I : SheafOfModules.{uM} R) :
    (cechComplexFunctorOfCover V U hU).obj I = cechComplex V U hU I :=
  rfl

end Stacks.Cohomology.CechSheaf

end
