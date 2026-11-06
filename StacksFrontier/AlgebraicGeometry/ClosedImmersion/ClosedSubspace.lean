module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Factorization

/-!
# The closed subspace associated to an ideal sheaf

For a locally ringed space `X` and a monomorphism `j : J ⟶ 𝒪_X` of sheaves of modules
exhibiting `J` as a sheaf of ideals, the associated closed subspace has underlying space the
support of the quotient `𝒪_X / J`. Its inclusion is a closed immersion whose ideal sheaf is
canonically `J`.

## Main definitions

* `quotientSupport X J j` is the support of `𝒪_X / J`, described stalkwise: a point belongs to
  it exactly when no local section of `J` has a unit germ there.
* `ClosedSubspaceData X J j` records the closed subspace, its inclusion, and the canonical
  identifications of the ideal sheaf and of the quotient structure sheaf.

## Main results

* `subsingleton_factorizations_closedSubspace` is the uniqueness half of Tag 01HP: a morphism
  into `X` admits at most one factorization through the associated closed subspace.

## Implementation notes

`ClosedSubspaceData` is data rather than a proposition because its clients use the inclusion
and the specified ideal, and the choice of representative of the associated closed subspace is
immaterial to them. The commuting isomorphisms identify the ideal sheaf and the quotient
structure sheaf canonically, not merely up to an arbitrary isomorphism.

Existence of such data for a locally generated ideal sheaf is Tag 01HN: it is proved in-repo by
`Stacks.ClosedImmersion.exists_closedSubspaceData` and chosen by
`Stacks.ClosedImmersion.closedSubspace`, registered `@[stacks 01HN]` in
`ClosedSubspaceExistence.lean`. Nothing below needs it, since the uniqueness statement takes
the data as a hypothesis.

The uniqueness itself is the general monomorphism statement
`Stacks.ClosedImmersion.subsingleton_factorizations` applied to `D.inclusion`, with
`D.isClosedImmersion` supplying the instance. That general statement is the reusable engine;
this file records the form Tag 01HP states, so that a client holding
`ClosedSubspaceData` can cite it directly.

## References

* [Stacks Project, Tag 01HN](https://stacks.math.columbia.edu/tag/01HN)
* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

variable (X : LocallyRingedSpace.{u})

/-- The support of the quotient of the structure sheaf by an ideal sheaf: the points at which
no local section of the ideal has a unit germ. -/
def quotientSupport (J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)) : Set X :=
  {x | ∀ (U : Opens X) (hx : x ∈ U) (s : J.val.obj (op U)),
    ¬ IsUnit (X.presheaf.germ U x hx (j.val.app (op U) s))}

/-- A point belongs to the support of `𝒪_X / J` precisely when no local section of `J` has a
unit germ at that point. -/
@[simp]
theorem mem_quotientSupport_iff (J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)) (x : X) :
    x ∈ quotientSupport X J j ↔
      ∀ (U : Opens X) (hx : x ∈ U) (s : J.val.obj (op U)),
        ¬ IsUnit (X.presheaf.germ U x hx (j.val.app (op U) s)) :=
  Iff.rfl

/-- Data of the closed subspace associated to an ideal sheaf: the subspace, its inclusion as a
closed immersion with the expected image, and the canonical identifications of the ideal sheaf
and of the quotient structure sheaf, each commuting with the inclusion into the structure
sheaf. -/
structure ClosedSubspaceData (J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)) [Mono j] where
  /-- The closed subspace. -/
  space : LocallyRingedSpace.{u}
  /-- Its inclusion into `X`. -/
  inclusion : space ⟶ X
  /-- The inclusion is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion inclusion.toShHom
  /-- Its image is the support of the quotient. -/
  range_eq_support : Set.range inclusion.toHom.base = quotientSupport X J j
  /-- The ideal sheaf of the inclusion is canonically `J`. -/
  idealIso : J ≅ idealSheaf inclusion.toShHom
  /-- That identification commutes with the inclusions into the structure sheaf. -/
  idealIso_compat : idealIso.hom ≫ kernel.ι _ = j
  /-- The quotient structure sheaf is canonically the cokernel of `j`. -/
  quotientIso : cokernel j ≅
    (SheafOfModules.pushforward (structureSheafHom inclusion.toShHom)).obj
      (SheafOfModules.unit (structureSheafRing space.toRingedSpace))
  /-- That identification commutes with the quotient maps. -/
  quotientIso_compat : cokernel.π j ≫ quotientIso.hom =
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom inclusion.toShHom)

/-- The inclusion of the associated closed subspace is a closed immersion. -/
instance ClosedSubspaceData.instIsClosedImmersion
    {J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    {j : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)} [Mono j]
    (D : ClosedSubspaceData X J j) : IsClosedImmersion D.inclusion.toShHom :=
  D.isClosedImmersion

/-- **Stacks Project, Tag 01HP.** A factorization of a morphism of locally ringed spaces
through the closed subspace associated to an ideal sheaf, when it exists, is unique. -/
@[stacks 01HP "uniqueness"]
theorem subsingleton_factorizations_closedSubspace {X' Y : LocallyRingedSpace.{u}}
    (J : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X'.toRingedSpace)) [Mono j]
    (D : ClosedSubspaceData X' J j) (f : Y ⟶ X') :
    Subsingleton {g : Y ⟶ D.space // g ≫ D.inclusion = f} :=
  subsingleton_factorizations D.inclusion f

end Stacks.ClosedImmersion

end
