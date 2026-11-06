module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
## Commutative maximal subalgebras
This file contains basic results about commutative subalgebras, under division algebras these
are just subfields.

# Main results
* `Subalgebra.maximal_comm_iff_self_centralizer` : a commutative subalgebra is maximal
  among commutative subalgebras iff it is self-centralizing.

-/

@[expose] public section

variable {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]

lemma Subalgebra.le_centralizer_iff_isMulCommutative (L : Subalgebra k A) :
    L ≤ Subalgebra.centralizer k (L : Set A) ↔ IsMulCommutative L :=
  ⟨fun h ↦ ⟨⟨fun x y ↦ Subtype.ext <| h y.2 x x.2⟩⟩,
    fun _ x hx y hy ↦ congrArg Subtype.val <| mul_comm' ⟨y, hy⟩ ⟨x, hx⟩⟩

/-- Adjoining an element of the centralizer of a commutative subalgebra `L` to `L` yields a
commutative subalgebra. -/
lemma Subalgebra.isMulCommutative_adjoin_insert_of_mem_centralizer {L : Subalgebra k A} {a : A}
    (ha : a ∈ Subalgebra.centralizer k (L : Set A)) [IsMulCommutative L] :
    IsMulCommutative (Algebra.adjoin k (insert a (L : Set A))) :=
  Algebra.isMulCommutative_adjoin k <| by
    rintro x (rfl | hx) y (rfl | hy) hne
    · exact (hne rfl).elim
    · exact ((Subalgebra.mem_centralizer_iff k).1 ha y hy).symm
    · exact (Subalgebra.mem_centralizer_iff k).1 ha x hx
    · exact congrArg Subtype.val <| mul_comm' (⟨x, hx⟩ : L) ⟨y, hy⟩

/-- A commutative subalgebra containing `L` centralizes `L`. -/
lemma Subalgebra.le_centralizer_of_le {L L' : Subalgebra k A} [IsMulCommutative L']
    (h : L ≤ L') : L' ≤ Subalgebra.centralizer k (L : Set A) :=
  fun x hx ↦ (Subalgebra.mem_centralizer_iff k).2
    fun y hy ↦ congrArg Subtype.val <| mul_comm' (⟨y, h hy⟩ : L') ⟨x, hx⟩

@[stacks 074V "(ii) ↔ (iii)"]
lemma Subalgebra.maximal_comm_iff_self_centralizer (L : Subalgebra k A) :
    Maximal (fun S : Subalgebra k A ↦ IsMulCommutative S) L ↔
      Subalgebra.centralizer k L = L := by
  refine ⟨fun ⟨hL1, hL2⟩ ↦ ?_, fun hL ↦ ?_⟩
  · refine le_antisymm (fun a ha ↦ ?_) ((le_centralizer_iff_isMulCommutative L).2 hL1)
    exact hL2 (isMulCommutative_adjoin_insert_of_mem_centralizer ha)
      (fun x hx ↦ Algebra.subset_adjoin (Set.mem_insert_of_mem a hx))
      (Algebra.subset_adjoin (Set.mem_insert a _))
  · exact ⟨(le_centralizer_iff_isMulCommutative L).1 hL.ge,
      fun L' hL' hLL' ↦ (le_centralizer_of_le hLL').trans hL.le⟩
