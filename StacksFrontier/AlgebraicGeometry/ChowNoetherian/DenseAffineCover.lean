module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite affine open cover of a Noetherian scheme whose intersection is dense

A Noetherian scheme has finitely many irreducible components, and in a quasi-separated scheme
any point lies in an affine open containing the generic points of finitely many prescribed
irreducible components (Stacks 01ZX,
`AlgebraicGeometry.exists_affineOpen_mem_of_genericPoints_irreducibleComponents`). Covering a
Noetherian scheme by such affine opens — one for each point, then a finite subcover — gives a
finite affine open cover every member of which contains *every* generic point. The
intersection of the members is therefore an open containing every generic point, hence dense.

This is the opening paragraph of the Stacks proof of Chow's lemma over a Noetherian base
(Stacks 0200): *"Since `X` is quasi-compact, we can find a finite affine open covering
`X = U₁ ∪ … ∪ Uₘ` such that each `Uᵢ` contains `η₁, …, η_r`. In particular we conclude that the
open `U = U₁ ∩ … ∩ Uₘ ⊆ X` is a dense open. This and the fact that the `Uᵢ` are affine opens
covering `X` are all that we will use below."*

## Main results

* `AlgebraicGeometry.exists_affineOpen_mem_and_genericPoints`: every point of a Noetherian
  scheme has an affine open neighbourhood containing the generic point of every irreducible
  component.
* `AlgebraicGeometry.exists_finite_dense_affine_open_cover`: a Noetherian scheme has a finite
  affine open cover with a dense open below every member.

## Implementation notes

`AlgebraicGeometry.exists_affineOpen_mem_of_genericPoints_irreducibleComponents` indexes the
prescribed components by `Fin n` and asks for the indexing to be injective, so the finitely many
components of a Noetherian scheme are transported along `Fintype.equivFin`.

The dense open is `F.inf id`, the infimum of the cover in `X.Opens`, rather than an iterated
binary intersection; density is proved by showing the generic point of every irreducible
component lies in it, which forces its closure to contain every component and hence all of `X`.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01ZX](https://stacks.math.columbia.edu/tag/01ZX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The generic point of an irreducible component of a scheme. -/
noncomputable def genericPointOfComponent {X : Scheme.{u}} (Z : irreducibleComponents X) : X :=
  Z.2.1.genericPoint

/-- `genericPointOfComponent Z` is a generic point of the irreducible component `Z`. -/
theorem genericPointOfComponent_isGeneric {X : Scheme.{u}} (Z : irreducibleComponents X) :
    IsGenericPoint (genericPointOfComponent Z) (Z : Set X) :=
  Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)

/-- **Every point of a Noetherian scheme has an affine open neighbourhood containing the generic
points of all irreducible components.** This is
`AlgebraicGeometry.exists_affineOpen_mem_of_genericPoints_irreducibleComponents` applied to the
finitely many irreducible components of a Noetherian scheme. -/
@[sga "3 VIA 3.2.1" "more general"]
theorem exists_affineOpen_mem_and_genericPoints {X : Scheme.{u}} [IsNoetherian X] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ Z : irreducibleComponents X, genericPointOfComponent Z ∈ U := by
  classical
  let : Finite (irreducibleComponents X) := finite_irreducibleComponents_of_isNoetherian
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let n := Fintype.card (irreducibleComponents X)
  let e : Fin n ≃ irreducibleComponents X := (Fintype.equivFin _).symm
  let Z : Fin n → Set X := fun i => (e i : Set X)
  have hZ (i) : Z i ∈ irreducibleComponents X := (e i).2
  have hinj : Function.Injective Z := fun i j hij => e.injective (Subtype.ext hij)
  let η : Fin n → X := fun i => genericPointOfComponent (e i)
  have hη (i) : IsGenericPoint (η i) (Z i) := genericPointOfComponent_isGeneric (e i)
  obtain ⟨U, hU, hxU, hηU⟩ :=
    exists_affineOpen_mem_of_genericPoints_irreducibleComponents X Z hZ hinj η hη x
  exact ⟨U, hU, hxU, fun W => by simpa [η, e] using hηU (Fintype.equivFin _ W)⟩

/-- Membership in the infimum of a finite set of opens, from membership in each member. -/
private theorem mem_finsetInf_of_mem_each {X : Scheme.{u}} (G : Finset X.Opens) (x : X)
    (hx : ∀ W ∈ G, x ∈ W) : x ∈ G.inf id := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | @insert W G hW ih =>
      rw [Finset.inf_insert]
      exact ⟨hx W (Finset.mem_insert_self _ _),
        ih (fun Z hZ => hx Z (Finset.mem_insert_of_mem hZ))⟩

/-- **A Noetherian scheme has a finite affine open cover with a dense open below every member.**
Each member of the cover contains the generic point of every irreducible component, so their
intersection does too, and an open containing every generic point is dense. -/
@[sga "3 VIA 3.2.1" "more general"]
theorem exists_finite_dense_affine_open_cover {X : Scheme.{u}} [IsNoetherian X] :
    ∃ (F : Finset X.Opens) (U : X.Opens),
      (∀ V ∈ F, IsAffineOpen V) ∧ (∀ x : X, ∃ V ∈ F, x ∈ V) ∧
        (∀ V ∈ F, U ≤ V) ∧ Dense (U : Set X) := by
  classical
  let V : X → X.Opens := fun x => Classical.choose (exists_affineOpen_mem_and_genericPoints x)
  have hV (x : X) : IsAffineOpen (V x) ∧ x ∈ V x ∧
      ∀ Z : irreducibleComponents X, genericPointOfComponent Z ∈ V x :=
    Classical.choose_spec (exists_affineOpen_mem_and_genericPoints x)
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    (fun x => (V x : Set X)) (fun x => (V x).2)
    (fun x _ => Set.mem_iUnion.2 ⟨x, (hV x).2.1⟩)
  refine ⟨t.image V, (t.image V).inf id, ?_, ?_, fun W hW => Finset.inf_le hW, ?_⟩
  · exact Finset.forall_mem_image.2 fun x _ => (hV x).1
  · intro x
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨V y, Finset.mem_image.mpr ⟨y, hyt, rfl⟩, hxy⟩
  · have hgeneric (Z : irreducibleComponents X) :
        genericPointOfComponent Z ∈ (t.image V).inf id :=
      mem_finsetInf_of_mem_each _ _ (Finset.forall_mem_image.2 fun x _ => (hV x).2.2 Z)
    rw [dense_iff_closure_eq]
    refine Set.eq_univ_iff_forall.2 fun x => ?_
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.1
      (by simp [sUnion_irreducibleComponents] : x ∈ ⋃₀ irreducibleComponents X)
    have hsingleton : ({genericPointOfComponent ⟨Z, hZ⟩} : Set X) ⊆
        (((t.image V).inf id : X.Opens) : Set X) :=
      Set.singleton_subset_iff.mpr (hgeneric ⟨Z, hZ⟩)
    have hcl : closure ({genericPointOfComponent ⟨Z, hZ⟩} : Set X) = Z :=
      (genericPointOfComponent_isGeneric ⟨Z, hZ⟩).def
    exact (hcl ▸ closure_mono hsingleton : Z ⊆ closure _) hxZ

end AlgebraicGeometry
