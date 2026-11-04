module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.RecoveryCatenary.Local

/-!
# Local criteria for universally catenary schemes

A locally Noetherian scheme is universally catenary exactly when this holds on an open covering.
Equivalently, the ring of sections over every affine open is universally catenary, or it is
enough that this holds over the members of one affine open covering.

## Main results

* `AlgebraicGeometry.Scheme.isUniversallyCatenary_tfae`: the four equivalent local criteria.

## References

* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IrreducibleClosedsCodim

namespace AlgebraicGeometry.Scheme

universe u

/-- A locally Noetherian scheme is universally catenary as soon as it has an open covering by
universally catenary schemes. -/
theorem isUniversallyCatenary_of_openCover (S : Scheme.{u}) [IsLocallyNoetherian S] {ι : Type u}
    (U : ι → S.Opens) (hU : IsOpenCover U) (h : ∀ i, IsUniversallyCatenary (U i).toScheme) :
    IsUniversallyCatenary S := by
  intro X f _
  apply ((isCatenarySpace_tfae X).out 2 1).mp
  exact ⟨ι, fun i => f ⁻¹ᵁ U i, hU.comap f.base.hom,
    fun i => h i _ (f.resLE (U i) (f ⁻¹ᵁ U i) le_rfl)⟩

/-- For a locally Noetherian scheme, universal catenarity is equivalent to holding on an open
covering, to universal catenarity of the ring of sections over every affine open, and to that
ring-theoretic condition holding over the members of one affine open covering. -/
@[stacks 02J9 "local_criteria"]
theorem isUniversallyCatenary_tfae (S : Scheme.{u}) [IsLocallyNoetherian S] :
    List.TFAE [
      IsUniversallyCatenary S,
      ∃ (ι : Type u) (U : ι → S.Opens),
        IsOpenCover U ∧ ∀ i, IsUniversallyCatenary (U i).toScheme,
      ∀ U : S.affineOpens, Ring.IsUniversallyCatenary Γ(S, U),
      ∃ (ι : Type u) (U : ι → S.affineOpens),
        IsOpenCover (fun i ↦ (U i : S.Opens)) ∧
          ∀ i, Ring.IsUniversallyCatenary Γ(S, U i)] := by
  apply List.tfae_of_forall (b := IsUniversallyCatenary S)
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact ⟨fun ⟨_, U, hU, hUC⟩ => isUniversallyCatenary_of_openCover S U hU hUC,
      fun hS => ⟨S.affineOpens, fun U => U.1, IsOpenCover.mk (iSup_affineOpens_eq_top S),
        fun U => isUniversallyCatenary_of_locallyOfFiniteType U.1.ι hS⟩⟩
  · exact (isUniversallyCatenary_iff_forall_affineOpens S).symm
  · exact ⟨fun ⟨_, U, hU, hUC⟩ => isUniversallyCatenary_of_affineOpenCover S U hU hUC,
      fun hS => ⟨S.affineOpens, fun U => U, IsOpenCover.mk (iSup_affineOpens_eq_top S),
        fun U => ringIsUniversallyCatenary_of_isUniversallyCatenary hS U⟩⟩

end AlgebraicGeometry.Scheme
