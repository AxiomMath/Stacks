module

public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.GradedSections.Avoidance
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Finite sets in a common affine open: the `Proj` case

A finite set of points of a scheme immersed in the `Proj` of an `ℕ`-graded ring lies in a single
affine open; this is part (4) of [Stacks, Tag 01ZY].

## Main results

* `Stacks.AmpleCluster.exists_isAffineOpen_basicOpen_of_finite`: a finite set of points of `Proj 𝒮`
  lies in a single affine `D₊(f)`.
* `Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_proj`: a finite set of
  points of a scheme immersed in `Proj 𝒮` lies in an affine open.

## References

* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 00JS](https://stacks.math.columbia.edu/tag/00JS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace Stacks.AmpleCluster

/-- **Finitely many points of `Proj 𝒮` lie in a single affine `D₊(f)`.** For a finite set `T` of
points of `Proj 𝒮` there is `f : S` such that `D₊(f)` is an affine open containing `T`. -/
theorem exists_isAffineOpen_basicOpen_of_finite {S : Type u} {σ : Type v} [CommRing S]
    [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    {T : Set (Proj 𝒮)} (hT : T.Finite) :
    ∃ f : S, IsAffineOpen (Proj.basicOpen 𝒮 f) ∧
      T ⊆ (Proj.basicOpen 𝒮 f : Set (Proj 𝒮)) := by
  classical
  obtain ⟨d, f, hd, hfd, -, hf⟩ :=
    Stacks.GradedAvoidance.exists_homogeneous_pos_forall_notMem 𝒮
      (fun x : Proj 𝒮 => x.asHomogeneousIdeal.toIdeal) hT.toFinset
      (fun x _ => x.asHomogeneousIdeal.isHomogeneous) (fun x _ => x.isPrime)
      (HomogeneousIdeal.irrelevant 𝒮).toIdeal (HomogeneousIdeal.irrelevant 𝒮).isHomogeneous
      le_rfl (fun x _ => x.not_irrelevant_le)
  exact ⟨f, Proj.isAffineOpen_basicOpen 𝒮 f hfd hd,
    fun x hx => (Proj.mem_basicOpen 𝒮 f x).mpr (hf x (hT.mem_toFinset.mpr hx))⟩

/-- A finite set of points of a scheme `X` with an immersion `X ⟶ Proj 𝒮` lies in an affine open of
`X`. -/
@[stacks 01ZY "part (4)"]
theorem exists_affineOpen_containing_finite_of_immersion_proj {X : Scheme.{u}} {S : Type u}
    {σ : Type v} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    (i : X ⟶ Proj 𝒮) [IsImmersion i] {E : Set X} (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) := by
  obtain ⟨f, hW, hTW⟩ := exists_isAffineOpen_basicOpen_of_finite 𝒮 (hE.image i.base)
  have : IsAffine (Proj.basicOpen 𝒮 f).toScheme := hW
  have hEV : ∀ x ∈ E, x ∈ i ⁻¹ᵁ Proj.basicOpen 𝒮 f := fun x hx => hTW ⟨x, hx, rfl⟩
  obtain ⟨U, hU, hEU⟩ := exists_affineOpen_containing_finite_of_immersion_affine
    (i ∣_ Proj.basicOpen 𝒮 f) (E := Subtype.val ⁻¹' E) (hE.preimage Subtype.val_injective.injOn)
  exact ⟨(i ⁻¹ᵁ Proj.basicOpen 𝒮 f).ι ''ᵁ U, hU.image_of_isOpenImmersion _,
    fun x hx => (Scheme.Opens.mem_ι_image_iff _).mpr (hEU (show (⟨x, hEV x hx⟩ : _) ∈ _ from hx))⟩

end Stacks.AmpleCluster

end
