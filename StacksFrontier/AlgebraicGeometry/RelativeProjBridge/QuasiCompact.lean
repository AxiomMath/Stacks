module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.RelativeProjQuasiCompact
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.DegreeZeroConditions

/-!
# Quasi-compactness of the relative homogeneous spectrum of a sheaf of graded algebras

Let `S` be a scheme and `𝒜` a quasi-coherent graded `𝒪_S`-algebra, in the sheaf-level form
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. The structure morphism
`Proj_S(𝒜) ⟶ S` of `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` is quasi-compact as soon
as `𝒜` is of finite type over `𝒜₀`, or generated over `𝒜₀` by a finite type `𝒜₀`-module `𝒜₁`,
or has locally nilpotent positive part modulo a finite type `𝒜₀`-submodule: the three
hypotheses of Stacks 07ZX.

Quasi-compactness is tested on the affine opens `U` of the base; the inverse image of `U` is the
chart `Proj 𝒜(U)` by the cartesian square of Tag 01NQ, and each hypothesis makes that chart
quasi-compact by the criterion of Stacks 01MD.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.IsFinitelyGeneratedInDegreeOne`:
  over every affine open the section ring is generated over its degree-zero part by its
  degree-one part, which is a finitely generated degree-zero module.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.HasNilpotentPositiveQuotient`:
  over every affine open there is a finitely generated degree-zero submodule of the irrelevant
  ideal modulo which the irrelevant ideal is nil.

## Main results

* `AlgebraicGeometry.Proj.compactSpace_of_adjoin_degreeOne`,
  `AlgebraicGeometry.Proj.compactSpace_of_isNil_mod_fg`: the two absolute criteria.
* `RelativeProjBridge.SheafGradedAlgebra.quasiCompact_toBase_of_compactSpace`:
  the structure morphism is quasi-compact when every affine chart is.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.quasiCompact_toBase`: the
  scheme case of Stacks 07ZX on this substrate.

## Implementation notes

The hypothesis (3) is read affine-open by affine-open: a quasi-coherent finite type
`𝒜₀`-submodule `ℱ ⊆ 𝒜₊` of the source gives, over every affine open, a finitely generated
submodule of the sections, and only those are used, so no compatibility between the submodules
over different opens is required.

## References

* [Stacks Project, Tag 07ZX](https://stacks.math.columbia.edu/tag/07ZX)
* [Stacks Project, Tag 01MD](https://stacks.math.columbia.edu/tag/01MD)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Proj

variable {A : Type*} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The projective spectrum of a graded ring generated over its degree-zero part by its
degree-one part, itself spanned by a finite set, is quasi-compact.** -/
theorem compactSpace_of_adjoin_degreeOne
    (hadj : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) (t : Finset A)
    (ht : (t : Set A) ⊆ (𝒜 1 : Set A))
    (hspan : (𝒜 1 : Set A) ⊆ (Submodule.span (𝒜 0) (t : Set A) : Set A)) :
    CompactSpace (Proj 𝒜) := by
  refine Stacks.RelativeProj.Situation.compactSpace_proj_of_finset_generators 𝒜 t
    (fun x hx => ⟨1, Nat.one_pos, ht hx⟩) (top_unique ?_)
  rw [← hadj]
  exact Algebra.adjoin_le_iff.mpr fun x hx => (Submodule.span_le.mpr fun y hy =>
    Algebra.subset_adjoin hy : Submodule.span (𝒜 0) (t : Set A) ≤
      (Algebra.adjoin (𝒜 0) (t : Set A)).toSubmodule) (hspan hx)

/-- The finite set of all homogeneous components of the members of a finite set. -/
private noncomputable def componentFinset (t : Finset A) : Finset A := by
  classical
  exact t.biUnion fun x => (DirectSum.decompose 𝒜 x).support.image
    fun n => GradedRing.proj 𝒜 n x

private theorem span_le_span_componentFinset (t : Finset A) :
    Ideal.span (t : Set A) ≤ Ideal.span (componentFinset 𝒜 t : Set A) := by
  classical
  refine Ideal.span_le.mpr fun x hx => ?_
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine Ideal.sum_mem _ fun n hn => Ideal.subset_span ?_
  rw [← GradedRing.proj_apply]
  exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩

private theorem componentFinset_pos {t : Finset A}
    (ht : ∀ x ∈ t, x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    ∀ x ∈ componentFinset 𝒜 t, ∃ d : ℕ, 0 < d ∧ x ∈ 𝒜 d := by
  classical
  intro x hx
  simp only [componentFinset, Finset.mem_biUnion, Finset.mem_image] at hx
  obtain ⟨y, hyt, n, hn, rfl⟩ := hx
  refine ⟨n, Nat.pos_of_ne_zero fun hn0 => ?_, SetLike.coe_mem _⟩
  subst hn0
  exact (GradedRing.mem_support_iff 𝒜 y 0).mp hn
    ((HomogeneousIdeal.mem_irrelevant_iff 𝒜 y).mp (ht y hyt))

/-- **The projective spectrum of a graded ring whose irrelevant ideal is nil modulo the ideal
generated by a finitely generated degree-zero submodule of it is quasi-compact.** -/
theorem compactSpace_of_isNil_mod_fg (F : Submodule (𝒜 0) A)
    (hFpos : (F : Set A) ⊆ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (hFfg : F.FG)
    (hnil : ∀ x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal,
      ∃ n : ℕ, x ^ n ∈ Ideal.span (F : Set A)) :
    CompactSpace (Proj 𝒜) := by
  obtain ⟨t, htspan⟩ := hFfg
  have htirr : ∀ x ∈ t, x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    fun x hx => hFpos (htspan ▸ Submodule.subset_span hx)
  have hFle : F ≤ (Ideal.span (t : Set A)).restrictScalars (𝒜 0) := by
    rw [← htspan]
    exact Submodule.span_le.mpr fun x hx => Ideal.subset_span hx
  have hspan : Ideal.span (F : Set A) ≤ Ideal.span (componentFinset 𝒜 t : Set A) :=
    (Ideal.span_le.mpr fun x hx => hFle hx).trans (span_le_span_componentFinset 𝒜 t)
  exact (Proj.compactSpace_iff 𝒜).2 ⟨_, componentFinset_pos 𝒜 htirr, fun x hx =>
    Ideal.mem_radical_iff.mpr ((hnil x hx).imp fun _ hn => hspan hn)⟩

end AlgebraicGeometry.Proj

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

open _root_.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **`𝒜` is generated by `𝒜₁` as an `𝒜₀`-algebra and `𝒜₁` is a finite type `𝒜₀`-module**: over
every affine open the graded ring of sections is generated over its degree-zero part by its
degree-one part, which is spanned over the degree-zero part by a finite set. Hypothesis (2) of
Stacks 07ZX. -/
def IsFinitelyGeneratedInDegreeOne : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    Algebra.adjoin (A.grading U 0) (A.grading U 1 : Set (A.sectionRing U)) = ⊤ ∧
    ∃ t : Finset (A.sectionRing U),
      (t : Set (A.sectionRing U)) ⊆ (A.grading U 1 : Set (A.sectionRing U)) ∧
      (A.grading U 1 : Set (A.sectionRing U)) ⊆
        (Submodule.span (A.grading U 0) (t : Set (A.sectionRing U)) : Set (A.sectionRing U))

/-- **`𝒜₊` is locally nilpotent modulo a finite type `𝒜₀`-submodule `ℱ ⊆ 𝒜₊`**: over every
affine open there is a finitely generated degree-zero submodule of the irrelevant ideal of the
graded ring of sections such that every element of the irrelevant ideal has a power in the ideal
it generates. Hypothesis (3) of Stacks 07ZX, read on the sections over the affine opens. -/
def HasNilpotentPositiveQuotient : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ∃ F : Submodule (A.grading U 0) (A.sectionRing U),
      (F : Set (A.sectionRing U)) ⊆ (HomogeneousIdeal.irrelevant (A.grading U)).toIdeal ∧
      F.FG ∧
      ∀ x ∈ (HomogeneousIdeal.irrelevant (A.grading U)).toIdeal,
        ∃ n : ℕ, x ^ n ∈ Ideal.span (F : Set (A.sectionRing U))

/-- **The structure morphism of the relative Proj is quasi-compact when every affine chart is.**
The inverse image of an affine open `U` of the base is the chart `Proj 𝒜(U)`, by the cartesian
square of Tag 01NQ. -/
theorem quasiCompact_toBase_of_compactSpace
    (h : ∀ U : S.Opens, IsAffineOpen U → CompactSpace (Proj (A.grading U))) :
    QuasiCompact (relativeProj A).toBase := by
  refine quasiCompact_iff_forall_isAffineOpen.2 fun U hU => ?_
  have e : Proj (A.grading U) ≅ ((relativeProj A).toBase ⁻¹ᵁ U).toScheme :=
    ((relativeProj A).chart_isPullback U hU).isoPullback.trans
      (isPullback_morphismRestrict (relativeProj A).toBase U).flip.isoPullback.symm
  have := h U hU
  have : CompactSpace (↑((relativeProj A).toBase ⁻¹ᵁ U : Set (relativeProj A).scheme)) :=
    (TopCat.homeoOfIso (asIso e.hom.base)).compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- **Stacks 07ZX on the sheaf-level substrate.** The structure morphism of the relative
homogeneous spectrum of a quasi-coherent graded `𝒪_S`-algebra is quasi-compact as soon as the
algebra is of finite type over its degree-zero part, or generated in degree one by a finite type
degree-zero module, or has locally nilpotent positive part modulo a finite type degree-zero
submodule. -/
theorem quasiCompact_toBase
    (h : A.IsFiniteTypeOverDegreeZero ∨ A.IsFinitelyGeneratedInDegreeOne ∨
      A.HasNilpotentPositiveQuotient) :
    QuasiCompact (relativeProj A).toBase := by
  refine A.quasiCompact_toBase_of_compactSpace fun U hU => ?_
  rcases h with hfin | hdeg | hnil
  · have := hfin U hU
    exact Stacks.RelativeProj.Situation.compactSpace_proj_of_finiteType (A.grading U)
  · obtain ⟨hadj, t, ht, hspan⟩ := hdeg U hU
    exact Proj.compactSpace_of_adjoin_degreeOne (A.grading U) hadj t ht hspan
  · obtain ⟨F, hFpos, hFfg, hF⟩ := hnil U hU
    exact Proj.compactSpace_of_isNil_mod_fg (A.grading U) F hFpos hFfg hF

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

end
