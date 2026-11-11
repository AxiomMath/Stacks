module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.Det
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartModule
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristicAffine

/-!
# Rank zero along affine charts and along all morphisms from affine schemes

Let `X` be a scheme and `K` a perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`. Two
notions of rank zero are in use for `K`:
`AlgebraicGeometry.DeterminantTwoTerm.IsRankZero` asks that the local avatar of `K` along every
morphism `Spec A ⟶ X` has rank zero, and `AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroOn`
asks it only along the charts `Spec Γ(X, V) ⟶ X` of the affine opens `V`. This file shows that
they agree.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.rankAtStalk_sub_eq_chiDerivedFibre`: for a two-term
  presentation `P` of the local avatar of `K` along `u : Spec A ⟶ X` and a prime `𝔭` of `A`,
  `rank_𝔭(P⁰) - rank_𝔭(P⁻¹)` is the derived-fibre Euler characteristic of `K` at `u(𝔭)`.
* `AlgebraicGeometry.DeterminantTwoTerm.isRankZero_iff_isRankZeroOn`: the two notions of rank
  zero agree.

## Implementation notes

The derived-fibre Euler characteristic depends only on `K` and the point of `X`, and is
compatible with derived pullback (Stacks 0BDI); on the sheaf of a bounded complex of finite
projective modules it is the alternating sum of the ranks of the terms. So the difference of the
ranks of the two terms of any presentation of the local avatar along `u` at `𝔭` is read off at
`u(𝔭)`, where an affine chart through `u(𝔭)` shows it vanishes.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TwoTermDeterminant
open AlgebraicGeometry.StandardModel AlgebraicGeometry.DerivedFibreBetti
open Stacks.Cohomology.DerivedPullbackOfATilde (tildeComplex)

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- A perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]` is pseudo-coherent. -/
theorem isPseudoCoherent_obj (K : PerfectTwoTermAmplitude X) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K.obj :=
  (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
    (X := X.toRingedSpace) _).1
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
      (X := X.toRingedSpace) _ K.property.1)

/-- The sheaf of a two-term presentation `P` of the local avatar of `K` along `u` is `Lu^*K`. -/
def tildePresentationIso (K : PerfectTwoTermAmplitude X) {A : CommRingCat.{u}}
    (u : Spec A ⟶ X) (P : TwoTermPresentation (localComplex K u).obj) :
    @Iso (DerivedCategory (Spec A).Modules) _ (DerivedCategory.Q.obj (tildeComplex P.complex))
      ((dpb u).obj K.obj) :=
  ((tilde.functor A).mapDerivedCategoryFactors.app P.complex).symm ≪≫
    (tilde.functor A).mapDerivedCategory.mapIso P.iso.symm ≪≫ localComplexIso K u

/-- **The ranks of a presentation of a local avatar are read off the derived-fibre Euler
characteristic.** For a two-term presentation `P` of the local avatar of `K` along
`u : Spec A ⟶ X` and a prime `𝔭` of `A`, `rank_𝔭(P⁰) - rank_𝔭(P⁻¹)` is the derived-fibre Euler
characteristic of `K` at `u(𝔭)`. -/
theorem rankAtStalk_sub_eq_chiDerivedFibre (K : PerfectTwoTermAmplitude X) {A : CommRingCat.{u}}
    (u : Spec A ⟶ X) (P : TwoTermPresentation (localComplex K u).obj) (p : Spec A) :
    letI := P.finite
    letI := P.projective
    (Module.rankAtStalk (P.complex.X 0) p : ℤ) - Module.rankAtStalk (P.complex.X (-1)) p =
      chiDerivedFibre X K.obj (isPseudoCoherent_obj K) (u.base p) := by
  let := P.finite
  let := P.projective
  have := P.strictlyGE
  have := P.strictlyLE
  have hperf : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
      (DerivedCategory.Q.obj (tildeComplexMod P.complex)) :=
    (isPerfect_tildeComplex_iff P.complex).2 ⟨P.complex, -1, 0, inferInstance, inferInstance,
      fun i => inferInstance, fun i => inferInstance, ⟨Iso.refl _⟩⟩
  have hpcT : RingedSpace.IsPseudoCoherent (X := (Spec A).toRingedSpace)
      (DerivedCategory.Q.obj (tildeComplex P.complex)) :=
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
      (X := (Spec A).toRingedSpace) _).1
      (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
        (X := (Spec A).toRingedSpace) _ hperf)
  have hpcK := isPseudoCoherent_obj K
  have h₁ := chiDerivedFibre_tildeComplex A P.complex (-1) 0 hpcT p
  have h₂ := congrFun (chiDerivedFibre_congr (Spec A) hpcT
    (isPseudoCoherent_derivedPullback u K.obj hpcK) (tildePresentationIso K u P)) p
  have h₃ := congrFun (chiDerivedFibre_derivedPullback u K.obj hpcK) p
  exact (finsum_negOnePow_rankAtStalk_of_twoTerm P.complex P.strictlyGE P.strictlyLE p).symm.trans
    (h₁.symm.trans (h₂.trans h₃))

/-- **Rank zero along every morphism from an affine scheme gives rank zero on the affine
charts.** -/
theorem IsRankZero.isRankZeroOn {K : PerfectTwoTermAmplitude X} (hK : IsRankZero K) :
    IsRankZeroOn K :=
  fun V => hK _ V.2.fromSpec

/-- **Rank zero on the affine charts gives rank zero along every morphism from an affine
scheme.** Both are the vanishing of the derived-fibre Euler characteristic of `K`, read at the
image point. -/
theorem isRankZero_of_isRankZeroOn {K : PerfectTwoTermAmplitude X} (hK : IsRankZeroOn K) :
    IsRankZero K := by
  intro A u
  obtain ⟨P⟩ := nonempty_twoTermPresentation (localComplex K u)
  refine ⟨P, fun p => ?_⟩
  have h₁ := rankAtStalk_sub_eq_chiDerivedFibre K u P p
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show u.base p ∈ (⊤ : X.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  obtain ⟨q, hq⟩ : u.base p ∈ Set.range hV'.fromSpec.base := by
    rwa [hV'.range_fromSpec]
  obtain ⟨Q, hQ⟩ := hK ⟨V, hV⟩
  have h₂ := rankAtStalk_sub_eq_chiDerivedFibre K hV'.fromSpec Q q
  rw [hq] at h₂
  have h₃ := hQ q
  simp only at h₁ h₂ h₃ ⊢
  omega

/-- **The two notions of rank zero agree**: `K` has rank zero along every morphism from an
affine scheme if and only if it has rank zero on every affine chart. -/
theorem isRankZero_iff_isRankZeroOn (K : PerfectTwoTermAmplitude X) :
    IsRankZero K ↔ IsRankZeroOn K :=
  ⟨IsRankZero.isRankZeroOn, isRankZero_of_isRankZeroOn⟩

end AlgebraicGeometry.DeterminantTwoTerm

end
