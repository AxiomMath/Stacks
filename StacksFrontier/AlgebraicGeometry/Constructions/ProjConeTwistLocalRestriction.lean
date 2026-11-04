module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistLocalMap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureRestriction

/-!
# Restriction between standard opens, for the cone over a homogeneous spectrum

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `f`, `g` be homogeneous of
positive degree with `D₊(g) ⊆ D₊(f)`. This file proves two compatibilities with restriction
along `D₊(g) ⊆ D₊(f)`.

The first is for the sheaf `M̃` associated to a graded module: the standard-open identification
`Γ(D₊(f), M̃) = M₍f₎` carries the restriction map of `M̃` to the canonical degree-zero map
`M₍f₎ → M₍g₎`.

The second is for the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`: the comparison maps
`(B[1/ψ f])₀ → A[1/f]` and `(B[1/ψ g])₀ → A[1/g]` of `Stacks.Truncation.awayToLocalization`
intertwine the degree-zero restriction map of `B` attached to `D₊(ψ g) ⊆ D₊(ψ f)` with the
restriction map of `A` attached to `D₊(g) ⊆ D₊(f)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv_restrict`:
  the standard-open identification intertwines the restriction map of `M̃` with the degree-zero
  restriction map `M₍f₎ → M₍g₎`, for any two positive-degree homogeneous elements with
  `D₊(g) ⊆ D₊(f)`.
* `Stacks.Truncation.awayToLocalization_degreeZeroRingMap`: the comparison maps
  `(B[1/ψ f])₀ → A[1/f]` commute with the restriction maps of degree-zero localizations, those
  of `B` on the left and those of `A` on the right.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The grading action used for a naturally graded ring acting on an integer-graded module. -/
local instance : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- The standard-open identification `Γ(D₊(f), M̃) = M₍f₎` intertwines the restriction map of
`M̃` with the canonical degree-zero restriction map `M₍f₎ → M₍g₎`, for any two positive-degree
homogeneous elements with `D₊(g) ⊆ D₊(f)`. -/
@[stacks 01M6 "part (3), the standard-open identification intertwines the restriction map of \
the associated sheaf with the degree-zero restriction map of Tag 01M4"]
theorem associatedModuleSheafStandardOpenEquiv_restrict (f g : S) {d e : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedModuleSheaf 𝒜 𝒨).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hg he
        ((associatedModuleSheaf 𝒜 𝒨).val.map (homOfLE hfg).op s) =
      (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
          ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).degreeZeroMap
        (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd s) := by
  refine degreeZeroToSection_injective 𝒜 𝒨 hg he ?_
  refine (degreeZeroToSection_associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hg he _).trans ?_
  refine Eq.trans ?_ (degreeZeroToSection_restriction 𝒜 𝒨 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
    (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd s))
  exact congrArg (fun z => (associatedModuleSheaf 𝒜 𝒨).val.map (homOfLE hfg).op z)
    (degreeZeroToSection_associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd s).symm

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.Truncation

open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A}

/-- The comparison maps `(B[1/ψ f])₀ → A[1/f]` commute with the restriction maps of
degree-zero localizations: the one of `B` attached to `D₊(ψ g) ⊆ D₊(ψ f)` on the source, the
one of `A` attached to `D₊(g) ⊆ D₊(f)` on the target. -/
@[stacks 0EKG "the comparison maps (B[1/psi f])_0 to A[1/f] commute with the restriction maps \
of degree-zero localizations, for a general inclusion D+(g) <= D+(f) of standard opens"]
theorem awayToLocalization_degreeZeroRingMap
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ e : ℕ, 0 < e ∧ g ∈ 𝒜 e)
    (hψf : ∃ d : ℕ, 0 < d ∧ psi 𝒜 f ∈ grading 𝒜 d)
    (hψg : ∃ e : ℕ, 0 < e ∧ psi 𝒜 g ∈ grading 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (hψfg : ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 g) ≤
      ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f))
    (z : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :
    awayToLocalization 𝒜
        (ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (psi 𝒜 g)
          hψf hψg hψfg z) =
      ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg (awayToLocalization 𝒜 z) := by
  set L : (x : A) → Localization.Away (psi 𝒜 x) →+* Localization.Away x := fun x =>
    Localization.awayLift ((algebraMap A (Localization.Away x)).comp (forgetDegree 𝒜))
      (psi 𝒜 x) (isUnit_iff_exists_inv.mpr ⟨awayFrac x 1 1, comp_psi_mul_awayFrac 𝒜⟩) with hL
  have hkey : (L g).comp
        (ProjectiveSpectrum.localizedRingMap (grading 𝒜) (psi 𝒜 f) (psi 𝒜 g)
          hψf hψg hψfg).toRingHom =
      (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg).toRingHom.comp (L f) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (psi 𝒜 f)) ?_
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [AlgHom.commutes, hL, IsLocalization.Away.lift_eq,
      IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.comp_apply, AlgHom.commutes]
  simpa only [awayToLocalization, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ProjectiveSpectrum.val_degreeZeroRingMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
    congrArg (fun φ : Localization.Away (psi 𝒜 f) →+* Localization.Away g => φ z.val) hkey

end Stacks.Truncation

end
