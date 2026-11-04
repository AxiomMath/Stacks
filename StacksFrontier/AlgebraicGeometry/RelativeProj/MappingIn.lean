module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.RingTheory.GradedDivision

/-!
# Mapping into a relative `Proj`: the trivialized case

Let `s` be a relative `Proj` situation, that is, a scheme `S` with a quasi-coherent, commutative,
nonnegatively graded algebra `𝒜` over its structure sheaf (Tag 01NN), and let `U ⊆ S` be an
affine open. The chart of `Proj_S(𝒜)` over `U` is the projective spectrum of the graded ring
`A = ⨁ₙ 𝒜ₙ(U)` of homogeneous sections over `U`, and the part of `Proj_S(𝒜)` lying over `U` is
exactly that chart (`Stacks.RelativeProj.Situation.relativeProjChart_isPullback`).

This file proves the mapping-in half of the universal property of relative `Proj`
(Constructions, Section 01NS) in the case where the invertible module on the test scheme is
trivialized: a morphism `W ⟶ Proj_S(𝒜)` over `U` is produced from a homomorphism of graded
rings `ψ : A ⟶ Γ(W, ⊤)` which restricts in degree zero to the given morphism `W ⟶ U`, and whose
image of the irrelevant ideal is the unit ideal.

## Main results

* `Stacks.RelativeProj.Situation.exists_hom_projInclusionToOpen`: the chart-level statement, a
  morphism into `Proj (⨁ₙ 𝒜ₙ(U))` over `U`.
* `Stacks.RelativeProj.Situation.exists_hom_relativeProjToBase`: the same morphism read into the
  relative `Proj` itself, over `S`.
* `Stacks.RelativeProj.Situation.exists_hom_relativeProjToBase_of_dvd`: the same conclusion from
  a ring map `π : A ⟶ Γ(W, ⊤)` agreeing with the structure morphism in degree zero whose
  degree-`n` part is divisible by `tⁿ` for a nonzerodivisor `t`, and whose degree-one part
  generates `(t)`.

## References

* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.RelativeProj.Situation

/-- **Mapping into the chart of a relative `Proj` over an affine open of the base.** A
homomorphism `ψ` from the graded ring of homogeneous sections over `U` to the global sections of
`W`, which agrees in degree zero with a given morphism `r : W ⟶ U` and whose image of the
irrelevant ideal is the unit ideal, classifies a morphism `W ⟶ Proj (⨁ₙ 𝒜ₙ(U))` over `U`. -/
theorem exists_hom_projInclusionToOpen (s : Situation.{u}) {U : s.base.Opens}
    (hU : IsAffineOpen U) {W : Scheme.{u}} (r : W ⟶ U.toScheme)
    (ψ : s.sectionRing U →+* Γ(W, ⊤))
    (hψ0 : ∀ x : Γ(s.base, U), ψ (s.sectionRingBaseMap U x) = (U.topIso.inv ≫ r.appTop).hom x)
    (hψtop : (HomogeneousIdeal.irrelevant (s.sectionRingGrading U)).toIdeal.map ψ = ⊤) :
    ∃ h : W ⟶ Proj (s.sectionRingGrading U), h ≫ projInclusionToOpen s U hU = r := by
  have hzero : s.sectionRingZeroMap U ≫
      CommRingCat.ofHom
        (ψ.comp (algebraMap (↥(s.sectionRingGrading U 0)) (s.sectionRing U))) =
      U.topIso.inv ≫ r.appTop := by
    ext x
    have hcoe : ((GradedRing.projZeroRingHom' (s.sectionRingGrading U)
        (s.sectionRingBaseMap U x) : ↥(s.sectionRingGrading U 0)) : s.sectionRing U) =
        s.sectionRingBaseMap U x :=
      congrArg Subtype.val (GradedRing.projZeroRingHom'_apply_coe _
        ⟨_, sectionRingBaseMap_mem_zero s U x⟩)
    show ψ ((GradedRing.projZeroRingHom' (s.sectionRingGrading U)
        (s.sectionRingBaseMap U x) : ↥(s.sectionRingGrading U 0)) : s.sectionRing U) = _
    rw [hcoe]
    exact hψ0 x
  refine ⟨Proj.fromOfGlobalSections (s.sectionRingGrading U) ψ hψtop, ?_⟩
  rw [projInclusionToOpen, ← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp_assoc, hzero, Spec.map_comp_assoc, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc]
  have h₂ : (U.toScheme).toSpecΓ ≫ Spec.map U.topIso.inv ≫ hU.isoSpec.inv = 𝟙 _ := by
    rw [← Category.assoc]
    exact hU.toSpecΓ_isoSpec_inv
  rw [h₂, Category.comp_id]

/-- **Mapping into a relative `Proj` over an affine open of the base.** A homomorphism `ψ` from
the graded ring of homogeneous sections over an affine open `U` to the global sections of `W`,
which agrees in degree zero with a given morphism `r : W ⟶ U` and whose image of the irrelevant
ideal is the unit ideal, gives a morphism `W ⟶ Proj_S(𝒜)` whose composite with the structure
morphism is `r` followed by the inclusion of `U`. -/
theorem exists_hom_relativeProjToBase (s : Situation.{u}) (U : s.base.affineOpens)
    {W : Scheme.{u}} (r : W ⟶ (U : s.base.Opens).toScheme)
    (ψ : s.sectionRing U.1 →+* Γ(W, ⊤))
    (hψ0 : ∀ x : Γ(s.base, U.1),
      ψ (s.sectionRingBaseMap U.1 x) = (U.1.topIso.inv ≫ r.appTop).hom x)
    (hψtop : (HomogeneousIdeal.irrelevant (s.sectionRingGrading U.1)).toIdeal.map ψ = ⊤) :
    ∃ g : W ⟶ relativeProj s, g ≫ relativeProjToBase s = r ≫ U.1.ι := by
  obtain ⟨h, hh⟩ := exists_hom_projInclusionToOpen s U.2 r ψ hψ0 hψtop
  refine ⟨h ≫ relativeProjChart s U, ?_⟩
  rw [Category.assoc, (relativeProjChart_isPullback s U).w, ← Category.assoc, hh]

/-- **Mapping into a relative `Proj` from a divisible numerator.** Let `π` be a ring map out of
the graded ring of sections over an affine open `U` into `Γ(W, ⊤)`, and `t ∈ Γ(W, ⊤)` a
nonzerodivisor such that `tⁿ` divides `π` of every homogeneous element of degree `n`. If `π`
agrees in degree zero with a given morphism `r : W ⟶ U` and `t` lies in the ideal generated by
the image of the degree-one part, then there is a morphism `W ⟶ Proj_S(𝒜)` whose composite with
the structure morphism is `r` followed by the inclusion of `U`. -/
theorem exists_hom_relativeProjToBase_of_dvd (s : Situation.{u}) (U : s.base.affineOpens)
    {W : Scheme.{u}} (r : W ⟶ (U : s.base.Opens).toScheme)
    (π : s.sectionRing U.1 →+* Γ(W, ⊤)) (t : Γ(W, ⊤)) (ht : t ∈ nonZeroDivisors Γ(W, ⊤))
    (hdvd : ∀ (n : ℕ) (a : s.sectionPieces U.1 n),
      ∃ c : Γ(W, ⊤), π (DirectSum.of (s.sectionPieces U.1) n a) = t ^ n * c)
    (hπ0 : ∀ x : Γ(s.base, U.1),
      π (s.sectionRingBaseMap U.1 x) = (U.1.topIso.inv ≫ r.appTop).hom x)
    (hgen : t ∈ Ideal.span
      (Set.range fun a : s.sectionPieces U.1 1 =>
        π (DirectSum.of (s.sectionPieces U.1) 1 a))) :
    ∃ g : W ⟶ relativeProj s, g ≫ relativeProjToBase s = r ≫ U.1.ι := by
  obtain ⟨ψ, hψ⟩ := Stacks.GradedDivision.exists_ringHom_pow_mul_eq π t ht hdvd
  set J := (HomogeneousIdeal.irrelevant (s.sectionRingGrading U.1)).toIdeal.map ψ
  have hmemJ (a : s.sectionPieces U.1 1) :
      ψ (DirectSum.of (s.sectionPieces U.1) 1 a) ∈ J :=
    Ideal.mem_map_of_mem _
      (HomogeneousIdeal.mem_irrelevant_of_mem (s.sectionRingGrading U.1) Nat.one_pos ⟨a, rfl⟩)
  have hdeg1 (a : s.sectionPieces U.1 1) :
      π (DirectSum.of (s.sectionPieces U.1) 1 a) ∈ Ideal.span {t} * J := by
    refine Submodule.mem_span_singleton_mul.mpr ⟨_, hmemJ a, ?_⟩
    simpa using hψ 1 a
  have htopJ : J = ⊤ := by
    refine Stacks.GradedDivision.eq_top_of_mem_span_singleton_mul ht ?_
    refine Ideal.span_le.mpr ?_ hgen
    rintro _ ⟨a, rfl⟩
    exact hdeg1 a
  have hψ0 (x : Γ(s.base, U.1)) :
      ψ (s.sectionRingBaseMap U.1 x) = (U.1.topIso.inv ≫ r.appTop).hom x := by
    obtain ⟨a, ha⟩ : ∃ a : s.sectionPieces U.1 0,
        DirectSum.of (s.sectionPieces U.1) 0 a = s.sectionRingBaseMap U.1 x :=
      sectionRingBaseMap_mem_zero s U.1 x
    rw [← ha, ← hπ0 x, ← ha, ← hψ 0 a, pow_zero, one_mul]
  exact exists_hom_relativeProjToBase s U r ψ hψ0 htopJ

end Stacks.RelativeProj.Situation

end
