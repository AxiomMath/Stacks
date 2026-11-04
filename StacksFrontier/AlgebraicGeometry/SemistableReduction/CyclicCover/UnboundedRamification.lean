module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Cohomology
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.BaseChange
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Regular
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.SpecialFibre
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Ramification
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.WeierstrassCurveExists
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAffineLine
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Unconditional
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksCore.Tactic.StacksAttribute

/-!
# A model whose generic fibre needs arbitrarily ramified extensions for semistable reduction

This file states the claims of [Stacks, Tag 0CEH]. Let `k` be algebraically closed, `Z` a smooth
projective curve over `k` of genus `g`, `n ≥ 1` invertible in `k`, `L` an invertible `𝒪_Z`-module
of order `n` in `Pic(Z)` and `φ : L^{⊗ n} ≅ 𝒪_Z`. Put `R = k[[π]]`, `K = k((π))`. The cyclic cover
`p : X ⟶ Z_R` is `Spec_{Z_R}(Sym(L_R)/(φ - π))`, built in
`StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Construction` from the
trivialization `Symⁿ L ≅ L^{⊗ n} ≅ 𝒪_Z` (`Stacks.CyclicCover.symPowTrivialization`).

Each theorem below states one claim of the example, with `φ : L^{⊗ n} ≅ 𝒪_Z` as in the source.

## Main results

* `Stacks.CyclicCover.finite_flat_pushforward_coverMap`: `p` is finite flat with
  `p_* 𝒪_X = 𝒪 ⊕ L_R ⊕ … ⊕ L_R^{⊗ n-1}`.
* `Stacks.CyclicCover.nonempty_coverMapArrowIso`: `p⁻¹(U_R) = Spec (A ⊗_k R)[x]/(xⁿ - π f)`.
* `Stacks.CyclicCover.finite_etale_genericFibre`: `X_K ⟶ Z_K` is finite étale.
* `Stacks.CyclicCover.globalSections_cover`: `H⁰(X, 𝒪_X) = R` and `H⁰(X_K, 𝒪_{X_K}) = K`.
* `Stacks.CyclicCover.genus_genericFibre`: the genus of `X_K` is `n(g - 1) + 1`.
* `Stacks.CyclicCover.isRegular_model`: `X` is regular.
* `Stacks.CyclicCover.specialFibre_eq_pow`: `X_k = n (X_k)_{red}` as effective Cartier divisors.
* `Stacks.CyclicCover.ramification_of_semistable`: an extension over which `X_K` attains
  semistable reduction has ramification index a positive multiple of `n`.
* `Stacks.CyclicCover.no_universal_bound`: there is no universal bound on the degree of an
  extension over which a genus one curve attains semistable reduction.

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RingedSpace (structureIsSheaf)
open scoped TensorProduct

universe u

namespace Stacks.CyclicCover

attribute [local instance] Abelian.hasFiniteBiproducts

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : tensorPow L n ≅ SheafOfModules.unit Z.ringCatSheaf)

/-- The trivialization `Symⁿ L ≅ L^{⊗ n} ≅ 𝒪_Z` given by `φ : L^{⊗ n} ≅ 𝒪_Z`. -/
def symPowTrivialization :
    (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf :=
  symPowIsoTensorPower f L n ≪≫ φ

/-- The base change `X ×_{Spec S} Spec S' ≅ X_{S'}` lies over `Spec S'`. -/
@[reassoc (attr := simp)]
theorem coverBaseChangeIso_hom_coverSnd {S S' : Type u} [CommRing S] [Algebra k S] [CommRing S']
    [Algebra k S'] (ψ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅
      SheafOfModules.unit Z.ringCatSheaf) (c : S) (σ : S →ₐ[k] S') :
    (coverBaseChangeIso f ψ c σ).hom ≫ coverSnd f ψ S' (σ c) = pullback.snd _ _ := by
  simp only [coverBaseChangeIso, Iso.trans_hom, pullback.congrHom_hom, Category.assoc,
    pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- **`p : X ⟶ Z_R` is finite flat, with `p_* 𝒪_X = ⨁_{i < n} L_R^{⊗ i}`**, the direct sum of
the pullbacks to `Z_R` of the tensor powers of `L`. -/
@[stacks 0CEH "p : X → Z_R is finite and flat, and p_*O_X = Sym*(L_R)/(φ - π) = O ⊕ L_R ⊕ … ⊕ \
L_R^{⊗ n-1}; X is built from φ : L^{⊗ n} ≅ O_Z through Symⁿ L ≅ L^{⊗ n}"]
theorem finite_flat_pushforward_coverMap (hn : 1 ≤ n) :
    IsFinite (coverMap f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X) ∧
      Flat (coverMap f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X) ∧
      Nonempty ((⨁ fun i : Fin n => (Scheme.Modules.pullback (baseChangeFst f (PowerSeries k))).obj
          (tensorPow L i)) ≅
        (Scheme.Modules.pushforward
          (coverMap f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)).obj
          (SheafOfModules.unit _)) := by
  have hn0 : n ≠ 0 := by omega
  have := isIso_pushforwardDecomposition f n (symPowTrivialization f φ) (PowerSeries k)
    PowerSeries.X hn0
  exact ⟨isFinite_coverMap f _ _ _ hn0, flat_coverMap f _ _ _ hn0,
    ⟨biproduct.mapIso (fun i : Fin n => (Scheme.Modules.pullback (baseChangeFst f
        (PowerSeries k))).mapIso (symPowIsoTensorPower f L i).symm) ≪≫
      asIso (pushforwardDecomposition f n (symPowTrivialization f φ) (PowerSeries k)
        PowerSeries.X)⟩⟩

/-- **The local description of `p`**: over an affine open `U = Spec A` of `Z` on which `L` is
trivialized by `s`, with `f = φ(s^{⊗ n})` a unit of `A`,
`p⁻¹(U_R) = Spec (A ⊗_k R)[x]/(xⁿ - π f)` over `U_R = Spec (A ⊗_k R)`. -/
@[stacks 0CEH "p⁻¹(U_R) = Spec((A ⊗_k R)[x]/(xⁿ - π f)) for U = Spec A trivializing L by s, \
with f = φ(s^{⊗ n}) a unit"]
theorem nonempty_coverMapArrowIso (U : Z.affineOpens)
    (b : Module.Basis PUnit.{u + 1} Γ(Z, U.1) Γ(L, U.1)) :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    let fU : Γ(Z, U.1) := φ.hom.app U.1 ((symPowIsoTensorPower f L n).hom.app U.1 (basisPow f U b))
    IsUnit fU ∧
      Nonempty (Arrow.mk (coverMap f (symPowTrivialization f φ) (PowerSeries k)
          PowerSeries.X ∣_ baseChangeOpen f (PowerSeries k) U.1) ≅
        Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap (Γ(Z, U.1) ⊗[k] PowerSeries k)
          (chartRing k n fU (PowerSeries.X : PowerSeries k)))))) := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  refine ⟨?_, ⟨coverMapArrowIso f (symPowTrivialization f φ) U b (PowerSeries k) PowerSeries.X⟩⟩
  change IsUnit (chartCoeff f (symPowTrivialization f φ) U b)
  exact isUnit_iff_exists_inv.mpr ⟨rootCoeff f (symPowTrivialization f φ) U b,
    (mul_comm _ _).trans (rootCoeff_mul_chartCoeff f (symPowTrivialization f φ) U b)⟩

/-- **The morphism of generic fibres `X_K ⟶ Z_K` is finite étale.** -/
@[stacks 0CEH "the morphism X_K → Z_K of generic fibres is finite étale"]
theorem finite_etale_genericFibre (hnk : IsUnit (n : k)) :
    IsFinite (coverMapBaseChange f (symPowTrivialization f φ) (PowerSeries.X : PowerSeries k)
        (powerSeriesToLaurent k)) ∧
      Etale (coverMapBaseChange f (symPowTrivialization f φ) (PowerSeries.X : PowerSeries k)
        (powerSeriesToLaurent k)) :=
  isFinite_etale_genericFibre f _ hnk.ne_zero

section Curve

variable [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f]

/-- The special case of the cyclic cover of a curve: `H⁰(X, 𝒪_X) = R` and `H⁰(X_K, 𝒪_{X_K}) = K`,
and the genus of `X_K` is `n(g - 1) + 1`. -/
private theorem bijective_appTop_and_genus_genericFibre (hn : 1 ≤ n)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n) :
    Function.Bijective
        (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X).appTop ∧
      Function.Bijective (pullback.snd
        (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
        (Spec.map (CommRingCat.ofHom (powerSeriesToLaurent k).toRingHom))).appTop ∧
      (genus (pullback.snd
        (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
        (Spec.map (CommRingCat.ofHom (powerSeriesToLaurent k).toRingHom))) : ℤ) =
        n * (genus f - 1) + 1 := by
  have := AlgebraicGeometry.isIso_globalSections_of_isAlgClosed k f
  have hdim : topologicalKrullDim Z ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hn0 : n ≠ 0 := by omega
  let ψ := symPowTrivialization f φ
  let c' := powerSeriesToLaurent k PowerSeries.X
  have := isFinite_coverMap f ψ (LaurentSeries k) c' hn0
  have : IsProper (coverSnd f ψ (LaurentSeries k) c') := by
    have h : coverSnd f ψ (LaurentSeries k) c' =
        coverMap f ψ (LaurentSeries k) c' ≫ baseChangeSnd f (LaurentSeries k) :=
      (coverMap_snd f ψ (LaurentSeries k) c').symm
    rw [h]
    infer_instance
  refine ⟨bijective_coverSnd_appTop f n ψ (PowerSeries k) PowerSeries.X hdim hn0 hord, ?_, ?_⟩
  · have h := (Stacks.Hilbert.AffineLine.bijective_appTop_of_isIso (coverBaseChangeIso f ψ
      PowerSeries.X (powerSeriesToLaurent k)).hom).comp
      (bijective_coverSnd_appTop f n ψ (LaurentSeries k) c' hdim hn0 hord)
    rw [← coverBaseChangeIso_hom_coverSnd f ψ PowerSeries.X (powerSeriesToLaurent k)]
    exact h
  · rw [← coverBaseChangeIso_hom_coverSnd f ψ PowerSeries.X (powerSeriesToLaurent k),
      genus_comp_iso_eq (LaurentSeries k)]
    exact genus_cover f n ψ hdim hn0 hord (LaurentSeries k) c'

/-- **`H⁰(X, 𝒪_X) = R` and `H⁰(X_K, 𝒪_{X_K}) = K`.** -/
@[stacks 0CEH "H^0(X, O_X) = R and H^0(X_K, O_{X_K}) = K"]
theorem globalSections_cover (hn : 1 ≤ n)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n) :
    Function.Bijective
        (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X).appTop ∧
      Function.Bijective (pullback.snd
        (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
        (Spec.map (CommRingCat.ofHom (powerSeriesToLaurent k).toRingHom))).appTop :=
  have h := bijective_appTop_and_genus_genericFibre f φ hn hord
  ⟨h.1, h.2.1⟩

/-- **The genus of `X_K` is `n(g - 1) + 1`**; in particular it is `1` when `Z` has genus `1`. -/
@[stacks 0CEH "the genus of X_K is n(g - 1) + 1, in particular 1 if Z has genus 1"]
theorem genus_genericFibre (hn : 1 ≤ n)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n) :
    (genus (pullback.snd
        (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
        (Spec.map (CommRingCat.ofHom (powerSeriesToLaurent k).toRingHom))) : ℤ) =
        n * (genus f - 1) + 1 ∧
      (genus f = 1 → genus (pullback.snd
        (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
        (Spec.map (CommRingCat.ofHom (powerSeriesToLaurent k).toRingHom))) = 1) := by
  have h := (bijective_appTop_and_genus_genericFibre f φ hn hord).2.2
  refine ⟨h, fun hg => ?_⟩
  rw [hg] at h
  simpa using h

end Curve

/-- **The scheme `X` is regular.** -/
@[stacks 0CEH "the scheme X is regular"]
theorem isRegular_model [Smooth f] (hnk : IsUnit (n : k)) :
    IsRegular (cover f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X) :=
  isRegular_cover f _ hnk.ne_zero

/-- **The special fibre `X_k` is `n` times the reduced special fibre as an effective Cartier
divisor**: `π 𝒪_X` and its radical are invertible ideals, and `π 𝒪_X = (rad(π 𝒪_X))ⁿ`. -/
@[stacks 0CEH "the special fibre X_k is n times the reduced special fibre (X_k)_red as an \
effective Cartier divisor"]
theorem specialFibre_eq_pow [Smooth f] (hnk : IsUnit (n : k)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (specialFibreIdeal f (symPowTrivialization f φ)) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor
        (specialFibreIdeal f (symPowTrivialization f φ)).radical ∧
      specialFibreIdeal f (symPowTrivialization f φ) =
        (specialFibreIdeal f (symPowTrivialization f φ)).radical ^ n :=
  ⟨isEffectiveCartierDivisor_specialFibreIdeal f _ hnk.ne_zero,
    isEffectiveCartierDivisor_radical_specialFibreIdeal f _ hnk.ne_zero,
    specialFibreIdeal_eq_radical_pow f _ hnk.ne_zero⟩

open Stacks.DiscreteValuationRing.Ramification in
/-- **Any finite extension `K'/K` over which `X_K` attains semistable reduction has ramification
index at least `n`**: the valuation `v_{R'}(π)` of `π` in the integral closure `R'` of `R` in
`K'` is a positive multiple of `n`. -/
@[stacks 0CEH "any finite extension K'/K over which X_K attains semistable reduction has \
ramification index at least n: v_{R'}(π) is a positive multiple of n, for R' the integral \
closure of R in K'"]
theorem ramification_of_semistable [IsAlgClosed k] [IsProper f] [Nonempty Z] (hn : 1 ≤ n)
    (K' : Type u) [Field K'] [Algebra (LaurentSeries k) K']
    [FiniteDimensional (LaurentSeries k) K'] [Algebra (PowerSeries k) K']
    [IsScalarTower (PowerSeries k) (LaurentSeries k) K'] :
    haveI := isDiscreteValuationRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
    haveI := _root_.isFractionRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
    (∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (integralClosure (PowerSeries k) K')))
      (e : pullback (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
          (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) K'))) ≅
        pullback q (Spec.map (CommRingCat.ofHom
          (algebraMap (integralClosure (PowerSeries k) K') K')))),
      Stacks.Models.IsModel (pullback.snd _ _) q e ∧ IsProper q ∧
        IsAtWorstNodalOfRelativeDimensionOne q) →
    ∃ m : ℕ, 0 < m ∧ IsDiscreteValuationRing.addVal (integralClosure (PowerSeries k) K')
      (algebraMap (PowerSeries k) (integralClosure (PowerSeries k) K') PowerSeries.X) =
        (n * m : ℕ) :=
  exists_ramificationIdx_eq_mul_of_hasSemistableReduction f _ (by omega) K'

open Stacks.DiscreteValuationRing.Ramification in
/-- **A finite extension `K'/K` over which `X_K` attains semistable reduction has degree at least
`n`**: its ramification index is a positive multiple of `n` (`ramification_of_semistable`), and
the ramification index is at most `[K' : K]` ([Stacks, Tag 09E5]). -/
theorem le_finrank_of_semistable [IsAlgClosed k] [IsProper f] [Nonempty Z] (hn : 1 ≤ n)
    (K' : Type u) [Field K'] [Algebra (LaurentSeries k) K']
    [FiniteDimensional (LaurentSeries k) K'] [Algebra (PowerSeries k) K']
    [IsScalarTower (PowerSeries k) (LaurentSeries k) K'] :
    haveI := isDiscreteValuationRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
    haveI := _root_.isFractionRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
    (∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (integralClosure (PowerSeries k) K')))
      (e : pullback (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
          (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) K'))) ≅
        pullback q (Spec.map (CommRingCat.ofHom
          (algebraMap (integralClosure (PowerSeries k) K') K')))),
      Stacks.Models.IsModel (pullback.snd _ _) q e ∧ IsProper q ∧
        IsAtWorstNodalOfRelativeDimensionOne q) →
    n ≤ Module.finrank (LaurentSeries k) K' := by
  have := isDiscreteValuationRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
  have := _root_.isFractionRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
  have := faithfulSMul_integralClosure (PowerSeries k) (LaurentSeries k) K'
  intro hss
  obtain ⟨m, hm, hv⟩ := ramification_of_semistable f φ hn K' hss
  set R' := integralClosure (PowerSeries k) K'
  have he := addVal_algebraMap_eq_ramificationIdx (PowerSeries k) R' PowerSeries.X
    PowerSeries.X_irreducible
  rw [hv] at he
  have he' : n * m = ramificationIdx (PowerSeries k) R' := by exact_mod_cast he
  have : IsLocalHom (algebraMap (PowerSeries k) R') := inferInstance
  obtain ⟨hfin, hle⟩ :=
    IsDiscreteValuationRing.residueField_finite_and_ramificationIdx_mul_residueDegree_le_finrank
      (PowerSeries k) R' (LaurentSeries k) K'
  have hidx : (IsLocalRing.maximalIdeal R').ramificationIdx (PowerSeries k) =
      ramificationIdx (PowerSeries k) R' := by
    have : (IsLocalRing.maximalIdeal R').LiesOver (IsLocalRing.maximalIdeal (PowerSeries k)) :=
      ⟨((IsLocalRing.isMaximal_iff _).mp
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal R'))).symm⟩
    exact (Ideal.ramificationIdx'_eq_ramificationIdx _ _
      (IsDiscreteValuationRing.not_a_field (PowerSeries k))).symm
  rw [hidx, ← he'] at hle
  calc n ≤ n * m := Nat.le_mul_of_pos_right n hm
    _ ≤ n * m * Module.finrank (IsLocalRing.ResidueField (PowerSeries k))
        (IsLocalRing.ResidueField R') :=
      Nat.le_mul_of_pos_right _ Module.finrank_pos
    _ ≤ _ := hle

/-- **An `n`-torsion invertible module has `L^{⊗ n} ≅ 𝒪_Z`**: the class of `L^{⊗ n}` is `n [L]`. -/
theorem nonempty_tensorPow_iso_unit
    (hord : n • Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace)
      L ‹_› = 0) :
    Nonempty (tensorPow L n ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  have h := picardClass_tensorPowerNat L ‹_› n
  rw [natCast_zsmul, hord] at h
  exact (Stacks.SheafOfModules.picardClass_eq_zero_iff _ _ _ _).1 h

end Stacks.CyclicCover

namespace Stacks.CyclicCover

open Stacks.DiscreteValuationRing.Ramification in
/-- **There is no universal bound on the degree of an extension over which a genus one curve
attains semistable reduction.** For every `B` there is a curve `X_K` over `K = k((π))` with
`H⁰(X_K, 𝒪) = K` and genus `1`, namely the generic fibre of the cyclic cover of a genus one curve
`Z` by an invertible module of prime order `ℓ > B`, such that every finite extension `K'/K` over
which `X_K` attains semistable reduction has `[K' : K] > B`. -/
@[stacks 0CEH "there is no universal bound for the degree of an extension over which a genus 1 \
curve attains semistable reduction: for every B there is a curve X_K over K = k((π)) with \
H⁰(X_K, O) = K and genus 1 such that every finite K'/K over which X_K attains semistable \
reduction has [K' : K] > B"]
theorem no_universal_bound (k : Type u) [Field k] [IsAlgClosed k] (B : ℕ) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ Spec (.of k)) (_ : IsCurve k f) (_ : IsProjectiveVariety k f)
      (_ : Smooth f) (L : Z.Modules)
      (_ : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L) (n : ℕ)
      (φ : tensorPow L n ≅ SheafOfModules.unit Z.ringCatSheaf),
      genus (pullback.snd (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
        (Spec.map (CommRingCat.ofHom (powerSeriesToLaurent k).toRingHom))) = 1 ∧
      Function.Bijective (pullback.snd (coverSnd f (symPowTrivialization f φ) (PowerSeries k)
        PowerSeries.X) (Spec.map (CommRingCat.ofHom (powerSeriesToLaurent k).toRingHom))).appTop ∧
      ∀ (K' : Type u) [Field K'] [Algebra (LaurentSeries k) K']
        [FiniteDimensional (LaurentSeries k) K'] [Algebra (PowerSeries k) K']
        [IsScalarTower (PowerSeries k) (LaurentSeries k) K'],
        haveI := isDiscreteValuationRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
        haveI := _root_.isFractionRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
        (∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (integralClosure (PowerSeries k) K')))
          (e : pullback (coverSnd f (symPowTrivialization f φ) (PowerSeries k) PowerSeries.X)
              (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) K'))) ≅
            pullback q (Spec.map (CommRingCat.ofHom
              (algebraMap (integralClosure (PowerSeries k) K') K')))),
          Stacks.Models.IsModel (pullback.snd _ _) q e ∧ IsProper q ∧
            IsAtWorstNodalOfRelativeDimensionOne q) →
        B < Module.finrank (LaurentSeries k) K' := by
  obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (max B (ringChar k) + 1)
  have := Fact.mk hℓ
  have hBℓ : B < ℓ := by omega
  have hcℓ : ringChar k < ℓ := by omega
  have hℓk : IsUnit (ℓ : k) := by
    refine IsUnit.mk0 _ fun h => ?_
    rcases (Nat.dvd_prime hℓ).1 ((ringChar.spec k ℓ).1 h) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact hcℓ.ne h1
  have hn : 1 ≤ ℓ := hℓ.one_lt.le
  obtain ⟨Z, f, hcurve, hproj, hsmooth, hg⟩ :=
    AlgebraicGeometry.GenusOne.exists_smooth_projective_curve_genus_one k
  obtain ⟨e⟩ :=
    Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve k f ℓ hn hℓk
  let i : Fin (2 * genus f) := ⟨0, by omega⟩
  let x : Stacks.Picard.ofScheme Z := e.symm (Pi.single i 1)
  have hx0 : x ≠ 0 := by
    intro h
    have h1 : e.symm (Pi.single i 1) = 0 := Subtype.ext h
    have h2 : (Pi.single i 1 : Fin (2 * genus f) → ZMod ℓ) i = 0 :=
      congrArg (fun y => y i) (e.symm.map_eq_zero_iff.1 h1)
    rw [Pi.single_eq_same] at h2
    exact one_ne_zero h2
  have hxℓ : ℓ • x = 0 := by
    have h := (Submodule.mem_torsionBy_iff _ _).1 (e.symm (Pi.single i 1)).2
    rwa [natCast_zsmul] at h
  let L : Z.Modules := (Stacks.Picard.picardRepresentative Z.toRingedSpace x).obj
  have hL : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).1
      (Stacks.Picard.picardRepresentative Z.toRingedSpace x).property
  have hclass : Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace)
      L ‹_› = x :=
    Stacks.Picard.classOf_picardRepresentative _ x
  have hord : addOrderOf (Stacks.SheafOfModules.picardClass Z.presheaf
      (structureIsSheaf Z.toRingedSpace) L ‹_›) = ℓ := by
    rw [hclass, addOrderOf_eq_prime hxℓ hx0]
  obtain ⟨φ⟩ := nonempty_tensorPow_iso_unit (L := L) (n := ℓ) (by rwa [hclass])
  exact ⟨Z, f, hcurve, hproj, hsmooth, L, hL, ℓ, φ, (genus_genericFibre f φ hn hord).2 hg,
    (globalSections_cover f φ hn hord).2, fun K' _ _ _ _ _ hss =>
      lt_of_lt_of_le hBℓ (le_finrank_of_semistable f φ hn K' hss)⟩

end Stacks.CyclicCover

end
