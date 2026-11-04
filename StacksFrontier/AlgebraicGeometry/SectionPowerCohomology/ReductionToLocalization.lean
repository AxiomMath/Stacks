module

public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.AffineBaseCase
public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 01XR] from the comparison map of [Stacks, Tag 09MR]

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)` a global section with affine
nonvanishing open `X_s`, `ℱ` a quasi-coherent `𝒪_X`-module and `p > 0`. [Stacks, Tag 01XR] says
that every class `ξ ∈ H^p(X, ℱ)` satisfies `sⁿ ξ = 0` in `H^p(X, ℱ ⊗ ℒ^{⊗ n})` for some `n ≥ 0`.

The source's proof is two lines: `H^p(X_s, ℱ)` vanishes because `X_s` is affine
([Stacks, Tag 01XB]), and therefore the comparison map

`H^p_*(X, ℒ, ℱ)₍s₎ ⟶ H^p(X_s, ℱ)`

of [Stacks, Tag 09MR] has a zero target, so -- being injective -- it forces
`H^p_*(X, ℒ, ℱ)₍s₎ = 0`, which says exactly that every class is annihilated by a power of `s`.
This file proves that deduction: injectivity of
`Stacks.Cohomology.TwistedLocalizationMap.canonicalMap` at the open `⊤` gives the conclusion of
Tag 01XR. Tag 01XR itself is `Stacks.SheafOfModules.exists_sectionPowerAction_eq_zero`, proved in
`StacksFrontier/AlgebraicGeometry/SectionPowerCohomology/QuasiCompact.lean` by the induction of
[Stacks, Tag 09MR] read on homogeneous classes.

## Main results

* `Stacks.Cohomology.SectionPowerLocalization.isZero_hgroup_nonvanishingPart_top`: the target
  of the comparison map vanishes when `X_s` is affine, `ℱ` is quasi-coherent and `p > 0`.
* `Stacks.Cohomology.SectionPowerLocalization.exists_sectionPowerAction_eq_zero_of_injective`:
  the conclusion of [Stacks, Tag 01XR] from injectivity of the comparison map at `⊤`.
* `Stacks.Cohomology.SectionPowerLocalization.injective_canonicalMap_of_isAffineOpen`: over an
  affine open the comparison map is injective in positive degree.

## Implementation notes

The class `ξ` is pushed into degree `1` rather than degree `0`: the degree-`0` homogeneous piece
of `H^p_*(X, ℒ, ℱ)` is `H^p(X, ℱ ⊗ ℒ^{⊗ 0})`, not `H^p(X, ℱ)`, so using it would require the
unitor of the tensor powers, whereas multiplying by `s` once lands in `H^p(X, ℱ ⊗ ℒ)` on the nose.
The fraction `s ξ / s` is then the element of the degree-zero localization that the injectivity
kills, and `Stacks.SheafOfModules.eq_zero_iff_exists_pow_smul_eq_zero` turns its vanishing into
`s^k · (s ξ) = 0`; the two multiplications compose into `s^{k+1}` by
`Stacks.Cohomology.TwistedLocalizationMap.sectionPowerAction_comp_actionOf_powerSectionValue`.

## References

* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules DirectSum
open Stacks.Cohomology.TwistedGradedModule
open Stacks.Cohomology.TwistedLocalizationMap

universe u

namespace Stacks.Cohomology.SectionPowerLocalization

attribute [local instance] Stacks.SheafOfModules.sectionDegreeVAdd

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- The section ring is internally graded by its homogeneous summands. -/
local instance gradedRingGrading :
    GradedRing (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) :=
  sectionRingGradingGradedRing (sectionSiteRing X) (sectionSiteSheaf X) L

variable (s : L.sections) (F : X.Modules) (p : ℕ)

/-- **The target of the comparison map of [Stacks, Tag 09MR] at the open `⊤` vanishes when `X_s`
is affine.** The target is `H^p(⊤ ⊓ X_s, ℱ) = H^p(X_s, ℱ)`, and the positive-degree cohomology of
a quasi-coherent module on an affine open is zero by [Stacks, Tag 01XB]. -/
theorem isZero_hgroup_nonvanishingPart_top [F.IsQuasicoherent]
    (hU : IsAffineOpen (nonvanishingOpen L s)) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf (nonvanishingPart X L s ⊤) p F) :=
  Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F (nonvanishingPart X L s ⊤)
    (by rw [show nonvanishingPart X L s ⊤ = nonvanishingOpen L s from top_inf_eq _]; exact hU)
    p hp

/-- Every element of the degree-zero localization vanishes, the comparison map being injective
into a zero group. -/
private theorem eq_zero_of_injective [F.IsQuasicoherent]
    (hU : IsAffineOpen (nonvanishingOpen L s)) (hp : 0 < p)
    (hinj : Function.Injective (canonicalMap X L s F p ⊤))
    (z : degreeZeroLocalization X L F p ⊤ (homogeneousSection X L s)) : z = 0 :=
  have _ : Subsingleton (Hgroup X.ringCatSheaf (nonvanishingPart X L s ⊤) p F : Type u) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      (isZero_hgroup_nonvanishingPart_top X L s F p hU hp)
  hinj (Subsingleton.elim _ _)

/-- `s ξ`, the class `ξ` multiplied once by `s`, a homogeneous class of degree one. Degree one
rather than degree zero: the degree-zero piece of `H^p_*(X, ℒ, ℱ)` is `H^p(X, ℱ ⊗ ℒ^{⊗ 0})`, which
is only isomorphic to `H^p(X, ℱ)`, whereas this lands on the nose. -/
private def twistOnce (ξ : Hgroup X.ringCatSheaf ⊤ p F) : gradedPiece X L F p ⊤ ((1 : ℕ) : ℤ) :=
  (Hfunctor X.ringCatSheaf ⊤ p).map
    (sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F ((1 : ℕ) : ℤ)
      (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s 1)) ξ

/-- The numerator `s ξ` of the fraction `s ξ / s`, as an element of the graded module. -/
private def numerator (ξ : Hgroup X.ringCatSheaf ⊤ p F) : twistedCohomologyModule X L F p ⊤ :=
  DirectSum.of (fun j : ℤ => gradedPiece X L F p ⊤ j) ((1 : ℕ) : ℤ) (twistOnce X L s F p ξ)

/-- The numerator is homogeneous of degree `1 * 1`, the shape the fraction calculus wants. -/
private theorem numerator_mem (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    numerator X L s F p ξ ∈ grading X L F p ⊤ ((1 * 1 : ℕ) : ℤ) := by
  rw [Nat.mul_one]
  exact ⟨twistOnce X L s F p ξ, rfl⟩

/-- **Some power of `s` kills `s ξ`**, which is what the vanishing of the fraction `s ξ / s` in the
degree-zero localization says. -/
private theorem exists_pow_smul_numerator_eq_zero [F.IsQuasicoherent]
    (hU : IsAffineOpen (nonvanishingOpen L s)) (hp : 0 < p)
    (hinj : Function.Injective (canonicalMap X L s F p ⊤))
    (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    ∃ k : ℕ, homogeneousSection X L s ^ k • numerator X L s F p ξ = 0 :=
  (eq_zero_iff_exists_pow_smul_eq_zero
      (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p ⊤)
      ⟨LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
          (numerator X L s F p ξ)
          ⟨homogeneousSection X L s ^ 1, by exact ⟨1, rfl⟩⟩,
        mk_mem_degreeZeroLocalization_of_degree
          (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p ⊤)
          (homogeneousSection_mem X L s) 1 _ (numerator_mem X L s F p ξ)⟩
      1 (numerator X L s F p ξ) rfl).mp
    (eq_zero_of_injective X L s F p hU hp hinj _)

/-- Multiplying the numerator by `s^k` is the degree-`k+1` homogeneous class `s^k · (s ξ)`. -/
private theorem pow_smul_numerator (k : ℕ) (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    homogeneousSection X L s ^ k • numerator X L s F p ξ =
      DirectSum.of _ ((k + 1 : ℕ) : ℤ)
        (act X L F p ⊤ (k : ℤ) ((1 : ℕ) : ℤ)
          (Stacks.Cohomology.PowerSection.powerSectionValue X L s k)
          (twistOnce X L s F p ξ)) := by
  rw [show numerator X L s F p ξ
        = DirectSum.of (fun j : ℤ => gradedPiece X L F p ⊤ j) ((1 : ℕ) : ℤ)
            (twistOnce X L s F p ξ) from rfl,
    ← Stacks.Cohomology.PowerSection.of_powerSectionValue]
  exact of_smul_of X L F p ⊤ k ((1 : ℕ) : ℤ)
    (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) (twistOnce X L s F p ξ)

/-- **`s^k · (s ξ) = 0` as a cohomology class**, read off the vanishing of the homogeneous
element. -/
private theorem act_pow_twistOnce_eq_zero [F.IsQuasicoherent]
    (hU : IsAffineOpen (nonvanishingOpen L s)) (hp : 0 < p)
    (hinj : Function.Injective (canonicalMap X L s F p ⊤))
    (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    ∃ k : ℕ, act X L F p ⊤ (k : ℤ) ((1 : ℕ) : ℤ)
      (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) (twistOnce X L s F p ξ) = 0 := by
  obtain ⟨k, hk⟩ := exists_pow_smul_numerator_eq_zero X L s F p hU hp hinj ξ
  refine ⟨k, ?_⟩
  have h2 : (homogeneousSection X L s ^ k • numerator X L s F p ξ) ((k + 1 : ℕ) : ℤ) = 0 := by
    rw [hk]; rfl
  rw [pow_smul_numerator, DirectSum.of_eq_same] at h2
  exact h2

/-- **The conclusion of [Stacks, Tag 01XR] from injectivity of the comparison map of
[Stacks, Tag 09MR] at `⊤`.** Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)`
a global section whose nonvanishing open `X_s` is affine, `ℱ` a quasi-coherent `𝒪_X`-module and
`p > 0`. If the canonical map

`H^p_*(X, ℒ, ℱ)₍s₎ ⟶ H^p(X_s, ℱ)`

is injective, then every class `ξ ∈ H^p(X, ℱ)` is annihilated by a power of `s`: there are `n` and
a morphism `t : 𝒪_X ⟶ ℒ^{⊗ n}` representing `sⁿ` with `sⁿ ξ = 0` in `H^p(X, ℱ ⊗ ℒ^{⊗ n})`. -/
theorem exists_sectionPowerAction_eq_zero_of_injective [F.IsQuasicoherent]
    (hU : IsAffineOpen (nonvanishingOpen L s)) (hp : 0 < p)
    (hinj : Function.Injective (canonicalMap X L s F p ⊤))
    (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    ∃ (n : ℕ) (t : SheafOfModules.unit X.ringCatSheaf ⟶
        TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n),
      IsSectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n t ∧
        (Hfunctor X.ringCatSheaf ⊤ p).map
          (sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F n t) ξ = 0 := by
  obtain ⟨k, hk⟩ := act_pow_twistOnce_eq_zero X L s F p hU hp hinj ξ
  refine ⟨k + 1, sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s (k + 1),
    isSectionPowerHom_sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s (k + 1), ?_⟩
  refine Eq.trans (congrArg (fun φ => (Hfunctor X.ringCatSheaf ⊤ p).map φ ξ)
    (sectionPowerAction_comp_actionOf_powerSectionValue X L s F k 1).symm) ?_
  exact (map_comp_apply X.ringCatSheaf p ⊤ _ _ ξ).trans hk

/-! ### Injectivity over an affine open

Over an affine open the source of the comparison map is trivial in positive degree -- every
homogeneous component `H^p(U, ℱ ⊗ ℒ^{⊗ n})` vanishes by [Stacks, Tag 01XB] -- so the comparison
map is injective there. -/

/-- **Over an affine open the comparison map of [Stacks, Tag 09MR] is injective in positive
degree**, its source being trivial by [Stacks, Tag 01XB]. -/
theorem injective_canonicalMap_of_isAffineOpen [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (hp : 0 < p) :
    Function.Injective (canonicalMap X L s F p U) := by
  have hsub : Subsingleton (degreeZeroLocalization X L F p U (homogeneousSection X L s)) :=
    Stacks.Cohomology.TwistedLocalization.subsingleton_degreeZeroLocalization_of_forall_eq_zero
      (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L) (grading X L F p U)
      (homogeneousSection_mem X L s) (fun n x hx => by
        obtain ⟨ξ, rfl⟩ := hx
        have hss := AddCommGrpCat.isZero_iff_subsingleton.mp
          (Stacks.Cohomology.TwistedLocalization.isZero_hgroup_twistedModule_of_isAffineOpen
            X L F U hU p hp (n : ℤ))
        rw [Subsingleton.elim ξ 0, map_zero])
  exact fun a b _ => Subsingleton.elim a b

/-- **The conclusion of [Stacks, Tag 01XR] on an affine scheme, through [Stacks, Tag 09MR].**
On an affine scheme the injectivity of the comparison map at `⊤` is
`injective_canonicalMap_of_isAffineOpen`, and `X_s` is affine by [Stacks, Tag 01PV]. -/
theorem exists_sectionPowerAction_eq_zero_of_isAffine [IsAffine X] [F.IsQuasicoherent]
    (hp : 0 < p) (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    ∃ (n : ℕ) (t : SheafOfModules.unit X.ringCatSheaf ⟶
        TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L n),
      IsSectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n t ∧
        (Hfunctor X.ringCatSheaf ⊤ p).map
          (sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F n t) ξ = 0 :=
  exists_sectionPowerAction_eq_zero_of_injective X L s F p
    (by
      have h := AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen L s ⊤
        (isAffineOpen_top X)
      rwa [top_inf_eq] at h)
    hp (injective_canonicalMap_of_isAffineOpen X L s F p ⊤ (isAffineOpen_top X) hp) ξ

/-! ### The degree-zero normalisation on a scheme

`HzeroIso` is stated for a sheaf of rings on a topological space; these two specialisations read
it at `X.ringCatSheaf`. -/

/-- **Degree-zero cohomology of a module on a scheme is its module of sections.** -/
def schemeHZeroIso (Y : Scheme.{u}) (U : Y.Opens) :
    (Hfunctor Y.ringCatSheaf U 0 : Y.Modules ⥤ AddCommGrpCat.{u}) ≅ secF Y.ringCatSheaf U :=
  HzeroIso Y.ringCatSheaf U

/-- **Restriction on degree-zero cohomology of a scheme is restriction of sections.** -/
theorem schemeHrestrict_zero (Y : Scheme.{u}) {U V : Y.Opens} (h : U ≤ V) (G : Y.Modules) :
    Hrestrict Y.ringCatSheaf h 0 G = (schemeHZeroIso Y V).hom.app G ≫
      (secRestrict Y.ringCatSheaf h).app G ≫ (schemeHZeroIso Y U).inv.app G := by
  have happ : Hrestrict Y.ringCatSheaf h 0 G ≫ ((schemeHZeroIso Y U).app G).hom =
      (schemeHZeroIso Y V).hom.app G ≫ (secRestrict Y.ringCatSheaf h).app G :=
    NatTrans.congr_app (HzeroIso_hom_HrestrictNT Y.ringCatSheaf h) G
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv ((schemeHZeroIso Y U).app G)).2 happ

end Stacks.Cohomology.SectionPowerLocalization

end
