module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceFormsDichotomy
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.TopFormsNormalizedDualizing
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction

/-!
# The twist dichotomy of a point blowup, carried to `AlgebraicGeometry.blowUp`

There are two constructions of the blowing up of a scheme in a quasi-coherent sheaf of ideals:
`Stacks.Blowup.blowUp`, the relative `Proj` of the Rees algebra built from
`Stacks.Blowup.reesData`, and `AlgebraicGeometry.blowUp`. They are isomorphic over the base
(`Stacks.Blowup.blowUpIso`) but not definitionally equal. This file proves [Stacks, Tag 0B4L],
the identification of `Ω_{X/S}` with the direct image of a finite locally free module on the
exceptional divisor, and the twist dichotomy of [Stacks, Tag 0B3T] for a point blowup, for
`AlgebraicGeometry.blowUp`.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `comap_exceptionalIdeal_blowUpIso_hom`, `exceptionalDivisorComparison`,
  `exceptionalDivisorComparison_subschemeι` and `isIso_exceptionalDivisorComparison`: the
  comparison isomorphism of the two exceptional divisors over the common blowup.
* `exists_forms_iso_pushforward_exceptionalIdeal`: [Stacks, Tag 0B4L] for
  `AlgebraicGeometry.blowUp`, `Ω_{X/S} ≅ i_*𝒢` with `𝒢` finite locally free of rank `s` on
  the exceptional divisor, as soon as `Ω_{E/Z}` is, where `X = AlgebraicGeometry.blowUp I` and
  `i` is the inclusion of `AlgebraicGeometry.exceptionalIdeal I`.
* `exists_le_min_tensorIso_reflexiveHull_exteriorPower_blowUp_ideal`: the bounded twist of
  [Stacks, Tag 0B3T] at `AlgebraicGeometry.blowUp I`.
* `exists_eq_zero_or_eq_one_tensorIso_reflexiveHull_exteriorPower_blowUp_ideal` and
  `nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_blowUp_ideal`: the dichotomy
  itself at `AlgebraicGeometry.blowUp I`, `Ω^r_{X} ≅ (b^*Ω^r)(E)` or `Ω^r_{X} ≅ b^*Ω^r`.
* `nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton`: the same at
  `AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)` for a closed point
  `w` of an integral regular Noetherian surface, stated with `Stacks.BlowupTwistUnit.hullForms`,
  under the hypothesis that `Ω_{E/Z}` is invertible.

## Implementation notes

In `exists_forms_iso_pushforward_exceptionalIdeal` the module on the exceptional divisor is the
pullback along the inverse of `Stacks.BlowupTwistUnit.exceptionalDivisorComparison`.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B4L](https://stacks.math.columbia.edu/tag/0B4L)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Scheme.Modules Stacks.SheafOfModules

universe u

namespace Stacks.BlowupTwistUnit

/-! ### The comparison of the two exceptional divisors -/

variable {S Z : Scheme.{u}} (p : Z ⟶ S) [IsClosedImmersion p]

/-- The two exceptional ideals correspond under the comparison of the two blowups. -/
theorem comap_exceptionalIdeal_blowUpIso_hom {X : Scheme.{u}} (I : X.IdealSheafData) :
    (AlgebraicGeometry.exceptionalIdeal I).comap (Stacks.Blowup.blowUpIso I).hom =
      Stacks.Blowup.exceptionalIdeal I := by
  change (I.comap (AlgebraicGeometry.blowUpToBase I)).comap (Stacks.Blowup.blowUpIso I).hom =
    I.comap (Stacks.Blowup.blowUpToBase I)
  rw [← Scheme.IdealSheafData.comap_comp, Stacks.Blowup.blowUpIso_hom_comp]

/-- The comparison morphism of the exceptional divisors of the two constructions of the blowup,
over the comparison isomorphism of the blowups themselves. -/
def exceptionalDivisorComparison {X : Scheme.{u}} (I : X.IdealSheafData) :
    (Stacks.Blowup.exceptionalIdeal I).subscheme ⟶
      (AlgebraicGeometry.exceptionalIdeal I).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (Stacks.Blowup.blowUpIso I).hom
    (by rw [← comap_exceptionalIdeal_blowUpIso_hom I]
        exact Scheme.IdealSheafData.le_map_comap _ _)

/-- The comparison of exceptional divisors sits over the comparison of the blowups. -/
theorem exceptionalDivisorComparison_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) :
    exceptionalDivisorComparison I ≫ (AlgebraicGeometry.exceptionalIdeal I).subschemeι =
      (Stacks.Blowup.exceptionalIdeal I).subschemeι ≫ (Stacks.Blowup.blowUpIso I).hom :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The comparison of the exceptional divisors is an isomorphism. -/
instance isIso_exceptionalDivisorComparison {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsIso (exceptionalDivisorComparison I) := by
  have hpb : IsPullback (Stacks.Blowup.exceptionalIdeal I).subschemeι
      (exceptionalDivisorComparison I) (Stacks.Blowup.blowUpIso I).hom
      (AlgebraicGeometry.exceptionalIdeal I).subschemeι :=
    AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _
      (exceptionalDivisorComparison_subschemeι I).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
          exact comap_exceptionalIdeal_blowUpIso_hom I)
  exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) hpb
    inferInstance

/-! ### Tag 0B4L for `AlgebraicGeometry.blowUp` -/

/-- For `p : Z ⟶ S` a closed immersion with `p.ker = I`, if the relative differentials of the
exceptional divisor over the centre are finite locally free of rank `s` then the relative
differentials of `AlgebraicGeometry.blowUpToBase I` are the direct image, along the inclusion of
`AlgebraicGeometry.exceptionalIdeal I`, of a module finite locally free of rank `s`
([Stacks, Tag 0B4L]). -/
theorem exists_forms_iso_pushforward_exceptionalIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    {Z : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p] (hp : p.ker = I) (s : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p)) s) :
    ∃ G : (AlgebraicGeometry.exceptionalIdeal I).subscheme.Modules,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s ∧
      Nonempty (Scheme.Hom.relativeDifferentials (AlgebraicGeometry.blowUpToBase I) ≅
        (Scheme.Modules.pushforward
          (AlgebraicGeometry.exceptionalIdeal I).subschemeι).obj G) := by
  subst hp
  have := hE
  set e := Stacks.Blowup.blowUpIso p.ker with he
  set ΩE := Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p) with hΩE
  refine ⟨(Scheme.Modules.pullback (inv (exceptionalDivisorComparison p.ker))).obj ΩE,
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ ΩE s, ?_⟩
  have hcomm : e.hom ≫ AlgebraicGeometry.blowUpToBase p.ker =
      Stacks.Blowup.blowUpToBase p.ker ≫ 𝟙 X := by
    rw [Category.comp_id, he]; exact Stacks.Blowup.blowUpIso_hom_comp p.ker
  have := Scheme.Hom.isIso_relativeDifferentialsMap_of_isIso e.hom
    (AlgebraicGeometry.blowUpToBase p.ker) (Stacks.Blowup.blowUpToBase p.ker) (𝟙 X) hcomm
  have i2 : (Scheme.Modules.pushforward e.hom).obj
      (Scheme.Hom.relativeDifferentials (Stacks.Blowup.blowUpToBase p.ker)) ≅
      Scheme.Hom.relativeDifferentials (AlgebraicGeometry.blowUpToBase p.ker) :=
    Scheme.Modules.pushforwardObjIsoOfPullbackIso e
      (asIso (Scheme.Hom.relativeDifferentialsMap e.hom
        (AlgebraicGeometry.blowUpToBase p.ker) (Stacks.Blowup.blowUpToBase p.ker) (𝟙 X)
        hcomm)).symm
  have i3 : Scheme.Hom.relativeDifferentials (Stacks.Blowup.blowUpToBase p.ker) ≅
      (Scheme.Modules.pushforward
        (Stacks.Blowup.exceptionalIdeal p.ker).subschemeι).obj ΩE :=
    @asIso _ _ _ _ (Stacks.Blowup.relativeDifferentialsToPushforward p)
      (Stacks.Blowup.isIso_relativeDifferentialsToPushforward p)
  have i4 : ΩE ≅ (Scheme.Modules.pullback (exceptionalDivisorComparison p.ker)).obj
      ((Scheme.Modules.pullback (inv (exceptionalDivisorComparison p.ker))).obj ΩE) :=
    ((Scheme.Modules.pullbackEquivOfIso
      (asIso (exceptionalDivisorComparison p.ker))).counitIso.app ΩE).symm
  have i5 : (Scheme.Modules.pushforward (exceptionalDivisorComparison p.ker)).obj ΩE ≅
      (Scheme.Modules.pullback (inv (exceptionalDivisorComparison p.ker))).obj ΩE :=
    Scheme.Modules.pushforwardObjIsoOfPullbackIso
      (asIso (exceptionalDivisorComparison p.ker)) i4
  refine ⟨i2.symm ≪≫ (Scheme.Modules.pushforward e.hom).mapIso i3 ≪≫ ?_⟩
  refine ((Scheme.Modules.pushforwardComp
    (Stacks.Blowup.exceptionalIdeal p.ker).subschemeι e.hom).app ΩE) ≪≫ ?_
  refine (Scheme.Modules.pushforwardCongr
    (exceptionalDivisorComparison_subschemeι p.ker).symm).app ΩE ≪≫ ?_
  refine ((Scheme.Modules.pushforwardComp (exceptionalDivisorComparison p.ker)
    (AlgebraicGeometry.exceptionalIdeal p.ker).subschemeι).app ΩE).symm ≪≫ ?_
  exact (Scheme.Modules.pushforward
    (AlgebraicGeometry.exceptionalIdeal p.ker).subschemeι).mapIso i5

/-! ### The bounded twist at `AlgebraicGeometry.blowUp` -/

variable {X S₀ : Scheme.{u}} (I : X.IdealSheafData)

/-- The top forms of `AlgebraicGeometry.blowUp I` differ from the pulled-back top forms of the base
by at most `min s r` copies of the exceptional divisor. -/
theorem exists_le_min_tensorIso_reflexiveHull_exteriorPower_blowUp_ideal
    {Z : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p] (hp : p.ker = I) (q : X ⟶ S₀)
    [AlgebraicGeometry.IsIntegral (AlgebraicGeometry.blowUp I)]
    (hX : AlgebraicGeometry.IsRegular (AlgebraicGeometry.blowUp I))
    (hXdim : topologicalKrullDim (AlgebraicGeometry.blowUp I) ≤ 2)
    [AlgebraicGeometry.IsIntegral (AlgebraicGeometry.exceptionalIdeal I).subscheme]
    (s : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p)) s)
    (r : ℕ)
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase I)).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)).IsCoherent]
    (U : (AlgebraicGeometry.blowUp I).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp I, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase I)).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)).over U) r] :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp I).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ (AlgebraicGeometry.blowUp I).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp I).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal I ^ k))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase I)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)) (r : ℤ))) := by
  obtain ⟨G, hGfree, ⟨hforms⟩⟩ :=
    exists_forms_iso_pushforward_exceptionalIdeal I p hp s hE
  have := hGfree
  exact Stacks.BlowupFormsDichotomy.exists_le_min_tensorIso_reflexiveHull_exteriorPower_of_forms_iso
    (AlgebraicGeometry.blowUpToBase I) q hX hXdim (AlgebraicGeometry.exceptionalIdeal I)
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) G s hforms r U hU

/-! ### The dichotomy at `AlgebraicGeometry.blowUp` -/

/-- The dichotomy of [Stacks, Tag 0B4T] at `AlgebraicGeometry.blowUp I`: the twist exponent is
`0` or `1`. -/
theorem exists_eq_zero_or_eq_one_tensorIso_reflexiveHull_exteriorPower_blowUp_ideal
    {Z : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p] (hp : p.ker = I) (q : X ⟶ S₀)
    [AlgebraicGeometry.IsIntegral (AlgebraicGeometry.blowUp I)]
    (hX : AlgebraicGeometry.IsRegular (AlgebraicGeometry.blowUp I))
    (hXdim : topologicalKrullDim (AlgebraicGeometry.blowUp I) ≤ 2)
    [AlgebraicGeometry.IsIntegral (AlgebraicGeometry.exceptionalIdeal I).subscheme]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p)) 1)
    (r : ℕ)
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase I)).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)).IsCoherent]
    (U : (AlgebraicGeometry.blowUp I).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp I, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase I)).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)).over U) r] :
    ∃ k : ℕ, (k = 0 ∨ k = 1) ∧ Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp I).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ (AlgebraicGeometry.blowUp I).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp I).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal I ^ k))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase I)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)) (r : ℤ))) := by
  obtain ⟨k, hk, hiso⟩ := exists_le_min_tensorIso_reflexiveHull_exteriorPower_blowUp_ideal
    I p hp q hX hXdim 1 hE r U hU
  exact ⟨k, Nat.le_one_iff_eq_zero_or_eq_one.mp (hk.trans (min_le_left _ _)), hiso⟩

/-- The dichotomy of [Stacks, Tag 0B4T] at `AlgebraicGeometry.blowUp I`, with its two alternatives
spelled out: `Ω^r_X ≅ (b^*Ω^r)(E)` or `Ω^r_X ≅ b^*Ω^r`, where `Ω^r` abbreviates `(⋀^r Ω)^{∨∨}`. -/
theorem nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_blowUp_ideal
    {Z : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p] (hp : p.ker = I) (q : X ⟶ S₀)
    [AlgebraicGeometry.IsIntegral (AlgebraicGeometry.blowUp I)]
    (hX : AlgebraicGeometry.IsRegular (AlgebraicGeometry.blowUp I))
    (hXdim : topologicalKrullDim (AlgebraicGeometry.blowUp I) ≤ 2)
    [AlgebraicGeometry.IsIntegral (AlgebraicGeometry.exceptionalIdeal I).subscheme]
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (Stacks.Blowup.exceptionalToCentre p)) 1)
    (r : ℕ)
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase I)).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)).IsCoherent]
    (U : (AlgebraicGeometry.blowUp I).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp I, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase I)).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)).over U) r] :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp I).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ (AlgebraicGeometry.blowUp I).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp I).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal I))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase I)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)) (r : ℤ))) ∨
    Nonempty
      (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase I)).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ)) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase I ≫ q)) (r : ℤ))) := by
  obtain ⟨k, hk, ⟨e⟩⟩ :=
    exists_eq_zero_or_eq_one_tensorIso_reflexiveHull_exteriorPower_blowUp_ideal
      I p hp q hX hXdim hE r U hU
  rcases hk with rfl | rfl
  · refine Or.inr ⟨Iso.symm ?_ ≪≫ e⟩
    exact Iso.app ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
          (eqToIso (congrArg Stacks.Divisors.invertibleSheaf'
              ((pow_zero (AlgebraicGeometry.exceptionalIdeal I)).trans
                Scheme.IdealSheafData.one_eq_top)) ≪≫
            Stacks.Divisors.invertibleSheafTopIsoUnit)) _ ≪≫
        AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso
          (AlgebraicGeometry.blowUp I).toRingedSpace _
  · refine Or.inl ⟨Iso.symm ?_ ≪≫ e⟩
    exact Iso.app ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
      (eqToIso (congrArg Stacks.Divisors.invertibleSheaf'
        (pow_one (AlgebraicGeometry.exceptionalIdeal I))))) _

/-! ### At a closed point of an integral regular Noetherian surface -/

/-- The dichotomy of [Stacks, Tag 0B4T] at the blowing up
`AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)` of an integral regular
Noetherian surface in a closed point `w` whose local ring has dimension two, when `Ω_{E/Z}` is
invertible (`hE`). -/
theorem nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_vanishingIdeal_singleton
    {W S₀ : Scheme.{u}} [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (q : W ⟶ S₀)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.exceptionalToCentre (pointIdeal w hw).subschemeι)) 1)
    (r : ℕ)
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)).IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)).over U) r] :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)) (r : ℤ))) ∨
    Nonempty
      (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ)) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)) (r : ℤ))) := by
  have : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    AlgebraicGeometry.isIntegral_blowUp _
      (Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hdim w hw)
  obtain ⟨hregX, hdimX⟩ :=
    AlgebraicGeometry.isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton
      W hreg hdim w hw
  obtain ⟨ec, -⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal
      w hw ((((isRegular_tfae W).out 1 2 rfl rfl).mp hreg).2 w) hstalkdim
  have : AlgebraicGeometry.IsIntegral
      (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)).subscheme :=
    AlgebraicGeometry.isIntegral_subscheme_of_iso_projectiveLineProj _ _ ec
  exact nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_blowUp_ideal
    (pointIdeal w hw) (pointIdeal w hw).subschemeι
    (Scheme.IdealSheafData.ker_subschemeι _) q hregX hdimX.le hE r U hU

/-- `(Ω^n_{V/S₀})^{**}` for `V ⟶ W ⟶ S ⟶ S₀` read with the last two morphisms composed: the
`Stacks.BlowupTwistUnit.hullForms` of the factorization through `W` is the reflexive hull of the
`n`-th exterior power of `Ω_{V/S₀}` presented through the factorization through `S`. -/
theorem hullForms_comp_eq_reflexiveHull_exteriorPower {S₀ S W V : Scheme.{u}} (p : S ⟶ S₀)
    (n : ℤ) (b : V ⟶ W) (h : W ⟶ S) :
    hullForms p n (b ≫ h) =
      reflexiveHull (exteriorPower
        (Scheme.Hom.relativeDifferentials (b ≫ (h ≫ p))) n) := by
  change reflexiveHull (Scheme.Hom.relativeDifferentialForms ((b ≫ h) ≫ p) n) =
    reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials (b ≫ (h ≫ p))) n)
  rw [Category.assoc]
  rfl

/-- The dichotomy of [Stacks, Tag 0B4T] at the blowup `b` of an integral regular Noetherian
surface `W` in a closed point, for `h : W ⟶ S` and `p : S ⟶ S₀`, in the form
`(⋀^r b^*Ω_{W/S₀})^{∨∨}(E) ≅ hullForms p r (b ≫ h)` or
`(⋀^r b^*Ω_{W/S₀})^{∨∨} ≅ hullForms p r (b ≫ h)`. -/
theorem nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton
    {S₀ S W : Scheme.{u}} [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials
        (Stacks.Blowup.exceptionalToCentre (pointIdeal w hw).subschemeι)) 1)
    (r : ℕ)
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).over U) r] :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
            (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ))) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) ∨
    Nonempty
      (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
            (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ)) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) := by
  rw [hullForms_comp_eq_reflexiveHull_exteriorPower]
  exact nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_vanishingIdeal_singleton
    hreg hdim w hw hstalkdim (h ≫ p) hE r U hU

end Stacks.BlowupTwistUnit

end
