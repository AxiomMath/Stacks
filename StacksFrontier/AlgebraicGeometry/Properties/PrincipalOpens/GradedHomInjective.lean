module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingGradedHom
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionsCore
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.TwistedHomAnnihilator

/-!
# Injectivity of the localized graded Hom map on a nonvanishing open

Let `X` be a quasi-compact scheme, let `L` be an invertible `𝒪_X`-module and let `s` be a global
section of `L`, with nonvanishing open `X_s`. This file transports a *local* annihilation
statement for a twisted global section of the internal Hom sheaf `ℋom(ℱ, 𝒢)` into the graded
module `⨁_n Hom(ℱ, 𝒢 ⊗ L^{⊗ n})` of
[Stacks, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M): a single power of `s` kills the
homogeneous element. This is the step on which the injectivity half of
[Stacks, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ) turns.

## Main definitions

* `Stacks.SheafOfModules.IsLocallyKilledByPowers`: the local annihilation condition on a twisted
  global section of `ℋom(ℱ, 𝒢) ⊗ L^{⊗ n}`.

## Main results

* `Stacks.SheafOfModules.exists_pow_smul_eq_zero_of_locally`: **the transport step**, on a
  quasi-compact scheme a locally annihilated twisted section gives one exponent `e` with
  `s ^ e • f = 0` in `⨁_n Hom(ℱ, 𝒢 ⊗ L^{⊗ n})`.
* `Stacks.SheafOfModules.homToTwistedSection_restrict_eq_zero`: the vanishing criterion, a
  fraction `f / sⁿ` sent to the zero morphism on `X_s` has `f` restricting to zero there.
* `Stacks.SheafOfModules.homLocalizationMap_injective_of_locally`: injectivity of the Tag 0B5M
  comparison map, granted the local annihilation step.
* `Stacks.SheafOfModules.homLocalizationMap_injective`: **[Stacks, Tag 01XQ] part (1)**, the
  Tag 0B5M comparison map is injective for `ℱ` of finite type on a quasi-compact scheme.

## Implementation notes

The graded action of the section ring on the section module is the one of Tag 01CV, computed on
homogeneous elements by `Stacks.SheafOfModules.sectionModuleAction`. That operation is the
coherence isomorphism applied to the pure tensor `c ⊗ t` of global sections, so its restriction
to an open `U` is zero as soon as the restricted pure tensor is: if `c|_U = r • q` and
`r` annihilates `t|_U`, the scalar moves across the tensor and kills it. Over an open where `s`
has a local equation `r` the power `s ^ e|_U` is divisible by `r ^ e`, so the local annihilation
hypothesis applies; raising the exponent only multiplies by a further power of `s`, so on a
quasi-compact space one exponent works at every point of a finite cover, and the sheaf condition
assembles the vanishing.

## References

* [Stacks Project, Tag 01XQ](https://stacks.math.columbia.edu/tag/01XQ)
* [Stacks Project, Tag 0B5M](https://stacks.math.columbia.edu/tag/0B5M)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite DirectSum Limits
open scoped _root_.TensorProduct

universe u

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

section GradedHomInjectivity

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

open MonoidalCategory

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv
  Stacks.SchemeModulesSpelling.sectionRingGradedRing
  Stacks.SchemeModulesSpelling.sectionRingGradingGradedRing
  Stacks.SchemeModulesSpelling.sectionModuleModule

variable (F G : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- Acting by `s ^ e` on a homogeneous element of the graded Hom module is, under the
internal-Hom comparison, acting by `s ^ e` on the corresponding twisted section. -/
private theorem gradedHomComparison_pow_smul (s : L.sections) (e n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))) :
    gradedHomComparison X L F G
        (homogeneousSection X L s ^ e • (DirectSum.of _ (n : ℤ) f : gradedHom X L F G)) =
      DirectSum.of _ ((e : ℤ) + (n : ℤ))
        (sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L
          (sheafHomSpace X.toRingedSpace F G) e (n : ℤ) (sectionPower X L s e)
          (homToTwistedSection X L F G (n : ℤ) f)) := by
  refine Eq.trans ((gradedHomComparison X L F G).apply_symm_apply _) ?_
  refine Eq.trans (congrArg (fun z => homogeneousSection X L s ^ e • z)
    (gradedHomComparison_of X L F G (n : ℤ) f)) ?_
  refine Eq.trans (congrArg (fun c => c • (DirectSum.of _ (n : ℤ)
    (homToTwistedSection X L F G (n : ℤ) f) :
      sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L
        (sheafHomSpace X.toRingedSpace F G)))
    (homogeneousSection_pow_eq_of_sectionPower X L s e)) ?_
  exact (chosenModuleStructure (sectionSiteRing X) (sectionSiteSheaf X) L
    (sheafHomSpace X.toRingedSpace F G)).smul_eq e (n : ℤ) (sectionPower X L s e)
    (homToTwistedSection X L F G (n : ℤ) f)

/-- A power of `s` kills a homogeneous element of the graded Hom module exactly when it kills
the corresponding twisted section of the internal Hom sheaf. -/
private theorem homogeneous_pow_smul_eq_zero_iff (s : L.sections) (e n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))) :
    homogeneousSection X L s ^ e • (DirectSum.of _ (n : ℤ) f : gradedHom X L F G) = 0 ↔
      sectionModuleAction (sectionSiteRing X) (sectionSiteSheaf X) L
        (sheafHomSpace X.toRingedSpace F G) e (n : ℤ) (sectionPower X L s e)
        (homToTwistedSection X L F G (n : ℤ) f) = 0 := by
  constructor
  · intro h
    have h0 := (gradedHomComparison_pow_smul X L F G s e n f).symm.trans
      ((congrArg (gradedHomComparison X L F G) h).trans (map_zero _))
    have hz := congrArg (fun z : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L
      (sheafHomSpace X.toRingedSpace F G) => z ((e : ℤ) + (n : ℤ))) h0
    simpa only [DirectSum.of_eq_same, DFinsupp.zero_apply] using hz
  · intro h
    refine (gradedHomComparison X L F G).injective ?_
    refine (gradedHomComparison_pow_smul X L F G s e n f).trans ?_
    rw [h]
    exact (map_zero _).trans (map_zero _).symm

/-- The local annihilation condition on a twisted global section `t` of `ℋom(ℱ, 𝒢) ⊗ L^{⊗ n}`:
near every point of `X` some power of a local equation for `s` kills the restriction of `t`. -/
abbrev IsLocallyKilledByPowers (s : L.sections) (n : ℕ)
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) : Prop :=
  ∀ x : X, ∃ (e : ℕ) (U : Opens X.toRingedSpace) (r : (sectionSiteRing X).obj (op U))
      (l : L.val.obj (op U)), x ∈ U ∧ s.eval (op U) = r • l ∧
    r ^ e • ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.map
        (terminal.from U).op t = 0

/-- **The transport of a local annihilation statement into the graded Hom module.** On a
quasi-compact scheme, if near every point some power of a local equation for `s` annihilates the
restriction of the twisted section attached to `f`, then a single power of `s` annihilates the
homogeneous element `f` of `⨁_n Hom(ℱ, 𝒢 ⊗ L^{⊗ n})`. -/
theorem exists_pow_smul_eq_zero_of_locally [CompactSpace X] (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)))))
    (hlocal : IsLocallyKilledByPowers X L F G s n
      (homToTwistedSection X L F G (n : ℤ) f)) :
    ∃ e : ℕ, homogeneousSection X L s ^ e •
      (DirectSum.of _ (n : ℤ) f : gradedHom X L F G) = 0 := by
  obtain ⟨e, he⟩ := exists_sectionModuleAction_eq_zero_of_locally X L
    (sheafHomSpace X.toRingedSpace F G) s (n : ℤ)
    (homToTwistedSection X L F G (n : ℤ) f) (by
      intro x
      obtain ⟨e, U, r, l, hxU, hsU, hr⟩ := hlocal x
      obtain ⟨q, hq⟩ := sectionPower_restrict_dvd_smul X L s U r l hsU e
      exact ⟨e, U, hxU, sectionModuleAction_restrict_eq_zero_of_smul X L
        (sheafHomSpace X.toRingedSpace F G) e (n : ℤ) (sectionPower X L s e)
        (homToTwistedSection X L F G (n : ℤ) f) U (r ^ e) q hq hr⟩)
  exact ⟨e, (homogeneous_pow_smul_eq_zero_iff X L F G s e n f).mpr he⟩

/-- **The vanishing criterion on the nonvanishing open.** If the fraction `f / sⁿ` is sent to
the zero morphism on `X_s`, then the twisted section attached to `f` already restricts to zero
on `X_s`. -/
theorem homToTwistedSection_restrict_eq_zero (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)))))
    (hf : homLocalizationMap X L F G s (homFraction X L F G s n f) = 0) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.map
        (terminal.from (nonvanishingOpen L s)).op
        (homToTwistedSection X L F G (n : ℤ) f) = 0 := by
  obtain ⟨be, hbe⟩ := exists_tensorBasisAt X L (sheafHomSpace X.toRingedSpace F G) s n
  obtain ⟨t, ht⟩ := be.surjective
    (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.map
        (terminal.from (nonvanishingOpen L s)).op (homToTwistedSection X L F G (n : ℤ) f))
  have hdiv := ht.symm.trans (hbe t)
  have ht0 : t = 0 :=
    congrArg (fun z : F.over (nonvanishingOpen L s) ⟶ G.over (nonvanishingOpen L s) => z.val)
      ((homLocalizationMap_fraction X L F G s n f t hdiv).symm.trans
        ((congrArg (homLocalizationMap X L F G s)
          (homFractionClass_eq_homFraction X L F G s n f)).trans hf))
  refine hdiv.trans ?_
  rw [ht0]
  exact (congrArg ((TensorSheafification.toSheafify (sectionSiteRing X) (sectionSiteSheaf X)
    ((PresheafOfModules.tensorObj (O := (sectionSiteRing X)) ((sheafHomSpace X.toRingedSpace F G).val) ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
        (n : ℤ)).val)))).app (op (nonvanishingOpen L s))).hom
    (TensorProduct.zero_tmul _ _)).trans (map_zero _)

/- The `Module.compHom` action under which `homAtNonvanishingOpen` is a submodule is kept out of
instance search by Mathlib, so it has to be made available again for that submodule's additive
structure to be found; it must be the very instance used when Tag 0B5M was stated. -/
attribute [local instance] gradedHomAwayModule

/-- A degree-zero fraction `f / sⁿ` sent to the zero morphism on `X_s` is itself zero, provided
the twisted section attached to `f` is locally annihilated by powers of local equations
for `s`. -/
private theorem homFraction_eq_zero_of_map_eq_zero [CompactSpace X] (s : L.sections) (n : ℕ)
    (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)))))
    (hloc : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.map
          (terminal.from (nonvanishingOpen L s)).op
          (homToTwistedSection X L F G (n : ℤ) f) = 0 →
      IsLocallyKilledByPowers X L F G s n (homToTwistedSection X L F G (n : ℤ) f))
    (hfrac : homLocalizationMap X L F G s (homFraction X L F G s n f) = 0) :
    homFraction X L F G s n f = 0 := by
  have hv := homToTwistedSection_restrict_eq_zero X L F G s n f hfrac
  have hl := hloc hv
  have hgot := exists_pow_smul_eq_zero_of_locally X L F G s n f hl
  obtain ⟨e, he⟩ := hgot
  exact (homFraction_eq_zero_iff X L F G s n f).mpr ⟨e, he⟩

/-- **Injectivity of the Tag 0B5M comparison map, granted the local annihilation step.** On a
quasi-compact scheme, the map `(⨁_n Hom(ℱ, 𝒢 ⊗ L^{⊗ n}))_{(s)} ⟶ Hom_{𝒪_{X_s}}(ℱ|_{X_s},
𝒢|_{X_s})` is injective as soon as a twisted section of `ℋom(ℱ, 𝒢) ⊗ L^{⊗ n}` vanishing on `X_s`
is annihilated near every point by a power of a local equation for `s`. -/
theorem homLocalizationMap_injective_of_locally [CompactSpace X] (s : L.sections)
    (hloc : ∀ (n : ℕ) (f : F ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (G)).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))),
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj ((sheafHomSpace X.toRingedSpace F G))).obj ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))))).val.map
          (terminal.from (nonvanishingOpen L s)).op
          (homToTwistedSection X L F G (n : ℤ) f) = 0 →
      IsLocallyKilledByPowers X L F G s n (homToTwistedSection X L F G (n : ℤ) f)) :
    Function.Injective (homLocalizationMap X L F G s) := by
  intro a b hab
  have hsub : homLocalizationMap X L F G s (a - b) = 0 :=
    ((homLocalizationMap X L F G s).map_sub a b).trans (sub_eq_zero.mpr hab)
  have hex : ∃ d : HomFractionData X L F G, homFraction X L F G s d.1 d.2 = a - b :=
    homFraction_surjective X L F G s (a - b)
  obtain ⟨d, hf⟩ := hex
  refine sub_eq_zero.mp (hf.symm.trans ?_)
  exact homFraction_eq_zero_of_map_eq_zero X L F G s d.1 d.2 (hloc d.1 d.2)
    ((congrArg (homLocalizationMap X L F G s) hf).trans hsub)

end GradedHomInjectivity

section Tag01XQ

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

/-- **[Stacks, Tag 01XQ] part (1).** Let `X` be a quasi-compact scheme, let `L` be an invertible
`𝒪_X`-module, let `s` be a global section of `L` and let `ℱ`, `𝒢` be quasi-coherent
`𝒪_X`-modules with `ℱ` of finite type. The comparison map of Tag 0B5M
`(⨁_n Hom(ℱ, 𝒢 ⊗ L^{⊗ n}))_{(s)} ⟶ Hom_{𝒪_{X_s}}(ℱ|_{X_s}, 𝒢|_{X_s})` is injective. -/
@[stacks 01XQ "injective"]
theorem homLocalizationMap_injective (X : Scheme.{u}) [CompactSpace X]
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsFiniteType]
    (s : L.sections) :
    Function.Injective (homLocalizationMap X L F G s) :=
  homLocalizationMap_injective_of_locally X L F G s
    (fun n _f hv => exists_pow_smul_internalHomTwist_restrict_eq_zero X L F G s n _ hv)

end Tag01XQ

end Stacks.SheafOfModules

end
