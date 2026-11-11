module

public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree-zero localization of the section ring at a section of an invertible module

Let `X` be a scheme, let `L` be an invertible `𝒪_X`-module and let `s` be a global section of
`L` with nonvanishing open `X_s`. The last assertion of
[Stacks, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW) is that the canonical ring map

`Γ_*(X, L)_{(s)} ⟶ Γ(X_s, 𝒪_X)`,   `a / sⁿ ↦ a ⊗ s^{-n}`,

out of the degree-zero homogeneous localization of the section ring
`Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` is an isomorphism when `X` is quasi-compact and
quasi-separated. This file proves it, and states the whole of Tag 01PW as one theorem.

## Main results

* `Stacks.SheafOfModules.sectionRingLocalizationMap_injective`: the ring map is injective for
  `X` quasi-compact.
* `Stacks.SheafOfModules.sectionRingLocalizationMap_bijective`: **the ring map is bijective for
  `X` quasi-compact and quasi-separated**, the last assertion of Tag 01PW.
* `Stacks.SheafOfModules.sectionRingLocalizationEquiv`: the same, as a ring isomorphism.
* `Stacks.SheafOfModules.sectionLocalizationMap_injective_and_bijective`: **[Stacks, Tag 01PW]**,
  parts (1) and (2) and the ring isomorphism together.

## Implementation notes

The source reads the ring statement off part (2) for `ℱ = 𝒪_X`, and so does the proof here. The
ring map is `Stacks.SheafOfModules.sectionRingLocalizationMap`, and the Tag 0B5L map of `𝒪_X` is
linear over it (`Stacks.SheafOfModules.sectionLocalizationMap_fractionAction`). Write `1 ⊗ s⁰` for
the degree-zero fraction of twisted sections of `𝒪_X` whose numerator is the unit section tensored
with `s⁰`; it goes to `1` on `X_s`, so the ring map is the composite of `a ↦ a • (1 ⊗ s⁰)` with
the Tag 0B5L map of `𝒪_X`. The second map is bijective by part (2). The first is bijective
because a homogeneous `b ∈ Γ(X, L^{⊗ n})` acts on `1 ⊗ s⁰` as the twisted section `1 ⊗ b`
(`Stacks.SheafOfModules.of_smul_of_tensorSectionAtOpen_sectionPower_zero`), and `b ↦ 1 ⊗ b` is
inverse to the left unit constraint `𝒪_X ⊗ L^{⊗ n} ≅ L^{⊗ n}` on global sections
(`Stacks.SheafOfModules.tensorSections_leftUnitorAt`). Injectivity only needs part (1).

The action `a ↦ a • ((1 ⊗ s⁰) / s⁰)` is always spelled through
`Stacks.SheafOfModules.fractionAction`, whose scalar action is elaborated once, in the module of
the Tag 0B5L map: elaborating the action here, at the structure sheaf rather than at a variable
module, exceeds the heartbeat budget of the statements that mention it.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite DirectSum Limits

universe u

section SectionRingLocalization

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv
  Stacks.SchemeModulesSpelling.sectionRingGradedRing
  Stacks.SchemeModulesSpelling.sectionRingGradingGradedRing
  Stacks.SchemeModulesSpelling.sectionModuleModule
  Stacks.SheafOfModules.sectionModuleDecompositionLoc
  Stacks.SheafOfModules.sectionModuleGradedSMulLoc

/-- The structure sheaf `𝒪_X`, as a module over itself. -/
local notation "𝒪ₘ" => _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)

attribute [local instance] Stacks.SheafOfModules.sectionAwayModuleLoc in
/-- The degree-zero fraction `(1 ⊗ s⁰) / s⁰` of twisted sections of `𝒪_X` is a degree-zero
fraction. -/
private theorem mk_unitSection_mem (s : L.sections) :
    LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
        (DirectSum.of _ ((0 : ℕ) : ℤ)
          (tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) 0
            (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
            (sectionPower X L s 0)) :
          sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ)
        ⟨homogeneousSection X L s ^ 0, ⟨0, rfl⟩⟩ ∈
      sectionAtNonvanishingOpen X L 𝒪ₘ s := by
  have h0 : (0 : ℕ) • ((1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) := by simp
  refine Submodule.subset_span ⟨1, 0, homogeneousSection_mem X L s, _, ?_, rfl⟩
  rw [h0]
  exact ⟨_, rfl⟩

/-- The degree-zero fraction `(1 ⊗ s⁰) / s⁰` of twisted sections of `𝒪_X`. -/
private def unitFraction (s : L.sections) : sectionAtNonvanishingOpen X L 𝒪ₘ s :=
  ⟨_, mk_unitSection_mem X L s⟩

/-- The Tag 0B5L map of `𝒪_X` sends `(1 ⊗ s⁰) / s⁰` to the unit function on `X_s`. -/
private theorem sectionLocalizationMap_unitFraction (s : L.sections) :
    sectionLocalizationMap X L 𝒪ₘ s (unitFraction X L s) =
      (1 : (sectionSiteRing X).obj (op (nonvanishingOpen L s))) := by
  refine sectionLocalizationMap_fraction X L 𝒪ₘ s 0
    (tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) 0
      (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
      (sectionPower X L s 0))
    (unitFraction X L s) (1 : (sectionSiteRing X).obj (op (nonvanishingOpen L s))) rfl ?_
  refine (tensorSections_naturalAt (sectionSiteRing X) (sectionSiteSheaf X) 𝒪ₘ
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L ((0 : ℕ) : ℤ))
    (terminal.from (nonvanishingOpen L s)).op
    (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (sectionPower X L s 0)).trans ?_
  have h1 : ((sectionSiteRing X).map (terminal.from (nonvanishingOpen L s)).op).hom 1 = 1 :=
    map_one _
  exact congrArg (fun r => tensorSectionAtOpen X L 𝒪ₘ (nonvanishingOpen L s) 0 r
    ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      ((0 : ℕ) : ℤ)).val.map (terminal.from (nonvanishingOpen L s)).op
      (sectionPower X L s 0))) h1

/-- The ring map of Tag 01PW is the Tag 0B5L map of `𝒪_X` applied to `a • ((1 ⊗ s⁰) / s⁰)`. -/
private theorem sectionRingLocalizationMap_eq (s : L.sections)
    (a : HomogeneousLocalization.Away
      (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s)) :
    sectionRingLocalizationMap X L s a =
      sectionLocalizationMap X L 𝒪ₘ s (fractionAction X L 𝒪ₘ s (unitFraction X L s) a) := by
  rw [sectionLocalizationMap_fractionAction, sectionLocalizationMap_unitFraction]
  exact (mul_one _).symm

/-- The action of a fraction `x / sⁿ` on `(1 ⊗ s⁰) / s⁰`, in the localized module. -/
private theorem val_mk_smul_unitFraction (s : L.sections) (n : ℕ)
    (x : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
    (hx : x ∈ sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L (n • 1)) :
    ((fractionAction X L 𝒪ₘ s (unitFraction X L s)
        (HomogeneousLocalization.Away.mk _ (homogeneousSection_mem X L s) n x hx) :
        sectionAtNonvanishingOpen X L 𝒪ₘ s) :
        LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
          (homogeneousSection X L s)
          (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
        (x • (DirectSum.of _ ((0 : ℕ) : ℤ)
          (tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) 0
            (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
            (sectionPower X L s 0)) :
          sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ))
        (⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩ * ⟨homogeneousSection X L s ^ 0, ⟨0, rfl⟩⟩) :=
  (fractionAction_val X L 𝒪ₘ s (unitFraction X L s) _).trans (LocalizedModule.mk_smul_mk _ _ _ _)

/-- **The left unit constraint inverts `b ↦ 1 ⊗ b` on global sections.** -/
private theorem tensorSectionAtOpen_one_injective (n : ℕ)
    {b c : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))}
    (h : tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) n
        (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) b =
      tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) n
        (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) c) :
    b = c := by
  let E := Invertible.tensorProductLeftUnitor (sectionSiteRing X) (sectionSiteSheaf X)
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
  have hb := tensorSections_leftUnitorAt (sectionSiteRing X) (sectionSiteSheaf X)
    (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) b
  have hc := tensorSections_leftUnitorAt (sectionSiteRing X) (sectionSiteSheaf X)
    (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) c
  exact hb.symm.trans ((congrArg (fun y =>
    (E.hom.val.app (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))).hom y) h).trans hc)

/-- **The left unit constraint kills `b` once `1 ⊗ b` vanishes.** -/
private theorem eq_zero_of_tensorSectionAtOpen_one_eq_zero (n : ℕ)
    {b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))}
    (h : tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) n
        (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) b = 0) :
    b = 0 := by
  let E := Invertible.tensorProductLeftUnitor (sectionSiteRing X) (sectionSiteSheaf X)
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
  have hb := tensorSections_leftUnitorAt (sectionSiteRing X) (sectionSiteSheaf X)
    (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ)) b
  exact hb.symm.trans ((congrArg (fun y =>
    (E.hom.val.app (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))).hom y) h).trans
      (map_zero _))

/-- **Every twisted global section of `𝒪_X ⊗ L^{⊗ n}` is `1 ⊗ b`.** -/
private theorem exists_tensorSectionAtOpen_one_eq (n : ℕ)
    (m : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj 𝒪ₘ).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    ∃ b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
        (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))),
      tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) n
        (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) b =
        m := by
  let E := Invertible.tensorProductLeftUnitor (sectionSiteRing X) (sectionSiteSheaf X)
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
  let V := op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))
  have hiso : IsIso (E.hom.val.app V) :=
    ((PresheafOfModules.evaluation _ V).mapIso
      ((_root_.SheafOfModules.forget _).mapIso E)).isIso_hom
  refine ⟨(E.hom.val.app V).hom m,
    (ConcreteCategory.bijective_of_isIso (E.hom.val.app V)).injective ?_⟩
  exact tensorSections_leftUnitorAt (sectionSiteRing X) (sectionSiteSheaf X) V
    (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
    ((E.hom.val.app V).hom m)

/-- **A homogeneous section acting trivially on `1 ⊗ s⁰` is zero.** -/
private theorem eq_zero_of_of_smul_eq_zero (s : L.sections) (k : ℕ)
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (k : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (h : (DirectSum.of _ k b : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) •
      (DirectSum.of _ ((0 : ℕ) : ℤ)
        (tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) 0
          (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
          (sectionPower X L s 0)) :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ) = 0) :
    (DirectSum.of _ k b : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) = 0 := by
  rw [of_smul_of_tensorSectionAtOpen_sectionPower_zero X L 𝒪ₘ s k b
    (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))] at h
  have ht := DirectSum.of_injective (k : ℤ)
    (h.trans (map_zero (DirectSum.of _ (k : ℤ))).symm)
  rw [eq_zero_of_tensorSectionAtOpen_one_eq_zero X L k ht, map_zero]

/-- **A fraction `x / sⁿ` killing `(1 ⊗ s⁰) / s⁰` has numerator killed by a power of `s`.** -/
private theorem exists_pow_smul_eq_zero_of_smul_unitFraction_eq_zero (s : L.sections) (n : ℕ)
    (x : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
    (hx : x ∈ sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L (n • 1))
    (h : fractionAction X L 𝒪ₘ s (unitFraction X L s)
      (HomogeneousLocalization.Away.mk _ (homogeneousSection_mem X L s) n x hx) = 0) :
    ∃ e : ℕ, (homogeneousSection X L s ^ e * x) •
      (DirectSum.of _ ((0 : ℕ) : ℤ)
        (tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) 0
          (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
          (sectionPower X L s 0)) :
        sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ) = 0 := by
  have hv := (val_mk_smul_unitFraction X L s n x hx).symm.trans (congrArg Subtype.val h)
  obtain ⟨e, he⟩ := (localizedModule_mk_eq_zero_iff (homogeneousSection X L s) _ _).mp hv
  exact ⟨e, (smul_smul _ _ _).symm.trans he⟩

/-- A homogeneous element of degree `n` of the section ring, as a numerator over `sⁿ`. -/
private theorem of_mem_sectionRingGrading_nsmul (n : ℕ)
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (DirectSum.of _ n b : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) ∈
      sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L (n • 1) := by
  have hbmem : (DirectSum.of _ n b : sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) ∈
      sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L n := ⟨b, rfl⟩
  simpa using hbmem

/-- A fraction `x / sⁿ` of a graded ring vanishes once some power of `s` kills `x`. -/
private theorem away_mk_eq_zero_of_pow_mul_eq_zero {R σ : Type*} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : R} (hf : f ∈ 𝒜 1) (n e : ℕ) (x : R)
    (hx : x ∈ 𝒜 (n • 1)) (h : f ^ e * x = 0) :
    HomogeneousLocalization.Away.mk 𝒜 hf n x hx = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨_, ⟨e, rfl⟩⟩, h⟩

/-- **The action of a homogeneous fraction on `(1 ⊗ s⁰) / s⁰` is injective.** -/
private theorem eq_zero_of_mk_of_smul_unitFraction_eq_zero (s : L.sections) (n : ℕ)
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (h : fractionAction X L 𝒪ₘ s (unitFraction X L s) (HomogeneousLocalization.Away.mk _
        (homogeneousSection_mem X L s) n _ (of_mem_sectionRingGrading_nsmul X L n b)) = 0) :
    HomogeneousLocalization.Away.mk _ (homogeneousSection_mem X L s) n _
      (of_mem_sectionRingGrading_nsmul X L n b) = 0 := by
  obtain ⟨e, he⟩ := exists_pow_smul_eq_zero_of_smul_unitFraction_eq_zero X L s n _ _ h
  have hfx := sectionRing_of_mul_of X L e n (sectionPower X L s e) b
  rw [← homogeneousSection_pow_eq_of_sectionPower] at hfx
  rw [hfx] at he
  exact away_mk_eq_zero_of_pow_mul_eq_zero _ _ n e _ _
    (hfx.trans (eq_zero_of_of_smul_eq_zero X L s (e + n) _ he))

/-- **The action on `(1 ⊗ s⁰) / s⁰` is injective.** -/
private theorem eq_zero_of_smul_unitFraction_eq_zero (s : L.sections)
    (a : HomogeneousLocalization.Away
      (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s))
    (h : fractionAction X L 𝒪ₘ s (unitFraction X L s) a = 0) : a = 0 := by
  obtain ⟨n, x, hx, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (homogeneousSection_mem X L s) a
  have hx' : x ∈ sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L n := by
    simpa using hx
  obtain ⟨b, rfl⟩ : ∃ b, (DirectSum.of _ n b :
      sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L) = x := hx'
  exact eq_zero_of_mk_of_smul_unitFraction_eq_zero X L s n b h

/-- **The fraction `b / sⁿ` acts on `(1 ⊗ s⁰) / s⁰` as the fraction `(1 ⊗ b) / sⁿ`.** -/
private theorem val_mk_of_smul_unitFraction (s : L.sections) (n : ℕ)
    (b : (TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L
      (n : ℤ)).val.obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (m : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj 𝒪ₘ).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (hb : tensorSectionAtOpen X L 𝒪ₘ (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)) n
      (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) b = m) :
    ((fractionAction X L 𝒪ₘ s (unitFraction X L s) (HomogeneousLocalization.Away.mk _
        (homogeneousSection_mem X L s) n _ (of_mem_sectionRingGrading_nsmul X L n b)) :
        sectionAtNonvanishingOpen X L 𝒪ₘ s) :
        LocalizedModule.Away (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
          (homogeneousSection X L s)
          (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
        (DirectSum.of _ (n : ℤ) m : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ)
        ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩ := by
  refine (val_mk_smul_unitFraction X L s n _ _).trans (congrArg₂ LocalizedModule.mk
    ((of_smul_of_tensorSectionAtOpen_sectionPower_zero X L 𝒪ₘ s n b
      (1 : (sectionSiteRing X).obj (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))).trans
      (congrArg (DirectSum.of _ (n : ℤ)) hb)) ?_)
  exact Subtype.ext (by simp)

/-- **A degree-zero fraction `m / sⁿ` of twisted sections of `𝒪_X` is
`a • ((1 ⊗ s⁰) / s⁰)`.** -/
private theorem exists_smul_unitFraction_eq_of_numerator (s : L.sections) (n : ℕ)
    (m : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sectionSiteRing X),
      Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X)) (forget₂ CommRingCat RingCat)
      ((sectionSiteSheaf X))⟩).obj 𝒪ₘ).obj ((TensorPower.tensorPower (sectionSiteRing X)
      (sectionSiteSheaf X) L (n : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace))))
    (w : sectionAtNonvanishingOpen X L 𝒪ₘ s)
    (hw : (w : LocalizedModule.Away
        (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s)
        (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
        (DirectSum.of _ (n : ℤ) m : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L 𝒪ₘ)
        ⟨homogeneousSection X L s ^ n, ⟨n, rfl⟩⟩) :
    ∃ a : HomogeneousLocalization.Away
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s),
      fractionAction X L 𝒪ₘ s (unitFraction X L s) a = w := by
  exact ⟨_, Subtype.ext ((val_mk_of_smul_unitFraction X L s n _ m
    (exists_tensorSectionAtOpen_one_eq X L n m).choose_spec).trans hw.symm)⟩

/-- **Every degree-zero fraction of twisted sections of `𝒪_X` is `a • ((1 ⊗ s⁰) / s⁰)`.** -/
private theorem exists_smul_unitFraction_eq (s : L.sections)
    (w : sectionAtNonvanishingOpen X L 𝒪ₘ s) :
    ∃ a : HomogeneousLocalization.Away
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s),
      fractionAction X L 𝒪ₘ s (unitFraction X L s) a = w := by
  have hnum := exists_twistedSection_numerator X L 𝒪ₘ s w
  obtain ⟨n, x, ⟨m, rfl⟩, hw⟩ := hnum
  exact exists_smul_unitFraction_eq_of_numerator X L s n m w hw

/-- **The ring map of Tag 01PW is injective on a quasi-compact scheme.** -/
theorem sectionRingLocalizationMap_injective [CompactSpace X] (s : L.sections) :
    Function.Injective (sectionRingLocalizationMap X L s) := by
  have : _root_.SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒪ₘ :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
  have hz : fractionAction X L 𝒪ₘ s (unitFraction X L s) a =
      fractionAction X L 𝒪ₘ s (unitFraction X L s) 0 :=
    sectionLocalizationMap_injective X L 𝒪ₘ s ((sectionRingLocalizationMap_eq X L s a).symm.trans
      (ha.trans ((map_zero (sectionRingLocalizationMap X L s)).symm.trans
        (sectionRingLocalizationMap_eq X L s 0))))
  exact eq_zero_of_smul_unitFraction_eq_zero X L s a
    (hz.trans (AddMonoidHom.map_zero (fractionAction X L 𝒪ₘ s (unitFraction X L s))))

/-- **[Stacks, Tag 01PW], the ring isomorphism.** Let `X` be a quasi-compact and quasi-separated
scheme, let `L` be an invertible `𝒪_X`-module and let `s` be a global section of `L`. The
canonical ring map `Γ_*(X, L)_{(s)} ⟶ Γ(X_s, 𝒪_X)`, `a / sⁿ ↦ a ⊗ s^{-n}`, is bijective. -/
@[stacks 01PW "the ring isomorphism"]
theorem sectionRingLocalizationMap_bijective [CompactSpace X] [QuasiSeparatedSpace X]
    (s : L.sections) : Function.Bijective (sectionRingLocalizationMap X L s) := by
  refine ⟨sectionRingLocalizationMap_injective X L s, fun t => ?_⟩
  have : _root_.SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒪ₘ :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  obtain ⟨w, hw⟩ := (sectionLocalizationMap_bijective X L 𝒪ₘ s).2 t
  obtain ⟨a, ha⟩ := exists_smul_unitFraction_eq X L s w
  exact ⟨a, (sectionRingLocalizationMap_eq X L s a).trans ((congrArg _ ha).trans hw)⟩

/-- **The ring isomorphism `Γ_*(X, L)_{(s)} ≃ Γ(X_s, 𝒪_X)`** of [Stacks, Tag 01PW], for `X`
quasi-compact and quasi-separated. -/
def sectionRingLocalizationEquiv [CompactSpace X] [QuasiSeparatedSpace X] (s : L.sections) :
    HomogeneousLocalization.Away
        (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
        (homogeneousSection X L s) ≃+*
      (sectionSiteRing X).obj (op (nonvanishingOpen L s)) :=
  RingEquiv.ofBijective _ (sectionRingLocalizationMap_bijective X L s)

/-- **[Stacks, Tag 01PW].** Let `X` be a scheme, let `L` be an invertible `𝒪_X`-module and let
`s` be a global section of `L`. Suppose `X` is quasi-compact.

1. For every quasi-coherent `𝒪_X`-module `ℱ` the comparison map of Tag 0B5L
   `(⨁_n Γ(X, ℱ ⊗ L^{⊗ n}))_{(s)} ⟶ Γ(X_s, ℱ|_{X_s})` is injective.
2. If `X` is moreover quasi-separated, that map is bijective for every quasi-coherent `ℱ`, and
   the canonical ring map `Γ_*(X, L)_{(s)} ⟶ Γ(X_s, 𝒪_X)`, `a / sⁿ ↦ a ⊗ s^{-n}`, is
   bijective. -/
@[stacks 01PW]
theorem sectionLocalizationMap_injective_and_bijective [CompactSpace X] (s : L.sections) :
    (∀ (F : X.Modules) [F.IsQuasicoherent],
      Function.Injective (sectionLocalizationMap X L F s)) ∧
    (QuasiSeparatedSpace X →
      (∀ (F : X.Modules) [F.IsQuasicoherent],
        Function.Bijective (sectionLocalizationMap X L F s)) ∧
      Function.Bijective (sectionRingLocalizationMap X L s)) :=
  ⟨fun F _ => sectionLocalizationMap_injective X L F s,
    fun _ => ⟨fun F _ => sectionLocalizationMap_bijective X L F s,
      sectionRingLocalizationMap_bijective X L s⟩⟩

end SectionRingLocalization

end Stacks.SheafOfModules

end
