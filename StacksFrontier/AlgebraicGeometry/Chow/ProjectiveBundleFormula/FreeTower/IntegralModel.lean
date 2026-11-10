module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.Hyperplane
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.UnitHom
import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange

/-!
# Projective space over the integers is a projective tower

`ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ] ⟶ Spec ℤ`, with its twisting sheaf `𝒪(1)`, is a projective tower of
fibre dimension `n` in the sense of `Stacks.Chow.IsProjectiveTower`, and so is `ℙⁿ_S ⟶ S`, with
the pullback of `𝒪(1)`, over every scheme `S`.

## Main results

* `Stacks.Chow.FreeTower.isProjectiveTower_projectiveSpaceAtUniverse`: the integral model.
* `Stacks.Chow.FreeTower.isProjectiveTower_projectiveSpaceOver`: `ℙⁿ_S ⟶ S` with the pullback
  of `𝒪(1)`.
* `Stacks.Chow.FreeTower.isAffineSpaceBundle_of_iso`: a morphism isomorphic over its target to
  the projection of affine space is an affine-space bundle.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ProjectiveSpaceModuli Stacks.ProjectiveFromSections
open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.Chow.FreeTower

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Affine-space bundles -/

/-- The projection of affine space is an affine-space bundle. -/
alias isAffineSpaceBundle_affineSpace := Stacks.Chow.isAffineSpaceBundle_affineSpaceOver

/-- **A morphism isomorphic over its target to the projection of affine space is an affine-space
bundle.** -/
theorem isAffineSpaceBundle_of_iso {Y T : Scheme.{u}} {f : Y ⟶ T} {r : ℕ}
    (e : Y ≅ 𝔸(ULift.{u} (Fin r); T)) (he : e.hom ≫ (𝔸(ULift.{u} (Fin r); T) ↘ T) = f) :
    IsAffineSpaceBundle f r :=
  IsAffineSpaceBundle.of_isPullback (g := 𝟙 T)
    (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
    (isAffineSpaceBundle_affineSpace T r)

/-! ### The integral model -/

attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable (n : ℕ)

/-- `ℙⁿ_ℤ` is integral. -/
instance isIntegral_projectiveSpaceAtUniverse : IsIntegral (projectiveSpaceAtUniverse.{u} n) :=
  Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj (ULift.{u} ℤ) n

/-- The coordinate sections of `𝒪(1)` on `ℙⁿ_ℤ` are nonzero. -/
theorem coordGlobalSection_ne_zero (i : Fin (n + 1)) : coordGlobalSection.{u} n i ≠ 0 :=
  Stacks.ProjectiveSpace.Cohomology.degreeSection_ne_zero (ULift.{u} ℤ) n 1
    ⟨MvPolynomial.X i, X_mem_coordGrading_one i⟩ (MvPolynomial.X_ne_zero i)

/-- `ℙⁿ` over the terminal scheme is the integral model. -/
def projectiveSpaceOverTerminalIso :
    projectiveSpaceOver n (⊤_ Scheme.{u}) ≅ projectiveSpaceAtUniverse.{u} n :=
  have : IsIso (terminal.from (⊤_ Scheme.{u})) :=
    isIso_of_isTerminal terminalIsTerminal terminalIsTerminal _
  asIso (pullback.snd (terminal.from (⊤_ Scheme.{u}))
    (terminal.from (projectiveSpaceAtUniverse.{u} n)))

/-- `ℙⁿ_ℤ ⟶ Spec ℤ` is locally of finite type. -/
instance locallyOfFiniteType_terminal_from :
    LocallyOfFiniteType (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse n

/-- `ℙⁿ_ℤ ⟶ Spec ℤ` is flat. -/
instance flat_terminal_from : Flat (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  flat_terminal_from_projectiveSpaceAtUniverse n

/-- `ℙⁿ_ℤ ⟶ Spec ℤ` is proper. -/
instance isProper_terminal_from : IsProper (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  have : IsProper (pullback.fst (terminal.from (⊤_ Scheme.{u}))
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) :=
    isProper_projectiveSpaceOver n _
  rw [show terminal.from (projectiveSpaceAtUniverse.{u} n) =
    (projectiveSpaceOverTerminalIso n).inv ≫ pullback.fst (terminal.from (⊤_ Scheme.{u}))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) from terminal.hom_ext _ _]
  infer_instance

/-- `ℙⁿ_ℤ ⟶ Spec ℤ` has relative dimension `n`. -/
theorem relativeDimension_terminal_from :
    RelativeDimension (terminal.from (projectiveSpaceAtUniverse.{u} n)) n :=
  have : LocallyOfFiniteType (pullback.fst (terminal.from (⊤_ Scheme.{u}))
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) :=
    locallyOfFiniteType_projectiveSpaceOver n _
  relativeDimension_of_iso_over (projectiveSpaceOverTerminalIso n).symm
    (pullback.fst (terminal.from (⊤_ Scheme.{u}))
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) _ (terminal.hom_ext _ _)
    (relativeDimension_projectiveSpaceOver n _)

/-- The nonvanishing locus of `Tᵢ` is the standard chart `D₊(Tᵢ)`. -/
theorem mem_nonvanishingLocus_coordGlobalSection_iff (i : Fin (n + 1))
    (x : projectiveSpaceAtUniverse.{u} n) :
    x ∈ Stacks.Ample.nonvanishingLocus (twistingSheafAtUniverse.{u} n)
        (coordGlobalSection.{u} n i) ↔
      x ∈ Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) :=
  Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    (coordGrading.{u} n) 1 1 ⟨MvPolynomial.X i, X_mem_coordGrading_one i⟩
    (by rw [whereInvertible_coordGrading_eq_top]; trivial)

/-- `𝒪(1)` on `ℙ⁰_ℤ` is trivial. -/
theorem nonempty_twistingSheafAtUniverse_zero_iso :
    Nonempty (twistingSheafAtUniverse.{u} 0 ≅
      SheafOfModules.unit (projectiveSpaceAtUniverse.{u} 0).ringCatSheaf) := by
  set X := projectiveSpaceAtUniverse.{u} 0
  set L := twistingSheafAtUniverse.{u} 0
  let s : L.sections := (Stacks.NonvanishingSpelling.sectionsEquiv X L).symm
    (coordGlobalSection.{u} 0 0)
  have hs : Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s = Set.univ := by
    rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq]
    refine Set.eq_univ_of_forall fun x => (mem_nonvanishingLocus_coordGlobalSection_iff 0 0 x).2 ?_
    have hint : ⨆ i : Fin 1,
        AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} 0) (MvPolynomial.X i) = ⊤ :=
      AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ _
        (AlgebraicGeometry.projectiveSpaceOver.irrelevant_coordGrading_le_span_X 0)
    rw [iSup_unique] at hint
    rw [show (0 : Fin 1) = default from rfl, hint]
    trivial
  have := isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ L s hs
  exact ⟨(asIso (L.unitHomEquiv.symm s)).symm⟩

/-- The hyperplane `V(T₀)` of `ℙ^{n+1}_ℤ` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_hyperplaneIdeal :
    Stacks.Divisors.IsEffectiveCartierDivisor (hyperplaneIdeal.{u} n) := by
  set X := projectiveSpaceAtUniverse.{u} (n + 1)
  set L := twistingSheafAtUniverse.{u} (n + 1)
  let s : L.sections := (Stacks.NonvanishingSpelling.sectionsEquiv X L).symm
    (coordGlobalSection.{u} (n + 1) 0)
  have hs : s.eval (Opposite.op ⊤) = coordGlobalSection.{u} (n + 1) 0 :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X L).apply_symm_apply _
  have h := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).2
    (AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero L s
      (hs ▸ coordGlobalSection_ne_zero (n + 1) 0))
  rwa [hs] at h

/-- The standard chart `D₊(T₀)` of `ℙ^{n+1}_ℤ`. -/
abbrev chartZero : (projectiveSpaceAtUniverse.{u} (n + 1)).Opens :=
  Proj.basicOpen (coordGrading.{u} (n + 1)) (MvPolynomial.X 0)

/-- The complement of `V(T₀)` in `ℙ^{n+1}_ℤ` is the standard chart `D₊(T₀)`. -/
theorem coe_chartZero_eq_compl_support :
    (chartZero.{u} n : Set (projectiveSpaceAtUniverse.{u} (n + 1))) =
      ((hyperplaneIdeal.{u} n).support : Set (projectiveSpaceAtUniverse.{u} (n + 1)))ᶜ := by
  set X := projectiveSpaceAtUniverse.{u} (n + 1)
  set L := twistingSheafAtUniverse.{u} (n + 1)
  let s : L.sections := (Stacks.NonvanishingSpelling.sectionsEquiv X L).symm
    (coordGlobalSection.{u} (n + 1) 0)
  have hs : s.eval (Opposite.op ⊤) = coordGlobalSection.{u} (n + 1) 0 :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X L).apply_symm_apply _
  have h := nonvanishingLocus_eq_compl_supportSet_zeroScheme L s
    (hs ▸ coordGlobalSection_ne_zero (n + 1) 0)
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq, hs] at h
  change _ = (zeroScheme (projectiveSpaceAtUniverse (n + 1)) L
    (coordGlobalSection (n + 1) 0)).supportSetᶜ
  rw [← h]
  ext x
  exact (mem_nonvanishingLocus_coordGlobalSection_iff (n + 1) 0 x).symm

/-- The standard chart `D₊(T₀)` of `ℙ^{n+1}_ℤ` is affine `(n+1)`-space. -/
def chartZeroIsoAffineSpace : (chartZero.{u} n).toScheme ≅
      𝔸(ULift.{u} (Fin (n + 1)); ⊤_ Scheme.{u}) :=
  have : IsIso (terminal.from (⊤_ Scheme.{u})) :=
    isIso_of_isTerminal terminalIsTerminal terminalIsTerminal _
  (projectiveSpaceOver.chartIsoBasicOpen (n + 1) 0
      (Equiv.ulift.trans (finSuccAboveEquiv 0))).symm ≪≫
    (asIso (pullback.snd (terminal.from (⊤_ Scheme.{u}))
      (terminal.from (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin (n + 1)))
        (ULift.{u} ℤ))))))).symm

/-- **Projective space over the integers is a projective tower**: `ℙⁿ_ℤ ⟶ Spec ℤ` with `𝒪(1)`
is a projective tower of fibre dimension `n`. -/
theorem isProjectiveTower_projectiveSpaceAtUniverse : ∀ n : ℕ,
    IsProjectiveTower n (terminal.from (projectiveSpaceAtUniverse.{u} n))
      (twistingSheafAtUniverse.{u} n)
  | 0 => by
    have := Stacks.DeRham.isIso_terminalFrom_projectiveSpaceAtUniverse_of_zero.{u}
    exact .zero _ _ inferInstance nonempty_twistingSheafAtUniverse_zero_iso
  | n + 1 => by
    have ih := isProjectiveTower_projectiveSpaceAtUniverse n
    set e := hyperplaneZeroSchemeIso.{u} n
    have he : e.hom ≫ terminal.from (projectiveSpaceAtUniverse.{u} n) =
        (hyperplaneIdeal.{u} n).subschemeι ≫
          terminal.from (projectiveSpaceAtUniverse.{u} (n + 1)) := terminal.hom_ext _ _
    have : LocallyOfFiniteType ((hyperplaneIdeal.{u} n).subschemeι ≫
        terminal.from (projectiveSpaceAtUniverse.{u} (n + 1))) := he ▸ inferInstance
    have hflat : Flat ((hyperplaneIdeal.{u} n).subschemeι ≫
        terminal.from (projectiveSpaceAtUniverse.{u} (n + 1))) := he ▸ inferInstance
    refine IsProjectiveTower.succ_of_eq n _ _ (relativeDimension_terminal_from (n + 1))
      (coordGlobalSection.{u} (n + 1) 0) (hyperplaneIdeal.{u} n) rfl
      ⟨isEffectiveCartierDivisor_hyperplaneIdeal n, hflat⟩
      (relativeDimension_of_iso_over e _ _ he (relativeDimension_terminal_from n))
      (IsProjectiveTower.of_iso_left e he (exists_pullback_subschemeι_iso n).choose ih)
      _ (coe_chartZero_eq_compl_support n)
      (isAffineSpaceBundle_of_iso (chartZeroIsoAffineSpace n) (terminal.hom_ext _ _))

/-- **Projective space over a scheme is a projective tower**: `ℙⁿ_S ⟶ S` with the pullback of
`𝒪(1)` from the integral model is a projective tower of fibre dimension `n`. -/
theorem isProjectiveTower_projectiveSpaceOver (S : Scheme.{u}) :
    IsProjectiveTower n (pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      ((Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
        (twistingSheafAtUniverse.{u} n)) :=
  (isProjectiveTower_projectiveSpaceAtUniverse n).of_isPullback
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip (Iso.refl _)

end Stacks.Chow.FreeTower

end
