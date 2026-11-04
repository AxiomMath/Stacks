module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentIntersection
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularPointBlowupCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.RegularLocalBlowupTwists
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.GenericStalkRankOne
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.IdealSubobject
public import StacksFrontier.AlgebraicGeometry.TopDirectImageRightExact.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructureDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.StructureSheafMono
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
import all StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk

/-!
# Higher direct images along the contraction of an exceptional curve

Let `f : X ⟶ X'` be a contraction of an exceptional curve: the blowup of a closed point
`x ∈ X'` whose local ring is regular of dimension two. For an invertible `𝒪_{X'}`-module `ℒ`
the higher direct images of `f^*ℒ` vanish, `Rᵠf_*(f^*ℒ) = 0` for `q ≥ 1`. This is the
statement "`Rf_*f^*ℒ = ℒ` (details omitted)" used in [Stacks, Remark 0CA8], in the form in which
it is consumed there.

Away from `x` the contraction is an isomorphism, so an affine morphism. At `x` flat base change
along `Spec 𝒪_{X', x} ⟶ X'` ([Stacks, Tag 02KH]) identifies the stalk with the cohomology of the
pullback of `f^*ℒ` to the blowup of the regular local ring `𝒪_{X', x}` in its maximal ideal.
There the pullback is trivial, since `ℒ` is trivial near `x`, and that blowup has no higher
cohomology of its structure sheaf: `H¹ = 0` because the maximal ideal has two generators, and
`Hᵠ = 0` for `q ≥ 2` because the blowup is a closed subscheme of the projective line over
`𝒪_{X', x}` ([Stacks, Tag 0AGS]).

## Main results

* `AlgebraicGeometry.isZero_Hgroup_unit_blowUp_maximalIdeal`: `Hᵠ(Bl, 𝒪) = 0` for `q ≥ 1` on the
  blowup of a two-dimensional regular local ring in its maximal ideal.
* `AlgebraicGeometry.IsContractionOfExceptionalCurve.isZero_rightDerivedPlus_pushforward_of_iso`:
  `Rᵠf_*ℱ = 0` for `q ≥ 1` and `ℱ ≅ f^*ℒ` with `ℒ` invertible.

## References

* [Stacks Project, Remark 0CA8](https://stacks.math.columbia.edu/tag/0CA8)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **`Hᵠ(Bl, 𝒪) = 0` for `q ≥ 1`** on the blowup of a regular local ring of dimension two in its
maximal ideal. In degree one this is `AlgebraicGeometry.isZero_Hgroup_one_blowUp_maximalIdeal`;
in degrees at least two the maximal ideal has two generators, and the `Proj` of the Rees algebra
of a two-generated ideal has no quasi-coherent cohomology above degree one. -/
theorem isZero_Hgroup_unit_blowUp_maximalIdeal (B : Type u) [CommRing B] [IsRegularLocalRing B]
    (hdim : ringKrullDim B = 2) (q : ℕ) (hq : 1 ≤ q) :
    IsZero (Hgroup (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
          (IsLocalRing.maximalIdeal B)))).ringCatSheaf ⊤ q
      (SheafOfModules.unit (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
          (IsLocalRing.maximalIdeal B)))).ringCatSheaf)) := by
  obtain rfl | hq2 : q = 1 ∨ 2 ≤ q := by omega
  · exact isZero_Hgroup_one_blowUp_maximalIdeal B hdim
  obtain ⟨x, hx⟩ := Stacks.Blowup.exists_range_eq_maximalIdeal B hdim
  obtain ⟨e⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase (R := B)
    (K := IsLocalRing.maximalIdeal B)
  have hei : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let e' : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading (IsLocalRing.maximalIdeal B)) ≅
      blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (IsLocalRing.maximalIdeal B))) :=
    @asIso _ _ _ _ e.hom.left hei
  have hqc : (SheafOfModules.unit (Stacks.Blowup.blowUpSpec
      (IsLocalRing.maximalIdeal B)).ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  have h := Stacks.Blowup.isZero_hgroup_of_two_le_of_two_generators x
    (fun j => by rw [hx]; exact Ideal.subset_span ⟨j, rfl⟩) hx
    (SheafOfModules.unit (Stacks.Blowup.blowUpSpec (IsLocalRing.maximalIdeal B)).ringCatSheaf)
    q hq2
  refine (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e' _ q).mp (h.of_iso ?_)
  exact (Hfunctor (AlgebraicGeometry.Proj
    (Stacks.Blowup.reesGrading (IsLocalRing.maximalIdeal B))).ringCatSheaf ⊤ q).mapIso
      (Scheme.Modules.pullbackUnitIso e'.hom)

/-- **The higher direct images of a pulled back invertible module along a contraction vanish.**
Let `f : X ⟶ X'` contract an exceptional curve, `ℒ` an invertible `𝒪_{X'}`-module and
`ℱ ≅ f^*ℒ`. Then `Rᵠf_*ℱ = 0` for every `q ≥ 1`. -/
theorem IsContractionOfExceptionalCurve.isZero_rightDerivedPlus_pushforward_of_iso
    {X X' : Scheme.{u}} {E : X.IdealSheafData} {f : X ⟶ X'}
    (hf : IsContractionOfExceptionalCurve E f) (L : X'.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property L)
    (F : X.Modules) [F.IsQuasicoherent] (eF : F ≅ (Scheme.Modules.pullback f).obj L)
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F) := by
  have : IsProper f := hf.isProper
  obtain ⟨hX', z, hz, hreg, hdim, -, e, he⟩ := hf
  have := hX'
  have := hreg
  generalize hM : Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X') = M at e he
  have hqc : (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F).IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus f F inferInstance q
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ (fun y => ?_)
  by_cases hy : y = z
  · subst hy
    let b := X'.fromSpecStalk y
    have : Flat b := flat_fromSpecStalk X' y
    obtain ⟨h, hpb⟩ := exists_isPullback_blowUpToBase_comap b M
    set p := blowUpToBase (M.comap b)
    have hpb' : IsPullback p (h ≫ e.inv) b f :=
      IsPullback.of_iso hpb (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (by simp)
        (by simp) (by simp) (by simp [← he])
    -- the cohomology of the structure sheaf of the local blowup vanishes
    have hloc : IsZero (Hgroup (blowUp (M.comap b)).ringCatSheaf ⊤ q
        (SheafOfModules.unit (blowUp (M.comap b)).ringCatSheaf)) := by
      rw [← hM, vanishingIdeal_singleton_comap_fromSpecStalk_eq y hz]
      exact isZero_Hgroup_unit_blowUp_maximalIdeal _ hdim q hq
    -- the pullback of `F` to the local blowup is trivial
    obtain ⟨eb⟩ := nonempty_pullback_fromSpecStalk_iso_unit L
      ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff L 1).mpr
        ((Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one X' L).mp hL))
      y
    obtain ⟨eh⟩ : Nonempty ((Scheme.Modules.pullback (h ≫ e.inv)).obj F ≅
        SheafOfModules.unit (blowUp (M.comap b)).ringCatSheaf) :=
      ⟨(Scheme.Modules.pullback (h ≫ e.inv)).mapIso eF ≪≫
        (Scheme.Modules.pullbackComp (h ≫ e.inv) f).app L ≪≫
        (Scheme.Modules.pullbackCongr hpb'.w.symm).app L ≪≫
        ((Scheme.Modules.pullbackComp p b).app L).symm ≪≫
        (Scheme.Modules.pullback p).mapIso eb ≪≫ Scheme.Modules.pullbackUnitIso p⟩
    have hqc₁ : ((Scheme.Modules.pullback (h ≫ e.inv)).obj F).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (blowUp (M.comap b)).ringCatSheaf).prop_of_iso eh.symm
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _)
    open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
    have hp : IsZero (((Scheme.Modules.pushforward p).rightDerivedPlus (q : ℤ)).obj
        ((Scheme.Modules.pullback (h ≫ e.inv)).obj F)) :=
      isZero_rightDerivedPlus_pushforward_of_isZero_cohomology
        p q _
      ((Stacks.Cohomology.AffineBase.isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup
        _ _ q).2 (hloc.of_iso ((Hfunctor _ ⊤ q).mapIso eh)))
    have hpull : IsZero ((Scheme.Modules.pullback b).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F)) :=
      hp.of_iso (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso hpb'.flip F q)
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    obtain ⟨e₁, -⟩ := exists_fromSpecStalkSectionsStalkLinearEquiv
      (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F) y hU hyU
    have hsub : Subsingleton (Γ((Scheme.Modules.pullback b).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F), ⊤)) :=
      ModuleCat.isZero_iff_subsingleton.mp ((SheafOfModules.evaluation _ (op ⊤)).map_isZero hpull)
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact e₁.symm.toEquiv.subsingleton
  · -- away from the centre the contraction is an isomorphism
    let V : X'.Opens := ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩
    have hiso : IsIso (f ∣_ V) := isIso_morphismRestrict_compl_of_blowUp_iso M z hz
      (by rw [← hM]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal _) e he
    have : IsAffineHom (f ∣_ V) := inferInstance
    have : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor _ _
    open Stacks.AlgebraicGeometry.SchemeHigherDirectImage in
    exact isZero_stalk_of_isZero_rightDerivedPlus_restrict
      f V y hy _ (by omega)
      (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom (f ∣_ V) _ q
        (by omega))

/-! ### The structure sheaf of the inverse image of a divisor -/

/-- An epimorphism between two isomorphisms is an epimorphism. -/
theorem epi_iso_hom_comp_comp_iso_hom {C : Type*} [Category C] {A B B' A' : C} (i : A ≅ B)
    (g : B ⟶ B') (j : B' ≅ A') [Epi g] : Epi (i.hom ≫ g ≫ j.hom) :=
  inferInstance

section InverseImage

variable {X X' : Scheme.{u}} {E : X.IdealSheafData} {f : X ⟶ X'}
  (hf : IsContractionOfExceptionalCurve E f) (D' : X'.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D']
  (hD : Stacks.Divisors.IsEffectiveCartierDivisor (D'.comap f))

include hf

/-- `Rᵠf_*𝒪_X = 0` for `q ≥ 1` along a contraction. -/
theorem IsContractionOfExceptionalCurve.isZero_rightDerived_pushforward_unit (q : ℕ)
    (hq : 1 ≤ q) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  have hqc : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).2
    (hf.isZero_rightDerivedPlus_pushforward_of_iso (SheafOfModules.unit X'.ringCatSheaf)
      (Stacks.SheafOfModules.isInvertible_unit X'.presheaf
        (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace))
      (SheafOfModules.unit X.ringCatSheaf) (Scheme.Modules.pullbackUnitIso f).symm q hq)

include hD in
/-- `Rᵠf_*𝒪_X(-f⁻¹D') = 0` for `q ≥ 1` along a contraction, `𝒪_X(-f⁻¹D')` being the pullback
of the invertible module `𝒪_{X'}(-D')`. -/
theorem IsContractionOfExceptionalCurve.isZero_rightDerived_pushforward_negativeTwist (q : ℕ)
    (hq : 1 ≤ q) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      (Stacks.Divisors.negativeTwist (D'.comap f))) := by
  have hqc : (Stacks.Divisors.negativeTwist (D'.comap f)).IsQuasicoherent :=
    have := @Stacks.Divisors.stacksIsInvertible_negativeTwist _ _ hD
    Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible X _
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).2
    (hf.isZero_rightDerivedPlus_pushforward_of_iso (Stacks.Divisors.negativeTwist D')
      (Stacks.Divisors.stacksIsInvertible_negativeTwist D') _
      (Stacks.Divisors.pullbackIdealSheafComapIso f D' hD).symm q hq)

include hD in
/-- **`Rᵠf_*(i_*𝒪_{f⁻¹D'}) = 0` for `q ≥ 1`**, from the long exact sequence of
`0 ⟶ 𝒪_X(-f⁻¹D') ⟶ 𝒪_X ⟶ i_*𝒪_{f⁻¹D'} ⟶ 0`. -/
theorem IsContractionOfExceptionalCurve.isZero_rightDerived_pushforward_subscheme (q : ℕ)
    (hq : 1 ≤ q) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      ((Scheme.Modules.pushforward (D'.comap f).subschemeι).obj
        (SheafOfModules.unit (D'.comap f).subscheme.ringCatSheaf))) := by
  have hS := Stacks.Cohomology.AmpleH1.shortExact_idealSheaf (D'.comap f).subschemeι
  have hex := (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Scheme.Modules.pushforward f)).exact_δ₁ hS q
  exact hex.isZero_X₂ ((hf.isZero_rightDerived_pushforward_unit q hq).eq_of_src _ _)
    ((hf.isZero_rightDerived_pushforward_negativeTwist D' hD (q + 1) (by omega)).eq_of_tgt _ _)

include hD in
/-- **`𝒪_{X'} ⟶ (i ≫ f)_*𝒪_{f⁻¹D'}` is an epimorphism**: `𝒪_{X'} ≅ f_*𝒪_X` for a contraction,
and `f_*𝒪_X ⟶ f_*i_*𝒪_{f⁻¹D'}` is onto because `R¹f_*𝒪_X(-f⁻¹D') = 0`. -/
theorem IsContractionOfExceptionalCurve.epi_unitToPushforwardObjUnit_subschemeι_comp :
    Epi (C := X'.Modules) (SheafOfModules.unitToPushforwardObjUnit
      ((D'.comap f).subschemeι ≫ f).toRingCatSheafHom) := by
  have hS := Stacks.Cohomology.AmpleH1.shortExact_idealSheaf (D'.comap f).subschemeι
  have h0 := Stacks.TopDirectImageRightExact.epi_rightDerived_map_g
    (Scheme.Modules.pushforward f) hS 0
    (hf.isZero_rightDerived_pushforward_negativeTwist D' hD 1 le_rfl)
  let g : SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward (D'.comap f).subschemeι).obj
        (SheafOfModules.unit (D'.comap f).subscheme.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit (D'.comap f).subschemeι.toRingCatSheafHom
  have h0' : Epi (((Scheme.Modules.pushforward f).rightDerived 0).map g) := h0
  have e := (Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf
  have h1 : Epi ((Scheme.Modules.pushforward f).map g) := by
    rw [← NatIso.naturality_1 e g]
    exact epi_iso_hom_comp_comp_iso_hom (e.app _).symm _ (e.app _)
  have h2 : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      f).1 hf.isIso_c
  rw [Stacks.AmpleCohomologicalCriterion.unitToPushforwardObjUnit_comp]
  exact @epi_iso_hom_comp_comp_iso_hom _ _ _ _ _ _
    (asIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) _
    ((Scheme.Modules.pushforwardComp (D'.comap f).subschemeι f).app _) h1

omit hf in
/-- **A morphism hitting the generic point of an integral target is injective on sections.** A
section killed by `g` has zero germ at `g y`, the generic point, because the stalk map there is a
ring map out of a field; and on an integral scheme a section with zero germ is zero. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.injective_app_of_apply_eq_genericPoint
    {Y Z : Scheme.{u}} [IsIntegral Z] (g : Y ⟶ Z) {y : Y} (hy : g y = genericPoint Z)
    (U : Z.Opens) : Function.Injective (g.app U) := by
  rcases eq_or_ne U ⊥ with rfl | hU
  · exact Function.injective_of_subsingleton _
  have hne : (U : Set Z).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun h => hU (Opens.coe_eq_empty.mp h)
  have hgU : g y ∈ U := by
    rw [hy]
    exact (genericPoint_spec Z).mem_open_set_iff U.isOpen |>.mpr (by rwa [Set.univ_inter])
  let : IsSimpleRing (Z.presheaf.stalk (g y)) := by
    rw [hy]
    exact inferInstanceAs (IsSimpleRing Z.functionField)
  intro a b hab
  apply germ_injective_of_isIntegral Z (g y) hgU
  apply RingHom.injective (g.stalkMap y).hom
  simp only [← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap]
  simp only [CommRingCat.comp_apply, hab]

include hD in
/-- **`f_*i_*𝒪_{f⁻¹D'} ≅ i'_*𝒪_{D'}`.** Let `g : f⁻¹D' ⟶ D'` be the morphism induced by `f`, and
suppose `D'` integral and hit at its generic point by `g`. The map `𝒪_{X'} ⟶ (i' ∘ g)_*𝒪_{f⁻¹D'}`
is onto
(`AlgebraicGeometry.IsContractionOfExceptionalCurve.epi_unitToPushforwardObjUnit_subschemeι_comp`)
and factors through the quotient `i'_*𝒪_{D'}` of `𝒪_{X'}` by a map which is injective, `g` being
injective on sections; so that map is an isomorphism. -/
theorem IsContractionOfExceptionalCurve.nonempty_pushforward_subscheme_iso
    (g : (D'.comap f).subscheme ⟶ D'.subscheme)
    (hg : g ≫ D'.subschemeι = (D'.comap f).subschemeι ≫ f) [IsIntegral D'.subscheme]
    {y : (D'.comap f).subscheme} (hy : g y = genericPoint D'.subscheme) :
    Nonempty ((Scheme.Modules.pushforward D'.subschemeι).obj
        (SheafOfModules.unit D'.subscheme.ringCatSheaf) ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pushforward (D'.comap f).subschemeι).obj
        (SheafOfModules.unit (D'.comap f).subscheme.ringCatSheaf))) := by
  have hepi := hf.epi_unitToPushforwardObjUnit_subschemeι_comp D' hD
  rw [← hg, Stacks.AmpleCohomologicalCriterion.unitToPushforwardObjUnit_comp] at hepi
  let u := (Scheme.Modules.pushforward D'.subschemeι).map
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp g D'.subschemeι).hom.app
      (SheafOfModules.unit (D'.comap f).subscheme.ringCatSheaf)
  have hmono₀ : Mono (C := D'.subscheme.Modules)
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) :=
    g.mono_unitToPushforwardObjUnit_of_app_injective
      (g.injective_app_of_apply_eq_genericPoint hy)
  have hmono₁ : Mono (C := X'.Modules) ((Scheme.Modules.pushforward D'.subschemeι).map
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)) :=
    @Functor.map_mono _ _ _ _ (Scheme.Modules.pushforward D'.subschemeι) inferInstance _ _ _
      hmono₀
  have hmono : Mono (C := X'.Modules) u :=
    @mono_comp _ _ _ _ _ _ hmono₁ _ (@IsIso.mono_of_iso _ _ _ _ _ (NatIso.hom_app_isIso _ _))
  have hepi' : Epi (C := X'.Modules) u := @epi_of_epi _ _ _ _ _ _ _ hepi
  have : IsIso (C := X'.Modules) u := isIso_of_mono_of_epi u
  exact ⟨asIso u ≪≫ (Scheme.Modules.pushforwardCongr hg).app _ ≪≫
    ((Scheme.Modules.pushforwardComp (D'.comap f).subschemeι f).app _).symm⟩

include hD in
/-- **`Hⁿ(f⁻¹D', 𝒪) ≅ Hⁿ(D', 𝒪)` as `Γ(X', 𝒪_{X'})`-modules**, in every degree, in the
setting of
`AlgebraicGeometry.IsContractionOfExceptionalCurve.nonempty_pushforward_subscheme_iso`. Both sides
are computed on `X'`: the right through the closed immersion `D' ⟶ X'`, the left through the
closed immersion `f⁻¹D' ⟶ X` followed by `f`, along which `i_*𝒪_{f⁻¹D'}` has no higher direct
images; and the two direct images to `X'` agree. -/
theorem IsContractionOfExceptionalCurve.nonempty_cohomology_subscheme_iso
    (g : (D'.comap f).subscheme ⟶ D'.subscheme)
    (hg : g ≫ D'.subschemeι = (D'.comap f).subschemeι ≫ f) [IsIntegral D'.subscheme]
    {y : (D'.comap f).subscheme} (hy : g y = genericPoint D'.subscheme) (n : ℕ) :
    Nonempty ((ModuleCat.restrictScalars f.appTop.hom).obj
        ((ModuleCat.restrictScalars (D'.comap f).subschemeι.appTop.hom).obj
          (((moduleGlobalSections (D'.comap f).subscheme).rightDerived n).obj
            (SheafOfModules.unit (D'.comap f).subscheme.ringCatSheaf))) ≅
      (ModuleCat.restrictScalars D'.subschemeι.appTop.hom).obj
        (((moduleGlobalSections D'.subscheme).rightDerived n).obj
          (SheafOfModules.unit D'.subscheme.ringCatSheaf))) := by
  obtain ⟨eiso⟩ := hf.nonempty_pushforward_subscheme_iso D' hD g hg hy
  have hac : (Scheme.Modules.pushforward f).rightAcyclic
      ((Scheme.Modules.pushforward (D'.comap f).subschemeι).obj
        (SheafOfModules.unit (D'.comap f).subscheme.ringCatSheaf)) :=
    (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ _).2 fun m hm =>
      hf.isZero_rightDerived_pushforward_subscheme D' hD m hm
  exact ⟨(ModuleCat.restrictScalars f.appTop.hom).mapIso
      ((Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso
        (D'.comap f).subschemeι n).app _) ≪≫
    Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso f _ n ≪≫
    Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso (Scheme.Modules.pushforward f)
      (moduleGlobalSections X')
      (Stacks.Cohomology.AffineComparison.rightAcyclic_moduleGlobalSections_pushforward_obj f)
      _ hac n ≪≫
    ((moduleGlobalSections X').rightDerived n).mapIso eiso.symm ≪≫
    ((Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso D'.subschemeι n).app
      _).symm⟩

end InverseImage

end AlgebraicGeometry

end
