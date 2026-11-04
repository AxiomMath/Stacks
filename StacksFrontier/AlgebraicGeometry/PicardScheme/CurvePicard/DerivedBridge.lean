module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapDegenerate
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatIndexed
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Normalized
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.SquareModel
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.OpenLocus
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# The derived condition of [Stacks, Tag 0B9V] read on fibres

[Stacks, Tag 0B9V] defines its subfunctor `F` of the Picard functor by the condition that
`Rf_{T,*}ℒ` be isomorphic to an invertible `𝒪_T`-module placed in degree `0`; the library's
`Stacks.PicardFunctor.normalizedSubfunctor` uses the fibrewise condition `H¹(X_t, ℒ_t) = 0`,
`dim H⁰(X_t, ℒ_t) = 1`. This file proves the comparison, starting with the part that only uses
`R¹f_{T,*}ℒ = 0`.

## Main results

* `Stacks.PicardFunctor.DerivedBridge.isZero_cohomology_preimage_of_isZero_homology`: a vanishing
  cohomology sheaf `Hᵖ(Rf_*ℱ)` gives `Hᵖ(f⁻¹V, ℱ) = 0` for every affine open `V` (Tags 01E5,
  01XK).
* `Stacks.PicardFunctor.DerivedBridge.isPullback_chart`: the preimage of an affine open `V` of a
  test scheme is the base change of the curve to `Γ(V)`.
* `Stacks.PicardFunctor.DerivedBridge.finrank_fibreCohomology_one_eq_zero_of_isZero_homology`:
  `H¹(Rf_{T,*}ℒ) = 0` forces `H¹(X_t, ℒ_t) = 0` on every fibre.

## References

* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.PicardFunctor.DerivedBridge

variable {Y T : Scheme.{u}} (f : Y ⟶ T)

/-- **The object `Rf_*ℱ` of `D(𝒪_T)`**: the derived pushforward along `f` of the module `ℱ` placed
in degree zero (in the standard model of the derived category). -/
abbrev derivedPushforwardModule (F : Y.Modules) : DerivedCategory T.Modules :=
  (derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor Y.Modules 0).obj F)

variable [QuasiCompact f] [QuasiSeparated f]

/-- **A vanishing cohomology sheaf of `Rf_*ℱ` gives vanishing cohomology over the preimage of an
affine open.** -/
theorem isZero_cohomology_preimage_of_isZero_homology (F : Y.Modules) [F.IsQuasicoherent] (p : ℕ)
    (h : IsZero ((homologyFunctor T.Modules (p : ℤ)).obj (derivedPushforwardModule f F)))
    (V : T.Opens) (hV : IsAffineOpen V) :
    IsZero (((moduleGlobalSections (f ⁻¹ᵁ V)).rightDerived p).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) := by
  have : IsAffine V := hV
  have h1 : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F) :=
    open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
    isZero_rightDerivedPlus_of_isZero_homologyFunctor_derivedPushforward f F p h
  have h3 : IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) :=
    ((Scheme.Modules.restrictFunctor V.ι).map_isZero h1).of_iso
      (ProjectiveCoherentImage.higherDirectImageRestrictObjIso f V F p)
  have h4 : IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived p).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) :=
    h3.of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ p).app _)
  have h5 := (moduleGlobalSections V).map_isZero h4
  have h6 := h5.of_iso
    (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso (f ∣_ V)
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) p)
  rw [ModuleCat.isZero_iff_subsingleton] at h6 ⊢
  exact h6

/-! ### The base change of the curve over an affine open of the test scheme -/

section Chart

open Stacks.TwoAffineCech Stacks.FibreCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))
  {T XT : Scheme.{u}} (a : T ⟶ Spec (.of k)) (gT : XT ⟶ X) (fT : XT ⟶ T)
  (hT : IsPullback gT fT fX a) (V : T.Opens) (hV : IsAffineOpen V)

/-- The `k`-algebra structure on the ring of an affine open of a scheme over `k`. -/
abbrev chartAlgebra : Algebra k Γ(T, V) :=
  (Spec.preimage (hV.isoSpec.inv ≫ V.ι ≫ a)).hom.toAlgebra

/-- Under `chartAlgebra`, the spectrum of the structure map `k → Γ(T, V)` is the composite
`Spec Γ(T, V) ≅ V ⟶ T ⟶ Spec k`. -/
theorem specMap_chartAlgebra :
    letI := chartAlgebra a V hV
    Spec.map (CommRingCat.ofHom (algebraMap k Γ(T, V))) = hV.isoSpec.inv ≫ V.ι ≫ a := by
  show Spec.map (CommRingCat.ofHom (Spec.preimage (hV.isoSpec.inv ≫ V.ι ≫ a)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The structure morphism of the preimage of an affine open, to the spectrum of its ring. -/
abbrev chartMap : (fT ⁻¹ᵁ V : Scheme.{u}) ⟶ Spec Γ(T, V) := (fT ∣_ V) ≫ hV.isoSpec.hom

include hT in
/-- **The preimage of an affine open `V` is the base change of the curve to `Γ(V)`.** -/
theorem isPullback_chart :
    letI := chartAlgebra a V hV
    IsPullback ((fT ⁻¹ᵁ V).ι ≫ gT) (chartMap fT V hV) fX
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(T, V)))) := by
  let := chartAlgebra a V hV
  have hbig := (isPullback_morphismRestrict fT V).flip.paste_horiz hT
  refine hbig.of_iso (Iso.refl _) (Iso.refl _) hV.isoSpec (Iso.refl _) (by simp) (by simp)
    (by simp) ?_
  rw [specMap_chartAlgebra]
  simp

/-- The preimage of an affine open is the base change of the family along the open. -/
theorem isPullback_chart_family :
    IsPullback (fT ⁻¹ᵁ V).ι (chartMap fT V hV) fT (hV.isoSpec.inv ≫ V.ι) :=
  (isPullback_morphismRestrict fT V).flip.of_iso (Iso.refl _) (Iso.refl _) hV.isoSpec
    (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

variable [IsProper fX] (U : Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i)) (L : XT.Modules) [Stacks.Ample.IsInvertibleModule XT L]

include hT hU hUaff in
/-- **If `R¹f_{T,*}ℒ = 0` then `H¹` vanishes on every fibre**: the cohomology in degree one of
`Rf_{T,*}ℒ` vanishing, `H¹` of `ℒ` vanishes over the preimage of every affine open, so the
two-term Čech differential is onto there, hence onto on every fibre. -/
theorem finrank_fibreCohomology_one_eq_zero_of_isZero_homology
    (h : IsZero ((homologyFunctor T.Modules (1 : ℤ)).obj (derivedPushforwardModule fT L)))
    (t : T) : Module.finrank (T.residueField t) (fibreCohomology fT L t 1) = 0 := by
  obtain ⟨V, hV, htV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := t) trivial
  let := chartAlgebra a V hV
  have hsq := isPullback_chart fX a gT fT hT V hV
  have : IsProper fT := MorphismProperty.of_isPullback hT inferInstance
  have : L.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  let L' := (Scheme.Modules.pullback (fT ⁻¹ᵁ V).ι).obj L
  have : Stacks.Ample.IsInvertibleModule _ L' :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (fT ⁻¹ᵁ V).ι L
  have : L'.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L'
  have : IsSeparated (chartMap fT V hV) := isSeparated_of_isPullback' fX _ _ hsq
  have : IsProper (chartMap fT V hV) := isProper_of_isPullback' fX _ _ hsq
  have h1 := isZero_cohomology_preimage_of_isZero_homology fT L 1 h V hV
  have h1' : IsZero (((moduleGlobalSections (fT ⁻¹ᵁ V)).rightDerived 1).obj L') :=
    h1.of_iso (((moduleGlobalSections (fT ⁻¹ᵁ V)).rightDerived 1).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (fT ⁻¹ᵁ V).ι).app L)).symm
  have hU' := iSup_sqCover U hU ((fT ⁻¹ᵁ V).ι ≫ gT)
  have hUaff' := isAffineOpen_sqCover fX U hUaff _ _ hsq
  have hcoh := cohomologyOneIso (chartMap fT V hV) (sqCover U ((fT ⁻¹ᵁ V).ι ≫ gT)) L' hU' hUaff'
  have hsurj : Function.Surjective
      (cechD (chartMap fT V hV) (sqCover U ((fT ⁻¹ᵁ V).ι ≫ gT)) L') := by
    have hz := ((ModuleCat.restrictScalars _).map_isZero h1').of_iso hcoh.symm
    rw [ModuleCat.isZero_iff_subsingleton] at hz
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    exact hz
  let p : PrimeSpectrum Γ(T, V) := hV.isoSpec.hom ⟨t, htV⟩
  have hfib := (isZero_cohomologyOverField_one_iff (chartMap fT V hV)
    (sqCover U ((fT ⁻¹ᵁ V).ι ≫ gT)) L' hU' hUaff' p).2
    (LinearMap.baseChange_surjective _ hsurj)
  have hdim := finrank_fibre_eq_fibreCohomology (chartMap fT V hV) L' p 1
  rw [ModuleCat.isZero_iff_subsingleton] at hfib
  rw [Module.finrank_zero_of_subsingleton] at hdim
  have htr := finrank_fibreCohomology_eq_of_isPullback fT L (fT ⁻¹ᵁ V).ι (chartMap fT V hV)
    (hV.isoSpec.inv ≫ V.ι) (isPullback_chart_family fT V hV) L' (Iso.refl _) (specPoint p) 1
  have ht : (hV.isoSpec.inv ≫ V.ι) (specPoint p) = t := by
    show V.ι ((hV.isoSpec.hom ≫ hV.isoSpec.inv) ⟨t, htV⟩) = t
    rw [Iso.hom_inv_id]
    rfl
  rw [← hdim] at htr
  clear_value p
  subst ht
  exact htr.symm

end Chart

end Stacks.PicardFunctor.DerivedBridge
