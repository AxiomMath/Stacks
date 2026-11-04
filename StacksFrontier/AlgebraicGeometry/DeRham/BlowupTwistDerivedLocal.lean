module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsRetractionUniqueness
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreForms
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsDerived
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupTwistDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsExtension
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleFormsDegreeZero
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionHomPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafSum
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.HomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.IsomorphismLimit

/-!
# The twist map along a blowup, étale locally on the coordinate model

Let `f : X ⟶ S` be smooth, `i : Z ⟶ X` a closed immersion with `Z` smooth over `S` and of empty
interior in `X`, `b : X' ⟶ X` the blowing up of `X` along `Z`, and `𝒟` an effective Cartier
divisor on `X'` which is trivial off the exceptional divisor and which, on some étale chart
(`Stacks.DeRham.BlowupEtaleChart`) through every point of `Z`, is the pullback of `(n - 1)E` for
the coordinate model with centre of codimension `n`. This file proves that the canonical map
`Ω^a_{X/S} ⟶ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟))` of `Stacks.DeRham.TwistDerived.twistDerivedMap` is an
isomorphism in `D(𝒪_X)`.

## Main results

* `Stacks.DeRham.TwistDerived.isIso_pullback_higherImage_map_iff`: flat base change of
  `H^q(Rb_*(φ))` for a map `φ` of quasi-coherent modules.
* `Stacks.DeRham.TwistDerived.isIso_twistDerivedMap_of_isZero_higherDirectImage`: if
  `𝒪_X ⟶ b_*𝒪(D)` is an isomorphism and `R^q b_*𝒪(D) = 0` for `q > 0`, then
  `ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪(D))` is an isomorphism for every finite locally free `ℰ`.
* `Stacks.DeRham.TwistDerived.isIso_twistDerivedMap_forms_of_etaleLocal`: the canonical map
  `Ω^a_{X/S} ⟶ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟))` is an isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham.TwistDerived

open Stacks.AlgebraicGeometry.FlatBaseChangeDerived

/-- **The cohomology sheaves `H^q(Rb_*(-))` of a module placed in degree zero**, as a functor. -/
abbrev higherImage {Y X : Scheme.{u}} (b : Y ⟶ X) (q : ℤ) : Y.Modules ⥤ X.Modules :=
  DerivedCategory.singleFunctor Y.Modules 0 ⋙ schemeDerivedPushforward b ⋙
    DerivedCategory.homologyFunctor X.Modules q

section Transfer

variable {Y X Y₁ X₁ : Scheme.{u}} {b : Y ⟶ X} {b' : Y₁ ⟶ X₁} {g : X₁ ⟶ X} {g' : Y₁ ⟶ Y}
  (H : IsPullback g' b' b g) [Flat g] [QuasiCompact b] [QuasiSeparated b]

include H in
/-- **Flat base change of `H^q(Rb_*(φ))`.** For a cartesian square with `g` flat and `b`
quasi-compact and quasi-separated, and a map `φ` of quasi-coherent modules, the inverse image
along `g` of `H^q(Rb_*φ)` is invertible exactly when `H^q(Rb'_*(g'^*φ))` is. -/
theorem isIso_pullback_higherImage_map_iff {M N : Y.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) (q : ℤ) :
    IsIso ((Scheme.Modules.pullback g).map ((higherImage b q).map φ)) ↔
      IsIso ((higherImage b' q).map ((Scheme.Modules.pullback g').map φ)) := by
  rw [← isIso_comp_right_iff _ (homologyDerivedPushforwardBaseChange H N q)]
  exact (congrArg IsIso (homologyDerivedPushforwardBaseChange_naturality H φ q)).to_iff.trans
    (isIso_comp_left_iff _ _)

include H in
/-- **Flat base change of the vanishing of `H^q(Rb_*M)`.** -/
theorem isZero_pullback_higherImage_obj_iff (M : Y.Modules) [M.IsQuasicoherent] (q : ℤ) :
    IsZero ((Scheme.Modules.pullback g).obj ((higherImage b q).obj M)) ↔
      IsZero ((higherImage b' q).obj ((Scheme.Modules.pullback g').obj M)) :=
  (homologyDerivedPushforwardBaseChangeIso H M q).isZero_iff

include H in
/-- **Flat base change of `H^q(Rb_*)` of the canonical section.** -/
theorem isIso_pullback_higherImage_canonicalSectionHom_iff (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsPullbackDefined g' D]
    (q : ℤ) :
    IsIso ((Scheme.Modules.pullback g).map
        ((higherImage b q).map (Stacks.Divisors.canonicalSectionHom D))) ↔
      IsIso ((higherImage b' q).map (Stacks.Divisors.canonicalSectionHom (D.comap g'))) := by
  have : (Stacks.Divisors.divisorSheaf D).IsQuasicoherent := isQuasicoherent_twist D
  refine (isIso_pullback_higherImage_map_iff H _ q).trans ?_
  have hK := congrArg (higherImage b' q).map (Stacks.Divisors.pullback_canonicalSectionHom g' D)
  have hK' := ((higherImage b' q).map_comp _ _).symm.trans (hK.trans
    ((higherImage b' q).map_comp _ _))
  have hν : IsIso (C := Y₁.Modules)
      (SheafOfModules.pullbackObjUnitToUnit g'.toRingCatSheafHom) :=
    StacksTag09NE.isIso_pullbackUnit g'
  let e₁ := (higherImage b' q).mapIso (asIso (C := Y₁.Modules)
    (SheafOfModules.pullbackObjUnitToUnit g'.toRingCatSheafHom))
  let e₂ := (higherImage b' q).mapIso (Stacks.Divisors.invertibleSheafPullbackIso g' D)
  exact (isIso_comp_right_iff _ e₂.hom).symm.trans
    ((congrArg IsIso hK').to_iff.trans (isIso_comp_left_iff e₁.hom _))

include H in
/-- **Flat base change of the vanishing of `H^q(Rb_*𝒪(D))`.** -/
theorem isZero_pullback_higherImage_twist_iff (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsPullbackDefined g' D]
    (q : ℤ) :
    IsZero ((Scheme.Modules.pullback g).obj ((higherImage b q).obj
        (Stacks.Divisors.invertibleSheaf' D))) ↔
      IsZero ((higherImage b' q).obj (Stacks.Divisors.invertibleSheaf' (D.comap g'))) := by
  have : (Stacks.Divisors.divisorSheaf D).IsQuasicoherent := isQuasicoherent_twist D
  exact (isZero_pullback_higherImage_obj_iff H _ q).trans
    ((higherImage b' q).mapIso (Stacks.Divisors.invertibleSheafPullbackIso g' D)).isZero_iff

end Transfer

/-! ### The degree-zero comparison -/

section DegreeZero

variable {L X : Scheme.{u}} (b : L ⟶ X)

/-- **`𝒪_X ⟶ b_*𝒪_L(D)` is `𝒪_X ⟶ b_*𝒪_L` followed by `b_*` of the canonical section.** -/
theorem twistUnitComparison_eq (D : L.IdealSheafData) :
    Stacks.DeRham.BlowupTwist.twistUnitComparison b (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.canonicalSectionHom D) =
      SheafOfModules.unitToPushforwardObjUnit b.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward b).map (Stacks.Divisors.canonicalSectionHom D) :=
  ((Stacks.RingedSpace.pullbackAdjunction b.toLRSHom.toShHom).homEquiv_naturality_right
    _ _).trans (congrArg (· ≫ _)
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _))

/-- `H^0(Rb_*φ)` is invertible exactly when `b_*φ` is. -/
private theorem isIso_higherImage_zero_map_iff {M N : L.Modules} (φ : M ⟶ N) :
    IsIso ((higherImage b 0).map φ) ↔ IsIso ((Scheme.Modules.pushforward b).map φ) := by
  have hnat := congrArg (DerivedCategory.homologyFunctor X.Modules 0).map
    (pushforwardSingleToDerived_naturality b φ)
  simp only [Functor.map_comp] at hnat
  have h1 := Stacks.DeRham.isIso_homology_zero_pushforwardSingleToDerived b M
  have h2 := Stacks.DeRham.isIso_homology_zero_pushforwardSingleToDerived b N
  have e : IsIso ((DerivedCategory.homologyFunctor X.Modules 0).map
      ((DerivedCategory.singleFunctor X.Modules 0).map ((Scheme.Modules.pushforward b).map φ))) ↔
      IsIso ((higherImage b 0).map φ) := by
    rw [← isIso_comp_right_iff _ ((DerivedCategory.homologyFunctor X.Modules 0).map
      (pushforwardSingleToDerived b N)), hnat, isIso_comp_left_iff]
    rfl
  exact e.symm.trans (NatIso.isIso_map_iff
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0) _)

/-- **`b_*φ` is invertible as soon as `H^0(Rb_*φ)` is.** -/
theorem isIso_pushforward_map_of_isIso_higherImage {M N : L.Modules} (φ : M ⟶ N)
    (h : IsIso ((higherImage b 0).map φ)) : IsIso ((Scheme.Modules.pushforward b).map φ) :=
  (isIso_higherImage_zero_map_iff b φ).1 h

end DegreeZero

/-! ### The criterion over an arbitrary base -/

section Criterion

variable {L X : Scheme.{u}} (b : L ⟶ X) (D : L.IdealSheafData)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- If `R^q b_*𝒪_L(D) = 0` for `q > 0`, then `R^q b_*(b^*ℰ ⊗ 𝒪_L(D)) = 0` for `q > 0` and every
finite locally free `ℰ`. -/
theorem isZero_higherDirectImage_pullbackTwist_of_isZero
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hR : ∀ i : ℤ, 0 < i → IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus i).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus i).obj
      (Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
        (Stacks.Divisors.invertibleSheaf' D))) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = i := ⟨i.toNat, by omega⟩
  have hstd : IsZero (((Scheme.Modules.pushforward b).rightDerived q).obj
      (Stacks.Divisors.invertibleSheaf' D)) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).2 (hR q hi)
  have hsm := (@Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ _ _ _ _ _ _
    (Scheme.Modules.pushforward b) _ (Scheme.Modules.hasDerivedCategory L)
    (Scheme.Modules.hasDerivedCategory X) q _).1 hstd
  have h₁ := (Functor.map_isZero (Stacks.ProjectionFormula.tensorRightInvertible X E) hsm).of_iso
    ((Stacks.ProjectionFormula.higherDirectImageTensorRightFiniteLocallyFreeIso b E q).app
      (Stacks.Divisors.invertibleSheaf' D))
  have h₂ := (@Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ _ _ _ _ _ _
    (Scheme.Modules.pushforward b) _ (Scheme.Modules.hasDerivedCategory L)
    (Scheme.Modules.hasDerivedCategory X) q _).2 h₁
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q _).1
    (h₂.of_iso (((Scheme.Modules.pushforward b).rightDerived q).mapIso
      (pullbackTwistCommIso b D E)))

/-- **The criterion for `ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(D))`, over an arbitrary base.** For `b`
quasi-compact and quasi-separated, if `𝒪_X ⟶ b_*𝒪_L(D)` is an isomorphism and
`R^q b_*𝒪_L(D) = 0` for `q > 0`, the canonical map is an isomorphism at every finite locally free
`ℰ`. -/
theorem isIso_twistDerivedMap_of_isZero_higherDirectImage [QuasiCompact b] [QuasiSeparated b]
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (h0 : IsIso (Stacks.DeRham.BlowupTwist.twistUnitComparison b
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.canonicalSectionHom D)))
    (hR : ∀ i : ℤ, 0 < i → IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus i).obj
      (Stacks.Divisors.invertibleSheaf' D)))
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsIso (twistDerivedMap b D E) := by
  have := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have := isQuasicoherent_pullbackTwist b D E
  have hac : (Scheme.Modules.pushforward b).rightAcyclic
      (Scheme.Modules.tensorObj ((Scheme.Modules.pullback b).obj E)
        (Stacks.Divisors.invertibleSheaf' D)) := by
    have hfin : PreservesFiniteLimits (Scheme.Modules.pushforward b) := inferInstance
    exact (((Scheme.Modules.pushforward b).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
      _).2 hfin).mpr (isZero_higherDirectImage_pullbackTwist_of_isZero b D hR E)
  have := isIso_twistUnderivedMap b D E h0
  have := isIso_pushforwardSingleToDerived b _ hac
  rw [twistDerivedMap_eq]
  infer_instance

/-- If `H^i(Rb_*M)` vanishes, then so does `R^i b_*M`. -/
theorem isZero_rightDerivedPlus_of_isZero_higherImage (M : L.Modules) (i : ℤ)
    (h : IsZero ((higherImage b i).obj M)) :
    IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus i).obj M) := by
  obtain ⟨e⟩ := Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso b M i
  exact h.of_iso e.symm

/-- A module whose restriction to every member of an open cover vanishes is zero. -/
theorem isZero_of_isZero_pullback_ι {Y : Scheme.{u}} {ι : Type*} (U : ι → Y.Opens)
    (hU : iSup U = ⊤) (M : Y.Modules)
    (h : ∀ i, IsZero ((Scheme.Modules.pullback (U i).ι).obj M)) : IsZero M := by
  have : IsIso (0 : M ⟶ M) := by
    refine Scheme.Modules.isIso_of_isIso_pullback_ι U hU _ fun i ↦ ?_
    rw [Functor.map_zero, (h i).eq_of_src 0 (𝟙 _)]
    infer_instance
  exact IsZero.of_mono_zero M M

end Criterion

/-! ### The coordinate model and the case of an isomorphism -/

section Inputs

/-- The canonical section of the unit divisor is an isomorphism `𝒪 ⟶ 𝒪(⊤)`. -/
theorem isIso_canonicalSectionHom_top (Y : Scheme.{u}) :
    IsIso (C := Y.Modules) (Stacks.Divisors.canonicalSectionHom (⊤ : Y.IdealSheafData)) := by
  refine Stacks.Algebraization.isIso_of_affine_sections_bijective _ fun U ↦ ?_
  let bU := Stacks.Divisors.dualBasisOneOfPrincipal (⊤ : Y.IdealSheafData) U (f := 1)
    Ideal.span_singleton_one.symm (Submonoid.one_mem _)
  have he : Stacks.Divisors.idealSheafSection _ bU.e = 1 :=
    Exists.choose_spec ((Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection
      (⊤ : Y.IdealSheafData) U 1).1 Submodule.mem_top)
  have hs : ((Stacks.Divisors.canonicalSection' (⊤ : Y.IdealSheafData)).val (op U.1) :
      Γ(Stacks.Divisors.divisorSheaf (⊤ : Y.IdealSheafData), U.1)) =
        Stacks.Divisors.dualBasisOneLam _ bU := by
    rw [Stacks.Divisors.canonicalSection_eq_smul_dualBasisOne_lam _ bU, he, one_smul]
  have key : ∀ r : Γ(Y, U.1),
      (Stacks.Divisors.canonicalSectionHom (⊤ : Y.IdealSheafData)).val.app (op U.1) r =
        Stacks.SheafOfModules.smulSectionMap (𝒪 := Y.presheaf)
          (h𝒪 := (structureSheafRing Y.toRingedSpace).property)
          (L := Stacks.Divisors.invertibleSheaf' (⊤ : Y.IdealSheafData)) bU.lam r := by
    intro r
    have h3 := ((Stacks.Divisors.canonicalSectionHom (⊤ : Y.IdealSheafData)).val.app
      (op U.1)).hom.map_smul r (1 : Γ(Y, U.1))
    refine ((congrArg ((Stacks.Divisors.canonicalSectionHom (⊤ : Y.IdealSheafData)).val.app
      (op U.1)).hom (mul_one r)).symm.trans h3).trans ?_
    rw [Stacks.Divisors.canonicalSectionHom_app_one]
    exact congrArg (r • ·) hs
  exact (congrArg Function.Bijective (funext key)).mpr
    (Stacks.Divisors.bijective_smulSectionMap_dualBasisOne_lam _ bU)

/-- `𝒪_X ⟶ b_*𝒪_L` is an isomorphism as soon as `Ω^0_{X/S} ⟶ b_*Ω^0_{L/S}` is. -/
theorem isIso_unitToPushforwardObjUnit_of_forms {L X S : Scheme.{u}} (b : L ⟶ X) (π : X ⟶ S)
    (h : IsIso (Scheme.Hom.formsDirectImageComparison b π 0)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit b.toRingCatSheafHom) := by
  have hzX : IsIso (Scheme.Hom.relativeDifferentialFormsZeroIso π).hom :=
    Iso.isIso_hom (Scheme.Hom.relativeDifferentialFormsZeroIso π)
  have hpush : IsIso ((Scheme.Modules.pushforward b).map
      (Scheme.Hom.relativeDifferentialFormsZeroIso (b ≫ π)).hom) :=
    ((Scheme.Modules.pushforward b).mapIso
      (Scheme.Hom.relativeDifferentialFormsZeroIso (b ≫ π))).isIso_hom
  have h1 : IsIso ((Scheme.Hom.relativeDifferentialFormsZeroIso π).hom ≫
      SheafOfModules.unitToPushforwardObjUnit b.toRingCatSheafHom) := by
    rw [← Scheme.Hom.formsDirectImageComparison_zero b π]
    exact IsIso.comp_isIso' h hpush
  exact IsIso.of_isIso_comp_left (Scheme.Hom.relativeDifferentialFormsZeroIso π).hom _

/-- `H^0(Rb_*φ)` is invertible as soon as `b_*φ` is. -/
theorem isIso_higherImage_of_isIso_pushforward_map {L X : Scheme.{u}} (b : L ⟶ X)
    {M N : L.Modules} (φ : M ⟶ N) (h : IsIso ((Scheme.Modules.pushforward b).map φ)) :
    IsIso ((higherImage b 0).map φ) :=
  (isIso_higherImage_zero_map_iff b φ).2 h

/-- On the coordinate model, `H^0(Rb_*)` of the canonical section of `𝒪_L((n-1)E)` is
invertible. -/
theorem isIso_higherImage_coordinate (R : Type u) [CommRing R] (m n : ℕ) (hn : 1 ≤ n) :
    IsIso ((higherImage (coordinateBlowupToAmbient R m n) 0).map
      (Stacks.Divisors.canonicalSectionHom (coordinateExceptional R m n ^ (n - 1)))) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (coordinateExceptional R m n ^ (n - 1)) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow inferInstance (n - 1)
  have hT := isIso_twistUnitComparison_of_bijective (coordinateBlowupToAmbient R m n)
    (coordinateExceptional R m n ^ (n - 1))
    (CoordinateCech.bijective_globalTwist R m n hn (n - 1) (by omega))
  rw [twistUnitComparison_eq] at hT
  have hu := isIso_unitToPushforwardObjUnit_of_forms (coordinateBlowupToAmbient R m n)
    (coordinateAmbientToBase R m n) (isIso_coordinateBlowupFormsDirectImage R m n hn 0)
  have : IsIso ((Scheme.Modules.pushforward (coordinateBlowupToAmbient R m n)).map
      (Stacks.Divisors.canonicalSectionHom (coordinateExceptional R m n ^ (n - 1)))) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hu hT
  exact isIso_higherImage_of_isIso_pushforward_map _ _ this

/-- On the coordinate model, `H^q(Rb_*𝒪_L((n-1)E)) = 0` for `q > 0`. -/
theorem isZero_higherImage_coordinate (R : Type u) [CommRing R] (m n : ℕ) (hn : 1 ≤ n)
    (q : ℤ) (hq : 0 < q) :
    IsZero ((higherImage (coordinateBlowupToAmbient R m n) q).obj
      (Stacks.Divisors.invertibleSheaf' (coordinateExceptional R m n ^ (n - 1)))) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (coordinateExceptional R m n ^ (n - 1)) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow inferInstance (n - 1)
  obtain ⟨e⟩ := Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso
    (coordinateBlowupToAmbient R m n)
    (Stacks.Divisors.invertibleSheaf' (coordinateExceptional R m n ^ (n - 1))) q
  exact (isZero_higherDirectImage_twist (coordinateBlowupToAmbient R m n)
    (coordinateExceptional R m n ^ (n - 1))
    (CoordinateCech.isZero_rightDerived_twistSheaf R m n hn (n - 1) (by omega))
    q hq).of_iso e

/-- If `b` is an isomorphism, then `H^q(Rb_*𝒪(⊤)) = 0` for `q > 0` and `H^0(Rb_*)` of the
canonical section of `⊤` is invertible. -/
theorem higherImage_inputs_of_isIso {L X : Scheme.{u}} (b : L ⟶ X) [IsIso b] :
    (∀ q : ℤ, 0 < q → IsZero ((higherImage b q).obj
      (Stacks.Divisors.invertibleSheaf' (⊤ : L.IdealSheafData)))) ∧
    IsIso ((higherImage b 0).map (Stacks.Divisors.canonicalSectionHom (⊤ : L.IdealSheafData))) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (⊤ : L.IdealSheafData) :=
    Stacks.Divisors.isEffectiveCartierDivisor_top
  refine ⟨fun q hq ↦ ?_, ?_⟩
  · obtain ⟨e⟩ := Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso b
      (Stacks.Divisors.invertibleSheaf' (⊤ : L.IdealSheafData)) q
    exact (@Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward _ _ b _
      (Stacks.Divisors.invertibleSheaf' (⊤ : L.IdealSheafData)) (isQuasicoherent_twist _) q
      hq).of_iso e
  · have := isIso_canonicalSectionHom_top L
    exact ((higherImage b 0).mapIso (asIso (C := L.Modules)
      (Stacks.Divisors.canonicalSectionHom (⊤ : L.IdealSheafData)))).isIso_hom

end Inputs

/-! ### The étale-local statement -/

section Local

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)

/-- On an étale chart `c` on which `𝒟` is the pullback of `(n - 1)E`, the pullbacks to `c.U` of
`H^q(Rb_*𝒪(𝒟))` vanish for `q > 0` and the pullback of `H^0(Rb_*)` of the canonical section of
`𝒟` is invertible. -/
theorem higherImage_inputs_chart [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)]
    (hint : interior (Set.range i.base) = ∅) (𝒟 : (blowUp i.ker).IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor 𝒟] (c : BlowupEtaleChart f i) {x : X}
    (hx : x ∈ c.U)
    (hc : 𝒟.comap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι =
      (coordinateExceptional c.R c.m c.n ^ (c.n - 1)).comap c.blowupMap) :
    (∀ q : ℤ, 0 < q → IsZero ((Scheme.Modules.pullback c.U.ι).obj
      ((higherImage (blowUpToBase i.ker) q).obj (Stacks.Divisors.invertibleSheaf' 𝒟)))) ∧
    IsIso ((Scheme.Modules.pullback c.U.ι).map
      ((higherImage (blowUpToBase i.ker) 0).map (Stacks.Divisors.canonicalSectionHom 𝒟))) := by
  let := c.commRing
  have hn := c.one_le_n hint hx
  have := quasiCompact_blowUpToBase (f := f) (i := i)
  have : QuasiSeparated (blowUpToBase i.ker) :=
    have := Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_blowUpToBase i.ker
    inferInstance
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      (coordinateExceptional c.R c.m c.n ^ (c.n - 1)) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow inferInstance (c.n - 1)
  have : Stacks.Divisors.IsPullbackDefined (blowUpToBase i.ker ⁻¹ᵁ c.U).ι 𝒟 :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
  have : Stacks.Divisors.IsPullbackDefined c.blowupMap
      (coordinateExceptional c.R c.m c.n ^ (c.n - 1)) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
  have H₁ := (isPullback_morphismRestrict (blowUpToBase i.ker) c.U).flip
  have H₂ := c.isPullback_blowupMap.flip
  refine ⟨fun q hq ↦ ?_, ?_⟩
  · refine (isZero_pullback_higherImage_twist_iff H₁ 𝒟 q).2 ?_
    rw [hc]
    refine (isZero_pullback_higherImage_twist_iff H₂ _ q).1 ?_
    exact Functor.map_isZero _ (isZero_higherImage_coordinate c.R c.m c.n hn q hq)
  · refine (isIso_pullback_higherImage_canonicalSectionHom_iff H₁ 𝒟 0).2 ?_
    rw [hc]
    refine (isIso_pullback_higherImage_canonicalSectionHom_iff H₂ _ 0).1 ?_
    have := isIso_higherImage_coordinate c.R c.m c.n hn
    exact Functor.map_isIso _ _

/-- Over the complement of the centre, where `𝒟` is trivial, the pullbacks of `H^q(Rb_*𝒪(𝒟))`
vanish for `q > 0` and the pullback of `H^0(Rb_*)` of the canonical section of `𝒟` is
invertible. -/
theorem higherImage_inputs_compl [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)]
    (𝒟 : (blowUp i.ker).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor 𝒟]
    (hoff : 𝒟.comap (blowUpToBase i.ker ⁻¹ᵁ i.ker.support.compl).ι = ⊤) :
    (∀ q : ℤ, 0 < q → IsZero
      ((Scheme.Modules.pullback (Scheme.Opens.ι (X := X) i.ker.support.compl)).obj
        ((higherImage (blowUpToBase i.ker) q).obj (Stacks.Divisors.invertibleSheaf' 𝒟)))) ∧
    IsIso ((Scheme.Modules.pullback (Scheme.Opens.ι (X := X) i.ker.support.compl)).map
      ((higherImage (blowUpToBase i.ker) 0).map (Stacks.Divisors.canonicalSectionHom 𝒟))) := by
  have := quasiCompact_blowUpToBase (f := f) (i := i)
  have : QuasiSeparated (blowUpToBase i.ker) :=
    have := Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_blowUpToBase i.ker
    inferInstance
  have : Stacks.Divisors.IsPullbackDefined
      (blowUpToBase i.ker ⁻¹ᵁ i.ker.support.compl).ι 𝒟 :=
    Stacks.Divisors.isPullbackDefined_of_flat _ _ inferInstance
  have : IsIso (blowUpToBase i.ker ∣_ i.ker.support.compl) :=
    isIso_blowUpToBase_restrict_of_subset_compl_support i.ker _ fun _ h ↦ h
  have H₁ := (isPullback_morphismRestrict (blowUpToBase i.ker) i.ker.support.compl).flip
  obtain ⟨h₁, h₂⟩ := higherImage_inputs_of_isIso (blowUpToBase i.ker ∣_ i.ker.support.compl)
  refine ⟨fun q hq ↦ (isZero_pullback_higherImage_twist_iff H₁ 𝒟 q).2 ?_,
    (isIso_pullback_higherImage_canonicalSectionHom_iff H₁ 𝒟 0).2 ?_⟩
  · rw [hoff]
    exact h₁ q hq
  · rwa [hoff]

end Local

section Main

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)

/-- **The canonical map `Ω^a_{X/S} ⟶ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟))` is an isomorphism.** Let
`f : X ⟶ S` be smooth, `i : Z ⟶ X` a closed immersion with `Z` smooth over `S` and of empty
interior in `X`, and `b : X' ⟶ X` the blowing up of `X` along `Z`. Let `𝒟` be an effective
Cartier divisor on `X'` which is trivial over the complement of `Z` (`hoff`) and which, on some
étale chart through every point of `Z`, is the pullback of `(n - 1)E` for the coordinate model
with centre of codimension `n` (`hchart`). Then for every `a ≥ 0` the canonical map
`Ω^a_{X/S} ⟶ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(𝒟))` is an isomorphism in `D(𝒪_X)`. -/
theorem isIso_twistDerivedMap_forms_of_etaleLocal [IsClosedImmersion i] [Smooth f]
    [Smooth (i ≫ f)] (hint : interior (Set.range i.base) = ∅)
    (𝒟 : (blowUp i.ker).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor 𝒟] (a : ℕ)
    (hoff : 𝒟.comap (blowUpToBase i.ker ⁻¹ᵁ i.ker.support.compl).ι = ⊤)
    (hchart : ∀ z : Z, ∃ c : BlowupEtaleChart f i, i.base z ∈ c.U ∧
      𝒟.comap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι =
        (coordinateExceptional c.R c.m c.n ^ (c.n - 1)).comap c.blowupMap) :
    IsIso (twistDerivedMap (blowUpToBase i.ker) 𝒟 (Scheme.Hom.relativeDifferentialForms f a)) := by
  classical
  have := quasiCompact_blowUpToBase (f := f) (i := i)
  have : QuasiSeparated (blowUpToBase i.ker) :=
    have := Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_blowUpToBase i.ker
    inferInstance
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms f a
  have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      (∀ q : ℤ, 0 < q → IsZero ((Scheme.Modules.pullback V.ι).obj
        ((higherImage (blowUpToBase i.ker) q).obj (Stacks.Divisors.invertibleSheaf' 𝒟)))) ∧
      IsIso ((Scheme.Modules.pullback V.ι).map
        ((higherImage (blowUpToBase i.ker) 0).map (Stacks.Divisors.canonicalSectionHom 𝒟))) := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨c, hzc, hc⟩ := hchart z
      exact ⟨c.U, hzc, higherImage_inputs_chart f i hint 𝒟 c hzc hc⟩
    · refine ⟨i.ker.support.compl, ?_, higherImage_inputs_compl f i 𝒟 hoff⟩
      change x ∉ (i.ker.support : Set X)
      rwa [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  choose V hxV hV using hloc
  have hcov : iSup V = ⊤ :=
    top_le_iff.1 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  have hiso : IsIso ((higherImage (blowUpToBase i.ker) 0).map
      (Stacks.Divisors.canonicalSectionHom 𝒟)) :=
    Scheme.Modules.isIso_of_isIso_pullback_ι V hcov _ fun x ↦ (hV x).2
  have hzero : ∀ q : ℤ, 0 < q → IsZero ((higherImage (blowUpToBase i.ker) q).obj
      (Stacks.Divisors.invertibleSheaf' 𝒟)) :=
    fun q hq ↦ isZero_of_isZero_pullback_ι V hcov _ fun x ↦ (hV x).1 q hq
  have hu := isIso_unitToPushforwardObjUnit_of_forms (blowUpToBase i.ker) f
    (Stacks.DeRham.isIso_formsDirectImageComparison_blowUpToBase hint 0)
  have hp := isIso_pushforward_map_of_isIso_higherImage (blowUpToBase i.ker) _ hiso
  refine isIso_twistDerivedMap_of_isZero_higherDirectImage _ _ ?_
    (fun q hq ↦ isZero_rightDerivedPlus_of_isZero_higherImage _ _ q (hzero q hq)) _
  rw [twistUnitComparison_eq]
  exact IsIso.comp_isIso' hu hp

end Main

end Stacks.DeRham.TwistDerived

end
