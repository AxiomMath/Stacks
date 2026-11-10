module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineChart
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIso
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionTorAmplitude

/-!
# The ring of the chart `U ×_V U`

Let `f : X ⟶ S`, let `U ⊆ X` and `V ⊆ S` be affine opens with `U ⊆ f⁻¹V`, and write
`R = Γ(S, V)` and `A = Γ(X, U)`. The ring of sections of the affine scheme `U ×_V U` is
`A ⊗_R A`; under this identification the diagonal `U ⟶ U ×_V U` is the multiplication map and
the first projection is the left coprojection. For `f` flat and locally of finite presentation
this transports the diagonal condition of a relative dualizing complex (Stacks 0E2C) from the
chart ring to `A ⊗_R A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)

/-- The map on global sections of the diagonal `U ⟶ U ×_V U`, read into `Γ(X, U)`. -/
abbrev chartDiagonalRing : Γ(chartSquare hUV, ⊤) ⟶ Γ(X, U) :=
  (chartDiagonal hUV).appTop ≫ U.topIso.hom

/-- The map on global sections of the first projection `U ×_V U ⟶ U`, read out of `Γ(X, U)`. -/
abbrev chartProjRing : Γ(X, U) ⟶ Γ(chartSquare hUV, ⊤) :=
  U.topIso.inv ≫ (pullback.fst (chartMap hUV) (chartMap hUV)).appTop

/-- The map on global sections of the second projection `U ×_V U ⟶ U`. -/
abbrev chartProjRing₂ : Γ(X, U) ⟶ Γ(chartSquare hUV, ⊤) :=
  U.topIso.inv ≫ (pullback.snd (chartMap hUV) (chartMap hUV)).appTop

include hU hV in
/-- The two projections exhibit `Γ(U ×_V U, ⊤)` as the pushout of `Γ(S, V) ⟶ Γ(X, U)` along
itself. -/
theorem isPushout_chartProjRing :
    IsPushout (f.appLE V U hUV) (f.appLE V U hUV) (chartProjRing hUV) (chartProjRing₂ hUV) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let fV := chartMap hUV
  have hpo₀ : IsPushout fV.appTop fV.appTop (pullback.fst fV fV).appTop
      (pullback.snd fV fV).appTop :=
    isPushout_appTop_of_isPullback (IsPullback.of_hasPullback fV fV)
  refine IsPushout.of_iso hpo₀ V.topIso U.topIso U.topIso (Iso.refl _)
    (arrowResLEAppIso f V U hUV).hom.w.symm (arrowResLEAppIso f V U hUV).hom.w.symm ?_ ?_
  · change (pullback.fst fV fV).appTop =
      U.topIso.hom ≫ U.topIso.inv ≫ (pullback.fst fV fV).appTop
    exact (Iso.hom_inv_id_assoc U.topIso _).symm
  · change (pullback.snd fV fV).appTop =
      U.topIso.hom ≫ U.topIso.inv ≫ (pullback.snd fV fV).appTop
    exact (Iso.hom_inv_id_assoc U.topIso _).symm

include hU hV in
/-- `isPushout_chartProjRing`, with `Γ(S, V) ⟶ Γ(X, U)` written as an `algebraMap`. -/
private theorem isPushout_chartProjRing_algebraMap :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    IsPushout (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)))
      (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))) (chartProjRing hUV)
        (chartProjRing₂ hUV) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hα : f.appLE V U hUV = CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)) := by
    apply CommRingCat.hom_ext
    rfl
  simpa [hα] using isPushout_chartProjRing hU hV hUV

/-- **The ring of `U ×_V U` is `Γ(X, U) ⊗_{Γ(S, V)} Γ(X, U)`**: both are the pushout of
`Γ(S, V) ⟶ Γ(X, U)` along itself. -/
def chartSquareRingEquiv :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    Γ(X, U) ⊗[Γ(S, V)] Γ(X, U) ≃+* Γ(chartSquare hUV, ⊤) :=
  letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hα : f.appLE V U hUV = CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)) := by
    apply CommRingCat.hom_ext
    rfl
  have hpo' : IsPushout (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)))
      (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))) (chartProjRing hUV)
        (chartProjRing₂ hUV) := by
    simpa [hα] using isPushout_chartProjRing hU hV hUV
  ((CommRingCat.isPushout_tensorProduct Γ(S, V) Γ(X, U) Γ(X, U)).isoPushout ≪≫
    hpo'.isoPushout.symm).commRingCatIsoToRingEquiv

/-- `chartSquareRingEquiv` carries `a ⊗ 1` to the pullback of `a` along the first projection. -/
theorem chartSquareRingEquiv_includeLeft (x : Γ(X, U)) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    chartSquareRingEquiv hU hV hUV (Algebra.TensorProduct.includeLeftRingHom (A := Γ(X, U))
      (R := Γ(S, V)) x) = (chartProjRing hUV).hom x := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hpo' := isPushout_chartProjRing_algebraMap hU hV hUV
  have hTensor := CommRingCat.isPushout_tensorProduct Γ(S, V) Γ(X, U) Γ(X, U)
  have h₁ := congrArg (fun k => k.hom x) hTensor.inl_isoPushout_hom
  have h₂ := congrArg (fun k => k.hom x) hpo'.inl_isoPushout_inv
  exact (congrArg hpo'.isoPushout.inv.hom h₁).trans h₂

/-- `chartSquareRingEquiv` carries `1 ⊗ a` to the pullback of `a` along the second projection. -/
theorem chartSquareRingEquiv_includeRight (x : Γ(X, U)) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    chartSquareRingEquiv hU hV hUV (Algebra.TensorProduct.includeRight (A := Γ(X, U))
      (R := Γ(S, V)) x) = (chartProjRing₂ hUV).hom x := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hpo' := isPushout_chartProjRing_algebraMap hU hV hUV
  have hTensor := CommRingCat.isPushout_tensorProduct Γ(S, V) Γ(X, U) Γ(X, U)
  have h₁ := congrArg (fun k => k.hom x) hTensor.inr_isoPushout_hom
  have h₂ := congrArg (fun k => k.hom x) hpo'.inr_isoPushout_inv
  exact (congrArg hpo'.isoPushout.inv.hom h₁).trans h₂

/-- Under `chartSquareRingEquiv`, the first projection is the left coprojection. -/
theorem chartSquareRingEquiv_symm_comp_chartProjRing :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    (chartSquareRingEquiv hU hV hUV).symm.toRingHom.comp (chartProjRing hUV).hom =
      Algebra.TensorProduct.includeLeftRingHom := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  ext x
  change (chartSquareRingEquiv hU hV hUV).symm ((chartProjRing hUV).hom x) = _
  rw [← chartSquareRingEquiv_includeLeft hU hV hUV x, RingEquiv.symm_apply_apply]

/-- A section `p` of the diagonal gives a retraction on global sections. -/
private theorem topIso_inv_comp_appTop_comp_chartDiagonalRing (p : chartSquare hUV ⟶ U)
    (hp : chartDiagonal hUV ≫ p = 𝟙 U.toScheme) :
    (U.topIso.inv ≫ p.appTop) ≫ chartDiagonalRing hUV = 𝟙 _ := by
  rw [Category.assoc, ← Category.assoc p.appTop, ← Scheme.Hom.comp_appTop, hp,
    Scheme.Hom.id_appTop, Category.id_comp]
  exact Iso.inv_hom_id U.topIso

/-- Under `chartSquareRingEquiv`, the diagonal is the multiplication map. -/
theorem chartDiagonalRing_comp_ringEquiv :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    (chartDiagonalRing hUV).hom.comp (chartSquareRingEquiv hU hV hUV).toRingHom =
      (Algebra.TensorProduct.lmul' Γ(S, V) :
        Γ(X, U) ⊗[Γ(S, V)] Γ(X, U) →ₐ[Γ(S, V)] Γ(X, U)).toRingHom := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hleft (x) : (chartDiagonalRing hUV).hom ((chartProjRing hUV).hom x) = x :=
    congrArg (fun k => k.hom x)
      (topIso_inv_comp_appTop_comp_chartDiagonalRing hUV _ (pullback.diagonal_fst _))
  have hright (x) : (chartDiagonalRing hUV).hom ((chartProjRing₂ hUV).hom x) = x :=
    congrArg (fun k => k.hom x)
      (topIso_inv_comp_appTop_comp_chartDiagonalRing hUV _ (pullback.diagonal_snd _))
  symm
  apply Algebra.TensorProduct.ringHom_ext
  · ext x
    change _ = (chartDiagonalRing hUV).hom (chartSquareRingEquiv hU hV hUV _)
    rw [chartSquareRingEquiv_includeLeft, hleft]
    simp
  · ext x
    change _ = (chartDiagonalRing hUV).hom (chartSquareRingEquiv hU hV hUV
      (Algebra.TensorProduct.includeRight x))
    rw [chartSquareRingEquiv_includeRight, hright]
    simp

open CochainComplex.DerivedExtensionScalars in
/-- **The diagonal derived base change, read on the chart.** Under `chartSquareRingEquiv` the
derived extension of `M` along the first projection of `U ×_V U` is `M ⊗ᴸ_A (A ⊗_R A)`. -/
theorem nonempty_diagonalDerivedExtension_iso_chart [Flat f] [LocallyOfFinitePresentation f]
    (M : DerivedCategory (ModuleCat.{u} Γ(X, U))) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
    Nonempty ((Dualizing.diagonalDerivedExtension Γ(S, V) Γ(X, U)).obj M ≅
      (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u}
          (chartSquareRingEquiv hU hV hUV))).functor.obj
        ((totalDerivedExtensionScalars.{u, u, u} (chartProjRing hUV).hom).functor.obj M)) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
  let ePush := chartSquareRingEquiv hU hV hUV
  let Df := totalDerivedExtensionScalars.{u, u, u} (chartProjRing hUV).hom
  let f'' := ePush.symm.toRingHom.comp
    ((chartProjRing hUV).hom.comp (RingEquiv.refl Γ(X, U)).toRingHom)
  let Dg := totalDerivedExtensionScalars.{u, u, u} f''
  have e₁ := @StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRight _ _ _ _ _ _ ePush
    (chartProjRing hUV).hom Df.functor Df.comparison Df.isLeftDerived Dg.functor Dg.comparison
    Dg.isLeftDerived
  have hf'' : f'' = Algebra.TensorProduct.includeLeftRingHom :=
    chartSquareRingEquiv_symm_comp_chartProjRing hU hV hUV
  let G₀ := ModuleCat.extendScalars.{u, u, u}
    (Algebra.TensorProduct.includeLeftRingHom : Γ(X, U) →+* Γ(X, U) ⊗[Γ(S, V)] Γ(X, U))
  let : PreservesFiniteLimits G₀ :=
    extendScalars_preservesFiniteLimits_of_flat' _ (Dualizing.includeLeftRingHom_flat _ _)
  let : PreservesColimitsOfSize.{0, 0} G₀ :=
    (ModuleCat.extendRestrictScalarsAdj
      (Algebra.TensorProduct.includeLeftRingHom :
        Γ(X, U) →+* Γ(X, U) ⊗[Γ(S, V)] Γ(X, U))).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits G₀ := PreservesColimitsOfSize.preservesFiniteColimits G₀
  let : G₀.Additive := Functor.additive_of_preserves_binary_products G₀
  have e₂ := RingTheory.TorIndependence.totalDerivedExtensionScalarsIsoMapDerivedCategory f'' G₀
    (eqToIso (congrArg ModuleCat.extendScalars.{u, u, u} hf''.symm))
  exact ⟨(e₂.app M).symm ≪≫ e₁.app M⟩

open CochainComplex.DerivedExtensionScalars in
/-- **The diagonal condition of Stacks 0E2C, transported from the chart.** If derived Hom from
`Γ(X, U)` over `Γ(U ×_V U, ⊤)` into the derived pullback of `M` along the first projection is
`Γ(X, U)` in degree zero, then so is `RHom_{A ⊗_R A}(A, M ⊗ᴸ_A (A ⊗_R A))`. -/
theorem nonempty_diagonalDerivedHom_iso_of_chart [Flat f] [LocallyOfFinitePresentation f]
    (M : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (h : Nonempty ((Dualizing.derivedHom.{u, u} (chartDiagonalRing hUV).hom).obj
        ((totalDerivedExtensionScalars.{u, u, u} (chartProjRing hUV).hom).functor.obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U)))) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
    letI : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
      algebraFinitePresentation_appLE f hV hU hUV rfl
    Nonempty ((Dualizing.derivedHom.{u, u} (Algebra.TensorProduct.lmul' Γ(S, V) :
        Γ(X, U) ⊗[Γ(S, V)] Γ(X, U) →ₐ[Γ(S, V)] Γ(X, U)).toRingHom).obj
          ((Dualizing.diagonalDerivedExtension Γ(S, V) Γ(X, U)).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U))) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
  obtain ⟨e₀⟩ := h
  obtain ⟨e₁⟩ := nonempty_diagonalDerivedExtension_iso_chart hU hV hUV M
  let ePush := chartSquareRingEquiv hU hV hUV
  let f' := (RingEquiv.refl Γ(X, U)).symm.toRingHom.comp
    ((chartDiagonalRing hUV).hom.comp ePush.toRingHom)
  have hf' : f' = (Algebra.TensorProduct.lmul' Γ(S, V) :
      Γ(X, U) ⊗[Γ(S, V)] Γ(X, U) →ₐ[Γ(S, V)] Γ(X, U)).toRingHom :=
    chartDiagonalRing_comp_ringEquiv hU hV hUV
  have e₂ := StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso.{u, 0} ePush
    (RingEquiv.refl Γ(X, U)) (chartDiagonalRing hUV).hom
  let EC := Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u} (RingEquiv.refl Γ(X, U)))
  have e₃ : EC.functor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
      (ModuleCat.of Γ(X, U) Γ(X, U))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U)) :=
    (Dualizing.mapDerivedCategoryIdIso).app _
  refine ⟨(Dualizing.derivedHom.{u, u} _).mapIso e₁ ≪≫ ?_⟩
  refine eqToIso (congrArg (fun g => (Dualizing.derivedHom.{u, u} g).obj _) hf'.symm) ≪≫ ?_
  exact e₂.app _ ≪≫ EC.functor.mapIso e₀ ≪≫ e₃

open CochainComplex.DerivedExtensionScalars in
include hU hV in
/-- For `M` perfect relative to `Γ(S, V)`, its derived pullback along the first projection of
`U ×_V U` is cohomologically bounded below. -/
theorem isBoundedBelow_chartExtension [Flat f] [LocallyOfFinitePresentation f]
    (M : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hM : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
      letI : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
        algebraFinitePresentation_appLE f hV hU hUV rfl
      PseudoCoherence.IsRelativelyPerfect.{u, u, u}
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Γ(S, V)).tensor
        (StacksDraft.TorAmplitude.canonicalTensorComparison Γ(S, V))
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived Γ(S, V)) M) :
    DerivedCategoryB.IsBoundedBelow
      ((totalDerivedExtensionScalars.{u, u, u} (chartProjRing hUV).hom).functor.obj M) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
  let : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
    algebraFinitePresentation_appLE f hV hU hUV rfl
  obtain ⟨a, ha⟩ :=
    Dualizing.exists_isGE_diagonalDerivedExtension_of_relativelyPerfect Γ(S, V) Γ(X, U) M hM
  obtain ⟨e₁⟩ := nonempty_diagonalDerivedExtension_iso_chart hU hV hUV M
  let E :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u} (chartSquareRingEquiv hU hV hUV)
  let N := (totalDerivedExtensionScalars.{u, u, u} (chartProjRing hUV).hom).functor.obj M
  have hGE : (E.functor.mapDerivedCategory.obj N).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso e₁ a
  refine ⟨a, fun n hn => ?_⟩
  have hz := (DerivedCategory.isZero_of_isGE (E.functor.mapDerivedCategory.obj N) a n hn).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso E.functor n).app N).symm
  rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢; assumption

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
