module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.RingTheory.ULiftRingModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.CoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.ModuleEssSurj

/-!
# Stacks 09YU, clause (3), for a coefficient ring in any universe

`AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleModuleSheaf` is stated for a Noetherian
ring `Λ₀ : Type (u + 1)`, the universe at which the shriek presentations of Stacks 095N are
available. A ring `Λ` in any universe with a ring isomorphism `φ : Λ₀ ≃+* Λ` is handled by
restriction of scalars along `φ`, which identifies sheaves of `Λ`-modules with sheaves of
`Λ₀`-modules (coefficients in `ModuleCat.{u + 1}`), compatibly with inverse image
(`CategoryTheory.Sheaf.sheafPullbackCoefficientIso`) and with constructibility. For `Λ : Type`
take `Λ₀ := ULift.{u + 1} Λ`, `φ := ULift.ringEquiv`, and
`Stacks.ULiftTransport.isNoetherianRing_ulift`.

## Main results

* `AlgebraicGeometry.isConstructibleModuleSheaf_restrictScalars_ringEquiv` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_of_restrictScalars_ringEquiv` — constructibility
  is carried both ways.
* `AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleModuleSheaf_of_ringEquiv`,
  `AlgebraicGeometry.smallEtaleStagesFull_isConstructibleModuleSheaf_of_ringEquiv`,
  `AlgebraicGeometry.smallEtaleStagesFaithful_isConstructibleModuleSheaf_of_ringEquiv` and
  `AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleModuleSheaf_of_ringEquiv` — Tag 09YU,
  clause (3), at `Λ`. Fullness and faithfulness pass along the change of coefficients by
  `AlgebraicGeometry.smallEtaleStagesFull_of_coefficientEquivalence`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]

/-- Direct image of sheaves of `Λ`-modules is a right adjoint, for a ring `Λ` in any universe and
coefficients in `ModuleCat.{u + 1} Λ`. -/
theorem SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse {S T : B.Scheme} (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  SmallEtale.isRightAdjointPushforward_moduleCat.{u, u + 1, r} B Λ f

/-- Presheaves of `Λ`-modules on a localization of the small étale site admit weak
sheafification, for a ring `Λ` in any universe and coefficients in `ModuleCat.{u + 1} Λ`. -/
theorem SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ) :=
  SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1, r} B Λ T V

attribute [local instance 2000] SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse
  SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse

variable {Λ₀ : Type (u + 1)} [CommRing Λ₀] (φ : Λ₀ ≃+* Λ)

/-- Modules over `Λ` and over `Λ₀`, by restriction of scalars along a ring isomorphism
`φ : Λ₀ ≃+* Λ`, in the module universe of the small étale sites. -/
abbrev moduleCatSiteRingEquivalence : ModuleCat.{u + 1} Λ ≌ ModuleCat.{u + 1} Λ₀ :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv φ


/-- Constructibility is carried along an equivalence of module categories that preserves
finitely generated modules. -/
private theorem isConstructibleModuleSheaf_functor_obj_of_isFG {R₁ R₂ : Type*} [CommRing R₁]
    [CommRing R₂] (e : ModuleCat.{u + 1} R₁ ≌ ModuleCat.{u + 1} R₂) (X : B.Scheme)
    (hfg : ∀ M, ModuleCat.isFG R₁ M → ModuleCat.isFG R₂ (e.functor.obj M))
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R₁))
    (hF : IsConstructibleModuleSheaf B X R₁ F) :
    IsConstructibleModuleSheaf B X R₂
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property) e).functor.obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i => Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence _
    e _ hfg _ (hs i) _
    ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B (s.piece i).1 (s.piece i).property) e).app F)⟩

/-- **Constructibility is carried to `Λ₀`-modules** by restriction of scalars along a ring
isomorphism `φ : Λ₀ ≃+* Λ`. -/
theorem isConstructibleModuleSheaf_restrictScalars_ringEquiv (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) :
    IsConstructibleModuleSheaf B X Λ₀
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        (moduleCatSiteRingEquivalence.{u} Λ φ)).functor.obj F) :=
  isConstructibleModuleSheaf_functor_obj_of_isFG B _ X
    (fun M hM => (ModuleCat.isFG_iff _).2 (by
      have := (ModuleCat.isFG_iff _).1 hM
      exact ModuleCat.moduleFinite_restrictScalars_of_ringEquiv φ M)) F hF

/-- **Constructibility is carried back to `Λ`-modules** by restriction of scalars. -/
theorem isConstructibleModuleSheaf_of_restrictScalars_ringEquiv (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ₀))
    (hF : IsConstructibleModuleSheaf B X Λ₀ F) :
    IsConstructibleModuleSheaf B X Λ
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        (moduleCatSiteRingEquivalence.{u} Λ φ)).inverse.obj F) :=
  isConstructibleModuleSheaf_functor_obj_of_isFG B (moduleCatSiteRingEquivalence.{u} Λ φ).symm X
    (fun M hM => (ModuleCat.isFG_iff _).2 (by
      have := (ModuleCat.isFG_iff _).1 hM
      exact ModuleCat.moduleFinite_restrictScalars_of_ringEquiv φ.symm M)) F hF

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

include φ

/-- **Stacks 09YU, clause (3), the essential surjectivity assertion, along a ring isomorphism.**
Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms and let `Λ` be a Noetherian ring. Every constructible
sheaf of `Λ`-modules on `X_étale` is isomorphic to the inverse image of a constructible sheaf of
`Λ`-modules on some `(X_i)_étale`.

This is `AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleModuleSheaf` at the ring
`Λ₀`, carried back along restriction of scalars. -/
theorem smallEtaleStagesEssSurj_isConstructibleModuleSheaf_of_ringEquiv [IsNoetherianRing Λ₀]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y => IsConstructibleModuleSheaf B Y Λ) := by
  intro F hF
  obtain ⟨i, Fi, hFi, ⟨e⟩⟩ := smallEtaleStagesEssSurj_isConstructibleModuleSheaf B
    Λ₀ Dg c hX hc haff hqc hqs _
    (isConstructibleModuleSheaf_restrictScalars_ringEquiv B Λ φ (B.obj c.pt hX) F hF)
  refine ⟨i, _, isConstructibleModuleSheaf_of_restrictScalars_ringEquiv B Λ φ _ Fi hFi, ⟨?_⟩⟩
  exact ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (coneStageHom B Dg c hX i))
      (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (SmallEtale.topology B c.pt hX) (moduleCatSiteRingEquivalence.{u} Λ φ).symm).app Fi).symm ≪≫
    (sheafCompose _ (moduleCatSiteRingEquivalence.{u} Λ φ).inverse).mapIso e ≪≫
    ((Sheaf.coefficientEquivalence (SmallEtale.topology B c.pt hX)
      (moduleCatSiteRingEquivalence.{u} Λ φ)).unitIso.app F).symm

omit [Nonempty I] in
/-- **Stacks 09YU, clause (3), the fullness assertion, along a ring isomorphism.** -/
theorem smallEtaleStagesFull_isConstructibleModuleSheaf_of_ringEquiv [IsNoetherianRing Λ₀]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFull B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y => IsConstructibleModuleSheaf B Y Λ) :=
  smallEtaleStagesFull_of_coefficientEquivalence B (moduleCatSiteRingEquivalence.{u} Λ φ) Dg c hX
    (fun X F hF => isConstructibleModuleSheaf_restrictScalars_ringEquiv B Λ φ X F hF)
    (smallEtaleStagesFull_isConstructibleModuleSheaf B Λ₀ Dg c hX hc haff hqc hqs)

omit [Nonempty I] in
/-- **Stacks 09YU, clause (3), the faithfulness assertion, along a ring isomorphism.** -/
theorem smallEtaleStagesFaithful_isConstructibleModuleSheaf_of_ringEquiv [IsNoetherianRing Λ₀]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y => IsConstructibleModuleSheaf B Y Λ) :=
  smallEtaleStagesFaithful_of_coefficientEquivalence B (moduleCatSiteRingEquivalence.{u} Λ φ) Dg c
    hX (fun X F hF => isConstructibleModuleSheaf_restrictScalars_ringEquiv B Λ φ X F hF)
    (smallEtaleStagesFaithful_isConstructibleModuleSheaf B Λ₀ Dg c hX hc haff hqc
      hqs)

/-- **Stacks 09YU, clause (3), along a ring isomorphism.** The category of constructible sheaves of
`Λ`-modules on `X_étale` is the colimit of the categories of constructible sheaves of
`Λ`-modules on the `(X_i)_étale`, for a ring `Λ` isomorphic to a Noetherian ring `Λ₀` in
`Type (u + 1)`. -/
theorem smallEtaleStagesColimit_isConstructibleModuleSheaf_of_ringEquiv [IsNoetherianRing Λ₀]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesColimit B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y => IsConstructibleModuleSheaf B Y Λ) where
  faithful := smallEtaleStagesFaithful_isConstructibleModuleSheaf_of_ringEquiv B Λ φ Dg c hX hc haff
    hqc hqs
  full := smallEtaleStagesFull_isConstructibleModuleSheaf_of_ringEquiv B Λ φ Dg c hX hc haff hqc hqs
  essSurj := smallEtaleStagesEssSurj_isConstructibleModuleSheaf_of_ringEquiv B Λ φ Dg c hX hc haff
    hqc hqs

end AlgebraicGeometry
