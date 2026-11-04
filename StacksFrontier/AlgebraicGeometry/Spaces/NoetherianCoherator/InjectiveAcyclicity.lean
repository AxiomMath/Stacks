module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.InjectiveRestrictionUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.HigherDirectImageBound
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.LerayAcyclicity
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.InjectiveQcohSpace

/-!
# Higher direct images of an injective quasi-coherent module on a Noetherian affine space

Let `U` be the algebraic space represented by an affine scheme with Noetherian ring of global
functions, with `U` Noetherian, and let `𝒥` be an injective object of `QCoh(𝒪_U)`.  For every
morphism `g : U ⟶ Y` to a quasi-compact quasi-separated algebraic space, `R^p g_* 𝒥 = 0` for
`p > 0`.

Choose an affine scheme `V` with a surjective étale morphism `V ⟶ Y`.  By étale base change it
suffices to show that the higher direct images along `U ×_Y V ⟶ V` of the restriction of `𝒥` to
`U ×_Y V` vanish; `U ×_Y V` is quasi-compact, quasi-separated and étale over `U`, and the target
is affine, so this is
`AlgebraicGeometry.Space.isZero_rightDerived_restriction_of_restrictionUnitPushforwardEpi`, whose
input is `AlgebraicGeometry.Space.restrictionUnitPushforwardEpi_of_injective`.

On a Noetherian algebraic space `X` an injective object `𝒥` of `QCoh(𝒪_X)` is a retract of
`j_*𝒥'` for an affine surjective étale chart `j : U ⟶ X` and an injective object `𝒥'` of
`QCoh(𝒪_U)` (the argument of Stacks 09TJ).  The affine case gives `R^q j_* 𝒥' = 0` and
`R^p (j ≫ f)_* 𝒥' = 0`, so `R^p f_*(j_* 𝒥') = 0` by the degenerate Leray spectral sequence, and
`R^p f_* 𝒥` is a retract of it.  This is Stacks 09TL (2) for a quasi-compact quasi-separated
target, which is the form in which Stacks 09TM uses it.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_injective_of_isAffine`.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_injective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  isGrothendieckAbelian_modules

attribute [local instance 5000] modulePushforward_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Higher direct images of an injective quasi-coherent module on a Noetherian affine space
vanish**, along any morphism to a quasi-compact quasi-separated algebraic space. -/
theorem isZero_rightDerived_modulePushforward_of_injective_of_isAffine
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (W : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)]
    (hWN : IsNoetherian B S hS hZ (schemeSpace W).1) {Y : AlgebraicSpaces B S hS}
    (g : schemeSpace W ⟶ Y) (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (J : QuasicoherentSheaves.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2)
    (hJ : Injective J) (p : ℕ) :
    IsZero (((modulePushforward B S hS g).rightDerived (p + 1)).obj J.obj) := by
  obtain ⟨U, c₀, hU, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y.1 Y.2).1 hYqc
  let c : schemeSpace U ⟶ Y := ObjectProperty.homMk c₀
  have hVaff : IsAffineSpace B S hS (schemeSpace U).1 := isAffineSpace_yoneda B S hS U hU
  let X₀ := AlgebraicSpaces.fiberProduct B S hS g c
  have hX₀qc : IsQuasiCompactSpace B S hS X₀.1 :=
    isQuasiCompactSpace_pullback B S hS hZ g.hom c.hom (schemeSpace W).2 Y.2 hWN.1
      hVaff.isQuasiCompactSpace hYqs
  have hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1 :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ g.hom c.hom (schemeSpace W).2
      (schemeSpace U).2 Y.2 hWN.2.1 (hVaff.isAbsolutelyQuasiSeparated B S hS hZ)
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS g c
  let i : X₀ ⟶ schemeSpace W := ObjectProperty.homMk (pullback.fst g.hom c.hom)
  let h : X₀ ⟶ schemeSpace U := ObjectProperty.homMk (pullback.snd g.hom c.hom)
  have hi : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS h i c g sq.flip het
  have hvan := isZero_rightDerived_restriction_of_restrictionUnitPushforwardEpi B S hS hZ hX₀qc
    hX₀qs i hi hVaff h J.obj J.2 (restrictionUnitPushforwardEpi_of_injective B S hS hZ W hWN J hJ)
  have := faithful_etaleModulePullback.{u, u} B S hS U c het hsurj
  have := etaleModulePullback_additive.{u, u} B S hS c het
  refine (etaleModulePullback.{u, u} B S hS c het).isZero_of_isZero_obj_of_faithful ?_
  exact IsZero.of_iso (hvan p)
    ((moduleHigherPushforwardEtaleBaseChangeIso B S hS _ _ g c sq het (p + 1)).app J.obj).symm

/-- **Higher direct images of an injective quasi-coherent module on a Noetherian algebraic space
vanish** along any morphism to a quasi-compact quasi-separated algebraic space (Stacks 09TL (2),
for a quasi-compact target). -/
theorem isZero_rightDerived_modulePushforward_of_injective (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (hX : IsNoetherian B S hS hZ X.1) (f : X ⟶ Y)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (hJ : Injective J) (p : ℕ) :
    IsZero (((modulePushforward B S hS f).rightDerived (p + 1)).obj J.obj) := by
  obtain ⟨W, j₀, hW, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX.1
  let j : schemeSpace W ⟶ X := ObjectProperty.homMk j₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hW
  have hWaff : IsAffineSpace B S hS (schemeSpace W).1 := isAffineSpace_yoneda B S hS W hW
  have hWN : IsNoetherian B S hS hZ (schemeSpace W).1 :=
    isNoetherian_of_isEtale_of_isAffineSpace B S hS hZ (schemeSpace W).2 X.2 j.hom het hWaff
      hX.2.2
  have hWloc : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) :=
    (exists_atlas_iff_forall_etale B S hS X.1
        (fun T : Scheme.{u} => IsLocallyNoetherian T) X.2).mp hX.2.2 W j₀
      ((isEtale_iff_presheaf_of_yoneda B S hS j₀).1 het)
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hjqc : IsQuasiCompact B S hS j.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hX.2.1 hWN.1 j.hom
  have hjqs : IsQuasiSeparated B S hS j.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ (schemeSpace W).2 hWN.2.1 j.hom
  have hqc : ∀ M : QuasicoherentSheaves.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2,
      ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite := fun M =>
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j hjqc hjqs M.obj M.2
  -- the retract of Stacks 09TJ
  have hinj := quasicoherentSheaves_enoughInjectives B S hS (schemeSpace W).1 (schemeSpace W).2
  obtain ⟨P⟩ := EnoughInjectives.presentation
    (C := QuasicoherentSheaves.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2)
    ((quasicoherentPullbackOfIsEtale B S hS j het).obj J)
  have := faithful_modulePullback B S hS W j het hsurj
  have := faithful_quasicoherentPullbackOfIsEtale B S hS j het
  let μ : J ⟶ (chartQuasicoherentPushforward B S hS j hqc).obj P.J :=
    (chartQuasicoherentAdjunction B S hS j het hqc).homEquiv J P.J P.f
  have : Mono μ := inferInstance
  let r : Retract J ((chartQuasicoherentPushforward B S hS j hqc).obj P.J) :=
    { i := μ
      r := Injective.factorThru (𝟙 J) μ
      retract := Injective.comp_factorThru (𝟙 J) μ }
  -- the affine case and Leray
  have hj0 : ∀ q : ℕ, IsZero (((modulePushforward B S hS j).rightDerived (q + 1)).obj P.J.obj) :=
    fun q => isZero_rightDerived_modulePushforward_of_injective_of_isAffine B S hS hZ W hWN j
      hX.1 hX.2.1 P.J P.injective q
  have hjf := isZero_rightDerived_modulePushforward_of_injective_of_isAffine B S hS hZ W hWN
    (j ≫ f) hYqc hYqs P.J P.injective p
  have hpush := isZero_rightDerived_modulePushforward_obj_of_isEtale B S hS j het f P.J.obj hj0 p
    hjf
  exact hpush.of_retract
    (r.map (ObjectProperty.ι _ ⋙ (modulePushforward B S hS f).rightDerived (p + 1)))

end AlgebraicGeometry.Space

end
