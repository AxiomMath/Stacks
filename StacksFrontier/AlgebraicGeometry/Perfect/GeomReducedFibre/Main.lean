module

public import StacksFrontier.AlgebraicGeometry.Perfect.GeomReducedFibre.BasicOpenTransfer

/-!
# [Stacks, Tag 0G7Y]: the direct image of `𝒪_X` near a geometrically reduced fibre

Let `f : X ⟶ S` be proper, flat and of finite presentation and let `s ∈ S` have geometrically
reduced fibre. After replacing `S` by an open neighbourhood of `s`,
`Rf_*𝒪_X = f_*𝒪_X ⊕ P` in `D(𝒪_S)`, where `f_*𝒪_X` is a finite etale `𝒪_S`-algebra and `P` is
perfect of Tor amplitude in `[1, ∞)`.

## Proof

Choose an affine open `W ∋ s` and write `g : f⁻¹W ⟶ Spec Γ(S, W)` for the restriction. The affine
case `exists_away_splitting_and_finiteEtale` gives `a, h ∉ 𝔭_s` with `a ∣ h` such that the
splitting holds over `Spec Γ(S, W)_a` and `Γ(S, W)_h ⊗ Γ(f⁻¹W, 𝒪)` is finite etale over
`Γ(S, W)_h`. The neighbourhood is `U = D(h)`:

* finite etaleness on `U` is `app_basicOpen_of_tensor`, and on every affine open inside `U` it
  follows by locality of finite etale ring maps (`app_of_le`);
* the splitting over `Spec Γ(S, W)_a` restricts to `U` (`exists_splitting_restrict_of_isPullback`),
  its first summand is `f_*𝒪_X[0]` (`exists_splitting_pushforward_std`), and it is carried to every
  model of the derived categories (`exists_splitting_any_model`).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe w u

namespace StacksDraft.Perfect.GeomReducedFibre

/-- **Restricting a splitting to an open of the base.** Let `ψ : T ⟶ S` be an open immersion,
`gT : Y ⟶ T` the base change of `f : X ⟶ S` along `ψ`, and `U ⊆ S` an open inside the image of
`ψ`. A splitting `RgT_*𝒪_Y ≅ X₁ ⊕ P` (with `X₁` of Tor amplitude in `[0, 0]` and `P` perfect of
Tor amplitude in `[1, b]`) gives one for `f ∣_ U`. -/
theorem exists_splitting_restrict_of_isPullback {X S T Y : Scheme.{u}} (f : X ⟶ S) {gT : Y ⟶ T}
    {ψ : T ⟶ S}
    [IsOpenImmersion ψ] {qT : Y ⟶ X} (hsq : IsPullback qT gT f ψ) [IsProper gT] [Flat gT]
    (hfp : FinitePresentation gT) (U : S.Opens) (hU : U ≤ ψ.opensRange) (b : ℤ) :
    letI := HasDerivedCategory.standard Y.Modules
    letI := HasDerivedCategory.standard T.Modules
    letI := HasDerivedCategory.standard (f ⁻¹ᵁ U).toScheme.Modules
    letI := HasDerivedCategory.standard U.toScheme.Modules
    (∃ X₁ P : DerivedCategory T.Modules,
      Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule gT
        (Scheme.unitModule Y) ≅ X₁ ⊞ P) ∧
      HasTorAmplitudeStd T X₁ 0 0 ∧ Stacks.Duality.CompactBoundedness.IsPerfectStd P ∧
      HasTorAmplitudeStd T P 1 b) →
    ∃ X₁ P : DerivedCategory U.toScheme.Modules,
      Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule (f ∣_ U)
          (Scheme.unitModule (f ⁻¹ᵁ U).toScheme) ≅ X₁ ⊞ P) ∧
      HasTorAmplitudeStd U.toScheme X₁ 0 0 ∧ Stacks.Duality.CompactBoundedness.IsPerfectStd P ∧
      HasTorAmplitudeStd U.toScheme P 1 b := by
  let j : U.toScheme ⟶ T := IsOpenImmersion.lift ψ U.ι (by rwa [Scheme.Opens.range_ι])
  have hj : j ≫ ψ = U.ι := IsOpenImmersion.lift_fac _ _ _
  let k : (f ⁻¹ᵁ U).toScheme ⟶ Y := hsq.lift (f ⁻¹ᵁ U).ι (f ∣_ U ≫ j) (by
    rw [Category.assoc, hj, morphismRestrict_ι])
  have hk : IsPullback k (f ∣_ U) gT j := by
    refine IsPullback.of_right (h₁₂ := qT) ?_ (hsq.lift_snd _ _ _) hsq
    rw [hsq.lift_fst, hj]
    exact (isPullback_morphismRestrict f U).flip
  exact exists_splitting_of_isPullback hk hfp b

/-- The restriction of `f` over an affine open `W`, followed by `W ≅ Spec Γ(S, W)`, is the base
change of `f` along `Spec Γ(S, W) ⟶ S`. -/
private theorem isPullback_morphismRestrict_isoSpec {X S : Scheme.{u}} (f : X ⟶ S) {W : S.Opens}
    (hW : IsAffineOpen W) :
    IsPullback (f ⁻¹ᵁ W).ι (f ∣_ W ≫ hW.isoSpec.hom) f hW.fromSpec := by
  refine IsPullback.of_iso (isPullback_morphismRestrict f W).flip (Iso.refl _) (Iso.refl _)
    hW.isoSpec (Iso.refl _) (by simp) (by simp) (by simp) ?_
  show _ = hW.isoSpec.hom ≫ hW.fromSpec
  rw [← hW.isoSpec_inv_ι, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]

/-- A morphism that is locally of finite presentation, quasi-compact and quasi-separated is of
finite presentation. -/
private theorem finitePresentation_of_instances {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] : FinitePresentation f :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- If `Γ(S, U) → Γ(X, f⁻¹U)` is finite and etale for an affine open `U`, then so is
`Γ(S, V) → Γ(X, f⁻¹V)` for every affine open `V ⊆ U`. -/
private theorem finite_and_etale_app_of_le {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] {U : S.Opens} (hU : IsAffineOpen U) (hfin : RingHom.Finite (f.app U).hom)
    (het : RingHom.Etale (f.app U).hom) :
    ∀ V : S.affineOpens, V.1 ≤ U →
      letI : Algebra Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
      Module.Finite Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1) ∧ Algebra.Etale Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1) :=
  fun V hVU => ⟨app_of_le f RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
      RingHom.finite_ofLocalizationSpan hU V.2 hVU hfin,
    app_of_le f RingHom.Etale.respectsIso RingHom.Etale.propertyIsLocal.localizationAwayPreserves
      RingHom.Etale.ofLocalizationSpan hU V.2 hVU het⟩

/-- **[Stacks, Tag 0G7Y].** Let `f : X ⟶ S` be proper, flat and of finite presentation and let
`s ∈ S` be a point whose fibre `X_s` is geometrically reduced. Then there is an affine open
neighbourhood `U` of `s` such that

* `f_*𝒪_X` is a finite etale `𝒪_S`-algebra over `U`: for every affine open `V ⊆ U` the ring
  map `Γ(S, V) → Γ(X, f⁻¹V)` is finite and etale;
* `Rf_*𝒪_X ≅ f_*𝒪_X ⊕ P` in `D(𝒪_U)` with `P` perfect of Tor amplitude in `[1, b]` for some `b`
  (so in `[1, ∞)`), at every model of the derived categories. -/
@[stacks 0G7Y]
theorem exists_open_finiteEtale_and_derivedPushforward_splitting {X S : Scheme.{u}} (f : X ⟶ S)
    (hfp : FinitePresentation f) [IsProper f] [Flat f] (s : S)
    (hred : GeometricallyReduced (f.fiberToSpecResidueField s)) :
    ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧
      (∀ V : S.affineOpens, V.1 ≤ U →
        letI : Algebra Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1) := (f.app V.1).hom.toAlgebra
        Module.Finite Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1) ∧ Algebra.Etale Γ(S, V.1) Γ(X, f ⁻¹ᵁ V.1)) ∧
      ∃ b : ℤ, 1 ≤ b ∧ ∀ (hX : HasDerivedCategory.{w} (f ⁻¹ᵁ U).toScheme.Modules)
        (hU : HasDerivedCategory.{w} U.toScheme.Modules),
        letI := hX
        letI := hU
        letI : HasDerivedCategory.{w}
          (SheafOfModules.{u} (structureSheafRing (f ⁻¹ᵁ U).toScheme.toSheafedSpace)) := hX
        letI : HasDerivedCategory.{w}
          (SheafOfModules.{u} (structureSheafRing U.toScheme.toSheafedSpace)) := hU
        ∃ P : DerivedCategory U.toScheme.Modules,
          @Stacks.Cohomology.PerfectComplexes.IsPerfect U.toScheme.toRingedSpace hU P ∧
          @Stacks.Cohomology.TorAmplitude.HasTorAmplitude U.toScheme.toRingedSpace hU P 1 b ∧
          Nonempty ((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj
              ((Scheme.Modules.pushforward (f ∣_ U)).obj
                (Scheme.unitModule (f ⁻¹ᵁ U).toScheme)) ⊞ P ≅
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
              (f ∣_ U).toLRSHom.toShHom).obj
              ((DerivedCategory.singleFunctor (f ⁻¹ᵁ U).toScheme.Modules 0).obj
                (Scheme.unitModule (f ⁻¹ᵁ U).toScheme))) := by
  have := hred
  obtain ⟨_, _, _⟩ := hfp
  obtain ⟨W, hW, hsW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  let R := Γ(S, W)
  let φ : Spec R ⟶ S := hW.fromSpec
  let g : (f ⁻¹ᵁ W).toScheme ⟶ Spec R := f ∣_ W ≫ hW.isoSpec.hom
  have hsq : IsPullback (f ⁻¹ᵁ W).ι g f φ := isPullback_morphismRestrict_isoSpec f hW
  have : IsProper g := by dsimp [g]; infer_instance
  have : Flat g := by dsimp [g]; infer_instance
  have hgfp : FinitePresentation g := by
    dsimp [g]; exact finitePresentation_of_instances _
  let x : PrimeSpectrum R := hW.primeIdealOf ⟨s, hsW⟩
  have hx : φ x = s := hW.fromSpec_primeIdealOf ⟨s, hsW⟩
  obtain ⟨a, ha, ⟨b, hall⟩, h, hh, hdvd, hfe⟩ := exists_away_splitting_and_finiteEtale (R := R) g
    hgfp x.asIdeal (fibreGeometricallyReducedAt_of_isPullback f s φ hsq x.asIdeal hx)
  let U : S.Opens := S.basicOpen h
  have hsU : s ∈ U := by
    rw [← hx]
    change x ∈ φ ⁻¹ᵁ S.basicOpen h
    rw [hW.fromSpec_preimage_basicOpen]
    exact hh
  have hUaff : IsAffineOpen U := hW.basicOpen h
  refine ⟨U, hsU, hUaff, ?_, ?_⟩
  · exact finite_and_etale_app_of_le f hUaff
      (app_basicOpen_of_tensor RingHom.finite_respectsIso f hW h
        (RingHom.finite_algebraMap.2 (hfe (Localization.Away h)).1))
      (app_basicOpen_of_tensor RingHom.Etale.respectsIso f hW h
        (RingHom.etale_algebraMap.2 (hfe (Localization.Away h)).2))
  · refine ⟨max b 1, le_max_right b 1, fun hX hU' => ?_⟩
    let ιa : Spec (.of (Localization.Away a)) ⟶ Spec R :=
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a)))
    have hsq' := (IsPullback.of_hasPullback g ιa).paste_horiz hsq
    obtain ⟨_, _, _⟩ := hgfp
    have hfp' : FinitePresentation (pullback.snd g ιa) := finitePresentation_of_instances _
    have hrange : U ≤ (ιa ≫ φ).opensRange := by
      rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_localizationAway,
        hW.fromSpec_image_basicOpen]
      obtain ⟨c, rfl⟩ := hdvd
      rw [show U = S.basicOpen (a * c) from rfl, Scheme.basicOpen_mul]
      exact inf_le_left
    exact exists_splitting_any_model (f ∣_ U) _ (max b 1) (le_max_right b 1)
      (exists_splitting_pushforward_std (f ∣_ U) b
        (exists_splitting_restrict_of_isPullback f hsq' hfp' U hrange b
          (hall (IsPullback.of_hasPullback g ιa)))) hX hU'

end StacksDraft.Perfect.GeomReducedFibre

end
