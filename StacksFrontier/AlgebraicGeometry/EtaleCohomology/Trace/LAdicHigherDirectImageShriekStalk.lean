module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LerayPointComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkFrobeniusResidueField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageCoefficient

/-!
# The stalks of `Rʳ g_! G` at closed points

Let `g : U ⟶ W` be separated of finite type, with a compactification `j_g`, `G` an ℓ-adic sheaf on
`U` and `R = Rʳ g_! G` (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`). At a point
`w` of `W` with finite residue field `κ = κ(w)`, with fibre `U_w = U ×_W Spec κ`,

`det(1 - π_w T | R_w̄ ⊗ ℚ_ℓ) = det(1 - π_κ T | Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ))`:

* the stalk Frobenius at `w` is the Frobenius of `κ` on `H⁰_c(Spec κ̄, i⁻¹ R)`
  (`Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkFrobenius_eq_residueField`);
* `H⁰_c(Spec κ̄, i⁻¹ R) ⊗ ℚ_ℓ` is the rational limit of `H⁰_c(Spec κ̄, i⁻¹ Rʳ g_! G'ₘ)` over the
  levels of the flat model `G'` of `G`: the tower of levels of `R` is the stable image tower of
  `m ↦ Rʳ g_! G'ₘ`, pro-isomorphic to it;
* `i⁻¹ Rʳ g_! G'ₘ ≅ Rʳ g_{w!} (G'ₘ|_{U_w})` by proper base change
  ([Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L),
  `Stacks.EtaleCohomology.lowerShriekHomologyBaseChangeIso`);
* `H⁰_c(Spec κ̄, Rʳ g_{w!} K) ≅ Hʳ_c(U_{w,κ̄}, K)` with Frobenius, from the Leray comparison
  ([Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J),
  `LAdicSheaf.exists_lowerShriekHomology_compactSupportSheafCohomology_iso`);
* the rational limit of `Hʳ_c(U_{w,κ̄}, G'ₘ|)` is `Hʳ_c(U_{w,κ̄}, G'| ⊗ ℚ_ℓ)`, and `G'` is
  isogenous to `G`.

This is the stalk input `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageStalkInput` of the
reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) for the family `Rʳ g_! G`, from the
constructibility of the `Rⁿ g_!` (Tag 0GL0,
`Stacks.EtaleCohomology.LowerShriekConstructibilityInput`) and the Leray comparison with Frobenius
(`Stacks.EtaleCohomology.LAdicSheaf.LerayFrobeniusComparison`).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkFrobenius_higherDirectImageShriek`.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **Characteristic polynomials are invariant under an equivariant isomorphism.** -/
theorem charpoly_eq_of_comm_iso {ℓ : ℕ} [Fact ℓ.Prime] {M N : ModuleCat.{u + 1} ℚ_[ℓ]}
    (hM : FiniteDimensional ℚ_[ℓ] M) (hN : FiniteDimensional ℚ_[ℓ] N) (e : M ≅ N) (φ : M ⟶ M)
    (ψ : N ⟶ N) (h : φ ≫ e.hom = e.hom ≫ ψ) : φ.hom.charpoly = ψ.hom.charpoly := by
  have hc : e.toLinearEquiv.conj φ.hom = ψ.hom := by
    refine LinearMap.ext fun v => ?_
    have := congrArg (fun t => t.hom (e.inv.hom v)) h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply]
    change e.hom.hom (φ.hom (e.inv.hom v)) = ψ.hom v
    rw [this]
    congr 1
    exact congrArg (fun t => t.hom v) e.inv_hom_id
  rw [← hc, LinearEquiv.charpoly_conj]

/-- Finite dimensionality along an isomorphism, with the hypothesis as an explicit argument. -/
private theorem finiteDimensional_of_iso {ℓ : ℕ} [Fact ℓ.Prime] {M N : ModuleCat.{u + 1} ℚ_[ℓ]}
    (e : M ≅ N) (h : FiniteDimensional ℚ_[ℓ] M) : FiniteDimensional ℚ_[ℓ] N := by
  have := h
  exact LinearEquiv.finiteDimensional e.toLinearEquiv

/-- An isomorphism of towers commuting with endomorphisms gives equal characteristic polynomials
on the rational limits. -/
theorem charpoly_rationalLim_map_eq_of_iso {ℓ : ℕ} [Fact ℓ.Prime]
    {A A' : ℕᵒᵖ ⥤ ModuleCat.{u + 1} ℤ_[ℓ]}
    (hA : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj A))
    (hA' : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj A')) (e : A ≅ A')
    (φ : A ⟶ A) (φ' : A' ⟶ A') (h : φ ≫ e.hom = e.hom ≫ φ') :
    ((rationalLim.{u + 1} (ℓ := ℓ)).map φ).hom.charpoly =
      ((rationalLim.{u + 1} (ℓ := ℓ)).map φ').hom.charpoly :=
  charpoly_eq_of_comm_iso hA hA' ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso e) _ _ (by
    rw [Functor.mapIso_hom, ← Functor.map_comp, h, Functor.map_comp])

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

section Core

variable {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (w : W.1) [Fintype (W.1.residueField w)] (hB : B.Contains ((B.inclusion.map g).fiber w))
  [IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)]
  (kbar : Type u) [Field kbar] [Algebra (W.1.residueField w) kbar] [IsAlgClosed kbar] (p n : ℕ)
  [Fact p.Prime] [CharP (W.1.residueField w) p] (hcard : Fintype.card (W.1.residueField w) = p ^ n)

/-- The fibre `U_w = U ×_W Spec κ(w)` as an object of the big étale site. -/
abbrev fibreObj : B.Scheme := B.obj ((B.inclusion.map g).fiber w) hB

/-- The inclusion of the fibre `U_w ⟶ U`. -/
abbrev fibreι : fibreObj B g w hB ⟶ U := ObjectProperty.homMk ((B.inclusion.map g).fiberι w)

/-- The fibre `U_w ⟶ Spec κ(w)`, as a morphism of the big étale site. -/
abbrev fibreToResidueField :
    fibreObj B g w hB ⟶ BigEtaleSite.specField B W (W.1.residueField w) :=
  ObjectProperty.homMk ((B.inclusion.map g).fiberToSpecResidueField w)

omit [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] in
/-- **The stalk of `Rʳ g_! G` at a point with finite residue field `κ`, with its Frobenius**, is
`Hʳ_c` of the fibre over `κ̄` with the Frobenius of `κ`, given the Leray identification
`H⁰_c(Spec κ̄, Rʳ g_{w!} K) ≅ Hʳ_c(U_{w,κ̄}, K)` with Frobenius `Ψ` on ℓ-power torsion sheaves of
the fibre: under the conditions
`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageShriekCondition` making `Rʳ g_! G` the ℓ-adic
sheaf of the stable images, the two Frobenius endomorphisms have the same characteristic
polynomial. -/
theorem LAdicSheaf.charpoly_rationalStalkFrobenius_higherDirectImageShriek
    (G : LAdicSheaf.{u, u + 1} B U ℓ) (r : ℕ)
    (hcond : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r)
    (hw : Finite (W.1.residueField w))
    (jgw : CompactificationOf (Over.mk ((B.inclusion.map g).fiberToSpecResidueField w)))
    (jU : CompactificationOf (Over.mk ((B.inclusion.map g).fiberToSpecResidueField w ≫
      𝟙 (Spec (.of (W.1.residueField w))))))
    (Ψ : (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
          (CompactificationOf.ofProper (𝟙 _)) kbar 0 ≅
      (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        compactSupportSheafCohomology ℤ_[ℓ]
          ((B.inclusion.map g).fiberToSpecResidueField w ≫ 𝟙 (Spec (.of (W.1.residueField w))))
          jU kbar r)
    (hΨ : Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (Functor.whiskerLeft
          (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
          (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
            (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0)) ≫ Ψ.hom =
      Ψ.hom ≫ Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (compactSupportSheafFrobenius ℤ_[ℓ]
          ((B.inclusion.map g).fiberToSpecResidueField w ≫ 𝟙 (Spec (.of (W.1.residueField w))))
          jU kbar p n hcard r))
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      (k := W.1.residueField w) B (fibreObj B g w hB) ℓ
      ((B.inclusion.map g).fiberToSpecResidueField w ≫ 𝟙 (Spec (.of (W.1.residueField w)))) jU kbar
      (LAdicSheaf.inverseImage (fibreι B g w hB) G) r)] :
    (LAdicSheaf.rationalStalkFrobenius B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) w
        hw).charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ
        ((B.inclusion.map g).fiberToSpecResidueField w ≫ 𝟙 (Spec (.of (W.1.residueField w)))) jU
        kbar p n hcard (LAdicSheaf.inverseImage (fibreι B g w hB) G) r).hom.charpoly := by
  have := hcond.fst
  -- notation
  let κ := W.1.residueField w
  let P := BigEtaleSite.specField B W κ
  let i : P ⟶ W := residueFieldPointHom B w
  let R := LAdicSheaf.higherDirectImageShriek B ℓ g jg G r
  let F' := LAdicSheaf.flatModel B ℓ G
  let Uw := fibreObj B g w hB
  let ιw : Uw ⟶ U := fibreι B g w hB
  let jP := CompactificationOf.ofProper (𝟙 (Spec (.of κ)))
  let H0 := compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of κ))) jP kbar 0
  let Fr0 := compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of κ))) jP kbar p n hcard 0
  let fw := (B.inclusion.map g).fiberToSpecResidueField w ≫ 𝟙 (Spec (.of κ))
  let Hr := compactSupportSheafCohomology ℤ_[ℓ] fw jU kbar r
  let Frr := compactSupportSheafFrobenius ℤ_[ℓ] fw jU kbar p n hcard r
  let Φ := etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map i) ⋙ H0
  let φΦ : Φ ⟶ Φ :=
    Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map i)) Fr0
  let L := LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r
  let Pt := IsLPowerTorsion ℓ U.1
  let Pw := IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)
  have hP : ∀ Q, Pt Q → ∃ m : ℕ, 0 < m ∧ m • 𝟙 Q = 0 := fun Q ⟨N, hN⟩ =>
    ⟨ℓ ^ N, pow_pos (Fact.out : ℓ.Prime).pos N, hN⟩
  let sq : IsPullback (B.inclusion.map ιw) ((B.inclusion.map g).fiberToSpecResidueField w)
      (B.inclusion.map g) (B.inclusion.map i) :=
    IsPullback.of_hasPullback (B.inclusion.map g) (W.1.fromSpecResidueField w)
  let BC := lowerShriekHomologyBaseChangeIso ℤ_[ℓ] sq jg jgw Pt hP r
  let tors : ℕᵒᵖ ⥤ Pt.FullSubcategory := LAdicSheaf.flatModelTorsionTower G
  let tors' : ℕᵒᵖ ⥤ Pw.FullSubcategory :=
    ObjectProperty.lift _ (tors ⋙ Pt.ι ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map ιw))
      (fun m => ⟨m.unop + 1, by
        change ℓ ^ (m.unop + 1) • 𝟙 ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
          (B.inclusion.map ιw)).obj (towerObj (LAdicSheaf.padicTower B U ℓ F') m.unop)) = 0
        rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
          LAdicSheaf.padicTower_annihilated B U ℓ F' m.unop, Functor.map_zero]⟩)
  -- the isomorphisms of towers
  let e₁ := Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ i R) H0
  let e₂ := Functor.isoWhiskerRight (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r
    hcond).symm Φ
  let α₃ := Functor.whiskerRight L.stableImageι Φ
  have : IsIso (limMap α₃) := L.isIso_limMap_whiskerRight_stableImageι Φ
  have hα₃ : IsIso ((rationalLim.{u + 1} (ℓ := ℓ)).map α₃) := by
    change IsIso ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map (limMap α₃))
    infer_instance
  let e₃ := @asIso _ _ _ _ ((rationalLim.{u + 1} (ℓ := ℓ)).map α₃) hα₃
  let e₄ := Functor.isoWhiskerLeft tors (Functor.isoWhiskerRight BC H0)
  let e₅ := Functor.isoWhiskerLeft tors' Ψ
  let e₆ := Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ ιw F') Hr
  let e₇ := (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
    (LAdicSheaf.padicTowerCohomologyIso B Uw ℓ fw jU kbar (LAdicSheaf.inverseImage ιw F') r)
  let eG := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B Uw ℓ fw jU kbar
    (LAdicSheaf.inverseImageMap ιw (LAdicSheaf.fromTorsionFreeModel G (LAdicSheaf.torsionBound G)))
    (LAdicSheaf.inverseImageMap ιw (LAdicSheaf.toTorsionFreeModel G (LAdicSheaf.torsionBound G)))
    (LAdicSheaf.torsionBound G) (by
      change (LAdicSheaf.inverseImageFunctor ιw).map _ ≫
        (LAdicSheaf.inverseImageFunctor ιw).map _ = _
      rw [← Functor.map_comp, LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel,
        Functor.map_nsmul, CategoryTheory.Functor.map_id]
      rfl) (by
      change (LAdicSheaf.inverseImageFunctor ιw).map _ ≫
        (LAdicSheaf.inverseImageFunctor ιw).map _ = _
      rw [← Functor.map_comp, LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel,
        Functor.map_nsmul, CategoryTheory.Functor.map_id]
      rfl) r
  -- finite dimensionality along the chain
  have hF7 : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      (k := κ) B Uw ℓ fw jU kbar (LAdicSheaf.inverseImage ιw F') r) :=
    finiteDimensional_of_iso eG.symm inferInstance
  have hF6 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B Uw ℓ (LAdicSheaf.inverseImage ιw F') ⋙ Hr)) :=
    finiteDimensional_of_iso e₇.symm hF7
  have hF5 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (tors' ⋙ Pw.ι ⋙ Hr)) :=
    finiteDimensional_of_iso ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso e₆).symm hF6
  have hF4 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (tors' ⋙ Pw.ι ⋙ lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w)
        jgw r ⋙ H0)) :=
    finiteDimensional_of_iso ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso e₅).symm hF5
  have hF3 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.lowerShriekTower B ℓ g jg G r ⋙ Φ)) :=
    finiteDimensional_of_iso ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso e₄) hF4
  have hF2 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (L.stableImageTower ⋙ Φ)) :=
    finiteDimensional_of_iso e₃.symm hF3
  have hF1 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B W ℓ R ⋙ Φ)) :=
    finiteDimensional_of_iso ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso e₂) hF2
  have hF0 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B P ℓ (LAdicSheaf.inverseImage i R) ⋙ H0)) :=
    finiteDimensional_of_iso ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso e₁) hF1
  have hFP : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      (k := κ) B P ℓ (𝟙 _) jP kbar (LAdicSheaf.inverseImage i R) 0) :=
    finiteDimensional_of_iso ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (LAdicSheaf.padicTowerCohomologyIso B P ℓ (𝟙 _) jP kbar
        (LAdicSheaf.inverseImage i R) 0)) hF0
  calc (LAdicSheaf.rationalStalkFrobenius B W ℓ R w hw).charpoly
      _ = (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := κ) B P ℓ (𝟙 _) jP kbar p n
          hcard (LAdicSheaf.inverseImage i R) 0).hom.charpoly :=
        @LAdicSheaf.charpoly_rationalStalkFrobenius_eq_residueField B ℓ _ _ _ _ W _ R w _ hw kbar _
          _ _ p n _ _ hcard hFP
      _ = ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
          (LAdicSheaf.padicTower B P ℓ (LAdicSheaf.inverseImage i R)) Fr0)).hom.charpoly :=
        (charpoly_rationalLim_map_eq_of_iso hF0 hFP
          (LAdicSheaf.padicTowerCohomologyIso B P ℓ (𝟙 _) jP kbar (LAdicSheaf.inverseImage i R) 0)
          _ _ (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B P ℓ (𝟙 _) jP kbar p n hcard
            (LAdicSheaf.inverseImage i R) 0)).symm
      _ = ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
          (LAdicSheaf.padicTower B W ℓ R) φΦ)).hom.charpoly :=
        (charpoly_rationalLim_map_eq_of_iso hF1 hF0 e₁ _ _ (by
          refine NatTrans.ext (funext fun m => ?_)
          exact
            (Fr0.naturality ((LAdicSheaf.padicTowerInverseImageIso B ℓ i R).hom.app m)).symm)).symm
      _ = ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
          L.stableImageTower φΦ)).hom.charpoly :=
        (charpoly_rationalLim_map_eq_of_iso hF2 hF1 e₂ _ _ (by
          refine NatTrans.ext (funext fun m => ?_)
          exact (φΦ.naturality ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r
            hcond).inv.app m)).symm)).symm
      _ = ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
          (LAdicSheaf.lowerShriekTower B ℓ g jg G r) φΦ)).hom.charpoly :=
        charpoly_eq_of_comm_iso hF2 hF3 e₃ _ _ (by
          change (rationalLim.{u + 1} (ℓ := ℓ)).map _ ≫ (rationalLim.{u + 1} (ℓ := ℓ)).map α₃ =
            (rationalLim.{u + 1} (ℓ := ℓ)).map α₃ ≫ (rationalLim.{u + 1} (ℓ := ℓ)).map _
          rw [← Functor.map_comp, ← Functor.map_comp]
          congr 1
          refine NatTrans.ext (funext fun m => ?_)
          exact (φΦ.naturality (L.stableImageι.app m)).symm)
      _ = ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft tors' (Functor.whiskerLeft Pw.ι
          (Functor.whiskerLeft (lowerShriekHomology ℤ_[ℓ]
            ((B.inclusion.map g).fiberToSpecResidueField w) jgw r) Fr0)))).hom.charpoly :=
        (charpoly_rationalLim_map_eq_of_iso hF4 hF3 e₄ _ _
          (by
            refine NatTrans.ext (funext fun m => ?_)
            exact (Fr0.naturality (BC.hom.app (tors.obj m))).symm)).symm
      _ = ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft tors'
          (Functor.whiskerLeft Pw.ι Frr))).hom.charpoly :=
        charpoly_rationalLim_map_eq_of_iso hF4 hF5 e₅ _ _
          (by refine NatTrans.ext (funext fun m => ?_); exact NatTrans.congr_app hΨ (tors'.obj m))
      _ = ((rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
          (LAdicSheaf.padicTower B Uw ℓ (LAdicSheaf.inverseImage ιw F')) Frr)).hom.charpoly :=
        charpoly_rationalLim_map_eq_of_iso hF5 hF6 e₆ _ _ (by
          refine NatTrans.ext (funext fun m => ?_)
          exact (Frr.naturality ((LAdicSheaf.padicTowerInverseImageIso B ℓ ιw F').hom.app m)).symm)
      _ = (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := κ) B Uw ℓ fw jU kbar p n
          hcard (LAdicSheaf.inverseImage ιw F') r).hom.charpoly :=
        charpoly_rationalLim_map_eq_of_iso hF6 hF7
          (LAdicSheaf.padicTowerCohomologyIso B Uw ℓ fw jU kbar (LAdicSheaf.inverseImage ιw F') r)
          _ _ (LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B Uw ℓ fw jU kbar p n hcard
            (LAdicSheaf.inverseImage ιw F') r)
      _ = (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := κ) B Uw ℓ fw jU kbar p n
          hcard (LAdicSheaf.inverseImage ιw G) r).hom.charpoly :=
        charpoly_eq_of_comm_iso hF7 inferInstance eG _ _
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback B Uw ℓ fw
            jU kbar _ _ _ _ _ r _).symm

end Core

/-! ### The stalk input -/

section Input

/-- Finite dimensionality of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is unchanged when the structure morphism is
replaced by an equal one, the compactification being transported. -/
theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_congr
    (X : B.Scheme) [IsNoetherian X.1] {k : Type u} [Field k]
    {f₁ f₂ : X.1 ⟶ Spec (.of k)} [LocallyOfFiniteType f₁] [QuasiCompact f₁] [IsSeparated f₁]
    [LocallyOfFiniteType f₂] [QuasiCompact f₂] [IsSeparated f₂] (h : f₁ = f₂)
    (j₁ : CompactificationOf (Over.mk f₁)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
    (h₂ : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f₂ (h ▸ j₁) kbar F i)) :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f₁ j₁ kbar F i) := by
  subst h
  exact h₂

/-- The characteristic polynomial of `π^*` on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is unchanged when the structure
morphism is replaced by an equal one, the compactification being transported. -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_congr
    (X : B.Scheme) [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
    {f₁ f₂ : X.1 ⟶ Spec (.of k)} [LocallyOfFiniteType f₁] [QuasiCompact f₁] [IsSeparated f₁]
    [LocallyOfFiniteType f₂] [QuasiCompact f₂] [IsSeparated f₂] (h : f₁ = f₂)
    (j₁ : CompactificationOf (Over.mk f₁)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f₁ j₁ kbar F i)]
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f₂ (h ▸ j₁) kbar F i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f₁ j₁ kbar p q hcard F
        i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f₂ (h ▸ j₁) kbar p q hcard F
        i).hom.charpoly := by
  subst h
  rfl

/-- **The stalk input of the induction step of Weil II for `Rʳ g_! G`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); proper base change, Tag 0F7L): at a closed
point `w` of `W`, the characteristic polynomial of the geometric Frobenius on
`(Rʳ g_! G)_w̄ ⊗ ℚ_ℓ` is that of the Frobenius of `κ(w)` on `Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ)`, for
one compactification of the fibre `U_w` over `κ(w)` serving every `G` and `r`. The inputs are the
constructibility of the `Rⁿ g_!` of constructible torsion sheaves (Tag 0GL0,
`Stacks.EtaleCohomology.LowerShriekConstructibilityInput`), which makes `Rʳ g_! G` the ℓ-adic sheaf
of the stable images, and the Leray comparison with Frobenius
(`Stacks.EtaleCohomology.LAdicSheaf.LerayFrobeniusComparison`, Tags 0F7J and 0F7L), used for the
fibre over `Spec κ(w)`. -/
theorem LAdicSheaf.higherDirectImageStalkInput_higherDirectImageShriek
    (hC : LowerShriekConstructibilityInput B)
    (hL : ∀ {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
      [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
      [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
      {k : Type u} [Field k] [Fintype k] (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
      [QuasiCompact fW] [IsSeparated fW] (jW : CompactificationOf (Over.mk fW))
      (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
      (hcard : Fintype.card k = p ^ q),
      LAdicSheaf.LerayFrobeniusComparison B ℓ g jg fW jW kbar p q hcard) :
    LAdicSheaf.HigherDirectImageStalkInput (LAdicSheaf.higherDirectImageShriekFamily B ℓ) := by
  intro k _ _ U W _ _ g _ _ _ jg fW _ w hB _ _ _ _ _ kbar _ _ _ p n _ _ hcard
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed (W.1.residueField w.1)
  let gw := fibreToResidueField B g w.1 hB
  have : LocallyOfFiniteType (B.inclusion.map gw) :=
    ‹LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w.1)›
  have : QuasiCompact (B.inclusion.map gw) :=
    ‹QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w.1)›
  have : IsSeparated (B.inclusion.map gw) :=
    ‹IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w.1)›
  have hdim : topologicalKrullDim (BigEtaleSite.specField B W (W.1.residueField w.1)).1 ≤ 0 :=
    topologicalKrullDim_le_zero_of_isFinite (𝟙 (Spec (.of (W.1.residueField w.1))))
  let sq : IsPullback (B.inclusion.map (fibreι B g w.1 hB))
      ((B.inclusion.map g).fiberToSpecResidueField w.1) (B.inclusion.map g)
      (W.1.fromSpecResidueField w.1) :=
    IsPullback.of_hasPullback (B.inclusion.map g) (W.1.fromSpecResidueField w.1)
  let jgw := jg.baseChange sq
  obtain ⟨jU, hΨ⟩ := LAdicSheaf.exists_lowerShriekHomology_compactSupportSheafCohomology_iso B ℓ
    gw jgw (𝟙 (Spec (.of (W.1.residueField w.1)))) (CompactificationOf.ofProper (𝟙 _)) kbar p n
    hcard hdim (hL gw jgw (𝟙 _) (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard)
  have hf : (B.inclusion.map g).fiberToSpecResidueField w.1 ≫
      𝟙 (Spec (.of (W.1.residueField w.1))) = (B.inclusion.map g).fiberToSpecResidueField w.1 :=
    Category.comp_id _
  refine ⟨hf ▸ jU, fun G r _ => ?_⟩
  obtain ⟨Ψ, hΨr⟩ := hΨ r
  have := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_congr B ℓ
    (fibreObj B g w.1 hB) hf jU kbar (LAdicSheaf.inverseImage (fibreι B g w.1 hB) G) r inferInstance
  exact (LAdicSheaf.charpoly_rationalStalkFrobenius_higherDirectImageShriek B ℓ g jg w.1 hB kbar p n
    hcard G r (LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput B ℓ
      g jg hC G r) _ jgw jU Ψ hΨr).trans
    (LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_congr B ℓ
      (fibreObj B g w.1 hB) hf jU kbar p n hcard _ r)

end Input

end Stacks.EtaleCohomology
