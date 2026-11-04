module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientHigherDirectImageStalkLinearIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageStalkChainNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ResiduePointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicStalkSheafFiberLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LerayFrobeniusComparisonDischarge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional

/-!
# `E`-linear proper base change at a stalk

Let `g : U ⟶ W` be separated of finite type with a compactification, `w` a point of `W` with
finite residue field `κ`, `U_w` the fibre, `G` an ℓ-adic sheaf on `U` and `R = Rʳ g_! G`. The
rational stalk `ℚ_ℓ ⊗ R_w̄` maps to `Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ)`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageStalkComparison`): the ℓ-adic stalk embeds
into the limit of the stalks of the levels on Mathlib's site, these into `H⁰_c(Spec κ̄, i⁻¹ Rₙ)`,
and the proper base change chain of
`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageStalkChainIso`
([Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L),
[Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)) identifies the rational limit of the latter
with `Hʳ_c`. The map is injective, carries the geometric Frobenius at `w` to the Frobenius of `κ`
and the endomorphism of `R` induced by any `φ : G ⟶ G` to the one induced on `G|_{U_w}`.
Comparing dimensions through the characteristic polynomials of the Frobenius
(`Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkFrobenius_higherDirectImageShriek`), it
is bijective; commuting with the action of `O`, its inverse is `E`-linear for `E = O[1/ℓ]`. This
proves `Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearIsoInput`, the stalk input of
the specialization and purity steps of Laumon's degeneration
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageStalkComparison`, with
  `Stacks.EtaleCohomology.LAdicSheaf.bijective_higherDirectImageStalkComparison`.
* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.exists_higherDirectImageStalkLinearEquiv`.
* `Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearIsoInput`.
* `Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearInput`.

## Implementation notes

The proper base change chain uses `Stacks.EtaleCohomology.derivedLowerShriek` in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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

/-- **Extension of scalars from `ℤ_ℓ` to `ℚ_ℓ` preserves injectivity**, `ℚ_ℓ` being flat. -/
theorem injective_extendScalars_padic_map {M N : ModuleCat.{u + 1} ℤ_[ℓ]} (f : M ⟶ N)
    (hf : Function.Injective f.hom) :
    Function.Injective
      ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map f).hom := by
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  show Function.Injective (LinearMap.lTensor ℚ_[ℓ] f.hom)
  exact Module.Flat.lTensor_preserves_injective_linearMap f.hom hf

/-! ### The stalk inside the limit of `H⁰_c(Spec κ̄, i⁻¹ Mₙ)` -/

section Stalk

variable {W : B.Scheme} [IsNoetherian W.1] (w : W.1) [Fintype (W.1.residueField w)]
  (kbar : Type u) [Field kbar] [Algebra (W.1.residueField w) kbar]
  [IsAlgClosure (W.1.residueField w) kbar] (p n : ℕ) [Fact p.Prime] [CharP (W.1.residueField w) p]
  (hcard : Fintype.card (W.1.residueField w) = p ^ n)

/-- **The ℓ-adic stalk at `w̄` maps into `lim_n H⁰_c(Spec κ̄, i⁻¹ Mₙ)`**, `i : Spec κ(w) ⟶ W`:
the stalk into the limit of the stalks of the levels, then the embeddings of the stalks of the
levels into `H⁰_c(Spec κ̄, i⁻¹ -)`. -/
def LAdicSheaf.residuePointLimitMap (M : LAdicSheaf.{u, u + 1} B W ℓ) :
    ModuleCat.of ℤ_[ℓ] (LAdicSheaf.stalk B W ℓ M (geometricPointAt W.1 (residuePointImage B w))) ⟶
      limit (LAdicSheaf.padicTower B W ℓ M ⋙ residuePointCohomology B ℓ w kbar) :=
  LAdicSheaf.stalkSheafFiberLimitMap _ M ≫ limMap (Functor.whiskerLeft
    (LAdicSheaf.padicTower B W ℓ M) (residuePointStalkEmbedding B ℓ w kbar p n hcard))

/-- **The map of the ℓ-adic stalk at `w̄` into `lim_n H⁰_c(Spec κ̄, i⁻¹ Mₙ)` is injective.** -/
theorem LAdicSheaf.injective_residuePointLimitMap (M : LAdicSheaf.{u, u + 1} B W ℓ) :
    Function.Injective (LAdicSheaf.residuePointLimitMap B ℓ w kbar p n hcard M).hom := by
  have : ∀ j, Mono ((Functor.whiskerLeft (LAdicSheaf.padicTower B W ℓ M)
      (residuePointStalkEmbedding B ℓ w kbar p n hcard)).app j) := fun j =>
    (ModuleCat.mono_iff_injective _).2 (injective_residuePointStalkEmbedding_app B ℓ w kbar p n
      hcard _)
  have : Mono (Functor.whiskerLeft (LAdicSheaf.padicTower B W ℓ M)
      (residuePointStalkEmbedding B ℓ w kbar p n hcard)) := NatTrans.mono_of_mono_app _
  exact ((ModuleCat.mono_iff_injective _).1 (inferInstance : Mono (limMap (Functor.whiskerLeft
    (LAdicSheaf.padicTower B W ℓ M) (residuePointStalkEmbedding B ℓ w kbar p n hcard))))).comp
    (LAdicSheaf.injective_stalkSheafFiberLimitMap _ M)

/-- **The map into the limit carries the geometric Frobenius at `w` to the Frobenius of
`κ(w)`.** -/
theorem LAdicSheaf.stalkEnd_comp_residuePointLimitMap (M : LAdicSheaf.{u, u + 1} B W ℓ) :
    ModuleCat.ofHom (LAdicSheaf.stalkEnd B W ℓ M (frobeniusPointHom W.1 (residuePointImage B w))) ≫
        LAdicSheaf.residuePointLimitMap B ℓ w kbar p n hcard M =
      LAdicSheaf.residuePointLimitMap B ℓ w kbar p n hcard M ≫ limMap (Functor.whiskerLeft
        (LAdicSheaf.padicTower B W ℓ M) (residuePointFrobenius B ℓ w kbar p n hcard)) := by
  rw [LAdicSheaf.residuePointLimitMap, ← Category.assoc,
    LAdicSheaf.stalkSheafFiberLimitMap_stalkEnd, Category.assoc, Category.assoc]
  simp only [limMap_eq, ← Functor.map_comp]
  congr 2
  refine NatTrans.ext (funext fun j => ?_)
  exact frobeniusStalk_comp_residuePointStalkEmbedding_app B ℓ w kbar p n hcard _

/-- **The map into the limit is natural in the ℓ-adic sheaf.** -/
theorem LAdicSheaf.stalkMap_comp_residuePointLimitMap {M M' : LAdicSheaf.{u, u + 1} B W ℓ}
    (ψ : M ⟶ M') :
    ModuleCat.ofHom (LAdicSheaf.stalkMap ψ (geometricPointAt W.1 (residuePointImage B w))) ≫
        LAdicSheaf.residuePointLimitMap B ℓ w kbar p n hcard M' =
      LAdicSheaf.residuePointLimitMap B ℓ w kbar p n hcard M ≫ limMap (Functor.whiskerRight
        (LAdicSheaf.padicTowerMap ψ) (residuePointCohomology B ℓ w kbar)) := by
  rw [LAdicSheaf.residuePointLimitMap, LAdicSheaf.residuePointLimitMap, ← Category.assoc,
    LAdicSheaf.stalkSheafFiberLimitMap_stalkMap, Category.assoc, Category.assoc]
  simp only [limMap_eq, ← Functor.map_comp]
  congr 2
  refine NatTrans.ext (funext fun j => ?_)
  exact (residuePointStalkEmbedding B ℓ w kbar p n hcard).naturality _

end Stalk

/-! ### The comparison map at the stalk -/

section Chain

variable {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (w : W.1) [Fintype (W.1.residueField w)] (hB : B.Contains ((B.inclusion.map g).fiber w))
  [IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)]
  (kbar : Type u) [Field kbar] [Algebra (W.1.residueField w) kbar] [IsAlgClosed kbar]
  [IsAlgClosure (W.1.residueField w) kbar] (p n : ℕ)
  [Fact p.Prime] [CharP (W.1.residueField w) p] (hcard : Fintype.card (W.1.residueField w) = p ^ n)
  (G : LAdicSheaf.{u, u + 1} B U ℓ) (r : ℕ)
  (hcond : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r)
  (jgw : CompactificationOf (Over.mk ((B.inclusion.map g).fiberToSpecResidueField w)))
  (jU : CompactificationOf (Over.mk (fibreStructureResidueField B g w)))
  (Ψ : (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
          (CompactificationOf.ofProper (𝟙 _)) kbar 0 ≅
      (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r)

/-- **The comparison map at the stalk**: `ℚ_ℓ ⊗ (Rʳ g_! G)_w̄ → Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ)`,
the rationalization of the map of the stalk into `lim_n H⁰_c(Spec κ̄, i⁻¹ Rₙ)` followed by the
proper base change chain. -/
def LAdicSheaf.higherDirectImageStalkComparison :
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℤ_[ℓ] (LAdicSheaf.stalk B W ℓ
          (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)
          (geometricPointAt W.1 (residuePointImage B w)))) ⟶
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar
        (LAdicSheaf.inverseImage (fibreι B g w hB) G) r :=
  (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      (LAdicSheaf.residuePointLimitMap B ℓ w kbar p n hcard
        (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)) ≫
    (LAdicSheaf.higherDirectImageStalkChainIso B ℓ g jg w hB kbar G r hcond jgw jU Ψ).hom

omit [IsAlgClosed kbar] in
/-- **The comparison map `ℚ_ℓ ⊗ (Rʳ g_! G)_w̄ → Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ)` is injective.** -/
theorem LAdicSheaf.injective_higherDirectImageStalkComparison :
    Function.Injective (LAdicSheaf.higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard G r
      hcond jgw jU Ψ).hom :=
  (ConcreteCategory.bijective_of_isIso
      (LAdicSheaf.higherDirectImageStalkChainIso B ℓ g jg w hB kbar G r hcond jgw jU Ψ).hom).1.comp
    (injective_extendScalars_padic_map ℓ _ (LAdicSheaf.injective_residuePointLimitMap B ℓ w kbar p n
      hcard _))

omit [IsAlgClosed kbar] in
/-- **The comparison map carries the geometric Frobenius at `w` to the Frobenius of `κ(w)`**,
given the Leray comparison `Ψ` with Frobenius. -/
theorem LAdicSheaf.higherDirectImageStalkComparison_frobenius
    (hΨ : Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (Functor.whiskerLeft
          (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
          (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
            (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0)) ≫ Ψ.hom =
      Ψ.hom ≫ Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (compactSupportSheafFrobenius ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar p n hcard
          r)) :
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map (ModuleCat.ofHom
        (LAdicSheaf.stalkEnd B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)
          (frobeniusPointHom W.1 (residuePointImage B w)))) ≫
        LAdicSheaf.higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard G r hcond jgw jU
          Ψ =
      LAdicSheaf.higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard G r hcond jgw jU Ψ ≫
        LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B
          (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar p n hcard
          (LAdicSheaf.inverseImage (fibreι B g w hB) G) r :=
  comm_comp_of_comm (functor_map_comp_eq_of_comp_eq
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ]))
      (LAdicSheaf.stalkEnd_comp_residuePointLimitMap B ℓ w kbar p n hcard _))
    (LAdicSheaf.higherDirectImageStalkChainIso_frobenius B ℓ g jg w hB kbar p n hcard G r hcond jgw
      jU Ψ hΨ)

omit [IsAlgClosed kbar] in
/-- **The comparison map is natural in `G`**: it carries the endomorphism of `Rʳ g_! G` induced by
`φ : G ⟶ G` to the endomorphism of `G|_{U_w}` induced by `φ`. -/
theorem LAdicSheaf.higherDirectImageStalkComparison_naturality (φ : G ⟶ G) :
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map (ModuleCat.ofHom
        (LAdicSheaf.stalkMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ)
          (geometricPointAt W.1 (residuePointImage B w)))) ≫
        LAdicSheaf.higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard G r hcond jgw jU
          Ψ =
      LAdicSheaf.higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard G r hcond jgw jU Ψ ≫
        (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (LAdicSheaf.geometricCompactlySupportedCohomologyMap (X := fibreObj B g w hB)
            (fibreStructureResidueField B g w) jU kbar
            (LAdicSheaf.inverseImageMap (fibreι B g w hB) φ) r) :=
  comm_comp_of_comm (functor_map_comp_eq_of_comp_eq
      (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ]))
      (LAdicSheaf.stalkMap_comp_residuePointLimitMap B ℓ w kbar p n hcard _))
    (LAdicSheaf.higherDirectImageStalkChainIso_naturality B ℓ g jg w hB kbar G r hcond jgw jU Ψ φ)

omit [IsAlgClosure (W.1.residueField w) kbar] in
include hcard hcond Ψ in
/-- **`Hʳ_c(U_{w,κ̄}, G|_{U_w} ⊗ ℚ_ℓ)` is finite dimensional**: through the proper base change
chain it is `H⁰_c(Spec κ̄, i⁻¹ Rʳ g_! G ⊗ ℚ_ℓ)`, finite dimensional since `Spec κ` is finite étale
over `κ`. -/
theorem LAdicSheaf.finiteDimensional_higherDirectImageStalkChain :
    FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      (k := W.1.residueField w) B (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar
      (LAdicSheaf.inverseImage (fibreι B g w hB) G) r) := by
  let R := LAdicSheaf.higherDirectImageShriek B ℓ g jg G r
  let P := BigEtaleSite.specField B W (W.1.residueField w)
  let i : P ⟶ W := residueFieldPointHom B w
  let jP := CompactificationOf.ofProper (𝟙 (Spec (.of (W.1.residueField w))))
  let H0 := compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w)))) jP kbar 0
  have hFP : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B P ℓ (𝟙 _) jP kbar
        (LAdicSheaf.inverseImage i R) 0)) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_etale B ℓ P (𝟙 _)
      jP kbar p n hcard _ 0
  have hF0 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B P ℓ (LAdicSheaf.inverseImage i R) ⋙ H0)) :=
    LinearEquiv.finiteDimensional ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (LAdicSheaf.padicTowerCohomologyIso B P ℓ (𝟙 _) jP kbar (LAdicSheaf.inverseImage i R)
        0)).symm.toLinearEquiv
  have hF1 : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.padicTower B W ℓ R ⋙ residuePointCohomology B ℓ w kbar)) :=
    LinearEquiv.finiteDimensional ((rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (Functor.isoWhiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ i R)
        H0)).symm.toLinearEquiv
  exact LinearEquiv.finiteDimensional
    (LAdicSheaf.higherDirectImageStalkChainIso B ℓ g jg w hB kbar G r hcond jgw jU Ψ).toLinearEquiv

/-- **The comparison map at the stalk is bijective**, the rational stalk being finite dimensional:
it is injective, and both sides have the dimension of the degree of the characteristic polynomial
of the Frobenius, which agree by
`Stacks.EtaleCohomology.LAdicSheaf.charpoly_rationalStalkFrobenius_higherDirectImageShriek`. -/
theorem LAdicSheaf.bijective_higherDirectImageStalkComparison
    (hΨ : Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (Functor.whiskerLeft
          (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
          (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
            (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0)) ≫ Ψ.hom =
      Ψ.hom ≫ Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (compactSupportSheafFrobenius ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar p n hcard r))
    [hS : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ
      (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)
      (geometricPointAt W.1 (residuePointImage B w)))] :
    Function.Bijective (LAdicSheaf.higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard G r
      hcond jgw jU Ψ).hom := by
  let R := LAdicSheaf.higherDirectImageShriek B ℓ g jg G r
  have hH := LAdicSheaf.finiteDimensional_higherDirectImageStalkChain B ℓ g jg w hB kbar p n hcard
    G r hcond jgw jU Ψ
  have key : ∀ x : W.1, x = w →
      FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ R (geometricPointAt W.1 x)) ∧
        Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ R (geometricPointAt W.1 x)) =
          Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ R
            (geometricPointAt W.1 (residuePointImage B w))) := by
    intro x hx
    rw [← residuePointImage_eq B w] at hx
    subst hx
    exact ⟨hS, rfl⟩
  obtain ⟨hSw, hfin⟩ := key w rfl
  have hdeg := congrArg Polynomial.natDegree
    (LAdicSheaf.charpoly_rationalStalkFrobenius_higherDirectImageShriek B ℓ g jg w hB kbar p n hcard
      G r hcond inferInstance jgw jU Ψ hΨ)
  rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree, hfin] at hdeg
  have hinj := LAdicSheaf.injective_higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard
    G r hcond jgw jU Ψ
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdeg).1 hinj⟩

end Chain

/-! ### With coefficients -/

section Coefficient

variable {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (w : W.1) [Fintype (W.1.residueField w)] (hB : B.Contains ((B.inclusion.map g).fiber w))
  [IsNoetherian ((B.inclusion.map g).fiber w)]
  [LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w)]
  [QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w)]
  [IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w)]
  (kbar : Type u) [Field kbar] [Algebra (W.1.residueField w) kbar] [IsAlgClosed kbar]
  [IsAlgClosure (W.1.residueField w) kbar] (p n : ℕ)
  [Fact p.Prime] [CharP (W.1.residueField w) p] (hcard : Fintype.card (W.1.residueField w) = p ^ n)
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B U ℓ O) (r : ℕ)
  (hcond : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg F.toLAdicSheaf r)
  (jgw : CompactificationOf (Over.mk ((B.inclusion.map g).fiberToSpecResidueField w)))
  (jU : CompactificationOf (Over.mk (fibreStructureResidueField B g w)))
  (Ψ : (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
          (CompactificationOf.ofProper (𝟙 _)) kbar 0 ≅
      (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar r)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra O E] [IsLocalization (Submonoid.powers (ℓ : O)) E]

include hcond in
/-- **`E`-linear proper base change at the stalk, at the point `x = w`**: the inverse of the
comparison map is an `E`-linear isomorphism `Hʳ_c(U_{w,κ̄}, F|_{U_w} ⊗ ℚ_ℓ) ≃ ℚ_ℓ ⊗ (Rʳ g_! F)_x̄`
carrying the Frobenius of `κ(w)` to the geometric Frobenius at `x`, given the Leray comparison
`Ψ` with Frobenius. It commutes with the action of `O` by naturality, hence with that of `E`. -/
theorem LAdicSheaf.CoefficientSheaf.exists_higherDirectImageStalkLinearEquiv
    (hΨ : Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (Functor.whiskerLeft
          (lowerShriekHomology ℤ_[ℓ] ((B.inclusion.map g).fiberToSpecResidueField w) jgw r)
          (compactSupportSheafFrobenius ℤ_[ℓ] (𝟙 (Spec (.of (W.1.residueField w))))
            (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard 0)) ≫ Ψ.hom =
      Ψ.hom ≫ Functor.whiskerLeft (IsLPowerTorsion ℓ ((B.inclusion.map g).fiber w)).ι
        (compactSupportSheafFrobenius ℤ_[ℓ] (fibreStructureResidueField B g w) jU kbar p n hcard r))
    (x : W.1) (hx : residuePointImage B w = x) (hxf : Finite (W.1.residueField x))
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B W ℓ
      (F.higherDirectImageShriek B ℓ g jg r).toLAdicSheaf (geometricPointAt W.1 x))] :
    letI := (F.higherDirectImageShriek B ℓ g jg r).rationalStalkModule (geometricPointAt W.1 x) E
    letI := (LAdicSheaf.CoefficientSheaf.inverseImage (fibreι B g w hB) F).rationalCohomologyModule
      (fibreStructureResidueField B g w) jU kbar r E
    ∃ Θ : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B (fibreObj B g w hB) ℓ
        (fibreStructureResidueField B g w) jU kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage (fibreι B g w hB) F).toLAdicSheaf r ≃ₗ[E]
        LAdicSheaf.rationalStalkLeft B W ℓ (F.higherDirectImageShriek B ℓ g jg r).toLAdicSheaf
          (geometricPointAt W.1 x),
      Θ.toLinearMap ∘ₗ (LAdicSheaf.CoefficientSheaf.inverseImage (fibreι B g w hB)
          F).rationalGeometricCompactlySupportedFrobenius (fibreStructureResidueField B g w) jU kbar
          r E p n hcard =
        (F.higherDirectImageShriek B ℓ g jg r).rationalStalkFrobenius E x hxf ∘ₗ Θ.toLinearMap := by
  subst hx
  let R := (F.higherDirectImageShriek B ℓ g jg r).toLAdicSheaf
  let s := geometricPointAt W.1 (residuePointImage B w)
  let F' := LAdicSheaf.CoefficientSheaf.inverseImage (fibreι B g w hB) F
  let Θ₀ := LAdicSheaf.higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard
    F.toLAdicSheaf r hcond jgw jU Ψ
  have hbij := LAdicSheaf.bijective_higherDirectImageStalkComparison B ℓ g jg w hB kbar p n hcard
    F.toLAdicSheaf r hcond jgw jU Ψ hΨ
  let e₀ : LAdicSheaf.rationalStalkLeft B W ℓ R s ≃ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B (fibreObj B g w hB) ℓ
        (fibreStructureResidueField B g w) jU kbar F'.toLAdicSheaf r :=
    LinearEquiv.ofBijective Θ₀.hom hbij
  have he₀ : ∀ u, e₀ u = Θ₀.hom u := fun _ => rfl
  have hfrob : ∀ u, e₀ (LAdicSheaf.rationalStalkEnd B W ℓ R
      (frobeniusPointHom W.1 (residuePointImage B w)) u) =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w) B
        (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar p n hcard
        F'.toLAdicSheaf r).hom (e₀ u) := by
    intro u
    have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (LAdicSheaf.higherDirectImageStalkComparison_frobenius B ℓ g jg w hB kbar p n hcard
        F.toLAdicSheaf r hcond jgw jU Ψ hΨ)) u
    simp only [ModuleCat.hom_comp] at h1
    rw [he₀, he₀]
    exact h1
  have hnat : ∀ (o : O) u, e₀ ((F.higherDirectImageShriek B ℓ g jg r).rationalStalkIntegralRingHom
      s o u) =
      F'.rationalIntegralRingHom (fibreStructureResidueField B g w) jU kbar r o (e₀ u) := by
    intro o u
    have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (LAdicSheaf.higherDirectImageStalkComparison_naturality B ℓ g jg w hB kbar p n hcard
        F.toLAdicSheaf r hcond jgw jU Ψ (F.act o))) u
    simp only [ModuleCat.hom_comp] at h1
    exact h1
  let := (F.higherDirectImageShriek B ℓ g jg r).rationalStalkModule s E
  let := F'.rationalCohomologyModule (fibreStructureResidueField B g w) jU kbar r E
  have hT : ∀ (o : O) v,
      e₀.symm (F'.rationalIntegralRingHom (fibreStructureResidueField B g w) jU kbar r o v) =
        algebraMap O E o • e₀.symm v := by
    intro o v
    rw [LinearEquiv.symm_apply_eq]
    show _ = e₀ ((F.higherDirectImageShriek B ℓ g jg r).rationalStalkRingHom s E
      (algebraMap O E o) (e₀.symm v))
    rw [LAdicSheaf.CoefficientSheaf.rationalStalkRingHom_algebraMap_apply, hnat,
      LinearEquiv.apply_symm_apply]
  refine ⟨{ e₀.symm.toAddEquiv with
    map_smul' := fun c v => LAdicSheaf.CoefficientSheaf.map_rationalRingHom_of_integral F'
      (fibreStructureResidueField B g w) jU kbar r E e₀.symm.toLinearMap.toAddMonoidHom hT c
      v }, ?_⟩
  refine LinearMap.ext fun v => ?_
  show e₀.symm ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius (k := W.1.residueField w)
    B (fibreObj B g w hB) ℓ (fibreStructureResidueField B g w) jU kbar p n hcard F'.toLAdicSheaf
    r).hom v) =
    LAdicSheaf.rationalStalkEnd B W ℓ R (frobeniusPointHom W.1 (residuePointImage B w)) (e₀.symm v)
  rw [LinearEquiv.symm_apply_eq, hfrob, LinearEquiv.apply_symm_apply]

end Coefficient

/-! ### The proposition -/

/-- **`E`-linear proper base change at the stalks of `Rʳ g_!`, as an isomorphism** (Tags 0F7L,
0F7I, with coefficients; `Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearIsoInput`
holds): the fibre `Y = U ×_W Spec κ(w)`, with the compactification over `κ(w)` given by the
Leray comparison (`Stacks.EtaleCohomology.LAdicSheaf.lerayFrobeniusComparison`, Tags 0F7J, 0F7L),
and the inverse of the comparison map at the stalk
(`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.exists_higherDirectImageStalkLinearEquiv`),
`Rʳ g_! F` being the ℓ-adic sheaf of the stable images by the constructibility of the `Rⁿ g_!`
(Tag 0GL0, `Stacks.EtaleCohomology.lowerShriekConstructibilityInput`). -/
theorem coefficientHigherDirectImageStalkLinearIsoInput :
    CoefficientHigherDirectImageStalkLinearIsoInput.{u} := by
  intro B ℓ _ _ _ _ k _ _ U W _ _ g _ _ _ jg fW _ w _ kbar _ _ _ p n _ _ hcard C hC
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed (W.1.residueField w.1)
  have hSpec : B.Contains (Spec (W.1.residueField w.1)) :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      (W.1.fromSpecResidueField w.1) W.property
  have hB : B.Contains ((B.inclusion.map g).fiber w.1) :=
    Scheme.size_pullback_lt _ _ U.property hSpec
  have : LocallyOfFiniteType ((B.inclusion.map g).fiberToSpecResidueField w.1) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : QuasiCompact ((B.inclusion.map g).fiberToSpecResidueField w.1) :=
    inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have : IsSeparated ((B.inclusion.map g).fiberToSpecResidueField w.1) :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsNoetherian ((B.inclusion.map g).fiber w.1) :=
    isNoetherian_of_locallyOfFiniteType_over_field (k := W.1.residueField w.1)
      ((B.inclusion.map g).fiberToSpecResidueField w.1)
  have : IsNoetherian (fibreObj B g w.1 hB).1 := ‹IsNoetherian ((B.inclusion.map g).fiber w.1)›
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
    hcard hdim (LAdicSheaf.lerayFrobeniusComparison B ℓ gw jgw (𝟙 _)
      (CompactificationOf.ofProper (𝟙 _)) kbar p n hcard)
  have hpb : IsPullback (B.inclusion.map (fibreι B g w.1 hB)) (fibreStructureResidueField B g w.1)
      (B.inclusion.map g) (W.1.fromSpecResidueField w.1) := by
    show IsPullback _ ((B.inclusion.map g).fiberToSpecResidueField w.1 ≫ 𝟙 _) _ _
    rw [Category.comp_id]
    exact sq
  refine hC (fibreObj B g w.1 hB) (fibreι B g w.1 hB) (fibreStructureResidueField B g w.1) hpb jU ?_
  intro O _ _ F r E _ _ _ _ hOE _
  obtain ⟨Ψ, hΨr⟩ := hΨ r
  exact LAdicSheaf.CoefficientSheaf.exists_higherDirectImageStalkLinearEquiv B ℓ g jg w.1 hB kbar
    p n hcard F r (LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput
      B ℓ g jg (lowerShriekConstructibilityInput B) F.toLAdicSheaf r) jgw jU Ψ E hΨr w.1
    (residuePointImage_eq B w.1) _

/-- **`E`-linear proper base change at the stalks of `Rʳ g_!`, for characteristic polynomials**
(input (b) of the purity step of Laumon's degeneration,
`Stacks.EtaleCohomology.CoefficientHigherDirectImageStalkLinearInput`, holds): conjugation by the
isomorphism of `Stacks.EtaleCohomology.coefficientHigherDirectImageStalkLinearIsoInput`. -/
theorem coefficientHigherDirectImageStalkLinearInput :
    CoefficientHigherDirectImageStalkLinearInput.{u} :=
  coefficientHigherDirectImageStalkLinearInput_of_iso
    coefficientHigherDirectImageStalkLinearIsoInput

end Stacks.EtaleCohomology
