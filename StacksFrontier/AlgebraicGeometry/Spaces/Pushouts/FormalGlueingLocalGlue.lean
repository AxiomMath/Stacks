module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkCech
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointNeighborhoodLift
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceChartBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingOverlapTranspose

/-!
# The glueing datum of a triple at a point of `f⁻¹Z`

In Situation 0AEV let `ȳ` be a geometric point of `Y` and `x̄ = f(ȳ)`.  The stalkwise proof of
Stacks 0AF0 attaches to a glueing triple `t = (ℋ, 𝒢, φ)` an object of
`Glue(𝒪_{X,x̄} → 𝒪_{Y,ȳ}, f₁, …, f_r)` (Stacks 05EL); in this development that object is
`FormalGlueing.pullbackDatum` of the data

* `N = (j_*ℋ)_x̄` (`localN`), `P = 𝒢_ȳ` (`localP`), `Q = (j'_*𝒢|_V)_ȳ` (`localQ`),
* `b : P → Q`, the stalk of the unit `𝒢 → j'_*𝒢|_V` (`localB`),
* `a : 𝒪_{Y,ȳ} ⊗ N → Q`, the stalk of the map `f^*j_*ℋ → j'_*𝒢|_V` of the triple
  (`overlapTranspose`) read through `(f^*j_*ℋ)_ȳ = 𝒪_{Y,ȳ} ⊗ (j_*ℋ)_x̄` (`localA`).

`FormalGlueing.pullbackDatum` asks that `a` and `b` become bijective after inverting each
generator; this file proves both, for generators given on a neighbourhood of `ȳ` as functions
whose zero locus is the point set of `f⁻¹Z`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.bijective_localizedMap_localB`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.bijective_localizedMap_localA`.

Both are instances of
`AlgebraicGeometry.Space.bijective_localizedMap_of_isIso_modulePullback_of_heq`: the unit of
`j'^* ⊣ j'_*` and the map of the triple are invertible over `V`
(`isIso_modulePullback_map_unit_of_isOpenImmersion`,
`isIso_modulePullback_map_overlapTranspose`), and the basic opens of the generators lie in `V`
(`range_pointsMap_openChart_basicOpen_subset`).

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 05EL](https://stacks.math.columbia.edu/tag/05EL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS) (y : GeometricPoint B S hS D.spaceY.1)

/-- The étale local ring `𝒪_{X, x̄}` at the image `x̄ = f(ȳ)`. -/
abbrev localRingX : CommRingCat.{u + 1} :=
  etaleLocalRing B S hS D.spaceX.1 (geometricPointMap D.ambientMorphism.hom y)

/-- The étale local ring `𝒪_{Y, ȳ}`. -/
abbrev localRingY : CommRingCat.{u + 1} := etaleLocalRing B S hS D.spaceY.1 y

/-- `𝒪_{Y,ȳ}` as an `𝒪_{X,x̄}`-algebra through the map of étale local rings induced by `f`. -/
instance localAlgebra : Algebra (D.localRingX y) (D.localRingY y) :=
  (etaleLocalRingMap D.spaceY.2 D.ambientMorphism.hom y).toAlgebra

/-- The localization of a composite is the composite of the localizations. -/
theorem _root_.LocalizedModule.map_comp_apply {R : Type*} [CommRing R] (T : Submonoid R)
    {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (h : M →ₗ[R] N) (k : N →ₗ[R] P) (z : LocalizedModule T M) :
    LocalizedModule.map T (k ∘ₗ h) z = LocalizedModule.map T k (LocalizedModule.map T h z) := by
  induction z using LocalizedModule.induction_on with
  | h m c => simp only [LocalizedModule.map_mk, LinearMap.comp_apply]

/-- The localization of a bijective linear map is bijective. -/
theorem _root_.LocalizedModule.map_bijective {R : Type*} [CommRing R] (T : Submonoid R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : Function.Bijective (LocalizedModule.map T e.toLinearMap) := by
  refine Function.bijective_iff_has_inverse.2 ⟨LocalizedModule.map T e.symm.toLinearMap, ?_, ?_⟩
  · intro z
    induction z using LocalizedModule.induction_on with
    | h m c => simp [LocalizedModule.map_mk]
  · intro z
    induction z using LocalizedModule.induction_on with
    | h m c => simp [LocalizedModule.map_mk]

/-- `N = (j_*ℋ)_x̄`. -/
abbrev localN (t : D.moduleGlueingComma) : ModuleCat (D.localRingX y) :=
  geometricModuleStalk B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y)
    ((modulePushforward B S hS D.openImmersion).obj t.left)

/-- `P = 𝒢_ȳ`. -/
abbrev localP (t : D.moduleGlueingComma) : ModuleCat (D.localRingY y) :=
  geometricModuleStalk B S hS D.spaceY y t.right

/-- `Q = (j'_*𝒢|_V)_ȳ`. -/
abbrev localQ (t : D.moduleGlueingComma) : ModuleCat (D.localRingY y) :=
  geometricModuleStalk B S hS D.spaceY y
    ((modulePushforward B S hS D.openImmersionOver).obj
      ((modulePullback B S hS D.openImmersionOver).obj t.right))

/-- The unit `𝒢 ⟶ j'_*j'^*𝒢` of a triple. -/
def overlapUnit (t : D.moduleGlueingComma) :
    t.right ⟶ (modulePushforward B S hS D.openImmersionOver).obj
      ((modulePullback B S hS D.openImmersionOver).obj t.right) :=
  (modulePullbackAdjunction B S hS D.openImmersionOver).unit.app t.right

/-- `b : 𝒢_ȳ ⟶ (j'_*𝒢|_V)_ȳ`, the stalk of the unit. -/
def localB (t : D.moduleGlueingComma) : D.localP y t ⟶ D.localQ y t :=
  ModuleCat.homEquiv.symm (geometricModuleStalkLinearMap B S hS D.spaceY y
    (D.overlapUnit t))

/-- `a : 𝒪_{Y,ȳ} ⊗ (j_*ℋ)_x̄ ⟶ (j'_*𝒢|_V)_ȳ`, the stalk of the map of the triple read through
`(f^*j_*ℋ)_ȳ = 𝒪_{Y,ȳ} ⊗ (j_*ℋ)_x̄`. -/
def localA (t : D.moduleGlueingComma) :
    ModuleCat.of (D.localRingY y) (D.localRingY y ⊗[D.localRingX y] D.localN y t) ⟶
      D.localQ y t :=
  (geometricModuleStalkPullbackIso B S hS D.ambientMorphism y
      ((modulePushforward B S hS D.openImmersion).obj t.left)).inv ≫
    ModuleCat.homEquiv.symm (geometricModuleStalkLinearMap B S hS D.spaceY y (D.overlapTranspose t))

/-- The inclusion of `V` into `Y`, as a morphism of algebraic spaces, is `V.ι`. -/
theorem openImmersionOver_eq_homMk :
    D.openImmersionOver = (ObjectProperty.homMk D.V.ι :
      (⟨D.V.toFunctor, D.isOpenSubspace_V.1⟩ : AlgebraicSpaces B S hS) ⟶ D.spaceY) := rfl

/-- **`b` is bijective after inverting a generator.**  If `U₀` is a neighbourhood of `ȳ` on whose
chart the point set of `f⁻¹Z` is the zero locus of the `gᵢ`, then the stalk of the unit
`𝒢 ⟶ j'_*𝒢|_V` becomes bijective after inverting the germ of any `gᵢ`. -/
theorem bijective_localizedMap_localB (t : D.moduleGlueingComma)
    (ht : t.right.IsQuasicoherentOnSite) (U₀ : SmallEtaleNeighborhood y) {ι : Type*}
    (g : ι → chartRing B S hS D.spaceY.1 D.spaceY.2 U₀.chart)
    (hg : chartPointsMap U₀.chart ⁻¹'
        Set.range (pointsMap B S hS (D.Z.preimage D.f).toFunctor (D.Z.preimage D.f).ι) =
      (chartScheme U₀.chart).zeroLocus (U := ⊤) (Set.range g)) (i : ι) :
    Function.Bijective (LocalizedModule.map
      (Submonoid.powers (etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g i)))
      (geometricModuleStalkLinearMap B S hS D.spaceY y (D.overlapUnit t))) := by
  have hqc' : ((modulePushforward B S hS D.openImmersionOver).obj
      ((modulePullback B S hS D.openImmersionOver).obj t.right)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS D.openImmersionOver
      D.isQuasiCompact_openImmersionOver D.isQuasiSeparated_openImmersionOver _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ ht)
  have hpts := range_pointsMap_openChart_basicOpen_subset (D.Z.preimage D.f)
    D.isClosedSubspace_preimage_Z U₀.chart g hg i
  rw [← D.V_eq_openComplement_preimage] at hpts
  have hunit : IsIso ((modulePullback B S hS D.openImmersionOver).map (D.overlapUnit t)) :=
    isIso_modulePullback_map_unit_of_isOpenImmersion B S hS D.openImmersionOver
      D.isOpenSubspace_V.2 t.right
  exact bijective_localizedMap_of_isIso_modulePullback_of_heq B S hS (X := D.spaceY) U₀ (g i) D.V
    D.isOpenSubspace_V D.openImmersionOver rfl HEq.rfl ht hqc' (D.overlapUnit t) hunit hpts

/-- **`a` is bijective after inverting a generator**, for a triple whose structure arrow is
invertible. -/
theorem bijective_localizedMap_localA (t : D.moduleGlueingComma) [IsIso t.hom]
    (hl : t.left.IsQuasicoherentOnSite) (hr : t.right.IsQuasicoherentOnSite)
    (U₀ : SmallEtaleNeighborhood y) {ι : Type*}
    (g : ι → chartRing B S hS D.spaceY.1 D.spaceY.2 U₀.chart)
    (hg : chartPointsMap U₀.chart ⁻¹'
        Set.range (pointsMap B S hS (D.Z.preimage D.f).toFunctor (D.Z.preimage D.f).ι) =
      (chartScheme U₀.chart).zeroLocus (U := ⊤) (Set.range g)) (i : ι) :
    Function.Bijective (LocalizedModule.map
      (Submonoid.powers (etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g i)))
      (D.localA y t).hom) := by
  have hqc' : ((modulePushforward B S hS D.openImmersionOver).obj
      ((modulePullback B S hS D.openImmersionOver).obj t.right)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS D.openImmersionOver
      D.isQuasiCompact_openImmersionOver D.isQuasiSeparated_openImmersionOver _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hr)
  have hqc : ((modulePullback B S hS D.ambientMorphism).obj
      ((modulePushforward B S hS D.openImmersion).obj t.left)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (D.modulePushforwardPreservesQuasicoherence_openImmersion _ hl)
  have hpts := range_pointsMap_openChart_basicOpen_subset (D.Z.preimage D.f)
    D.isClosedSubspace_preimage_Z U₀.chart g hg i
  rw [← D.V_eq_openComplement_preimage] at hpts
  have hiso := D.isIso_modulePullback_map_overlapTranspose t
  have hstalk := bijective_localizedMap_of_isIso_modulePullback_of_heq B S hS (X := D.spaceY) U₀
    (g i) D.V D.isOpenSubspace_V D.openImmersionOver rfl HEq.rfl hqc hqc' _ hiso hpts
  set e := geometricModuleStalkPullbackIso B S hS D.ambientMorphism y
      ((modulePushforward B S hS D.openImmersion).obj t.left)
  have he := LocalizedModule.map_bijective
      (Submonoid.powers (etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g i))) e.symm.toLinearEquiv
  have hcomp : ⇑(LocalizedModule.map
      (Submonoid.powers (etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g i)))
        (D.localA y t).hom) =
      ⇑(LocalizedModule.map
        (Submonoid.powers (etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g i)))
        (geometricModuleStalkLinearMap B S hS D.spaceY y (D.overlapTranspose t))) ∘
      ⇑(LocalizedModule.map
        (Submonoid.powers (etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g i)))
        e.symm.toLinearEquiv.toLinearMap) :=
    funext fun z => LocalizedModule.map_comp_apply _ _ _ z
  rw [hcomp]
  exact hstalk.comp he

end AlgebraicGeometry.Space.FormalGlueingSituation

end
