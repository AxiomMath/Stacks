module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingLocalGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingPushforwardCechHeq
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingStalkQuotient
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingPullbackDatum

/-!
# The generic map of the stalk glueing datum is bijective

In Situation 0AEV let `ȳ` be a geometric point of `Y` lying on `f⁻¹(Z)`, with image `x̄ = f(ȳ)`,
and let `t = (ℋ, 𝒢, φ)` be a glueing triple of quasi-coherent modules.  The stalkwise proof of
Stacks 0AF0 compares `𝒢_ȳ` with the fibre product `N ×_Q P` of the data of
`AlgebraicGeometry.Space.FormalGlueingSituation.localA` and
`AlgebraicGeometry.Space.FormalGlueingSituation.localB`
(`N = (j_*ℋ)_x̄`, `P = 𝒢_ȳ`, `Q = (j'_*𝒢|_V)_ȳ`).  This file proves that the canonical map
`𝒪_{Y,ȳ} ⊗_{𝒪_{X,x̄}} (N ×_Q P) → P` is bijective, by Stacks 05ER in the form
`FormalGlueing.pullbackGenericMap_bijective`, applied to the germs `f₁, …, f_r` at `x̄` of
functions cutting out `Z` on an affine chart.

The hypotheses of that lemma are assembled from:

* flatness of `𝒪_{X,x̄} → 𝒪_{Y,ȳ}` and bijectivity of `𝒪_{X,x̄}/J → 𝒪_{Y,ȳ}/J𝒪_{Y,ȳ}`
  (`flat_etaleLocalRingMap_of_mem_preimage`, `bijective_quotientMap_etaleLocalRingMap`);
* bijectivity of `a` and `b` after inverting each `fᵢ` (`bijective_localizedMap_localA`,
  `bijective_localizedMap_localB`), read on a neighbourhood of `ȳ` lying over the chart of `x̄`
  (`exists_smallEtaleNeighborhood_lift`, `etaleLocalRingMap_germ`);
* Čech separation and glueing of `N` and separation of `Q` along the `fᵢ`, which hold on affine
  charts for direct images along open immersions whose complement is cut out by the `fᵢ`
  (`eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_of_heq`,
  `cechGlueingElementary_modulePushforward_of_heq`) and pass to geometric stalks
  (`cechSeparated_geometricModuleStalk`, `cechGlueingElementary_geometricModuleStalk`).

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.bijective_localPullbackGenericMap_of_mem`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.bijective_localPullbackGenericMap`.

## Implementation notes

The chart data are fixed as hypotheses of an auxiliary statement
(`bijective_localPullbackGenericMap_of_chart`) and eliminated from the existence statements in
term mode: destructuring them with `obtain` against the goal exceeds the heartbeat budget.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 05ER](https://stacks.math.columbia.edu/tag/05ER)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

/-- Bijectivity of a localized map at the powers of an element only depends on the element. -/
theorem LocalizedModule.bijective_restrictScalars_map_powers_of_eq {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) {x x' : R} (h : x = x')
    (hb : Function.Bijective (LocalizedModule.map (Submonoid.powers x') φ)) :
    Function.Bijective ((LocalizedModule.map (Submonoid.powers x) φ).restrictScalars R) := by
  subst h
  exact hb

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If on the chart `V` the point set of `Z` is the zero locus of the `gᵢ`, every point of a chart
`U` over `V` lying over the open complement of `Z` lies in the basic open of some restricted
`gᵢ`. -/
theorem exists_mem_basicOpen_chartRestrict_of_mem_openComplement
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F} (Z : Subfunctor F)
    {U V : SmallEtale B S hS F} (m : U ⟶ V) {ι : Type*} (g : ι → chartRing B S hS F hF V)
    (hg : chartPointsMap V ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      (chartScheme V).zeroLocus (U := ⊤) (Set.range g)) (x : chartScheme U)
    (hx : chartPointsMap U x ∈
      Set.range
        (pointsMap B S hS (openComplement B S hS Z).toFunctor (openComplement B S hS Z).ι)) :
    ∃ i, x ∈ (chartScheme U).basicOpen (chartRestrict (hF := hF) m (g i)) :=
  exists_mem_basicOpen_of_mem_openComplement Z U _
    (preimage_chartPointsMap_eq_zeroLocus_restrict Z m g hg) x hx

namespace FormalGlueingSituation

variable (D : FormalGlueingSituation B S hS)

/-- **The generic map of the stalk glueing datum is bijective, for given chart data.**  Let `ȳ`
lie on `f⁻¹(Z)`, let `N₀` be an affine pointed chart of `X` at `x̄ = f(ȳ)` on which `Z` is the zero
locus of `g₁, …, g_r`, and let `U₀` be a pointed chart of `Y` at `ȳ` mapping to `N₀` over `f`.
Then `𝒪_{Y,ȳ} ⊗_{𝒪_{X,x̄}} (N ×_Q P) → P` is bijective. -/
theorem bijective_localPullbackGenericMap_of_chart (t : D.moduleGlueingData)
    (y : GeometricPoint B S hS D.spaceY.1)
    (hy : y.image ∈
      Set.range (pointsMap B S hS (D.Z.preimage D.f).toFunctor (D.Z.preimage D.f).ι))
    (N₀ : SmallEtaleNeighborhood (geometricPointMap D.f y))
    (hN₀ : IsAffine (chartScheme N₀.chart)) {r : ℕ}
    (g : Fin r → chartRing B S hS D.X D.algebraicSpace_X N₀.chart)
    (hg : chartPointsMap N₀.chart ⁻¹' Set.range (pointsMap B S hS D.Z.toFunctor D.Z.ι) =
      (chartScheme N₀.chart).zeroLocus (U := ⊤) (Set.range g))
    (U₀ : SmallEtaleNeighborhood y) (m : U₀.chart.obj.left ⟶ N₀.chart.obj.left)
    (hcomm : U₀.chart.obj.hom ≫ D.f = yoneda.map m ≫ N₀.chart.obj.hom)
    (hpt : U₀.point ≫ m = N₀.point) :
    Function.Bijective (FormalGlueing.pullbackGenericMap.{u + 1, u + 1, 0} (D.localRingY y)
      (D.localN y t.obj) (D.localP y t.obj) (D.localQ y t.obj) (D.localA y t.obj)
      (D.localB y t.obj)) := by
  have hiso : IsIso t.obj.hom := t.property.1
  have hl : t.obj.left.IsQuasicoherentOnSite := t.property.2.1
  have hr : t.obj.right.IsQuasicoherentOnSite := t.property.2.2
  let fx : Fin r → D.localRingX y := fun i =>
    etaleLocalRingGerm B S hS D.X (geometricPointMap D.f y) (op N₀) (g i)
  let g' : Fin r → chartRing B S hS D.spaceY.1 D.spaceY.2 U₀.chart := fun i =>
    ((BigFppfOver.toScheme B S hS).map m).appTop (g i)
  have hg' : chartPointsMap U₀.chart ⁻¹'
        Set.range (pointsMap B S hS (D.Z.preimage D.f).toFunctor (D.Z.preimage D.f).ι) =
      (chartScheme U₀.chart).zeroLocus (U := ⊤) (Set.range g') :=
    preimage_chartPointsMap_preimage_eq_zeroLocus D.f D.Z U₀.chart N₀.chart m hcomm g hg
  have hgerm : ∀ i, algebraMap (D.localRingX y) (D.localRingY y) (fx i) =
      etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g' i) := fun i =>
    etaleLocalRingMap_germ D.algebraicSpace_Y D.f U₀ N₀ m hcomm hpt (g i)
  have hflat : Module.Flat (D.localRingX y) (D.localRingY y) :=
    D.flat_etaleLocalRingMap_of_mem_preimage y hy
  have hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range fx)).map (algebraMap (D.localRingX y) (D.localRingY y)))
      (algebraMap (D.localRingX y) (D.localRingY y)) Ideal.le_comap_map) :=
    D.bijective_quotientMap_etaleLocalRingMap y hy N₀ hN₀ g hg
  have hcovX : ∀ (M : SmallEtaleNeighborhood (geometricPointMap D.ambientMorphism.hom y))
      (d : M ⟶ N₀) (x : chartScheme M.chart), chartPointsMap M.chart x ∈
        Set.range (pointsMap B S hS D.U.toFunctor D.U.ι) →
      ∃ i, x ∈ (chartScheme M.chart).basicOpen
        (chartRestrict (hF := D.spaceX.2) d.hom (g i)) := fun M d x hx =>
    exists_mem_basicOpen_chartRestrict_of_mem_openComplement D.Z d.hom g hg x hx
  have hN : FormalGlueing.CechSeparated fx (D.localN y t.obj) :=
    cechSeparated_geometricModuleStalk B S hS D.spaceX (geometricPointMap D.ambientMorphism.hom y)
      ((modulePushforward B S hS D.openImmersion).obj t.obj.left) N₀ g
      (fun M d hM s hs => eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_of_heq
        (X := D.spaceX) D.U D.isOpenSubspace_U D.openImmersion rfl HEq.rfl t.obj.left M.chart hM
        _ (hcovX M d) s hs)
  have hN' : FormalGlueing.CechGlueing fx (D.localN y t.obj) :=
    FormalGlueing.cechGlueing_of_elementary fx (D.localN y t.obj)
      (cechGlueingElementary_geometricModuleStalk B S hS D.spaceX
        (geometricPointMap D.ambientMorphism.hom y)
        ((modulePushforward B S hS D.openImmersion).obj t.obj.left) N₀ g
        (fun M d hM => cechGlueingElementary_modulePushforward_of_heq
          (X := D.spaceX) D.U D.isOpenSubspace_U D.openImmersion rfl HEq.rfl t.obj.left
          (D.modulePushforwardPreservesQuasicoherence_openImmersion _ hl) M.chart hM
          _ (hcovX M d)))
  have hcovY : ∀ (M : SmallEtaleNeighborhood y) (d : M ⟶ U₀) (x : chartScheme M.chart),
      chartPointsMap M.chart x ∈ Set.range (pointsMap B S hS D.V.toFunctor D.V.ι) →
      ∃ i, x ∈ (chartScheme M.chart).basicOpen
        (chartRestrict (hF := D.spaceY.2) d.hom (g' i)) := by
    intro M d x hx
    rw [D.V_eq_openComplement_preimage] at hx
    exact exists_mem_basicOpen_chartRestrict_of_mem_openComplement (D.Z.preimage D.f) d.hom g'
      hg' x hx
  have hQ' : FormalGlueing.CechSeparated
      (fun i => etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g' i)) (D.localQ y t.obj) :=
    cechSeparated_geometricModuleStalk B S hS D.spaceY y
      ((modulePushforward B S hS D.openImmersionOver).obj
        ((modulePullback B S hS D.openImmersionOver).obj t.obj.right)) U₀ g'
      (fun M d hM s hs => eq_zero_of_forall_pow_smul_eq_zero_modulePushforward_of_heq
        (X := D.spaceY) D.V D.isOpenSubspace_V D.openImmersionOver rfl HEq.rfl
        ((modulePullback B S hS D.openImmersionOver).obj t.obj.right) M.chart hM
        _ (hcovY M d) s hs)
  have hfun : (fun i => algebraMap (D.localRingX y) (D.localRingY y) (fx i)) =
      fun i => etaleLocalRingGerm B S hS D.spaceY.1 y (op U₀) (g' i) := funext hgerm
  have hQ : FormalGlueing.CechSeparated
      (fun i => algebraMap (D.localRingX y) (D.localRingY y) (fx i)) (D.localQ y t.obj) := by
    rw [hfun]
    exact hQ'
  refine FormalGlueing.pullbackGenericMap_bijective.{u + 1, u + 1, 0} (D.localRingY y) fx
    (D.localN y t.obj) (D.localP y t.obj) (D.localQ y t.obj) (D.localA y t.obj)
    (D.localB y t.obj) (fun i => ?_) (fun i => ?_) hflat hq hN hN' hQ
  · exact LocalizedModule.bijective_restrictScalars_map_powers_of_eq _ (hgerm i)
      (D.bijective_localizedMap_localA y t.obj hl hr U₀ g' hg' i)
  · exact LocalizedModule.bijective_restrictScalars_map_powers_of_eq _ (hgerm i)
      (D.bijective_localizedMap_localB y t.obj hr U₀ g' hg' i)

/-- **The generic map of the stalk glueing datum is bijective** at every geometric point `ȳ` of
`Y` lying on `f⁻¹(Z)`: for a glueing triple `t` of quasi-coherent modules, the canonical map
`𝒪_{Y,ȳ} ⊗_{𝒪_{X,x̄}} ((j_*ℋ)_x̄ ×_{(j'_*𝒢|_V)_ȳ} 𝒢_ȳ) → 𝒢_ȳ` is bijective. -/
theorem bijective_localPullbackGenericMap_of_mem (t : D.moduleGlueingData)
    (y : GeometricPoint B S hS D.spaceY.1)
    (hy : y.image ∈
      Set.range (pointsMap B S hS (D.Z.preimage D.f).toFunctor (D.Z.preimage D.f).ι)) :
    Function.Bijective (FormalGlueing.pullbackGenericMap.{u + 1, u + 1, 0} (D.localRingY y)
      (D.localN y t.obj) (D.localP y t.obj) (D.localQ y t.obj) (D.localA y t.obj)
      (D.localB y t.obj)) := by
  obtain ⟨N₀, hN₀, r, g, hg⟩ := D.exists_chart_zeroLocus_eq (geometricPointMap D.f y)
  exact (exists_smallEtaleNeighborhood_lift D.f
    (nonempty_smallEtaleNeighborhood D.algebraicSpace_Y y).some N₀).elim fun U₀ h =>
      h.elim fun _ h => h.elim fun m h =>
        D.bijective_localPullbackGenericMap_of_chart t y hy N₀ hN₀ g hg U₀ m h.1 h.2

/-- **The generic map of the stalk glueing datum is bijective** at the image in `Y` of every
geometric point of `f⁻¹(Z)`. -/
theorem bijective_localPullbackGenericMap (t : D.moduleGlueingData)
    (z : GeometricPoint B S hS (D.Z.preimage D.f).toFunctor) :
    Function.Bijective (FormalGlueing.pullbackGenericMap.{u + 1, u + 1, 0}
      (D.localRingY (geometricPointMap (D.Z.preimage D.f).ι z))
      (D.localN (geometricPointMap (D.Z.preimage D.f).ι z) t.obj)
      (D.localP (geometricPointMap (D.Z.preimage D.f).ι z) t.obj)
      (D.localQ (geometricPointMap (D.Z.preimage D.f).ι z) t.obj)
      (D.localA (geometricPointMap (D.Z.preimage D.f).ι z) t.obj)
      (D.localB (geometricPointMap (D.Z.preimage D.f).ι z) t.obj)) :=
  D.bijective_localPullbackGenericMap_of_mem t _ ⟨z.image, rfl⟩

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
