module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeBLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeUnitEquation
public import StacksFrontier.Homology.CompositeCollapseComparison

/-!
# The transpose of the affine base change isomorphism

For a cartesian square

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `Y = Spec(A)` and `Y' = Spec(B)` affine and `g` flat, this file computes the chosen
isomorphism `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso` on the
pure tensors `h ⊗ 1`, that is, its transpose across the adjunction between extension and
restriction of scalars.

## Main results

* `ModuleCat.restrictScalars_map_hom_apply`: restriction of scalars does not change the
  underlying map of a morphism.
* `ModuleCat.extendRestrictScalarsAdj_homEquiv_hom_apply`: the transpose of a map out of an
  extension of scalars is precomposition with `x ↦ 1 ⊗ x`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.naturalCohomologyPushforwardIso_eq`: the two
  spellings of the Leray collapse `H^i(X', 𝓕') ≅ H^i(X, g'_*𝓕')` agree.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyPullbackOverBase_hom_apply`: the
  pullback map on cohomology, read over `A`, on an element.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso_hom_tmul_one`: the
  value of the chosen isomorphism at `h ⊗ 1` is the pullback map on cohomology at `h`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.baseChartBaseRingHom_algebraMap`: the coordinate-ring
  map `A ⟶ B` of the two charts agrees with the comparison `Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'})`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules
open Stacks.FlatDevissage
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.TensorByBaseModule hiding ringSheaf

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe u v

/-- The underlying map of `ModuleCat.restrictScalars ρ` applied to a morphism is that morphism's
own underlying map. -/
theorem ModuleCat.restrictScalars_map_hom_apply {R S : Type*} [Ring R] [Ring S] (ρ : R →+* S)
    {M N : ModuleCat.{v} S} (v : M ⟶ N) (x : (ModuleCat.restrictScalars ρ).obj M) :
    ((ModuleCat.restrictScalars ρ).map v).hom x = v.hom x := rfl

/-- For `ρ : R ⟶ S` and a map `g : S ⊗_R M ⟶ N` of `S`-modules, the transpose of `g` across
`ModuleCat.extendRestrictScalarsAdj ρ` sends `x` to `g (1 ⊗ x)`. -/
theorem ModuleCat.extendRestrictScalarsAdj_homEquiv_hom_apply {R S : Type u} [CommRing R]
    [CommRing S] (ρ : R →+* S) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    (g : (ModuleCat.extendScalars ρ).obj M ⟶ N) (x : M) :
    (((ModuleCat.extendRestrictScalarsAdj ρ).homEquiv M N) g).hom x =
      g.hom (TensorProduct.tmul R (1 : S) x) :=
  rfl

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-! ### The two spellings of the collapse -/

/-- For `g` flat and `Y`, `Y'` affine, the two spellings of the Leray collapse
`H^i(X', 𝓕') ≅ H^i(X, g'_*𝓕')` agree:
`AlgebraicGeometry.Space.BaseChangeDiagram.naturalCohomologyPushforwardIso`, built from
`Stacks.RightDerivedComp.objIso`, equals
`AlgebraicGeometry.Space.BaseChangeDiagram.cohomologyPushforwardIso`, built from
`Stacks.RightDerivedComp.objIsoOfAcyclicImage`. -/
theorem naturalCohomologyPushforwardIso_eq (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ) :
    D.naturalCohomologyPushforwardIso hg hY hY' i = D.cohomologyPushforwardIso hg hY hY' i := by
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have := enoughInjectives_modules B S hS D.X.1 D.X.2
  have := preservesInjectiveObjects_modulePushforward_of_isFlat B S hS D.g' (D.isFlat_g' hg)
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS D.X.1 D.X.2
  refine congrArg (fun e =>
    ((derivedGlobalSectionsPushforwardIso B S hS D.g' i).app D.pulledBack).symm ≪≫ e) ?_
  exact Stacks.RightDerivedComp.objIso_eq_objIsoOfAcyclicImage
    (modulePushforward B S hS D.g')
    (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O))
    (fun n hn => D.isZero_rightDerived_pushforward_pulledBack
      (D.relativelyRepresentable_g' hY hY') (D.isAffineHom_g' hY hY') n hn)
    (acyclicPushforwardOfInjective_of_isFlat B S hS D.g' (D.isFlat_g' hg)) i

/-! ### The pullback map on cohomology, on elements -/

/-- The pullback map `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyPullbackOverBase`,
read over `A`, sends `h` to the derived global sections of the unit of `(g')^* ⊣ g'_*` applied to
`h`, followed by the inverse of the collapse `H^i(X', 𝓕') ≅ H^i(X, g'_*𝓕')` and by the
reassociation of the two restrictions of scalars. -/
theorem affineCohomologyPullbackOverBase_hom_apply (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ)
    (h : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      D.affineCohomologyOverBase i) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (D.affineCohomologyPullbackOverBase hg hY hY' i).hom h =
      (D.restrictScalarsSquareIso.hom.app
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).obj D.pulledBack)).hom
        ((D.cohomologyPushforwardIso hg hY hY' i).inv.hom
          ((((globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).rightDerived
                i).map ((modulePullbackAdjunction B S hS D.g').unit.app D.F)).hom h)) := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have := enoughInjectives_modules B S hS D.X.1 D.X.2
  have hdef : (globalSectionsRestrictScalars B S hS D.f).map
        (cohomologyPullbackMap B S hS D.g' (D.isAffineHom_g' hY hY') (D.isFlat_g' hg) D.F
          D.isQuasicoherent i) ≫
        D.restrictScalarsSquareIso.hom.app
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).obj D.pulledBack) =
      D.affineCohomologyPullbackOverBase hg hY hY' i := rfl
  rw [cohomologyPullbackMap_eq] at hdef
  exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hdef) h).symm

/-! ### The transpose of the chosen isomorphism -/

variable (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
  (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom]

/-- For `g` flat, `f` quasi-compact and quasi-separated, and affine charts `V₀`, `V₀'` of `Y`,
`Y'`, the chosen `A`-linear isomorphism
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso` sends `h ⊗ 1` to
`H^i(X, −)` of the unit of `(g')^* ⊣ g'_*` at `h`, followed by the inverse of the collapse and by
the reassociation of the restrictions of scalars. -/
theorem affineCohomologyBaseChangeIso_hom_tmul_one (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ)
    (h : D.affineCohomologyOverBaseChart V₀ i) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    letI hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
    letI hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
    (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom
        (h ⊗ₜ[baseChartRing B S hS D.Y V₀] (1 : baseChartRing B S hS D.Y' V₀')) =
      (D.restrictScalarsSquareIso.hom.app
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).obj D.pulledBack)).hom
        ((D.cohomologyPushforwardIso hg hY hY' i).inv.hom
          ((((globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).rightDerived
                i).map ((modulePullbackAdjunction B S hS D.g').unit.app D.F)).hom h)) := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have := enoughInjectives_modules B S hS D.X.1 D.X.2
  letI hV₀ : IsTerminal V₀ := isTerminal_of_isIso_chart B S hS D.Y V₀
  have hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
  have hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
  have hg' : yoneda.relativelyRepresentable D.g'.hom := D.relativelyRepresentable_g' hY hY'
  have hiso : (D.tensorOneMap V₀ V₀' hV₀ ≫ (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom) ≫
      ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).inv =
      (modulePullbackAdjunction B S hS D.g').unit.app D.F :=
    (Iso.comp_inv_eq _).2 (D.tensorOneMap_comp_pushforwardTensorChartIso hg' V₀ V₀' hV₀)
  have key := congrArg (fun m => ModuleCat.Hom.hom m
      (h ⊗ₜ[baseChartRing B S hS D.Y V₀] (1 : baseChartRing B S hS D.Y V₀)))
    (D.spanHom_comp_affineCohomologyBaseChangeIso_hom V₀ V₀' hZ hg hqc hqs i)
  refine Eq.trans ?_ (Eq.trans key ?_)
  · exact congrArg (fun z => (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom
      (h ⊗ₜ[baseChartRing B S hS D.Y V₀] z)) (one_smul _ _).symm
  · have hPhi := (((cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map_comp
        (D.tensorOneMap V₀ V₀' hV₀ ≫ (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀).hom)
        ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).inv).symm.trans
      (congrArg (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).map hiso))
    have hPhih := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hPhi)
      ((TensorProduct.rid (baseChartRing B S hS D.Y V₀)
        (D.affineCohomologyOverBaseChart V₀ i)).toModuleIso.hom.hom
          (h ⊗ₜ[baseChartRing B S hS D.Y V₀] (1 : baseChartRing B S hS D.Y V₀)))
    have hr : (TensorProduct.rid (baseChartRing B S hS D.Y V₀)
        (D.affineCohomologyOverBaseChart V₀ i)).toModuleIso.hom.hom
          (h ⊗ₜ[baseChartRing B S hS D.Y V₀] (1 : baseChartRing B S hS D.Y V₀)) = h :=
      (TensorProduct.rid_tmul h (1 : baseChartRing B S hS D.Y V₀)).trans (one_smul _ h)
    refine Eq.trans (congrArg (fun y => ModuleCat.Hom.hom
        ((baseChartRestrictScalars B S hS D.Y hV₀).map
          (D.restrictScalarsSquareIso.hom.app
            (((globalSectionsFunctor.{u + 1, u, u, u}
              (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
                i).obj D.pulledBack)))
        (ModuleCat.Hom.hom ((globalSectionsRestrictScalars B S hS D.f ⋙
            baseChartRestrictScalars B S hS D.Y hV₀).map
          (D.cohomologyPushforwardIso hg hY hY' i).inv) y)) hPhih) ?_
    exact congrArg _ (congrArg _ (congrArg _ hr))

/-! ### The chart spelling and the global spelling of the ring map `A ⟶ B` -/

omit [IsIso V₀'.obj.hom] in
/-- For terminal charts `V₀`, `V₀'` of `Y`, `Y'`, reading the image of `a : A` in `B` as a
global regular function on `Y'` by the chart equivalence there gives the same global function as
reading `a` as a global function on `Y` by the chart equivalence at `Y` and carrying it along the
comparison `Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'})`. -/
theorem baseChartBaseRingHom_algebraMap (hV₀ : IsTerminal V₀) (hV₀' : IsTerminal V₀')
    (a : baseChartRing B S hS D.Y V₀) :
    letI := baseChartAlgebra B S hS D.g V₀ V₀'
    baseChartBaseRingHom B S hS D.Y' hV₀'
        (algebraMap (baseChartRing B S hS D.Y V₀) (baseChartRing B S hS D.Y' V₀') a) =
      globalSectionsRingHomSite B S hS D.g (baseChartBaseRingHom B S hS D.Y hV₀ a) := by
  let _ := baseChartAlgebra B S hS D.g V₀ V₀'
  refine ((globalSectionsChartRingEquiv B S hS D.Y' hV₀').symm_apply_eq).2 ?_
  exact (baseChartRingHom_apply B S hS D.g hV₀ V₀' a).symm

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

end
