module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramIsoDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange

/-!
# The comparison map of equation 076R is an isomorphism on quasi-coherent modules

Let `φ : a ⋙ g ≅ f` be a 2-commutative triangle of 1-morphisms of categories fibred in groupoids
over `(Sch/S)_{fppf}` whose sources `𝒰`, `𝒱` are representable by algebraic spaces `U`, `V`, and
let `ℱ` be an `𝒪_𝒳`-module.  Equation 076R of the source attaches to it the comparison map

```
c_φ : a_small^*(g^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale},
```

`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules`.  This file computes `c_φ` on the
canonical sections of the inverse image and proves that it is an isomorphism as soon as `ℱ` is
cartesian between objects of `𝒳` lying over affine schemes — which is the case for every
quasi-coherent `ℱ` (Stacks 0H0E).

## Main results

* `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_chartSection`: on the canonical
  section `modulePullbackChartSection d s` of the inverse image over a diagram of étale scheme
  charts, `c_φ` is restriction of `s` along `AlgebraicGeometry.Space.comparisonMorphism`.
* `AlgebraicGeometry.Space.bijective_comparisonAlgebraicSpacesModules_app`: `c_φ` is bijective
  over every diagram of affine étale charts, for `ℱ` cartesian between affine objects.
* `AlgebraicGeometry.Space.isIso_comparisonAlgebraicSpacesModules`: hence `c_φ` is an
  isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v v' v'' w w' w''

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS)
  (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (a : 𝒰 ⥤ 𝒱) (f : 𝒰 ⥤ 𝒳) (g : 𝒱 ⥤ 𝒳)
  (hf : p.IsFibredOneMorphism r f) (hg : q.IsFibredOneMorphism r g)
  (φ : a ⋙ g ≅ f) (aSpace : U ⟶ V)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hr : r.IsFiberedInGroupoids)
  (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
  (hab : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha.hom.app Z))

/-- **The comparison map of equation 076R on the canonical sections of the inverse image.**  On
the section `modulePullbackChartSection d s` of `a_small^*(g^*ℱ|_{V_étale})` attached to a
section `s` of `g^*ℱ|_{V_étale}` over the chart of `V` of a diagram `d` of étale scheme charts,
`c_φ` is the restriction of `s` along `AlgebraicGeometry.Space.comparisonMorphism`. -/
theorem comparisonAlgebraicSpacesModules_chartSection
    (ℱ : inheritedEtaleModules.{u, v'', w'', u} B S hS r hr)
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (s : (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ).val.obj (op d.V)) :
    (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ℱ).val.app (op d.U)
        (modulePullbackChartSection B S hS aSpace
          (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ) d s) =
      ℱ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op s := by
  rw [← modulePullbackUnitSection_eq_modulePullbackChartSection,
    ← modulePullbackHomFMap_app]
  show (modulePushforwardHomFMap B S hS aSpace _ _
    ((modulePullbackAdjunction B S hS aSpace).homEquiv _ _
      (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
        hab ℱ))).app d s = _
  rw [comparisonAlgebraicSpacesModules_adjoint]
  show (modulePushforwardHomFMap B S hS aSpace _ _ (moduleFMapHom B S hS aSpace _ _ _)).app d s
    = _
  rw [modulePushforwardHomFMap_moduleFMapHom]
  rfl

/-- The identification of the ring of functions on an étale chart `W` of `U` with the ring of
functions on the object `f(u_U W)` of `𝒳`, as a ring isomorphism: the component of
`AlgebraicGeometry.Space.etaleChartStructureHom`, which is pullback of functions along an
`eqToHom`. -/
noncomputable def etaleChartStructureRingEquiv (W : SmallEtale B S hS U.1) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS U.1 U.2).O)).obj.obj
        (op W) ≃+*
      (FibredSite.ringStructureSheafCore B S hS r hr .etale).obj.obj
        (op ((etaleChartToFibred B S hS p eU f).obj W)) :=
  RingEquiv.ofRingHom ((etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app (op W)).hom
    ((BigFppfOver.structureSheaf B S hS).obj.map
      (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p r eU f hf) W).symm).op).hom
    (by
      ext x
      rw [etaleChartStructureHom_app]
      change ((BigFppfOver.structureSheaf B S hS).obj.map _ ≫
        (BigFppfOver.structureSheaf B S hS).obj.map _).hom x = x
      rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id]
      exact ConcreteCategory.congr_hom ((BigFppfOver.structureSheaf B S hS).obj.map_id _) x)
    (by
      ext x
      rw [etaleChartStructureHom_app]
      change ((BigFppfOver.structureSheaf B S hS).obj.map _ ≫
        (BigFppfOver.structureSheaf B S hS).obj.map _).hom x = x
      rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id]
      exact ConcreteCategory.congr_hom ((BigFppfOver.structureSheaf B S hS).obj.map_id _) x)

/-- An étale chart `W` of `U` lying over an affine scheme maps to an object of `𝒳` lying over an
affine scheme. -/
private theorem isAffine_etaleChartToFibred (hf : p.IsFibredOneMorphism r f)
    (W : SmallEtale B S hS U.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    IsAffine ((r ⋙ BigFppfOver.toScheme B S hS).obj
      ((etaleChartToFibred B S hS p eU f).obj W)) := by
  have h := Functor.congr_obj (etaleChartToFibred_comp B S hS p r eU f hf) W
  show IsAffine ((BigFppfOver.toScheme B S hS).obj (r.obj _))
  rw [show r.obj _ = _ from h]
  exact hW

open scoped ChangeOfRings in
/-- **The comparison map of equation 076R is bijective over a diagram of affine étale charts**,
for a module `ℱ` cartesian between objects of `𝒳` lying over affine schemes whose restriction to
`V` is quasi-coherent.

The canonical base change `𝒪_U(W) ⊗ (g^*ℱ|_V)(V') ⟶ (a_small^*(g^*ℱ|_V))(W)` is bijective
(Stacks 083K,
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`), and
its composite with `c_φ` is, through the identifications of rings of functions, the base change of
`ℱ` along `AlgebraicGeometry.Space.comparisonMorphism`, which is bijective because `ℱ` is
cartesian. -/
theorem bijective_comparisonAlgebraicSpacesModules_app
    (ℱ : inheritedEtaleModules.{u, v'', w'', u} B S hS r hr)
    (hℱ : ∀ ⦃x y : 𝒳⦄ (k : y ⟶ x), IsAffine ((r ⋙ BigFppfOver.toScheme B S hS).obj x) →
      IsAffine ((r ⋙ BigFppfOver.toScheme B S hS).obj y) →
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v'', w'', u, u}
        (R := (r ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ) ℱ.val k.op))
    (hqc : (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ).IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS V.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    Function.Bijective ((comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ
      aSpace ha hr hφ hab ℱ).val.app (op d.U)) := by
  let G := etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ
  let c := comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr
    hφ hab ℱ
  let x := (etaleChartToFibred B S hS q eV g).obj d.V
  let y := (etaleChartToFibred B S hS p eU f).obj d.U
  let k : y ⟶ x := comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d
  have hx := isAffine_etaleChartToFibred B S hS q r eV g hg d.V hV
  have hy := isAffine_etaleChartToFibred B S hS p r eU f hf d.U hU
  let := chartDiagramAlgebra B S hS aSpace d
  have hbc := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS aSpace G hqc
    d hU hV
  let R := (r ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ
  let : Module (R.obj (op x)) (R.obj (op y)) := Module.compHom _ (R.map k.op).hom
  let α := etaleChartStructureRingEquiv B S hS q r hq eV g hg hr d.V
  let β := etaleChartStructureRingEquiv B S hS p r hp eU f hf hr d.U
  have hsq : ∀ t, β (chartDiagramRestrict B S hS aSpace d t) = (R.map k.op).hom (α t) :=
    fun t => (structureSheaf_map_comparisonMorphism B S hS p q r hp hq eU eV a f g hf hg φ aSpace
      ha hr hφ hab d t).symm
  let : Module (R.obj (op x)) (G.val.obj (op d.V)) :=
    (inferInstance : Module ((FibredSite.ringStructureSheafCore B S hS r hr .etale).obj.obj
      (op x)) (ℱ.val.obj (op x)))
  let T := Stacks.RingSquare.tensorMap (P := G.val.obj (op d.V))
    (chartDiagramRestrict B S hS aSpace d) (R.map k.op).hom α β hsq
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hT : Function.Bijective T := Stacks.RingSquare.bijective_tensorMap _ _ _ _ _ _ _ _
  have hkey : ∀ z, (c.val.app (op d.U)).hom (modulePullbackChartBaseChange B S hS aSpace G d z) =
      (Stacks.PresheafOfModules.restrictionBaseChange (R := R) ℱ.val k.op).hom (T z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
        ((congrArg _ (map_zero T)).trans (map_zero _)).symm)
    | tmul t s =>
      refine Eq.trans ?_ (Stacks.PresheafOfModules.restrictionBaseChange_tmul (R := R) ℱ.val k.op
        (β t) s).symm
      refine Eq.trans (congrArg (c.val.app (op d.U)).hom
        (modulePullbackChartBaseChange_tmul B S hS aSpace G d t s)) ?_
      refine Eq.trans ((c.val.app (op d.U)).hom.map_smul t _) ?_
      exact congrArg (fun m => t • m) (comparisonAlgebraicSpacesModules_chartSection B S hS p q
        r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab ℱ d s)
    | add z w hz hw => exact ((congrArg _ (map_add _ z w)).trans ((map_add _ _ _).trans
        (congrArg₂ (· + ·) hz hw))).trans ((congrArg _ (map_add T z w)).trans
          (map_add _ _ _)).symm
  have hcomp : (c.val.app (op d.U)).hom ∘ modulePullbackChartBaseChange B S hS aSpace G d =
      (Stacks.PresheafOfModules.restrictionBaseChange (R := R) ℱ.val k.op).hom ∘ T :=
    funext hkey
  have h2 : Function.Bijective ((c.val.app (op d.U)).hom ∘
      modulePullbackChartBaseChange B S hS aSpace G d) := by
    rw [hcomp]
    exact (hℱ k hx hy).comp hT
  exact (Function.Bijective.of_comp_iff _ hbc).mp h2

/-- **The comparison map of equation 076R is an isomorphism** for a module `ℱ` cartesian between
objects of `𝒳` lying over affine schemes whose restriction to `V` is quasi-coherent: it is
bijective over every diagram of affine étale charts, and those cover. -/
theorem isIso_comparisonAlgebraicSpacesModules
    (ℱ : inheritedEtaleModules.{u, v'', w'', u} B S hS r hr)
    (hℱ : ∀ ⦃x y : 𝒳⦄ (k : y ⟶ x), IsAffine ((r ⋙ BigFppfOver.toScheme B S hS).obj x) →
      IsAffine ((r ⋙ BigFppfOver.toScheme B S hS).obj y) →
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v'', w'', u, u}
        (R := (r ⋙ BigFppfOver.toScheme B S hS).op ⋙ Scheme.Γ) ℱ.val k.op))
    (hqc : (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ).IsQuasicoherentOnSite) :
    IsIso (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr
      hφ hab ℱ) :=
  isIso_of_bijective_affineChartDiagram B S hS aSpace _ fun d hU hV =>
    bijective_comparisonAlgebraicSpacesModules_app B S hS p q r hp hq eU eV a f g hf hg φ aSpace
      ha hr hφ hab ℱ hℱ hqc d hU hV

end AlgebraicGeometry.Space

end
