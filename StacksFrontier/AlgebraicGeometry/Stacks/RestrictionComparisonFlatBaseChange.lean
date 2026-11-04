module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpaceIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeAffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat

/-!
# The comparison map of equation 076R on modules with the flat base change property

Let `φ : a ⋙ g ≅ f` be a 2-commutative triangle of 1-morphisms of categories fibred in groupoids
over `(Sch/S)_{fppf}`, with source categories `𝒰`, `𝒱` representable by algebraic spaces `U`,
`V`, and `aSpace : U ⟶ V` the morphism of algebraic spaces corresponding to `a`.  For an
`𝒪_𝒳`-module `ℱ` on the inherited étale site of `𝒳`, equation 076R of the source is the
comparison map `c_φ : a_small^*(g^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale}`
(`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules`).

`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionComparisonAlgebraicSpaceIso.lean` proves that
`c_φ` is an isomorphism for `ℱ` quasi-coherent on the fppf site.  This file proves the same for
`ℱ` in the class `LQCoh^{fbc}(𝒪_𝒳)` of locally quasi-coherent modules with the flat base change
property (Stacks 06WJ, 0762), provided `aSpace` is flat, which is the setting of Stacks 076S and
of the proof of Stacks 07B7.

## Main results

* `Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent`:
  for `ℱ` locally quasi-coherent, `f^*ℱ|_{U_étale}` is a quasi-coherent `𝒪_U`-module.
* `Space.isIso_comparisonAlgebraicSpacesModules_of_locallyQuasicoherentFlatBaseChangeSheaf`:
  for `ℱ ∈ LQCoh^{fbc}(𝒪_𝒳)` and `aSpace` flat, `c_φ` is an isomorphism.
* `Space.bijective_liftBaseChange_etaleRestriction_of_bijective_restrictionBaseChange`:
  the sections of `f₁^*ℱ|_{U₁}` over a chart are the base change of the sections of
  `f₂^*ℱ|_{U₂}` over a second chart along a morphism `n` of `𝒳` lying over a morphism of the
  charts, as soon as the sections of `ℱ` are cartesian along `n`.

## Proof

The proof is that of the quasi-coherent case, with its single module-theoretic input, the
cartesianness of a quasi-coherent module between affine objects, replaced as follows.

* Morphisms of the small étale site of `U` lie over étale morphisms of schemes
  (`AlgebraicGeometry.Space.etale_of_comp_etale_chart`), along which a locally quasi-coherent
  module is cartesian between affine objects
  (`AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_isLocallyQuasicoherent_of_etale`).
* The comparison morphism `f(u_U W) ⟶ g(u_V V')` of a chart diagram lies over the morphism of
  schemes `W ⟶ V'`, which is flat when `aSpace` is; a module with the flat base change property
  is cartesian along it between affine objects
  (`Stack.bijective_restrictionBaseChange_of_locallyQuasicoherentFlatBaseChangeSheaf`).

The passage from the base-change comparison over the rings of global functions to the one over
the rings of regular functions on the charts is
`Stacks.PresheafOfModules.bijective_liftBaseChange_of_bijective_restrictionBaseChange`.

## Implementation notes

No `@[stacks]` attribute is carried: the source uses these statements without numbering them.

## References

* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 07B7](https://stacks.math.columbia.edu/tag/07B7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w v' w' v'' w'' v₁ w₁ v₂ w₂

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property of morphisms of schemes transports along a lift.**  If `n` lies over `t`, then
the morphism of schemes underlying `r.map n` is the one underlying `t`. -/
theorem prop_map_of_isHomLift {𝒳 : Type v''} [Category.{w''} 𝒳]
    {r : 𝒳 ⥤ BigFppfOver B S hS} (P : MorphismProperty Scheme.{u})
    {T₁ T₂ : BigFppfOver B S hS} (t : T₁ ⟶ T₂) {y x : 𝒳} (n : y ⟶ x) [r.IsHomLift t n]
    (ht : P ((BigFppfOver.toScheme B S hS).map t)) :
    P (B.inclusion.map (r.map n).left) := by
  subst_hom_lift r t n
  exact ht

/-- If `n` lies over `t`, then `r.obj` of the source and target of `n` are affine schemes as soon
as the source and target of `t` are. -/
private theorem isAffine_obj_of_isHomLift {𝒳 : Type v''} [Category.{w''} 𝒳]
    (r : 𝒳 ⥤ BigFppfOver B S hS) {T₁ T₂ : BigFppfOver B S hS} (t : T₁ ⟶ T₂) {y x : 𝒳}
    (n : y ⟶ x) [r.IsHomLift t n] (h₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₁))
    (h₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₂)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (r.obj y)) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj (r.obj x)) := by
  rw [IsHomLift.domain_eq r t n, IsHomLift.codomain_eq r t n]
  exact ⟨h₁, h₂⟩

section Core

variable {U₁ U₂ : AlgebraicSpaces B S hS}
  {𝒰₁ : Type v₁} [Category.{w₁} 𝒰₁] {𝒰₂ : Type v₂} [Category.{w₂} 𝒰₂]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p₁ : 𝒰₁ ⥤ BigFppfOver B S hS) (p₂ : 𝒰₂ ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp₁ : p₁.IsFiberedInGroupoids) (hp₂ : p₂.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (e₁ : StacksRepresentableCFG.EquivalenceOver p₁ (presheafOfCategories (U₁.1 ⋙ typeToCat)).p)
  (e₂ : StacksRepresentableCFG.EquivalenceOver p₂ (presheafOfCategories (U₂.1 ⋙ typeToCat)).p)
  (f₁ : 𝒰₁ ⥤ 𝒳) (f₂ : 𝒰₂ ⥤ 𝒳) (hf₁ : p₁.IsFibredOneMorphism r f₁)
  (hf₂ : p₂.IsFibredOneMorphism r f₂)

/-- **The sections of the restriction of a module over a chart are the base change of its
sections over a second chart, along a morphism of `𝒳` along which the module is cartesian.**

Let `ℱ` be an `𝒪_𝒳`-module on the inherited étale site of `𝒳`.  For étale charts `W₁` of `U₁`
and `W₂` of `U₂`, a morphism `t : W₁ ⟶ W₂` of `(Sch/S)_{fppf}` and a morphism
`n : f₁(u W₁) ⟶ f₂(u W₂)` of `𝒳` lying over `t` such that the base-change comparison
`𝒪(f₁(u W₁)) ⊗_{𝒪(f₂(u W₂))} ℱ(f₂(u W₂)) ⟶ ℱ(f₁(u W₁))` of the restriction along `n` is
bijective, the comparison
`𝒪_{U₁}(W₁) ⊗_{𝒪_{U₂}(W₂)} (f₂^*ℱ|_{U₂})(W₂) ⟶ (f₁^*ℱ|_{U₁})(W₁)` of any linear map agreeing
with restriction along `n` is bijective.  The algebra structure is any one whose structure map
is pullback along `t`.

This is `Stacks.PresheafOfModules.bijective_liftBaseChange_of_bijective_restrictionBaseChange`
read through the identifications `AlgebraicGeometry.Space.etaleChartFppfStructureRingEquiv` of the
rings of regular functions on the charts with the rings of global functions of the two objects
of `𝒳`, whose compatibility with `n` is
`AlgebraicGeometry.Space.structureSheaf_map_of_isHomLift`. -/
theorem bijective_liftBaseChange_etaleRestriction_of_bijective_restrictionBaseChange
    (ℱ : inheritedEtaleModules.{u} B S hS r hr) {W₁ : SmallEtale B S hS U₁.1}
    {W₂ : SmallEtale B S hS U₂.1}
    (t : (SmallEtale.toOver B S hS U₁.1).obj W₁ ⟶ (SmallEtale.toOver B S hS U₂.1).obj W₂)
    (n : (etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁ ⟶
      (etaleChartToFibred B S hS p₂ e₂ f₂).obj W₂) [r.IsHomLift t n]
    (hn : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v'', w'', u, u}
      (R := (Stack.structureSheaf B S hS r hr (etaleTopology B)
        (Stack.etaleTopology_le_topology B)).obj) ℱ.val n.op))
    [Algebra (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁)]
    (halg : ∀ c, algebraMap (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁) c =
      ((BigFppfOver.structureSheaf B S hS).obj.map t.op).hom c)
    [iA : Module (chartRing B S hS U₂.1 U₂.2 W₂)
      ((etaleRestrictedModuleInverseImage B S hS p₁ r hp₁ hr e₁ f₁ hf₁ ℱ).val.obj (op W₁))]
    [iT : IsScalarTower (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁)
      ((etaleRestrictedModuleInverseImage B S hS p₁ r hp₁ hr e₁ f₁ hf₁ ℱ).val.obj (op W₁))]
    (ρ : (etaleRestrictedModuleInverseImage B S hS p₂ r hp₂ hr e₂ f₂ hf₂ ℱ).val.obj (op W₂)
      →ₗ[chartRing B S hS U₂.1 U₂.2 W₂]
        (etaleRestrictedModuleInverseImage B S hS p₁ r hp₁ hr e₁ f₁ hf₁ ℱ).val.obj (op W₁))
    (hρ : ∀ s, ρ s = ℱ.val.map n.op s) :
    Function.Bijective (ρ.liftBaseChange (chartRing B S hS U₁.1 U₁.2 W₁)) := by
  let R := (Stack.structureSheaf B S hS r hr (etaleTopology B)
    (Stack.etaleTopology_le_topology B)).obj
  let e₁' : chartRing B S hS U₁.1 U₁.2 W₁ ≃+*
      (R.obj (op ((etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁)) : Type u) :=
    etaleChartFppfStructureRingEquiv B S hS p₁ r hp₁ hr e₁ f₁ hf₁ W₁
  let e₂' : chartRing B S hS U₂.1 U₂.2 W₂ ≃+*
      (R.obj (op ((etaleChartToFibred B S hS p₂ e₂ f₂).obj W₂)) : Type u) :=
    etaleChartFppfStructureRingEquiv B S hS p₂ r hp₂ hr e₂ f₂ hf₂ W₂
  let iAx : Module (chartRing B S hS U₂.1 U₂.2 W₂)
      (ℱ.val.obj (op ((etaleChartToFibred B S hS p₂ e₂ f₂).obj W₂))) :=
    inferInstanceAs (Module (chartRing B S hS U₂.1 U₂.2 W₂)
      ((etaleRestrictedModuleInverseImage B S hS p₂ r hp₂ hr e₂ f₂ hf₂ ℱ).val.obj (op W₂)))
  let iBy : Module (chartRing B S hS U₁.1 U₁.2 W₁)
      (ℱ.val.obj (op ((etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁))) :=
    inferInstanceAs (Module (chartRing B S hS U₁.1 U₁.2 W₁)
      ((etaleRestrictedModuleInverseImage B S hS p₁ r hp₁ hr e₁ f₁ hf₁ ℱ).val.obj (op W₁)))
  let iAy : Module (chartRing B S hS U₂.1 U₂.2 W₂)
      (ℱ.val.obj (op ((etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁))) := iA
  have iT' : IsScalarTower (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁)
      (ℱ.val.obj (op ((etaleChartToFibred B S hS p₁ e₁ f₁).obj W₁))) := iT
  exact Stacks.PresheafOfModules.bijective_liftBaseChange_of_bijective_restrictionBaseChange
    (R := R) ℱ.val n.op hn (chartRing B S hS U₂.1 U₂.2 W₂) (chartRing B S hS U₁.1 U₁.2 W₁)
    e₂'.symm (fun c m => congrArg (· • m) (e₂'.apply_symm_apply c))
    e₁'.symm (fun c m => congrArg (· • m) (e₁'.apply_symm_apply c))
    (fun c => by
      rw [halg c, RingEquiv.symm_symm]
      exact (RingEquiv.eq_symm_apply e₁').2
        (structureSheaf_map_of_isHomLift B S hS p₁ p₂ r hp₁ hp₂ hr e₁ e₂ f₁ f₂ hf₁ hf₂ t n
          c).symm)
    ρ hρ

end Core

section Restriction

variable {U : AlgebraicSpaces B S hS} {𝒰 : Type v} [Category.{w} 𝒰]
  {𝒳 : Type v''} [Category.{w''} 𝒳] (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)

/-- **The restriction to `U_étale` of the inverse image of a locally quasi-coherent module is
cartesian on affine charts.**  For a locally quasi-coherent `𝒪_𝒳`-module `ℱ` on the inherited
étale site of `𝒳` (Stacks 06WJ) and a 1-morphism `f : 𝒰 ⥤ 𝒳` out of a category representable by
the algebraic space `U`, the sections of `f^*ℱ|_{U_étale}` over a smaller affine étale chart are
the base change of its sections over a larger one.

The morphism between the images under `f` of the two charts lies over the morphism of charts,
whose underlying morphism of schemes is étale (`etale_of_comp_etale_chart`); along it `ℱ` is
cartesian between affine objects by
`Stack.bijective_restrictionBaseChange_of_isLocallyQuasicoherent_of_etale`, so this is
`bijective_liftBaseChange_etaleRestriction_of_bijective_restrictionBaseChange`. -/
theorem isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent
    (ℱ : SheafOfModules.{u}
      (Stack.ringStructureSheafCore B S hS r hr (etaleTopology B)
        (Stack.etaleTopology_le_topology B)))
    (hℱ : Stack.IsLocallyQuasicoherent B E h S hS r hr ℱ.val) :
    IsCartesianOnAffineCharts (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ) := by
  intro W₂ W₁ hW₂ hW₁ j
  have : r.IsHomLift ((SmallEtale.toOver B S hS U.1).map j)
      ((etaleChartToFibred B S hS p eU f).map j) :=
    Functor.isHomLift_map_of_comp_eq (etaleChartToFibred_comp B S hS p r eU f hf) _ j
  obtain ⟨hy, hx⟩ := isAffine_obj_of_isHomLift B S hS r ((SmallEtale.toOver B S hS U.1).map j)
    ((etaleChartToFibred B S hS p eU f).map j) hW₁ hW₂
  have hn := Stack.bijective_restrictionBaseChange_of_isLocallyQuasicoherent_of_etale B E h S hS
    r hr ℱ.val hℱ ((etaleChartToFibred B S hS p eU f).map j)
    (prop_map_of_isHomLift B S hS _ ((SmallEtale.toOver B S hS U.1).map j) _
      (etale_of_comp_etale_chart B S hS W₁.property W₂.property (CostructuredArrow.w j.hom)))
    hx hy
  let := chartAlgebra (hF := U.2) j
  let := chartSectionsModule (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ) j
  have := chartSections_isScalarTower
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ) j
  have halg : ∀ c, algebraMap (chartRing B S hS U.1 U.2 W₂) (chartRing B S hS U.1 U.2 W₁) c =
      ((BigFppfOver.structureSheaf B S hS).obj.map
        ((SmallEtale.toOver B S hS U.1).map j).op).hom c := fun c => rfl
  have hρ : ∀ s,
      chartRestrictLinear (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ) j s =
        ℱ.val.map ((etaleChartToFibred B S hS p eU f).map j).op s := fun s => rfl
  exact bijective_liftBaseChange_etaleRestriction_of_bijective_restrictionBaseChange B S hS p p r
    hp hp hr eU eU f f hf hf ℱ _ _ hn halg _ hρ

/-- **The restriction to `U_étale` of the inverse image of a locally quasi-coherent module is
quasi-coherent.**  For a locally quasi-coherent `𝒪_𝒳`-module `ℱ` on the inherited étale site of
`𝒳` (Stacks 06WJ) and a 1-morphism `f : 𝒰 ⥤ 𝒳` out of a category representable by the algebraic
space `U`, the `𝒪_U`-module `f^*ℱ|_{U_étale}` is quasi-coherent.

It is cartesian on affine charts
(`isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent`),
and a module cartesian on affine charts is quasi-coherent by Descent, Proposition 03DX(2)
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`). -/
theorem isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent
    (ℱ : SheafOfModules.{u}
      (Stack.ringStructureSheafCore B S hS r hr (etaleTopology B)
        (Stack.etaleTopology_le_topology B)))
    (hℱ : Stack.IsLocallyQuasicoherent B E h S hS r hr ℱ.val) :
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent B E h S
      hS p r hp hr eU f hf ℱ hℱ)

end Restriction

section Triangle

variable {U V : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
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

/-- **The comparison map of equation 076R is bijective on the sections over the chart of an
affine chart diagram**, for a module with the flat base change property and a flat morphism of
algebraic spaces.

Let `d` be a commutative diagram of étale scheme charts over `aSpace`, a chart `W` of `U` above a
chart `V'` of `V`, both affine.  The sections of `a_small^*(g^*ℱ|_{V_étale})` over `W` are the
base change `𝒪_U(W) ⊗_{𝒪_V(V')} ℱ(g(u_V V'))`, because `g^*ℱ|_{V_étale}` is quasi-coherent
(`isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent`)
and by the chart bijectivity of Stacks 083K
(`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`).
The sections of `f^*ℱ|_{U_étale}` over `W` are `ℱ(f(u_U W))`, which is the same base change
because the comparison morphism `f(u_U W) ⟶ g(u_V V')` lies over the morphism `W ⟶ V'` of
affine schemes, which is flat since `aSpace` is, and `ℱ` has the flat base change property
(`Stack.bijective_restrictionBaseChange_of_locallyQuasicoherentFlatBaseChangeSheaf`).
Under these two identifications `c_φ` is the identity of the base change, by
`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_app_chartSection`. -/
theorem bijective_comparisonAlgebraicSpacesModules_app_of_locallyQuasicoherentFlatBaseChangeSheaf
    (haflat : IsFlat B S hS aSpace.hom)
    (ℱ : SheafOfModules.{u}
      (Stack.ringStructureSheafCore B S hS r hr (etaleTopology B)
        (Stack.etaleTopology_le_topology B)))
    (hℱ : Stack.locallyQuasicoherentFlatBaseChangeSheaf B E h S hS r hr ℱ)
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (hdU : IsAffine ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hdV : IsAffine ((SmallEtale.toOver B S hS V.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    Function.Bijective
      ((comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
        hab ℱ).val.app (op d.U)).hom := by
  let G := etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ
  let F := etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ
  let c := comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr
    hφ hab ℱ
  let n := comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d
  have hG : G.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent B E h S hS
      q r hq hr eV g hg ℱ hℱ.1
  let := chartDiagramAlgebra B S hS aSpace d
  have h1 := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS aSpace G hG d
    hdU hdV
  have := isHomLift_comparisonMorphism B S hS p q r eU eV a f g hg φ aSpace ha hφ hab d
  obtain ⟨hy, hx⟩ := isAffine_obj_of_isHomLift B S hS r d.g n hdU hdV
  have hn := Stack.bijective_restrictionBaseChange_of_locallyQuasicoherentFlatBaseChangeSheaf B E
    h S hS r hr ℱ hℱ n
    (prop_map_of_isHomLift B S hS _ d.g n
      (haflat _ _ d.U.obj.hom d.V.obj.hom d.g d.U.property d.V.property d.comm.symm))
    hx hy
  let : Module (chartRing B S hS V.1 V.2 d.V) (F.val.obj (op d.U)) :=
    Module.compHom _ (chartDiagramRestrict B S hS aSpace d)
  have : IsScalarTower (chartRing B S hS V.1 V.2 d.V) (chartRing B S hS U.1 U.2 d.U)
      (F.val.obj (op d.U)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let ρ : G.val.obj (op d.V) →ₗ[chartRing B S hS V.1 V.2 d.V] F.val.obj (op d.U) :=
    { toFun := (moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ℱ).app d
      map_add' := (moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab
        ℱ).map_add d
      map_smul' := (moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
        hab ℱ).map_smul d }
  have h2 := bijective_liftBaseChange_etaleRestriction_of_bijective_restrictionBaseChange B S hS
    p q r hp hq hr eU eV f g hf hg ℱ d.g n hn (fun _ => rfl) ρ fun _ => rfl
  have h3 : (c.val.app (op d.U)).hom ∘ modulePullbackChartBaseChange B S hS aSpace G d =
      ρ.liftBaseChange (chartRing B S hS U.1 U.2 d.U) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | tmul x s =>
      rw [Function.comp_apply, modulePullbackChartBaseChange_tmul, LinearMap.map_smul,
        LinearMap.liftBaseChange_tmul]
      exact congrArg (fun y => x • y)
        (comparisonAlgebraicSpacesModules_app_chartSection B S hS p q r hp hq eU eV a f g hf hg φ
          aSpace ha hr hφ hab ℱ d s)
    | add x y hx hy =>
      simp only [Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  exact (Function.Bijective.of_comp_iff _ h1).1 (h3 ▸ h2)

/-- **The comparison map of equation 076R is an isomorphism on modules with the flat base change
property, along a flat morphism of algebraic spaces.**

Let `φ : a ⋙ g ≅ f` be a 2-commutative triangle of 1-morphisms of categories fibred in groupoids
over `(Sch/S)_{fppf}` whose source categories `𝒰`, `𝒱` are representable by algebraic spaces
`U`, `V`, with `aSpace : U ⟶ V` the morphism of algebraic spaces corresponding to `a`, assumed
flat (Stacks 03ML), and let `ℱ` be an `𝒪_𝒳`-module in `LQCoh^{fbc}(𝒪_𝒳)`: locally
quasi-coherent (Stacks 06WJ) with the flat base change property (Stacks 0762).  Then the
comparison map
```
c_φ : a_small^*(g^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale}
```
of equation 076R is an isomorphism of `𝒪_U`-modules.

The proof checks bijectivity on the sections over the charts carrying an affine chart diagram
over `aSpace`
(`bijective_comparisonAlgebraicSpacesModules_app_of_locallyQuasicoherentFlatBaseChangeSheaf`),
which are cover-dense
(`AlgebraicGeometry.Space.isIso_of_bijective_app_of_hasAffineChartDiagram`). -/
theorem isIso_comparisonAlgebraicSpacesModules_of_locallyQuasicoherentFlatBaseChangeSheaf
    (haflat : IsFlat B S hS aSpace.hom)
    (ℱ : SheafOfModules.{u}
      (Stack.ringStructureSheafCore B S hS r hr (etaleTopology B)
        (Stack.etaleTopology_le_topology B)))
    (hℱ : Stack.locallyQuasicoherentFlatBaseChangeSheaf B E h S hS r hr ℱ) :
    IsIso (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ
      hab ℱ) := by
  refine isIso_of_bijective_app_of_hasAffineChartDiagram B S hS aSpace _ fun W hW => ?_
  obtain ⟨hWaff, V', t, ht, hV'aff⟩ := hW
  exact bijective_comparisonAlgebraicSpacesModules_app_of_locallyQuasicoherentFlatBaseChangeSheaf
    B E h S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab haflat ℱ hℱ ⟨W, V', t, ht.symm⟩
    hWaff hV'aff

end Triangle

end AlgebraicGeometry.Space

end
