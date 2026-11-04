module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PullbackTransportChartSection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComparisonAlgebraicSpacesIso

/-!
# Comparison maps of equation 076R along equal morphisms of algebraic spaces

Two comparison maps of equation 076R whose morphisms of algebraic spaces `aSpace`, `aSpace'` are
equal, and whose comparison morphisms agree on every chart diagram, differ by the transport
`aSpace^*𝒢 ⟶ aSpace'^*𝒢` along that equality.  Both sides are restriction of sections of `ℱ` on
chart sections, so this is checked there.

## Main results

* `AlgebraicGeometry.Space.modulePullback_hom_ext_of_chartSection`: two morphisms out of an
  inverse image `g^*M` which agree on the chart sections are equal.
* `AlgebraicGeometry.Space.pullbackTransport_comp_comparisonAlgebraicSpacesModules`: the
  transport followed by the second comparison map is the first.

## References

* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v v' v'' w w' w''

namespace AlgebraicGeometry.Space

/-- **Two morphisms out of an inverse image of modules which agree on the chart sections are
equal.** -/
theorem modulePullback_hom_ext_of_chartSection (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
    (g : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (u v : (modulePullback B S hS g).obj M ⟶ N)
    (h : ∀ (e : ChartDiagram B S hS X.1 Y.1 g.hom) (s : M.val.obj (op e.V)),
      u.val.app (op e.U) (modulePullbackChartSection B S hS g M e s) =
        v.val.app (op e.U) (modulePullbackChartSection B S hS g M e s)) :
    u = v := by
  refine (modulePullbackFMapEquiv B S hS g N M).injective ?_
  refine ModuleFMap.ext B S hS (funext fun e ↦ funext fun s ↦ ?_)
  refine Eq.trans (modulePullbackHomFMap_app B S hS g M N u e s) ?_
  refine Eq.trans ?_ (modulePullbackHomFMap_app B S hS g M N v e s).symm
  refine Eq.trans (congrArg (fun w ↦ u.val.app (op e.U) w)
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M e s)) ?_
  refine Eq.trans (h e s) ?_
  exact congrArg (fun w ↦ v.val.app (op e.U) w)
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M e s).symm

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
  (a a' : 𝒰 ⥤ 𝒱) (f : 𝒰 ⥤ 𝒳) (g : 𝒱 ⥤ 𝒳)
  (hf : p.IsFibredOneMorphism r f) (hg : q.IsFibredOneMorphism r g)
  (φ : a ⋙ g ≅ f) (φ' : a' ⋙ g ≅ f) (aSpace aSpace' : U ⟶ V)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (ha' : schemeChartFunctor B S hS U.1 p eU ⋙ a' ≅
    CostructuredArrow.map aSpace'.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hr : r.IsFiberedInGroupoids)
  (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
  (hφ' : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ'.inv.app X))
  (hab : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha.hom.app Z))
  (hab' : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a'.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha'.hom.app Z))

omit ha' hab' in
/-- **Comparison maps with equal comparison morphisms are equal.** -/
theorem comparisonAlgebraicSpacesModules_eq_of_comparisonMorphism_eq
    (ha₂ : schemeChartFunctor B S hS U.1 p eU ⋙ a' ≅
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
    (hab₂ : ∀ Z : CostructuredArrow yoneda U.1,
      q.IsHomLift (𝟙 (q.obj (a'.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
        (ha₂.hom.app Z))
    (hcm : ∀ d : ChartDiagram B S hS U.1 V.1 aSpace.hom,
      comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d =
        comparisonMorphism B S hS p q eU eV a' f g φ' aSpace ha₂ d)
    (ℱ : inheritedEtaleModules.{u, v'', w'', u} B S hS r hr) :
    comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a' f g hf hg φ' aSpace ha₂ hr
        hφ' hab₂ ℱ =
      comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr
        hφ hab ℱ := by
  refine modulePullback_hom_ext_of_chartSection B S hS aSpace _ _ _ _ fun d s ↦ ?_
  have e1 := comparisonAlgebraicSpacesModules_chartSection B S hS p q r hp hq eU eV a' f g hf hg
    φ' aSpace ha₂ hr hφ' hab₂ ℱ d s
  have e2 := comparisonAlgebraicSpacesModules_chartSection B S hS p q r hp hq eU eV a f
    g hf hg φ aSpace ha hr hφ hab ℱ d s
  rw [e1, e2, hcm d]

/-- Transport along `rfl` is the identity. -/
theorem pullbackTransport_rfl {T X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)
    (f : T ⟶ X) : pullbackTransport M (rfl : f = f) = 𝟙 _ :=
  rfl

/-- **Comparison maps along equal morphisms of algebraic spaces.**  If `aSpace = aSpace'` and the
comparison morphisms of the two triangles agree on every chart diagram (read over `aSpace'`),
then the transport `aSpace^*𝒢 ⟶ aSpace'^*𝒢` followed by the second comparison map of
equation 076R is the first. -/
theorem pullbackTransport_comp_comparisonAlgebraicSpacesModules (h : aSpace = aSpace')
    (hcm : ∀ d : ChartDiagram B S hS U.1 V.1 aSpace.hom,
      comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d =
        comparisonMorphism B S hS p q eU eV a' f g φ' aSpace' ha' (d.transport B S hS h))
    (ℱ : inheritedEtaleModules.{u, v'', w'', u} B S hS r hr) :
    pullbackTransport (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ) h ≫
        comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a' f g hf hg φ' aSpace' ha' hr
          hφ' hab' ℱ =
      comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr
        hφ hab ℱ := by
  subst h
  rw [pullbackTransport_rfl, Category.id_comp]
  exact comparisonAlgebraicSpacesModules_eq_of_comparisonMorphism_eq B S hS p q r hp hq eU eV
    a a' f g hf hg φ φ' aSpace ha hr hφ hφ' hab ha' hab' hcm ℱ

end AlgebraicGeometry.Space

end
