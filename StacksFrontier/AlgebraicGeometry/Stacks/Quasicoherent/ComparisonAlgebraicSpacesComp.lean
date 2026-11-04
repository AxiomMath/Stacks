module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionTransitionCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompHomExt
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComparisonAlgebraicSpacesIso

/-!
# The composition law for the comparison maps of equation 076R

Let
```
𝒲 --b--> 𝒰 --a--> 𝒱
   \      |      /
    h     f     g
     \    |    /
      v   v   v
         𝒳
```
be 1-morphisms of categories fibred in groupoids over `(Sch/S)_{fppf}` with 2-morphisms
`ψ : b ⋙ f ≅ h` and `φ : a ⋙ g ≅ f`, where `𝒲`, `𝒰`, `𝒱` are representable by algebraic spaces
`W`, `U`, `V`, and let `c : 𝒲 ⥤ 𝒱` with `χ : c ⋙ g ≅ h` be a third triangle over the composite
`W ⟶ U ⟶ V`.  Equation 076R attaches comparison maps `c_φ`, `c_ψ`, `c_χ` to the three triangles.
If the morphisms of `𝒳` inducing them compose — on every pair of chart diagrams over
`W ⟶ U` and `U ⟶ V`, the comparison morphism of `χ` at the composite diagram is the comparison
morphism of `ψ` followed by that of `φ` — then
```
c_χ = (compIso)⁻¹ ≫ b_small^*(c_φ) ≫ c_ψ.
```
This is the composition law of the comparison maps, the module form of the compatibility of
Stacks 075D (1); it is what the cocycle condition of the descent datum of Stacks 06WT is made
of.

## Main results

* `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_comp`: the composition law.

## Implementation notes

Both sides are morphisms out of an iterated inverse image once the comparison of Stacks 03LU is
moved across, and those are determined on iterated chart sections
(`AlgebraicGeometry.Space.modulePullback_comp_hom_ext`).  On iterated chart sections both sides
are restriction of sections of `ℱ`: the left side along the comparison morphism of `χ` at the
composite diagram, by the chart formula of the comparison of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackCompIso_hom_chartSection_comp`), and the right side along
the two comparison morphisms in turn.  The hypothesis `hcomp` is the equation in `𝒳` saying these
agree; it is a statement about named morphisms of `𝒳` which each caller verifies.

## References

* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v v' v'' v''' w w' w'' w'''

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W U V : AlgebraicSpaces B S hS}
  {𝒲 : Type v'''} [Category.{w'''} 𝒲]
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p₀ : 𝒲 ⥤ BigFppfOver B S hS) (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS)
  (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp₀ : p₀.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (eW : StacksRepresentableCFG.EquivalenceOver p₀
    (presheafOfCategories (W.1 ⋙ typeToCat)).p)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (b : 𝒲 ⥤ 𝒰) (a : 𝒰 ⥤ 𝒱) (c : 𝒲 ⥤ 𝒱) (h : 𝒲 ⥤ 𝒳) (f : 𝒰 ⥤ 𝒳) (g : 𝒱 ⥤ 𝒳)
  (hh : p₀.IsFibredOneMorphism r h) (hf : p.IsFibredOneMorphism r f)
  (hg : q.IsFibredOneMorphism r g)
  (ψ : b ⋙ f ≅ h) (φ : a ⋙ g ≅ f) (χ : c ⋙ g ≅ h)
  (bSpace : W ⟶ U) (aSpace : U ⟶ V)
  (hb : schemeChartFunctor B S hS W.1 p₀ eW ⋙ b ≅
    CostructuredArrow.map bSpace.hom ⋙ schemeChartFunctor B S hS U.1 p eU)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hc : schemeChartFunctor B S hS W.1 p₀ eW ⋙ c ≅
    CostructuredArrow.map (bSpace ≫ aSpace).hom ⋙ schemeChartFunctor B S hS V.1 q eV)
  (hr : r.IsFiberedInGroupoids)
  (hψ : ∀ X : 𝒲, r.IsHomLift (𝟙 (r.obj (h.obj X))) (ψ.inv.app X))
  (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
  (hχ : ∀ X : 𝒲, r.IsHomLift (𝟙 (r.obj (h.obj X))) (χ.inv.app X))
  (hbb : ∀ Z : CostructuredArrow yoneda W.1,
    p.IsHomLift (𝟙 (p.obj (b.obj ((schemeChartFunctor B S hS W.1 p₀ eW).obj Z))))
      (hb.hom.app Z))
  (hab : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha.hom.app Z))
  (hcc : ∀ Z : CostructuredArrow yoneda W.1,
    q.IsHomLift (𝟙 (q.obj (c.obj ((schemeChartFunctor B S hS W.1 p₀ eW).obj Z))))
      (hc.hom.app Z))

/-- Restriction along two composable morphisms is restriction along a morphism equal to their
composite. -/
theorem _root_.PresheafOfModules.map_op_map_op_eq {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (K : PresheafOfModules.{u} R) {X₁ X₂ X₃ : C} (k₁ : X₁ ⟶ X₂) (k₂ : X₂ ⟶ X₃) (k : X₁ ⟶ X₃)
    (hk : k = k₁ ≫ k₂) (t : K.obj (op X₃)) :
    K.map k₁.op (K.map k₂.op t) = K.map k.op t := by
  subst hk
  rw [op_comp, PresheafOfModules.map_comp_apply]

section Values

variable (ℱ : inheritedEtaleModules.{u, v'', w'', u} B S hS r hr)
  {U₀ : SmallEtale B S hS W.1} {V₀ : SmallEtale B S hS U.1} {W₀ : SmallEtale B S hS V.1}
  (x : (SmallEtale.toOver B S hS W.1).obj U₀ ⟶ (SmallEtale.toOver B S hS U.1).obj V₀)
  (y : (SmallEtale.toOver B S hS U.1).obj V₀ ⟶ (SmallEtale.toOver B S hS V.1).obj W₀)
  (hx : U₀.1.hom ≫ bSpace.hom = yoneda.map x ≫ V₀.1.hom)
  (hy : V₀.1.hom ≫ aSpace.hom = yoneda.map y ≫ W₀.1.hom)
  (s : (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ).val.obj (op W₀))

/-- The two-step side of the composition law on an iterated chart section: restriction of
sections of `ℱ` along the comparison morphism of `φ`, then along that of `ψ`. -/
theorem comparisonAlgebraicSpacesModules_comp_left_apply :
    ((modulePullback B S hS bSpace).map
        (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr
          hφ hab ℱ) ≫
      comparisonAlgebraicSpacesModules B S hS p₀ p r hp₀ hp eW eU b h f hh hf ψ bSpace hb hr
        hψ hbb ℱ).val.app (op U₀)
      (modulePullbackChartSection B S hS bSpace _ ⟨U₀, V₀, x, hx⟩
        (modulePullbackChartSection B S hS aSpace _ ⟨V₀, W₀, y, hy⟩ s)) =
    ℱ.val.map (comparisonMorphism B S hS p₀ p eW eU b h f ψ bSpace hb ⟨U₀, V₀, x, hx⟩).op
      (ℱ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha ⟨V₀, W₀, y, hy⟩).op
        s) := by
  refine (comp_val_app_apply B S hS _ _ (op U₀) _).trans ?_
  erw [modulePullbackChartSection_map B S hS bSpace _ _ ⟨U₀, V₀, x, hx⟩,
    comparisonAlgebraicSpacesModules_chartSection B S hS p q r hp hq eU eV a f g hf hg φ
      aSpace ha hr hφ hab ℱ ⟨V₀, W₀, y, hy⟩ s]
  exact comparisonAlgebraicSpacesModules_chartSection B S hS p₀ p r hp₀ hp eW eU b h f hh hf
    ψ bSpace hb hr hψ hbb ℱ ⟨U₀, V₀, x, hx⟩ _

/-- The one-step side of the composition law on an iterated chart section: restriction of
sections of `ℱ` along the comparison morphism of `χ` at the composite diagram. -/
theorem comparisonAlgebraicSpacesModules_comp_right_apply :
    ((modulePullbackCompIso B S hS bSpace aSpace).hom.app _ ≫
      comparisonAlgebraicSpacesModules B S hS p₀ q r hp₀ hq eW eV c h g hh hg χ
        (bSpace ≫ aSpace) hc hr hχ hcc ℱ).val.app (op U₀)
      (modulePullbackChartSection B S hS bSpace _ ⟨U₀, V₀, x, hx⟩
        (modulePullbackChartSection B S hS aSpace _ ⟨V₀, W₀, y, hy⟩ s)) =
    ℱ.val.map (comparisonMorphism B S hS p₀ q eW eV c h g χ (bSpace ≫ aSpace) hc
      (ChartDiagram.comp B S hS bSpace aSpace x y hx hy)).op s := by
  refine (comp_val_app_apply B S hS _ _ (op U₀) _).trans ?_
  erw [modulePullbackCompIso_hom_chartSection_comp bSpace aSpace _ x y hx hy s]
  exact comparisonAlgebraicSpacesModules_chartSection B S hS p₀ q r hp₀ hq eW eV
    c h g hh hg χ (bSpace ≫ aSpace) hc hr hχ hcc ℱ
    (ChartDiagram.comp B S hS bSpace aSpace x y hx hy) s

end Values

/-- **The composition law for the comparison maps of equation 076R.**  If, on every pair of
chart diagrams over `W ⟶ U` and `U ⟶ V`, the comparison morphism of the triangle `χ` at the
composite diagram is the comparison morphism of `ψ` followed by that of `φ`, then
`b_small^*(c_φ) ≫ c_ψ` is the comparison of Stacks 03LU followed by `c_χ`. -/
theorem comparisonAlgebraicSpacesModules_comp
    (hcomp : ∀ {U₀ : SmallEtale B S hS W.1} {V₀ : SmallEtale B S hS U.1}
      {W₀ : SmallEtale B S hS V.1}
      (x : (SmallEtale.toOver B S hS W.1).obj U₀ ⟶ (SmallEtale.toOver B S hS U.1).obj V₀)
      (y : (SmallEtale.toOver B S hS U.1).obj V₀ ⟶ (SmallEtale.toOver B S hS V.1).obj W₀)
      (hx : U₀.1.hom ≫ bSpace.hom = yoneda.map x ≫ V₀.1.hom)
      (hy : V₀.1.hom ≫ aSpace.hom = yoneda.map y ≫ W₀.1.hom),
      comparisonMorphism B S hS p₀ q eW eV c h g χ (bSpace ≫ aSpace) hc
          (ChartDiagram.comp B S hS bSpace aSpace x y hx hy) =
        comparisonMorphism B S hS p₀ p eW eU b h f ψ bSpace hb ⟨U₀, V₀, x, hx⟩ ≫
          comparisonMorphism B S hS p q eU eV a f g φ aSpace ha ⟨V₀, W₀, y, hy⟩)
    (ℱ : inheritedEtaleModules.{u, v'', w'', u} B S hS r hr) :
    (modulePullback B S hS bSpace).map
        (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr
          hφ hab ℱ) ≫
      comparisonAlgebraicSpacesModules B S hS p₀ p r hp₀ hp eW eU b h f hh hf ψ bSpace hb hr
        hψ hbb ℱ =
    (modulePullbackCompIso B S hS bSpace aSpace).hom.app _ ≫
      comparisonAlgebraicSpacesModules B S hS p₀ q r hp₀ hq eW eV c h g hh hg χ
        (bSpace ≫ aSpace) hc hr hχ hcc ℱ := by
  refine modulePullback_comp_hom_ext B S hS bSpace aSpace _ _ _ _ ?_
  intro U₀ V₀ W₀ x y hx hy s
  refine (comparisonAlgebraicSpacesModules_comp_left_apply B S hS p₀ p q r hp₀ hp hq eW eU eV
    b a h f g hh hf hg ψ φ bSpace aSpace hb ha hr hψ hφ hbb hab ℱ x y hx hy s).trans ?_
  refine Eq.trans ?_ (comparisonAlgebraicSpacesModules_comp_right_apply B S hS p₀ q r hp₀ hq
    eW eV c h g hh hg χ bSpace aSpace hc hr hχ hcc ℱ x y hx hy s).symm
  exact PresheafOfModules.map_op_map_op_eq ℱ.val
    (comparisonMorphism B S hS p₀ p eW eU b h f ψ bSpace hb ⟨U₀, V₀, x, hx⟩)
    (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha ⟨V₀, W₀, y, hy⟩)
    (comparisonMorphism B S hS p₀ q eW eV c h g χ (bSpace ≫ aSpace) hc
      (ChartDiagram.comp B S hS bSpace aSpace x y hx hy)) (hcomp x y hx hy) s

end AlgebraicGeometry.Space

end
