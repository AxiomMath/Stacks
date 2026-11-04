module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace

/-!
# The comparison squares of a presentation of a category fibred in groupoids

Let `S` be a scheme in a big fppf site and let

```
𝒰 --a--> 𝒱
  \      |
   f     g
    \    |
     v   v
       𝒳
```

be a 2-commutative triangle of 1-morphisms of categories fibred in groupoids over
`(Sch/S)_{fppf}` with 2-morphism `φ : a ⋙ g ≅ f`, with `𝒰` and `𝒱` representable by algebraic
spaces `U` and `V`.  Equation 076R of the source attaches to it the comparison map

```
c_φ : a_small^*(g^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale}
```

of `𝒪_U`-modules, for every `𝒪_𝒳`-module `ℱ`; it is
`AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules`. The map `c_φ` is **natural in `ℱ`**: a
morphism `ψ : ℱ ⟶ ℋ` of `𝒪_𝒳`-modules gives a commutative square

```
a_small^*(g^*ℱ|_{V_étale}) --c_φ(ℱ)--> f^*ℱ|_{U_étale}
         |                                  |
a_small^*(g^*ψ|_{V_étale})             f^*ψ|_{U_étale}
         v                                  v
a_small^*(g^*ℋ|_{V_étale}) --c_φ(ℋ)--> f^*ℋ|_{U_étale}
```

of `𝒪_U`-modules.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImageMap` is `ψ ↦ f^*ψ|_{U_étale}`, the
  action on morphisms of the restriction `ℱ ↦ f^*ℱ|_{U_étale}` of
  `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage`.

## Main results

* `AlgebraicGeometry.Space.moduleComparisonPushforwardHom_naturality`: the map
  `g^*ℱ|_{V_étale} ⟶ a_{small,*}(f^*ℱ|_{U_étale})` of equation 076R is natural in `ℱ`.
* `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_naturality`: the comparison map of
  equation 076R is natural in `ℱ`.
* `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules_square_app`: a commutative square
  through the comparison map of equation 076R, read on sections over a diagram of charts.
* `AlgebraicGeometry.Space.comparison_etaleRestrictedHom`: for a 1-morphism `x` out of the
  presentation of the object space of a groupoid in algebraic spaces and the two 2-commutative
  triangles attached to the source and the target of the groupoid, every `x^*ψ|_{U_étale}` fits
  into the commutative diagram of Stacks 076S.

## References

* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 076S](https://stacks.math.columbia.edu/tag/076S)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w' v'' w''

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS)
  (r : 𝒳 ⥤ BigFppfOver B S hS)

/-- The restriction `f^*ψ|_{U_étale}` of a morphism `ψ` of `𝒪_𝒳`-modules to the small étale site
of the algebraic space `U` representing `𝒰`: the morphism of `𝒪_U`-modules between the
restrictions `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` of its source and
target.

Restriction of modules along the functor `U_étale ⥤ 𝒳` of
`AlgebraicGeometry.Space.etaleChartToFibred` is a functor, and this is its action on morphisms;
over an étale chart `W` of `U` the component of the restricted morphism is the component of `ψ`
over the object `f(u_U W)` of `𝒳`. -/
noncomputable def etaleRestrictedModuleInverseImageMap (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)
    {ℱ ℋ : inheritedEtaleModules B S hS r hr} (ψ : ℱ ⟶ ℋ) :
    etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ ⟶
      etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℋ :=
  haveI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  (SheafOfModules.pushforward (etaleChartStructureHom B S hS p r hp hr eU f hf)).map ψ

/-- The component over an étale chart `W` of `U` of the restriction of a morphism `ψ` of
`𝒪_𝒳`-modules is the component of `ψ` over the object `f(u_U W)` of `𝒳`. -/
theorem etaleRestrictedModuleInverseImageMap_app (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)
    {ℱ ℋ : inheritedEtaleModules B S hS r hr} (ψ : ℱ ⟶ ℋ) (W : SmallEtale B S hS U.1)
    (s : (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ).val.obj (op W)) :
    (etaleRestrictedModuleInverseImageMap B S hS p r hp hr eU f hf ψ).val.app (op W) s =
      ψ.val.app (op (f.obj ((restrictionFunctor B S hS U.1 p eU).obj W))) s :=
  rfl

/-! ### Naturality of the comparison map of equation 076R in the module -/

section Triangle

variable (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
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

/-- The linear map of sections attached by the chartwise universal property of the direct image
of Stacks 03LU to the map `g^*ℱ|_{V_étale} ⟶ a_{small,*}(f^*ℱ|_{U_étale})` of equation 076R is
the one that map was built from. -/
private theorem homEquiv_moduleComparisonPushforwardHom
    (ℱ : inheritedEtaleModules B S hS r hr) :
    modulePushforwardHomEquiv B S hS aSpace
        (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ)
        (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ)
        (moduleComparisonPushforwardHom B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
          hr hφ hab ℱ) =
      moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab ℱ :=
  (modulePushforwardHomEquiv B S hS aSpace _ _).apply_symm_apply _

/-- **The map into the direct image of equation 076R is natural in the module.** -/
theorem moduleComparisonPushforwardHom_naturality
    {ℱ ℋ : inheritedEtaleModules B S hS r hr} (ψ : ℱ ⟶ ℋ) :
    moduleComparisonPushforwardHom B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
          hr hφ hab ℱ ≫
        (modulePushforward B S hS aSpace).map
          (etaleRestrictedModuleInverseImageMap B S hS p r hp hr eU f hf ψ) =
      etaleRestrictedModuleInverseImageMap B S hS q r hq hr eV g hg ψ ≫
        moduleComparisonPushforwardHom B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
          hr hφ hab ℋ := by
  refine (modulePushforwardHomEquiv B S hS aSpace
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℋ)
    (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ)).injective ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  rw [modulePushforwardHomEquiv_app_comp_right, modulePushforwardHomEquiv_app_comp_left,
    homEquiv_moduleComparisonPushforwardHom, homEquiv_moduleComparisonPushforwardHom,
    moduleComparisonFMap_app, moduleComparisonFMap_app]
  refine Eq.trans (etaleRestrictedModuleInverseImageMap_app B S hS p r hp hr eU f hf ψ d.U
    (ℱ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op s)) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply ψ.val
    (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op s) ?_
  exact congrArg
    (fun z ↦ ℋ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op z)
    (etaleRestrictedModuleInverseImageMap_app B S hS q r hq hr eV g hg ψ d.V s).symm

/-- **Stacks 076R is natural in the module.**  A morphism `ψ : ℱ ⟶ ℋ` of `𝒪_𝒳`-modules gives a
commutative square

```
a_small^*(g^*ℱ|_{V_étale}) --c_φ(ℱ)--> f^*ℱ|_{U_étale}
         |                                  |
a_small^*(g^*ψ|_{V_étale})             f^*ψ|_{U_étale}
         v                                  v
a_small^*(g^*ℋ|_{V_étale}) --c_φ(ℋ)--> f^*ℋ|_{U_étale}
```

of `𝒪_U`-modules. -/
theorem comparisonAlgebraicSpacesModules_naturality
    {ℱ ℋ : inheritedEtaleModules B S hS r hr} (ψ : ℱ ⟶ ℋ) :
    comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
          hr hφ hab ℱ ≫
        etaleRestrictedModuleInverseImageMap B S hS p r hp hr eU f hf ψ =
      (modulePullback B S hS aSpace).map
          (etaleRestrictedModuleInverseImageMap B S hS q r hq hr eV g hg ψ) ≫
        comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
          hr hφ hab ℋ := by
  refine ((modulePullbackAdjunction B S hS aSpace).homEquiv
    (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ)
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℋ)).injective ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    comparisonAlgebraicSpacesModules_adjoint, comparisonAlgebraicSpacesModules_adjoint]
  exact moduleComparisonPushforwardHom_naturality B S hS p q r hp hq eU eV a f g hf hg φ
    aSpace ha hr hφ hab ψ

/-- **A square through the comparison map of equation 076R, read on sections.**  Let
`ϕ : g^*ℱ|_{V_étale} ⟶ g^*ℋ|_{V_étale}` and `χ : f^*ℱ|_{U_étale} ⟶ f^*ℋ|_{U_étale}` be
morphisms of modules on the two small étale sites for which the square

```
a_small^*(g^*ℱ|_{V_étale}) --c_φ(ℱ)--> f^*ℱ|_{U_étale}
         |                                  |
   a_small^*ϕ                               χ
         v                                  v
a_small^*(g^*ℋ|_{V_étale}) --c_φ(ℋ)--> f^*ℋ|_{U_étale}
```

commutes.  Then over every commutative diagram `d` of étale scheme charts over `a`, `χ` carries
the restriction of a section `s` of `ℱ` along `AlgebraicGeometry.Space.comparisonMorphism` to the
restriction of `ϕ(s)`. -/
theorem comparisonAlgebraicSpacesModules_square_app
    {ℱ ℋ : inheritedEtaleModules B S hS r hr}
    (ϕ : etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ ⟶
      etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℋ)
    (χ : etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ ⟶
      etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℋ)
    (hsq : comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
          hr hφ hab ℱ ≫ χ =
      (modulePullback B S hS aSpace).map ϕ ≫
        comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
          hr hφ hab ℋ)
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (s : (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ).val.obj (op d.V)) :
    χ.val.app (op d.U)
        (ℱ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op s) =
      ℋ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op
        (ϕ.val.app (op d.V) s) := by
  have h₁ := congrArg ((modulePullbackAdjunction B S hS aSpace).homEquiv
    (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ)
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℋ)) hsq
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    comparisonAlgebraicSpacesModules_adjoint, comparisonAlgebraicSpacesModules_adjoint] at h₁
  have h₂ := congrArg (fun m => (modulePushforwardHomEquiv B S hS aSpace
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℋ)
    (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ) m).app d s) h₁
  rwa [modulePushforwardHomEquiv_app_comp_right, modulePushforwardHomEquiv_app_comp_left,
    homEquiv_moduleComparisonPushforwardHom, homEquiv_moduleComparisonPushforwardHom,
    moduleComparisonFMap_app, moduleComparisonFMap_app] at h₂

end Triangle

/-! ### The comparison squares of a groupoid presentation -/

section Presentation

variable {R : AlgebraicSpaces B S hS}
  {ℛ : Type v} [Category.{w} ℛ]
  (pR : ℛ ⥤ BigFppfOver B S hS) (pU : 𝒰 ⥤ BigFppfOver B S hS)
  (hpR : pR.IsFiberedInGroupoids) (hpU : pU.IsFiberedInGroupoids)
  (hr : r.IsFiberedInGroupoids)
  (eR : StacksRepresentableCFG.EquivalenceOver pR
    (presheafOfCategories (R.1 ⋙ typeToCat)).p)
  (eU : StacksRepresentableCFG.EquivalenceOver pU
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (sLeg tLeg : ℛ ⥤ 𝒰) (x : 𝒰 ⥤ 𝒳) (xs : ℛ ⥤ 𝒳)
  (hx : pU.IsFibredOneMorphism r x) (hxs : pR.IsFibredOneMorphism r xs)
  (φs : sLeg ⋙ x ≅ xs) (φt : tLeg ⋙ x ≅ xs)
  (sSpace tSpace : R ⟶ U)
  (has : schemeChartFunctor B S hS R.1 pR eR ⋙ sLeg ≅
    CostructuredArrow.map sSpace.hom ⋙ schemeChartFunctor B S hS U.1 pU eU)
  (hat : schemeChartFunctor B S hS R.1 pR eR ⋙ tLeg ≅
    CostructuredArrow.map tSpace.hom ⋙ schemeChartFunctor B S hS U.1 pU eU)
  (hφs : ∀ Y : ℛ, r.IsHomLift (𝟙 (r.obj (xs.obj Y))) (φs.inv.app Y))
  (hφt : ∀ Y : ℛ, r.IsHomLift (𝟙 (r.obj (xs.obj Y))) (φt.inv.app Y))
  (habs : ∀ Z : CostructuredArrow yoneda R.1,
    pU.IsHomLift (𝟙 (pU.obj (sLeg.obj ((schemeChartFunctor B S hS R.1 pR eR).obj Z))))
      (has.hom.app Z))
  (habt : ∀ Z : CostructuredArrow yoneda R.1,
    pU.IsHomLift (𝟙 (pU.obj (tLeg.obj ((schemeChartFunctor B S hS R.1 pR eR).obj Z))))
      (hat.hom.app Z))

/-- **The image of `ψ ↦ x^*ψ|_{U_étale}` consists of comparison-compatible maps.**

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `S`, let `𝒳` be a category fibred
in groupoids over `(Sch/S)_{fppf}`, and let `x : 𝒰 ⥤ 𝒳` be a 1-morphism out of the presentation
of the object space `U`;  for `𝒳 = [U/R]` and `x` the canonical projection of Stacks 044R
this is the situation of Stacks 076S.  Let `ℛ` be the presentation of the arrow space `R`, let
`sLeg, tLeg : ℛ ⥤ 𝒰` be the 1-morphisms realizing the source and the target of the groupoid as
morphisms `sSpace, tSpace : R ⟶ U` of algebraic spaces, and let `φs : sLeg ⋙ x ≅ xs` and
`φt : tLeg ⋙ x ≅ xs` be 2-morphisms into a common 1-morphism `xs : ℛ ⥤ 𝒳`.

Then for every morphism `ψ : ℱ ⟶ ℋ` of `𝒪_𝒳`-modules the map `varphi = x^*ψ|_{U_étale}` fits
into the commutative diagram of Stacks 076S:  both the square

```
s_small^*(x^*ℱ|_{U_étale}) --c_{φs}(ℱ)--> (x ∘ s)^*ℱ|_{R_étale}
          |                                        |
s_small^*varphi                          (x ∘ s)^*ψ|_{R_étale}
          v                                        v
s_small^*(x^*ℋ|_{U_étale}) --c_{φs}(ℋ)--> (x ∘ s)^*ℋ|_{R_étale}
```

and its analogue for the target commute, the horizontal arrows being the comparison maps of
equation 076R. -/
theorem comparison_etaleRestrictedHom
    {ℱ ℋ : inheritedEtaleModules B S hS r hr} (ψ : ℱ ⟶ ℋ) :
    (comparisonAlgebraicSpacesModules B S hS pR pU r hpR hpU eR eU sLeg xs x hxs hx φs
            sSpace has hr hφs habs ℱ ≫
          etaleRestrictedModuleInverseImageMap B S hS pR r hpR hr eR xs hxs ψ =
        (modulePullback B S hS sSpace).map
            (etaleRestrictedModuleInverseImageMap B S hS pU r hpU hr eU x hx ψ) ≫
          comparisonAlgebraicSpacesModules B S hS pR pU r hpR hpU eR eU sLeg xs x hxs hx φs
            sSpace has hr hφs habs ℋ) ∧
      comparisonAlgebraicSpacesModules B S hS pR pU r hpR hpU eR eU tLeg xs x hxs hx φt
            tSpace hat hr hφt habt ℱ ≫
          etaleRestrictedModuleInverseImageMap B S hS pR r hpR hr eR xs hxs ψ =
        (modulePullback B S hS tSpace).map
            (etaleRestrictedModuleInverseImageMap B S hS pU r hpU hr eU x hx ψ) ≫
          comparisonAlgebraicSpacesModules B S hS pR pU r hpR hpU eR eU tLeg xs x hxs hx φt
            tSpace hat hr hφt habt ℋ :=
  ⟨comparisonAlgebraicSpacesModules_naturality B S hS pR pU r hpR hpU eR eU sLeg xs x hxs hx
      φs sSpace has hr hφs habs ψ,
    comparisonAlgebraicSpacesModules_naturality B S hS pR pU r hpR hpU eR eU tLeg xs x hxs hx
      φt tSpace hat hr hφt habt ψ⟩

end Presentation

end AlgebraicGeometry.Space

end
