module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartSourceNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackEquations
public import StacksFrontier.CategoryTheory.CommutingSquares
public import StacksFrontier.CategoryTheory.EqToHomAbsorption
public import StacksFrontier.CategoryTheory.EqToHomAbsorptionSupplement

/-!
# The chart-level source square

`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso` exhibits the inverse image of
`a^*Ω_{Y/Bb}` to the small étale site of an étale chart of the source as the associated module of
the Zariski cotangent sheaf of the chart square. It is natural in the chart of the source:
passing to a smaller chart commutes with it, up to the comparisons of [Stacks Project, Tag 03LU]
in front and the Zariski comparison of two pullback cotangent sheaves behind.

The comparison is a composite of three factors — `AlgebraicGeometry.Space.modulePullbackCompIso`
at the chart, `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso`, and the change
of the inner sheaf by `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso` — and its square is the
pasting of the squares of the three factors.

## Main results

* `AlgebraicGeometry.Space.schemeSpaceMap_eq_representedSpaceMap`,
  `AlgebraicGeometry.Space.modulePullbackCompIso_representedSpaceMap` and
  `AlgebraicGeometry.Space.modulePullback_map_schemeSpaceMap`: the two spellings of a morphism of
  represented spaces agree, at the morphism, at the comparison of [Stacks Project, Tag 03LU] and
  under the inverse image.
* `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso_hom_square`: the square of the
  middle factor, granted the square of its own last factor.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_chartPullback`:
  [Stacks Project, Tag 03LU]'s composition law at the middle factor's last factor.
* `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso_hom_square_of_factorization`:
  the square of the middle factor.
* `AlgebraicGeometry.Space.representedAssociatedModule_cotangentSheafIso_square`: the square of
  the last factor, the Zariski change of the inner sheaf.
* `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom_square`: the source
  comparison of a chart presentation is natural in the chart of the source.
* `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom_square_of_chartMap`: the
  same at a morphism of étale scheme charts of the source.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {Bb Z Y : AlgebraicSpaces B S hS} {W V : BigFppfOver B S hS}

/-! ### The two spellings of a morphism of represented spaces -/

/-- **The comparison of [Stacks Project, Tag 03LU] does not see which of the two spellings of a
morphism of represented spaces it is given**, at the isomorphism. -/
theorem modulePullbackCompIso_representedSpaceMap {T T' : BigFppfOver B S hS}
    (ρ : T' ⟶ T) (r : T ⟶ W) :
    modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ) (schemeSpaceMap r) =
      modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ)
        (representedSpaceMap B S hS r) :=
  rfl

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_representedSpaceMap` at a component. -/
theorem modulePullbackCompIso_hom_app_representedSpaceMap {T T' : BigFppfOver B S hS}
    (ρ : T' ⟶ T) (r : T ⟶ W)
    (M : Modules.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ) (schemeSpaceMap r)).hom.app M =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ)
        (representedSpaceMap B S hS r)).hom.app M :=
  congrArg (fun z => z.hom.app M) (modulePullbackCompIso_representedSpaceMap B S hS ρ r)

/-- **The two spellings of a morphism of represented spaces are equal**:
`AlgebraicGeometry.Space.schemeSpaceMap r = AlgebraicGeometry.Space.representedSpaceMap r`. -/
theorem schemeSpaceMap_eq_representedSpaceMap {T T₀ : BigFppfOver B S hS} (r : T ⟶ T₀) :
    schemeSpaceMap r = representedSpaceMap B S hS r :=
  rfl

/-- **The comparison of [Stacks Project, Tag 03LU] with *both* of its arguments crossed at
once**, at the isomorphism. -/
theorem modulePullbackCompIso_representedSpaceMap₂ {T T' : BigFppfOver B S hS}
    (ρ : T' ⟶ T) (r : T ⟶ W) :
    modulePullbackCompIso B S hS (schemeSpaceMap ρ) (schemeSpaceMap r) =
      modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ)
        (representedSpaceMap B S hS r) :=
  rfl

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_representedSpaceMap₂` at a component. -/
theorem modulePullbackCompIso_hom_app_representedSpaceMap₂ {T T' : BigFppfOver B S hS}
    (ρ : T' ⟶ T) (r : T ⟶ W)
    (M : Modules.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2) :
    (modulePullbackCompIso B S hS (schemeSpaceMap ρ) (schemeSpaceMap r)).hom.app M =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS ρ)
        (representedSpaceMap B S hS r)).hom.app M :=
  congrArg (fun z => z.hom.app M) (modulePullbackCompIso_representedSpaceMap₂ B S hS ρ r)

/-- **The chart's structure morphism is natural in the chart, at the represented reading of the
chart space.** `AlgebraicGeometry.Space.chartMap_comp_chartToSpace` with the morphism of chart
spaces written as `AlgebraicGeometry.Space.schemeSpaceMap` of the morphism of the site under the
chart. -/
theorem schemeSpaceMap_toOver_comp_chartToSpace (X : AlgebraicSpaces B S hS)
    {A A' : SmallEtale B S hS X.1} (f : A' ⟶ A) :
    schemeSpaceMap ((SmallEtale.toOver B S hS X.1).map f) ≫
        (chartToSpace B S hS X A :
          schemeSpace ((SmallEtale.toOver B S hS X.1).obj A) ⟶ X) =
      (chartToSpace B S hS X A' :
        schemeSpace ((SmallEtale.toOver B S hS X.1).obj A') ⟶ X) :=
  chartMap_comp_chartToSpace B S hS X f

/-! ### The two spellings under the inverse image -/

/-- **The inverse image does not see which of the two spellings of a morphism of represented
spaces it is given**, at the level of the *functor*. -/
theorem modulePullback_schemeSpaceMap_eq {T T₀ : BigFppfOver B S hS} (r : T ⟶ T₀) :
    modulePullback B S hS (schemeSpaceMap r) =
      modulePullback B S hS (representedSpaceMap B S hS r) :=
  congrArg (modulePullback B S hS) (schemeSpaceMap_eq_representedSpaceMap B S hS r)

/-- `AlgebraicGeometry.Space.modulePullback_schemeSpaceMap_eq` at a morphism of modules, up to
the transports along two given equations of objects. -/
theorem modulePullback_map_eqToHom_schemeSpaceMap {T T₀ : BigFppfOver B S hS} (r : T ⟶ T₀)
    {M N : Modules.{u, u} B S hS (schemeSpace T₀).1 (schemeSpace T₀).2} (ζ : M ⟶ N)
    (hΦ : (modulePullback B S hS (schemeSpaceMap r)).obj M =
            (modulePullback B S hS (representedSpaceMap B S hS r)).obj M)
    (hΨ : (modulePullback B S hS (representedSpaceMap B S hS r)).obj N =
            (modulePullback B S hS (schemeSpaceMap r)).obj N) :
    (modulePullback B S hS (schemeSpaceMap r)).map ζ =
      eqToHom hΦ ≫ (modulePullback B S hS (representedSpaceMap B S hS r)).map ζ ≫ eqToHom hΨ :=
  CategoryTheory.Functor.congr_hom_of_eq (modulePullback_schemeSpaceMap_eq B S hS r) ζ hΦ hΨ

/-- **The inverse image does not see which of the two spellings of a morphism of represented
spaces it is given**, at an arbitrary morphism of modules. -/
theorem modulePullback_map_schemeSpaceMap {T T₀ : BigFppfOver B S hS} (r : T ⟶ T₀)
    {M N : Modules.{u, u} B S hS (schemeSpace T₀).1 (schemeSpace T₀).2} (ζ : M ⟶ N)
    (hΦ : (modulePullback B S hS (schemeSpaceMap r)).obj M =
            (modulePullback B S hS (representedSpaceMap B S hS r)).obj M)
    (hΨ : (modulePullback B S hS (representedSpaceMap B S hS r)).obj N =
            (modulePullback B S hS (schemeSpaceMap r)).obj N) :
    (modulePullback B S hS (schemeSpaceMap r)).map ζ =
      (modulePullback B S hS (representedSpaceMap B S hS r)).map ζ :=
  (modulePullback_map_eqToHom_schemeSpaceMap B S hS r ζ hΦ hΨ).trans
    ((CategoryTheory.eqToHom_comp_of_refl hΦ _).trans
      (CategoryTheory.comp_eqToHom_of_refl hΨ _))

/-! ### The square of the middle comparison -/

/-- **The square of `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso` in a
morphism `ρ` of the site**, granted the square of its last factor. -/
theorem chartCompositeDifferentialsAssociatedIso_hom_square (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) (r' : T' ⟶ W)
    (c : schemeSpace T ⟶ Y) (hc : c = schemeSpaceMap r ≫ w)
    (c' : schemeSpace T' ⟶ Y) (hc' : c' = schemeSpaceMap r' ≫ w)
    (hd : schemeSpaceMap ρ ≫ c = c')
    (ht : schemeSpaceMap ρ ≫ schemeSpaceMap r = schemeSpaceMap r')
    (he : schemeSpaceMap ρ ≫ schemeSpaceMap r ≫ w = schemeSpaceMap r' ≫ w)
    {Φ : _}
    (sP : (modulePullback B S hS (schemeSpaceMap ρ)).map
            (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).hom ≫ Φ =
          ((modulePullbackCompIso B S hS (schemeSpaceMap ρ) (schemeSpaceMap r)).hom.app
              ((modulePullback B S hS w).obj (sheafOfDifferentials B S hS q)) ≫
            eqToHom (congrArg (fun g : schemeSpace T' ⟶ schemeSpace W =>
              (modulePullback B S hS w ⋙ modulePullback B S hS g).obj
                (sheafOfDifferentials B S hS q)) ht)) ≫
            (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r').hom) :
    (modulePullback B S hS (schemeSpaceMap ρ)).map
          (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r c hc).hom ≫ Φ =
      ((modulePullbackCompIso B S hS (schemeSpaceMap ρ) c).hom.app
            (sheafOfDifferentials B S hS q) ≫
          eqToHom (congrArg (fun g : schemeSpace T' ⟶ Y =>
            (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hd)) ≫
        (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r' c' hc').hom :=
  CategoryTheory.square_of_functor_factorizations (modulePullback B S hS (schemeSpaceMap ρ))
    (chartCompositeDifferentialsAssociatedIso_hom B S hS q w v k hw hv hsq r c hc)
    (chartCompositeDifferentialsAssociatedIso_hom B S hS q w v k hw hv hsq r' c' hc')
    (modulePullbackCompIso_map_eqToHom_square' B S hS (schemeSpaceMap ρ) hc
      c' (schemeSpaceMap r' ≫ w) hd he (sheafOfDifferentials B S hS q)
      (congrArg (fun g : schemeSpace T' ⟶ Y =>
        (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hc')
      (eqToIso (congrArg (fun g : schemeSpace T ⟶ Y =>
        (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hc)).hom
      (eqToIso.hom _)
      (eqToIso (congrArg (fun g : schemeSpace T' ⟶ Y =>
        (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hc')).hom
      (eqToIso.hom _))
    (headSquareInv_app B S hS (schemeSpaceMap ρ) (schemeSpaceMap r) w (schemeSpaceMap r') ht
      (sheafOfDifferentials B S hS q)
      (congrArg (fun g : schemeSpace T' ⟶ Y =>
        (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) he))
    sP

/-! ### The middle factor's last square -/

/-- The inverse image along a composite of represented morphisms is the inverse image along the
represented composite, at the level of the *functor*. -/
theorem modulePullback_representedSpaceMap_comp_eq {T T' : BigFppfOver B S hS} (r : T ⟶ W)
    (ρ : T' ⟶ T) :
    modulePullback B S hS (representedSpaceMap B S hS ρ ≫ representedSpaceMap B S hS r) =
      modulePullback B S hS (representedSpaceMap B S hS (ρ ≫ r)) :=
  congrArg (modulePullback B S hS)
    (rfl : representedSpaceMap B S hS ρ ≫ representedSpaceMap B S hS r =
      representedSpaceMap B S hS (ρ ≫ r))

/-- `AlgebraicGeometry.Space.modulePullback_representedSpaceMap_comp_eq` at a morphism of
modules. -/
theorem modulePullback_map_representedSpaceMap_comp {T T' : BigFppfOver B S hS} (r : T ⟶ W)
    (ρ : T' ⟶ T) {M N : Modules.{u, u} B S hS (schemeSpace W).1 (schemeSpace W).2} (ζ : M ⟶ N)
    (hΦ : (modulePullback B S hS
              (representedSpaceMap B S hS ρ ≫ representedSpaceMap B S hS r)).obj M =
            (modulePullback B S hS (representedSpaceMap B S hS (ρ ≫ r))).obj M)
    (hΨ : (modulePullback B S hS (representedSpaceMap B S hS (ρ ≫ r))).obj N =
            (modulePullback B S hS
              (representedSpaceMap B S hS ρ ≫ representedSpaceMap B S hS r)).obj N) :
    (modulePullback B S hS
          (representedSpaceMap B S hS ρ ≫ representedSpaceMap B S hS r)).map ζ =
      (modulePullback B S hS (representedSpaceMap B S hS (ρ ≫ r))).map ζ :=
  (CategoryTheory.Functor.congr_hom_of_eq
      (modulePullback_representedSpaceMap_comp_eq B S hS r ρ) ζ hΦ hΨ).trans
    ((CategoryTheory.eqToHom_comp_of_refl hΦ _).trans
      (CategoryTheory.comp_eqToHom_of_refl hΨ _))

/-- **The pulled-back chart-square comparison's `hom`, at the spelling of the composition law.**
`AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso_hom` with the chart-square
comparison written as `AlgebraicGeometry.Space.chartSquareDifferentialsRepresentedHom`. -/
theorem chartPullbackDifferentialsAssociatedIso_hom_represented (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W) :
    (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).hom =
      (modulePullback B S hS (representedSpaceMap B S hS r)).map
          (chartSquareDifferentialsRepresentedHom B S hS q w v k hw hv hsq) ≫
        (representedAssociatedModulePullbackIso B S hS r
          (relativelyRepresentable_yoneda_map B S hS r)
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).hom :=
  (chartPullbackDifferentialsAssociatedIso_hom B S hS q w v k hw hv hsq r).trans
    (congrArg (fun z => z ≫ (representedAssociatedModulePullbackIso B S hS r
        (relativelyRepresentable_yoneda_map B S hS r)
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).hom)
      (congrArg (fun z => (modulePullback B S hS (representedSpaceMap B S hS r)).map z)
        (chartSquareDifferentialsRepresentedHom_eq B S hS q w v k hw hv hsq)).symm)

/-- `AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso_hom_represented` at a
composite `ρ ≫ r`, with the inverse image taken along the *composite of the two represented
morphisms*. -/
theorem chartPullbackDifferentialsAssociatedIso_hom_representedComp (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) :
    (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq (ρ ≫ r)).hom =
      (modulePullback B S hS
            (representedSpaceMap B S hS ρ ≫ representedSpaceMap B S hS r)).map
          (chartSquareDifferentialsRepresentedHom B S hS q w v k hw hv hsq) ≫
        (representedAssociatedModulePullbackIso B S hS (ρ ≫ r)
          (relativelyRepresentable_yoneda_map B S hS (ρ ≫ r))
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).hom :=
  (chartPullbackDifferentialsAssociatedIso_hom_represented B S hS q w v k hw hv hsq
      (ρ ≫ r)).trans
    (congrArg (fun z => z ≫ (representedAssociatedModulePullbackIso B S hS (ρ ≫ r)
        (relativelyRepresentable_yoneda_map B S hS (ρ ≫ r))
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).hom)
      (modulePullback_map_representedSpaceMap_comp B S hS r ρ
        (chartSquareDifferentialsRepresentedHom B S hS q w v k hw hv hsq) rfl rfl).symm)

/-- The inverse image along `ρ` of
`AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso`, with `ρ` read through
`AlgebraicGeometry.Space.representedSpaceMap` and the comparison expanded by
`AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso_hom_represented`. -/
theorem modulePullback_map_chartPullback (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) :
    (modulePullback B S hS (schemeSpaceMap ρ)).map
        (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).hom =
      (modulePullback B S hS (representedSpaceMap B S hS ρ)).map
        ((modulePullback B S hS (representedSpaceMap B S hS r)).map
            (chartSquareDifferentialsRepresentedHom B S hS q w v k hw hv hsq) ≫
          (representedAssociatedModulePullbackIso B S hS r
            (relativelyRepresentable_yoneda_map B S hS r)
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).hom) :=
  (modulePullback_map_schemeSpaceMap B S hS ρ
      (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).hom rfl rfl).trans
    (congrArg (fun z => (modulePullback B S hS (representedSpaceMap B S hS ρ)).map z)
      (chartPullbackDifferentialsAssociatedIso_hom_represented B S hS q w v k hw hv hsq r))

/-- The transport `AlgebraicGeometry.Scheme.Modules.pullbackCongr` along the factorization of
`ρ ≫ r` is the identity. -/
theorem pullbackComp_comp_pullbackCongr (k : W ⟶ V) {T T' : BigFppfOver B S hS} (r : T ⟶ W)
    (ρ : T' ⟶ T)
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map (ρ ≫ r)) :
    (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
            ((BigFppfOver.toScheme B S hS).map r)).hom.app
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫
        (Scheme.Modules.pullbackCongr hrr).hom.app
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
            ((BigFppfOver.toScheme B S hS).map r)).hom.app
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) :=
  (congrArg (fun z => (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
          ((BigFppfOver.toScheme B S hS).map r)).hom.app
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫ z)
      (rfl : (Scheme.Modules.pullbackCongr hrr).hom.app
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) = 𝟙 _)).trans
    (Category.comp_id _)

/-- The associated module of `AlgebraicGeometry.Space.pullbackComp_comp_pullbackCongr`. -/
theorem representedAssociatedModule_map_pullbackComp_pullbackCongr (k : W ⟶ V)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T)
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map (ρ ≫ r))
    (hT' : IsAlgebraicSpace B S hS (yoneda.obj T')) :
    (representedAssociatedModule B S hS T' hT').map
          ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                ((BigFppfOver.toScheme B S hS).map r)).hom.app
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫
            (Scheme.Modules.pullbackCongr hrr).hom.app
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) =
      (representedAssociatedModule B S hS T' hT').map
        ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
              ((BigFppfOver.toScheme B S hS).map r)).hom.app
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) :=
  congrArg (fun z => (representedAssociatedModule B S hS T' hT').map z)
    (pullbackComp_comp_pullbackCongr B S hS k r ρ hrr)

/-- The transport of [Stacks Project, Tag 03LU] at the two spellings of the pulled-back Zariski
differentials. -/
theorem representedAssociatedModulePullbackIso_hom_inclusion (k : W ⟶ V)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) :
    (representedAssociatedModulePullbackIso B S hS ρ
          (relativelyRepresentable_yoneda_map B S hS ρ)
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)))).hom =
      (representedAssociatedModulePullbackIso B S hS ρ
          (relativelyRepresentable_yoneda_map B S hS ρ)
          ((Scheme.Modules.pullback (B.inclusion.map r.left)).obj
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k) :
              ((BigFppfOver.toScheme B S hS).obj W).Modules))).hom :=
  rfl

/-- The associated module of [Stacks Project, Tag 03LU]'s composition comparison at the two
spellings — the chain's `AlgebraicGeometry.Space.representedAssociatedModule` and
`AlgebraicGeometry.BigFppfOver.toScheme` against the law's
`AlgebraicGeometry.SmallEtale.associatedModule` with the comparison equivalence and
`B.inclusion.map ·.left`. -/
theorem representedAssociatedModule_map_pullbackComp_inclusion (k : W ⟶ V)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) :
    (representedAssociatedModule B S hS T' (schemeSpace T').2).map
          ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                ((BigFppfOver.toScheme B S hS).map r)).hom.app
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) =
      (representedSmallEtaleModuleEquivalence B S hS T').functor.map
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
          ((Scheme.Modules.pullbackComp (B.inclusion.map ρ.left)
              (B.inclusion.map r.left)).hom.app
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k) :
              ((BigFppfOver.toScheme B S hS).obj W).Modules))) :=
  rfl

/-- The transport of [Stacks Project, Tag 03LU] at the pulled-back Zariski differentials,
followed by the associated module of the composition comparison of pullbacks, is the same at the
two spellings of `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_hom_inclusion`
and `AlgebraicGeometry.Space.representedAssociatedModule_map_pullbackComp_inclusion`. -/
theorem representedAssociatedModulePullbackIso_comp_vertical (k : W ⟶ V)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) :
    (representedAssociatedModulePullbackIso B S hS ρ
            (relativelyRepresentable_yoneda_map B S hS ρ)
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
              (Scheme.Hom.relativeDifferentials
                ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
        (representedAssociatedModule B S hS T' (schemeSpace T').2).map
          ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                ((BigFppfOver.toScheme B S hS).map r)).hom.app
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) =
      (representedAssociatedModulePullbackIso B S hS ρ
            (relativelyRepresentable_yoneda_map B S hS ρ)
            ((Scheme.Modules.pullback (B.inclusion.map r.left)).obj
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k) :
                ((BigFppfOver.toScheme B S hS).obj W).Modules))).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            ((Scheme.Modules.pullbackComp (B.inclusion.map ρ.left)
                (B.inclusion.map r.left)).hom.app
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k) :
                ((BigFppfOver.toScheme B S hS).obj W).Modules))) :=
  (CategoryTheory.eq_whisker
      (representedAssociatedModulePullbackIso_hom_inclusion B S hS k r ρ) _).trans
    (CategoryTheory.whisker_eq _
      (representedAssociatedModule_map_pullbackComp_inclusion B S hS k r ρ))

/-- **[Stacks Project, Tag 03LU]'s composition law at
`AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso`**: the square that
`AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso_hom_square` takes as its
hypothesis `sP`. -/
theorem representedAssociatedModulePullbackIso_comp_chartPullback (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) (r' : T' ⟶ W) (hr : ρ ≫ r = r')
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map r')
    (ht : schemeSpaceMap ρ ≫ schemeSpaceMap r = schemeSpaceMap r') :
    (modulePullback B S hS (schemeSpaceMap ρ)).map
          (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).hom ≫
        ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Scheme.Hom.relativeDifferentials
                    ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS T' (schemeSpace T').2).map
            ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                  ((BigFppfOver.toScheme B S hS).map r)).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫
              (Scheme.Modules.pullbackCongr hrr).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)))) =
      ((modulePullbackCompIso B S hS (schemeSpaceMap ρ) (schemeSpaceMap r)).hom.app
            ((modulePullback B S hS w).obj (sheafOfDifferentials B S hS q)) ≫
          eqToHom (congrArg (fun g : schemeSpace T' ⟶ schemeSpace W =>
            (modulePullback B S hS w ⋙ modulePullback B S hS g).obj
              (sheafOfDifferentials B S hS q)) ht)) ≫
        (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r').hom := by
  subst hr
  refine (CategoryTheory.whisker_eq _ (CategoryTheory.whisker_eq _
    (representedAssociatedModule_map_pullbackComp_pullbackCongr B S hS k r ρ hrr
      (schemeSpace T').2))).trans ?_
  refine (CategoryTheory.eq_whisker
    (modulePullback_map_chartPullback B S hS q w v k hw hv hsq r ρ) _).trans ?_
  refine (CategoryTheory.whisker_eq _
    (representedAssociatedModulePullbackIso_comp_vertical B S hS k r ρ)).trans ?_
  refine (representedAssociatedModulePullbackIso_comp_chartSquare B S hS q w v k hw hv hsq
    r ρ).trans ?_
  refine (CategoryTheory.whisker_eq _
    (chartPullbackDifferentialsAssociatedIso_hom_representedComp B S hS q w v k hw hv hsq
      r ρ).symm).trans ?_
  refine (CategoryTheory.eq_whisker
    (modulePullbackCompIso_hom_app_representedSpaceMap₂ B S hS ρ r
      ((modulePullback B S hS w).obj (sheafOfDifferentials B S hS q))).symm _).trans ?_
  exact CategoryTheory.eq_whisker
    (CategoryTheory.comp_eqToHom_of_refl
      (congrArg (fun g : schemeSpace T' ⟶ schemeSpace W =>
          (modulePullback B S hS w ⋙ modulePullback B S hS g).obj
            (sheafOfDifferentials B S hS q)) ht)
      ((modulePullbackCompIso B S hS (schemeSpaceMap ρ) (schemeSpaceMap r)).hom.app
        ((modulePullback B S hS w).obj (sheafOfDifferentials B S hS q)))).symm
    (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq (ρ ≫ r)).hom

/-- **The square of `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso` in a
morphism `ρ` of the site, unconditionally.**
`AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso_hom_square` with its last
factor's square discharged by
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_chartPullback`. -/
theorem chartCompositeDifferentialsAssociatedIso_hom_square_of_factorization (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) (r' : T' ⟶ W) (hr : ρ ≫ r = r')
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map r')
    (c : schemeSpace T ⟶ Y) (hc : c = schemeSpaceMap r ≫ w)
    (c' : schemeSpace T' ⟶ Y) (hc' : c' = schemeSpaceMap r' ≫ w)
    (hd : schemeSpaceMap ρ ≫ c = c')
    (ht : schemeSpaceMap ρ ≫ schemeSpaceMap r = schemeSpaceMap r')
    (he : schemeSpaceMap ρ ≫ schemeSpaceMap r ≫ w = schemeSpaceMap r' ≫ w) :
    (modulePullback B S hS (schemeSpaceMap ρ)).map
          (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r c hc).hom ≫
        ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Scheme.Hom.relativeDifferentials
                    ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS T' (schemeSpace T').2).map
            ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                  ((BigFppfOver.toScheme B S hS).map r)).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫
              (Scheme.Modules.pullbackCongr hrr).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)))) =
      ((modulePullbackCompIso B S hS (schemeSpaceMap ρ) c).hom.app
            (sheafOfDifferentials B S hS q) ≫
          eqToHom (congrArg (fun g : schemeSpace T' ⟶ Y =>
            (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hd)) ≫
        (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r' c' hc').hom :=
  chartCompositeDifferentialsAssociatedIso_hom_square B S hS q w v k hw hv hsq r ρ r' c hc c' hc'
    hd ht he
    (representedAssociatedModulePullbackIso_comp_chartPullback B S hS q w v k hw hv hsq r ρ r'
      hr hrr ht)

/-! ### The square of the Zariski change of the inner sheaf -/

/-- `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_naturality` at the spelling
of `AlgebraicGeometry.Space.representedAssociatedModule`, and with the underlying morphism of
schemes written as `AlgebraicGeometry.BigFppfOver.toScheme` of `g` rather than as
`B.inclusion.map g.left`. -/
theorem representedAssociatedModule_map_square {T T' : BigFppfOver B S hS} (ρ : T' ⟶ T)
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
    (hT' : IsAlgebraicSpace B S hS (yoneda.obj T'))
    {M N : ((BigFppfOver.toScheme B S hS).obj T).Modules} (β : M ⟶ N) :
    (modulePullback B S hS (representedSpaceMap B S hS ρ)).map
          ((representedAssociatedModule B S hS T hT).map β) ≫
        (representedAssociatedModulePullbackIso B S hS ρ
          (relativelyRepresentable_yoneda_map B S hS ρ) N).hom =
      (representedAssociatedModulePullbackIso B S hS ρ
          (relativelyRepresentable_yoneda_map B S hS ρ) M).hom ≫
        (representedAssociatedModule B S hS T' hT').map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ρ)).map β) :=
  representedAssociatedModulePullbackIso_naturality B S hS ρ
    (relativelyRepresentable_yoneda_map B S hS ρ) β

/-- **The associated module of the Zariski square of the change of the inner sheaf.** The square
`AlgebraicGeometry.Space.pullbackCotangentCompHom_cotangentSheafIso` of Zariski modules, carried
through `AlgebraicGeometry.Space.representedAssociatedModule` by
`CategoryTheory.Functor.map_comp` on each side. -/
theorem representedAssociatedModule_map_pullbackCotangentCompHom (k : W ⟶ V)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) (r' : T' ⟶ W)
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map r')
    (hT' : IsAlgebraicSpace B S hS (yoneda.obj T')) :
    (representedAssociatedModule B S hS T' hT').map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ρ)).map
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
              (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom)) ≫
        (representedAssociatedModule B S hS T' hT').map
          (Stacks.Smooth.pullbackCotangentCompHom ((BigFppfOver.toScheme B S hS).map k)
            ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map ρ)
            ((BigFppfOver.toScheme B S hS).map r') hrr) =
      (representedAssociatedModule B S hS T' hT').map
          ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                ((BigFppfOver.toScheme B S hS).map r)).hom.app
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫
            (Scheme.Modules.pullbackCongr hrr).hom.app
              (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) ≫
        (representedAssociatedModule B S hS T' hT').map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r')).map
            (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom) :=
  (((representedAssociatedModule B S hS T' hT').map_comp _ _).symm.trans
      (congrArg (fun z => (representedAssociatedModule B S hS T' hT').map z)
        ((pullbackCotangentCompHom_cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)
            ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map ρ)
            ((BigFppfOver.toScheme B S hS).map r') hrr).trans
          (Category.assoc _ _ _).symm))).trans
    ((representedAssociatedModule B S hS T' hT').map_comp _ _)

/-- **The square of the chain's last factor in a morphism `ρ` of the site.** The inverse image
along `ρ` of the associated module of `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso` pulled
back along `r`, followed by the transport of [Stacks Project, Tag 03LU] at the pullback cotangent
sheaf and the associated module of `Stacks.Smooth.pullbackCotangentCompHom`, is the transport at
the pullback of the relative differentials followed by the associated module of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and of the transport along the factorization, and
then the same change of the inner sheaf along `r'`. -/
theorem representedAssociatedModule_cotangentSheafIso_square (k : W ⟶ V)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) (r' : T' ⟶ W)
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map r')
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
    (hT' : IsAlgebraicSpace B S hS (yoneda.obj T')) :
    (modulePullback B S hS (representedSpaceMap B S hS ρ)).map
          ((representedAssociatedModule B S hS T hT).map
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
              (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom)) ≫
        ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Stacks.Smooth.cotangentSheaf
                    ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS T' hT').map
            (Stacks.Smooth.pullbackCotangentCompHom ((BigFppfOver.toScheme B S hS).map k)
              ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map ρ)
              ((BigFppfOver.toScheme B S hS).map r') hrr)) =
      ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Scheme.Hom.relativeDifferentials
                    ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS T' hT').map
            ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                  ((BigFppfOver.toScheme B S hS).map r)).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫
              (Scheme.Modules.pullbackCongr hrr).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)))) ≫
        (representedAssociatedModule B S hS T' hT').map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r')).map
            (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom) :=
  CategoryTheory.square_comp
    (representedAssociatedModule_map_square B S hS ρ hT hT'
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
        (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom))
    (representedAssociatedModule_map_pullbackCotangentCompHom B S hS k r ρ r' hrr hT')

/-- `AlgebraicGeometry.Space.representedAssociatedModule_cotangentSheafIso_square` with the
inverse image taken along `AlgebraicGeometry.Space.schemeSpaceMap`. -/
theorem representedAssociatedModule_cotangentSheafIso_square_schemeSpaceMap (k : W ⟶ V)
    {T T' : BigFppfOver B S hS} (r : T ⟶ W) (ρ : T' ⟶ T) (r' : T' ⟶ W)
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map r')
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
    (hT' : IsAlgebraicSpace B S hS (yoneda.obj T')) :
    (modulePullback B S hS (schemeSpaceMap ρ)).map
          ((representedAssociatedModule B S hS T hT).map
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
              (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom)) ≫
        ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Stacks.Smooth.cotangentSheaf
                    ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS T' hT').map
            (Stacks.Smooth.pullbackCotangentCompHom ((BigFppfOver.toScheme B S hS).map k)
              ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map ρ)
              ((BigFppfOver.toScheme B S hS).map r') hrr)) =
      ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Scheme.Hom.relativeDifferentials
                    ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS T' hT').map
            ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                  ((BigFppfOver.toScheme B S hS).map r)).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫
              (Scheme.Modules.pullbackCongr hrr).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)))) ≫
        (representedAssociatedModule B S hS T' hT').map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r')).map
            (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom) :=
  (CategoryTheory.eq_whisker
      (modulePullback_map_schemeSpaceMap B S hS ρ
        ((representedAssociatedModule B S hS T hT).map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
            (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom))
        rfl rfl) _).trans
    (representedAssociatedModule_cotangentSheafIso_square B S hS k r ρ r' hrr hT hT')

/-- `AlgebraicGeometry.Space.representedAssociatedModule_cotangentSheafIso_square_schemeSpaceMap`
at the chart data, with the inverse image's two objects read at
`AlgebraicGeometry.Space.chartSpace`. -/
theorem representedAssociatedModule_cotangentSheafIso_square_chart (k : W ⟶ V)
    (A A' : SmallEtale B S hS Z.1)
    (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (r' : (SmallEtale.toOver B S hS Z.1).obj A' ⟶ W)
    (ρ : (SmallEtale.toOver B S hS Z.1).obj A' ⟶ (SmallEtale.toOver B S hS Z.1).obj A)
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map r') :
    (modulePullback B S hS
          (schemeSpaceMap ρ : chartSpace B S hS Z A' ⟶ chartSpace B S hS Z A)).map
          ((representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A)
            (chartSpace B S hS Z A).2).map
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
              (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom)) ≫
        ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Stacks.Smooth.cotangentSheaf
                    ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A')
            (chartSpace B S hS Z A').2).map
            (Stacks.Smooth.pullbackCotangentCompHom ((BigFppfOver.toScheme B S hS).map k)
              ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map ρ)
              ((BigFppfOver.toScheme B S hS).map r') hrr)) =
      ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Scheme.Hom.relativeDifferentials
                    ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A')
            (chartSpace B S hS Z A').2).map
            ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map ρ)
                  ((BigFppfOver.toScheme B S hS).map r)).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) ≫
              (Scheme.Modules.pullbackCongr hrr).hom.app
                (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)))) ≫
        (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A')
            (chartSpace B S hS Z A').2).map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r')).map
            (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom) :=
  representedAssociatedModule_cotangentSheafIso_square_schemeSpaceMap B S hS k r ρ r' hrr
    (chartSpace B S hS Z A).2 (chartSpace B S hS Z A').2

/-! ### The chart-level source square -/

/-- **The source comparison of a chart presentation, factored, and read at the represented chart
space.** `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_eq` with the inverse
image of the first factor taken along `AlgebraicGeometry.Space.chartToSpace` read as a morphism
*out of* `AlgebraicGeometry.Space.schemeSpace` of the chart's object of the site. -/
theorem chartDifferentialsAssociatedCotangentIso_eq_represented (q : Y ⟶ Bb) (a : Z ⟶ Y)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    (A : SmallEtale B S hS Z.1) (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (hc : chartToSpace B S hS Z A ≫ a = schemeSpaceMap r ≫ w) :
    (modulePullbackCompIso B S hS
            (X := schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A))
            (chartToSpace B S hS Z A) a).app (sheafOfDifferentials B S hS q) ≪≫
        chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r
          (chartToSpace B S hS Z A ≫ a) hc ≪≫
        (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A)
          (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).property).mapIso
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).mapIso
              (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k))) =
      chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A r hc :=
  (chartDifferentialsAssociatedCotangentIso_eq B S hS q a w v k hw hv hsq A r hc).symm

/-- **The chain equation of the source comparison, at the represented chart space.**
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_eq_represented` on `hom`. -/
theorem chartDifferentialsAssociatedCotangentIso_hom_represented (q : Y ⟶ Bb) (a : Z ⟶ Y)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    (A : SmallEtale B S hS Z.1) (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (hc : chartToSpace B S hS Z A ≫ a = schemeSpaceMap r ≫ w) :
    ((modulePullbackCompIso B S hS
              (X := schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A))
              (chartToSpace B S hS Z A) a).app (sheafOfDifferentials B S hS q)).hom ≫
        (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r
            (chartToSpace B S hS Z A ≫ a) hc).hom ≫
          (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A)
              (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).property).map
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
              (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom) =
      (chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A r hc).hom :=
  congrArg Iso.hom
    (chartDifferentialsAssociatedCotangentIso_eq_represented B S hS q a w v k hw hv hsq A r hc)

/-- **The source comparison of a chart presentation is natural in the chart of the source.** For
a chart square `w ≫ q = k ≫ v` of étale charts of `q`, two étale scheme charts `A` and `A'` of the
source with morphisms `r` and `r'` of the site through which their composites to `Y` factor, and a
morphism `ρ` of the site from the smaller chart to the larger one with `ρ ≫ r = r'`, the inverse
image along `ρ` of `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso` at `A`,
followed by the Zariski comparison of the two pullback cotangent sheaves, is the comparison of
[Stacks Project, Tag 03LU] at the chart followed by the comparison at `A'`. -/
theorem chartDifferentialsAssociatedCotangentIso_hom_square (q : Y ⟶ Bb) (a : Z ⟶ Y)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    (A A' : SmallEtale B S hS Z.1)
    (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (r' : (SmallEtale.toOver B S hS Z.1).obj A' ⟶ W)
    (ρ : (SmallEtale.toOver B S hS Z.1).obj A' ⟶ (SmallEtale.toOver B S hS Z.1).obj A)
    (hr : ρ ≫ r = r')
    (hrr : (BigFppfOver.toScheme B S hS).map ρ ≫ (BigFppfOver.toScheme B S hS).map r =
      (BigFppfOver.toScheme B S hS).map r')
    (hc : chartToSpace B S hS Z A ≫ a = schemeSpaceMap r ≫ w)
    (hc' : chartToSpace B S hS Z A' ≫ a = schemeSpaceMap r' ≫ w)
    (hκ : schemeSpaceMap ρ ≫
        (chartToSpace B S hS Z A :
          schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z) =
      (chartToSpace B S hS Z A' :
        schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A') ⟶ Z))
    (hd : schemeSpaceMap ρ ≫
        (chartToSpace B S hS Z A :
          schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z) ≫ a =
      (chartToSpace B S hS Z A' :
        schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A') ⟶ Z) ≫ a)
    (ht : schemeSpaceMap ρ ≫ schemeSpaceMap r = schemeSpaceMap r')
    (he : schemeSpaceMap ρ ≫ schemeSpaceMap r ≫ w = schemeSpaceMap r' ≫ w) :
    (modulePullback B S hS (schemeSpaceMap ρ)).map
          (chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A r hc).hom ≫
        ((representedAssociatedModulePullbackIso B S hS ρ
                (relativelyRepresentable_yoneda_map B S hS ρ)
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Stacks.Smooth.cotangentSheaf ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A')
              (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A')).property).map
            (Stacks.Smooth.pullbackCotangentCompHom ((BigFppfOver.toScheme B S hS).map k)
              ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map ρ)
              ((BigFppfOver.toScheme B S hS).map r') hrr)) =
      ((modulePullbackCompIso B S hS (schemeSpaceMap ρ)
              (chartToSpace B S hS Z A :
                schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z)).hom.app
            ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS q)) ≫
          eqToHom (congrArg
            (fun g : schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A') ⟶ Z =>
              (modulePullback B S hS a ⋙ modulePullback B S hS g).obj
                (sheafOfDifferentials B S hS q)) hκ)) ≫
        (chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A' r' hc').hom := by
  refine CategoryTheory.square_of_functor_factorizations_of_paste
    (modulePullback B S hS (schemeSpaceMap ρ)) ?_ ?_
    (CategoryTheory.square_comp'
      (modulePullbackCompIso_app_hom_square B S hS (schemeSpaceMap ρ)
        (chartToSpace B S hS Z A :
          schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z)
        (chartToSpace B S hS Z A' :
          schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A') ⟶ Z)
        hκ a hd (sheafOfDifferentials B S hS q)).symm
      (CategoryTheory.square_comp'
        (chartCompositeDifferentialsAssociatedIso_hom_square_of_factorization B S hS q w v k
          hw hv hsq r ρ r' hr hrr
          ((chartToSpace B S hS Z A :
            schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z) ≫ a) hc
          ((chartToSpace B S hS Z A' :
            schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A') ⟶ Z) ≫ a) hc' hd ht he).symm
        (representedAssociatedModule_cotangentSheafIso_square_schemeSpaceMap B S hS k r ρ r' hrr
          (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).property
          (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A')).property).symm))
  · exact (chartDifferentialsAssociatedCotangentIso_hom_represented B S hS q a w v k hw hv hsq
      A r hc).symm
  · exact (chartDifferentialsAssociatedCotangentIso_hom_represented B S hS q a w v k hw hv hsq
      A' r' hc').symm

/-- **The chart-level source square at a morphism of étale scheme charts of the source.**
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom_square` at
`ρ = (AlgebraicGeometry.SmallEtale.toOver … ).map f`, for a morphism `f : A' ⟶ A` of étale charts
and morphisms `r`, `r'` of the site with `ρ ≫ r = r'`. -/
theorem chartDifferentialsAssociatedCotangentIso_hom_square_of_chartMap (q : Y ⟶ Bb) (a : Z ⟶ Y)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    (A A' : SmallEtale B S hS Z.1) (f : A' ⟶ A)
    (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (r' : (SmallEtale.toOver B S hS Z.1).obj A' ⟶ W)
    (hr : (SmallEtale.toOver B S hS Z.1).map f ≫ r = r')
    (hc : chartToSpace B S hS Z A ≫ a = schemeSpaceMap r ≫ w)
    (hc' : chartToSpace B S hS Z A' ≫ a = schemeSpaceMap r' ≫ w) :
    (modulePullback B S hS (schemeSpaceMap ((SmallEtale.toOver B S hS Z.1).map f))).map
          (chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A r hc).hom ≫
        ((representedAssociatedModulePullbackIso B S hS
                ((SmallEtale.toOver B S hS Z.1).map f)
                (relativelyRepresentable_yoneda_map B S hS
                  ((SmallEtale.toOver B S hS Z.1).map f))
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
                  (Stacks.Smooth.cotangentSheaf ((BigFppfOver.toScheme B S hS).map k)))).hom ≫
          (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A')
              (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A')).property).map
            (Stacks.Smooth.pullbackCotangentCompHom ((BigFppfOver.toScheme B S hS).map k)
              ((BigFppfOver.toScheme B S hS).map r)
              ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Z.1).map f))
              ((BigFppfOver.toScheme B S hS).map r')
              ((((BigFppfOver.toScheme B S hS).map_comp
                    ((SmallEtale.toOver B S hS Z.1).map f) r).symm).trans
                (congrArg (BigFppfOver.toScheme B S hS).map hr)))) =
      ((modulePullbackCompIso B S hS
              (schemeSpaceMap ((SmallEtale.toOver B S hS Z.1).map f))
              (chartToSpace B S hS Z A :
                schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z)).hom.app
            ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS q)) ≫
          eqToHom (congrArg
            (fun g : schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A') ⟶ Z =>
              (modulePullback B S hS a ⋙ modulePullback B S hS g).obj
                (sheafOfDifferentials B S hS q))
            (schemeSpaceMap_toOver_comp_chartToSpace B S hS Z f))) ≫
        (chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A' r' hc').hom := by
  have hρ := schemeSpaceMap_toOver_comp_chartToSpace B S hS Z f
  have ht : schemeSpaceMap ((SmallEtale.toOver B S hS Z.1).map f) ≫ schemeSpaceMap r =
      schemeSpaceMap r' := (rfl : schemeSpaceMap ((SmallEtale.toOver B S hS Z.1).map f) ≫
        schemeSpaceMap r = schemeSpaceMap ((SmallEtale.toOver B S hS Z.1).map f ≫ r)).trans
    (congrArg schemeSpaceMap hr)
  exact chartDifferentialsAssociatedCotangentIso_hom_square B S hS q a w v k hw hv hsq A A' r r'
    ((SmallEtale.toOver B S hS Z.1).map f) hr
    ((((BigFppfOver.toScheme B S hS).map_comp ((SmallEtale.toOver B S hS Z.1).map f) r).symm).trans
      (congrArg (BigFppfOver.toScheme B S hS).map hr))
    hc hc' hρ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ a) hρ)) ht
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ w) ht))

end AlgebraicGeometry.Space

end
