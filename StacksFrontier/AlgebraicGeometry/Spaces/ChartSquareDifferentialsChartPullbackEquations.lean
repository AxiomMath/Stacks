module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullback

/-!
# The chart-square source comparison is its defining composite, factor by factor

`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso` exhibits the inverse image of
`a^*Ω_{Y/Bb}` to the small étale site of an étale chart space as the associated module of the
Zariski cotangent sheaf of the chart square.  It is a five-factor composite, built up through
three intermediate isomorphisms, and the next step over it — that it carries the small étale
universal differential `d_{Y/Bb}` to the Zariski `Stacks.Smooth.pullbackD` — has to take each
factor's own derivation compatibility and compose them.

This file supplies the equations that make that composition affordable: each of the four
isomorphisms of the chain *is* its defining composite, stated **between the isomorphisms** and
never at a component.

## Why these are wanted

The measurement is recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalizationDerivation`, where the
same three lemmas took the derivation compatibility of [Stacks Project, Tag 04CU] from a kernel
timeout to about two seconds.  Assembling a composite of this shape in one declaration exhausts
the 200 000-heartbeat *kernel* budget while the elaborator succeeds: the cost is neither the
statement nor the definitional unfolding of the composite — each of those is cheap on its own —
but **projecting `hom` and `inv` out of isomorphisms built as structure literals**, whose
`CategoryTheory.Iso.hom_inv_id` and `CategoryTheory.Iso.inv_hom_id` fields are large derivation
computations that `whnf` drags in at every projection.

Rewriting with an equation of isomorphisms and then with `CategoryTheory.Iso.trans_hom` reaches
the same composite of components without ever unfolding a `def` underneath a projection, so each
factor's named `hom` or `inv` — such as
`AlgebraicGeometry.Scheme.Hom.cotangentSheafIso_hom` or
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_hom` — is what the projection
meets instead of a structure literal.

## Main results

* `AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso_eq`: [Stacks Project, Tag 04CU]
  followed by [Stacks Project, Tag 04CS].
* `AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso_eq`: the previous one pulled
  back, followed by `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`.
* `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso_eq`: the previous one behind
  the transport of the factorization and [Stacks Project, Tag 03LU].
* `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_eq`: the previous one between
  [Stacks Project, Tag 03LU] and the change of the inner sheaf by
  `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`.

Each is `rfl`.  No `@[stacks]` attribute is claimed: these are equation lemmas for
isomorphisms registered where they are built.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
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

/-- **The chart-square comparison is [Stacks Project, Tag 04CU] followed by the named form of
[Stacks Project, Tag 04CS].**  Stated between the isomorphisms, so that a projection of either
side meets the two factors' named components and not a structure literal. -/
theorem chartSquareDifferentialsAssociatedIso_eq (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) :
    chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq =
      sheafOfDifferentialsEtaleLocalizationIso B S hS q w (schemeSpaceMap k) v hw hv hsq ≪≫
        representedAssociatedDifferentialsIso B S hS k :=
  rfl

/-- **The chart-square comparison pulled back along a further morphism of the site is the inverse
image of `AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso` followed by
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`.** -/
theorem chartPullbackDifferentialsAssociatedIso_eq (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W) :
    chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r =
      (modulePullback B S hS (representedSpaceMap B S hS r)).mapIso
          (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq) ≪≫
        representedAssociatedModulePullbackIso B S hS r
          (relativelyRepresentable_yoneda_map B S hS r)
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) :=
  rfl

/-- **The comparison at a morphism which factors through the chart square is the transport of the
factorization, the inverse of [Stacks Project, Tag 03LU], and
`AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso`.** -/
theorem chartCompositeDifferentialsAssociatedIso_eq (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W)
    (c : schemeSpace T ⟶ Y) (hc : c = schemeSpaceMap r ≫ w) :
    chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r c hc =
      eqToIso (congrArg
          (fun g : schemeSpace T ⟶ Y =>
            (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hc) ≪≫
        ((modulePullbackCompIso B S hS (schemeSpaceMap r) w).app
          (sheafOfDifferentials B S hS q)).symm ≪≫
        chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r :=
  rfl

/-- **The source comparison of a chart presentation is [Stacks Project, Tag 03LU], the comparison
at the factoring composite, and the change of the inner sheaf by
`AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`.** -/
theorem chartDifferentialsAssociatedCotangentIso_eq (q : Y ⟶ Bb) (a : Z ⟶ Y)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    (A : SmallEtale B S hS Z.1) (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (hc : chartToSpace B S hS Z A ≫ a = schemeSpaceMap r ≫ w) :
    chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A r hc =
      (modulePullbackCompIso B S hS
            (chartToSpace B S hS Z A :
              schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z) a).app
          (sheafOfDifferentials B S hS q) ≪≫
        chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r
          (chartToSpace B S hS Z A ≫ a) hc ≪≫
        (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A)
          (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).property).mapIso
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).mapIso
              (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k))) :=
  rfl

/-! ### The projections

Each composite's `hom` and `inv`, obtained from the equation of isomorphisms above — which is
where they are cheap, exactly as
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_hom` is obtained from its own.
Note that `inv` of a right-nested `CategoryTheory.Iso.trans` is left-nested. -/

/-- The chart-square comparison on `hom`. -/
theorem chartSquareDifferentialsAssociatedIso_hom (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) :
    (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq).hom =
      (sheafOfDifferentialsEtaleLocalizationIso B S hS q w (schemeSpaceMap k) v hw hv
            hsq).hom ≫
        (representedAssociatedDifferentialsIso B S hS k).hom :=
  congrArg Iso.hom (chartSquareDifferentialsAssociatedIso_eq B S hS q w v k hw hv hsq)

/-- The chart-square comparison on `inv`. -/
theorem chartSquareDifferentialsAssociatedIso_inv (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) :
    (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq).inv =
      (representedAssociatedDifferentialsIso B S hS k).inv ≫
        (sheafOfDifferentialsEtaleLocalizationIso B S hS q w (schemeSpaceMap k) v hw hv hsq).inv :=
  congrArg Iso.inv (chartSquareDifferentialsAssociatedIso_eq B S hS q w v k hw hv hsq)

/-- The pulled-back chart-square comparison on `hom`. -/
theorem chartPullbackDifferentialsAssociatedIso_hom (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W) :
    (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).hom =
      (modulePullback B S hS (representedSpaceMap B S hS r)).map
          (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq).hom ≫
        (representedAssociatedModulePullbackIso B S hS r
          (relativelyRepresentable_yoneda_map B S hS r)
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).hom :=
  congrArg Iso.hom (chartPullbackDifferentialsAssociatedIso_eq B S hS q w v k hw hv hsq r)

/-- The pulled-back chart-square comparison on `inv`. -/
theorem chartPullbackDifferentialsAssociatedIso_inv (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W) :
    (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).inv =
      (representedAssociatedModulePullbackIso B S hS r
            (relativelyRepresentable_yoneda_map B S hS r)
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))).inv ≫
        ((modulePullback B S hS (representedSpaceMap B S hS r)).mapIso
          (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq)).inv :=
  (congrArg Iso.inv
    (chartPullbackDifferentialsAssociatedIso_eq B S hS q w v k hw hv hsq r)).trans
      (Iso.trans_inv _ _)

/-- The comparison at a factoring morphism on `hom`. -/
theorem chartCompositeDifferentialsAssociatedIso_hom (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W)
    (c : schemeSpace T ⟶ Y) (hc : c = schemeSpaceMap r ≫ w) :
    (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r c hc).hom =
      (eqToIso (congrArg
            (fun g : schemeSpace T ⟶ Y =>
              (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hc)).hom ≫
        (((modulePullbackCompIso B S hS (schemeSpaceMap r) w).app
              (sheafOfDifferentials B S hS q)).symm.hom ≫
          (chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).hom) :=
  (congrArg Iso.hom
    (chartCompositeDifferentialsAssociatedIso_eq B S hS q w v k hw hv hsq r c hc)).trans
      (Iso.trans_hom _ _)

/-- The comparison at a factoring morphism on `inv`. -/
theorem chartCompositeDifferentialsAssociatedIso_inv (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W)
    (c : schemeSpace T ⟶ Y) (hc : c = schemeSpaceMap r ≫ w) :
    (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r c hc).inv =
      ((chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r).inv ≫
          ((modulePullbackCompIso B S hS (schemeSpaceMap r) w).app
            (sheafOfDifferentials B S hS q)).symm.inv) ≫
        (eqToIso (congrArg
          (fun g : schemeSpace T ⟶ Y =>
            (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hc)).inv :=
  (congrArg Iso.inv
    (chartCompositeDifferentialsAssociatedIso_eq B S hS q w v k hw hv hsq r c hc)).trans
      (Iso.trans_inv _ _)

/-- The source comparison of a chart presentation on `hom`. -/
theorem chartDifferentialsAssociatedCotangentIso_hom (q : Y ⟶ Bb) (a : Z ⟶ Y)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    (A : SmallEtale B S hS Z.1) (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (hc : chartToSpace B S hS Z A ≫ a = schemeSpaceMap r ≫ w) :
    (chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A r hc).hom =
      ((modulePullbackCompIso B S hS
            (chartToSpace B S hS Z A :
              schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z) a).app
          (sheafOfDifferentials B S hS q)).hom ≫
        (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r
            (chartToSpace B S hS Z A ≫ a) hc).hom ≫
          (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A)
            (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).property).map
              ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
                (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).hom) :=
  congrArg Iso.hom
    (chartDifferentialsAssociatedCotangentIso_eq B S hS q a w v k hw hv hsq A r hc)

/-- The source comparison of a chart presentation on `inv`. -/
theorem chartDifferentialsAssociatedCotangentIso_inv (q : Y ⟶ Bb) (a : Z ⟶ Y)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    (A : SmallEtale B S hS Z.1) (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (hc : chartToSpace B S hS Z A ≫ a = schemeSpaceMap r ≫ w) :
    (chartDifferentialsAssociatedCotangentIso B S hS q a w v k hw hv hsq A r hc).inv =
      ((representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A)
            (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).property).map
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).map
              (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)).inv) ≫
          (chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r
            (chartToSpace B S hS Z A ≫ a) hc).inv) ≫
        ((modulePullbackCompIso B S hS
            (chartToSpace B S hS Z A :
              schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z) a).app
          (sheafOfDifferentials B S hS q)).inv :=
  congrArg Iso.inv
    (chartDifferentialsAssociatedCotangentIso_eq B S hS q a w v k hw hv hsq A r hc)

end AlgebraicGeometry.Space

end
