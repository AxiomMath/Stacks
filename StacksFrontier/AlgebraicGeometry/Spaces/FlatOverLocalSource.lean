module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Flatness of a module over its own algebraic space is étale local on the source

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `F` be a
quasi-coherent `𝒪_X`-module.  Stacks 05VV says what it means for `F` to be flat over an
algebraic space it maps to; read at the identity of `X` that is flatness of `F` over `X`
itself.  This file proves that **that condition may be checked after pulling back along an
étale family covering `|X|`**: if `φ_i : U_i ⟶ X` is a family of étale morphisms whose images
exhaust the points of `X` and each `φ_i^* F` is flat over `U_i`, then `F` is flat over `X`.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_id_of_isEtale_cover`: **flatness of a quasi-coherent
  module over its own space descends along an étale family surjective on points.**
* `AlgebraicGeometry.Space.isFlatOver_id_of_etale_cover_of_representable`: the same for a
  jointly surjective family of étale subobjects of a *representing object* of the site, with
  the covering hypothesis read on the points of the representing schemes — the form the
  flatness clause of Stacks 0CZA consumes.

## Implementation notes

Both directions of the argument are pointwise on geometric points, through the geometric-stalk
form of Stacks 05VV,
`AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint`.  A geometric point
of `X` lifts along an étale morphism to any point of the source above its image **without
extending its field** — that is Stacks 05VN,
`AlgebraicGeometry.Space.exists_geometricPoint_lift_of_isEtale` — and that is exactly what makes
the descent work: the conclusion of Stacks 05VW part (2) is a statement at the *image* of the
lifted geometric point, so the lift has to land on the nose.

The square fed to Stacks 05VW part (2),
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_of_modulePullback`, is

```
U_i --φ_i--> X
|𝟙           |𝟙
v            v
U_i --φ_i--> X
```

which is cartesian because two opposite sides are identities
(`CategoryTheory.IsPullback.of_vert_isIso`).  Its flatness hypothesis on the lower horizontal
morphism is flatness of `φ_i`, which holds because `φ_i` is étale (Stacks 0467).  This is why
the statement is about flatness over the *identity*: for a general `f : X ⟶ Y` the square
whose upper horizontal morphism is `φ_i` and whose right vertical morphism is `f` is cartesian
only when `φ_i` is an isomorphism, so source locality relative to a fixed `f` does not follow
from Stacks 05VW part (2) in this way.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flatness of a quasi-coherent module over its own algebraic space descends along an étale
family surjective on points.**  Let `φ_i : U_i ⟶ X` be étale morphisms of algebraic spaces whose
images exhaust `|X|` and let `F` be a quasi-coherent `𝒪_X`-module whose pullback to each `U_i`
is flat over `U_i` in the sense of Stacks 05VV.  Then `F` is flat over `X`.

A geometric point `x̄` of `X` lifts along some `φ_i` to a geometric point `ū` of `U_i` **with
the same field** by Stacks 05VN, and flatness of `φ_i^* F` over `U_i` at `ū` descends to
flatness of `F` over `X` at `x̄` by Stacks 05VW part (2) applied to the cartesian square whose
vertical morphisms are identities, whose flatness hypothesis is flatness of `φ_i`. -/
theorem isFlatOver_id_of_isEtale_cover {X : AlgebraicSpaces B S hS} {ι : Type v}
    {U : ι → AlgebraicSpaces B S hS} (φ : ∀ i, U i ⟶ X)
    (hφ : ∀ i, IsEtale B S hS (φ i).hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite]
    (hcov : ∀ x : points B S hS X.1, ∃ (i : ι) (u : points B S hS (U i).1),
      pointsMap B S hS (U i).1 (φ i).hom u = x)
    (hflat : ∀ i, IsFlatOver B S hS (U i).2 (𝟙 (U i) : U i ⟶ U i).hom
      ((modulePullback B S hS (φ i)).obj F)) :
    IsFlatOver B S hS X.2 (𝟙 X : X ⟶ X).hom F := by
  refine (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (𝟙 X) F).2 fun xbar ↦ ?_
  obtain ⟨i, u, hu⟩ := hcov xbar.image
  obtain ⟨ubar, -, hval⟩ := exists_geometricPoint_lift_of_isEtale B S hS (U i).2 X.2
    (φ i).hom (hφ i) xbar u hu
  have : ((modulePullback B S hS (φ i)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (φ i) F inferInstance
  have hsq : IsPullback (φ i) (𝟙 (U i)) (𝟙 X) (φ i) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hgp : geometricPointMap (φ i).hom ubar = xbar := Subtype.ext hval
  have hdesc := isFlatOverAtGeometricPoint_of_modulePullback B S hS hsq F ubar
    ((isFlat_iff_forall_isFlatAt B S hS (φ i).hom).1
      (isFlat_of_isEtale B S hS (hφ i)) (geometricPointMap (𝟙 (U i) : U i ⟶ U i).hom ubar).image)
    ((isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (𝟙 (U i))
      ((modulePullback B S hS (φ i)).obj F)).1 (hflat i) ubar)
  rwa [hgp] at hdesc

/-- **Flatness of a quasi-coherent module over a represented algebraic space may be checked on
a jointly surjective family of étale subobjects of the representing object.**  This is
`AlgebraicGeometry.Space.isFlatOver_id_of_isEtale_cover` with its covering hypothesis read on
the points of the representing schemes, which is the shape a family of open subobjects of a
scheme comes in; the comparison is the bijection
`AlgebraicGeometry.Space.pointsToScheme`, natural in the site object. -/
theorem isFlatOver_id_of_etale_cover_of_representable {T : BigFppfOver B S hS} {κ : Type v}
    {W : κ → BigFppfOver B S hS} (p : ∀ k, W k ⟶ T)
    (hp : ∀ k, AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (p k)))
    (hcov : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p k)))
    (F : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    [F.IsQuasicoherentOnSite]
    (hflat : ∀ k, IsFlatOver B S hS (schemeSpace (W k)).2
      (𝟙 (schemeSpace (W k)) : schemeSpace (W k) ⟶ schemeSpace (W k)).hom
      ((modulePullback B S hS (schemeSpaceMap (p k))).obj F)) :
    IsFlatOver B S hS (schemeSpace T).2
      (𝟙 (schemeSpace T) : schemeSpace T ⟶ schemeSpace T).hom F := by
  refine isFlatOver_id_of_isEtale_cover B S hS (fun k ↦ schemeSpaceMap (p k))
    (fun k ↦ isEtale_schemeSpaceMap B S hS (W k) (p k) (hp k)) F (fun x ↦ ?_) hflat
  obtain ⟨k, y, hy⟩ := hcov (pointsToScheme B S hS T x)
  refine ⟨k, (pointsEquivScheme B S hS (W k)).symm y,
    injective_pointsToScheme B S hS T ?_⟩
  have hu : pointsToScheme B S hS (W k) ((pointsEquivScheme B S hS (W k)).symm y) = y :=
    (pointsEquivScheme B S hS (W k)).apply_symm_apply y
  have hnat := pointsToScheme_pointsMap_yoneda B S hS (p k)
    ((pointsEquivScheme B S hS (W k)).symm y)
  rw [hu] at hnat
  exact hnat.trans hy

end AlgebraicGeometry.Space

end
