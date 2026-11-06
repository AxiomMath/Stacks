module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Restricting the comparison map of Stacks 04CX to a square of étale charts

Let

```
X' --g'--> X
|          |
p'         p
v          v
Y'         Y
```

be a commutative square of algebraic spaces over `S` and let `c : (g')^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` be
its comparison map of Stacks 04CX.  Suppose the square is covered by a square of étale charts:
étale charts `a : U ⟶ X`, `b : V ⟶ Y` of the right column and `a' : U' ⟶ X'`, `b' : V' ⟶ Y'` of
the left column, together with chart morphisms `k : U' ⟶ U` and `l : V' ⟶ V` making the whole
diagram commute.  Then the restriction `(a')^*c` of the comparison map along the chart of the
source **is** the comparison map of Stacks 04CX of the chart square `k`, `r`, `r'`, `l`, read
through the two étale-localization isomorphisms of Stacks 04CU.

This is proved from Stacks 05Z7 alone, applied to the two factorizations

```
U' --a'--> X' --g'--> X        and        U' --k--> U --a--> X
```

of one and the same morphism `U' ⟶ X`, together with the uniqueness clause of Stacks 04CX: both
pastings are comparison maps for the outer square, so they agree, and the two comparison maps
along the étale charts are isomorphisms by Stacks 04CU
(`AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_etaleSquare`).  Nothing about the
sheaf of differentials of a morphism of *schemes* enters, and no hypothesis is carried.

The consequence is that every chartwise question about the comparison map of a commutative square
of algebraic spaces — invertibility for Stacks 05ZC and Stacks 05ZD, monomorphy for Stacks 06BI —
reduces to the same question for the comparison map of the chart square, which is a square of
schemes of the site read as algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isIso_modulePullback_map_of_isIso_chartComparison`: the restriction of
  the comparison map to an étale chart of the source is an isomorphism as soon as the comparison
  map of the chart square is.
* `AlgebraicGeometry.Space.mono_modulePullback_map_of_mono_chartComparison`: the same for
  monomorphy, which is the form Stacks 06BI consumes.
* `AlgebraicGeometry.Space.isIso_of_isIso_chartComparison`: invertibility of the comparison map
  itself, from invertibility of the comparison map of the chart square over a *surjective* étale
  scheme chart of the source.  The descent is
  `AlgebraicGeometry.Space.faithful_modulePullback` together with the abelian structure of the
  `𝒪_{X'}`-modules: a faithful functor reflects monomorphisms and epimorphisms, and a morphism of
  an abelian category which is both is an isomorphism.

## Implementation notes

The two pastings of Stacks 05Z7 are comparison maps for the outer squares with top edges
`a' ≫ g'` and `k ≫ a`.  Those two morphisms are equal but not syntactically so, and the type of a
comparison map depends on its top edge, so the uniqueness clause cannot be applied to them
directly.  `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_eq` and its monomorphy
twin take the two top edges as variables and substitute the equation, which is what makes the
comparison legal; this is the same device as
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_eqToHom_comp`, with the transport absorbed
into the conclusion rather than exposed as an `eqToHom`.

Each comparison map is named by `AlgebraicGeometry.Space.sheafOfDifferentialsMap`, the
construction of Stacks 04CX, rather than carried as a parameter pinned by its characterizing
property: the uniqueness clause makes the two readings interchangeable, and naming the
construction keeps the statements free of auxiliary realizations.

The abelian structure of the `𝒪_F`-modules on the small étale site of an algebraic space is
`SheafOfModules.instAbelian`, restated locally at a raised priority; see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean` for why instance search does not
reach it at the projections of the small étale ringed site.

## References

* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials.
* [Stacks Project, Tag 05Z7](https://stacks.math.columbia.edu/tag/05Z7), the comparison map of a
  composite of two squares.
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0), the étale-local nature
  of a question about `𝒪_X`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ChartRestriction

variable {X Y X' Y' U V U' V' : AlgebraicSpaces B S hS}

/-- **The uniqueness clause of Stacks 04CX across an equality of top edges**, in the form that
transports invertibility.  Two comparison maps for the same right and left edges, whose top edges
are equal, are equal after that equation is substituted; so one is invertible when the other is.
-/
theorem isIso_of_isSheafOfDifferentialsMap_of_eq {f₁ f₂ : X' ⟶ X} (hf : f₁ = f₂) (p : X ⟶ Y)
    (p' : X' ⟶ Y')
    {c₁ : (modulePullback B S hS f₁).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {c₂ : (modulePullback B S hS f₂).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (h₁ : IsSheafOfDifferentialsMap B S hS f₁ p p' c₁)
    (h₂ : IsSheafOfDifferentialsMap B S hS f₂ p p' c₂) (h : IsIso c₂) : IsIso c₁ := by
  subst hf
  rw [eq_of_isSheafOfDifferentialsMap B S hS f₁ p p' h₁ h₂]
  exact h

/-- **The uniqueness clause of Stacks 04CX across an equality of top edges**, in the form that
transports monomorphy. -/
theorem mono_of_isSheafOfDifferentialsMap_of_eq {f₁ f₂ : X' ⟶ X} (hf : f₁ = f₂) (p : X ⟶ Y)
    (p' : X' ⟶ Y')
    {c₁ : (modulePullback B S hS f₁).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {c₂ : (modulePullback B S hS f₂).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (h₁ : IsSheafOfDifferentialsMap B S hS f₁ p p' c₁)
    (h₂ : IsSheafOfDifferentialsMap B S hS f₂ p p' c₂) (h : Mono c₂) : Mono c₁ := by
  subst hf
  rw [eq_of_isSheafOfDifferentialsMap B S hS f₁ p p' h₁ h₂]
  exact h

/-- The pasting of the comparison map of the chart square with the comparison map along the chart
of `X` is a comparison map for the outer square with top edge `k ≫ a`. -/
theorem isSheafOfDifferentialsMap_chartPasting (p : X ⟶ Y) (a : U ⟶ X) (r : U ⟶ V) (b : V ⟶ Y)
    (r' : U' ⟶ V') (k : U' ⟶ U) (l : V' ⟶ V) (hUV : a ≫ p = r ≫ b) (hk : k ≫ r = r' ≫ l) :
    IsSheafOfDifferentialsMap B S hS (k ≫ a) p r'
      ((modulePullbackCompIso B S hS k a).inv.app (sheafOfDifferentials B S hS p) ≫
        (modulePullback B S hS k).map (sheafOfDifferentialsMap B S hS a p r b hUV) ≫
          sheafOfDifferentialsMap B S hS k r r' l hk) :=
  isSheafOfDifferentialsMap_comp B S hS a k p r r'
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS a p r b hUV)
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS k r r' l hk)

/-- The pasting of the comparison map of the square with the comparison map along the chart of
`X'` is a comparison map for the outer square with top edge `a' ≫ g'`. -/
theorem isSheafOfDifferentialsMap_sourceChartPasting (g' : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (a' : U' ⟶ X') (r' : U' ⟶ V') (b' : V' ⟶ Y') (hUV' : a' ≫ p' = r' ≫ b')
    {c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c) :
    IsSheafOfDifferentialsMap B S hS (a' ≫ g') p r'
      ((modulePullbackCompIso B S hS a' g').inv.app (sheafOfDifferentials B S hS p) ≫
        (modulePullback B S hS a').map c ≫
          sheafOfDifferentialsMap B S hS a' p' r' b' hUV') :=
  isSheafOfDifferentialsMap_comp B S hS g' a' p p' r' hc
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS a' p' r' b' hUV')

/-- **The restriction of the comparison map of Stacks 04CX to an étale chart of the source is an
isomorphism as soon as the comparison map of the chart square is.**

The two pastings of Stacks 05Z7 along `U' ⟶ X' ⟶ X` and along `U' ⟶ U ⟶ X` are comparison maps
for the same outer square, so they agree; the two comparison maps along the étale charts are
isomorphisms by Stacks 04CU, and the comparison of inverse images of Stacks 03LU is one as
well. -/
theorem isIso_modulePullback_map_of_isIso_chartComparison (g' : X' ⟶ X) (p : X ⟶ Y)
    (p' : X' ⟶ Y') (a : U ⟶ X) (r : U ⟶ V) (b : V ⟶ Y) (a' : U' ⟶ X') (r' : U' ⟶ V')
    (b' : V' ⟶ Y') (k : U' ⟶ U) (l : V' ⟶ V) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (ha' : IsEtale B S hS a'.hom) (hb' : IsEtale B S hS b'.hom)
    (hUV : a ≫ p = r ≫ b) (hUV' : a' ≫ p' = r' ≫ b') (hk : k ≫ r = r' ≫ l)
    (htop : a' ≫ g' = k ≫ a)
    {c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c)
    (hchart : IsIso (sheafOfDifferentialsMap B S hS k r r' l hk)) :
    IsIso ((modulePullback B S hS a').map c) := by
  have := isIso_sheafOfDifferentialsMap_of_isEtale B S hS p a r b ha hb hUV
  have := isIso_sheafOfDifferentialsMap_of_isEtale B S hS p' a' r' b' ha' hb' hUV'
  have := isIso_of_isSheafOfDifferentialsMap_of_eq B S hS htop p r'
    (isSheafOfDifferentialsMap_sourceChartPasting B S hS g' p p' a' r' b' hUV' hc)
    (isSheafOfDifferentialsMap_chartPasting B S hS p a r b r' k l hUV hk) inferInstance
  have : IsIso ((modulePullback B S hS a').map c ≫
      sheafOfDifferentialsMap B S hS a' p' r' b' hUV') :=
    IsIso.of_isIso_comp_left
      ((modulePullbackCompIso B S hS a' g').inv.app (sheafOfDifferentials B S hS p)) _
  exact IsIso.of_isIso_comp_right ((modulePullback B S hS a').map c)
    (sheafOfDifferentialsMap B S hS a' p' r' b' hUV')

/-- **The restriction of the comparison map of Stacks 04CX to an étale chart of the source is a
monomorphism as soon as the comparison map of the chart square is.**  This is the form the proof
of Stacks 06BI consumes; the argument is that of
`AlgebraicGeometry.Space.isIso_modulePullback_map_of_isIso_chartComparison`. -/
theorem mono_modulePullback_map_of_mono_chartComparison (g' : X' ⟶ X) (p : X ⟶ Y)
    (p' : X' ⟶ Y') (a : U ⟶ X) (r : U ⟶ V) (b : V ⟶ Y) (a' : U' ⟶ X') (r' : U' ⟶ V')
    (b' : V' ⟶ Y') (k : U' ⟶ U) (l : V' ⟶ V) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (ha' : IsEtale B S hS a'.hom) (hb' : IsEtale B S hS b'.hom)
    (hUV : a ≫ p = r ≫ b) (hUV' : a' ≫ p' = r' ≫ b') (hk : k ≫ r = r' ≫ l)
    (htop : a' ≫ g' = k ≫ a)
    {c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c)
    (hchart : Mono (sheafOfDifferentialsMap B S hS k r r' l hk)) :
    Mono ((modulePullback B S hS a').map c) := by
  have := isIso_sheafOfDifferentialsMap_of_isEtale B S hS p a r b ha hb hUV
  have := isIso_sheafOfDifferentialsMap_of_isEtale B S hS p' a' r' b' ha' hb' hUV'
  have := mono_of_isSheafOfDifferentialsMap_of_eq B S hS htop p r'
    (isSheafOfDifferentialsMap_sourceChartPasting B S hS g' p p' a' r' b' hUV' hc)
    (isSheafOfDifferentialsMap_chartPasting B S hS p a r b r' k l hUV hk) inferInstance
  have : Mono ((modulePullback B S hS a').map c ≫
      sheafOfDifferentialsMap B S hS a' p' r' b' hUV') := by
    have h := mono_comp
      (inv ((modulePullbackCompIso B S hS a' g').inv.app (sheafOfDifferentials B S hS p)))
      ((modulePullbackCompIso B S hS a' g').inv.app (sheafOfDifferentials B S hS p) ≫
        (modulePullback B S hS a').map c ≫
          sheafOfDifferentialsMap B S hS a' p' r' b' hUV')
    rwa [IsIso.inv_hom_id_assoc] at h
  exact mono_of_mono ((modulePullback B S hS a').map c)
    (sheafOfDifferentialsMap B S hS a' p' r' b' hUV')

end ChartRestriction

/-! ### Invertibility of the comparison map itself, over a surjective étale scheme chart -/

section Descent

variable {X Y X' Y' V V' : AlgebraicSpaces B S hS}

/-- **A morphism of `𝒪_{X'}`-modules whose inverse image along a surjective étale scheme chart is
an isomorphism is an isomorphism.**  The inverse image is faithful by
`AlgebraicGeometry.Space.faithful_modulePullback`, a faithful functor reflects monomorphisms and
epimorphisms, and a morphism of an abelian category which is both is an isomorphism. -/
theorem isIso_of_isIso_modulePullback_chart (W : BigFppfOver B S hS)
    (i : schemeSpace W ⟶ X') (hi : IsEtale B S hS i.hom)
    (hs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    {M N : Modules.{u, u} B S hS X'.1 X'.2} (c : M ⟶ N)
    (h : IsIso ((modulePullback B S hS i).map c)) : IsIso c := by
  have := faithful_modulePullback B S hS W i hi hs
  have : Mono c := (modulePullback B S hS i).mono_of_mono_map (f := c) inferInstance
  have : Epi c := (modulePullback B S hS i).epi_of_epi_map (f := c) (IsIso.epi_of_iso _)
  exact isIso_of_mono_of_epi c

/-- **The comparison map of Stacks 04CX of a commutative square of algebraic spaces is an
isomorphism as soon as the comparison map of a chart square over a surjective étale scheme chart
of the source is.**

This is `AlgebraicGeometry.Space.isIso_modulePullback_map_of_isIso_chartComparison` followed by
`AlgebraicGeometry.Space.isIso_of_isIso_modulePullback_chart`; it is the shape in which
Stacks 05ZC and Stacks 05ZD consume the chart square. -/
theorem isIso_of_isIso_chartComparison {U W : BigFppfOver B S hS} (g' : X' ⟶ X) (p : X ⟶ Y)
    (p' : X' ⟶ Y') (a : schemeSpace U ⟶ X) (r : schemeSpace U ⟶ V) (b : V ⟶ Y)
    (a' : schemeSpace W ⟶ X') (r' : schemeSpace W ⟶ V') (b' : V' ⟶ Y')
    (k : schemeSpace W ⟶ schemeSpace U) (l : V' ⟶ V) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (ha' : IsEtale B S hS a'.hom) (hb' : IsEtale B S hS b'.hom)
    (hs' : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a'.hom)
    (hUV : a ≫ p = r ≫ b) (hUV' : a' ≫ p' = r' ≫ b') (hk : k ≫ r = r' ≫ l)
    (htop : a' ≫ g' = k ≫ a)
    {c : (modulePullback B S hS g').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS g' p p' c)
    (hchart : IsIso (sheafOfDifferentialsMap B S hS k r r' l hk)) : IsIso c :=
  isIso_of_isIso_modulePullback_chart B S hS W a' ha' hs' c
    (isIso_modulePullback_map_of_isIso_chartComparison B S hS g' p p' a r b a' r' b' k l
      ha hb ha' hb' hUV hUV' hk htop hc hchart)

end Descent

end AlgebraicGeometry.Space

end
