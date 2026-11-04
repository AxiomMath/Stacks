module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImagePartialSection
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningOpenImmersionIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionOpenSubstack

/-!
# The dimension of an algebraic stack is local on open substacks

An open immersion `j : 𝒰 ⟶ 𝒳` of algebraic stacks over `S` is smooth of relative dimension `0`,
so the dimension formula of **Stacks 0DRP** along it says that the dimension of Stacks 0AFN at a
point of `|𝒰|` is the dimension of `𝒳` at its image, and the additivity of the relative
dimension of **Stacks 0DRL** along a composite with smooth first factor says that the relative
dimension of `j ≫ g` at a point of `|𝒰|` is that of `g` at its image.

Both statements are what makes the proof of **Stacks 0DS4** free to replace `𝒯` by a nonempty
quasi-compact open substack: neither the dimension of `𝒯` at a point nor the dimension of the
fibre of `f` there changes.

## Main results

* `AlgebraicGeometry.Stack.relativeStackDimensionAt_id_eq_zero`: the relative dimension of
  Stacks 0DRL of an identity 1-morphism is `0`.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_zero_of_isMonomorphism`: the relative
  dimension of Stacks 0DRL of a monomorphism is `0`; in particular that of an open immersion is,
  which is `AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_zero_of_isOpenImmersion`.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_of_isMonomorphism_of_isSmooth` and
  `AlgebraicGeometry.Stack.dimensionAtPoint_eq_of_isOpenImmersion`: the dimension of
  Stacks 0AFN does not change along a smooth monomorphism, so it is local on open substacks.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_comp_eq_of_isOpenImmersion`: the relative
  dimension of Stacks 0DRL is local on open substacks of the source.

## Implementation notes

Smoothness of identities, `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_id`, is taken from
`StacksFrontier/AlgebraicGeometry/Stacks/GerbeSmooth.lean`.

The vanishing of the relative dimension of an identity is the additivity of
`AlgebraicGeometry.Stack.relativeStackDimensionAt_comp_of_isSmooth` applied to `𝟙 𝒳 ≫ 𝟙 𝒳`: it
says that the value `c` at a point satisfies `c = c + c`, and `c` is an integer by
`AlgebraicGeometry.Stack.exists_relativeStackDimensionAt_eq_intCast`, so it may be cancelled.
That an open immersion then has relative dimension `0` is
`AlgebraicGeometry.Stack.relativeStackDimensionAt_comp_of_isMonomorphism` at `𝟙 𝒰 ≫ j`, an open
immersion being an immersion and hence a monomorphism (**Stacks 0504**).

Both localities are then immediate: the first is **Stacks 0DRP** and the second the additivity
along `j ≫ g`, each with the relative dimension of `j` replaced by `0`.

## References

* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The relative dimension of Stacks 0DRL only depends on the 1-morphism, not on a proof that it
is locally of finite type. -/
private theorem relativeStackDimensionAt_congr
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} {f f' : 𝒰 ⟶ 𝒳} (e : f = f')
    {hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f}
    {h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS 𝒰}
    {h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳}
    {t : points B S hS 𝒰.val.val 𝒰.val.property} :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒰 h𝒳 t =
      relativeStackDimensionAt.{u, w} B S hS f' (e ▸ hf) h𝒰 h𝒳 t := by
  subst e
  rfl

/-- **The relative dimension of Stacks 0DRL of an identity 1-morphism is `0`.** The additivity
of the relative dimension along `𝟙 𝒳 ≫ 𝟙 𝒳`, whose first factor is smooth, says that its value
`c` at a point satisfies `c = c + c`; and `c` is an integer, so it may be cancelled. -/
theorem relativeStackDimensionAt_id_eq_zero (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hid : AlgebraicStacks.IsLocallyOfFiniteType B S hS (𝟙 𝒳))
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒳.val.val 𝒳.val.property) :
    relativeStackDimensionAt.{u, w} B S hS (𝟙 𝒳) hid h𝒳 h𝒳 t = 0 := by
  classical
  have hcomp : AlgebraicStacks.IsLocallyOfFiniteType B S hS (𝟙 𝒳 ≫ 𝟙 𝒳) := by
    rwa [Category.comp_id]
  have hpt : pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒳.val.property
      (𝟙 𝒳 : 𝒳 ⟶ 𝒳).hom.hom t = t := by
    induction t using Quotient.inductionOn with
    | h p => cases p; rfl
  have h := relativeStackDimensionAt_comp_of_isSmooth.{u, w} B S hS (𝟙 𝒳) (𝟙 𝒳)
    (AlgebraicStacks.isSmooth_id B S hS 𝒳) hid hid hcomp h𝒳 h𝒳 h𝒳 t
  rw [hpt, relativeStackDimensionAt_congr B S hS (Category.comp_id _)] at h
  obtain ⟨c, hc⟩ := exists_relativeStackDimensionAt_eq_intCast.{u, w} B S hS (𝟙 𝒳) hid h𝒳 h𝒳 t
  rw [hc] at h
  rw [hc]
  refine (eq_of_add_intCast_eq_add_intCast (A := (0 : EInt)) (B := ((c : ℤ) : EInt)) (c := c)
    ?_).symm
  rw [zero_add]
  exact h

/-- **The relative dimension of Stacks 0DRL of a monomorphism is `0`.** Postcomposing the
identity of the source of a monomorphism with it does not change the relative dimension, and the
relative dimension of an identity is `0`. -/
theorem relativeStackDimensionAt_eq_zero_of_isMonomorphism
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒳)
    (hmono : AlgebraicStacks.IsMonomorphism B S hS j)
    (hjft : AlgebraicStacks.IsLocallyOfFiniteType B S hS j)
    (h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS 𝒰)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒰.val.val 𝒰.val.property) :
    relativeStackDimensionAt.{u, w} B S hS j hjft h𝒰 h𝒳 t = 0 := by
  classical
  have hid : AlgebraicStacks.IsLocallyOfFiniteType B S hS (𝟙 𝒰) :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS (𝟙 𝒰)
      (AlgebraicStacks.isSmooth_id B S hS 𝒰)
  have hidj : AlgebraicStacks.IsLocallyOfFiniteType B S hS (𝟙 𝒰 ≫ j) := by
    rwa [Category.id_comp]
  have h := relativeStackDimensionAt_comp_of_isMonomorphism.{u, w} B S hS (𝟙 𝒰) j hmono hid hidj
    h𝒰 h𝒰 h𝒳 t
  rw [relativeStackDimensionAt_congr B S hS (Category.id_comp _),
    relativeStackDimensionAt_id_eq_zero B S hS 𝒰 hid h𝒰 t] at h
  exact h

/-- **The dimension of Stacks 0AFN does not change along a smooth monomorphism.** For a smooth
monomorphism `j : 𝒰 ⟶ 𝒳` of locally Noetherian algebraic stacks over `S` and `t ∈ |𝒰|`, the
dimension of `𝒰` at `t` is the dimension of `𝒳` at the image of `t`.

Stacks 0DRP along `j` says that the two differ by the relative dimension of `j` at `t`, and that
is `0`. -/
theorem dimensionAtPoint_eq_of_isMonomorphism_of_isSmooth
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒳)
    (hmono : AlgebraicStacks.IsMonomorphism B S hS j)
    (hjsm : AlgebraicStacks.IsSmooth B S hS j)
    (h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS 𝒰)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒰.val.val 𝒰.val.property) :
    dimensionAtPoint B S hS 𝒰 h𝒰 t =
      dimensionAtPoint B S hS 𝒳 h𝒳
        (pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property j.hom.hom t) := by
  have hjft : AlgebraicStacks.IsLocallyOfFiniteType B S hS j :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS j hjsm
  rw [dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth.{u, w} B S hS j hjsm hjft
      h𝒰 h𝒳 t,
    relativeStackDimensionAt_eq_zero_of_isMonomorphism B S hS j hmono hjft h𝒰 h𝒳 t, add_zero]

/-- **The dimension of Stacks 0AFN is local on open substacks.** For an open immersion
`j : 𝒰 ⟶ 𝒳` of locally Noetherian algebraic stacks over `S` and `t ∈ |𝒰|`, the dimension of
`𝒰` at `t` is the dimension of `𝒳` at the image of `t`. -/
theorem dimensionAtPoint_eq_of_isOpenImmersion
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS 𝒰)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒰.val.val 𝒰.val.property) :
    dimensionAtPoint B S hS 𝒰 h𝒰 t =
      dimensionAtPoint B S hS 𝒳 h𝒳
        (pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒳.val.property j.hom.hom t) :=
  dimensionAtPoint_eq_of_isMonomorphism_of_isSmooth B S hS j
    (AlgebraicStacks.isMonomorphism_of_isOpenImmersion B S hS j hj)
    (AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS j hj) h𝒰 h𝒳 t

/-- **The relative dimension of Stacks 0DRL is local on open substacks of the source.** For an
open immersion `j : 𝒰 ⟶ 𝒯` and a 1-morphism `g : 𝒯 ⟶ 𝒳` locally of finite type of locally
Noetherian algebraic stacks over `S`, the relative dimension of `j ≫ g` at `t ∈ |𝒰|` is that of
`g` at the image of `t`.

The additivity along `j ≫ g`, whose first factor is smooth, says that the two differ by the
relative dimension of `j` at `t`, and that is `0`. -/
theorem relativeStackDimensionAt_comp_eq_of_isOpenImmersion
    {𝒰 𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (j : 𝒰 ⟶ 𝒯) (g : 𝒯 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (hg : AlgebraicStacks.IsLocallyOfFiniteType B S hS g)
    (hjg : AlgebraicStacks.IsLocallyOfFiniteType B S hS (j ≫ g))
    (h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS 𝒰)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒰.val.val 𝒰.val.property) :
    relativeStackDimensionAt.{u, w} B S hS (j ≫ g) hjg h𝒰 h𝒳 t =
      relativeStackDimensionAt.{u, w} B S hS g hg h𝒯 h𝒳
        (pointsMap B S hS 𝒰.val.val 𝒰.val.property 𝒯.val.property j.hom.hom t) := by
  have hjsm : AlgebraicStacks.IsSmooth B S hS j :=
    AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS j hj
  have hjft : AlgebraicStacks.IsLocallyOfFiniteType B S hS j :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS j hjsm
  rw [relativeStackDimensionAt_comp_of_isSmooth.{u, w} B S hS j g hjsm hjft hg hjg h𝒰 h𝒯 h𝒳 t,
    relativeStackDimensionAt_eq_zero_of_isOpenImmersion B S hS j hj hjft h𝒰 h𝒯 t, add_zero]

end AlgebraicGeometry.Stack

end
