module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescent

/-!
# The limit of Situation 0DKU is a limit of schemes on affine charts

`AlgebraicGeometry.Space.RelativeDescentSituation` (Stacks 0DKU) records the limit
`Y = lim Yᵢ` as a limit cone in the category of presheaves on the size-bounded big fppf site
`BigFppfOver B S hS`.  In the Stacks project the limit of Situation 0DKU is the limit of
algebraic spaces of Limits of Spaces, Lemma 07SF: over an affine chart `Z ⟶ Y₀` it is the
spectrum of the colimit of the rings of the affine base changes `Z ×_{Y₀} Yᵢ`, that is, the
limit of those affine schemes in the category of *all* schemes.  This file records that
standing meaning as a predicate, `AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`.

## Why the presheaf limit is not enough

A limit of presheaves on the size-bounded site only sees test schemes of size below the
cutoff `κ` of the site, and it can differ from the limit of schemes when the latter is too big
for the site.  Let `Σ = κ.out`, let `I` be the finite subsets of `Σ` ordered by inclusion, put
`S = Spec ℚ` and `F_T = ℚ(x_s : s ∈ T)` for `T ∈ I`, and let `Yᵢ = yoneda (Spec F_T)` with the
evident affine transition morphisms; each stage is affine, hence quasi-compact and
quasi-separated.  A compatible family of morphisms `Z ⟶ Spec F_T` from an object `Z` of the
site is a ring map `K = ℚ(x_s : s ∈ Σ) ⟶ Γ(Z, 𝒪_Z)`; if `Z` has a point `z`, composing with
`Γ(Z, 𝒪_Z) ⟶ κ(z)` gives an injection of the field `K` into `κ(z)`, so
`#K ≤ #κ(z) ≤ size Z < κ ≤ #K` (`AlgebraicGeometry.Scheme.mk_stalk_le_size`), which is absurd.
So the presheaf limit of the `Yᵢ` is `yoneda ∅`, an algebraic space, and with `X₀ = Y₀` and
`p₀ = 𝟙` all fields of `AlgebraicGeometry.Space.RelativeDescentSituation` hold.  But `D(𝒪_∅)` is
trivial while `colim_T Hom_{D(F_T)}(F_T, F_T) = K ≠ 0`, so the conclusions of Stacks 0DKV and
Stacks 0DKW fail for this structure.  The limit of the `Spec F_T` in all schemes is `Spec K`,
which is not in the site: the cone with vertex `yoneda ∅` is a limit of presheaves on the site
but not a limit of schemes.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`: the projection `Y ⟶ Y₀` is
  affine, and for every affine object `Z` of the site and every `z : yoneda Z ⟶ Y₀`, every
  choice of objects of the site representing the base changes `Yᵢ ×_{Y₀} Z` and `Y ×_{Y₀} Z`
  gives, on underlying schemes, a limit cone in `Scheme`.

## References

* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- A choice of objects of the site representing the base changes of the stages `Yᵢ`,
`i ≥ i₀`, and of the limit `Y` along `z : yoneda Z ⟶ Y₀`: a system `W` of objects of the site
with a cone `c`, and the projections of each `W i` to `Yᵢ` and to `Z` exhibiting `yoneda (W i)`
as `Yᵢ ×_{Y₀} Z`, compatibly with the transitions, and the same for the vertex of `c` and
`Y ×_{Y₀} Z`. -/
structure AffineBaseChangeRepresentation (Z : BigAffineFppf B S hS)
    (z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.Y.obj (op D.i₀)) where
  /-- The objects representing the base changes of the stages. -/
  W : D.LaterIndexᵒᵖ ⥤ BigFppfOver B S hS
  /-- The cone representing the base change of the limit. -/
  c : Cone W
  /-- The projection of a base change to its stage. -/
  p : ∀ i : D.LaterIndex, yoneda.obj (W.obj (op i)) ⟶ D.Y.obj (op i.1)
  /-- The projection of a base change to `Z`. -/
  q : ∀ i : D.LaterIndex, W.obj (op i) ⟶ (BigAffineFppf.inclusion B S hS).obj Z
  /-- Each `yoneda (W i)` is the base change `Yᵢ ×_{Y₀} Z`. -/
  isPullback : ∀ i, IsPullback (p i) (yoneda.map (q i)) (D.Y.map (homOfLE i.2).op) z
  /-- The projections to the stages are compatible with the transitions. -/
  map_p : ∀ (i j : D.LaterIndex) (h : i ≤ j),
    yoneda.map (W.map (homOfLE h).op) ≫ p i = p j ≫ D.Y.map (homOfLE h).op
  /-- The projections to `Z` are compatible with the transitions. -/
  map_q : ∀ (i j : D.LaterIndex) (h : i ≤ j), W.map (homOfLE h).op ≫ q i = q j
  /-- The projection of the vertex to the limit. -/
  pc : yoneda.obj c.pt ⟶ D.limitCone.pt
  /-- The projection of the vertex to `Z`. -/
  qc : c.pt ⟶ (BigAffineFppf.inclusion B S hS).obj Z
  /-- The vertex is the base change `Y ×_{Y₀} Z`. -/
  isPullback_pt : IsPullback pc (yoneda.map qc) (D.limitCone.π.app (op D.i₀)) z
  /-- The legs of the cone are compatible with the projections to the stages. -/
  π_p : ∀ i, yoneda.map (c.π.app (op i)) ≫ p i = pc ≫ D.limitCone.π.app (op i.1)
  /-- The legs of the cone are compatible with the projections to `Z`. -/
  π_q : ∀ i, c.π.app (op i) ≫ q i = qc

/-- **The limit of Situation 0DKU is a limit of schemes on affine charts.**  This is the
standing meaning of `Y = lim Yᵢ` in Stacks 0DKU, which takes the limit of algebraic spaces of
Stacks 07SF: the projection `Y ⟶ Y₀` is affine, and for every affine object `Z` of the site and
every `z : yoneda Z ⟶ Y₀`, every choice of objects of the site representing the base changes
`Yᵢ ×_{Y₀} Z` and `Y ×_{Y₀} Z` is, on underlying schemes, a limit cone in `Scheme`.

The limit cone of `AlgebraicGeometry.Space.RelativeDescentSituation` is only a limit of
presheaves on the size-bounded site, which can differ from the limit of schemes: see the module
documentation for a situation whose presheaf limit is `yoneda ∅` while the limit of schemes is
the spectrum of a field too big for the site, and for which Stacks 0DKV and Stacks 0DKW fail. -/
def IsSchemeLimit : Prop :=
  IsAffineHom B S hS (D.limitCone.π.app (op D.i₀)) ∧
    ∀ (Z : BigAffineFppf B S hS)
      (z : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.Y.obj (op D.i₀))
      (R : D.AffineBaseChangeRepresentation Z z),
      Nonempty (IsLimit ((BigFppfOver.toScheme B S hS).mapCone R.c))

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
