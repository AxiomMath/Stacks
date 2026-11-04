module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionClosureImage
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismQuasiSeparatedAbs
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# The inequality clause of Stacks 0DS4 for every 1-morphism

Let `f : 𝒯 ⟶ 𝒳` be a 1-morphism locally of finite type of Jacobson, pseudo-catenary, locally
Noetherian algebraic stacks over `S` with `|𝒯|` irreducible and `𝒳` quasi-separated, and let
`𝒵 ↪ 𝒳` be its scheme theoretic image (**Stacks 0CMI**). The inequality clause of
**Stacks 0DS4** says that `dim_t(𝒯_{f(t)}) ≥ dim(𝒯) - dim(𝒵)` for every `t ∈ |𝒯|`, which is
written here as `dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` in `WithBot ℕ∞`. This file proves it with no
quasi-compactness asked of `f`.

Every declaration named in this docstring lives in the namespace `AlgebraicGeometry.Stack`.

The equality clause of Stacks 0DS4 does need `f` quasi-compact:
`not_forall_dimension_le_add_and_exists_isOpen_dense_eq` refutes it without. Both clauses for a
quasi-compact `f` are proved in `DimensionSchemeTheoreticImage.lean`.

## Main results

* `forall_dimension_le_closedSubstackDimension_add_relativeStackDimensionAt`:
  the inequality clause of **Stacks 0DS4**, for every `f`.

## Implementation notes

The proof is the first step of the source's: pass to a nonempty open substack `𝒰` of `𝒯` on
which `f` is quasi-compact. Choose a smooth surjective chart `U ⟶ 𝒯` by a scheme and a nonempty
affine open `V ⊆ U`. **Stacks 05UP**,
`AlgebraicGeometry.Stack.exists_openSubstack_isOpenImmersion_smooth_surjective`, gives an
open substack `j : 𝒰 ⟶ 𝒯` with a surjective smooth 1-morphism `V ⟶ 𝒰`. So `𝒰` is quasi-compact
and nonempty, and `j ≫ f` is quasi-compact by **Stacks 075S**, part (1), since `𝒳` is
quasi-separated: `isQuasiCompactMorphism_of_isQuasiCompactStack_of_isQuasiSeparatedAbs`.

The rest is
`dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_quasiCompactRestriction`:
the equality holds generically for the restriction of the factorization `𝒯 ⟶ 𝒵` to `𝒰`, with
the scheme theoretic image of that restriction, a closed substack of `𝒵` of dimension at most
`dim(𝒵)`, in place of `𝒵`; and the inequality spreads from the nonempty open image of `|𝒰|` to
every point of the irreducible `|𝒯|` by the upper semi-continuity of **Stacks 0DRQ** (1).

## References

* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 05UP](https://stacks.math.columbia.edu/tag/05UP)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A nonempty algebraic stack has a nonempty quasi-compact open substack.** More precisely,
the open substack is given by an open immersion `j : 𝒰 ⟶ 𝒯` with `𝒰` quasi-compact and
nonempty. It is the open substack of **Stacks 05UP** attached to a nonempty affine open of a
smooth surjective chart of `𝒯` by a scheme, which covers it by a surjective 1-morphism. -/
theorem exists_isOpenImmersion_isQuasiCompactStack_nonempty (𝒯 : AlgebraicStacks.{u, w} B S hS)
    (hne : Nonempty (points B S hS 𝒯.val.val 𝒯.val.property)) :
    ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (j : 𝒰 ⟶ 𝒯),
      AlgebraicStacks.IsOpenImmersion B S hS j ∧
        IsQuasiCompactStack.{u, w} B S hS 𝒰.val 𝒰.property ∧
          Nonempty (points B S hS 𝒰.val.val 𝒰.val.property) := by
  obtain ⟨U₀, a₀, ha₀sm, ha₀surj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒯
  obtain ⟨e, hesm, hesurj⟩ := exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U₀
  obtain ⟨t₀⟩ := hne
  obtain ⟨p, -⟩ := ha₀surj t₀
  set X := (BigFppfOver.toScheme B S hS).obj U₀
  let x : X := pointsHomeomorphScheme B S hS U₀ p
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨V₀, i₀, hi₀, hi₀range, hV₀⟩ := BigFppfOver.exists_affineOpen_restrict B S hS U₀ ⟨W, hW⟩
  obtain ⟨v, -⟩ : x ∈ Set.range ((BigFppfOver.toScheme B S hS).map i₀) := by
    rw [hi₀range]; exact hxW
  obtain ⟨hV, 𝒰, j, q, hj, -, hqsurj, -⟩ :=
    exists_openSubstack_isOpenImmersion_smooth_surjective.{u, w} B S hS
      (isAlgebraicSpace_yoneda B S hS U₀) (Space.isOpenImmersion_yoneda_map B S hS i₀ hi₀)
      (e ≫ a₀) (AlgebraicStacks.isSmooth_comp B S hS e a₀ hesm ha₀sm)
      (isSurjective_comp B S hS e a₀ hesurj ha₀surj)
  refine ⟨𝒰, j, hj, ?_, ⟨AlgebraicStacks.pointsMap B S hS q
    (stackPointOfSpacePoint B S hS (yoneda.obj V₀) ((Space.pointsEquivScheme B S hS V₀).symm v))⟩⟩
  exact isQuasiCompactStack_of_isSurjective B S hS q
    (isQuasiCompactStack_fibredCategory.{u, w} B S hS (yoneda.obj V₀) hV
      (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀ hV₀) _) hqsurj

/-- **The inequality clause of Stacks 0DS4, for every 1-morphism.** Let `f : 𝒯 ⟶ 𝒳` be a
1-morphism locally of finite type of Jacobson, pseudo-catenary, locally Noetherian algebraic
stacks over `S`, with `|𝒯|` irreducible and `𝒳` quasi-separated, and let `P` cut out the scheme
theoretic image `𝒵` of `f` (Stacks 0CMI). Then `dim(𝒯) ≤ dim(𝒵) + dim_t(𝒯_{f(t)})` for every
`t ∈ |𝒯|`, i.e. `dim_t(𝒯_{f(t)}) ≥ dim(𝒯) - dim(𝒵)`.

No quasi-compactness of `f` is asked. A nonempty quasi-compact open substack `𝒰` of `𝒯` exists by
`AlgebraicGeometry.Stack.exists_isOpenImmersion_isQuasiCompactStack_nonempty` (through
Stacks 05UP); the restriction of `f` to it is quasi-compact by Stacks 075S, part (1), the target
being quasi-separated; and
`dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_quasiCompactRestriction`
concludes. -/
@[stacks 0DS4 "the inequality clause, for every f (no quasi-compactness), under the hypotheses \
of the statement in the Stacks Project other than quasi-compactness of f. The equality clause needs f \
quasi-compact and is registered on \
AlgebraicGeometry.Stack.dimension_le_add_and_exists_isOpen_dense_eq_add_\
relativeStackDimensionAt_of_isQuasiCompactMorphism; \
without quasi-compactness it is refuted by \
AlgebraicGeometry.Stack.not_forall_dimension_le_add_and_exists_isOpen_dense_eq"]
theorem forall_dimension_le_closedSubstackDimension_add_relativeStackDimensionAt
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    ∀ t : points B S hS 𝒯.val.val 𝒯.val.property,
      dimension B S hS 𝒯 h𝒯 ≤
        closedSubstackDimension B S hS 𝒳 P hP.1 hP.isAlgebraicStack h𝒳 +
          relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t := by
  intro t
  obtain ⟨𝒰, j, hj, h𝒰qc, h𝒰ne⟩ := exists_isOpenImmersion_isQuasiCompactStack_nonempty B S hS 𝒯
    (@IrreducibleSpace.toNonempty _ (pointTopology B S hS 𝒯.val) h𝒯Irreducible)
  exact dimension_le_closedSubstackDimension_add_relativeStackDimensionAt_of_quasiCompactRestriction
    B S hS f hf h𝒯 h𝒳 h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
    h𝒳QuasiSeparated j hj h𝒰ne
    (isQuasiCompactMorphism_of_isQuasiCompactStack_of_isQuasiSeparatedAbs B S hS (j ≫ f) h𝒰qc
      h𝒳QuasiSeparated) hP t

end AlgebraicGeometry.Stack

end
