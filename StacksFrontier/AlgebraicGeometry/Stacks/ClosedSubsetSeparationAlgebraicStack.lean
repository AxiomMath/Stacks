module

public import StacksFrontier.AlgebraicGeometry.Limits.ClosedSubsetFibreSeparation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.InnerSquareOfOuterTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PasteInnerSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsCartesianSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.SitePullbackStackSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeExistenceUniversallyClosed
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Separating a closed subset of a base change of a quasi-compact algebraic stack

Let `g : Z ⟶ Y` be a morphism of affine schemes, let `f : 𝒳 ⟶ Y` be a quasi-compact 1-morphism
of algebraic stacks with `𝒳` quasi-compact, let `z` be a point of `Z` and let `T ⊆ |𝒳 ×_Y Z|` be
a closed subset whose image in `|Z|` misses `z`. **Stacks 0H29** produces an open neighbourhood
`V` of `z` in `Z`, a commutative square `V ⟶ Z' ⟶ Y`, `V ⟶ Z ⟶ Y`, and a closed subset
`T' ⊆ |𝒳 ×_Y Z'|` such that

1. `Z'` is affine and of finite presentation over `Y`,
2. the image `a(z)` of `z` in `|Z'|` misses the image of `T'` in `|Z'|`, and
3. the inverse image of `T` in `|𝒳 ×_Y V|` maps into `T'`.

This file proves it, reducing to the case of schemes
`AlgebraicGeometry.exists_affine_locallyFinitePresentation_separation_isClosed`.

## Main definitions

* `AlgebraicGeometry.Stack.siteMap`: the morphism of the site underlying a 1-morphism of
  represented algebraic stacks, with `AlgebraicGeometry.Stack.schemeStackMapIso` identifying the
  1-morphism with the one it induces.
* `AlgebraicGeometry.Stack.baseChangeSquare`: the canonical 2-fibre product of `f` and the
  1-morphism represented by a morphism of the site — the square `𝒳 ×_Y Z₀`.
* `AlgebraicGeometry.Stack.atlasInnerSquare`: the vertical square of the diagram of Stacks 0H29,
  presenting `W ×_Y Z₀ ⟶ 𝒳 ×_Y Z₀` as a base change of the smooth surjective atlas `W ⟶ 𝒳`.
* `AlgebraicGeometry.Stack.factorMap` and `AlgebraicGeometry.Stack.atlasFactorMap`: the
  horizontal comparison 1-morphisms of that diagram, at the level of the stack and of the atlas.
* `AlgebraicGeometry.Stack.reprPointTopology`: the point topology of Stacks 04XL on a represented
  algebraic stack, made a local instance.

## Main results

* `AlgebraicGeometry.Stack.exists_affine_finitePresentation_separation`: **Stacks 0H29**.
* `AlgebraicGeometry.Stack.exists_affineAtlas_of_isQuasiCompactStack`: the affine smooth
  presentation of a quasi-compact algebraic stack supplied by **Stacks 04YC**, with smoothness
  read as that of Stacks 075U.
* `AlgebraicGeometry.Stack.schemeStackMap_comp`: the 2-Yoneda construction on morphisms of the
  site is functorial.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_atlasFactorSquare`: the right-hand square of the
  diagram of Stacks 0H29 is 2-cartesian.
* `AlgebraicGeometry.Stack.siteMap_atlasFactorMap_comp_sitePullbackFst` and
  `AlgebraicGeometry.Stack.siteMap_atlasFactorMap_comp_sitePullbackSnd`: the two projections of
  the atlas-level comparison 1-morphism, as morphisms of the site. These pin it down, by
  `CategoryTheory.Limits.pullback.hom_ext`, as the comparison morphism of *schemes* that the case
  of schemes hands back.

## Implementation notes

The diagram of the source is built entirely out of terminality, with no 2-cell compatibility
square written by hand.

Both of its squares come from `CategoryTheory.Bicategory.pasteInnerSq` applied to
`AlgebraicGeometry.Stack.atlasInnerSquare`: the outer square fed to it is the atlas square of `V`
reindexed along the comparison 2-cell `AlgebraicGeometry.Stack.factorIsoSnd`
(`CategoryTheory.Bicategory.TwoCommSq.reindexFst`), and the pre-morphism is the one terminality
supplies. The filler of the resulting square is then the first comparison 2-cell of that
pre-morphism by definition, which is exactly the 2-commutativity the point-set steps need; and
the right-hand square is 2-cartesian by
`AlgebraicGeometry.Stack.isTwoFibreProduct_pasteInnerSqAlgebraicStacks`.

The passage between the stack-level comparison 1-morphisms and the comparison morphisms of
schemes that the case of schemes produces runs through
`AlgebraicGeometry.Stack.siteMap`: a 1-morphism of represented algebraic stacks is 2-isomorphic
to the one induced by the morphism of the site underlying it, that assignment is multiplicative
and does not see a 2-morphism, and a morphism into a fibre product of schemes is determined by
its two projections. So each of the two comparison 1-morphisms is identified with a morphism of
the site by computing its two projections out of the 2-cells of the diagram, and nothing has to
be said about the 2-cells themselves.

Quasi-compactness of `f` is a hypothesis of the source and is kept, but it is not used: the
atlas `W` of `𝒳` and the base `Y` are both affine, so the morphism of schemes the case of
schemes is applied to is quasi-compact for that reason alone.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 05BD](https://stacks.math.columbia.edu/tag/05BD)
* [Stacks Project, Tag 0H29](https://stacks.math.columbia.edu/tag/0H29)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of the site underlying 1-morphisms of represented algebraic stacks -/

/-- **The 2-Yoneda construction on morphisms of the site is functorial.** The 1-morphism of
represented algebraic stacks induced by a composite of morphisms of the site is the composite of
the induced 1-morphisms.

Both sides are the based functor `CategoryTheory.Over.map` of the composite, read in the
2-category of algebraic stacks: the 1-morphisms and 2-morphisms of a full sub-2-category are
those of the ambient one, so the claim is `CategoryTheory.Over.mapComp_eq` together with the
fact that a based functor is determined by its underlying functor. -/
theorem schemeStackMap_comp {U V W : BigFppfOver B S hS} (a : U ⟶ V) (b : V ⟶ W) :
    schemeStackMap.{u, w} B S hS a ≫ schemeStackMap.{u, w} B S hS b =
      schemeStackMap.{u, w} B S hS (a ≫ b) :=
  Bicategory.InducedBicategory.hom_ext (Bicategory.InducedBicategory.hom_ext
    (BasedCategory.BasedFunctor.ext' (Over.mapComp_eq a b).symm))

/-- The morphism of the big fppf category over `S` underlying a 1-morphism of represented
algebraic stacks. -/
abbrev siteMap {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V) : U ⟶ V :=
  schemeMapOfFunctor B S hS c.hom.hom

/-- **A 1-morphism of represented algebraic stacks is 2-isomorphic to the one induced by the
morphism of the site underlying it.** The two have the same underlying morphism of the site by
`AlgebraicGeometry.Stack.schemeMapOfFunctor_overMapBased`, so
`AlgebraicGeometry.Stack.basedNatTransOfSchemeMapEq` gives a 2-morphism between them, and every
2-morphism of categories fibred in groupoids is invertible. -/
def schemeStackMapIso {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V) :
    c ≅ schemeStackMap.{u, w} B S hS (siteMap B S hS c) :=
  let η : c.hom ⟶ (schemeStackMap.{u, w} B S hS (siteMap B S hS c)).hom :=
    Bicategory.InducedBicategory.mkHom₂
      (basedNatTransOfSchemeMapEq B S hS c.hom.hom
        (overMapBased B S hS (siteMap B S hS c))
        (schemeMapOfFunctor_overMapBased B S hS (siteMap B S hS c)).symm)
  Bicategory.InducedBicategory.isoMk
    (@asIso _ _ _ _ η ((CatFiberedInGroupoids.homGroupoid _ _).all_isIso η))

/-- The morphism of the site underlying the 1-morphism induced by a morphism of the site is that
morphism. -/
theorem siteMap_schemeStackMap {U V : BigFppfOver B S hS} (m : U ⟶ V) :
    siteMap B S hS (schemeStackMap.{u, w} B S hS m) = m :=
  schemeMapOfFunctor_overMapBased B S hS m

/-- A 2-morphism does not change the morphism of the site underlying a 1-morphism of represented
algebraic stacks. -/
theorem siteMap_eq_of_iso {U V : BigFppfOver B S hS}
    {c d : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V} (e : c ≅ d) :
    siteMap B S hS c = siteMap B S hS d :=
  schemeMapOfFunctor_eq_of_basedNatTrans B S hS e.hom.hom.hom

/-- **The morphism of the site underlying a composite.** The first factor is 2-isomorphic to the
1-morphism induced by the morphism of the site underlying it, and precomposition with an induced
1-morphism is computed by `AlgebraicGeometry.Stack.schemeMapOfFunctor_comp_overMapBased`. -/
theorem siteMap_comp {U V W : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V)
    (d : schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS W) :
    siteMap B S hS (c ≫ d) = siteMap B S hS c ≫ siteMap B S hS d :=
  (siteMap_eq_of_iso B S hS (Bicategory.whiskerRightIso (schemeStackMapIso B S hS c) d)).trans
    (schemeMapOfFunctor_comp_overMapBased B S hS (siteMap B S hS c) d.hom.hom)

/-- **Two morphisms of the site inducing 2-isomorphic 1-morphisms are equal.** -/
theorem eq_of_iso_schemeStackMap {U V : BigFppfOver B S hS} {m n : U ⟶ V}
    (e : schemeStackMap.{u, w} B S hS m ≅ schemeStackMap.{u, w} B S hS n) : m = n := by
  have h := siteMap_eq_of_iso B S hS e
  rwa [siteMap_schemeStackMap, siteMap_schemeStackMap] at h

/-- The point topology of Stacks 04XL on the points of the algebraic stack represented by an
object of the site. It is made a local instance so that the homeomorphism
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, whose statement supplies this topology by a
`letI`, can be used without spelling the topology out at every application. -/
@[instance_reducible]
def reprPointTopology (U : BigFppfOver B S hS) :
    TopologicalSpace (points B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property) :=
  pointTopology B S hS (schemeFibredCategory B S hS U)

attribute [local instance] reprPointTopology

/-- **The identification of the points of a represented algebraic stack with its scheme carries
a 1-morphism to the morphism of the site underlying it.** -/
theorem pointsHomeomorphScheme_pointsMap {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V)
    (x : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U)) :
    pointsHomeomorphScheme B S hS V (AlgebraicStacks.pointsMap B S hS c x) =
      (BigFppfOver.toScheme B S hS).map (siteMap B S hS c)
        (pointsHomeomorphScheme B S hS U x) := by
  rw [AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS (schemeStackMapIso B S hS c).hom]
  exact pointsHomeomorphScheme_naturality B S hS _ x

/-- **Smoothness from relative smoothness, for a 1-morphism of algebraic stacks.** Smoothness in
the sense of Stacks 075U is the relative property of Stacks 03YK at the smoothness of morphisms
of algebraic spaces, both ends being algebraic stacks. -/
theorem isSmooth_of_isRelativelySmooth {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (c : 𝒳 ⟶ 𝒴)
    (hc : IsRelativelySmooth.{u, u, u + 1} B S hS c.hom) :
    AlgebraicStacks.IsSmooth B S hS c := by
  obtain ⟨hrep, hrel⟩ := hc
  exact (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u + 1} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) 𝒳.property 𝒴.property c.hom hrep).mpr
    hrel

/-! ### The diagram of Stacks 0H29 -/

variable {Y : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (f : 𝒳 ⟶ schemeStack.{u, w} B S hS Y) {W : BigFppfOver B S hS}
  (ρ : schemeStack.{u, w} B S hS W ⟶ 𝒳)

/-- The base change `𝒳 ×_Y Z₀` of `f : 𝒳 ⟶ Y` along the 1-morphism of represented algebraic
stacks induced by a morphism `k : Z₀ ⟶ Y` of the site: the canonical 2-fibre product square of
that cospan. -/
abbrev baseChangeSquare {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y) :
    Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS k) f :=
  twoFibreProductSquareAlgebraicStacks B S hS (schemeStackMap.{u, w} B S hS k) f

/-- The square of represented algebraic stacks over the fibre product `W ×_Y Z₀` of the site,
with the projection to `Z₀` as its first leg. -/
abbrev atlasSquare (s : W ⟶ Y) {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y) :
    Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS k) (schemeStackMap.{u, w} B S hS s) :=
  (schemeStackSquare.{u, w} B S hS (isPullback_sitePullback B S hS s k).w).swap

/-- **The vertical square of the diagram of Stacks 0H29.** The fibre product `W ×_Y Z₀` of the
site, read as a square over the cospan `(𝒳 ×_Y Z₀ ⟶ 𝒳, ρ)`: it exhibits
`W ×_Y Z₀ ⟶ 𝒳 ×_Y Z₀` as a base change of the atlas `ρ : W ⟶ 𝒳`. -/
def atlasInnerSquare (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y) :
    Bicategory.TwoCommSq (baseChangeSquare B S hS f k).snd ρ :=
  innerSquareOfOuter B S hS (baseChangeSquare B S hS f k)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (schemeStackMap.{u, w} B S hS k) f) θ (atlasSquare B S hS s k)

/-- **The vertical square of the diagram of Stacks 0H29 is 2-cartesian.** -/
def isTwoFibreProduct_atlasInnerSquare (s : W ⟶ Y)
    (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s) {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y) :
    Bicategory.IsTwoFibreProduct (atlasInnerSquare B S hS f ρ s θ k) :=
  isTwoFibreProduct_innerSquareOfOuter B S hS (baseChangeSquare B S hS f k)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (schemeStackMap.{u, w} B S hS k) f) θ (atlasSquare B S hS s k)
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_sitePullbackStackSquare.{u, w} B S hS s k))

/-- The second leg of the vertical square is the projection `W ×_Y Z₀ ⟶ W`, up to a
2-morphism. -/
def atlasInnerSquare_snd_iso (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y) :
    schemeStackMap.{u, w} B S hS (sitePullbackFst B S hS s k) ≅
      (atlasInnerSquare B S hS f ρ s θ k).snd :=
  innerSquareOfOuter_snd_iso B S hS (baseChangeSquare B S hS f k)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (schemeStackMap.{u, w} B S hS k) f) θ (atlasSquare B S hS s k)

/-- The first leg of the vertical square, followed by the projection of `𝒳 ×_Y Z₀` to `Z₀`, is
the projection `W ×_Y Z₀ ⟶ Z₀`, up to a 2-morphism. -/
def atlasInnerSquare_fst_comp_iso (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y) :
    schemeStackMap.{u, w} B S hS (sitePullbackSnd B S hS s k) ≅
      (atlasInnerSquare B S hS f ρ s θ k).fst ≫ (baseChangeSquare B S hS f k).fst :=
  innerSquareOfOuter_fst_comp_iso B S hS (baseChangeSquare B S hS f k)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (schemeStackMap.{u, w} B S hS k) f) θ (atlasSquare B S hS s k)

/-! ### The horizontal comparison 1-morphisms -/

/-- The base change `𝒳 ×_Y V`, read as a square over the cospan `(Z' ⟶ Y, f)` through a
factorization `k = a ≫ b`. -/
def factorSquare {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y)
    (hab : k = a ≫ b) : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS b) f where
  pt := (baseChangeSquare B S hS f k).pt
  fst := (baseChangeSquare B S hS f k).fst ≫ schemeStackMap.{u, w} B S hS a
  snd := (baseChangeSquare B S hS f k).snd
  iso := α_ _ _ _ ≪≫ Bicategory.whiskerLeftIso _ (eqToIso
      ((schemeStackMap_comp B S hS a b).trans
        (congrArg (schemeStackMap.{u, w} B S hS) hab.symm))) ≪≫
    (baseChangeSquare B S hS f k).iso

/-- The pre-morphism from `AlgebraicGeometry.Stack.factorSquare` to the base change `𝒳 ×_Y Z'`,
supplied by terminality of the latter. -/
def factorPreHom {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y)
    (hab : k = a ≫ b) :
    Bicategory.TwoCommSq.PreHom (factorSquare B S hS f k a b hab)
      (baseChangeSquare B S hS f b) :=
  Bicategory.twoFibreProductPreHom
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (schemeStackMap.{u, w} B S hS b) f) (factorSquare B S hS f k a b hab)

/-- **The comparison 1-morphism `𝒳 ×_Y V ⟶ 𝒳 ×_Y Z'`** attached to a factorization
`k = a ≫ b`. -/
def factorMap {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y)
    (hab : k = a ≫ b) :
    (baseChangeSquare B S hS f k).pt ⟶ (baseChangeSquare B S hS f b).pt :=
  (factorPreHom B S hS f k a b hab).hom

/-- The comparison 1-morphism followed by the projection to `Z'` is the projection to `V`
followed by `a`, up to a 2-morphism. -/
def factorIsoFst {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y)
    (hab : k = a ≫ b) :
    (baseChangeSquare B S hS f k).fst ≫ schemeStackMap.{u, w} B S hS a ≅
      factorMap B S hS f k a b hab ≫ (baseChangeSquare B S hS f b).fst :=
  (factorPreHom B S hS f k a b hab).isoFst

/-- The comparison 1-morphism commutes with the two projections to `𝒳`, up to a 2-morphism. -/
def factorIsoSnd {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y)
    (hab : k = a ≫ b) :
    (baseChangeSquare B S hS f k).snd ≅
      factorMap B S hS f k a b hab ≫ (baseChangeSquare B S hS f b).snd :=
  (factorPreHom B S hS f k a b hab).isoSnd

/-- The vertical square of `V`, reindexed so that its cospan is the one the comparison
1-morphism cuts out. -/
def atlasOuterSquare (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    Bicategory.TwoCommSq
      (factorMap B S hS f k a b hab ≫ (baseChangeSquare B S hS f b).snd) ρ :=
  (atlasInnerSquare B S hS f ρ s θ k).reindexFst (factorIsoSnd B S hS f k a b hab)

/-- The pre-morphism from the reassociated outer rectangle of `V` to the vertical square of `Z'`,
supplied by terminality of the latter. -/
def atlasFactorPreHom (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    Bicategory.TwoCommSq.PreHom
      (Bicategory.pasteOuterSq (factorMap B S hS f k a b hab)
        (atlasOuterSquare B S hS f ρ s θ k a b hab)) (atlasInnerSquare B S hS f ρ s θ b) :=
  Bicategory.twoFibreProductPreHom (isTwoFibreProduct_atlasInnerSquare B S hS f ρ s θ b)
    (Bicategory.pasteOuterSq (factorMap B S hS f k a b hab)
      (atlasOuterSquare B S hS f ρ s θ k a b hab))

/-- **The comparison 1-morphism `W ×_Y V ⟶ W ×_Y Z'`** at the level of the atlas. -/
def atlasFactorMap (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    schemeStack.{u, w} B S hS (sitePullbackObj B S hS s k) ⟶
      schemeStack.{u, w} B S hS (sitePullbackObj B S hS s b) :=
  (atlasFactorPreHom B S hS f ρ s θ k a b hab).hom

/-- **The right-hand square of the diagram of Stacks 0H29**: the comparison 1-morphisms of the
stack and of the atlas, over the two vertical legs. -/
def atlasFactorSquare (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    Bicategory.TwoCommSq (factorMap B S hS f k a b hab)
      (atlasInnerSquare B S hS f ρ s θ b).fst :=
  Bicategory.pasteInnerSq (atlasInnerSquare B S hS f ρ s θ b)
    (atlasFactorPreHom B S hS f ρ s θ k a b hab)

/-- **The right-hand square of the diagram of Stacks 0H29 is 2-cartesian.** -/
def isTwoFibreProduct_atlasFactorSquare (s : W ⟶ Y)
    (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s) {V Z' : BigFppfOver B S hS} (k : V ⟶ Y)
    (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    Bicategory.IsTwoFibreProduct (atlasFactorSquare B S hS f ρ s θ k a b hab) :=
  isTwoFibreProduct_pasteInnerSqAlgebraicStacks B S hS
    (atlasInnerSquare B S hS f ρ s θ b) (isTwoFibreProduct_atlasInnerSquare B S hS f ρ s θ b)
    (Bicategory.isTwoFibreProduct_reindexFst (factorIsoSnd B S hS f k a b hab)
      (isTwoFibreProduct_atlasInnerSquare B S hS f ρ s θ k))
    (atlasFactorPreHom B S hS f ρ s θ k a b hab)

/-- The atlas-level comparison 1-morphism commutes with the two projections to `W`, up to a
2-morphism. -/
def atlasFactorIsoFst (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    schemeStackMap.{u, w} B S hS (sitePullbackFst B S hS s k) ≅
      atlasFactorMap B S hS f ρ s θ k a b hab ≫
        schemeStackMap.{u, w} B S hS (sitePullbackFst B S hS s b) :=
  atlasInnerSquare_snd_iso B S hS f ρ s θ k ≪≫
    (atlasFactorPreHom B S hS f ρ s θ k a b hab).isoSnd ≪≫
    Bicategory.whiskerLeftIso _ (atlasInnerSquare_snd_iso B S hS f ρ s θ b).symm

/-- The atlas-level comparison 1-morphism followed by the projection to `Z'` is the projection to
`V` followed by `a`, up to a 2-morphism. -/
def atlasFactorIsoSnd (s : W ⟶ Y) (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s)
    {V Z' : BigFppfOver B S hS} (k : V ⟶ Y) (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    schemeStackMap.{u, w} B S hS (sitePullbackSnd B S hS s k) ≫
        schemeStackMap.{u, w} B S hS a ≅
      atlasFactorMap B S hS f ρ s θ k a b hab ≫
        schemeStackMap.{u, w} B S hS (sitePullbackSnd B S hS s b) :=
  Bicategory.whiskerRightIso (atlasInnerSquare_fst_comp_iso B S hS f ρ s θ k) _ ≪≫
    α_ _ _ _ ≪≫
    Bicategory.whiskerLeftIso _ (factorIsoFst B S hS f k a b hab) ≪≫
    (α_ _ _ _).symm ≪≫
    Bicategory.whiskerRightIso (atlasFactorPreHom B S hS f ρ s θ k a b hab).isoFst _ ≪≫
    α_ _ _ _ ≪≫
    Bicategory.whiskerLeftIso _ (atlasInnerSquare_fst_comp_iso B S hS f ρ s θ b).symm

/-- **The first projection of the atlas-level comparison morphism of the site.** -/
theorem siteMap_atlasFactorMap_comp_sitePullbackFst (s : W ⟶ Y)
    (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s) {V Z' : BigFppfOver B S hS} (k : V ⟶ Y)
    (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    siteMap B S hS (atlasFactorMap B S hS f ρ s θ k a b hab) ≫ sitePullbackFst B S hS s b =
      sitePullbackFst B S hS s k := by
  have h := siteMap_eq_of_iso B S hS (atlasFactorIsoFst B S hS f ρ s θ k a b hab)
  rw [siteMap_schemeStackMap, siteMap_comp, siteMap_schemeStackMap] at h
  exact h.symm

/-- **The second projection of the atlas-level comparison morphism of the site.** -/
theorem siteMap_atlasFactorMap_comp_sitePullbackSnd (s : W ⟶ Y)
    (θ : ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s) {V Z' : BigFppfOver B S hS} (k : V ⟶ Y)
    (a : V ⟶ Z') (b : Z' ⟶ Y) (hab : k = a ≫ b) :
    siteMap B S hS (atlasFactorMap B S hS f ρ s θ k a b hab) ≫ sitePullbackSnd B S hS s b =
      sitePullbackSnd B S hS s k ≫ a := by
  have h := siteMap_eq_of_iso B S hS (atlasFactorIsoSnd B S hS f ρ s θ k a b hab)
  rw [siteMap_comp, siteMap_schemeStackMap, siteMap_schemeStackMap, siteMap_comp,
    siteMap_schemeStackMap] at h
  exact h.symm

/-! ### The separation lemma -/

/-- **Stacks 04YC.** A quasi-compact algebraic stack over `S` receives a smooth surjective
1-morphism from the algebraic stack represented by an object of the site with affine underlying
scheme. -/
theorem exists_affineAtlas_of_isQuasiCompactStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    ∃ (W : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
      (ρ : schemeStack.{u, w} B S hS W ⟶ 𝒳),
      IsSurjective B S hS ρ ∧ AlgebraicStacks.IsSmooth B S hS ρ := by
  obtain ⟨W, hW, ρ, hρsurj, hρrel⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 h𝒳
  exact ⟨W, hW, ρ, hρsurj, isSmooth_of_isRelativelySmooth B S hS ρ hρrel⟩

/-- **Stacks 0H29.** Let `g : Z ⟶ Y` be a morphism of the big fppf category of `S` between
objects with affine underlying schemes, let `f : 𝒳 ⟶ Y` be a quasi-compact 1-morphism of
algebraic stacks over `S` with `𝒳` quasi-compact, let `z` be a point of `Z` and let
`T ⊆ |𝒳 ×_Y Z|` be a closed subset whose image in `|Z|` misses `z`. Then there are an open
neighbourhood `V` of `z` in `Z`, a commutative square `V ⟶ Z' ⟶ Y`, `V ⟶ Z ⟶ Y`, and a closed
subset `T' ⊆ |𝒳 ×_Y Z'|` such that

1. `Z'` is affine and of finite presentation over `Y`,
2. the image of `z` in `|Z'|` misses the image of `T'` in `|Z'|`, and
3. the inverse image of `T` in `|𝒳 ×_Y V|` maps into `T'`.

The two comparison 1-morphisms of the last two clauses are the canonical ones
`AlgebraicGeometry.Stack.factorMap`; their compatibilities with the projections of the three base
changes are `AlgebraicGeometry.Stack.factorIsoFst` and `AlgebraicGeometry.Stack.factorIsoSnd`. -/
@[stacks 0H29]
theorem exists_affine_finitePresentation_separation {Y Z : BigFppfOver B S hS}
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) (g : Z ⟶ Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ schemeStack.{u, w} B S hS Y)
    (_hf : IsQuasiCompactMorphism.{u, w} B S hS f)
    (h𝒳 : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS Z))
    (T : Set (AlgebraicStacks.points B S hS (baseChangeSquare B S hS f g).pt))
    (hT : @IsClosed _ (pointTopology B S hS (baseChangeSquare B S hS f g).pt.val) T)
    (hz : z ∉ AlgebraicStacks.pointsMap B S hS (baseChangeSquare B S hS f g).fst '' T) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ Z),
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      ∃ v : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS V),
        AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS j) v = z ∧
        ∃ (Z' : BigFppfOver B S hS) (b : Z' ⟶ Y),
          IsAffine ((BigFppfOver.toScheme B S hS).obj Z') ∧
          FinitePresentation ((BigFppfOver.toScheme B S hS).map b) ∧
          ∃ (a : V ⟶ Z') (hab : j ≫ g = a ≫ b)
            (T' : Set (AlgebraicStacks.points B S hS (baseChangeSquare B S hS f b).pt)),
            @IsClosed _ (pointTopology B S hS (baseChangeSquare B S hS f b).pt.val) T' ∧
            AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS a) v ∉
              AlgebraicStacks.pointsMap B S hS (baseChangeSquare B S hS f b).fst '' T' ∧
            AlgebraicStacks.pointsMap B S hS (factorMap B S hS f (j ≫ g) a b hab) ''
                (AlgebraicStacks.pointsMap B S hS
                  (factorMap B S hS f (j ≫ g) j g rfl) ⁻¹' T) ⊆ T' := by
  classical
  have := hY
  have := hZ
  -- The affine smooth presentation of `𝒳` supplied by Stacks 04YC.
  obtain ⟨W, hWaff, ρ, hρsurj, hρsmooth⟩ :=
    exists_affineAtlas_of_isQuasiCompactStack B S hS 𝒳 h𝒳
  have := hWaff
  -- The morphism `W ⟶ Y` of the site under `ρ ≫ f`, with its 2-Yoneda identification.
  obtain ⟨s, θ⟩ : Σ s : W ⟶ Y, ρ ≫ f ≅ schemeStackMap.{u, w} B S hS s :=
    ⟨_, schemeStackMapIso B S hS (ρ ≫ f)⟩
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map s) := inferInstance
  -- The vertical legs of the diagram are smooth and surjective, being base changes of `ρ`.
  have hsm : ∀ {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y),
      AlgebraicStacks.IsSmooth B S hS (atlasInnerSquare B S hS f ρ s θ k).fst := fun k =>
    AlgebraicStacks.isSmooth_baseChange B S hS ρ (baseChangeSquare B S hS f k).snd _
      (isTwoFibreProduct_atlasInnerSquare B S hS f ρ s θ k) hρsmooth
  have hsu : ∀ {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y),
      IsSurjective B S hS (atlasInnerSquare B S hS f ρ s θ k).fst := fun k =>
    isSurjective_of_isTwoFibreProduct B S hS (atlasInnerSquare B S hS f ρ s θ k).swap
      (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_atlasInnerSquare B S hS f ρ s θ k))
      hρsurj
  -- A point of `W ×_Y Z₀` has the same image in `Z₀` read through the stack or through the site.
  have key : ∀ {Z₀ : BigFppfOver B S hS} (k : Z₀ ⟶ Y)
      (x : AlgebraicStacks.points B S hS
        (schemeStack.{u, w} B S hS (sitePullbackObj B S hS s k))),
      pointsHomeomorphScheme B S hS Z₀
          (AlgebraicStacks.pointsMap B S hS (baseChangeSquare B S hS f k).fst
            (AlgebraicStacks.pointsMap B S hS (atlasInnerSquare B S hS f ρ s θ k).fst x)) =
        (BigFppfOver.toScheme B S hS).map (sitePullbackSnd B S hS s k)
          (pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s k) x) := by
    intro Z₀ k x
    have h1 := congrFun (AlgebraicStacks.pointsMap_comp B S hS
      (atlasInnerSquare B S hS f ρ s θ k).fst (baseChangeSquare B S hS f k).fst) x
    have h3 := congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
      (atlasInnerSquare_fst_comp_iso B S hS f ρ s θ k).hom) x
    exact (congrArg (pointsHomeomorphScheme B S hS Z₀) (h1.symm.trans h3.symm)).trans
      (pointsHomeomorphScheme_naturality B S hS (sitePullbackSnd B S hS s k) x)
  -- The closed subset of `W ×_Y Z`, read on the scheme, and the point of `Z` it misses.
  have hTW : @IsClosed _ (pointTopology B S hS (atlasInnerSquare B S hS f ρ s θ g).pt.val)
      (AlgebraicStacks.pointsMap B S hS (atlasInnerSquare B S hS f ρ s θ g).fst ⁻¹' T) :=
    @IsClosed.preimage _ _ (pointTopology B S hS (atlasInnerSquare B S hS f ρ s θ g).pt.val)
      (pointTopology B S hS (baseChangeSquare B S hS f g).pt.val) _
      (continuous_pointsMap B S hS (atlasInnerSquare B S hS f ρ s θ g).pt.val
        (baseChangeSquare B S hS f g).pt.val _) _ hT
  set SE : Set ((BigFppfOver.toScheme B S hS).obj (sitePullbackObj B S hS s g)) :=
    (pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s g)).symm ⁻¹'
      (AlgebraicStacks.pointsMap B S hS (atlasInnerSquare B S hS f ρ s θ g).fst ⁻¹' T)
    with hSEdef
  have hE : IsClosed SE :=
    @IsClosed.preimage _ _ _
      (pointTopology B S hS (atlasInnerSquare B S hS f ρ s θ g).pt.val) _
      (pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s g)).symm.continuous _ hTW
  have hEt : pointsHomeomorphScheme B S hS Z z ∉
      pullback.snd ((BigFppfOver.toScheme B S hS).map s)
        ((BigFppfOver.toScheme B S hS).map g) '' SE := by
    rintro ⟨x, hx, hxt⟩
    refine hz ⟨AlgebraicStacks.pointsMap B S hS (atlasInnerSquare B S hS f ρ s θ g).fst
      ((pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s g)).symm x), hx, ?_⟩
    refine (pointsHomeomorphScheme B S hS Z).injective ?_
    refine (key g ((pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s g)).symm x)).trans ?_
    refine Eq.trans (congrArg
      (fun y => (BigFppfOver.toScheme B S hS).map (sitePullbackSnd B S hS s g) y)
      ((pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s g)).apply_symm_apply x)) ?_
    exact hxt
  -- The case of schemes, Stacks 05BD, applied to the atlas.
  obtain ⟨Vo, htV, Z'sch, hZ'aff, bsch, hbsch, asch, habsch, E', hE', psch, qsch,
    hp1, hp2, hq1, hq2, hnot', hsubE⟩ :=
    exists_affine_locallyFinitePresentation_separation_isClosed
      ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map g)
      (pointsHomeomorphScheme B S hS Z z) SE hE hEt
  have := hZ'aff
  have := hbsch
  -- The open neighbourhood and the finitely presented approximation, as objects of the site.
  have hVcont : B.Contains Vo.1.toScheme :=
    Scheme.size_lt_of_isOpenImmersion Vo.1.ι Z.left.property
  have hZ'cont : B.Contains Z'sch :=
    B.contains_of_locallyOfFinitePresentation bsch Y.left.property
  set Vst : BigFppfOver B S hS := BigFppfOver.siteObjectOver B S hS Z hVcont Vo.1.ι with hVstdef
  set jst : Vst ⟶ Z := BigFppfOver.siteMapOver B S hS Z hVcont Vo.1.ι with hjstdef
  set Z'st : BigFppfOver B S hS := BigFppfOver.siteObjectOver B S hS Y hZ'cont bsch with hZ'stdef
  set bst : Z'st ⟶ Y := BigFppfOver.siteMapOver B S hS Y hZ'cont bsch with hbstdef
  have hjopen : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jst) :=
    (inferInstance : AlgebraicGeometry.IsOpenImmersion Vo.1.ι)
  -- The morphism `V ⟶ Z'` of the site, and the commutativity of the square.
  have hgw : (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map Y.hom =
      B.inclusion.map Z.hom :=
    (B.inclusion.map_comp g.left Y.hom).symm.trans (congrArg B.inclusion.map (Over.w g))
  have hstr : asch ≫ bsch ≫ B.inclusion.map Y.hom = Vo.1.ι ≫ B.inclusion.map Z.hom := by
    rw [← hgw, ← Category.assoc, ← habsch, Category.assoc]
  set ast : Vst ⟶ Z'st :=
    Over.homMk (⟨asch⟩ : Vst.left ⟶ Z'st.left)
      (B.inclusion.map_injective (by rw [B.inclusion.map_comp]; exact hstr)) with hastdef
  have hjg : jst ≫ g = ast ≫ bst :=
    Over.OverMorphism.ext (B.inclusion.map_injective habsch)
  -- The point of `V` above `z`.
  set v : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS Vst) :=
    (pointsHomeomorphScheme B S hS Vst).symm ⟨pointsHomeomorphScheme B S hS Z z, htV⟩ with hvdef
  have hvh : pointsHomeomorphScheme B S hS Vst v =
      ⟨pointsHomeomorphScheme B S hS Z z, htV⟩ :=
    (pointsHomeomorphScheme B S hS Vst).apply_symm_apply _
  have hv : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS jst) v = z := by
    refine (pointsHomeomorphScheme B S hS Z).injective ?_
    refine (pointsHomeomorphScheme_naturality B S hS jst v).trans ?_
    rw [hvh]
    rfl
  -- The two comparison morphisms of the site are the ones the case of schemes produced.
  have hpt : ∀ {Z' : BigFppfOver B S hS} (a : Vst ⟶ Z') (b : Z' ⟶ Y) (hab : jst ≫ g = a ≫ b)
      (p : (BigFppfOver.toScheme B S hS).obj (sitePullbackObj B S hS s (jst ≫ g)) ⟶ _),
      p ≫ (BigFppfOver.toScheme B S hS).map (sitePullbackFst B S hS s b) =
        (BigFppfOver.toScheme B S hS).map (sitePullbackFst B S hS s (jst ≫ g)) →
      p ≫ (BigFppfOver.toScheme B S hS).map (sitePullbackSnd B S hS s b) =
        (BigFppfOver.toScheme B S hS).map (sitePullbackSnd B S hS s (jst ≫ g) ≫ a) → ∀ ξ,
      pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s b)
          (AlgebraicStacks.pointsMap B S hS
            (atlasFactorMap B S hS f ρ s θ (jst ≫ g) a b hab) ξ) =
        p (pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s (jst ≫ g)) ξ) := by
    intro Z' a b hab p h1 h2 ξ
    rw [pointsHomeomorphScheme_pointsMap]
    congr 1
    obtain rfl : (BigFppfOver.toScheme B S hS).map
        (siteMap B S hS (atlasFactorMap B S hS f ρ s θ (jst ≫ g) a b hab)) = p := by
      refine pullback.hom_ext (Eq.trans ?_ h1.symm) (Eq.trans ?_ h2.symm)
      · exact (Functor.map_comp ..).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map
          (siteMap_atlasFactorMap_comp_sitePullbackFst B S hS f ρ s θ (jst ≫ g) a b hab))
      · exact (Functor.map_comp ..).symm.trans (congrArg (BigFppfOver.toScheme B S hS).map
          (siteMap_atlasFactorMap_comp_sitePullbackSnd B S hS f ρ s θ (jst ≫ g) a b hab))
    rfl
  -- The left-hand square of the diagram, on points.
  have hleft : ∀ ξ, AlgebraicStacks.pointsMap B S hS (factorMap B S hS f (jst ≫ g) jst g rfl)
        (AlgebraicStacks.pointsMap B S hS
          (atlasInnerSquare B S hS f ρ s θ (jst ≫ g)).fst ξ) =
      AlgebraicStacks.pointsMap B S hS (atlasInnerSquare B S hS f ρ s θ g).fst
        (AlgebraicStacks.pointsMap B S hS
          (atlasFactorMap B S hS f ρ s θ (jst ≫ g) jst g rfl) ξ) := by
    intro ξ
    have h1 := congrFun (AlgebraicStacks.pointsMap_comp B S hS
      (atlasInnerSquare B S hS f ρ s θ (jst ≫ g)).fst
      (factorMap B S hS f (jst ≫ g) jst g rfl)) ξ
    have h2 := congrFun (AlgebraicStacks.pointsMap_comp B S hS
      (atlasFactorMap B S hS f ρ s θ (jst ≫ g) jst g rfl)
      (atlasInnerSquare B S hS f ρ s θ g).fst) ξ
    have h3 := congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
      (atlasFactorSquare B S hS f ρ s θ (jst ≫ g) jst g rfl).iso.hom) ξ
    exact h1.symm.trans (h3.trans h2)
  -- The descent step, along the right-hand square.
  have hdesc := AlgebraicStacks.image_closure_image_subset_of_isTwoFibreProduct B S hS
    (baseChangeSquare B S hS f bst).fst
    (atlasFactorSquare B S hS f ρ s θ (jst ≫ g) ast bst hjg)
    (isTwoFibreProduct_atlasFactorSquare B S hS f ρ s θ (jst ≫ g) ast bst hjg) (hsu bst)
    (AlgebraicStacks.isOpenMap_pointsMap_of_isSmooth B S hS _ (hsm bst))
    (AlgebraicStacks.pointsMap B S hS (factorMap B S hS f (jst ≫ g) jst g rfl) ⁻¹' T)
    (pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s bst) ⁻¹' E')
    (hE'.preimage (pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s bst)).continuous)
    (by
      rintro _ ⟨ξ, hξ, rfl⟩
      have hpξ : psch (pointsHomeomorphScheme B S hS
          (sitePullbackObj B S hS s (jst ≫ g)) ξ) ∈ SE := by
        change AlgebraicStacks.pointsMap B S hS (atlasInnerSquare B S hS f ρ s θ g).fst
          ((pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s g)).symm
            (psch (pointsHomeomorphScheme B S hS
              (sitePullbackObj B S hS s (jst ≫ g)) ξ))) ∈ T
        have hξ' : AlgebraicStacks.pointsMap B S hS
            (factorMap B S hS f (jst ≫ g) jst g rfl)
            (AlgebraicStacks.pointsMap B S hS
              (atlasInnerSquare B S hS f ρ s θ (jst ≫ g)).fst ξ) ∈ T := hξ
        erw [← hpt jst g rfl psch hp1 hp2 ξ, (pointsHomeomorphScheme B S hS
          (sitePullbackObj B S hS s g)).symm_apply_apply]
        exact (congrArg (fun y => y ∈ T) (hleft ξ)).mp hξ'
      have hq := hsubE hpξ
      change pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s bst)
        (AlgebraicStacks.pointsMap B S hS
          (atlasFactorMap B S hS f ρ s θ (jst ≫ g) ast bst hjg) ξ) ∈ E'
      erw [hpt ast bst hjg qsch hq1 hq2]
      exact hq)
  refine ⟨Vst, jst, hjopen, v, hv, Z'st, bst, hZ'aff,
    ⟨hbsch, (inferInstance : QuasiCompact bsch), (inferInstance : QuasiSeparated bsch)⟩,
    ast, hjg,
    @closure _ (pointTopology B S hS (baseChangeSquare B S hS f bst).pt.val)
      (AlgebraicStacks.pointsMap B S hS (factorMap B S hS f (jst ≫ g) ast bst hjg) ''
        (AlgebraicStacks.pointsMap B S hS
          (factorMap B S hS f (jst ≫ g) jst g rfl) ⁻¹' T)),
    @isClosed_closure _ (pointTopology B S hS (baseChangeSquare B S hS f bst).pt.val) _, ?_,
    @subset_closure _ (pointTopology B S hS (baseChangeSquare B S hS f bst).pt.val) _⟩
  rintro hmem
  obtain ⟨ξ, hξ, hξeq⟩ := hdesc hmem
  have h2 := congrFun (AlgebraicStacks.pointsMap_comp B S hS
    (atlasInnerSquare B S hS f ρ s θ bst).fst (baseChangeSquare B S hS f bst).fst) ξ
  have hB : AlgebraicStacks.pointsMap B S hS (baseChangeSquare B S hS f bst).fst
        (AlgebraicStacks.pointsMap B S hS (atlasInnerSquare B S hS f ρ s θ bst).fst ξ) =
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS ast) v :=
    h2.symm.trans hξeq
  refine hnot' ⟨pointsHomeomorphScheme B S hS (sitePullbackObj B S hS s bst) ξ, hξ, ?_⟩
  refine (key bst ξ).symm.trans ?_
  rw [hB, pointsHomeomorphScheme_pointsMap B S hS
    (schemeStackMap.{u, w} B S hS ast) v, siteMap_schemeStackMap, hvh]
  rfl

end AlgebraicGeometry.Stack

end
