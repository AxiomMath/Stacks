module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality

/-!
# The pullbacks of a module to the stages and to the limit of a morphism descent system

In the situation of Stacks 084W, carried by
`AlgebraicGeometry.Space.MorphismDescentSituation`, a module `F₀` on the distinguished source `X₀`
has pullbacks `F_i` to each stage `X_i` and `F` to the limit `X`, along the projections of the
two fibre products `X_i = B_i ×_{B₀} X₀` and `X = B ×_{B₀} X₀`. These are the modules appearing
in Stacks 08K2, and this file names them and computes their supports.

The support computation is part (3) of Stacks 07TZ,
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`: for `F₀` quasi-coherent of finite
type the support of a pullback is the inverse image of the support. In particular each of those
supports is closed, which part (3) gives with no quasi-coherence hypothesis through
`AlgebraicGeometry.Space.isClosed_supportOfSheaf_modulePullback`.

## Main definitions

* `AlgebraicGeometry.Space.MorphismDescentSituation.sourceAtToSource₀` and
  `AlgebraicGeometry.Space.MorphismDescentSituation.sourceLimitToSource₀`: the projections
  `X_i ⟶ X₀` and `X ⟶ X₀`, as morphisms in the category of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.MorphismDescentSituation.moduleAt` and
  `AlgebraicGeometry.Space.MorphismDescentSituation.moduleLimit`: the pullbacks `F_i` and `F` of a
  module on `X₀`.

## Main results

* `AlgebraicGeometry.Space.MorphismDescentSituation.supportOfSheaf_moduleAt` and
  `AlgebraicGeometry.Space.MorphismDescentSituation.supportOfSheaf_moduleLimit`: each support is
  the inverse image of the support of `F₀` under the projection.
* `AlgebraicGeometry.Space.MorphismDescentSituation.isClosed_supportOfSheaf_moduleAt` and
  `AlgebraicGeometry.Space.MorphismDescentSituation.isClosed_supportOfSheaf_moduleLimit`: each
  support is closed.

## Implementation notes

The pullback functor `AlgebraicGeometry.Space.modulePullback` is indexed by a morphism in the
category `AlgebraicGeometry.AlgebraicSpaces` rather than by a morphism of presheaves together
with algebraicity hypotheses, so the projections are packaged as morphisms there, by
`CategoryTheory.ObjectProperty.homMk` on top of the already available
`AlgebraicGeometry.Space.MorphismDescentSituation.sourceAt_isAlgebraicSpace` and
`AlgebraicGeometry.Space.MorphismDescentSituation.sourceLimit_isAlgebraicSpace`. The support
statements are nonetheless phrased with the bare presheaf projection
`CategoryTheory.Limits.pullback.snd`, which is what the packaged morphism is underneath, so that
they can be used without unfolding the packaging.

## References

* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.MorphismDescentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

/-- The distinguished source `X₀`, as an object of the category of algebraic spaces over `S`. -/
def source₀Space : AlgebraicSpaces B S hS := ⟨D.source₀, D.source₀_isAlgebraicSpace⟩

/-- The source `X_i` at a stage, as an object of the category of algebraic spaces over `S`. -/
def sourceAtSpace (i : I) (hi : D.initial ≤ i) : AlgebraicSpaces B S hS :=
  ⟨D.sourceAt i hi, D.sourceAt_isAlgebraicSpace i hi⟩

/-- The source `X` at the limit, as an object of the category of algebraic spaces over `S`. -/
def sourceLimitSpace : AlgebraicSpaces B S hS :=
  ⟨D.sourceLimit, D.sourceLimit_isAlgebraicSpace⟩

/-- The projection `X_i ⟶ X₀`. -/
def sourceAtToSource₀ (i : I) (hi : D.initial ≤ i) :
    D.sourceAtSpace i hi ⟶ D.source₀Space :=
  ObjectProperty.homMk (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase)

/-- The projection `X ⟶ X₀`. -/
def sourceLimitToSource₀ : D.sourceLimitSpace ⟶ D.source₀Space :=
  ObjectProperty.homMk (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase)

/-- The underlying morphism of `sourceAtToSource₀ i hi` is the second pullback projection
`X_i = B_i ×_{B₀} X₀ ⟶ X₀`. -/
@[simp] theorem sourceAtToSource₀_hom (i : I) (hi : D.initial ≤ i) :
    (D.sourceAtToSource₀ i hi).hom =
      pullback.snd (D.baseAtToInitial i hi) D.sourceToBase := rfl

/-- The underlying morphism of `sourceLimitToSource₀` is the second pullback projection
`X = B ×_{B₀} X₀ ⟶ X₀`. -/
@[simp] theorem sourceLimitToSource₀_hom :
    D.sourceLimitToSource₀.hom =
      pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase := rfl

variable (F₀ : Modules.{u, u} B S hS D.source₀Space.1 D.source₀Space.2)

/-- `F_i`, the pullback of a module on `X₀` to the stage `X_i`. -/
def moduleAt (i : I) (hi : D.initial ≤ i) :
    Modules.{u, u} B S hS (D.sourceAtSpace i hi).1 (D.sourceAtSpace i hi).2 :=
  (modulePullback B S hS (D.sourceAtToSource₀ i hi)).obj F₀

/-- `F`, the pullback of a module on `X₀` to the limit `X`. -/
def moduleLimit : Modules.{u, u} B S hS D.sourceLimitSpace.1 D.sourceLimitSpace.2 :=
  (modulePullback B S hS D.sourceLimitToSource₀).obj F₀

/-- **Stacks 07TZ part (3) at a stage.** The support of `F_i` is the inverse image of the
support of `F₀` under the projection `X_i ⟶ X₀`. -/
theorem supportOfSheaf_moduleAt (hqc : F₀.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) (i : I) (hi : D.initial ≤ i) :
    supportOfSheaf B S hS (D.sourceAt i hi)
        ((SheafOfModules.toSheaf _).obj (D.moduleAt F₀ i hi)) =
      pointsMap B S hS (D.sourceAt i hi)
          (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase) ⁻¹'
        supportOfSheaf B S hS D.source₀ ((SheafOfModules.toSheaf _).obj F₀) :=
  supportOfSheaf_modulePullback_eq B S hS (D.sourceAtToSource₀ i hi) F₀ hqc hft

/-- **Stacks 07TZ part (3) at the limit.** The support of `F` is the inverse image of the
support of `F₀` under the projection `X ⟶ X₀`. -/
theorem supportOfSheaf_moduleLimit (hqc : F₀.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    supportOfSheaf B S hS D.sourceLimit
        ((SheafOfModules.toSheaf _).obj (D.moduleLimit F₀)) =
      pointsMap B S hS D.sourceLimit
          (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase) ⁻¹'
        supportOfSheaf B S hS D.source₀ ((SheafOfModules.toSheaf _).obj F₀) :=
  supportOfSheaf_modulePullback_eq B S hS D.sourceLimitToSource₀ F₀ hqc hft

/-- The support of `F_i` is closed. -/
theorem isClosed_supportOfSheaf_moduleAt
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) (i : I) (hi : D.initial ≤ i) :
    _root_.IsClosed (supportOfSheaf B S hS (D.sourceAt i hi)
      ((SheafOfModules.toSheaf _).obj (D.moduleAt F₀ i hi))) :=
  isClosed_supportOfSheaf_modulePullback B S hS (D.sourceAtToSource₀ i hi) F₀ hft

/-- The support of `F` is closed. -/
theorem isClosed_supportOfSheaf_moduleLimit
    (hft : SheafOfModules.IsFiniteTypeOnSite F₀) :
    _root_.IsClosed (supportOfSheaf B S hS D.sourceLimit
      ((SheafOfModules.toSheaf _).obj (D.moduleLimit F₀))) :=
  isClosed_supportOfSheaf_modulePullback B S hS D.sourceLimitToSource₀ F₀ hft

end AlgebraicGeometry.Space.MorphismDescentSituation

end
