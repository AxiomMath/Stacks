module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Limits of algebraic spaces with a flat finitely presented space over one stage

A directed inverse system of quasi-compact, quasi-separated algebraic spaces with affine
transition morphisms, a flat morphism of finite presentation over one chosen stage, and all of
its base changes to the later stages and to the limit.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation`: the inverse system together with the
  chosen flat finitely presented space over one stage and all of its base changes.

## References

* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- A directed inverse system of quasi-compact, quasi-separated algebraic spaces with affine
transition morphisms, together with its limit, a flat algebraic space of finite presentation
over one chosen stage, and the base changes of that space to every later stage and to the
limit. -/
@[stacks 0DKU]
structure RelativeDescentSituation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type v) [Preorder I]
    [IsDirected I (· ≤ ·)] where
  /-- The inverse system of algebraic spaces. -/
  Y : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- Its cone, whose vertex is the limit space. -/
  limitCone : Cone Y
  /-- The cone is limiting. -/
  isLimit : IsLimit limitCone
  /-- Each stage is an algebraic space. -/
  stage_isAlgebraicSpace : ∀ i, IsAlgebraicSpace B S hS (Y.obj (Opposite.op i))
  /-- The limit is an algebraic space. -/
  limit_isAlgebraicSpace : IsAlgebraicSpace B S hS limitCone.pt
  /-- Each stage is quasi-compact. -/
  stage_isQuasiCompact : ∀ i, IsQuasiCompactSpace B S hS (Y.obj (Opposite.op i))
  /-- Each stage is quasi-separated. -/
  stage_isQuasiSeparated : ∀ i,
    IsAbsolutelyQuasiSeparated B S hS hZ (Y.obj (Opposite.op i))
  /-- Every transition morphism is affine. -/
  transition_isAffine : ∀ (i j : I) (hij : i ≤ j),
    IsAffineHom B S hS (Y.map (homOfLE hij).op)
  /-- The chosen initial stage. -/
  i₀ : I
  /-- The space over the chosen stage. -/
  X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Its structure morphism. -/
  p₀ : X₀ ⟶ Y.obj (Opposite.op i₀)
  /-- The source is an algebraic space. -/
  initial_isAlgebraicSpace : IsAlgebraicSpace B S hS X₀
  /-- The structure morphism is flat. -/
  initial_isFlat : IsFlat B S hS p₀
  /-- The structure morphism is of finite presentation. -/
  initial_isFinitePresentation : IsFinitePresentation B S hS p₀
  /-- The base change at each later stage. -/
  Xᵢ : ∀ i : I, i₀ ≤ i → ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- Each base change is an algebraic space. -/
  stageX_isAlgebraicSpace : ∀ (i : I) (hi : i₀ ≤ i), IsAlgebraicSpace B S hS (Xᵢ i hi)
  /-- Its projection to the initial space. -/
  toX₀ : ∀ (i : I) (hi : i₀ ≤ i), Xᵢ i hi ⟶ X₀
  /-- Its projection to the current base. -/
  toYᵢ : ∀ (i : I) (hi : i₀ ≤ i), Xᵢ i hi ⟶ Y.obj (Opposite.op i)
  /-- Each stage is the prescribed base change. -/
  stage_isPullback : ∀ (i : I) (hi : i₀ ≤ i),
    IsPullback (toYᵢ i hi) (toX₀ i hi) (Y.map (homOfLE hi).op) p₀
  /-- Transition maps between the base changes. -/
  fᵢⱼ : ∀ (i j : I) (hi : i₀ ≤ i) (hj : i₀ ≤ j) (_hij : i ≤ j), Xᵢ j hj ⟶ Xᵢ i hi
  /-- A transition map lies over the corresponding base transition. -/
  fᵢⱼ_toYᵢ : ∀ (i j : I) (hi : i₀ ≤ i) (hj : i₀ ≤ j) (hij : i ≤ j),
    fᵢⱼ i j hi hj hij ≫ toYᵢ i hi = toYᵢ j hj ≫ Y.map (homOfLE hij).op
  /-- A transition map preserves the projection to the initial space. -/
  fᵢⱼ_toX₀ : ∀ (i j : I) (hi : i₀ ≤ i) (hj : i₀ ≤ j) (hij : i ≤ j),
    fᵢⱼ i j hi hj hij ≫ toX₀ i hi = toX₀ j hj
  /-- The base change at the limit. -/
  X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The limit base change is an algebraic space. -/
  X_isAlgebraicSpace : IsAlgebraicSpace B S hS X
  /-- Its projection to the initial space. -/
  toInitial : X ⟶ X₀
  /-- Its projection to the limit base. -/
  toLimit : X ⟶ limitCone.pt
  /-- The limit-stage square is cartesian. -/
  limit_isPullback :
    IsPullback toLimit toInitial (limitCone.π.app (Opposite.op i₀)) p₀
  /-- Projection of the limit-stage base change to each later base change. -/
  fᵢ : ∀ (i : I) (hi : i₀ ≤ i), X ⟶ Xᵢ i hi
  /-- The projection is over the corresponding projection of the base limit. -/
  fᵢ_toYᵢ : ∀ (i : I) (hi : i₀ ≤ i),
    fᵢ i hi ≫ toYᵢ i hi = toLimit ≫ limitCone.π.app (Opposite.op i)
  /-- The projection preserves the map to the initial space. -/
  fᵢ_toX₀ : ∀ (i : I) (hi : i₀ ≤ i), fᵢ i hi ≫ toX₀ i hi = toInitial

end AlgebraicGeometry.Space

end
