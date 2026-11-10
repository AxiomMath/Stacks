module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Descending properties of morphisms along a limit of algebraic spaces

A morphism descent system over a scheme `S` consists of a directed inverse system `(B_i)` of
algebraic spaces over `S` with affine transition morphisms, whose limit `B = lim_i B_i` is again
an algebraic space, together with a distinguished index `0 ∈ I` and a morphism
`f₀ : X₀ ⟶ Y₀` of algebraic spaces over `B₀`, all three of `B₀`, `X₀` and `Y₀` being
quasi-compact and quasi-separated. It is the standing setup for transferring a property of the
base change `f : X ⟶ Y` of `f₀` to `B` back to the base change `f_i : X_i ⟶ Y_i` of `f₀` to some
finite stage `B_i`, and conversely.

The base changes themselves are constructed here, as fibre products of presheaves, and shown to
be algebraic spaces sitting in cartesian squares.

## Main definitions

* `AlgebraicGeometry.Space.MorphismDescentSystem` bundles the inverse system, its distinguished
  stage, and the morphism to be descended.
* `AlgebraicGeometry.Space.MorphismDescentSystem.baseAtToInitial` is the transition morphism
  `B_i ⟶ B₀` for a stage `i ≥ 0`.
* `AlgebraicGeometry.Space.MorphismDescentSystem.sourceAt`,
  `AlgebraicGeometry.Space.MorphismDescentSystem.targetAt` and
  `AlgebraicGeometry.Space.MorphismDescentSystem.mapAt` are `X_i`, `Y_i` and `f_i`, the base
  change of `f₀ : X₀ ⟶ Y₀` to a stage `i ≥ 0`.
* `AlgebraicGeometry.Space.MorphismDescentSystem.sourceLimit`,
  `AlgebraicGeometry.Space.MorphismDescentSystem.targetLimit` and
  `AlgebraicGeometry.Space.MorphismDescentSystem.mapLimit` are `X`, `Y` and `f`, the base change
  of `f₀ : X₀ ⟶ Y₀` to the limit `B`.

* `AlgebraicGeometry.Space.MorphismDescentSituation` is the same situation with no condition on
  the size of the index, as Stacks 084W states it, with the same base changes; and
  `AlgebraicGeometry.Space.MorphismDescentSystem.toSituation` forgets the bound on the index.

## Main results

* `AlgebraicGeometry.Space.MorphismDescentSystem.sourceAt_isPullback`,
  `AlgebraicGeometry.Space.MorphismDescentSystem.targetAt_isPullback`,
  `AlgebraicGeometry.Space.MorphismDescentSystem.sourceLimit_isPullback` and
  `AlgebraicGeometry.Space.MorphismDescentSystem.targetLimit_isPullback`: each base change sits
  in a cartesian square over the transition morphism it was formed along.
* `AlgebraicGeometry.Space.MorphismDescentSystem.mapAt_fst`,
  `AlgebraicGeometry.Space.MorphismDescentSystem.mapAt_snd`,
  `AlgebraicGeometry.Space.MorphismDescentSystem.mapLimit_fst` and
  `AlgebraicGeometry.Space.MorphismDescentSystem.mapLimit_snd`: a base-changed morphism is the
  identity on the base coordinate and `f₀` on the other.
* `AlgebraicGeometry.Space.MorphismDescentSystem.sourceAt_isAlgebraicSpace`,
  `AlgebraicGeometry.Space.MorphismDescentSystem.targetAt_isAlgebraicSpace`,
  `AlgebraicGeometry.Space.MorphismDescentSystem.sourceLimit_isAlgebraicSpace` and
  `AlgebraicGeometry.Space.MorphismDescentSystem.targetLimit_isAlgebraicSpace`: every base
  change is an algebraic space over `S`.
* `AlgebraicGeometry.Space.isSurjective_baseChange_diagonal_iff` and
  `AlgebraicGeometry.Space.isIso_baseChange_diagonal_iff`: formation of the relative diagonal
  commutes with base change, read off surjectivity and off invertibility.

## Implementation notes

Algebraic spaces over `S` are presheaves on the big fppf site over `S`, so the inverse system is
a functor out of the opposite `Iᵒᵖ` of the indexing preorder and the transition morphism
`B_{i'} ⟶ B_i` for `i ≤ i'` is the image of the corresponding morphism of `Iᵒᵖ`. The limit is
the canonical limit of the presheaf category; that it is an algebraic space is Stacks 07SF, and
it is part of the data rather than derived here.

The index type is required to be small compared to the cofinality of the site's size cutoff.
That is the explicit form of the all-rings-in-the-site convention under which Stacks 07SF holds:
it is what keeps the limits of the affine charts of the system inside the site.

`AlgebraicGeometry.Space.MorphismDescentSituation` records the situation with no such condition,
as Situation 70.6.1 states it. Its base changes are built exactly as those of a morphism descent
system, so that `AlgebraicGeometry.Space.MorphismDescentSystem.toSituation` identifies the two by
`rfl`. What a descent result over a situation needs of the index is an explicit hypothesis of
that result: typically `AlgebraicGeometry.Space.IsSiteSmall` of the inverse system.

The distinguished stage need not be an initial element of the index, so each of the
stagewise base changes takes the comparison `initial ≤ i` as a hypothesis. Fibre products are
the canonical ones of the presheaf category and the base-changed morphisms are the universal
maps into them, which is why the two component equations are exactly the defining equations of
`CategoryTheory.Limits.pullback.lift`.

Quasi-separatedness is the absolute notion of Stacks 03BS, part (3), so the containment `hZ` of
the terminal scheme in the site is a parameter.

## References

* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 084W.** The standing situation for descending a property of a
morphism of algebraic spaces along a directed limit: a directed inverse system of algebraic
spaces over `S` with affine transition morphisms and algebraic limit, a distinguished stage of
the system, and a morphism of quasi-compact quasi-separated algebraic spaces over that
stage. -/
@[stacks 084W]
structure MorphismDescentSystem (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] where
  /-- The inverse system `(B_i)` of presheaves on the big fppf site over `S`. -/
  base : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- The index type is small compared to the cofinality of the site's size cutoff, so that the
  limits of the affine charts of the system remain in the site. -/
  indexSize : Cardinal.mk I < B.cutoff.ord.cof
  /-- Every member of the system is an algebraic space over `S`. -/
  base_isAlgebraicSpace : ∀ i : I, IsAlgebraicSpace B S hS (base.obj (op i))
  /-- Every transition morphism of the system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (base.map a)
  /-- The limit `B` of the system is an algebraic space over `S`. -/
  limit_isAlgebraicSpace : IsAlgebraicSpace B S hS (limit base)
  /-- The distinguished stage `0 ∈ I`, over which the morphism to be descended is given. -/
  initial : I
  /-- The source `X₀` of the given morphism. -/
  source₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The target `Y₀` of the given morphism. -/
  target₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The structure morphism `X₀ ⟶ B₀` exhibiting the source over the distinguished stage. -/
  sourceToBase : source₀ ⟶ base.obj (op initial)
  /-- The structure morphism `Y₀ ⟶ B₀` exhibiting the target over the distinguished stage. -/
  targetToBase : target₀ ⟶ base.obj (op initial)
  /-- The morphism `f₀ : X₀ ⟶ Y₀` to be descended. -/
  map₀ : source₀ ⟶ target₀
  /-- The given morphism is a morphism over the distinguished stage. -/
  map₀_over : map₀ ≫ targetToBase = sourceToBase
  /-- The source `X₀` is an algebraic space over `S`. -/
  source₀_isAlgebraicSpace : IsAlgebraicSpace B S hS source₀
  /-- The target `Y₀` is an algebraic space over `S`. -/
  target₀_isAlgebraicSpace : IsAlgebraicSpace B S hS target₀
  /-- The distinguished stage `B₀` is quasi-compact. -/
  base₀_quasiCompact : IsQuasiCompactSpace B S hS (base.obj (op initial))
  /-- The distinguished stage `B₀` is quasi-separated. -/
  base₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ (base.obj (op initial))
  /-- The source `X₀` is quasi-compact. -/
  source₀_quasiCompact : IsQuasiCompactSpace B S hS source₀
  /-- The source `X₀` is quasi-separated. -/
  source₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ source₀
  /-- The target `Y₀` is quasi-compact. -/
  target₀_quasiCompact : IsQuasiCompactSpace B S hS target₀
  /-- The target `Y₀` is quasi-separated. -/
  target₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ target₀

namespace MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

/-- The transition morphism `B_i ⟶ B₀` from a stage `i` at or beyond the distinguished stage
to the distinguished stage. -/
def baseAtToInitial (i : I) (hi : D.initial ≤ i) :
    D.base.obj (op i) ⟶ D.base.obj (op D.initial) :=
  D.base.map (homOfLE hi).op

/-- The source `X_i = B_i ×_{B₀} X₀` of the base change of `f₀` to a stage `i ≥ 0`. -/
noncomputable def sourceAt (i : I) (hi : D.initial ≤ i) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (D.baseAtToInitial i hi) D.sourceToBase

/-- The target `Y_i = B_i ×_{B₀} Y₀` of the base change of `f₀` to a stage `i ≥ 0`. -/
noncomputable def targetAt (i : I) (hi : D.initial ≤ i) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (D.baseAtToInitial i hi) D.targetToBase

/-- The base change `f_i : X_i ⟶ Y_i` of `f₀` to a stage `i ≥ 0`. -/
noncomputable def mapAt (i : I) (hi : D.initial ≤ i) : D.sourceAt i hi ⟶ D.targetAt i hi :=
  pullback.lift
    (pullback.fst (D.baseAtToInitial i hi) D.sourceToBase)
    (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀)
    (by
      calc
        pullback.fst (D.baseAtToInitial i hi) D.sourceToBase ≫ D.baseAtToInitial i hi =
            pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.sourceToBase :=
          pullback.condition
        _ = pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫
            (D.map₀ ≫ D.targetToBase) := by rw [D.map₀_over]
        _ = (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀) ≫
            D.targetToBase := (Category.assoc _ _ _).symm)

/-- The source `X = B ×_{B₀} X₀` of the base change of `f₀` to the limit `B`. -/
noncomputable def sourceLimit : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (limit.π D.base (op D.initial)) D.sourceToBase

/-- The target `Y = B ×_{B₀} Y₀` of the base change of `f₀` to the limit `B`. -/
noncomputable def targetLimit : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (limit.π D.base (op D.initial)) D.targetToBase

/-- The base change `f : X ⟶ Y` of `f₀` to the limit `B`. -/
noncomputable def mapLimit : D.sourceLimit ⟶ D.targetLimit :=
  pullback.lift
    (pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase)
    (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase ≫ D.map₀)
    (by dsimp [sourceLimit, targetLimit]; simp [Category.assoc, D.map₀_over, pullback.condition])

/-- The square exhibiting `X_i` as the fibre product of `B_i` and `X₀` over `B₀` is
cartesian. -/
theorem sourceAt_isPullback (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.fst (D.baseAtToInitial i hi) D.sourceToBase)
      (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase)
      (D.baseAtToInitial i hi) D.sourceToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `Y_i` as the fibre product of `B_i` and `Y₀` over `B₀` is
cartesian. -/
theorem targetAt_isPullback (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.fst (D.baseAtToInitial i hi) D.targetToBase)
      (pullback.snd (D.baseAtToInitial i hi) D.targetToBase)
      (D.baseAtToInitial i hi) D.targetToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `X` as the fibre product of `B` and `X₀` over `B₀` is cartesian. -/
theorem sourceLimit_isPullback :
    IsPullback (pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase)
      (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase)
      (limit.π D.base (op D.initial)) D.sourceToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `Y` as the fibre product of `B` and `Y₀` over `B₀` is cartesian. -/
theorem targetLimit_isPullback :
    IsPullback (pullback.fst (limit.π D.base (op D.initial)) D.targetToBase)
      (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase)
      (limit.π D.base (op D.initial)) D.targetToBase := IsPullback.of_hasPullback _ _

/-- The base change `f_i` of `f₀` to a stage is the identity on the base coordinate. -/
@[simp] theorem mapAt_fst (i : I) (hi : D.initial ≤ i) :
    D.mapAt i hi ≫ pullback.fst (D.baseAtToInitial i hi) D.targetToBase =
      pullback.fst (D.baseAtToInitial i hi) D.sourceToBase := pullback.lift_fst _ _ _

/-- The base change `f_i` of `f₀` to a stage is `f₀` on the other coordinate. -/
@[simp] theorem mapAt_snd (i : I) (hi : D.initial ≤ i) :
    D.mapAt i hi ≫ pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀ := pullback.lift_snd _ _ _

/-- The base change `f` of `f₀` to the limit is the identity on the base coordinate. -/
@[simp] theorem mapLimit_fst :
    D.mapLimit ≫ pullback.fst (limit.π D.base (op D.initial)) D.targetToBase =
      pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase :=
  pullback.lift_fst _ _ _

/-- The base change `f` of `f₀` to the limit is `f₀` on the other coordinate. -/
@[simp] theorem mapLimit_snd :
    D.mapLimit ≫ pullback.snd (limit.π D.base (op D.initial)) D.targetToBase =
      pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase ≫ D.map₀ :=
  pullback.lift_snd _ _ _

/-- The source `X_i` of the base change of `f₀` to a stage is an algebraic space over `S`. -/
theorem sourceAt_isAlgebraicSpace (i : I) (hi : D.initial ≤ i) :
    IsAlgebraicSpace B S hS (D.sourceAt i hi) :=
  isAlgebraicSpace_pullback B S hS _ _
    (D.base_isAlgebraicSpace i) D.source₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The target `Y_i` of the base change of `f₀` to a stage is an algebraic space over `S`. -/
theorem targetAt_isAlgebraicSpace (i : I) (hi : D.initial ≤ i) :
    IsAlgebraicSpace B S hS (D.targetAt i hi) :=
  isAlgebraicSpace_pullback B S hS _ _
    (D.base_isAlgebraicSpace i) D.target₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The source `X` of the base change of `f₀` to the limit is an algebraic space over `S`. -/
theorem sourceLimit_isAlgebraicSpace : IsAlgebraicSpace B S hS D.sourceLimit :=
  isAlgebraicSpace_pullback B S hS _ _
    D.limit_isAlgebraicSpace D.source₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The target `Y` of the base change of `f₀` to the limit is an algebraic space over `S`. -/
theorem targetLimit_isAlgebraicSpace : IsAlgebraicSpace B S hS D.targetLimit :=
  isAlgebraicSpace_pullback B S hS _ _
    D.limit_isAlgebraicSpace D.target₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

end MorphismDescentSystem

/-- **The situation of Stacks 084W**: a directed inverse system of algebraic spaces over `S`
with affine transition morphisms and algebraic limit, a distinguished stage of the system, and a
morphism of quasi-compact quasi-separated algebraic spaces over that stage. No condition is
imposed on the size of the index. -/
structure MorphismDescentSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] where
  /-- The inverse system `(B_i)` of presheaves on the big fppf site over `S`. -/
  base : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- Every member of the system is an algebraic space over `S`. -/
  base_isAlgebraicSpace : ∀ i : I, IsAlgebraicSpace B S hS (base.obj (op i))
  /-- Every transition morphism of the system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (base.map a)
  /-- The limit `B` of the system is an algebraic space over `S`. -/
  limit_isAlgebraicSpace : IsAlgebraicSpace B S hS (limit base)
  /-- The distinguished stage `0 ∈ I`, over which the morphism to be descended is given. -/
  initial : I
  /-- The source `X₀` of the given morphism. -/
  source₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The target `Y₀` of the given morphism. -/
  target₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The structure morphism `X₀ ⟶ B₀` exhibiting the source over the distinguished stage. -/
  sourceToBase : source₀ ⟶ base.obj (op initial)
  /-- The structure morphism `Y₀ ⟶ B₀` exhibiting the target over the distinguished stage. -/
  targetToBase : target₀ ⟶ base.obj (op initial)
  /-- The morphism `f₀ : X₀ ⟶ Y₀` to be descended. -/
  map₀ : source₀ ⟶ target₀
  /-- The given morphism is a morphism over the distinguished stage. -/
  map₀_over : map₀ ≫ targetToBase = sourceToBase
  /-- The source `X₀` is an algebraic space over `S`. -/
  source₀_isAlgebraicSpace : IsAlgebraicSpace B S hS source₀
  /-- The target `Y₀` is an algebraic space over `S`. -/
  target₀_isAlgebraicSpace : IsAlgebraicSpace B S hS target₀
  /-- The distinguished stage `B₀` is quasi-compact. -/
  base₀_quasiCompact : IsQuasiCompactSpace B S hS (base.obj (op initial))
  /-- The distinguished stage `B₀` is quasi-separated. -/
  base₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ (base.obj (op initial))
  /-- The source `X₀` is quasi-compact. -/
  source₀_quasiCompact : IsQuasiCompactSpace B S hS source₀
  /-- The source `X₀` is quasi-separated. -/
  source₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ source₀
  /-- The target `Y₀` is quasi-compact. -/
  target₀_quasiCompact : IsQuasiCompactSpace B S hS target₀
  /-- The target `Y₀` is quasi-separated. -/
  target₀_quasiSeparated : IsAbsolutelyQuasiSeparated B S hS hZ target₀

namespace MorphismDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

/-- The transition morphism `B_i ⟶ B₀` from a stage `i` at or beyond the distinguished stage
to the distinguished stage. -/
def baseAtToInitial (i : I) (hi : D.initial ≤ i) :
    D.base.obj (op i) ⟶ D.base.obj (op D.initial) :=
  D.base.map (homOfLE hi).op

/-- The source `X_i = B_i ×_{B₀} X₀` of the base change of `f₀` to a stage `i ≥ 0`. -/
noncomputable def sourceAt (i : I) (hi : D.initial ≤ i) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (D.baseAtToInitial i hi) D.sourceToBase

/-- The target `Y_i = B_i ×_{B₀} Y₀` of the base change of `f₀` to a stage `i ≥ 0`. -/
noncomputable def targetAt (i : I) (hi : D.initial ≤ i) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (D.baseAtToInitial i hi) D.targetToBase

/-- The base change `f_i : X_i ⟶ Y_i` of `f₀` to a stage `i ≥ 0`. -/
noncomputable def mapAt (i : I) (hi : D.initial ≤ i) : D.sourceAt i hi ⟶ D.targetAt i hi :=
  pullback.lift
    (pullback.fst (D.baseAtToInitial i hi) D.sourceToBase)
    (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀)
    (by
      calc
        pullback.fst (D.baseAtToInitial i hi) D.sourceToBase ≫ D.baseAtToInitial i hi =
            pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.sourceToBase :=
          pullback.condition
        _ = pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫
            (D.map₀ ≫ D.targetToBase) := by rw [D.map₀_over]
        _ = (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀) ≫
            D.targetToBase := (Category.assoc _ _ _).symm)

/-- The source `X = B ×_{B₀} X₀` of the base change of `f₀` to the limit `B`. -/
noncomputable def sourceLimit : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (limit.π D.base (op D.initial)) D.sourceToBase

/-- The target `Y = B ×_{B₀} Y₀` of the base change of `f₀` to the limit `B`. -/
noncomputable def targetLimit : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (limit.π D.base (op D.initial)) D.targetToBase

/-- The base change `f : X ⟶ Y` of `f₀` to the limit `B`. -/
noncomputable def mapLimit : D.sourceLimit ⟶ D.targetLimit :=
  pullback.lift
    (pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase)
    (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase ≫ D.map₀)
    (by dsimp [sourceLimit, targetLimit]; simp [Category.assoc, D.map₀_over, pullback.condition])

/-- The square exhibiting `X_i` as the fibre product of `B_i` and `X₀` over `B₀` is
cartesian. -/
theorem sourceAt_isPullback (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.fst (D.baseAtToInitial i hi) D.sourceToBase)
      (pullback.snd (D.baseAtToInitial i hi) D.sourceToBase)
      (D.baseAtToInitial i hi) D.sourceToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `Y_i` as the fibre product of `B_i` and `Y₀` over `B₀` is
cartesian. -/
theorem targetAt_isPullback (i : I) (hi : D.initial ≤ i) :
    IsPullback (pullback.fst (D.baseAtToInitial i hi) D.targetToBase)
      (pullback.snd (D.baseAtToInitial i hi) D.targetToBase)
      (D.baseAtToInitial i hi) D.targetToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `X` as the fibre product of `B` and `X₀` over `B₀` is cartesian. -/
theorem sourceLimit_isPullback :
    IsPullback (pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase)
      (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase)
      (limit.π D.base (op D.initial)) D.sourceToBase := IsPullback.of_hasPullback _ _

/-- The square exhibiting `Y` as the fibre product of `B` and `Y₀` over `B₀` is cartesian. -/
theorem targetLimit_isPullback :
    IsPullback (pullback.fst (limit.π D.base (op D.initial)) D.targetToBase)
      (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase)
      (limit.π D.base (op D.initial)) D.targetToBase := IsPullback.of_hasPullback _ _

/-- The base change `f_i` of `f₀` to a stage is the identity on the base coordinate. -/
@[simp] theorem mapAt_fst (i : I) (hi : D.initial ≤ i) :
    D.mapAt i hi ≫ pullback.fst (D.baseAtToInitial i hi) D.targetToBase =
      pullback.fst (D.baseAtToInitial i hi) D.sourceToBase := pullback.lift_fst _ _ _

/-- The base change `f_i` of `f₀` to a stage is `f₀` on the other coordinate. -/
@[simp] theorem mapAt_snd (i : I) (hi : D.initial ≤ i) :
    D.mapAt i hi ≫ pullback.snd (D.baseAtToInitial i hi) D.targetToBase =
      pullback.snd (D.baseAtToInitial i hi) D.sourceToBase ≫ D.map₀ := pullback.lift_snd _ _ _

/-- The base change `f` of `f₀` to the limit is the identity on the base coordinate. -/
@[simp] theorem mapLimit_fst :
    D.mapLimit ≫ pullback.fst (limit.π D.base (op D.initial)) D.targetToBase =
      pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase :=
  pullback.lift_fst _ _ _

/-- The base change `f` of `f₀` to the limit is `f₀` on the other coordinate. -/
@[simp] theorem mapLimit_snd :
    D.mapLimit ≫ pullback.snd (limit.π D.base (op D.initial)) D.targetToBase =
      pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase ≫ D.map₀ :=
  pullback.lift_snd _ _ _

/-- The source `X_i` of the base change of `f₀` to a stage is an algebraic space over `S`. -/
theorem sourceAt_isAlgebraicSpace (i : I) (hi : D.initial ≤ i) :
    IsAlgebraicSpace B S hS (D.sourceAt i hi) :=
  isAlgebraicSpace_pullback B S hS _ _
    (D.base_isAlgebraicSpace i) D.source₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The target `Y_i` of the base change of `f₀` to a stage is an algebraic space over `S`. -/
theorem targetAt_isAlgebraicSpace (i : I) (hi : D.initial ≤ i) :
    IsAlgebraicSpace B S hS (D.targetAt i hi) :=
  isAlgebraicSpace_pullback B S hS _ _
    (D.base_isAlgebraicSpace i) D.target₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The source `X` of the base change of `f₀` to the limit is an algebraic space over `S`. -/
theorem sourceLimit_isAlgebraicSpace : IsAlgebraicSpace B S hS D.sourceLimit :=
  isAlgebraicSpace_pullback B S hS _ _
    D.limit_isAlgebraicSpace D.source₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

/-- The target `Y` of the base change of `f₀` to the limit is an algebraic space over `S`. -/
theorem targetLimit_isAlgebraicSpace : IsAlgebraicSpace B S hS D.targetLimit :=
  isAlgebraicSpace_pullback B S hS _ _
    D.limit_isAlgebraicSpace D.target₀_isAlgebraicSpace (D.base_isAlgebraicSpace D.initial)

end MorphismDescentSituation

namespace MorphismDescentSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSystem B S hS hZ I)

/-- The situation of Stacks 084W underlying a morphism descent system: the same data, with the
bound on the index forgotten. -/
def toSituation : MorphismDescentSituation B S hS hZ I where
  base := D.base
  base_isAlgebraicSpace := D.base_isAlgebraicSpace
  transition_affine := D.transition_affine
  limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
  initial := D.initial
  source₀ := D.source₀
  target₀ := D.target₀
  sourceToBase := D.sourceToBase
  targetToBase := D.targetToBase
  map₀ := D.map₀
  map₀_over := D.map₀_over
  source₀_isAlgebraicSpace := D.source₀_isAlgebraicSpace
  target₀_isAlgebraicSpace := D.target₀_isAlgebraicSpace
  base₀_quasiCompact := D.base₀_quasiCompact
  base₀_quasiSeparated := D.base₀_quasiSeparated
  source₀_quasiCompact := D.source₀_quasiCompact
  source₀_quasiSeparated := D.source₀_quasiSeparated
  target₀_quasiCompact := D.target₀_quasiCompact
  target₀_quasiSeparated := D.target₀_quasiSeparated

/-- The inverse system `(B_i)` of the underlying situation is that of the system. -/
@[simp] theorem toSituation_base : D.toSituation.base = D.base := rfl

/-- The initial index of the underlying situation is that of the system. -/
@[simp] theorem toSituation_initial : D.toSituation.initial = D.initial := rfl

/-- The source `X₀` of the underlying situation is that of the system. -/
@[simp] theorem toSituation_source₀ : D.toSituation.source₀ = D.source₀ := rfl

/-- The target `Y₀` of the underlying situation is that of the system. -/
@[simp] theorem toSituation_target₀ : D.toSituation.target₀ = D.target₀ := rfl

/-- The structure morphism `X₀ ⟶ B₀` of the underlying situation is that of the system. -/
@[simp] theorem toSituation_sourceToBase : D.toSituation.sourceToBase = D.sourceToBase := rfl

/-- The structure morphism `Y₀ ⟶ B₀` of the underlying situation is that of the system. -/
@[simp] theorem toSituation_targetToBase : D.toSituation.targetToBase = D.targetToBase := rfl

/-- The morphism `f₀` of the underlying situation is that of the system. -/
@[simp] theorem toSituation_map₀ : D.toSituation.map₀ = D.map₀ := rfl

/-- The base change of `f₀` to a stage is that of the underlying situation. -/
@[simp] theorem toSituation_mapAt (i : I) (hi : D.initial ≤ i) :
    D.toSituation.mapAt i hi = D.mapAt i hi := rfl

/-- The base change of `f₀` to the limit is that of the underlying situation. -/
@[simp] theorem toSituation_mapLimit : D.toSituation.mapLimit = D.mapLimit := rfl

end MorphismDescentSystem

/-- An isomorphism of presheaves is surjective on points. -/
theorem pointsMap_surjective_of_iso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    Function.Surjective (pointsMap B S hS F e.hom) := by
  intro y
  refine ⟨pointsMap B S hS G e.inv y, ?_⟩
  have h := congrFun (pointsMap_comp B S hS G e.inv e.hom) y
  rw [e.inv_hom_id, pointsMap_id] at h
  exact h.symm

/-- Formation of the diagonal commutes with base change: if `F : Z₁ ×_{Z₀} X₀ ⟶ Z₁ ×_{Z₀} Y₀`
is the base change of `f : X₀ ⟶ Y₀` along `t : Z₁ ⟶ Z₀`, then the diagonal of `F` followed by an
isomorphism is the base change along `t` of the diagonal of `f`. -/
theorem exists_isIso_diagonal_comp_eq_baseChange_diagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X₀ Y₀ Z₀ Z₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : X₀ ⟶ Z₀) (b : Y₀ ⟶ Z₀) (t : Z₁ ⟶ Z₀)
    (f : X₀ ⟶ Y₀) (hfb : f ≫ b = a)
    (F : pullback t a ⟶ pullback t b)
    (hFfst : F ≫ pullback.fst t b = pullback.fst t a)
    (hFsnd : F ≫ pullback.snd t b = pullback.snd t a ≫ f) :
    ∃ e : pullback F F ⟶ pullback t (pullback.fst f f ≫ a), IsIso e ∧
      pullback.diagonal F ≫ e =
        (pullback.lift (pullback.fst t a)
          (pullback.snd t a ≫ pullback.diagonal f) (by
            simpa [Category.assoc] using (pullback.condition (f := t) (g := a)) :
              pullback.fst t a ≫ t =
                pullback.snd t a ≫ pullback.diagonal f ≫
                  pullback.fst f f ≫ a) :
            pullback t a ⟶ pullback t (pullback.fst f f ≫ a)) := by
  have hdiag : pullback.fst f f ≫ a = pullback.snd f f ≫ a := by
    rw [← hfb, pullback.condition_assoc]
  have hq : pullback.fst F F ≫ pullback.fst t a = pullback.snd F F ≫ pullback.fst t a := by
    rw [← hFfst, pullback.condition_assoc]
  let d₀ : pullback F F ⟶ pullback f f :=
    pullback.lift (pullback.fst F F ≫ pullback.snd t a) (pullback.snd F F ≫ pullback.snd t a)
      (by simp only [Category.assoc, ← hFsnd, pullback.condition_assoc])
  let e : pullback F F ⟶ pullback t (pullback.fst f f ≫ a) :=
    pullback.lift (pullback.fst F F ≫ pullback.fst t a) d₀ (by
      simp [d₀, pullback.condition])
  let x₁ : pullback t (pullback.fst f f ≫ a) ⟶ pullback t a := pullback.lift (pullback.fst t _)
      (pullback.snd t _ ≫ pullback.fst f f) (by
        simpa [Category.assoc] using
          (pullback.condition (f := t) (g := pullback.fst f f ≫ a)))
  let x₂ : pullback t (pullback.fst f f ≫ a) ⟶ pullback t a := pullback.lift (pullback.fst t _)
      (pullback.snd t _ ≫ pullback.snd f f) (by
        rw [Category.assoc, ← hdiag]
        exact pullback.condition)
  have hex₁ : e ≫ x₁ = pullback.fst F F := by
    apply pullback.hom_ext <;>
      simp [e, x₁, d₀]
  have hex₂ : e ≫ x₂ = pullback.snd F F := by
    apply pullback.hom_ext <;>
      simp [e, x₂, d₀, hq]
  have hcomp : x₁ ≫ F = x₂ ≫ F := by
    apply pullback.hom_ext <;> simp [x₁, x₂, hFfst, hFsnd, pullback.condition]
  let k : pullback t (pullback.fst f f ≫ a) ⟶ pullback F F := pullback.lift x₁ x₂ hcomp
  have he₁ : e ≫ k = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp [k, hex₁, hex₂]
  have he₂ : k ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · simp [k, e, x₁]
    · apply pullback.hom_ext <;>
        simp [k, e, d₀, x₁, x₂]
  refine ⟨e, ⟨⟨k, he₁, he₂⟩⟩, ?_⟩
  apply pullback.hom_ext
  · simp [e, pullback.diagonal_fst_assoc]
  · apply pullback.hom_ext <;>
      simp [e, d₀, pullback.diagonal_fst,
        pullback.diagonal_snd, pullback.diagonal_fst_assoc, pullback.diagonal_snd_assoc]

/-- Formation of the diagonal commutes with base change: if `F : Z₁ ×_{Z₀} X₀ ⟶ Z₁ ×_{Z₀} Y₀`
is the base change of `f : X₀ ⟶ Y₀` along `t : Z₁ ⟶ Z₀`, then the base change along `t` of the
diagonal of `f` is surjective exactly when the diagonal of `F` is surjective. -/
theorem isSurjective_baseChange_diagonal_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X₀ Y₀ Z₀ Z₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : X₀ ⟶ Z₀) (b : Y₀ ⟶ Z₀) (t : Z₁ ⟶ Z₀)
    (f : X₀ ⟶ Y₀) (hfb : f ≫ b = a)
    (F : pullback t a ⟶ pullback t b)
    (hFfst : F ≫ pullback.fst t b = pullback.fst t a)
    (hFsnd : F ≫ pullback.snd t b = pullback.snd t a ≫ f) :
    IsSurjective B S hS
        (pullback.lift (pullback.fst t a)
          (pullback.snd t a ≫ pullback.diagonal f) (by
            simpa [Category.assoc] using (pullback.condition (f := t) (g := a)) :
              pullback.fst t a ≫ t =
                pullback.snd t a ≫ pullback.diagonal f ≫
                  pullback.fst f f ≫ a) :
            pullback t a ⟶ pullback t (pullback.fst f f ≫ a)) ↔
      IsSurjective B S hS (pullback.diagonal F) := by
  obtain ⟨e, _, hfactor⟩ :=
    exists_isIso_diagonal_comp_eq_baseChange_diagonal B S hS a b t f hfb F hFfst hFsnd
  rw [← hfactor, IsSurjective, pointsMap_comp]
  exact Function.Surjective.of_comp_iff'
    ⟨pointsMap_injective_of_mono B S hS e, pointsMap_surjective_of_iso B S hS (asIso e)⟩ _

/-- Formation of the diagonal commutes with base change: if `F : Z₁ ×_{Z₀} X₀ ⟶ Z₁ ×_{Z₀} Y₀`
is the base change of `f : X₀ ⟶ Y₀` along `t : Z₁ ⟶ Z₀`, then the base change along `t` of the
diagonal of `f` is an isomorphism exactly when the diagonal of `F` is an isomorphism. -/
theorem isIso_baseChange_diagonal_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X₀ Y₀ Z₀ Z₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : X₀ ⟶ Z₀) (b : Y₀ ⟶ Z₀) (t : Z₁ ⟶ Z₀)
    (f : X₀ ⟶ Y₀) (hfb : f ≫ b = a)
    (F : pullback t a ⟶ pullback t b)
    (hFfst : F ≫ pullback.fst t b = pullback.fst t a)
    (hFsnd : F ≫ pullback.snd t b = pullback.snd t a ≫ f) :
    IsIso
        (pullback.lift (pullback.fst t a)
          (pullback.snd t a ≫ pullback.diagonal f) (by
            simpa [Category.assoc] using (pullback.condition (f := t) (g := a)) :
              pullback.fst t a ≫ t =
                pullback.snd t a ≫ pullback.diagonal f ≫
                  pullback.fst f f ≫ a) :
            pullback t a ⟶ pullback t (pullback.fst f f ≫ a)) ↔
      IsIso (pullback.diagonal F) := by
  obtain ⟨e, _, hfactor⟩ :=
    exists_isIso_diagonal_comp_eq_baseChange_diagonal B S hS a b t f hfb F hFfst hFsnd
  rw [← hfactor]
  exact ⟨fun _ => IsIso.of_isIso_comp_right _ e, fun _ => inferInstance⟩

end AlgebraicGeometry.Space

end
