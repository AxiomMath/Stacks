module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FreeAtGenericPointsTransition

/-!
# Base change in a smooth family and cofiltered limits of the base

Let `f : X ⟶ S` be the family of Situation 05MP and let `E` be a cofiltered inverse system of
schemes over `S` with limit `T`. This file exhibits `X ×_S T` as the limit of the system
`i ↦ X ×_S E i` of base changes, and shows that the transition morphisms of that system are
affine as soon as the stages of `E` are affine, which is what makes the approximation results
for cofiltered limits of schemes applicable to it.

## Main definitions

* `AlgebraicGeometry.FreeAtGenericPointsSituation.baseChangeFunctor` is base change along the
  family, as a functor from schemes over the base to schemes.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.isLimitMapConeBaseChangeFunctor`: base change
  along the family carries a limit cone over a cofiltered index category to a limit cone.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.isAffineHom_transitionHom`: a transition
  morphism of base changes is affine as soon as the two schemes over the base are affine.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.exists_preimage_eq_transitionHom`: a
  quasi-compact open of the base change to the limit is the preimage of a quasi-compact open of
  the base change to some stage.

## Implementation notes

Base change along `f` is the composite of `CategoryTheory.Over.pullback f`, which is a right
adjoint by `CategoryTheory.Over.mapPullbackAdj` and hence preserves all limits, with the
forgetful functor of the slice over `X`, which creates and therefore preserves connected
limits. A cofiltered index category is connected, so the same forgetful functor for the slice
over `S` also reflects limits, which turns the hypothesis that a cone of schemes over the base
is a limit after forgetting the structure morphisms into a limit cone in the slice itself. The
composite functor lands on the fibre product written with `f` in the second factor, so it is
compared with `baseChangeFunctor`, which uses the first, by the symmetry of the fibre product.

The affineness of a transition morphism uses nothing about the family: the transition morphism
is a base change of the morphism of schemes over `S` inducing it, and that morphism is affine
because its source and target are. In particular `f` is not assumed quasi-compact anywhere,
and the stages of the system need only be affine, which is exactly the hypothesis under which
`AlgebraicGeometry.exists_preimage_eq` descends a quasi-compact open to a stage.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w' w u

namespace AlgebraicGeometry.FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u})

/-- The transition morphism induced by the identity of a scheme over the base is the
identity. -/
@[simp]
theorem transitionHom_id (T : Over D.S) :
    D.transitionHom (𝟙 T) = 𝟙 (pullback D.f T.hom) := by
  refine pullback.hom_ext ?_ ?_
  · rw [transitionHom_comp_fst, Category.id_comp]
  · rw [transitionHom_comp_snd, Over.id_left, Category.comp_id, Category.id_comp]

/-- The transition morphisms of base changes compose. -/
@[simp]
theorem transitionHom_comp {T T' T'' : Over D.S} (g : T'' ⟶ T') (g' : T' ⟶ T) :
    D.transitionHom (g ≫ g') = D.transitionHom g ≫ D.transitionHom g' := by
  refine pullback.hom_ext ?_ ?_
  · rw [transitionHom_comp_fst, Category.assoc, transitionHom_comp_fst, transitionHom_comp_fst]
  · rw [transitionHom_comp_snd, Category.assoc, transitionHom_comp_snd, ← Category.assoc,
      transitionHom_comp_snd, Over.comp_left, Category.assoc]

/-- Base change along the family of the situation, as a functor from schemes over the base to
schemes: it sends `T` to `X ×_S T` and a morphism to its transition morphism. -/
@[simps]
noncomputable def baseChangeFunctor : Over D.S ⥤ Scheme.{u} where
  obj T := pullback D.f T.hom
  map g := D.transitionHom g
  map_id T := D.transitionHom_id T
  map_comp g g' := D.transitionHom_comp g g'

/-- Base change along the family is the pullback functor to the slice over the total space
followed by the forgetful functor of that slice, up to the symmetry of the fibre product. -/
noncomputable def baseChangeFunctorIsoPullback :
    D.baseChangeFunctor ≅ Over.pullback D.f ⋙ Over.forget D.X :=
  NatIso.ofComponents (fun T ↦ pullbackSymmetry D.f T.hom) (by
    intro T T' g
    refine pullback.hom_ext ?_ ?_
    · simp [baseChangeFunctor, transitionHom, pullback.lift_fst, pullback.lift_snd]
    · simp [baseChangeFunctor, transitionHom, pullback.lift_fst, pullback.lift_snd])

/-- Base change along the family preserves connected limits: pullback to the slice over the
total space is a right adjoint, and the forgetful functor of that slice preserves connected
limits. -/
instance preservesLimitsOfShape_baseChangeFunctor {I : Type w} [Category.{w'} I]
    [IsConnected I] : PreservesLimitsOfShape I D.baseChangeFunctor :=
  preservesLimitsOfShape_of_natIso D.baseChangeFunctorIsoPullback.symm

/-- Base change along the family of the situation commutes with cofiltered limits: if a cone on
a cofiltered system of schemes over the base is a limit cone after forgetting the structure
morphisms, then the induced cone of base changes is a limit cone of schemes. -/
noncomputable def isLimitMapConeBaseChangeFunctor {I : Type w} [Category.{w'} I]
    [IsCofiltered I] (E : I ⥤ Over D.S) (c : Cone E)
    (hc : IsLimit ((Over.forget D.S).mapCone c)) :
    IsLimit (D.baseChangeFunctor.mapCone c) := by
  have : IsConnected I := IsCofiltered.isConnected I
  exact isLimitOfPreserves D.baseChangeFunctor (isLimitOfReflects (Over.forget D.S) hc)

/-- A transition morphism of base changes along a morphism of affine schemes over the base is
affine: it is a base change of that morphism. -/
theorem isAffineHom_transitionHom {T T' : Over D.S} (g : T' ⟶ T)
    [IsAffine T.left] [IsAffine T'.left] : IsAffineHom (D.transitionHom g) :=
  MorphismProperty.of_isPullback (D.isPullback_transitionHom g).flip
    (isAffineHom_of_isAffine g.left)

/-- The transition morphisms of the system of base changes of a system of affine schemes over
the base are affine, in the shape in which the approximation results for cofiltered limits of
schemes take them as an instance. -/
theorem isAffineHom_comp_baseChangeFunctor_map {I : Type w} [Category.{w'} I]
    (E : I ⥤ Over D.S) (hE : ∀ i, IsAffine ((Over.forget D.S).obj (E.obj i)))
    {i j : I} (e : i ⟶ j) : IsAffineHom ((E ⋙ D.baseChangeFunctor).map e) :=
  have : IsAffine (E.obj j).left := hE j
  have : IsAffine (E.obj i).left := hE i
  D.isAffineHom_transitionHom (E.map e)

/-- **Stacks Project, Tag 01Z4 (1)** for the base changes of a cofiltered system of affine
schemes over the base: a quasi-compact open of the base change to the limit is the preimage of
a quasi-compact open of the base change to some stage of the system. -/
theorem exists_preimage_eq_transitionHom {I : Type u} [Category.{u} I] [IsCofiltered I]
    (E : I ⥤ Over D.S) (c : Cone E) (hc : IsLimit ((Over.forget D.S).mapCone c))
    (hE : ∀ i, IsAffine ((Over.forget D.S).obj (E.obj i)))
    (U : (pullback D.f c.pt.hom).Opens)
    (hU : IsCompact (U : Set ↥(pullback D.f c.pt.hom))) :
    ∃ (i : I) (V : (pullback D.f (E.obj i).hom).Opens),
      IsCompact (V : Set ↥(pullback D.f (E.obj i).hom)) ∧
        D.transitionHom (c.π.app i) ⁻¹ᵁ V = U := by
  have : ∀ {i j : I} (e : i ⟶ j), IsAffineHom ((E ⋙ D.baseChangeFunctor).map e) :=
    fun e ↦ D.isAffineHom_comp_baseChangeFunctor_map E hE e
  exact exists_preimage_eq (E ⋙ D.baseChangeFunctor) (D.baseChangeFunctor.mapCone c)
    (D.isLimitMapConeBaseChangeFunctor E c hc) U hU

end AlgebraicGeometry.FreeAtGenericPointsSituation

end
