module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Continuous

/-!
# The big h topoi of a morphism: the two site functors and the three formulas

Let `f : T ⟶ S` be a morphism of a big h site.  The source describes the morphism of big h
topoi `f_big : Sh((Sch/T)_h) → Sh((Sch/S)_h)` through the two functors relating the slice
sites: postcomposition `u : V/T ↦ V/S` and base change `v : U/S ↦ U ×_S T/T`.  This file
records, for the big h sites of Stacks 0EU1, that `u` is cocontinuous and continuous, that
`v` is a continuous right adjoint of `u`, that `u` and `v` induce the same morphism of topoi,
the two formulas `f_big^{-1}(G)(U/T) = G(U/S)` and `f_{big,*}(F)(U/S) = F(U ×_S T/T)`, and the
existence of a left adjoint `f_{big!}` of `f_big^{-1}` commuting with fibre products and
equalizers.

## Main definitions

* `AlgebraicGeometry.bigHOverMapPullbackAdj`: the adjunction `u ⊣ v`.
* `AlgebraicGeometry.bigHLowerShriekAdj`: the adjunction `f_{big!} ⊣ f_big^{-1}`.

## Main results

* `AlgebraicGeometry.isCocontinuous_bigHOverMap`,
  `AlgebraicGeometry.isContinuous_bigHOverMap`: `u` is cocontinuous and continuous.
* `AlgebraicGeometry.isContinuous_bigHOverPullback`: `v` is continuous.
* `AlgebraicGeometry.bigHMorphismOfTopoi_pushforwardIso`,
  `AlgebraicGeometry.bigHMorphismOfTopoi_inverseImageIso`: `u` and `v` induce the same
  morphism of topoi, namely `AlgebraicGeometry.bigHMorphismOfTopoi`.
* `AlgebraicGeometry.bigHMorphismOfTopoi_inverseImage_obj_obj_obj`,
  `AlgebraicGeometry.bigHMorphismOfTopoi_pushforward_obj_obj_obj`,
  `AlgebraicGeometry.bigHSheafPushforwardCocontinuousObjIso`: the two section formulas.
* `AlgebraicGeometry.preservesLimitsOfShape_bigHLowerShriek`: `f_{big!}` commutes with fibre
  products and equalizers.

## Implementation notes

The big h category over an object of a big h site is a slice of the size-bounded category of
schemes, whose topology is the slice topology, so every clause follows from the generic site
lemmas instantiated at `CategoryTheory.Over.map` and `CategoryTheory.Over.pullback`:
cocontinuity and continuity of both functors are Mathlib's instances for a slice topology, the
agreement of the two morphisms of topoi is Stacks 00XX (1) in the form
`CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso` and Stacks 00XR (1) in the form
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous`, and the
behaviour of `f_{big!}` on connected limits is Stacks 00XS.

Since the direct and inverse images of `AlgebraicGeometry.bigHMorphismOfTopoi` are restriction
along `v` and along `u`, the two displayed formulas of the source hold for it by definition;
the content is that these restrictions are the direct and inverse images attached to the
cocontinuous functor `u`, which is what the two comparison isomorphisms say.

The hypotheses of Stacks 00XS are met because the big h category over `T` has a terminal
object and pullbacks, hence all finite limits and in particular equalizers, and because
`CategoryTheory.Over.map` preserves connected limits: it does so after composition with the
forgetful functor of the slice, which reflects them.

## References

* [Stacks Project, Tag 0EU6](https://stacks.math.columbia.edu/tag/0EU6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe t u

namespace AlgebraicGeometry

variable (B : BigHSite.{u}) {T S : B.Schemes} (f : T ⟶ S)

/-- **Stacks 0EU6.** The functor `u : (Sch/T)_h ⥤ (Sch/S)_h`, `V/T ↦ V/S`, is cocontinuous. -/
@[stacks 0EU6 "`u : V/T ↦ V/S` is cocontinuous"]
public theorem isCocontinuous_bigHOverMap :
    (Over.map f).IsCocontinuous (B.topology.over T) (B.topology.over S) :=
  inferInstance

/-- **Stacks 0EU6**, used in the proof. The functor `u : (Sch/T)_h ⥤ (Sch/S)_h`,
`V/T ↦ V/S`, is continuous. -/
@[stacks 0EU6 "`u : V/T ↦ V/S` is continuous"]
public theorem isContinuous_bigHOverMap :
    (Over.map f).IsContinuous (B.topology.over T) (B.topology.over S) :=
  inferInstance

/-- **Stacks 0EU6.** The functor `v : (Sch/S)_h ⥤ (Sch/T)_h` given by base change along `f` is
a right adjoint of `u`: for `U/T` and `V/S` one has `Mor_S(u(U), V) = Mor_T(U, V ×_S T)`. -/
@[stacks 0EU6 "`v : U/S ↦ U ×_S T/T` is a right adjoint of `u`"]
public noncomputable def bigHOverMapPullbackAdj : Over.map f ⊣ Over.pullback f :=
  Over.mapPullbackAdj f

/-- The functor `v` of `AlgebraicGeometry.bigHOverMapPullbackAdj` is base change: the scheme
underlying `v(U/S)` is the fibre product `U ×_S T`. -/
public theorem bigHOverPullback_obj_left (U : Over S) :
    ((Over.pullback f).obj U).left = Limits.pullback U.hom f :=
  rfl

/-- **Stacks 0EU6.** The functor `v : (Sch/S)_h ⥤ (Sch/T)_h`, `U/S ↦ U ×_S T/T`, is
continuous. -/
@[stacks 0EU6 "`v : U/S ↦ U ×_S T/T` is continuous"]
public theorem isContinuous_bigHOverPullback :
    (Over.pullback f).IsContinuous (B.topology.over S) (B.topology.over T) :=
  inferInstance

/-- **Stacks 0EU6.** The functors `u` and `v` induce the same morphism of topoi: the direct
image `{}_s u` attached to cocontinuity of `u` is the direct image `v^s` of
`AlgebraicGeometry.bigHMorphismOfTopoi`. -/
@[stacks 0EU6 "`u` and `v` induce the same morphism of topoi `f_big`, direct images"]
public noncomputable def bigHMorphismOfTopoi_pushforwardIso :
    (Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
        (B.topology.over T) (B.topology.over S) ≅
      (bigHMorphismOfTopoi B f).pushforward :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type (u + 1))

/-- **Stacks 0EU6.** The inverse image `(u^p -)^#` attached to cocontinuity of `u` is the
inverse image of `AlgebraicGeometry.bigHMorphismOfTopoi`, namely plain restriction along `u`:
the sheafification is unnecessary. -/
@[stacks 0EU6 "`u` and `v` induce the same morphism of topoi `f_big`, inverse images"]
public noncomputable def bigHMorphismOfTopoi_inverseImageIso :
    (Over.map f).sheafPullbackCocontinuous (Type (u + 1))
        (B.topology.over T) (B.topology.over S) ≅
      (bigHMorphismOfTopoi B f).inverseImage :=
  (Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type (u + 1))
    (B.topology.over T) (B.topology.over S)

/-- **Stacks 0EU6**, the formula `f_big^{-1}(G)(U/T) = G(U/S)`. -/
@[stacks 0EU6 "`f_big⁻¹(G)(U/T) = G(U/S)`"]
public theorem bigHMorphismOfTopoi_inverseImage_obj_obj_obj
    (G : Sheaf (BigHOver.topology B S.obj S.property) (Type (u + 1))) (U : Over T) :
    ((bigHMorphismOfTopoi B f).inverseImage.obj G).obj.obj (op U) =
      G.obj.obj (op ((Over.map f).obj U)) :=
  rfl

/-- **Stacks 0EU6**, the formula `f_{big,*}(F)(U/S) = F(U ×_S T/T)`. -/
@[stacks 0EU6 "`f_big,*(F)(U/S) = F(U ×_S T/T)`"]
public theorem bigHMorphismOfTopoi_pushforward_obj_obj_obj
    (F : Sheaf (BigHOver.topology B T.obj T.property) (Type (u + 1))) (U : Over S) :
    ((bigHMorphismOfTopoi B f).pushforward.obj F).obj.obj (op U) =
      F.obj.obj (op ((Over.pullback f).obj U)) :=
  rfl

/-- **Stacks 0EU6**, the formula `f_{big,*}(F)(U/S) = F(U ×_S T/T)` for the direct image
`{}_s u` attached to cocontinuity of `u`. -/
@[stacks 0EU6 "`f_big,*(F)(U/S) = F(U ×_S T/T)`"]
public noncomputable def bigHSheafPushforwardCocontinuousObjIso
    (F : Sheaf (BigHOver.topology B T.obj T.property) (Type (u + 1))) (U : Over S) :
    (((Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
        (B.topology.over T) (B.topology.over S)).obj F).obj.obj (op U) ≅
      F.obj.obj (op ((Over.pullback f).obj U)) :=
  ((sheafToPresheaf (B.topology.over S) (Type (u + 1))).mapIso
    ((bigHMorphismOfTopoi_pushforwardIso B f).app F)).app (op U)

/-- **Stacks 0EU6.** The inverse image `f_big^{-1}` has a left adjoint `f_{big!}`, namely the
sheaf pullback along the continuous functor `u`. -/
@[stacks 0EU6 "`f_big⁻¹` has a left adjoint `f_big!`"]
public noncomputable def bigHLowerShriekAdj :
    (Over.map f).sheafPullback (Type (u + 1)) (B.topology.over T) (B.topology.over S) ⊣
      (bigHMorphismOfTopoi B f).inverseImage :=
  (Over.map f).sheafAdjunctionContinuous (Type (u + 1))
    (B.topology.over T) (B.topology.over S)

/-- **Stacks 0EU6.** The left adjoint `f_{big!}` of `f_big^{-1}` commutes with fibre products
and equalizers, and more generally with every finite connected limit. -/
@[stacks 0EU6 "`f_big!` commutes with fibre products and equalizers"]
public theorem preservesLimitsOfShape_bigHLowerShriek
    (I : Type t) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I
      ((Over.map f).sheafPullback (Type (u + 1))
        (B.topology.over T) (B.topology.over S)) := by
  have : HasFiniteLimits (Over T) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have key (J : Type) [SmallCategory J] [IsConnected J] : PreservesLimitsOfShape J (Over.map f) :=
    have : PreservesLimitsOfShape J (Over.map f ⋙ Over.forget S) :=
      inferInstanceAs (PreservesLimitsOfShape J (Over.forget T))
    preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)
  have := key WalkingCospan
  have := key WalkingParallelPair
  exact Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (B.topology.over T) (B.topology.over S) I

/-- **Stacks 0EU6.** `f_{big!}` commutes with fibre products. -/
@[stacks 0EU6 "`f_big!` commutes with fibre products and equalizers"]
public theorem preservesLimitsOfShape_walkingCospan_bigHLowerShriek :
    PreservesLimitsOfShape WalkingCospan
      ((Over.map f).sheafPullback (Type (u + 1))
        (B.topology.over T) (B.topology.over S)) :=
  preservesLimitsOfShape_bigHLowerShriek B f WalkingCospan

/-- **Stacks 0EU6.** `f_{big!}` commutes with equalizers. -/
@[stacks 0EU6 "`f_big!` commutes with fibre products and equalizers"]
public theorem preservesLimitsOfShape_walkingParallelPair_bigHLowerShriek :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.map f).sheafPullback (Type (u + 1))
        (B.topology.over T) (B.topology.over S)) :=
  preservesLimitsOfShape_bigHLowerShriek B f WalkingParallelPair

end AlgebraicGeometry
