module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality

/-!
# Systems of sheaves on an inverse system of schemes

Let `I` be a preordered set and let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes, so that
`i' ≥ i` gives a transition morphism `f_{i'i} : X_{i'} ⟶ X_i`. A *system of sheaves* on such a
system consists of a sheaf `F_i` on the small étale site of `X_i` for every index, together with
maps `f_{i'i}^{-1} F_i ⟶ F_{i'}` which compose correctly along `i'' ≥ i' ≥ i`.

The inverse image of étale sheaves along a transition is the left adjoint of the direct image,
which in turn is restriction along base change of small étale sites. The comparison between the
inverse image along a composite transition and the composite of the inverse images is therefore
not a datum of a system but is fixed once and for all: it is obtained from the associativity of
fibre products by transport to direct images and then to their left adjoints.

## Main definitions

* `Stacks.EtaleCohomology.systemPushforward` — direct image along a transition morphism.
* `Stacks.EtaleCohomology.systemPullback` — inverse image along a transition morphism.
* `Stacks.EtaleCohomology.EtaleSheafSystem` — sheaves on the members of an inverse system of
  schemes with transition maps satisfying the cocycle condition.

## Main results

* `Stacks.EtaleCohomology.systemPullbackComp` — the canonical comparison between the inverse
  image along a composite transition and the composite of the inverse images.

## Implementation notes

The index set is only preordered and no condition is imposed on the transition morphisms, as in
the source. The source's compatibility is the cocycle condition alone; it does not ask the map at
an identity index to be the identity, and that condition is not imposed here either. The unital
variant, which does impose it, is `Stacks.EtaleCohomology.UnitalEtaleSheafSystem`.

The coefficient category is arbitrary, the source's sheaves of sets and sheaves of abelian groups
being instances. The inverse image exists as soon as the direct image has a left adjoint, which is
the hypothesis carried here; for coefficients admitting sheafification and the relevant left Kan
extensions it is supplied by `CategoryTheory.Functor.sheafPullbackConstruction`.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w v u

namespace Stacks.EtaleCohomology

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (A : Type w) [Category.{w'} A]

/-- The direct image of sheaves along a transition morphism `D.map a : X_{i} ⟶ X_{j}` of an
inverse system of schemes: restriction along base change of small étale sites. -/
public abbrev systemPushforward {i j : Iᵒᵖ} (a : i ⟶ j) :
    Sheaf (smallEtaleTopology (D.obj i)) A ⥤ Sheaf (smallEtaleTopology (D.obj j)) A :=
  (smallEtaleBaseChange (D.map a)).sheafPushforwardContinuous A
    (smallEtaleTopology (D.obj j)) (smallEtaleTopology (D.obj i))

/-- Base change of small étale sites along a composite transition is the composite of the base
changes, in the reverse order. -/
public def systemBaseChangeComp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    smallEtaleBaseChange (D.map b) ⋙ smallEtaleBaseChange (D.map a) ≅
      smallEtaleBaseChange (D.map (a ≫ b)) :=
  (smallEtaleBaseChangeComp (D.map a) (D.map b)).symm ≪≫
    eqToIso (congrArg (fun f : D.obj i ⟶ D.obj k => smallEtaleBaseChange f)
      (D.map_comp a b).symm)

/-- The direct image along a composite transition is the composite of the direct images. -/
public def systemPushforwardComp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    systemPushforward D A a ⋙ systemPushforward D A b ≅ systemPushforward D A (a ≫ b) :=
  Functor.sheafPushforwardContinuousComp' (systemBaseChangeComp D a b) A
    (smallEtaleTopology (D.obj k)) (smallEtaleTopology (D.obj j))
    (smallEtaleTopology (D.obj i))

variable [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- The inverse image of sheaves along a transition morphism of an inverse system of schemes,
as the left adjoint of the direct image. -/
public abbrev systemPullback {i j : Iᵒᵖ} (a : i ⟶ j) :
    Sheaf (smallEtaleTopology (D.obj j)) A ⥤ Sheaf (smallEtaleTopology (D.obj i)) A :=
  (smallEtaleBaseChange (D.map a)).sheafPullback A
    (smallEtaleTopology (D.obj j)) (smallEtaleTopology (D.obj i))

/-- The inverse image along a transition morphism is left adjoint to the direct image. -/
public def systemAdjunction {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemPullback D A a ⊣ systemPushforward D A a :=
  Functor.sheafAdjunctionContinuous (smallEtaleBaseChange (D.map a)) A
    (smallEtaleTopology (D.obj j)) (smallEtaleTopology (D.obj i))

/-- The inverse image along a composite transition is the composite of the inverse images:
the comparison adjoint to `Stacks.EtaleCohomology.systemPushforwardComp`. -/
public def systemPullbackComp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    systemPullback D A b ⋙ systemPullback D A a ≅ systemPullback D A (a ≫ b) :=
  Functor.sheafPullbackComp' (systemBaseChangeComp D a b) A
    (smallEtaleTopology (D.obj k)) (smallEtaleTopology (D.obj j))
    (smallEtaleTopology (D.obj i))

/-- A *system of sheaves* on an inverse system of schemes `D`: a sheaf on the small étale site of
each member, together with a map from the inverse image of the sheaf at an index to the sheaf at
any larger index, compatible with composition of the transition morphisms through the canonical
comparison `Stacks.EtaleCohomology.systemPullbackComp`.

As in the source, no condition is imposed on the map attached to an identity index. -/
@[stacks 0EZL "a system of sheaves: sheaves on the small étale sites of the members and maps \
  f_{i'i}^{-1}F_i ⟶ F_{i'} satisfying the cocycle condition, the only condition the source \
  imposes; arbitrary coefficient category"]
public structure EtaleSheafSystem where
  /-- The sheaf on the small étale site of each member of the system. -/
  obj : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) A
  /-- The map from the inverse image of the sheaf at an index to the sheaf at a larger index. -/
  map : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), (systemPullback D A a).obj (obj j) ⟶ obj i
  /-- The cocycle condition: the map attached to a composite transition is the composite of the
  maps attached to its factors. -/
  map_comp : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
    (systemPullbackComp D A a b).inv.app (obj k) ≫
        (systemPullback D A a).map (map b) ≫ map a =
      map (a ≫ b)

end Stacks.EtaleCohomology

end
