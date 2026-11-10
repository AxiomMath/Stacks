module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekContinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesLowerShriek.ModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricStalkLocalHom
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# `f_small^*` and `f_{big,*}` on sheaves of `𝒪`-modules at the module universe of Stacks 0DDH

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its objects.  This file builds,
at the module universe `u + 1` of the étale cohomology comparisons of Stacks 0DDH:

* the direct image `f_{small,*}` and the pullback `f_small^*` of sheaves of `𝒪`-modules along the
  morphism of small étale ringed sites of Stacks 070R part (2), with their adjunction;
* the direct image `f_{big,*}` of sheaves of `𝒪`-modules along `f_big`, and the adjunction
  `f_big^* ⊣ f_{big,*}` with the inverse image `f_big^* = f_big^{-1}` of Stacks 04CC part (2);
* **Stacks 0759 on sheaves of `𝒪`-modules** for these sites —
  `(f_{big,*}ℱ)|_{S_étale} = f_{small,*}(ℱ|_{T_étale})` — and its mate on inverse images,
  `f_big^*(π_S^*K) ≅ π_T^*(f_small^*K)`.

## Main definitions

* `AlgebraicGeometry.smallEtaleRingStructureSharp` and
  `AlgebraicGeometry.bigEtaleRingStructureSharp` — the structure maps `f_small^♯` and `f_big^♯`.
* `AlgebraicGeometry.smallEtaleModulePushforward`, `.smallEtaleModulePullbackLarge` and
  `.bigEtaleModulePushforward` — `f_{small,*}`, `f_small^*` and `f_{big,*}` on `𝒪`-modules.

## Main results

* `AlgebraicGeometry.smallEtaleModulePullbackAdjunction` — `f_small^* ⊣ f_{small,*}`.
* `AlgebraicGeometry.bigEtaleModuleInverseImageAdjunction` — `f_big^* ⊣ f_{big,*}`.
* `AlgebraicGeometry.smallEtaleRingStructureSharp_eq_restrictStructureMap` — the three structure
  maps are compatible with the commuting square of site functors of Stacks 021I.
* `AlgebraicGeometry.smallEtaleRestrictionPushforwardModules_eq` — Stacks 0759 on `𝒪`-modules.
* `AlgebraicGeometry.smallEtaleModulePullbackProjectionIso` — its mate on inverse images.

## Implementation notes

The pullback `f_small^*` is Mathlib's `SheafOfModules.pullback` at module universe `u + 1`, which
exists by `SheafOfModules.pushforward_isRightAdjoint_of_univLE`: the small étale site of a scheme
has its objects in `Type (u + 1)` and its morphisms and structure rings in `Type u`, so all four
`UnivLE` hypotheses of that instance hold at module universe `u + 1`.  Its structure map is
`AlgebraicGeometry.structureSharpRing`, the structure map `f_small^♯` of Stacks 070R part (2)
with the commutativity of the sections forgotten.

`f_{big,*}` is restriction along `CategoryTheory.Over.pullback f` — the direct image of the
morphism of topoi `f_big` — together with restriction of scalars along
`AlgebraicGeometry.bigEtaleRingStructureSharp`, which pulls a global function on `V / S` back
along the projection `V ×_S T ⟶ V`.  That projection is the counit of
`CategoryTheory.Over.mapPullbackAdj f` (this is
`AlgebraicGeometry.baseChangeProjection_app`), and the structure map is written as the counit
rather than as the projection because the two compatibilities that
`SheafOfModules.pushforwardPushforwardAdj` asks of a pair of structure maps over an adjoint pair
of site functors are then the triangle identities of that adjunction.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 04CC](https://stacks.math.columbia.edu/tag/04CC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-! ### The structure map of `f_small` -/

/-- **`f_small^♯ : 𝒪_S ⟶ f_{small,*}𝒪_T`, at the sheaves of rings the module apparatus reads.**
At an étale `V / S` it pulls a global function on `V` back along the projection `T ×_S V ⟶ V`.

This is `AlgebraicGeometry.structureSharp`, the structure map of the morphism of ringed sites of
Stacks 070R part (2), with the commutativity of the sections forgotten (its presheaf map is
`AlgebraicGeometry.structureSharpRing`), read as a morphism of the `RingCat`-valued structure
sheaves of the two small étale sites. -/
public def smallEtaleRingStructureSharp :
    SmallEtale.structureSheaf B S.obj S.property ⟶
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj
        (SmallEtale.structureSheaf B T.obj T.property) :=
  ObjectProperty.homMk (structureSharpRing B f)

/-- The structure map of `f_small` on modules is the structure map of the morphism of
ringed sites of Stacks 070R part (2), on underlying presheaves of rings. -/
public theorem smallEtaleRingStructureSharp_hom :
    (smallEtaleRingStructureSharp B T S f).hom = structureSharpRing B f :=
  rfl

/-! ### `f_{small,*}` and `f_small^*` on sheaves of `𝒪`-modules -/

/-- **`f_{small,*}` on sheaves of `𝒪`-modules**, at the module universe of Stacks 0DDH: the
direct image along small étale base change, with restriction of scalars along `f_small^♯`. -/
public abbrev smallEtaleModulePushforward :
    SheafOfModules.{u + 1} (SmallEtale.structureSheaf B T.obj T.property) ⥤
      SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property) :=
  SheafOfModules.pushforward.{u + 1} (smallEtaleRingStructureSharp B T S f)

section Pullback

/-- **`f_small^*` on sheaves of `𝒪`-modules**, at the module universe of Stacks 0DDH: the left
adjoint of `f_{small,*}`, which is how Stacks 03D6 part (2) defines it. -/
public abbrev smallEtaleModulePullbackLarge :
    SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property) ⥤
      SheafOfModules.{u + 1} (SmallEtale.structureSheaf B T.obj T.property) :=
  SheafOfModules.pullback.{u + 1} (smallEtaleRingStructureSharp B T S f)

/-- On sheaves of `𝒪`-modules on the small étale sites of schemes, at the module universe of
Stacks 0DDH, `f_small^*` is left adjoint to `f_{small,*}`. -/
@[stacks 03D7 "the small étale sites of schemes, at the module universe `u + 1` of the étale \
cohomology comparisons of Stacks 0DDH rather than at the universe `u` of the sections of the \
structure sheaves"]
public def smallEtaleModulePullbackAdjunction :
    smallEtaleModulePullbackLarge B T S f ⊣ smallEtaleModulePushforward B T S f :=
  SheafOfModules.pullbackPushforwardAdjunctionUnivLE.{u + 1}
    (smallEtaleRingStructureSharp B T S f)

/-- `f_small^*` on `𝒪`-modules preserves finite colimits, being a left adjoint. -/
public instance smallEtaleModulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleModulePullbackLarge B T S f) :=
  ((smallEtaleModulePullbackAdjunction B T S f).leftAdjoint_preservesColimits.{u + 1,
    u + 1}).preservesFiniteColimits

/-- `f_small^*` on `𝒪`-modules is additive: it preserves finite colimits, hence binary
biproducts. -/
public instance smallEtaleModulePullback_additive :
    (smallEtaleModulePullbackLarge B T S f).Additive :=
  have : PreservesBinaryBiproducts (smallEtaleModulePullbackLarge B T S f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

end Pullback

/-! ### The structure map of `f_big`, and `f_{big,*}` on sheaves of `𝒪`-modules -/

/-- **`f_big^♯ : 𝒪 ⟶ f_{big,*}𝒪`, the structure map of `f_big` on the big étale sites.**  At an
object `V / S` it pulls a global function on `V` back along the projection `V ×_S T ⟶ V`, which
is the counit of `CategoryTheory.Over.mapPullbackAdj f`
(`AlgebraicGeometry.baseChangeProjection_app`).

The target is typed with the structure sheaf of the big étale site over `T`, which is legitimate
by `AlgebraicGeometry.bigEtaleInverseImageRing_eq`: restricting the structure sheaf of the big
étale site over `S` along postcomposition with `f` returns the structure sheaf of the big étale
site over `T`. -/
public def bigEtaleRingStructureSharp :
    BigEtaleOver.structureSheaf B S.obj S.property ⟶
      ((Over.pullback f).sheafPushforwardContinuous RingCat.{u}
          (BigEtaleOver.topology B S.obj S.property)
          (BigEtaleOver.topology B T.obj T.property)).obj
        (BigEtaleOver.structureSheaf B T.obj T.property) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op (Over.mapPullbackAdj f).counit)
    (BigEtaleOver.structureSheaf B S.obj S.property).obj)

/-- At `V / S` the structure map of `f_big` is pullback of global functions along the counit of
`CategoryTheory.Over.mapPullbackAdj f`, which is the projection `V ×_S T ⟶ V` of the fibre
product by `AlgebraicGeometry.baseChangeProjection_app`. -/
public theorem bigEtaleRingStructureSharp_hom_app (V : (Over S)ᵒᵖ) :
    (bigEtaleRingStructureSharp B T S f).hom.app V =
      (BigEtaleOver.structureSheaf B S.obj S.property).obj.map
        (Opposite.op ((Over.mapPullbackAdj f).counit.app V.unop)) :=
  rfl

/-- **`f_{big,*}` on sheaves of `𝒪`-modules**, at the module universe of Stacks 0DDH:
restriction along base change `V/S ↦ V ×_S T / T`, with restriction of scalars along
`f_big^♯`. -/
public abbrev bigEtaleModulePushforward :
    SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B T.obj T.property) ⥤
      SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) :=
  SheafOfModules.pushforward.{u + 1} (bigEtaleRingStructureSharp B T S f)

/-- The first compatibility of the two structure maps of `f_big` over the adjoint pair
`Over.map f ⊣ Over.pullback f`: the structure map of `f_{big,*}` *is* the counit of that
adjunction read on global functions, the structure map of `f_big^*` being the identity. -/
public theorem bigEtaleRingStructureSharp_counit :
    Functor.whiskerRight (NatTrans.op (Over.mapPullbackAdj f).counit)
        (BigEtaleOver.structureSheaf B S.obj S.property).obj =
      (bigEtaleRingStructureSharp B T S f).hom ≫
        (Over.pullback f).op.whiskerLeft
          (Stacks.SheafOfModules.structureMap
            (BigEtaleOver.topology B T.obj T.property)
            (BigEtaleOver.topology B S.obj S.property) (Over.map f)
            (BigEtaleOver.structureSheaf B S.obj S.property)).hom :=
  rfl

/-- The second compatibility of the two structure maps of `f_big` over the adjoint pair
`Over.map f ⊣ Over.pullback f`: it is the triangle identity of that adjunction, read on global
functions. -/
public theorem bigEtaleRingStructureSharp_triangle :
    (Stacks.SheafOfModules.structureMap
          (BigEtaleOver.topology B T.obj T.property)
          (BigEtaleOver.topology B S.obj S.property) (Over.map f)
          (BigEtaleOver.structureSheaf B S.obj S.property)).hom ≫
        (Over.map f).op.whiskerLeft (bigEtaleRingStructureSharp B T S f).hom ≫
          Functor.whiskerRight (NatTrans.op (Over.mapPullbackAdj f).unit)
            (BigEtaleOver.structureSheaf B T.obj T.property).obj =
      𝟙 (BigEtaleOver.structureSheaf B T.obj T.property).obj := by
  refine NatTrans.ext (funext fun V => ?_)
  have h : ((Over.map f).map ((Over.mapPullbackAdj f).unit.app V.unop)) ≫
      (Over.mapPullbackAdj f).counit.app ((Over.map f).obj V.unop) = 𝟙 _ :=
    (Over.mapPullbackAdj f).left_triangle_components _
  have key : (BigEtaleOver.structureSheaf B S.obj S.property).obj.map
        ((Over.mapPullbackAdj f).counit.app ((Over.map f).obj V.unop)).op ≫
      (BigEtaleOver.structureSheaf B S.obj S.property).obj.map
        ((Over.map f).map ((Over.mapPullbackAdj f).unit.app V.unop)).op =
      𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, h, CategoryTheory.op_id]
    exact (BigEtaleOver.structureSheaf B S.obj S.property).obj.map_id _
  exact key

/-- On the big étale sites of schemes, the inverse image `f_big^* = f_big^{-1}` of sheaves of
`𝒪`-modules of Stacks 04CC part (2) is left adjoint to the direct image `f_{big,*}`. -/
@[stacks 03D7 "the big étale sites of schemes, where the pullback of sheaves of modules is the \
inverse image of Stacks 04CC part (2), at the module universe `u + 1`",
  sga "4 Vbis 1.3.6" "special case"]
public def bigEtaleModuleInverseImageAdjunction :
    bigEtaleInverseImageModules B T S f ⊣ bigEtaleModulePushforward B T S f :=
  SheafOfModules.pushforwardPushforwardAdj.{u + 1} (Over.mapPullbackAdj f)
    (Stacks.SheafOfModules.structureMap
      (BigEtaleOver.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property) (Over.map f)
      (BigEtaleOver.structureSheaf B S.obj S.property))
    (bigEtaleRingStructureSharp B T S f)
    (bigEtaleRingStructureSharp_counit B T S f)
    (bigEtaleRingStructureSharp_triangle B T S f)

/-! ### The module form of Stacks 0759 for the big and small étale sites of schemes -/

section Square

attribute [local instance] smallEtaleInclusion_isCocontinuous

/-- **The three structure maps are compatible with the commuting square of site functors of
Stacks 021I.**  The structure map `f_small^♯` is the structure map `f_big^♯` restricted to the
small étale site of `S` and read through
`AlgebraicGeometry.smallEtaleBaseChange_comp_inclusion`: both are pullback of global functions
along the projection of the base change `T ×_S V ⟶ V`. -/
public theorem smallEtaleRingStructureSharp_eq_restrictStructureMap :
    smallEtaleRingStructureSharp B T S f =
      Stacks.SheafOfModules.restrictStructureMap
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property)
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property)
        (Over.pullback f) (smallEtaleBaseChange B f)
        (SmallEtale.inclusion B S.obj S.property)
        (SmallEtale.inclusion B T.obj T.property)
        (BigEtaleOver.structureSheaf B T.obj T.property)
        (BigEtaleOver.structureSheaf B S.obj S.property)
        (bigEtaleRingStructureSharp B T S f)
        (smallEtaleBaseChange_comp_inclusion B f).symm := by
  change smallEtaleRingStructureSharp B T S f =
    ((SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property)).map
      (bigEtaleRingStructureSharp B T S f) ≫ eqToHom rfl
  rw [eqToHom_refl, Category.comp_id]
  exact Sheaf.hom_ext (NatTrans.ext (funext fun _ => rfl))

/-- Restriction to the small étale site of `S` of the direct image along `f_big` of a sheaf of
`𝒪`-modules is the direct image along `f_small` of its restriction to the small étale site of
`T`:
`(f_{big,*}ℱ)|_{S_étale} = f_{small,*}(ℱ|_{T_étale})`, as an equality of functors. -/
@[stacks 0759 "sheaves of `𝒪`-modules on the big and small étale sites of schemes, at the \
module universe `u + 1` of the étale cohomology comparisons of Stacks 0DDH"]
public theorem smallEtaleRestrictionPushforwardModules_eq :
    Stacks.SheafOfModules.inverseImage.{u + 1}
          (SmallEtale.topology B T.obj T.property)
          (BigEtaleOver.topology B T.obj T.property)
          (SmallEtale.inclusion B T.obj T.property)
          (BigEtaleOver.structureSheaf B T.obj T.property) ⋙
        smallEtaleModulePushforward B T S f =
      bigEtaleModulePushforward B T S f ⋙
        Stacks.SheafOfModules.inverseImage.{u + 1}
          (SmallEtale.topology B S.obj S.property)
          (BigEtaleOver.topology B S.obj S.property)
          (SmallEtale.inclusion B S.obj S.property)
          (BigEtaleOver.structureSheaf B S.obj S.property) :=
  Stacks.SheafOfModules.inverseImage_comp_pushforward_eq.{u + 1}
    (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B T.obj T.property)
    (SmallEtale.topology B S.obj S.property)
    (BigEtaleOver.topology B S.obj S.property)
    (Over.pullback f) (smallEtaleBaseChange B f)
    (SmallEtale.inclusion B S.obj S.property)
    (SmallEtale.inclusion B T.obj T.property)
    (BigEtaleOver.structureSheaf B T.obj T.property)
    (BigEtaleOver.structureSheaf B S.obj S.property)
    (bigEtaleRingStructureSharp B T S f)
    (smallEtaleRingStructureSharp B T S f)
    (smallEtaleBaseChange_comp_inclusion B f).symm
    (smallEtaleRingStructureSharp_eq_restrictStructureMap B T S f)

section Mate

/-- **The left adjoint of `f_{big,*}` on sheaves of `𝒪`-modules is the inverse image
`f_big^* = f_big^{-1}` of Stacks 04CC part (2)**: two left adjoints of one functor are
canonically isomorphic. -/
public def bigEtaleModulePullbackIso :
    SheafOfModules.pullback.{u + 1} (bigEtaleRingStructureSharp B T S f) ≅
      bigEtaleInverseImageModules B T S f :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunctionUnivLE.{u + 1}
      (bigEtaleRingStructureSharp B T S f))
    (bigEtaleModuleInverseImageAdjunction B T S f)

/-- **The left adjoint of `π_{X,*}` on sheaves of `𝒪`-modules is the lower shriek of
Stacks 0797 along the small étale inclusion**, that is `π_X^*`: two left adjoints of one functor
are canonically isomorphic. -/
public def smallEtaleModuleInclusionPullbackIso (X : B.Scheme)
    [HasSheafify (SmallEtale.topology B X.obj X.property) Ab.{u + 1}]
    [HasSheafify (BigEtaleOver.topology B X.obj X.property) Ab.{u + 1}]
    [(SmallEtale.topology B X.obj X.property).WEqualsLocallyBijective Ab.{u + 1}]
    [(BigEtaleOver.topology B X.obj X.property).WEqualsLocallyBijective Ab.{u + 1}] :
    (Stacks.SheafOfModules.inverseImage.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property)
        (SmallEtale.inclusion B X.obj X.property)
        (BigEtaleOver.structureSheaf B X.obj X.property)).leftAdjoint ≅
      Stacks.SheafOfModules.lowerShriek.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property)
        (SmallEtale.inclusion B X.obj X.property)
        (BigEtaleOver.structureSheaf B X.obj X.property) :=
  Adjunction.leftAdjointUniq (Adjunction.ofIsRightAdjoint _)
    (Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (BigEtaleOver.topology B X.obj X.property)
      (SmallEtale.inclusion B X.obj X.property)
      (BigEtaleOver.structureSheaf B X.obj X.property))

/-- The mate of `AlgebraicGeometry.smallEtaleRestrictionPushforwardModules_eq` on inverse images
of sheaves of `𝒪`-modules on the big and small étale sites of schemes:
`π_T^* ∘ f_small^* ≅ f_big^* ∘ π_S^*`, that is `f_big^{-1}(π_S^*K) ≅ π_T^*(f_small^*K)`, where
`π^*` is the lower shriek of Stacks 0797 along the small étale inclusion and `f_big^*` is the
inverse image of Stacks 04CC part (2). -/
@[stacks 0759 "inverse images of sheaves of `𝒪`-modules on the big and small étale sites of \
schemes, at the module universe `u + 1` of the étale cohomology comparisons of Stacks 0DDH"]
public def smallEtaleModulePullbackProjectionIso :
    smallEtaleModulePullbackLarge B T S f ⋙
        Stacks.SheafOfModules.lowerShriek.{u + 1}
          (SmallEtale.topology B T.obj T.property)
          (BigEtaleOver.topology B T.obj T.property)
          (SmallEtale.inclusion B T.obj T.property)
          (BigEtaleOver.structureSheaf B T.obj T.property) ≅
      Stacks.SheafOfModules.lowerShriek.{u + 1}
          (SmallEtale.topology B S.obj S.property)
          (BigEtaleOver.topology B S.obj S.property)
          (SmallEtale.inclusion B S.obj S.property)
          (BigEtaleOver.structureSheaf B S.obj S.property) ⋙
        bigEtaleInverseImageModules B T S f := by
  haveI : (SheafOfModules.pushforward.{u + 1}
      (S := Stacks.SheafOfModules.inverseImageRing
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property)
        (SmallEtale.inclusion B S.obj S.property)
        (BigEtaleOver.structureSheaf B S.obj S.property))
      (R := Stacks.SheafOfModules.inverseImageRing
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property)
        (SmallEtale.inclusion B T.obj T.property)
        (BigEtaleOver.structureSheaf B T.obj T.property))
      (smallEtaleRingStructureSharp B T S f)).IsRightAdjoint :=
    (smallEtaleModulePullbackAdjunction B T S f).isRightAdjoint
  haveI : (SheafOfModules.pushforward.{u + 1}
      (bigEtaleRingStructureSharp B T S f)).IsRightAdjoint :=
    (bigEtaleModuleInverseImageAdjunction B T S f).isRightAdjoint
  haveI : (Stacks.SheafOfModules.inverseImage.{u + 1}
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)
      (SmallEtale.inclusion B T.obj T.property)
      (BigEtaleOver.structureSheaf B T.obj T.property)).IsRightAdjoint :=
    (Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)
      (SmallEtale.inclusion B T.obj T.property)
      (BigEtaleOver.structureSheaf B T.obj T.property)).isRightAdjoint
  haveI : (Stacks.SheafOfModules.inverseImage.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)
      (SmallEtale.inclusion B S.obj S.property)
      (BigEtaleOver.structureSheaf B S.obj S.property)).IsRightAdjoint :=
    (Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)
      (SmallEtale.inclusion B S.obj S.property)
      (BigEtaleOver.structureSheaf B S.obj S.property)).isRightAdjoint
  exact Stacks.SheafOfModules.pullbackCompLowerShriekIso.{u + 1}
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)
      (Over.pullback f) (smallEtaleBaseChange B f)
      (SmallEtale.inclusion B S.obj S.property)
      (SmallEtale.inclusion B T.obj T.property)
      (BigEtaleOver.structureSheaf B T.obj T.property)
      (BigEtaleOver.structureSheaf B S.obj S.property)
      (bigEtaleRingStructureSharp B T S f)
      (smallEtaleRingStructureSharp B T S f)
      (smallEtaleBaseChange_comp_inclusion B f).symm
      (smallEtaleRingStructureSharp_eq_restrictStructureMap B T S f) ≪≫
    Functor.isoWhiskerLeft _ (bigEtaleModulePullbackIso B T S f)

end Mate

end Square

end AlgebraicGeometry

end
