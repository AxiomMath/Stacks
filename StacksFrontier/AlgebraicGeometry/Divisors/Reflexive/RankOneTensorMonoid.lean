module

public import Mathlib.CategoryTheory.Skeletal
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentTensorAssoc
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DeterminantInvertible
import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor monoid of rank one coherent reflexive modules

Let `X` be an integral locally Noetherian scheme and `𝒞` the category of coherent reflexive
`𝒪_X`-modules with its hull tensor product `ℱ ⊗_𝒞 𝒢 = (ℱ ⊗_{𝒪_X} 𝒢)^∨∨`.  A coherent module
has *rank one* when its fibre rank at the generic point is one.  The hull tensor product
preserves rank one, and on isomorphism classes of rank one coherent reflexive modules it is a
commutative monoid law with the structure sheaf as its unit.

## Main definitions

* `HasRankOne F`: the fibre rank of `ℱ` at the generic point is one.
* `RankOneReflexiveModules X`: the rank one coherent reflexive modules, a full subcategory.
* `rankOneTensorObj`, `rankOneUnitObj`: the hull tensor product and the structure sheaf, as
  rank one coherent reflexive modules.
* `rankOneSkeletonCommMonoid`: the commutative monoid of isomorphism classes.

## Main results

* `hasRankOne_tensorObj`: the hull tensor product of two rank one coherent reflexive modules
  has rank one.
* `tensorObjUnit`, `unitTensorObj`: the structure sheaf is a two-sided unit for the hull tensor
  product of coherent reflexive modules.
* `rankOneSkeletonCommMonoid`: **part of Stacks, Tag 0EBL** — the rule
  `ℱ, 𝒢 ↦ (ℱ ⊗_{𝒪_X} 𝒢)^∨∨` is a commutative monoid law on the set of isomorphism classes of
  rank one coherent reflexive `𝒪_X`-modules.

## Implementation notes

**What of Tag 0EBL is here and what is not.**  The tag has two assertions: that
`(ℋom_{𝒪_X}(ℱ, 𝒪_X) ⊗_{𝒪_X} 𝒢)^∨∨ → ℋom_{𝒪_X}(ℱ, 𝒢)` is an isomorphism, and that the rule
`ℱ, 𝒢 ↦ (ℱ ⊗_{𝒪_X} 𝒢)^∨∨` is an abelian *group* law on isomorphism classes of rank one
coherent reflexive modules.  This file proves the monoid part of the second assertion — the
operation is well defined, associative, commutative and unital — and no declaration here claims
more.  The two remaining parts of the tag need normality, which this file does not assume, and
live elsewhere: the first assertion is
`AlgebraicGeometry.CoherentReflexive.isIso_dualTensorHullToSheafHom` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/DualTensorInternalHom.lean`, and the inverses
are `AlgebraicGeometry.CoherentReflexive.rankOneSkeletonCommGroup` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassSurjective.lean`, whose
multiplication is the law defined here on the nose
(`rankOneSkeletonCommGroup_toCommMonoid`).

**Normality is not assumed.**  The tag states its hypotheses for a normal scheme, and
normality is genuinely needed for inverses: on the spectrum of the nonnormal domain
`k[y, x², xy, x³]` a rank one coherent reflexive module need not have a tensor inverse, which is
`AlgebraicGeometry.not_forall_fiberRank_one_tensorObj_dualObj_iso_unit` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneNotInvertible.lean`.  The monoid law
needs no such hypothesis, so it is stated without one.

**Rank one is measured at the generic point** by `AlgebraicGeometry.Scheme.Modules.fiberRank`,
the rank function of [Stacks, Tag 05P2], which is the spelling the counterexample just cited
uses.  On an integral scheme the local ring at the generic point is a field, so every stalk
there is free; that is what makes the fibre rank multiplicative under the tensor product
(`Module.finrank_tensorProduct`) and insensitive to taking the reflexive hull
(`AlgebraicGeometry.Scheme.Modules.fiberRank_reflexiveHull_eq_of_free_stalk`).

**Two module structures on a stalk.**  The isomorphism `(ℱ ⊗ 𝒢)_x ≅ ℱ_x ⊗ 𝒢_x` of
[Stacks, Tag 01CB] is linear for the scalar action built in that tag, which is equal to but not
syntactically Mathlib's.  `finrank_stalk_tensorSheaf` takes the three module structures as
parameters together with `Stacks.SheafOfModules.stalkModule_eq`, so that they can be
substituted; this is the device of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorBifunctorStalk.lean`.

**The group of isomorphism classes** is the skeleton of the full subcategory, as for the Picard
group in `StacksFrontier/AlgebraicGeometry/PicardGroup/Basic.lean`; the monoid axioms are the
isomorphisms `tensorObjAssoc`, `tensorObjComm`, `unitTensorObj` and `tensorObjUnit` read
through `CategoryTheory.toSkeleton_eq_toSkeleton_iff`.

## References

* [Stacks Project, Tag 0EBL](https://stacks.math.columbia.edu/tag/0EBL)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive reflexiveHull dualSheaf unitModule
  toDoubleDual)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules inclusion)
open Stacks.SheafOfModules.TensorStalkRingedSpace (tensorStalkIso)

universe u

namespace AlgebraicGeometry.CoherentReflexive

-- The stalk module of a tensor product is indexed by `Stacks.SheafOfModules.Tensor.ringSheaf`,
-- which agrees with `structureSheafRing` only after it unfolds; instance search works at
-- `instances` transparency, so without this the canonical `stalkModule` is not even a candidate.
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

/-! ### The fibre rank of a tensor product at the generic point -/

/-- The sheafified tensor product of two `𝒪_X`-modules on a scheme, read as an `𝒪_X`-module.
This is a transport of spelling: the two types are definitionally equal. -/
noncomputable abbrev tensorModules {X : Scheme.{u}} (F G : X.Modules) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
    ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))

/-- The fibre rank of a tensor product is the product of the fibre ranks, at a point where both
stalks are free.  The three module structures on the stalks are parameters, so that the scalar
action of [Stacks, Tag 01CB] — for which the comparison `(ℱ ⊗ 𝒢)_x ≅ ℱ_x ⊗ 𝒢_x` is linear — can
be substituted for Mathlib's. -/
theorem finrank_stalk_tensorSheaf {X : Scheme.{u}} (F G : X.Modules) (x : X)
    (iF : Module (X.presheaf.stalk x) (F.presheaf.stalk x))
    (iG : Module (X.presheaf.stalk x) (G.presheaf.stalk x))
    (iT : Module (X.presheaf.stalk x)
      ((tensorModules F G).presheaf.stalk x))
    (hF : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace F.val x = iF)
    (hG : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x = iG)
    (hT : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))).val x = iT)
    (fF : @Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x) _ _ iF)
    (fG : @Module.Free (X.presheaf.stalk x) (G.presheaf.stalk x) _ _ iG) :
    @Module.finrank _ _ _ _ iT =
      @Module.finrank _ _ _ _ iF * @Module.finrank _ _ _ _ iG := by
  subst hF
  subst hG
  subst hT
  have fF' : @Module.Free
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace F.val x) _ _
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace F.val x) := fF
  have fG' : @Module.Free
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace G.val x) _ _
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x) := fG
  exact (tensorStalkIso X.toRingedSpace x F G).finrank_eq.trans Module.finrank_tensorProduct

/-- **The fibre rank at the generic point is multiplicative under the tensor product.**  On an
integral scheme the local ring at the generic point is a field, so both stalks are free there
and the comparison `(ℱ ⊗ 𝒢)_η ≅ ℱ_η ⊗ 𝒢_η` of [Stacks, Tag 01CB] computes the rank. -/
theorem fiberRank_genericPoint_tensorSheaf {X : Scheme.{u}} [IsIntegral X] (F G : X.Modules)
    [F.IsFiniteType] [G.IsFiniteType] [(tensorModules F G).IsFiniteType] :
    Scheme.Modules.fiberRank (tensorModules F G) (genericPoint X) =
      Scheme.Modules.fiberRank F (genericPoint X) *
        Scheme.Modules.fiberRank G (genericPoint X) := by
  rw [Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk,
    Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk,
    Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk]
  exact finrank_stalk_tensorSheaf F G _ _ _ _
    (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace F.val _)
    (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace G.val _)
    (Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace _ _)
    (Scheme.Modules.free_stalk_genericPoint F) (Scheme.Modules.free_stalk_genericPoint G)

/-! ### Rank one coherent reflexive modules -/

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A coherent reflexive module has **rank one** when its fibre rank at the generic point is
one.  This is the rank function of [Stacks, Tag 05P2], measured at the generic point. -/
def HasRankOne (F : CoherentReflexiveModules X) : Prop :=
  Scheme.Modules.fiberRank F.obj.obj (genericPoint X) = 1

/-- **The structure sheaf has rank one.**  Its stalk at the generic point is the local ring
there, a one dimensional vector space over itself. -/
@[sga "6 I 6.0" "(iii), special case"]
theorem hasRankOne_unitObj (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    HasRankOne (unitObj X) := by
  have hft : (unitModule X).IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have h := Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk (unitModule X)
  refine h.trans ?_
  have e : (X.presheaf.stalk (genericPoint X)) ≃ₗ[X.presheaf.stalk (genericPoint X)]
      ((unitModule X).presheaf.stalk (genericPoint X)) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.unitStalkEquiv X (genericPoint X)
  rw [← e.finrank_eq, Module.finrank_self]

/-- **The hull tensor product preserves rank one.**  The fibre rank at the generic point is
multiplicative under the tensor product, and taking the reflexive hull does not change it
because the stalk at the generic point is free over a field. -/
theorem hasRankOne_tensorObj {F G : CoherentReflexiveModules X}
    (hF : HasRankOne F) (hG : HasRankOne G) : HasRankOne (tensorObj F G) := by
  have hFc : _root_.SheafOfModules.IsCoherent F.obj.obj := F.obj.property
  have hGc : _root_.SheafOfModules.IsCoherent G.obj.obj := G.obj.property
  set E : X.Modules := (ordinaryTensor F G).obj with hE
  have hEc : _root_.SheafOfModules.IsCoherent E := (ordinaryTensor F G).property
  have hEft : E.IsFiniteType := _root_.IsCoherent.toIsFiniteType E
  have hEfp : E.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent E
  have hdfp : (dualSheaf E).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFinitePresentation_dualSheaf E
  have hhc : _root_.SheafOfModules.IsCoherent (reflexiveHull E) :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_doubleDual E
  have hhft : (reflexiveHull E).IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have hFft : F.obj.obj.IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have hGft : G.obj.obj.IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have hhull : Scheme.Modules.fiberRank (reflexiveHull E) (genericPoint X) =
      Scheme.Modules.fiberRank E (genericPoint X) :=
    Scheme.Modules.fiberRank_reflexiveHull_eq_of_free_stalk E (genericPoint X)
      (Scheme.Modules.free_stalk_genericPoint E)
  have htens : Scheme.Modules.fiberRank E (genericPoint X) =
      Scheme.Modules.fiberRank F.obj.obj (genericPoint X) *
        Scheme.Modules.fiberRank G.obj.obj (genericPoint X) :=
    fiberRank_genericPoint_tensorSheaf F.obj.obj G.obj.obj
  change Scheme.Modules.fiberRank (reflexiveHull E) (genericPoint X) = 1
  rw [hhull, htens, hF, hG, mul_one]

/-- The rank one coherent reflexive `𝒪_X`-modules, as a full subcategory of the coherent
reflexive modules. -/
abbrev RankOneReflexiveModules (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :=
  ObjectProperty.FullSubcategory (fun F : CoherentReflexiveModules X => HasRankOne F)

/-! ### The structure sheaf is a unit for the hull tensor product -/

/-- The reflexive hull of a coherent reflexive module is that module: the canonical map to the
double dual is invertible, which is what reflexivity says. -/
noncomputable def hullReflectionInclusionIso (A : CoherentReflexiveModules X) :
    (hullReflection X).obj ((inclusion X).obj A) ≅ A :=
  have : IsIso (toDoubleDual A.obj.obj) := A.property
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (asIso (toDoubleDual A.obj.obj)).symm)

/-- **The structure sheaf is a right unit for the hull tensor product.**  The ordinary tensor
product with the structure sheaf is the right unitor of [Stacks, Tag 01CA], and the hull of a
coherent reflexive module is that module. -/
noncomputable def tensorObjUnit (F : CoherentReflexiveModules X) :
    tensorObj F (unitObj X) ≅ F :=
  (hullReflection X).mapIso (ObjectProperty.isoMk _
      (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.2
        F.obj.obj)) ≪≫
    hullReflectionInclusionIso F

/-- **The structure sheaf is a left unit for the hull tensor product**, by symmetry of the hull
tensor product. -/
noncomputable def unitTensorObj (F : CoherentReflexiveModules X) :
    tensorObj (unitObj X) F ≅ F :=
  tensorObjComm (unitObj X) F ≪≫ tensorObjUnit F

/-- **Functoriality of the hull tensor product in both variables.**  It is the hull of the
functoriality of the ordinary tensor product. -/
noncomputable def tensorObjIso {F F' G G' : CoherentReflexiveModules X} (e : F ≅ F')
    (f : G ≅ G') : tensorObj F G ≅ tensorObj F' G' :=
  (hullReflection X).mapIso (ObjectProperty.isoMk _
    (Stacks.SheafOfModules.Invertible.tensorProductIso X.presheaf X.ringCatSheaf.2
      ((inclusion X ⋙ ObjectProperty.ι _).mapIso e)
      ((inclusion X ⋙ ObjectProperty.ι _).mapIso f)))

/-! ### The hull tensor product on rank one modules -/

/-- The hull tensor product of two rank one coherent reflexive modules. -/
noncomputable def rankOneTensorObj (F G : RankOneReflexiveModules X) :
    RankOneReflexiveModules X :=
  ⟨tensorObj F.obj G.obj, hasRankOne_tensorObj F.property G.property⟩

/-- The structure sheaf, as a rank one coherent reflexive module. -/
noncomputable def rankOneUnitObj (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] :
    RankOneReflexiveModules X :=
  ⟨unitObj X, hasRankOne_unitObj X⟩

/-- Functoriality of the hull tensor product of rank one modules in both variables. -/
noncomputable def rankOneTensorIso {F F' G G' : RankOneReflexiveModules X}
    (e : F ≅ F') (f : G ≅ G') : rankOneTensorObj F G ≅ rankOneTensorObj F' G' :=
  ObjectProperty.isoMk _ (tensorObjIso ((ObjectProperty.ι _).mapIso e)
    ((ObjectProperty.ι _).mapIso f))

/-- Associativity of the hull tensor product of rank one modules. -/
noncomputable def rankOneTensorAssoc (F G K : RankOneReflexiveModules X) :
    rankOneTensorObj (rankOneTensorObj F G) K ≅ rankOneTensorObj F (rankOneTensorObj G K) :=
  ObjectProperty.isoMk _ (tensorObjAssoc F.obj G.obj K.obj)

/-- Commutativity of the hull tensor product of rank one modules. -/
noncomputable def rankOneTensorComm (F G : RankOneReflexiveModules X) :
    rankOneTensorObj F G ≅ rankOneTensorObj G F :=
  ObjectProperty.isoMk _ (tensorObjComm F.obj G.obj)

/-- The structure sheaf is a right unit for the hull tensor product of rank one modules. -/
noncomputable def rankOneTensorUnitIso (F : RankOneReflexiveModules X) :
    rankOneTensorObj F (rankOneUnitObj X) ≅ F :=
  ObjectProperty.isoMk _ (tensorObjUnit F.obj)

/-- The structure sheaf is a left unit for the hull tensor product of rank one modules. -/
noncomputable def rankOneUnitTensorIso (F : RankOneReflexiveModules X) :
    rankOneTensorObj (rankOneUnitObj X) F ≅ F :=
  ObjectProperty.isoMk _ (unitTensorObj F.obj)

/-! ### The monoid of isomorphism classes -/

/-- The hull tensor product on isomorphism classes of rank one coherent reflexive modules. -/
noncomputable def rankOneSkeletonMul (a b : Skeleton (RankOneReflexiveModules X)) :
    Skeleton (RankOneReflexiveModules X) :=
  toSkeleton <| rankOneTensorObj
    ((fromSkeleton (RankOneReflexiveModules X)).obj a)
    ((fromSkeleton (RankOneReflexiveModules X)).obj b)

/-- The isomorphism class of the structure sheaf. -/
noncomputable def rankOneSkeletonOne : Skeleton (RankOneReflexiveModules X) :=
  toSkeleton (rankOneUnitObj X)

/-- **Stacks Project, Tag 0EBL.**  The product of two isomorphism classes of rank one coherent
reflexive modules is the class of `(ℱ ⊗_{𝒪_X} 𝒢)^∨∨`.  This identifies the monoid law of
`rankOneSkeletonCommMonoid` with the rule the tag states, so the two together assert that that
rule is a commutative monoid law. -/
@[simp, stacks 0EBL "the monoid law is the double dual of the tensor product"]
theorem rankOneSkeletonMul_toSkeleton (F G : RankOneReflexiveModules X) :
    rankOneSkeletonMul (toSkeleton F) (toSkeleton G) = toSkeleton (rankOneTensorObj F G) :=
  toSkeleton_eq_toSkeleton_iff.2
    ⟨rankOneTensorIso (fromSkeletonToSkeletonIso F) (fromSkeletonToSkeletonIso G)⟩

/-- Every element of the skeleton of a category is the class of an object. -/
private theorem exists_toSkeleton_eq {C : Type*} [Category C] (a : Skeleton C) :
    ∃ F, toSkeleton F = a :=
  ⟨_, toSkeleton_fromSkeleton_obj a⟩

/-- The product of isomorphism classes is associative: the associativity isomorphism of the hull
tensor product identifies the two triple products. -/
theorem rankOneSkeleton_mul_assoc (a b c : Skeleton (RankOneReflexiveModules X)) :
    rankOneSkeletonMul (rankOneSkeletonMul a b) c =
      rankOneSkeletonMul a (rankOneSkeletonMul b c) := by
  obtain ⟨F, rfl⟩ := exists_toSkeleton_eq a
  obtain ⟨G, rfl⟩ := exists_toSkeleton_eq b
  obtain ⟨K, rfl⟩ := exists_toSkeleton_eq c
  rw [rankOneSkeletonMul_toSkeleton, rankOneSkeletonMul_toSkeleton,
    rankOneSkeletonMul_toSkeleton, rankOneSkeletonMul_toSkeleton]
  exact toSkeleton_eq_toSkeleton_iff.2 ⟨rankOneTensorAssoc F G K⟩

/-- The class of the structure sheaf is a left unit for the product of isomorphism classes. -/
theorem rankOneSkeleton_one_mul (a : Skeleton (RankOneReflexiveModules X)) :
    rankOneSkeletonMul rankOneSkeletonOne a = a := by
  obtain ⟨F, rfl⟩ := exists_toSkeleton_eq a
  rw [rankOneSkeletonOne, rankOneSkeletonMul_toSkeleton]
  exact toSkeleton_eq_toSkeleton_iff.2 ⟨rankOneUnitTensorIso F⟩

/-- The class of the structure sheaf is a right unit for the product of isomorphism classes. -/
theorem rankOneSkeleton_mul_one (a : Skeleton (RankOneReflexiveModules X)) :
    rankOneSkeletonMul a rankOneSkeletonOne = a := by
  obtain ⟨F, rfl⟩ := exists_toSkeleton_eq a
  rw [rankOneSkeletonOne, rankOneSkeletonMul_toSkeleton]
  exact toSkeleton_eq_toSkeleton_iff.2 ⟨rankOneTensorUnitIso F⟩

/-- The product of isomorphism classes is commutative, by symmetry of the hull tensor
product. -/
theorem rankOneSkeleton_mul_comm (a b : Skeleton (RankOneReflexiveModules X)) :
    rankOneSkeletonMul a b = rankOneSkeletonMul b a := by
  obtain ⟨F, rfl⟩ := exists_toSkeleton_eq a
  obtain ⟨G, rfl⟩ := exists_toSkeleton_eq b
  rw [rankOneSkeletonMul_toSkeleton, rankOneSkeletonMul_toSkeleton]
  exact toSkeleton_eq_toSkeleton_iff.2 ⟨rankOneTensorComm F G⟩

/-- **Stacks Project, Tag 0EBL, the monoid part of the group law.**  On an integral locally
Noetherian scheme the rule `ℱ, 𝒢 ↦ (ℱ ⊗_{𝒪_X} 𝒢)^∨∨` is a commutative monoid law on the set of
isomorphism classes of rank one coherent reflexive `𝒪_X`-modules, with the class of the
structure sheaf as its unit.  Inverses are not provided; see the implementation notes. -/
@[instance_reducible, stacks 0EBL "commutative monoid law on rank 1 coherent reflexive classes"]
noncomputable def rankOneSkeletonCommMonoid (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] : CommMonoid (Skeleton (RankOneReflexiveModules X)) where
  mul := rankOneSkeletonMul
  one := rankOneSkeletonOne
  mul_assoc := rankOneSkeleton_mul_assoc
  one_mul := rankOneSkeleton_one_mul
  mul_one := rankOneSkeleton_mul_one
  mul_comm := rankOneSkeleton_mul_comm

end AlgebraicGeometry.CoherentReflexive

end
