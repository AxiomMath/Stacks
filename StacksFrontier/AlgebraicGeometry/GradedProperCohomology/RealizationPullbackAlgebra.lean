module

public import StacksFrontier.AlgebraicGeometry.Constructions.UngradedRealizationPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.CommRingSheafLiftIso
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafCoproductInt

/-!
# The ungraded realization of a sheaf of graded algebras, and algebra pullback

Let `g : Z ⟶ X` be a morphism of schemes and `A` a sheaf of graded `𝒪_X`-algebras whose
homogeneous multiplication commutes. There are two sheaves of commutative `𝒪_Z`-algebras built
from `A` and `g`:

* `(algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)`, the algebra pullback
  `g⁻¹R(A) ⊗_{g⁻¹𝒪_X} 𝒪_Z` of the realization of `A`;
* `Stacks.RelativeSpec.gradedAlgebraSheaf Z (Stacks.Conormal.gradedPullback g A) hc'`, the
  realization of the degreewise pullback.

`Stacks.RelativeSpec.pullbackUnderlyingModuleIso`
(`StacksFrontier/AlgebraicGeometry/Constructions/UngradedRealizationPullback.lean`) identifies the
`𝒪_Z`-module underlying the second with the module pullback of the module underlying the first.
**This file builds the comparison of the two as sheaves of commutative `𝒪_Z`-algebras**, in the
direction out of the algebra pullback, and nothing else: it is a morphism, not an isomorphism.

## Why this direction, and what it costs

The algebra pullback is a pushout of sheaves of commutative rings
(`Stacks.AffineAlgebraEquivalence.algebraPullback_isPushout`), so a morphism *out* of it is
`IsPushout.desc` applied to its two legs, and neither leg needs the sections of the pushout to be
described. The leg out of `𝒪_Z` is the structure morphism of the target. The leg out of
`g⁻¹R(A)` is the adjoint transpose of a morphism `R(A) ⟶ g_* R(g^*A)`, which is assembled from
the sheafification-free data of the grading:

* `Stacks.GradedAlgebra.totalRingHomOfFamily` turns a degreewise family of additive maps into a
  ring homomorphism out of the sections of `A`'s ungraded realization, given multiplicativity on
  homogeneous sections and the image of the graded unit;
* the family is the pullback unit `Stacks.RingedSpace.pullbackUnit` followed by the homogeneous
  inclusion into the realization of `g^*A`, so multiplicativity is
  `Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit` and the unit condition is
  `Stacks.RingedSpace.pullbackGradedAlgebra_one_eval` — the two identities that pin the
  pulled-back algebra down;
* `Stacks.GradedAlgebra.totalSheafLift` extends the result across the sheafification, and
  `Stacks.CommRingSheaf.homMk'` reads it in `CommRingCat`.

The opposite direction is not here, but its degreewise input is: a morphism *into* the pushout
out of the realization of `g^*A` has to be built degreewise out of `g^*(A.piece n)`, whose only
handle is the universal property of the module pullback, and the morphism of modules that
property needs is `Stacks.FundamentalGroup.algebraPullbackModuleComparison`, which is
unconditional. `pieceToPullbackAlgebra` below is that family and
`pieceToPullbackAlgebra_pullbackUnit` computes it on pullback-unit images. What is still missing
is multiplicativity of the family *for all* local sections — the pullback-unit images do not
exhaust them, so it needs the bilinear extensionality
`Stacks.RingedSpace.pullbackBilinear_heq_ext` with both sides packaged as bilinear morphisms of
sheaves of modules — and then the two round-trip identities. So
**invertibility of the comparison below is open**, and it is the one missing input for
[Stacks, Tag 01LX] read at `𝓑 = f^* B̃`, which is what [Stacks, Tag 0897] part (1) needs: the
multiplicative comparison for `B̃` itself is proved, as
`Stacks.AffineGradedAlgebra.isIso_gradedTildeOfToPushforwardAlgebra`.

**No `@[stacks]` attribute is attached.** [Stacks, Tag 01LX] part (2) is proved in full
generality for a quasi-coherent algebra sheaf as
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`, and no clause of 01LX mentions a
grading; the comparison here is the plumbing between that statement and the graded input of
[Stacks, Tag 0897], exactly as recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Constructions/UngradedRealizationPullback.lean`.

**Where this belongs.** Next to
`StacksFrontier/AlgebraicGeometry/Constructions/UngradedRealizationPullback.lean`, whose
`Stacks.RelativeSpec.pullbackUnderlyingModuleIso` is the module half of the same comparison.

## Main definitions

* `Stacks.RelativeSpec.RealizationPullback.pullbackRealization`: the realization of `g^*A`, as a
  sheaf of commutative `𝒪_Z`-algebras.
* `Stacks.RelativeSpec.RealizationPullback.totalToRealization`: the ring homomorphism from the
  sections of the direct sum of the homogeneous pieces of `A` over `U` to the sections of the
  realization of `g^*A` over `g⁻¹U`.
* `Stacks.RelativeSpec.RealizationPullback.realizationPullbackHom`: **the comparison
  `(algebraPullback g).obj R(A) ⟶ R(g^*A)` of sheaves of commutative `𝒪_Z`-algebras.**
* `Stacks.RelativeSpec.RealizationPullback.pieceInclUnderlyingModule` and
  `pieceToPullbackAlgebra`: the homogeneous inclusion into the module underlying `R(A)`, and the
  degreewise family out of `g^*A` that the comparison in the *opposite* direction would be built
  from.

## Main results

* `Stacks.RelativeSpec.RealizationPullback.totalToRealization_incl` and
  `totalToRealization_structureMap`: the comparison on a homogeneous section and on the image of
  the structure map.
* `Stacks.RelativeSpec.RealizationPullback.structureMap_square`: the comparison is compatible
  with the two structure morphisms, which is what fills the pushout square.
* `Stacks.RelativeSpec.RealizationPullback.pieceToPullbackAlgebra_pullbackUnit`: that degreewise
  family on a pullback-unit image.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec.RealizationPullback

variable {Z X : Scheme.{u}} (g : Z ⟶ X) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)

/-- The degreewise map into the ungraded realization of the pulled-back algebra: a homogeneous
local section of `A` over `U` goes to its pullback-unit image over `g⁻¹U`, read in the ungraded
realization of `g^*A`. -/
def pieceToRealization (n : ℤ) (U : X.Opens) :
    (A.piece n).val.obj (op U) →+
      (Stacks.Conormal.gradedPullback g A).ungradedSheaf.obj.obj (op (g ⁻¹ᵁ U)) where
  toFun x := (Stacks.Conormal.gradedPullback g A).ungradedIncl n
    (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece n) (op U) x)
  map_zero' := by
    change (Stacks.Conormal.gradedPullback g A).ungradedIncl n
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (A.piece n)).val.app (op U) 0) = 0
    rw [map_zero]
    exact (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.inclSheaf_zero _ n
  map_add' x y := by
    change (Stacks.Conormal.gradedPullback g A).ungradedIncl n
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (A.piece n)).val.app (op U) (x + y)) = _
    rw [map_add]
    exact (Stacks.Conormal.gradedPullback g A).toPresheafGradedAlgebra.inclSheaf_add _ n _ _

/-- **The sections of the realization of `g^*A` over `g⁻¹U`, as a ring under the sections of the
direct sum of the homogeneous pieces of `A` over `U`.** The multiplicativity is
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit` and the unit is
`Stacks.RingedSpace.pullbackGradedAlgebra_one_eval`. -/
def totalToRealization (U : X.Opens) :
    A.toPresheafGradedAlgebra.Total (op U) →+*
      (Stacks.Conormal.gradedPullback g A).ungradedSheaf.obj.obj (op (g ⁻¹ᵁ U)) :=
  A.toPresheafGradedAlgebra.totalRingHomOfFamily (op U) (pieceToRealization g A · U)
    (fun i j x y =>
      Eq.trans (congrArg ((Stacks.Conormal.gradedPullback g A).ungradedIncl (i + j))
          (Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit
            g.toLRSHom.toShHom A i j U x y).symm)
        ((Stacks.Conormal.gradedPullback g A).ungradedIncl_mul i j _ _).symm)
    (Eq.trans (congrArg ((Stacks.Conormal.gradedPullback g A).ungradedIncl 0)
        (Stacks.RingedSpace.pullbackGradedAlgebra_one_eval g.toLRSHom.toShHom A U).symm)
      ((Stacks.Conormal.gradedPullback g A).ungradedIncl_one _))

/-- `totalToRealization` on a homogeneous section is the pullback-unit image read in the
realization of `g^*A`. -/
theorem totalToRealization_incl (n : ℤ) (U : X.Opens) (x : (A.piece n).val.obj (op U)) :
    totalToRealization g A U (A.toPresheafGradedAlgebra.incl n x) =
      (Stacks.Conormal.gradedPullback g A).ungradedIncl n
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece n) (op U) x) :=
  A.toPresheafGradedAlgebra.totalRingHomOfFamily_incl _ _ _ _ n x

/-- `totalToRealization` commutes with restriction along an inclusion of opens, on a homogeneous
section. -/
theorem totalToRealization_restrict (n : ℤ) {V₁ V₂ : X.Opens}
    (α : (op V₁ : (Opens ↥X)ᵒᵖ) ⟶ op V₂) (x : (A.piece n).val.obj (op V₁)) :
    totalToRealization g A V₂ (A.toPresheafGradedAlgebra.totalRestrict α
        (A.toPresheafGradedAlgebra.incl n x)) =
      ((Stacks.Conormal.gradedPullback g A).ungradedSheaf.obj.map
          ((Opens.map g.base).op.map α)).hom
        (totalToRealization g A V₁ (A.toPresheafGradedAlgebra.incl n x)) :=
  Eq.trans (congrArg (totalToRealization g A V₂)
      (A.toPresheafGradedAlgebra.totalRestrict_incl α n x))
    (Eq.trans (totalToRealization_incl g A n V₂ _)
      (Eq.trans (congrArg ((Stacks.Conormal.gradedPullback g A).ungradedIncl n)
          (Stacks.RingedSpace.pullbackUnit_restrict g.toLRSHom.toShHom (A.piece n) α x).symm)
        (Eq.trans ((Stacks.Conormal.gradedPullback g A).ungradedIncl_naturality
            ((Opens.map g.base).op.map α) n _).symm
          (congrArg (((Stacks.Conormal.gradedPullback g A).ungradedSheaf.obj.map
              ((Opens.map g.base).op.map α)).hom)
            (totalToRealization_incl g A n V₁ x).symm))))

/-- `totalToRealization` carries the structure map `r ↦ r · 1` of the realization of `A` to the
structure map of the realization of `g^*A`, read over the preimage. -/
theorem totalToRealization_structureMap (U : X.Opens)
    (r : X.ringCatSheaf.obj.obj (op U)) :
    totalToRealization g A U (A.toPresheafGradedAlgebra.structureMap (op U) r) =
      ((Stacks.Conormal.gradedPullback g A).ungradedStructureMap.hom.app
        (op (g ⁻¹ᵁ U))).hom (Stacks.RingedSpace.sharp g.toLRSHom.toShHom (op U) r) := by
  have h1 : A.toPresheafGradedAlgebra.structureMap (op U) r =
      A.toPresheafGradedAlgebra.incl 0 (r • A.toPresheafGradedAlgebra.one.eval (op U)) :=
    (A.toPresheafGradedAlgebra.incl_smul 0 r
      (A.toPresheafGradedAlgebra.one.eval (op U))).symm
  refine Eq.trans (congrArg (totalToRealization g A U) h1) ?_
  refine Eq.trans (totalToRealization_incl g A 0 U _) ?_
  refine Eq.trans (congrArg ((Stacks.Conormal.gradedPullback g A).ungradedIncl 0) ?_)
    ((Stacks.Conormal.gradedPullback g A).ungradedIncl_smul_one (op (g ⁻¹ᵁ U))
      (Stacks.RingedSpace.sharp g.toLRSHom.toShHom (op U) r))
  exact Eq.trans (Stacks.RingedSpace.pullbackUnit_smul g.toLRSHom.toShHom (A.piece 0) (op U) r _)
    (congrArg (fun y => Stacks.RingedSpace.sharp g.toLRSHom.toShHom (op U) r • y)
      (Stacks.RingedSpace.pullbackGradedAlgebra_one_eval g.toLRSHom.toShHom A U).symm)

variable (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
  (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

/-- **The ungraded realization of the degreewise pullback `g^*A`, as a sheaf of commutative
`𝒪_Z`-algebras.** -/
abbrev pullbackRealization : Stacks.RelativeSpec.AlgebraSheaf Z :=
  Stacks.RelativeSpec.gradedAlgebraSheaf Z (Stacks.Conormal.gradedPullback g A)
    (Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm g.toLRSHom.toShHom A hc)

/-- The pushforward along `g` of the realization of `g^*A`, as a sheaf of rings on `X`: the
target of the transposed comparison. -/
abbrev pullbackRealizationTarget :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology (X : TopCat))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
    ((TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj (pullbackRealization g A hc).right)

/-- The transposed comparison as a morphism of presheaves of rings out of the direct sum of the
homogeneous pieces of `A`. -/
def realizationPullbackPresheafHom :
    A.toPresheafGradedAlgebra.totalPresheaf ⟶ (pullbackRealizationTarget g A hc).obj where
  app W := RingCat.ofHom (totalToRealization g A W.unop)
  naturality W₁ W₂ α := by
    obtain ⟨V₁⟩ := W₁
    obtain ⟨V₂⟩ := W₂
    refine RingCat.hom_ext (RingHom.ext fun a => ?_)
    change totalToRealization g A V₂ (A.toPresheafGradedAlgebra.totalRestrict α a) =
      ((Stacks.Conormal.gradedPullback g A).ungradedSheaf.obj.map
        ((Opens.map g.base).op.map α)).hom (totalToRealization g A V₁ a)
    induction a using A.toPresheafGradedAlgebra.incl_induction with
    | zero =>
      refine Eq.trans (congrArg (totalToRealization g A V₂)
        (map_zero (A.toPresheafGradedAlgebra.totalRestrictRingHom α))) ?_
      refine Eq.trans (map_zero (totalToRealization g A V₂)) ?_
      refine Eq.trans (map_zero (((Stacks.Conormal.gradedPullback g A).ungradedSheaf.obj.map
        ((Opens.map g.base).op.map α)).hom)).symm ?_
      exact congrArg (((Stacks.Conormal.gradedPullback g A).ungradedSheaf.obj.map
        ((Opens.map g.base).op.map α)).hom) (map_zero (totalToRealization g A V₁)).symm
    | incl n x => exact totalToRealization_restrict g A n α x
    | add a b ha hb =>
      rw [map_add, map_add, map_add, ha, hb]
      exact (map_add _ _ _).symm

/-- The transposed comparison as a morphism of sheaves of rings: `realizationPullbackPresheafHom`
extended across the sheafification, which is possible because the target is a sheaf. -/
def ungradedRealizationHom : A.ungradedSheaf ⟶ pullbackRealizationTarget g A hc :=
  A.toPresheafGradedAlgebra.totalSheafLift (Opens.grothendieckTopology (X : TopCat))
    (pullbackRealizationTarget g A hc) (realizationPullbackPresheafHom g A hc)

/-- The morphism of sheaves of rings is `totalToRealization` on the sheafification unit. -/
theorem ungradedRealizationHom_totalUnit (U : X.Opens)
    (a : A.toPresheafGradedAlgebra.Total (op U)) :
    ((ungradedRealizationHom g A hc).hom.app (op U)).hom
        (A.toPresheafGradedAlgebra.totalUnit
          (Opens.grothendieckTopology (X : TopCat)) (op U) a) =
      totalToRealization g A U a :=
  congrArg (fun φ => RingCat.Hom.hom (NatTrans.app φ (op U)) a)
    (Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift A.toPresheafGradedAlgebra
      (Opens.grothendieckTopology (X : TopCat)) _ (realizationPullbackPresheafHom g A hc))

/-- **The transposed comparison**, as a morphism of sheaves of commutative rings from the
realization of `A` to the pushforward along `g` of the realization of `g^*A`. -/
def toPushforwardRealization :
    (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj (pullbackRealization g A hc).right :=
  Stacks.CommRingSheaf.homMk' _ (A.mul_comm_ungradedSheaf hc) (ungradedRealizationHom g A hc)

/-- The comparison out of the inverse image: the adjoint transpose of
`toPushforwardRealization`. This is the leg of the pushout square out of `g⁻¹R(A)`. -/
def inverseImageToRealization :
    (TopCat.Sheaf.pullback CommRingCat.{u} g.base).obj
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).right ⟶
      (pullbackRealization g A hc).right :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv _ _).symm
    (toPushforwardRealization g A hc)

/-- The structural map of `g` on structure sheaves, as a morphism into the pushforward. It is
the adjoint transpose of `AlgebraicGeometry.inverseImageStructureMap`. -/
def toPushforwardStructureSheaf :
    X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj Z.sheaf := ⟨g.c⟩

/-- **The transposed comparison is compatible with the two structure morphisms**: the structure
map of the realization of `A` followed by the comparison is the structural map of `g` followed by
the structure map of the realization of `g^*A`. -/
theorem structureMap_square :
    (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).hom ≫ toPushforwardRealization g A hc =
      toPushforwardStructureSheaf g ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
        (pullbackRealization g A hc).hom := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => CommRingCat.hom_ext
    (RingHom.ext fun r => ?_)))
  refine Eq.trans (ungradedRealizationHom_totalUnit g A hc W.unop
    (A.toPresheafGradedAlgebra.structureMap W r)) ?_
  exact totalToRealization_structureMap g A W.unop r

/-- The pushout square of [Stacks, Tag 01SA] that exhibits `algebraPullback` as extension of
scalars, filled in by the comparison: this is `structureMap_square` transposed back. -/
theorem algebraPullback_square :
    (TopCat.Sheaf.pullback CommRingCat.{u} g.base).map
        (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc).hom ≫
      inverseImageToRealization g A hc =
    inverseImageStructureMap g ≫ (pullbackRealization g A hc).hom :=
  Eq.trans ((Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans
      (congrArg ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).homEquiv
        X.sheaf (pullbackRealization g A hc).right).symm (structureMap_square g A hc)))
    (Adjunction.homEquiv_naturality_right_symm _ _ _)

/-- **The comparison of the algebra pullback of the ungraded realization of `A` with the ungraded
realization of the degreewise pullback `g^*A`**, as a morphism of sheaves of commutative
`𝒪_Z`-algebras.

It is the `IsPushout.desc` of `Stacks.AffineAlgebraEquivalence.algebraPullback_isPushout` at the
two legs `inverseImageToRealization` and the structure morphism of the target, which agree on
`g⁻¹𝒪_X` by `algebraPullback_square`. Invertibility is not asserted; see the implementation
notes. -/
def realizationPullbackHom :
    (algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc) ⟶
      pullbackRealization g A hc :=
  Under.homMk ((algebraPullback_isPushout g
      (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).desc
      (inverseImageToRealization g A hc) (pullbackRealization g A hc).hom
      (algebraPullback_square g A hc))
    ((algebraPullback_isPushout g (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).inr_desc _ _ _)

/-! ### Towards the inverse comparison -/

/-- The homogeneous inclusion of a piece into the `𝒪_X`-module underlying the realization: a
homogeneous local section, read in the ungraded realization by
`SheafOfModules.GradedAlgebra.ungradedIncl`.

It is `𝒪_X`-linear because a scalar multiple of a homogeneous section is the product with the
image of the scalar under the structure map
(`SheafOfModules.GradedAlgebra.ungradedIncl_smul`), which is exactly how the underlying module
restricts its scalars, and natural by
`SheafOfModules.GradedAlgebra.ungradedIncl_naturality`. Giving the morphism by this formula
rather than as the `n`-th leg of
`Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule` is what makes
`pieceInclUnderlyingModule_app` available, and every statement below about the inverse
comparison is proved by computing on homogeneous sections. -/
def pieceInclUnderlyingModule (n : ℤ) :
    A.piece n ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
      (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc) where
  val :=
    { app := fun W => ModuleCat.ofHom
        (X := (A.piece n).val.obj W)
        (Y := (Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
          (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)).val.obj W)
        { toFun := fun x => A.ungradedIncl n x
          map_add' := fun x y => A.ungradedIncl_add n W x y
          map_smul' := fun r x => A.ungradedIncl_smul n W r x }
      naturality := fun {_ _} f => ModuleCat.hom_ext (LinearMap.ext fun x =>
        (A.ungradedIncl_naturality f n x).symm) }

/-- `pieceInclUnderlyingModule` on a local section is `ungradedIncl`. -/
@[simp] theorem pieceInclUnderlyingModule_app (n : ℤ) (W : (Opens ↥X)ᵒᵖ)
    (x : (A.piece n).val.obj W) :
    (pieceInclUnderlyingModule A hc n).val.app W x = A.ungradedIncl n x :=
  rfl

/-- The degreewise family the inverse comparison needs: a morphism of `𝒪_Z`-modules from the
degree-`n` piece of `g^*A` to the module underlying the algebra pullback of the realization
of `A`.

It is `g^*` of `pieceInclUnderlyingModule` followed by
`Stacks.FundamentalGroup.algebraPullbackModuleComparison`, the canonical morphism
`g^*(module underlying E) ⟶ module underlying ((algebraPullback g).obj E)`
(`StacksFrontier/AlgebraicGeometry/EtaleAlgebra/FlatBaseChange/AlgebraComparison.lean:187`), which
is unconditional: it is the adjoint transpose of the module underlying the unit of
`Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction`, and it needs neither the
module underlying a pushout to be described nor the inverse image of a module to be identified.
The implementation notes of
`StacksFrontier/AlgebraicGeometry/Constructions/UngradedRealizationPullback.lean` record the
module-side route as blocked, on
`Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso`; that is right for an
*isomorphism* of underlying modules and not for the morphism, which is all this needs. -/
def pieceToPullbackAlgebra (n : ℤ) :
    (Stacks.Conormal.gradedPullback g A).piece n ⟶
      Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) :=
  (Scheme.Modules.pullback g).map (pieceInclUnderlyingModule A hc n) ≫
    Stacks.FundamentalGroup.algebraPullbackModuleComparison g
      (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)

/-- **The degreewise family on a pullback-unit image** is the homogeneous inclusion followed by
the module underlying the unit of the algebra base-change adjunction.

This is `Adjunction.homEquiv_unit` for
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`: the transpose of
`pieceToPullbackAlgebra` is `pieceInclUnderlyingModule` followed by the module underlying that
unit. It is the identity on which multiplicativity of the family would be checked, products of
pullback-unit
images being pullback-unit images of products
(`Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit`), the inclusion being
multiplicative across degrees (`SheafOfModules.GradedAlgebra.ungradedIncl_mul`) and the unit
being a morphism of algebra sheaves; extending from pullback-unit images to all local sections
is what `Stacks.RingedSpace.pullbackBilinear_heq_ext` is for. -/
theorem pieceToPullbackAlgebra_pullbackUnit (n : ℤ) (U : X.Opens)
    (x : (A.piece n).val.obj (op U)) :
    (pieceToPullbackAlgebra g A hc n).val.app (op (g ⁻¹ᵁ U))
        (Stacks.RingedSpace.pullbackUnit g.toLRSHom.toShHom (A.piece n) (op U) x) =
      (pieceInclUnderlyingModule A hc n ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app
          (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))).val.app (op U) x :=
  have h1 : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (pieceToPullbackAlgebra g A hc n) =
      pieceInclUnderlyingModule A hc n ≫ Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap
        ((algebraPullbackPushforwardAdjunction g).unit.app
          (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)) :=
    Eq.trans (Adjunction.homEquiv_naturality_left _ _ _)
      (congrArg (fun k => pieceInclUnderlyingModule A hc n ≫ k)
        (Stacks.FundamentalGroup.homEquiv_algebraPullbackModuleComparison g
          (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc)))
  congrArg (fun φ : A.piece n ⟶ (Scheme.Modules.pushforward g).obj
      (Stacks.RelativeSpec.AlgebraSheaf.underlyingModule
        ((algebraPullback g).obj (Stacks.RelativeSpec.gradedAlgebraSheaf X A hc))) =>
    φ.val.app (op U) x)
    (Eq.trans (Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction g) _ _
      (pieceToPullbackAlgebra g A hc n)).symm h1)

end Stacks.RelativeSpec.RealizationPullback

end
