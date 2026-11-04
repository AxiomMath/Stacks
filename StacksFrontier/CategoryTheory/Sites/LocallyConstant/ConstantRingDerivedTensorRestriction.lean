module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantRingDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesDerivedCompatibility

/-!
# The derived tensor product of sheaves of `Λ`-modules commutes with restriction to a slice

Let `(C, J)` be a small site, `Λ` a commutative ring, `R` a sheaf of commutative rings on `C`
and `α` a locally bijective morphism from the constant presheaf of rings on `Λ` to the sheaf of
rings underlying `R`. `StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantRingDerivedTensor`
carries the derived tensor product of Stacks 06YU across the resulting identification of sheaves
of modules over `R` with sheaves of `Λ`-modules, giving
`Stacks.ConstantRingModules.derivedTensor` on `D(Sheaf J (ModuleCat Λ))`.

`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction` proves
that the derived tensor product of sheaves of modules over a ringed site commutes with
restriction to a slice site, as the natural isomorphism
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso`. This file transports that
statement across the identification, so that it reads on `D(Sheaf J (ModuleCat Λ))`:

`(K ⊗^L_R L)|_U ≅ K|_U ⊗^L_{R|_U} L|_U`.

## Main definitions

* `Stacks.ConstantRingModules.toModuleSheafInvOverIso`: **the mate of the slicing square**. The
  square `Stacks.ConstantRingModules.toModuleSheafOverIso` compares the *functors* of the two
  equivalences `Stacks.ConstantRingModules.moduleSheafEquivalence` with restriction to a slice;
  this is the corresponding square for their *inverses*.
* `Stacks.ConstantRingModules.toModuleSheafInvOverDerivedIso`: the mate on derived categories.
* `Stacks.ConstantRingModules.derivedTensorOverObjIso`: **the transported slice compatibility**,
  at a pair of objects of `D(Sheaf J (ModuleCat Λ))`.
* `Stacks.ConstantRingModules.constantDerivedTensorOverObjIso`: the same for
  `Stacks.ConstantRingModules.constantDerivedTensor`, the derived tensor product over the
  constant sheaf of commutative rings on `Λ` that Stacks 094H and 094I are about.

## Implementation notes

**Why a mate.** `derivedTensor` is `tensorBackward ⋙ T.tensor ⋙ … ⋙ tensorForward`, so reading
a comparison of bifunctors on `D(Mod(R))` as one on `D(Sheaf J (ModuleCat Λ))` needs the slicing
square in three slots, and only the outer one is
`Stacks.ConstantRingModules.toModuleSheafOverDerivedIso` as stated: the two inner slots are
whiskered by the comparison of the *inverse* equivalence with restriction. That is the mate of
`toModuleSheafOverIso` along the two adjunctions of `moduleSheafEquivalence`, and it is
Mathlib's `CategoryTheory.mateEquiv`, not a hand-rolled construction.

The mate of an invertible square need not be invertible — that is the Beck–Chevalley phenomenon
— but it is here, both adjunctions being those of equivalences. The step is
`Stacks.CategoryTheory.isIso_map_mateEquiv_app_of_isIso_map_counit` of
`StacksFrontier.CategoryTheory.Adjunction.Mates`, which reads
`CategoryTheory.mateEquiv_counit` as a factorization and concludes that the equivalence's
functor carries the component of the mate to an isomorphism; that functor reflects
isomorphisms, which is the one thing it leaves to the caller and which its docstring records as
left open. The general statement
`Stacks.CategoryTheory.isIso_mateEquiv_natTrans` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction` is the same
conclusion packaged, and is *not* used here only because importing it would put the whole étale
cohomology closure under this module, and hence under any future module that discharges the
`hbounded` hypothesis of
`isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor_of_bounded`
in this namespace — which lives in `ConstantRingDerivedTensor` and would therefore have to
import it.

**No new ringed site.** `derivedTensorRestrictNatIso` is stated for an
`AlgebraicGeometry.RingedSite`, while `derivedTensor` is indexed by the sheaf of commutative
rings alone. The ringed site is therefore built as an anonymous structure inside the proof of
`derivedTensorOverObjIso` and appears in no statement, so neither
`Stacks.SheafOfModules.ringedSiteOf` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalDual` (which packages a *presheaf*
together with the `RingCat`-valued sheaf condition, so that its structure sheaf is not the given
`R` on the nose) nor `AlgebraicGeometry.RingedSite.constantRingedSite` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfAConstantComplex` (which is
fixed at universe `0` and at the constant sheaf) has to be reconciled with it.

**The respelling of the restricted ring map.** `Stacks.ConstantRingModules.overRingMap` has
target `(R'.over U).obj` for the sheaf of rings `R'`, whereas `derivedTensor` over `R.over U`
asks for a morphism into `(Stacks.SheafOfModules.Tensor.ringSheaf (R.over U)).obj`. The two are
equal by `rfl` but not at reducible transparency, so instance resolution does not carry
`Presheaf.IsLocallyInjective` and `IsLocallySurjective` across; `tensorOverRingMap` is
`overRingMap` with the second type ascribed, and the two instances are seated on it.

**What is not proved.** This file supplies one of the inputs the *bounded* case of Stacks 094H
needs — the one the "What is not proved" note of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove` records as the
conjugation that is not written. It does not prove that bounded case, and no `@[stacks]`
attribute is attached here. A compatibility of a derived tensor product with restriction to a
slice site is not a statement of the source at this point; Stacks 08JB is the corresponding
statement for the derived internal Hom.

The ringed-space analogue of the objectwise form, for an open subset of a ringed space and the
K-flat bifunctor construction of the derived tensor product rather than the data of Stacks 06YU,
is `Stacks.Cohomology.RestrictOpenDerivedTensor.derivedTensorRestrictObjIso` in
`StacksFrontier.Topology.Sheaves.Cohomology.KFlat.RestrictOpenDerivedTensor`; it is about a
different category and a different bifunctor and neither implies the other.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules Stacks.ConstantSheaf

-- Exactness of restriction of sheaves of modules to a slice, which
-- `CategoryTheory.Functor.mapDerivedCategory` of that functor asks for. The two declarations are
-- `local instance`s of
-- `StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesDerivedCompatibility`, so they are
-- not in instance scope here and have to be re-seated; re-declaring them would duplicate them.
attribute [local instance] preservesFiniteLimitsModuleSheafOverFunctor
  preservesFiniteColimitsModuleSheafOverFunctor

/-! ### The mate of the slicing square -/

section Mate

universe d u

variable {C : Type u} [Category.{u} C] (Λ : Type u) [Ring Λ]
  (J : GrothendieckTopology C) {R : Sheaf J RingCat.{u}}
  (α : constRing (C := C) Λ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J (ModuleCat.{u} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} R)]
  [HasDerivedCategory.{d} (Sheaf J (ModuleCat.{u} Λ))]
  [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{u}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (U : C)
  [HasWeakSheafify (J.over U) (ModuleCat.{u} Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} (R.over U))]
  [HasDerivedCategory.{d} (Sheaf (J.over U) (ModuleCat.{u} Λ))]

/-- The functor of `Stacks.ConstantRingModules.moduleSheafEquivalence` is additive: it is
`toModuleSheaf`, which is, but `moduleSheafEquivalence` is a `def` and instance resolution does
not unfold it. -/
local instance additive_moduleSheafEquivalence_functor :
    (moduleSheafEquivalence.{u} Λ J α).functor.Additive :=
  inferInstanceAs (toModuleSheaf.{u} Λ J α).Additive

/-- The inverse of `Stacks.ConstantRingModules.moduleSheafEquivalence` is additive, being the
inverse of an equivalence with additive functor. -/
local instance additive_moduleSheafEquivalence_inverse :
    (moduleSheafEquivalence.{u} Λ J α).inverse.Additive :=
  (moduleSheafEquivalence.{u} Λ J α).inverse_additive

/-- The functor of `Stacks.ConstantRingModules.moduleSheafEquivalence` reflects isomorphisms,
being an equivalence; seated for the same reason as its additivity. -/
local instance reflectsIsomorphisms_moduleSheafEquivalence_functor :
    (moduleSheafEquivalence.{u} Λ J α).functor.ReflectsIsomorphisms :=
  inferInstanceAs (toModuleSheaf.{u} Λ J α).ReflectsIsomorphisms

/-- **The mate of the slicing square of the two readings of a sheaf of `Λ`-modules.**
`Stacks.ConstantRingModules.toModuleSheafOverIso` is the square

`toModuleSheaf ⋙ (-)|_U ≅ (-)|_U ⋙ toModuleSheaf`

for the *functors* of the equivalences `Stacks.ConstantRingModules.moduleSheafEquivalence` over
`C` and over `C/U`. This is the square for their *inverses*, which is what the two inner slots of
a conjugated bifunctor are whiskered by. It is `CategoryTheory.mateEquiv` of the inverse of that
square, invertible because both adjunctions are those of equivalences. -/
def toModuleSheafInvOverIso :
    (moduleSheafEquivalence.{u} Λ J α).inverse ⋙ _root_.SheafOfModules.overFunctor.{u} R U ≅
      J.overPullback (ModuleCat.{u} Λ) U ⋙
        (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).inverse :=
  haveI hsqapp : ∀ V, IsIso ((TwoSquare.mk (_root_.SheafOfModules.overFunctor.{u} R U)
      (moduleSheafEquivalence.{u} Λ J α).functor
      (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).functor
      (J.overPullback (ModuleCat.{u} Λ) U)
      (toModuleSheafOverIso.{u} Λ J α U).inv).app V) := fun V =>
    inferInstanceAs (IsIso ((toModuleSheafOverIso.{u} Λ J α U).symm.hom.app V))
  haveI hcounit : IsIso (moduleSheafEquivalence.{u} Λ J α).toAdjunction.counit := by
    dsimp [Equivalence.toAdjunction]; infer_instance
  haveI hcounitU : IsIso (moduleSheafEquivalence.{u} Λ (J.over U)
      (overRingMap Λ J α U)).toAdjunction.counit := by
    dsimp [Equivalence.toAdjunction]; infer_instance
  haveI happ : ∀ W, IsIso ((mateEquiv (moduleSheafEquivalence.{u} Λ J α).toAdjunction
      (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).toAdjunction
      (TwoSquare.mk (_root_.SheafOfModules.overFunctor.{u} R U)
        (moduleSheafEquivalence.{u} Λ J α).functor
        (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).functor
        (J.overPullback (ModuleCat.{u} Λ) U)
        (toModuleSheafOverIso.{u} Λ J α U).inv)).app W) := by
    intro W
    have := Stacks.CategoryTheory.isIso_map_mateEquiv_app_of_isIso_map_counit
      (moduleSheafEquivalence.{u} Λ J α).toAdjunction
      (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).toAdjunction
      (TwoSquare.mk (_root_.SheafOfModules.overFunctor.{u} R U)
        (moduleSheafEquivalence.{u} Λ J α).functor
        (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).functor
        (J.overPullback (ModuleCat.{u} Λ) U)
        (toModuleSheafOverIso.{u} Λ J α U).inv) W
    exact isIso_of_reflects_iso _
      (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).functor
  haveI : IsIso (mateEquiv (moduleSheafEquivalence.{u} Λ J α).toAdjunction
      (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).toAdjunction
      (TwoSquare.mk (_root_.SheafOfModules.overFunctor.{u} R U)
        (moduleSheafEquivalence.{u} Λ J α).functor
        (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).functor
        (J.overPullback (ModuleCat.{u} Λ) U)
        (toModuleSheafOverIso.{u} Λ J α U).inv)) :=
    NatIso.isIso_of_isIso_app _
  asIso (mateEquiv (moduleSheafEquivalence.{u} Λ J α).toAdjunction
    (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).toAdjunction
    (TwoSquare.mk (_root_.SheafOfModules.overFunctor.{u} R U)
      (moduleSheafEquivalence.{u} Λ J α).functor
      (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).functor
      (J.overPullback (ModuleCat.{u} Λ) U)
      (toModuleSheafOverIso.{u} Λ J α U).inv))

/-- **The mate of the slicing square, on derived categories.**
`Stacks.ConstantRingModules.toModuleSheafInvOverIso` pushed through
`CategoryTheory.Functor.mapDerivedCategory` by the functoriality package of
`StacksFrontier.RingTheory.Dualizing.MapDerivedCategory`, exactly as
`Stacks.ConstantRingModules.toModuleSheafOverDerivedIso` is the push of the square itself. -/
def toModuleSheafInvOverDerivedIso :
    (moduleSheafEquivalence.{u} Λ J α).inverse.mapDerivedCategory ⋙
        (_root_.SheafOfModules.overFunctor.{u} R U).mapDerivedCategory ≅
      (J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory ⋙
        (moduleSheafEquivalence.{u} Λ (J.over U)
          (overRingMap Λ J α U)).inverse.mapDerivedCategory :=
  Dualizing.mapDerivedCategoryCompNatIso (moduleSheafEquivalence.{u} Λ J α).inverse
      (_root_.SheafOfModules.overFunctor.{u} R U)
      (J.overPullback (ModuleCat.{u} Λ) U ⋙
        (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).inverse)
      (toModuleSheafInvOverIso.{u} Λ J α U) ≪≫
    Dualizing.mapDerivedCategoryComp (J.overPullback (ModuleCat.{u} Λ) U)
      (moduleSheafEquivalence.{u} Λ (J.over U) (overRingMap Λ J α U)).inverse

end Mate

/-! ### The transported slice compatibility -/

section Tensor

universe u

open Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] _root_.SheafOfModules.instAbelian
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (Λ : Type u) [CommRing Λ] (R : Sheaf J CommRingCat.{u})
  (α : constRing (C := C) Λ ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasWeakSheafify J (ModuleCat.{u} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{u}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (U : C)
  [HasWeakSheafify (J.over U) (ModuleCat.{u} Λ)]
  [(J.over U).WEqualsLocallyBijective (ModuleCat.{u} Λ)]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- The restriction to the slice site of the morphism out of the constant presheaf of rings,
with its target written as the sheaf of rings underlying `R.over U`, which is the spelling
`Stacks.ConstantRingModules.derivedTensor` over `R.over U` asks for. It is
`Stacks.ConstantRingModules.overRingMap` with that type ascribed; the two targets are equal by
`rfl`, but not at the transparency instance resolution uses, so the two local-bijectivity
instances have to be seated again at this spelling. -/
def tensorOverRingMap : constRing (C := Over U) Λ ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (R.over U)).obj :=
  overRingMap Λ J α U

/-- The morphism `tensorOverRingMap Λ R α U` is locally injective for the slice topology. -/
instance isLocallyInjective_tensorOverRingMap :
    Presheaf.IsLocallyInjective (J.over U) (tensorOverRingMap Λ R α U) :=
  isLocallyInjective_overRingMap Λ J α U

/-- The morphism `tensorOverRingMap Λ R α U` is locally surjective for the slice topology. -/
instance isLocallySurjective_tensorOverRingMap :
    Presheaf.IsLocallySurjective (J.over U) (tensorOverRingMap Λ R α U) :=
  isLocallySurjective_overRingMap Λ J α U

/-- **The derived tensor product of sheaves of `Λ`-modules commutes with restriction to a slice
site**, at a pair of objects:

`(K ⊗^L_R L)|_U ≅ K|_U ⊗^L_{R|_U} L|_U`.

`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` is the same statement for
sheaves of modules over a ringed site; this is it read through the identification of those with
sheaves of `Λ`-modules, which is what
`Stacks.ConstantRingModules.derivedTensor` is defined by conjugating. The outer slot of the
conjugation is `Stacks.ConstantRingModules.toModuleSheafOverDerivedIso` and the two inner ones
are its mate `Stacks.ConstantRingModules.toModuleSheafInvOverDerivedIso`. -/
def derivedTensorOverObjIso (K L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    (J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj
        (((derivedTensor Λ R α).obj K).obj L) ≅
      ((derivedTensor Λ (R.over U) (tensorOverRingMap Λ R α U)).obj
          ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj K)).obj
        ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj L) :=
  (toModuleSheafOverDerivedIso Λ J α U).app
      (((canonicalDerivedTensorProduct R).tensor.obj
        ((tensorBackward Λ R α).obj K)).obj ((tensorBackward Λ R α).obj L)) ≪≫
    (toModuleSheaf.{u} Λ (J.over U) (overRingMap Λ J α U)).mapDerivedCategory.mapIso
      ((Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso
            ({ C := C, J := J, O := R } : RingedSite.{u, u, u}) U
            (canonicalDerivedTensorProduct R)
            (canonicalDerivedTensorProduct (R.over U))).app
          ((tensorBackward Λ R α).obj K, (tensorBackward Λ R α).obj L) ≪≫
        ((canonicalDerivedTensorProduct (R.over U)).tensor.mapIso
            ((toModuleSheafInvOverDerivedIso Λ J α U).app K)).app
          ((_root_.SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) U).mapDerivedCategory.obj
              ((tensorBackward Λ R α).obj L)) ≪≫
        ((canonicalDerivedTensorProduct (R.over U)).tensor.obj
            ((tensorBackward Λ (R.over U) (tensorOverRingMap Λ R α U)).obj
              ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj K))).mapIso
          ((toModuleSheafInvOverDerivedIso Λ J α U).app L))

/-- **The derived tensor product over the constant sheaf of commutative rings on `Λ` commutes
with restriction to a slice site**, at a pair of objects. This is
`Stacks.ConstantRingModules.derivedTensorOverObjIso` at the bifunctor
`Stacks.ConstantRingModules.constantDerivedTensor` that Stacks 094H and 094I are about, which is
the form in which an argument local on the site consumes it. -/
def constantDerivedTensorOverObjIso (K L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    (J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj
        (((constantDerivedTensor J Λ).obj K).obj L) ≅
      ((derivedTensor Λ ((constantCommRingSheaf J Λ).over U)
            (tensorOverRingMap Λ (constantCommRingSheaf J Λ)
              (constantTensorRingMap J Λ) U)).obj
          ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj K)).obj
        ((J.overPullback (ModuleCat.{u} Λ) U).mapDerivedCategory.obj L) :=
  derivedTensorOverObjIso Λ (constantCommRingSheaf J Λ) (constantTensorRingMap J Λ) U K L

end Tensor

end Stacks.ConstantRingModules

end
