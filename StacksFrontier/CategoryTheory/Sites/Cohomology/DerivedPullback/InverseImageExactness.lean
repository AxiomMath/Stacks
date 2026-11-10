module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageChangeOfRings
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the inverse image of sheaves of modules at the geometric half of a pullback

The Stacks 0G6R reduction reduces Stacks 0G6R to two inputs, one of which
is `Stacks.Sheaves.InverseImageExactness.InverseImagePreservesShortExact f`: exactness of
`(StacksPullbackFactorization.auxHomG f).pullbackTopos`, the inverse image of sheaves of
modules with **no change of rings**, for a morphism of ringed topoi whose underlying continuous
functor is a morphism of sites.  **This file discharges that input.**

## What had to be proved, and where it was

The obstruction recorded in that file and in the 05VD reduction is Stacks 00YR at module level:
the underlying abelian sheaf of `SheafOfModules.pullback φ` is the abelian inverse image of the
underlying abelian sheaf, for `φ` the **unit** of the inverse-image/direct-image adjunction on
sheaves of commutative rings.  The *general* form of that comparison is disproved in this tree
(`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`, orders 2 versus 4 at one object of a
`Bool` site), so only the unit case can hold, and the counterexample sits exactly where the
adjoint of the structure map is the counit rather than an identity.

The route taken here never compares abelian-group structures.  Instead it identifies
`(auxHomG f).pullbackTopos` with the inverse image of sheaves of modules *as this development
already builds it* for a morphism of topoi,
`Stacks.Sheaves.RingedToposModules.inverseImageModules`, whose underlying sheaf of **sets** is
`f⁻¹` of the underlying sheaf of sets definitionally.  Exactness of that functor is
`Stacks.Sheaves.RingedToposModules.shortExact_map_inverseImageModules` (Stacks 04JC for sheaves
of modules).  So the work in this file is the
identification, in three stages.

* **Rings.**  `ringCompare` compares the two inverse images of the structure sheaf of `Y`:
  Mathlib's `Functor.sheafPullback CommRingCat` (which `StacksPullbackFactorization.invRing`
  uses) and this development's transported one
  (`Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf`).  Both are left adjoints of the direct
  image — the second by `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, the first by
  `Functor.sheafAdjunctionContinuous` — and the two direct images agree by
  `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, so `Adjunction.leftAdjointUniq` makes
  the comparison an isomorphism.
* **The structure map.**  `fSharpRing_eq` says that `(auxHomG f).fSharpRing` is the transported
  unit followed by the direct image of `ringCompare`.  This is `leftAdjointUniq`'s
  compatibility with units (`Adjunction.unit_leftAdjointUniq_hom_app`), pushed through
  `forget₂ CommRingCat RingCat`, which is fully faithful on sheaves.
* **Modules.**  `pushforwardIso` turns the pushforward of sheaves of modules along
  `(auxHomG f).fSharpRing` into restriction of scalars along `ringCompare` followed by
  `directImageModules`.  Every step is an instance of `SheafOfModules.pushforwardComp` (which
  is `Iso.refl`) or of `Stacks.Sheaves.ToposPullback.restrictionModuleIso`.  Uniqueness of left
  adjoints then transports exactness.

## Main results

* `Stacks.Sheaves.InverseImageExactness.ringCompare`: the two inverse images of the structure sheaf
  agree, as sheaves
  of rings.
* `Stacks.Sheaves.InverseImageExactness.fSharpRing_eq`: the structure map of the geometric half of
  the factorization,
  expressed through that comparison and the unit.
* `Stacks.Sheaves.InverseImageExactness.pullbackIsoInverseImageModules`: **the identification.**
  `(auxHomG f).pullbackTopos` is the inverse image of sheaves of modules along the underlying
  morphism of topoi, read over `f⁻¹O_Y` through the comparison of rings.
* `Stacks.Sheaves.InverseImageExactness.preservesFiniteLimits_pullbackTopos_auxHomG`: **Stacks 00YR
  at module level,
  in the form the chain needs.**  `g^*` is left exact.
* `Stacks.Sheaves.InverseImageExactness.inverseImagePreservesShortExact`: **the input of the
  Stacks 0G6R reduction is discharged**, with no hypothesis beyond the morphism-of-sites
  condition that the predicate itself carries.
* `Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact`: **Stacks 0G6R from
  universally quantified
  Stacks 05VD alone.**  One of the two open inputs of
  `Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact_of_univ` is now closed.
* `Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex`: the K-flatness assertion of Tag
  0G7E on universally
  quantified Stacks 05VD alone.

## Implementation notes

**Explicit implicit arguments are load-bearing here.**  Written with the
implicit sheaves of rings left to unification, the single declaration `restrictScalarsCompIso`
below does not finish elaborating in six minutes; with `S`, `R` and `R'` supplied it costs under
six thousand heartbeats.  The mechanism is that `SheafOfModules.pushforward`'s structure map has
type `S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R`, so leaving `R` open asks the
unifier to solve `(F.sheafPushforwardContinuous RingCat J K).obj ?R` against a large
transported sheaf of rings.  For the same reason **no composite identification is stated as one
ascribed isomorphism**: `directImageModulesIso` and `pushforwardIso` are assembled from eight
declarations, each of which is a single `pushforwardComp`, `pushforwardCongr` or whiskering.
Stating the same isomorphism in one step, leaving the chain to definitional
unfolding, also does not terminate.  Each piece costs a few thousand heartbeats, so the file
needs no elaboration-budget guard of any kind.

**The second failure of the composite form was in the KERNEL, not the elaborator, and that
distinction matters.**  Written as a single `≪≫` chain with an ascribed type,
`directImageModulesIso` *elaborated* and then failed with `(kernel) deterministic timeout`: the
elaborator's unifier caches the functor-composition definitional checks, the kernel re-does them
from scratch on the finished term.  Raising an elaboration budget would not have helped, and the
fix is structural — state the three steps separately, each with its type written out, so that
every join in the final `≪≫` is syntactic and the kernel has nothing to compute.  The
abbreviations `ringU`, `restrRing`, `restrMod` and `unitRestricted` exist for the same reason:
they make the adjacent types in the chain equal as written rather than merely definitionally.

**`toposHom` is written out as a structure instance rather than taken as
`hmos.morphismOfTopoi`.**  `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi` is a
`def`, so `hmos.morphismOfTopoi.pushforward` does not reduce at reducible or instance
transparency and every lemma stated for `Functor.sheafPushforwardContinuous` fails to apply to
it.  Written as an `abbrev` whose fields are the Mathlib functors, the projections reduce and
`restrictionCommRingIso` applies on the nose.  The two agree definitionally; nothing is
asserted about a different morphism of topoi.

**The two `HasSheafCompose` hypotheses that this chain did not previously carry are derivable
at this size.**  `X.J.HasSheafCompose (forget RingCat)` and `(forget AddCommGrpCat)` are found
by instance search for a `RingedTopos.{u, u, u}`, so this file adds no instance hypothesis
beyond the six that the Stacks 0G6R reduction already carries.

**Universes.**  Everything is at `AlgebraicGeometry.RingedTopos.{u, u, u}`.  The narrowing is
inherited: it is forced four independent ways on this chain, recorded in the implementation
notes of the Stacks 05VD reduction, and additionally by
`CategoryTheory.Functor.IsMorphismOfSites`, which is declared for `{C D : Type u}` with
`SmallCategory` on both.  Nothing here narrows further.

**No tag is placed in this file.**  Stacks 00YR has **no statement of its own** in this
development — so no clause string for it exists, and it is registered nowhere.  The clause
`04JC "inverse_image_exact"` is the *abelian-sheaf* assertion and is already carried by
`CategoryTheory.Sites.abelianInverseImage_exact`; the clause `04JC
  "flat_pullback_exact"` is about the
pullback along a **flat** morphism of ringed topoi, which is not what is proved here.  Stacks
0G6R registers its single clause with a bare attribute, and `pullbackPreservesShortExact`
below is still conditional on universally quantified Stacks 05VD, which nothing in either tree
concludes, so it may not carry that tag either.

## References

* [The Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [The Stacks Project, Section 7.44 (Tag 00YR)](https://stacks.math.columbia.edu/tag/00YR)
* [The Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [The Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [The Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open StacksPullbackFactorization

universe u

namespace Stacks.Sheaves.InverseImageExactness

noncomputable section

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  (f : AlgebraicGeometry.RingedToposSiteHom X Y)
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- The morphism of topoi underlying `f`, written out as a structure instance so that its
projections reduce at reducible transparency; see the implementation notes. -/
abbrev toposHom : MorphismOfTopoi (Sheaf X.J (Type u)) (Sheaf Y.J (Type u)) where
  pushforward := f.u.sheafPushforwardContinuous (Type u) Y.J X.J
  inverseImage := f.u.sheafPullback (Type u) Y.J X.J
  adj := f.u.sheafAdjunctionContinuous (Type u) Y.J X.J
  preservesFiniteLimits := hmos.preservesFiniteLimits

/-- `f⁻¹O_Y` as this development's transported inverse-image sheaf of rings. -/
abbrev invRingTransported : Sheaf X.J RingCat.{u} :=
  inverseImageRingSheaf.{u, u, u, u, u, u} (toposHom f hmos)
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The transported direct image of `invRingTransported`. -/
abbrev pushRingTransported : Sheaf Y.J RingCat.{u} :=
  pushforwardRingSheaf.{u, u, u, u, u, u} (toposHom f hmos) (invRingTransported.{u} f hmos)

/-- Mathlib's direct image of `invRingTransported`, i.e. restriction along `f.u`. -/
abbrev pushRingRestriction : Sheaf Y.J RingCat.{u} :=
  (f.u.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj (invRingTransported.{u} f hmos)

/-- `f⁻¹O_Y` as `StacksPullbackFactorization.invRing` gives it, read as a sheaf of rings. -/
abbrev invRingAbstract : Sheaf X.J RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)

/-- The direct image of sheaves of commutative rings along the morphism of topoi underlying
`f` **is** restriction along the continuous functor `f.u`. -/
def pushCommRingIso :
    pushforwardCommRingFunctor.{u, u, u, u, u, u} (toposHom f hmos) ≅
      f.u.sheafPushforwardContinuous CommRingCat.{u} Y.J X.J :=
  NatIso.ofComponents (fun O ↦ restrictionCommRingIso Y.J X.J f.u O)
    (fun a ↦ restrictionCommRingIso_naturality Y.J X.J f.u a)

/-- The two constructions of the inverse image of sheaves of commutative rings along the
morphism of topoi underlying `f` agree: both are left adjoint to the same direct image. -/
def invCommRingIso :
    inverseImageCommRingFunctor.{u, u, u, u, u, u} (toposHom f hmos) ≅
      f.u.sheafPullback CommRingCat.{u} Y.J X.J :=
  Adjunction.leftAdjointUniq
    ((commRingImageAdjunction.{u, u, u, u, u, u}
      (toposHom f hmos)).ofNatIsoRight (pushCommRingIso f hmos))
    (f.u.sheafAdjunctionContinuous CommRingCat.{u} Y.J X.J)

/-- **The comparison of the two inverse images of the structure sheaf**, after forgetting
commutativity: the transported `f⁻¹O_Y` is the one `StacksPullbackFactorization.invRing`
uses. -/
def ringCompare : invRingTransported.{u} f hmos ≅ invRingAbstract.{u} f :=
  (Stacks.forgetCommRingSheaf X.J).mapIso ((invCommRingIso f hmos).app Y.O)

/-- The unit `O_Y ⟶ f_*f⁻¹O_Y` of this development, as a morphism of sheaves of rings. -/
abbrev ringU :
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶ pushRingTransported.{u} f hmos :=
  ringUnit.{u, u, u, u, u, u} (toposHom f hmos) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The comparison of the transported direct image with restriction along `f.u`. -/
abbrev restrRing : pushRingTransported.{u} f hmos ⟶ pushRingRestriction.{u} f hmos :=
  (restrictionRingIso Y.J X.J f.u (invRingTransported.{u} f hmos)).hom

/-- Restriction of sheaves of modules along the continuous functor `f.u`. -/
abbrev restrMod :
    SheafOfModules.{u} (invRingTransported.{u} f hmos) ⥤
      SheafOfModules.{u} (pushRingRestriction.{u} f hmos) :=
  restrictionModules Y.J X.J f.u (invRingTransported.{u} f hmos)

/-- The unit `O_Y ⟶ f_*f⁻¹O_Y` of this development, read with Mathlib's direct image. -/
abbrev unitRestricted :
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶ pushRingRestriction.{u} f hmos :=
  ringU.{u} f hmos ≫ restrRing.{u} f hmos

/-- **The structure map of the geometric half of the factorization, through the comparison of
rings.**  `(auxHomG f).fSharp` is the unit of Mathlib's adjunction on sheaves of commutative
rings; `unitRestricted` is the unit of this development's; and `ringCompare` is the comparison
of their values.  Uniqueness of left adjoints relates the two units, and this is that relation
after forgetting commutativity. -/
theorem fSharpRing_eq :
    (auxHomG f).fSharpRing =
      unitRestricted f hmos ≫
        (f.u.sheafPushforwardContinuous RingCat.{u} Y.J X.J).map (ringCompare f hmos).hom := by
  have hfl : PreservesFiniteLimits (toposHom f hmos).inverseImage :=
    (toposHom f hmos).preservesFiniteLimits
  have hfp : PreservesFiniteProducts (toposHom f hmos).inverseImage := inferInstance
  have key := Adjunction.unit_leftAdjointUniq_hom_app
    ((commRingImageAdjunction.{u, u, u, u, u, u}
      (toposHom f hmos)).ofNatIsoRight (pushCommRingIso f hmos))
    (f.u.sheafAdjunctionContinuous CommRingCat.{u} Y.J X.J) Y.O
  rw [Adjunction.ofNatIsoRight_unit] at key
  have key2 : (commRingImageAdjunction.{u, u, u, u, u, u} (toposHom f hmos)).unit.app Y.O ≫
      (pushforwardCommRingFunctor.{u, u, u, u, u, u} (toposHom f hmos)).map
          ((invCommRingIso f hmos).hom.app Y.O) ≫
        (pushCommRingIso f hmos).hom.app (invRing f) = (auxHomG f).fSharp := by
    rw [(pushCommRingIso f hmos).hom.naturality ((invCommRingIso f hmos).hom.app Y.O),
      ← Category.assoc]
    exact key
  have key3 := congrArg (Stacks.forgetCommRingSheaf Y.J).map key2
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at key3
  have haux : (pushforwardRingFunctor (toposHom f hmos)).map
        ((forgetCommRingSheafCompPullbackIso X.J
          (toposHom f hmos).inverseImage).hom.app Y.O) ≫
      (forgetCommRingSheafCompPullbackIso Y.J (toposHom f hmos).pushforward).hom.app
        ((inverseImageCommRingFunctor.{u, u, u, u, u, u} (toposHom f hmos)).obj Y.O)
      = 𝟙 _ :=
    (sheafCompose Y.J (forget RingCat.{u})).map_injective
      (Sheaf.hom_ext_sections fun _ _ ↦ rfl)
  have h2 : (Stacks.forgetCommRingSheaf Y.J).map
      ((commRingImageAdjunction.{u, u, u, u, u, u} (toposHom f hmos)).unit.app Y.O) =
      ringUnit.{u, u, u, u, u, u} (toposHom f hmos)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) := by
    simp only [commRingImageAdjunction]
    rw [Adjunction.map_restrictFullyFaithful_unit_app, haux]
    exact Category.comp_id _
  have h3 : (Stacks.forgetCommRingSheaf Y.J).map
      ((pushforwardCommRingFunctor.{u, u, u, u, u, u} (toposHom f hmos)).map
        ((invCommRingIso f hmos).hom.app Y.O)) =
      pullbackRingSheafMap Y.J (f.u.sheafPushforwardContinuous (Type u) Y.J X.J)
        ((ringCompare f hmos).hom) :=
    forgetCommRingSheaf_map_pullbackCommRingSheafMap Y.J (toposHom f hmos).pushforward
      ((invCommRingIso f hmos).hom.app Y.O)
  have h4 : (Stacks.forgetCommRingSheaf Y.J).map ((pushCommRingIso f hmos).hom.app (invRing f)) =
      (restrictionRingIso Y.J X.J f.u (invRingAbstract.{u} f)).hom :=
    forgetCommRingSheaf_map_restrictionCommRingIso_hom Y.J X.J f.u (invRing f)
  rw [h2, h3, h4] at key3
  have hnat2 := restrictionRingIso_naturality Y.J X.J f.u ((ringCompare f hmos).hom)
  exact key3.symm.trans
    ((congrArg (fun z ↦ ringUnit.{u, u, u, u, u, u} (toposHom f hmos)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫ z)
      hnat2).trans (Category.assoc _ _ _).symm)

/-! ### The module-level identification

Each declaration below is a single `SheafOfModules.pushforwardComp`, `pushforwardCongr` or
whiskering, with all implicit sheaves of rings supplied; see the implementation notes for why
they are not combined. -/

/-- Restricting scalars along `restrictionRingIso` and then along the unit is restricting
scalars along `unitRestricted`. -/
def restrictScalarsCompIso :
    SheafOfModules.restrictScalars (restrRing.{u} f hmos) ⋙
        SheafOfModules.restrictScalars (ringU.{u} f hmos) ≅
      SheafOfModules.restrictScalars (unitRestricted.{u} f hmos) :=
  SheafOfModules.pushforwardComp (F := 𝟭 Y.C) (G := 𝟭 Y.C)
    (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (R := pushRingTransported.{u} f hmos) (R' := pushRingRestriction.{u} f hmos)
    (ringU.{u} f hmos) (restrRing.{u} f hmos)

/-- Restriction along `f.u` followed by restriction of scalars along `unitRestricted` is the
pushforward of sheaves of modules along `unitRestricted`. -/
def restrictionCompIso := SheafOfModules.pushforwardComp (F := 𝟭 Y.C) (G := f.u)
    (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (R := pushRingRestriction.{u} f hmos)
    (R' := invRingTransported.{u} f hmos)
    (unitRestricted.{u} f hmos) (𝟙 (pushRingRestriction.{u} f hmos))

/-- The structure map produced by `restrictionCompIso` is `unitRestricted` itself. -/
def restrictionCompCongr :
    SheafOfModules.pushforward (F := 𝟭 Y.C ⋙ f.u)
        (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (R := invRingTransported.{u} f hmos)
        (unitRestricted.{u} f hmos ≫
          ((𝟭 Y.C).sheafPushforwardContinuous RingCat.{u} Y.J Y.J).map
            (𝟙 (pushRingRestriction.{u} f hmos))) ≅
      SheafOfModules.pushforward (F := 𝟭 Y.C ⋙ f.u)
        (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (R := invRingTransported.{u} f hmos) (unitRestricted.{u} f hmos) :=
  SheafOfModules.pushforwardCongr
    (by rw [CategoryTheory.Functor.map_id]; exact Category.comp_id _)

/-- Restriction of scalars along `ringCompare` followed by the pushforward along
`unitRestricted` is the pushforward along the composite structure map. -/
def pushforwardCompareIso := SheafOfModules.pushforwardComp (F := f.u) (G := 𝟭 X.C)
    (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (R := invRingTransported.{u} f hmos)
    (R' := invRingAbstract.{u} f)
    (unitRestricted.{u} f hmos) ((ringCompare f hmos).hom)

/-- That composite structure map is `(auxHomG f).fSharpRing`, by `fSharpRing_eq`. -/
def pushforwardCompareCongr :
    SheafOfModules.pushforward (F := f.u ⋙ 𝟭 X.C)
        (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (R := invRingAbstract.{u} f)
        (unitRestricted.{u} f hmos ≫
          (f.u.sheafPushforwardContinuous RingCat.{u} Y.J X.J).map (ringCompare f hmos).hom) ≅
      SheafOfModules.pushforward (F := f.u ⋙ 𝟭 X.C)
        (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (R := invRingAbstract.{u} f) (auxHomG f).fSharpRing :=
  SheafOfModules.pushforwardCongr (fSharpRing_eq f hmos).symm

/-- Step one of `directImageModulesIso`: `restrictionModuleIso` whiskered with restriction of
scalars along the unit. -/
def directImageWhiskerIso :
    directImageModules.{u, u, u, u, u, u} (toposHom f hmos)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      (restrMod.{u} f hmos ⋙ SheafOfModules.restrictScalars (restrRing.{u} f hmos)) ⋙
        SheafOfModules.restrictScalars (ringU.{u} f hmos) :=
  Functor.isoWhiskerRight
    (restrictionModuleIso Y.J X.J f.u (invRingTransported.{u} f hmos))
    (SheafOfModules.restrictScalars (ringU.{u} f hmos))

/-- Step two: the two restrictions of scalars merge. -/
def directImageMergeIso :
    (restrMod.{u} f hmos ⋙ SheafOfModules.restrictScalars (restrRing.{u} f hmos)) ⋙
        SheafOfModules.restrictScalars (ringU.{u} f hmos) ≅
      restrMod.{u} f hmos ⋙ SheafOfModules.restrictScalars (unitRestricted.{u} f hmos) :=
  Functor.isoWhiskerLeft (restrMod.{u} f hmos) (restrictScalarsCompIso f hmos)

/-- Step three: restriction followed by that restriction of scalars is the pushforward. -/
def directImageMergeIso' :
    restrMod.{u} f hmos ⋙ SheafOfModules.restrictScalars (unitRestricted.{u} f hmos) ≅
      SheafOfModules.pushforward (F := 𝟭 Y.C ⋙ f.u)
        (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (R := invRingTransported.{u} f hmos) (unitRestricted.{u} f hmos) :=
  restrictionCompIso f hmos ≪≫ restrictionCompCongr f hmos

/-- **The direct image of sheaves of modules of Stacks 03D3 is Mathlib's pushforward along
`unitRestricted`.**  The only content is `restrictionModuleIso`: the transported module
structure on the sections of a restriction is the original one.  The three steps are stated
separately so that no single definitional check is large; see the implementation notes. -/
def directImageModulesIso :
    directImageModules.{u, u, u, u, u, u} (toposHom f hmos)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      SheafOfModules.pushforward (F := 𝟭 Y.C ⋙ f.u)
        (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (R := invRingTransported.{u} f hmos) (unitRestricted.{u} f hmos) :=
  directImageWhiskerIso f hmos ≪≫ directImageMergeIso f hmos ≪≫
    directImageMergeIso' f hmos

/-- **`g_*` is restriction of scalars along `ringCompare` followed by the direct image of
Stacks 03D3.** -/
def pushforwardIso :
    (auxHomG f).pushforwardTopos ≅
      SheafOfModules.restrictScalars (ringCompare f hmos).hom ⋙
        directImageModules.{u, u, u, u, u, u} (toposHom f hmos)
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (pushforwardCompareCongr f hmos).symm ≪≫ (pushforwardCompareIso f hmos).symm ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.pushforward (F := 𝟭 X.C) (S := invRingTransported.{u} f hmos)
        (R := invRingAbstract.{u} f) (ringCompare f hmos).hom)
      (directImageModulesIso f hmos).symm

/-- **The identification.**  `g^*`, the inverse image of sheaves of modules with no change of
rings, is the inverse image of sheaves of modules along the underlying morphism of topoi
(Stacks 03D2), read over `f⁻¹O_Y` through `ringCompare`.  Both sides are left adjoint to
`g_*`. -/
def pullbackIsoInverseImageModules :
    (auxHomG f).pullbackTopos ≅
      inverseImageModules.{u, u, u, u, u, u} (toposHom f hmos)
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
          (ringCompare f hmos)).functor :=
  Adjunction.leftAdjointUniq ((auxHomG f).pullbackPushforwardAdjunctionTopos)
    (((inverseImageAdjDirectImageModules.{u, u, u, u, u, u}
        (toposHom f hmos) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).comp
      (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
        (ringCompare f hmos)).toAdjunction).ofNatIsoRight (pushforwardIso f hmos).symm)

include hmos in
/-- **Stacks 00YR at module level, in the form this chain needs.**  The inverse image of sheaves
of modules with no change of rings is left exact.

Its general form is false — the comparison of lower shriek with forgetting the module structure
is not an isomorphism in general — and the content of this statement is that the case at hand is
the unit case, where the adjoint of the structure map is an identity rather than a counit. -/
@[sga "4 IV 13.7" "special case"]
theorem preservesFiniteLimits_pullbackTopos_auxHomG :
    PreservesFiniteLimits (auxHomG f).pullbackTopos := by
  have h1 : PreservesFiniteLimits
      (inverseImageModules.{u, u, u, u, u, u} (toposHom f hmos)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
    inverseImageModules_preservesFiniteLimits.{u, u, u, u, u, u} (toposHom f hmos)
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  have h2 : PreservesFiniteLimits
      (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
        (ringCompare f hmos)).functor := inferInstance
  have h3 : PreservesFiniteLimits
      (inverseImageModules.{u, u, u, u, u, u} (toposHom f hmos)
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
          (ringCompare f hmos)).functor) := comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (pullbackIsoInverseImageModules f hmos).symm

/-- `g^*` is right exact, being a left adjoint.  Unlike its sibling this needs no hypothesis on
`f.u` at all. -/
theorem preservesFiniteColimits_pullbackTopos_auxHomG :
    PreservesFiniteColimits (auxHomG f).pullbackTopos := by
  have : PreservesColimitsOfSize.{0, 0} (auxHomG f).pullbackTopos :=
    ((auxHomG f).pullbackPushforwardAdjunctionTopos).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

end

section Discharge

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks 04JC for sheaves of modules at the geometric half `g` of the factorization — the
remaining input of the Stacks 0G6R reduction, discharged.**  No hypothesis is added: the
morphism-of-sites condition is the one the predicate itself carries, and it is what makes
`f⁻¹` on sheaves of sets left exact. -/
@[sga "4 IV 13.7" "special case"]
theorem inverseImagePreservesShortExact (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    InverseImagePreservesShortExact f := by
  intro hmos T hT
  have h1 : PreservesFiniteLimits (auxHomG f).pullbackTopos :=
    preservesFiniteLimits_pullbackTopos_auxHomG f hmos
  have h2 : PreservesFiniteColimits (auxHomG f).pullbackTopos :=
    preservesFiniteColimits_pullbackTopos_auxHomG f
  exact hT.map_of_exact _

omit [HasSheafify Y.J AddCommGrpCat.{u}] in
/-- **Stacks 0G6R from universally quantified Stacks 05VD alone.**  The second input of
`pullbackPreservesShortExact_of_univ` is now closed, so Stacks 0G6R rests on Stacks 05VD and
nothing else. -/
theorem pullbackPreservesShortExact (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hpf : PullbackPreservesIsFlatUniv.{u}) :
    Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact f :=
  -- Mathlib's global instance, not the omitted section variable
  letI : HasSheafify Y.J AddCommGrpCat.{u} :=
    instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover Y.J _
  pullbackPreservesShortExact_of_univ f hpf (inverseImagePreservesShortExact f)

section Consumer

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The K-flatness assertion of Tag 0G7E on universally quantified Stacks 05VD alone.**
`Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex_of_univ` takes two open inputs; the
  second is discharged
by `inverseImagePreservesShortExact`, so only Stacks 05VD remains. -/
theorem kFlat_pullbackComplex (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : PullbackPreservesIsFlatUniv.{u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat X.O
      ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K) :=
  kFlat_pullbackComplex_of_univ f hmos hpf (inverseImagePreservesShortExact f) K hK hflatK

end Consumer

end Discharge

end Stacks.Sheaves.InverseImageExactness

end
