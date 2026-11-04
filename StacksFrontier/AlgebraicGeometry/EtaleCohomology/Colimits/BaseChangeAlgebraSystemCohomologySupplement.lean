module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomology
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SiteEquivalenceGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Pretopology.AsSmallSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Systems of base changes over an affine scheme and their etale cohomology

This module supplements
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomology`.
For an inverse system `Z_i` of affine schemes over an affine scheme `T` and an arbitrary `X`
over `T`, the base changes `Z_i ×_T X` form a system with affine transition morphisms. This
module sets up the corresponding system of small affine etale sites, compares the cohomology
of the small affine etale site of a scheme, raised to a larger universe, with its etale
cohomology, and constructs the sheaf `colim_i f_i^{-1} F_i` of Stacks 03Q6 on the system of
base changes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u

namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem

open AlgebraicGeometry

section SystemGeneral

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)

variable [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]

omit [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine X.left] in
/-- **The projection `Y_i = Z_i ×_T X ⟶ X` is affine.** It is the base change along `X ⟶ T` of
the structure morphism `Z_i ⟶ T`, which is a morphism of affine schemes and so affine, and
affine morphisms are stable under base change.

No affineness of `X` is used, which is what makes the transitions of the system of base changes
affine for an arbitrary `X` over an affine `T`. -/
@[ega "II 1.6.2" "(iii), special case", sga "3 III 0.1.7" "0.1.7(a), special case"]
theorem isAffineHom_baseChange_snd (i : Iᵒᵖ) :
    IsAffineHom (Limits.pullback.snd (Z.obj i).hom X.hom) :=
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) X.hom :=
    MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange
      (@IsAffineHom) X.hom
  MorphismProperty.pullback_snd _ _ (isAffineHom_of_isAffine (Z.obj i).hom)


omit [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine X.left] in
/-- **Every transition morphism of the system of base changes is affine**, with no affineness of
`X` (the general form of `isAffineHom_baseChange_map`): only `T` and the `Z_i` are affine.

The transition `Y_i ⟶ Y_j` lies over `X`, the system of base changes being built inside the
category of schemes over `X` (`Over.w`), and both projections `Y_i ⟶ X` and `Y_j ⟶ X` are affine
by `isAffineHom_baseChange_snd`; so the transition is affine by the cancellation property of
affine morphisms (`AlgebraicGeometry.IsAffineHom.comp_iff`).

For an affine `X` this is immediate, every level then being affine
(`isAffine_baseChange_obj`); the point of the argument above is that it is the one piece of the
system of sites of Stacks 0EYL which the affineness of `X` was supplying, so with it the site
system is available for a general `X` over an affine base. -/
instance isAffineHom_baseChange_map' {i j : Iᵒᵖ} (a : i ⟶ j) :
    IsAffineHom ((baseChange T X Z).map a) := by
  have hj := isAffineHom_baseChange_snd T X Z j
  have hw : (baseChange T X Z).map a ≫ Limits.pullback.snd (Z.obj j).hom X.hom =
      Limits.pullback.snd (Z.obj i).hom X.hom :=
    Over.w ((Z ⋙ Over.pullback X.hom).map a)
  have key : IsAffineHom ((baseChange T X Z).map a ≫
      Limits.pullback.snd (Z.obj j).hom X.hom) := hw ▸ isAffineHom_baseChange_snd T X Z i
  exact (@IsAffineHom.comp_iff _ _ _ _ _ hj).mp key


end SystemGeneral

section ColimitGeneral

open Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **The system of sites of Stacks 0EYL for the system of base changes, for an arbitrary `X`**:
the strict inverse system of small sites equivalent to the small affine etale sites of the `Y_i`.
Only `T` and the `Z_i` are affine; the transitions are affine by
`isAffineHom_baseChange_map'`. For an affine `X` it is `bcSys`. -/
def bcSysGen (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt) :
    InverseSystemOfFiniteSites.{u, u, u + 1} :=
  sys.{u, u} (baseChange T X Z) cY B hD hY hcY

/-- The small affine etale site of the limit `Y`, raised to the universe of the levels of the
system. This is `Stacks.EtaleCohomology.AffineLimitCohomology.limitSite` written out. -/
abbrev bcLimitSiteGen (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (_hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (_hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt) :
    Type (u + 1) :=
  AsSmall.{u + 1} (AlgebraicGeometry.SmallAffineEtale B cY.pt hY)

/-- The etale coverings of the raised site of `Y`, as a precoverage. -/
def bcPrecoverageGen (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt) :
    Precoverage (bcLimitSiteGen T X Z cY hcY B hD hY) :=
  limitSitePrecoverage.{u, u} (baseChange T X Z) cY B hY

/-- The canonical functors from the levels of the system to the raised site of `Y`. -/
def bcToLimitSmallGen (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
    (i : (bcSysGen T X Z cY hcY B hD hY).I) :
    (bcSysGen T X Z cY hcY B hD hY).C i ⥤ bcLimitSiteGen T X Z cY hcY B hD hY :=
  toLimitSmall.{u, u} (baseChange T X Z) cY B hD hY hcY i

/-- **The cocone identity of Stacks 09YL** for the system of base changes: the functors to the
site of `Y` are compatible with the transition functors of the system. -/
theorem bcToLimitSmallGen_transition (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
    {i j : (bcSysGen T X Z cY hcY B hD hY).I} (a : i ⟶ j) :
    (bcSysGen T X Z cY hcY B hD hY).u a ⋙ bcToLimitSmallGen T X Z cY hcY B hD hY i =
      bcToLimitSmallGen T X Z cY hcY B hD hY j :=
  toLimitSmall_transition.{u, u} (baseChange T X Z) cY B hD hY hcY a


end ColimitGeneral

end Stacks.EtaleCohomology.BaseChangeAlgebraSystem

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence

/-- The etale topology of the small affine etale site of `S`, raised to the universe of the levels
of a system of Stacks 0EYL. This is the topology Stacks 09YP computes with, and it is
`Stacks.EtaleCohomology.AffineLimitCohomology.limitSitePrecoverage` generated as a topology. -/
abbrev raisedAffineEtaleTopology :
    GrothendieckTopology (AsSmall.{u + 1} (AlgebraicGeometry.SmallAffineEtale B S hS)) :=
  ((AlgebraicGeometry.SmallAffineEtale.precoverage B S hS).comap AsSmall.down).toGrothendieck

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up

/-- Abelian sheaves on the raised site admit sheafification. -/
theorem hasSheafify_raisedAffineEtale :
    HasSheafify (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u + 1, u + 1} _

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale

/-- Abelian sheaves on the raised site are locally `(u + 1)`-small. -/
theorem locallySmall_raisedAffineEtale :
    LocallySmall.{u + 1} (Sheaf (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{u + 1, u + 1, u + 1, u + 1, u + 2}
    (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale

/-- Abelian sheaves on the raised site have enough injectives. -/
theorem enoughInjectives_raisedAffineEtale :
    EnoughInjectives (Sheaf (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u + 1, u + 1, u + 2}
    (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale

/-- `Ext`-groups of abelian sheaves on the raised site exist in `Type (u + 1)`. -/
theorem hasExt_raisedAffineEtale :
    HasExt.{u + 1} (Sheaf (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale

/-- **The restriction of an abelian sheaf from the raised site back to the small affine etale
site of `S`.** -/
abbrev restrictFromRaised :
    Sheaf (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1} ⥤
      Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
  (AsSmall.up :
      AlgebraicGeometry.SmallAffineEtale B S hS ⥤
        AsSmall.{u + 1} (AlgebraicGeometry.SmallAffineEtale B S hS)).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
    (raisedAffineEtaleTopology B S hS)

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale

/-- The `p`-th cohomology functor of abelian sheaves on the raised site: the `Ext`-groups out of
the constant sheaf on `ℤ`, which is the cohomology Stacks 09YP produces. -/
abbrev raisedAffineEtaleCohomologyFunctor (p : ℕ) :
    Sheaf (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u + 1, u + 1} (raisedAffineEtaleTopology B S hS) p

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale

/-- **Raising the morphism universe of the small affine etale site does not change cohomology.**
For every degree `p`,

`H^p(S_{affine,etale}, F|_{S_{affine,etale}}) ≅ H^p(AsSmall S_{affine,etale}, F)`

naturally in the abelian sheaf `F` on the raised site. The raise is the inclusion of a dense
subsite (`CategoryTheory.AsSmall.isDenseSubsite_up`), so restriction along it is an equivalence of
abelian sheaf categories, and an equivalence of sites changes neither the constant sheaf on `ℤ`
nor the injective objects, hence not the `Ext`-groups out of the constant sheaf.

This is `Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence`, the form of
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` at *independent
morphism universes*: the two sites have the same objects but their morphisms differ by one
universe, which is exactly what the raise does. -/
def raisedAffineEtaleCohomologyFunctorIso (p : ℕ) :
    restrictFromRaised B S hS ⋙ affineEtaleCohomologyFunctor B S hS p ≅
      raisedAffineEtaleCohomologyFunctor B S hS p :=
  Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence.{u + 1, u, u + 1, u + 1}
    (AlgebraicGeometry.SmallAffineEtale.topology B S hS) (raisedAffineEtaleTopology B S hS)
    AsSmall.up p

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale

/-- **The abelian sheaf on the small etale site of `S` that an abelian sheaf on the raised small
affine etale site comes from.** Restrict along the raise, then invert the equivalence of Stacks
04HR. -/
abbrev raisedToSmallEtale :
    Sheaf (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1} ⥤
      Sheaf (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
  restrictFromRaised B S hS ⋙ (restrictToAffineEtale B S hS).asEquivalence.inverse

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale

/-- The cohomology of the small affine etale site, written on the small etale site through the
inverse of the equivalence of Stacks 04HR. -/
def affineEtaleCohomologyFunctorIsoInv (p : ℕ) :
    affineEtaleCohomologyFunctor B S hS p ≅
      (restrictToAffineEtale B S hS).asEquivalence.inverse ⋙
        smallEtaleCohomologyFunctor B S hS p :=
  ((restrictToAffineEtale B S hS).asEquivalence.invFunIdAssoc
      (affineEtaleCohomologyFunctor B S hS p)).symm ≪≫
    Functor.isoWhiskerLeft _ (affineEtaleCohomologyFunctorIso B S hS p)

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale

/-- **The cohomology of the raised small affine etale site of `S` is the etale cohomology of
`S`.** For every degree `p`,

`H^p(AsSmall S_{affine,etale}, F) ≅ H^p(S_etale, F')`

naturally in the abelian sheaf `F` on the raised site, where `F'` is the abelian sheaf on the
small etale site that `F` comes from (`raisedToSmallEtale`). No affineness of `S` is needed.

This is the step the cohomological half of Stacks 03Q6 was missing: Stacks 09YP computes on the
raised site of `CategoryTheory.AsSmall`, Stacks 04HR compares the small affine etale site with the
small etale site, and `raisedAffineEtaleCohomologyFunctorIso` joins the two. The right hand side
is the library's mainstream etale cohomology functor, by `etaleCohomologyFunctor_eq`. -/
def raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology (p : ℕ) :
    raisedAffineEtaleCohomologyFunctor B S hS p ≅
      raisedToSmallEtale B S hS ⋙
        Stacks.EtaleCohomology.etaleCohomologyFunctor B ⟨S, hS⟩ p :=
  (raisedAffineEtaleCohomologyFunctorIso B S hS p).symm ≪≫
    Functor.isoWhiskerLeft _ (affineEtaleCohomologyFunctorIsoInv B S hS p) ≪≫
    (Functor.associator _ _ _).symm

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale

/-- The isomorphism of `raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology` at a fixed abelian
sheaf on the raised site. -/
def raisedAffineEtaleCohomologyIsoEtaleCohomology
    (F : Sheaf (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (raisedAffineEtaleCohomologyFunctor B S hS p).obj F ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B ⟨S, hS⟩ p).obj
        ((raisedToSmallEtale B S hS).obj F) :=
  (raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology B S hS p).app F

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale
section
variable [IsAffine S]
attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale
attribute [local instance] additive_sheafΓ_smallAffineEtale
attribute [local instance] additive_sectionsFinal_smallAffineEtale

/-- `S / S`, raised to the universe of the levels: the terminal object of the raised site. -/
abbrev raisedFinal : AsSmall.{u + 1} (AlgebraicGeometry.SmallAffineEtale B S hS) :=
  AsSmall.up.obj (AlgebraicGeometry.SmallAffineEtale.final B S hS)

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale
section
variable [IsAffine S]
attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale
attribute [local instance] additive_sheafΓ_smallAffineEtale
attribute [local instance] additive_sectionsFinal_smallAffineEtale

/-- The raised object `S / S` is terminal in the raised site: terminality transports along
`CategoryTheory.AsSmall.up`. -/
def raisedFinal_isTerminal : IsTerminal (raisedFinal B S hS) :=
  Stacks.EtaleCohomology.AffineLimitCohomology.isTerminal_asSmallUp
    (AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B S hS)

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale
section
variable [IsAffine S]
attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale
attribute [local instance] additive_sheafΓ_smallAffineEtale
attribute [local instance] additive_sectionsFinal_smallAffineEtale

/-- Global sections of abelian sheaves on the raised site of an affine `S` exist: the site has a
terminal object, namely `S / S` raised. -/
theorem hasGlobalSectionsFunctor_raisedAffineEtale :
    HasGlobalSectionsFunctor (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1} :=
  have : HasTerminal (AsSmall.{u + 1} (AlgebraicGeometry.SmallAffineEtale B S hS)) :=
    (raisedFinal_isTerminal B S hS).hasTerminal
  CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal _ _

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale
section
variable [IsAffine S]
attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale
attribute [local instance] additive_sheafΓ_smallAffineEtale
attribute [local instance] additive_sectionsFinal_smallAffineEtale
attribute [local instance] hasGlobalSectionsFunctor_raisedAffineEtale

/-- Global sections of abelian sheaves on the raised site are additive, being a right adjoint. -/
theorem additive_sheafΓ_raisedAffineEtale :
    (Sheaf.Γ (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u + 1, u + 1} _

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale
section
variable [IsAffine S]
attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale
attribute [local instance] additive_sheafΓ_smallAffineEtale
attribute [local instance] additive_sectionsFinal_smallAffineEtale
attribute [local instance] hasGlobalSectionsFunctor_raisedAffineEtale
attribute [local instance] additive_sheafΓ_raisedAffineEtale

/-- Sections over the terminal object of the raised site are additive. -/
theorem additive_sectionsRaisedFinal :
    (((sheafSections (raisedAffineEtaleTopology B S hS)
      AddCommGrpCat.{u + 1}).obj (op (raisedFinal B S hS)))).Additive where
  map_add := by intros; rfl

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale
section
variable [IsAffine S]
attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale
attribute [local instance] additive_sheafΓ_smallAffineEtale
attribute [local instance] additive_sectionsFinal_smallAffineEtale
attribute [local instance] hasGlobalSectionsFunctor_raisedAffineEtale
attribute [local instance] additive_sheafΓ_raisedAffineEtale
attribute [local instance] additive_sectionsRaisedFinal

/-- For an affine `S` the global sections of an abelian sheaf on the raised site are its sections
over the raised `S / S`, that object being terminal. -/
def sheafΓIsoSectionsRaisedFinal :
    Sheaf.Γ (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1} ≅
      (sheafSections (raisedAffineEtaleTopology B S hS)
        AddCommGrpCat.{u + 1}).obj (op (raisedFinal B S hS)) :=
  Sheaf.ΓNatIsoSheafSections _ _ (raisedFinal_isTerminal B S hS)

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale
section
variable [IsAffine S]
attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale
attribute [local instance] additive_sheafΓ_smallAffineEtale
attribute [local instance] additive_sectionsFinal_smallAffineEtale
attribute [local instance] hasGlobalSectionsFunctor_raisedAffineEtale
attribute [local instance] additive_sheafΓ_raisedAffineEtale
attribute [local instance] additive_sectionsRaisedFinal

/-- **Cohomology over the terminal object of the raised site of an affine `S` is its sheaf
cohomology.** The right derived functors of sections over the raised `S / S` are the `Ext`-groups
out of the constant sheaf on `ℤ`. -/
def rightDerivedSectionsRaisedFinalIso (p : ℕ) :
    (((sheafSections (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}).obj
        (op (raisedFinal B S hS))).rightDerived p) ≅
      raisedAffineEtaleCohomologyFunctor B S hS p :=
  (Functor.rightDerivedIsoOfNatIso (sheafΓIsoSectionsRaisedFinal B S hS) p).symm ≪≫
    Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u + 1, u + 1}
      (raisedAffineEtaleTopology B S hS) p

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion
attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale
attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale
attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale
attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale
attribute [local instance] restrictToAffineEtale_isEquivalence
attribute [local instance] AsSmall.isDenseSubsite_up
attribute [local instance] hasSheafify_raisedAffineEtale
attribute [local instance] locallySmall_raisedAffineEtale
attribute [local instance] enoughInjectives_raisedAffineEtale
attribute [local instance] hasExt_raisedAffineEtale
section
variable [IsAffine S]
attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale
attribute [local instance] additive_sheafΓ_smallAffineEtale
attribute [local instance] additive_sectionsFinal_smallAffineEtale
attribute [local instance] hasGlobalSectionsFunctor_raisedAffineEtale
attribute [local instance] additive_sheafΓ_raisedAffineEtale
attribute [local instance] additive_sectionsRaisedFinal

/-- **The cohomological half of Stacks 03Q6, for an affine `S`.** The right derived functors of
sections over the terminal object of the *raised* small affine etale site of `S` — which is the
functor Stacks 09YP and Stacks 09YQ compute with — are the etale cohomology groups of `S`:

`H^p(AsSmall S_{affine,etale}, F) ≅ H^p(S_etale, F')`,

naturally in the abelian sheaf `F` on the raised site, where `F'` is the abelian sheaf on the
small etale site that `F` comes from (`raisedToSmallEtale`), and the right hand side is the
library's `Stacks.EtaleCohomology.etaleCohomologyFunctor`.

This is the passage between the raised site and the unraised one composed with the comparison of
Stacks 04HR: `rightDerivedSectionsRaisedFinalIso` identifies the derived sections with the
`Ext`-groups out of the constant sheaf on the raised site, and
`raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology` carries those to the etale cohomology of
the scheme. -/
def rightDerivedSectionsRaisedFinalIsoEtaleCohomology (p : ℕ) :
    (((sheafSections (raisedAffineEtaleTopology B S hS) AddCommGrpCat.{u + 1}).obj
        (op (raisedFinal B S hS))).rightDerived p) ≅
      raisedToSmallEtale B S hS ⋙
        Stacks.EtaleCohomology.etaleCohomologyFunctor B ⟨S, hS⟩ p :=
  rightDerivedSectionsRaisedFinalIso B S hS p ≪≫
    raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology B S hS p

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
attribute [local instance] IsCofiltered.isConnected
variable [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]


end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
open Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
section
variable (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
  (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
  (B : AlgebraicGeometry.BigEtaleSite.{u})
  (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
    (bcSys T X Z cY hcY B hD hY))

/-- **The sheaf `𝒢 = colim_i f_i^{-1} F_i` of Stacks 03Q6, constructed.** The left Kan extension
of the system `F` along the functors to the small affine etale site of `Y = lim_i Y_i`. -/
def bcColimitSheaf : Sheaf (bcPrecoverage T X Z cY hcY B hD hY).toGrothendieck Ab.{u + 1} :=
  colimitSheaf.{u, u} (baseChange T X Z) cY B hD hY hcY F

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
open Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
section
variable (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
  (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
  (B : AlgebraicGeometry.BigEtaleSite.{u})
  (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
    (bcSys T X Z cY hcY B hD hY))

/-- The legs `F_j ⟶ f_j^{-1} 𝒢` of `bcColimitSheaf`. -/
def bcColimitSheafLegs (j : (bcSys T X Z cY hcY B hD hY).I) :
    (F.obj j).obj ⟶ (bcToLimitSmall T X Z cY hcY B hD hY j).op ⋙
      (bcColimitSheaf T X Z cY hcY B hD hY F).obj :=
  colimitSheafLegs.{u, u} (baseChange T X Z) cY B hD hY hcY F j

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
open Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
section
variable (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
  (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
  (B : AlgebraicGeometry.BigEtaleSite.{u})
  (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
    (bcSys T X Z cY hcY B hD hY))

/-- **`bcColimitSheaf` presents the colimit of the inverse images**, which is the datum `hcolim`
of Stacks 09YP for the system of base changes. -/
theorem isColimitPresentation_bcColimitSheaf :
    IsColimitPresentation.{u, u, u + 1, u + 1} (bcSys T X Z cY hcY B hD hY)
      (bcToLimitSmall T X Z cY hcY B hD hY) (bcToLimitSmall_transition T X Z cY hcY B hD hY)
      (bcPrecoverage T X Z cY hcY B hD hY) F (bcColimitSheaf T X Z cY hcY B hD hY F)
      (bcColimitSheafLegs T X Z cY hcY B hD hY F) :=
  isColimitPresentation_colimitSheaf.{u, u} (baseChange T X Z) cY B hD hY hcY F

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
open Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
section
variable (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
  (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
  (B : AlgebraicGeometry.BigEtaleSite.{u})
  (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
    (bcSys T X Z cY hcY B hD hY))

/-- The canonical cohomology cocone of Stacks 03Q6 at the constructed colimit sheaf: the diagram
of the groups `H^p(Y_j, F_j)` with its cocone at `H^p(Y, colim_i f_i^{-1} F_i)`. -/
def bcCohomologyCocone (i : (bcSys T X Z cY hcY B hD hY).I) (p : ℕ) :
    CohomologyCocone.{u, u, u + 1, u + 1} (bcSys T X Z cY hcY B hD hY)
      (bcToLimitSmall T X Z cY hcY B hD hY) (bcToLimitSmall_transition T X Z cY hcY B hD hY)
      (bcPrecoverage T X Z cY hcY B hD hY) F (bcColimitSheaf T X Z cY hcY B hD hY F)
      (bcColimitSheafLegs T X Z cY hcY B hD hY F) i
      (bcLevelTerminal T X Z cY hcY B hD hY i) p :=
  cohomologyCoconeOfColimitSheaf.{u, u} (baseChange T X Z) cY B hD hY hcY F i p

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
open Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
section
variable (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
  (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
  (B : AlgebraicGeometry.BigEtaleSite.{u})
  (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
    (bcSys T X Z cY hcY B hD hY))

/-- **Stacks 03Q6 for an affine `X`, with the colimit sheaf constructed.** Same hypotheses as
`etaleCohomologyColimit_baseChange_isColimit`, but the sheaf presenting `colim_i f_i^{-1} F_i`,
its legs and its universal property are the constructions `bcColimitSheaf`,
`bcColimitSheafLegs` and `isColimitPresentation_bcColimitSheaf` rather than hypotheses. -/
def etaleCohomologyColimit_baseChange_colimitSheaf_isColimit
    (i : (bcSys T X Z cY hcY B hD hY).I) (p : ℕ)
    (E : CohomologyCocone.{u, u, u + 1, u + 1} (bcSys T X Z cY hcY B hD hY)
      (bcToLimitSmall T X Z cY hcY B hD hY) (bcToLimitSmall_transition T X Z cY hcY B hD hY)
      (bcPrecoverage T X Z cY hcY B hD hY) F (bcColimitSheaf T X Z cY hcY B hD hY F)
      (bcColimitSheafLegs T X Z cY hcY B hD hY F) i
      (bcLevelTerminal T X Z cY hcY B hD hY i) p :=
      bcCohomologyCocone T X Z cY hcY B hD hY F i p) :
    IsColimit E.cocone :=
  etaleCohomologyColimit_baseChange_isColimit T X Z cY hcY B hD hY F
    (bcColimitSheaf T X Z cY hcY B hD hY F) (bcColimitSheafLegs T X Z cY hcY B hD hY F)
    (isColimitPresentation_bcColimitSheaf T X Z cY hcY B hD hY F) i p E

end
end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u
namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open AlgebraicGeometry
section
open Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **Stacks 03Q6 for an affine `X`, at the canonical limit, with the colimit sheaf
constructed.** This is `etaleCohomologyColimit_baseChange_colimitSheaf_isColimit` at
`cY = systemLimitCone T X Z`, so that the cohomology on the left is taken over the honest
`Y = (lim_i Z_i) ×_T X = Spec B ×_{Spec A} X`, and the sheaf it is taken of is the constructed
`colim_i f_i^{-1} F_i` rather than a given one.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
def etaleCohomologyColimit_baseChange_systemLimit_colimitSheaf_isColimit
    (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i))
    (hY : B.Contains (systemLimitCone T X Z).pt)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
      (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY))
    (i : (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY).I) (p : ℕ)
    (E : CohomologyCocone.{u, u, u + 1, u + 1}
      (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall_transition T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY)
      (bcPrecoverage T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY) F
      (bcColimitSheaf T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY F)
      (bcColimitSheafLegs T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY F)
      i
      (bcLevelTerminal T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY i) p :=
      bcCohomologyCocone T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY
        F i p) :
    IsColimit E.cocone :=
  etaleCohomologyColimit_baseChange_colimitSheaf_isColimit T X Z (systemLimitCone T X Z)
    (isLimitSystemLimitCone T X Z) B hD hY F i p E

end
end Stacks.EtaleCohomology.BaseChangeAlgebraSystem
end
