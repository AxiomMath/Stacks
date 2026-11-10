module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionKInjectiveEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects

/-!
# Cohomology of a module over an object, over a site with large objects

Let `(C, J)` be a site whose objects form a type in an arbitrary universe `c` while its
morphisms, its sheaf of rings `R` and its modules all live in one universe `u`, let `U` be an
object of `C` and let `F` be a sheaf of `R`-modules. Part (2) of Stacks 03F3 says that the
cohomology of `F` over `U` agrees with the cohomology of the restriction `F|_U` on the localized
site `C/U`:

`H^p(U, F) = H^p(C/U, F|_U)`.

This is the single-universe development of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Localization/CohomologyOfModuleOverObject.lean`
restated with the universe of the objects of the site freed from the universe of its morphisms,
everything else staying in the single universe `u`. The reason is the one given in
`RestrictionPreservesInjectivesEssentiallySmall.lean`, which does the same for part (1) of the
tag: the small étale ringed site of an algebraic space has its objects one universe above its
morphisms, it is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, and so the single-universe
statements — which ask for an `AlgebraicGeometry.RingedSite.{u, u, u}` — cannot be instantiated
at it.

## Main results

* `Stacks.Cohomology.Localization.OfEssentiallySmall.restriction_exact`: restriction to the
  slice site is exact.
* `Stacks.Cohomology.Localization.OfEssentiallySmall.derivedSectionsOverObjectIsoSlice`:
  **Stacks 0D6F at the level of functors**, unbounded derived sections over `U` are the
  unbounded derived sections on `C/U` of the derived restriction.
* `Stacks.Cohomology.Localization.OfEssentiallySmall.cohomologyOverObjectIsoRestriction`:
  **Stacks 0D6F**.
* `Stacks.Cohomology.Localization.OfEssentiallySmall.cohomologyOverObjectIsoSlice`:
  **Stacks 03F3 (2)**, naturally in the module.
* `Stacks.Cohomology.Localization.OfEssentiallySmall.cohomologyOverObjectIsoSliceOfModule`:
  the same statement for one sheaf of modules.

## Implementation notes

**No hypothesis is added.** The single-universe development obtains sheafification, the
locally-bijective description of the weak equivalences and Grothendieck abelianness of the
modules from smallness of the site; here all four come from essential `u`-smallness instead, by
`CategoryTheory.hasSheafifyEssentiallySmallSite`,
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` and
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`, the last of which transports
Mathlib's instance along the equivalence with the small model and asks for exactly the first
two. The slice `Over U` is essentially `u`-small because `C` is and `C` is locally `u`-small,
so the same four are available there. Grothendieck abelianness is what makes the total right
derived functors exist, and it is the only one of the four that is not already recorded for
this configuration elsewhere in the tree.

Everything else is the single-universe proof verbatim. In particular:

* `restriction_exact` below is
  `Stacks.Cohomology.Localization.restriction_exact` with its appeal to
  `GrothendieckTopology.hasSheafify_addCommGrpCat` — which asks the objects of the site to lie
  in the universe of its morphisms — replaced by the essentially small form. Its right exactness
  argument, that an epimorphism of sheaves of modules is locally surjective and that local
  surjectivity survives whiskering along `(Over.forget U).op`, never mentions the universe of
  the objects.
* preservation of K-injectivity by restriction is not reproved: it is
  `Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall`, already available at
  these binders.
* the derived comparison is assembled by `Stacks.Cohomology.LerayUnbounded.derivedCompIso`,
  which carries no universe coupling at all.

The functors `sectionsOverObject`, `sectionsOnSlice` and the three homotopy and three derived
functors are restated rather than reused because the single-universe ones are indexed by an
`AlgebraicGeometry.RingedSite.{u, u, u}`; they are the same formulas at the freer binders, and
are given in the `(J, R, U)` form of the part (1) file rather than packaged into a ringed site,
which is what makes them instantiable at a site whose structure sheaf is `CommRingCat.{u}`-valued
while its objects are not `u`-small.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.LerayUnbounded

namespace Stacks.Cohomology.Localization.OfEssentiallySmall

universe u c

attribute [local instance] HasDerivedCategory.standard

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]
  (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u}) (U : C)

/-! ### The four ambient inputs, from essential smallness alone -/

/-- Every slice of an essentially `u`-small category whose morphisms lie in `Type u` is again
essentially `u`-small. This is the part (1) file's `essentiallySmall_over`, which is a plain
lemma there and is needed as an instance here. -/
local instance essentiallySmall_over : EssentiallySmall.{u} (Over U) :=
  Stacks.Sites.ExtensionByZero.OfEssentiallySmall.essentiallySmall_over U

/-- Abelian presheaves on an essentially `u`-small site have a left exact sheafification. -/
local instance hasSheafify_base : HasSheafify J AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- On an essentially `u`-small site the weak equivalences of abelian presheaves are the
locally bijective maps. -/
local instance wEqualsLocallyBijective_base :
    J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Sheafification on the localized site, the slice being essentially `u`-small too. -/
local instance hasSheafify_slice : HasSheafify (J.over U) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- The locally bijective description of the weak equivalences on the localized site. -/
local instance wEqualsLocallyBijective_slice :
    (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Sheaves of `R`-modules form a Grothendieck abelian category at module universe `u`, the
site being essentially `u`-small. This is what makes the total right derived functors below
exist. -/
local instance isGrothendieckAbelian_modules :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall R

/-- Sheaves of `R_U`-modules on the localized site form a Grothendieck abelian category at
module universe `u`. -/
local instance isGrothendieckAbelian_slice_modules :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (R.over U)) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall (R.over U)

/-! ### Exactness of restriction -/

/-- Restriction to the slice site over `U` preserves epimorphisms: an epimorphism of sheaves of
modules is locally surjective, local surjectivity is preserved by whiskering along
`(Over.forget U).op`, and a locally surjective morphism of sheaves is an epimorphism. -/
theorem preservesEpimorphisms_restriction :
    Functor.PreservesEpimorphisms (SheafOfModules.overFunctor.{u} R U) := by
  let F := SheafOfModules.overFunctor.{u} R U
  constructor
  intro A B f _
  have hlocal : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf R).map f).hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat ((SheafOfModules.toSheaf R).map f)).mpr
      (preserves_epi_of_preservesColimit (SheafOfModules.toSheaf R) f)
  have hOver : Presheaf.IsLocallySurjective (J.over U)
      ((SheafOfModules.toSheaf (R.over U)).map (F.map f)).hom := by
    have heq : ((SheafOfModules.toSheaf (R.over U)).map (F.map f)).hom =
        Functor.whiskerLeft (Over.forget U).op ((SheafOfModules.toSheaf R).map f).hom := by
      ext V x
      rfl
    rw [heq]
    exact Presheaf.isLocallySurjective_whisker (J := J.over U) (K := J) (H := Over.forget U) _
  let T := SheafOfModules.toSheaf (R.over U)
  have hUnder : Epi (T.map (F.map f)) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat (T.map (F.map f))).mp hOver
  exact T.epi_of_epi_map hUnder

set_option synthInstance.maxHeartbeats 200000 in
-- instance synthesis of finite-limit and homology preservation for `SheafOfModules.overFunctor`
/-- Restriction to the slice site over an object is exact, over a site whose objects need not lie
in the universe of its morphisms. Left exactness is the direct image part of Stacks 04BD (2),
which carries no universe coupling; right exactness is
`preservesEpimorphisms_restriction`. -/
theorem restriction_exact :
    exactFunctor _ _ (SheafOfModules.overFunctor.{u} R U) := by
  let F := SheafOfModules.overFunctor.{u} R U
  have hLim : PreservesFiniteLimits F :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.pushforward.{u}
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))))
  have hCol : PreservesFiniteColimits F := by
    have : Functor.PreservesEpimorphisms F := preservesEpimorphisms_restriction J R U
    have : F.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels F
    have : ∀ {A B : SheafOfModules R} (f : A ⟶ B),
        PreservesColimit (parallelPair f 0) F := fun f =>
          Functor.PreservesHomology.preservesCokernel F f
    exact Functor.preservesFiniteColimits_of_preservesCokernels F
  exact (exactFunctor_iff F).2 ⟨hLim, hCol⟩

/-- Restriction of sheaves of modules to the slice site over `U` preserves finite limits. -/
local instance preservesFiniteLimits_restriction :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} R U) :=
  ((exactFunctor_iff _).mp (restriction_exact J R U)).1

/-- Restriction of sheaves of modules to the slice site over `U` preserves finite colimits. -/
local instance preservesFiniteColimits_restriction :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} R U) :=
  ((exactFunctor_iff _).mp (restriction_exact J R U)).2

/-! ### Sections, and the underived comparison -/

/-- Sections of a sheaf of modules over an object, with the module structure forgotten. -/
abbrev sectionsOverObject : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation R (op U) ⋙
    forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}

/-- Global sections of a sheaf of modules on the site localized at `U`, with the module
structure forgotten. The final object of `C/U` is the identity arrow of `U`. -/
abbrev sectionsOnSlice : SheafOfModules.{u} (R.over U) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation (R.over U) (op (Over.mk (𝟙 U))) ⋙
    forget₂ (ModuleCat.{u} ((R.over U).obj.obj (op (Over.mk (𝟙 U))))) AddCommGrpCat.{u}

/-- The functor of sections over `U`, `sectionsOverObject J R U`, is additive. -/
instance additive_sectionsOverObject : (sectionsOverObject J R U).Additive where
  map_add := rfl

/-- The functor of global sections on the slice site, `sectionsOnSlice J R U`, is additive. -/
instance additive_sectionsOnSlice : (sectionsOnSlice J R U).Additive where
  map_add := rfl

/-- Sections over `U` are the global sections of the restriction to the site localized at `U`:
both are the sections of the underlying presheaf at the identity arrow of `U`. -/
def sectionsRestrictionIso :
    sectionsOverObject J R U ≅
      SheafOfModules.overFunctor.{u} R U ⋙ sectionsOnSlice J R U := by
  refine NatIso.ofComponents (fun F => eqToIso (by
    dsimp [sectionsOverObject, sectionsOnSlice, SheafOfModules.evaluation,
      SheafOfModules.overFunctor]
    rfl)) fun f => ?_
  dsimp [sectionsOverObject, sectionsOnSlice, SheafOfModules.overFunctor,
    SheafOfModules.evaluation]
  rfl

/-! ### The derived functors -/

/-- The sections functor on complexes, followed by localization. -/
abbrev homotopySectionsOverObject :
    HomotopyCategory (SheafOfModules.{u} R) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (sectionsOverObject J R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Restriction of complexes to the slice, followed by localization. -/
abbrev homotopyRestriction :
    HomotopyCategory (SheafOfModules.{u} R) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (R.over U)) :=
  (SheafOfModules.overFunctor.{u} R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Global sections of complexes on the slice, followed by localization. -/
abbrev homotopySectionsOnSlice :
    HomotopyCategory (SheafOfModules.{u} (R.over U)) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (sectionsOnSlice J R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Unbounded derived sections over `U`. -/
abbrev derivedSectionsOverObject :
    DerivedCategory (SheafOfModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (homotopySectionsOverObject J R U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ))

/-- Unbounded derived restriction to the localized site. -/
abbrev derivedRestriction :
    DerivedCategory (SheafOfModules.{u} R) ⥤ DerivedCategory (SheafOfModules.{u} (R.over U)) :=
  (homotopyRestriction J R U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ))

/-- Unbounded derived global sections on the localized site. -/
abbrev derivedSectionsOnSlice :
    DerivedCategory (SheafOfModules.{u} (R.over U)) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (homotopySectionsOnSlice J R U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (R.over U)) (ComplexShape.up ℤ))

/-- **Stacks 0D6F, at the level of functors, over a site with large objects.** Unbounded derived
sections over an object `U` are the unbounded derived sections on the localized site `C/U` of the
derived restriction to `C/U`. Restriction is exact and carries K-injective complexes to
K-injective complexes (Stacks 08FI, here
`Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall`), and sections over `U`
are global sections on `C/U` already before deriving. -/
def derivedSectionsOverObjectIsoSlice :
    derivedSectionsOverObject J R U ≅
      derivedRestriction J R U ⋙ derivedSectionsOnSlice J R U :=
  (derivedCompIso (SheafOfModules.overFunctor.{u} R U) (sectionsOnSlice J R U)
    (sectionsOverObject J R U) (sectionsRestrictionIso J R U).symm
    (fun I _ => isKInjective_over_of_essentiallySmall J R U I)).symm

/-- The total right derived restriction to the slice site is the functor that restriction, being
exact, induces on unbounded derived categories. Both are right derived functors of degreewise
restriction followed by localization: for the induced functor the comparison is Mathlib's
`Functor.mapDerivedCategoryFactorsh`, which is an isomorphism, hence an isomorphism on
K-injective complexes. -/
def derivedRestrictionIsoMapDerivedCategory :
    derivedRestriction J R U ≅
      (SheafOfModules.overFunctor.{u} R U).mapDerivedCategory := by
  let A := SheafOfModules.{u} R
  let sh := ComplexShape.up ℤ
  let G := SheafOfModules.overFunctor.{u} R U
  let α : homotopyRestriction J R U ⟶ DerivedCategory.Qh ⋙ G.mapDerivedCategory :=
    G.mapDerivedCategoryFactorsh.inv
  let := rightDerived_of_kInjectives (homotopyRestriction J R U) G.mapDerivedCategory α
    (fun I _ => inferInstance)
  exact Functor.rightDerivedNatIso (derivedRestriction J R U) G.mapDerivedCategory
    ((homotopyRestriction J R U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A sh))
    α (HomotopyCategory.quasiIso A sh) (Iso.refl _)

/-! ### The comparisons -/

/-- **Stacks 0D6F over a site with large objects.** Cohomology over `U` agrees naturally with
cohomology of the restricted derived module on the slice site `C/U`, over a site whose objects
need not lie in the universe of its morphisms. -/
def cohomologyOverObjectIsoRestriction (p : ℤ) :
    derivedSectionsOverObject J R U ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} p ≅
      derivedRestriction J R U ⋙ derivedSectionsOnSlice J R U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} p :=
  Functor.isoWhiskerRight (derivedSectionsOverObjectIsoSlice J R U)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p) ≪≫
    Functor.associator _ _ _

/-- **Stacks 03F3 (2) over a site with large objects.** For a site `(C, J)` whose objects need
not lie in the universe of its morphisms, a sheaf of rings `R` on it and an object `U` of `C`,
the cohomology `H^p(U, F)` of a sheaf of `R`-modules over `U` is the cohomology
`H^p(C/U, F|_U)` of its restriction on the site localized at `U`. Both sides place the module in
degree zero and take the `p`-th homology of the corresponding derived sections; the isomorphism
is natural in the module.

This is `Stacks.Cohomology.Localization.cohomologyOverObjectIsoSlice` with the object universe
freed, and it is the half of the tag matching
`Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor_of_essentiallySmall`,
which is part (1) at the same binders. -/
def cohomologyOverObjectIsoSlice (p : ℤ) :
    DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0 ⋙
        derivedSectionsOverObject J R U ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} p ≅
      SheafOfModules.overFunctor.{u} R U ⋙
        DerivedCategory.singleFunctor (SheafOfModules.{u} (R.over U)) 0 ⋙
          derivedSectionsOnSlice J R U ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} p := by
  let G := SheafOfModules.overFunctor.{u} R U
  let Hp := DerivedCategory.homologyFunctor AddCommGrpCat.{u} p
  let S := derivedSectionsOnSlice J R U ⋙ Hp
  let e₁ : derivedSectionsOverObject J R U ⋙ Hp ≅ derivedRestriction J R U ⋙ S :=
    cohomologyOverObjectIsoRestriction J R U p
  let e₂ : derivedRestriction J R U ⋙ S ≅ G.mapDerivedCategory ⋙ S :=
    Functor.isoWhiskerRight (derivedRestrictionIsoMapDerivedCategory J R U) S
  exact Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0) (e₁ ≪≫ e₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapDerivedCategorySingleFunctor 0) S ≪≫
    Functor.associator _ _ _

/-- **Stacks 03F3 (2) over a site with large objects**, for one module: the cohomology of `F`
over `U` is the cohomology of `F|_U` on the site localized at `U`. -/
def cohomologyOverObjectIsoSliceOfModule
    (p : ℤ) (F : SheafOfModules.{u} R) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
        ((derivedSectionsOverObject J R U).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj F)) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
        ((derivedSectionsOnSlice J R U).obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (R.over U)) 0).obj
            (F.over U))) :=
  (cohomologyOverObjectIsoSlice J R U p).app F

end Stacks.Cohomology.Localization.OfEssentiallySmall

end
