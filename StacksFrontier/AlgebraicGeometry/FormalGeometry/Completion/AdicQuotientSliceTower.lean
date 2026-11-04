module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerSiteComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.IdealSmulRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSmulQuotientTower

/-!
# The restriction of the adic quotient tower is the slice's own adic quotient tower

Let `X` be a scheme, `𝓘` a quasi-coherent sheaf of ideals, `ℱ` a sheaf of `𝒪_X`-modules and `V`
an open of `X`. The tower `Stacks.Algebraization.adicQuotientSystem 𝓘 ℱ` is `n ↦ ℱ/𝓘ⁿℱ`, formed
on the scheme. The slice of the small Zariski site over `V` carries its own such tower,
`Stacks.Sites.idealSmulQuotientTower (ℱ|_V) (𝓘|_V)`, formed on the ringed site and available
there because the slice of an opens site is not an opens site of a scheme. This file identifies
them:

**the restriction of the scheme's adic quotient tower to the slice over `V` is the slice's own
adic quotient tower**, compatibly with the quotient projections out of `ℱ|_V`.

## Main results

* `Stacks.Algebraization.overSubmodule_idealPowerMultiple` — `(𝓘ⁿℱ)|_V = (𝓘|_V)ⁿ(ℱ|_V)`, the
  identification of the subsheaves being quotiented out.
* `Stacks.Algebraization.adicQuotientSliceIso` and
  `Stacks.Algebraization.π_comp_adicQuotientSliceIso` — the identification term by term, with the
  quotient projections.
* `Stacks.Algebraization.adicQuotientSliceTowerIso` and
  `Stacks.Algebraization.π_comp_adicQuotientSliceTowerIso_hom_app` — **the identification of the
  towers**, with the quotient projections.

## What this is for

It turns the hypothesis of `Stacks.Algebraization.isIso_comparison_of_affineOpens` of
`Completion/AdicQuotientSliceDescent.lean` — a derived-limit presentation of `(ℱ|_V)^∧` over the
*restriction* of the scheme's tower — into one over the slice's own tower, the tower the Koszul
chain of `DerivedCompletionRinged/` presents `(ℱ|_V)^∧` over. The descent asks for nothing else.

## Where the restatement lives, and a retracted obstruction

The restatement of `Stacks.Algebraization.isIso_comparison_of_affineOpens` over the slice's own
tower is done in `Completion/AdicQuotientSliceTowerDescent.lean`: the identification below is
carried into the derived category by `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`,
and the presentation is transported along it by
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.ofNatIso` of
`Homology/DerivedCategory/InverseSystem/DerivedLimitWithProjectionsFunctor.lean` (the
pro-isomorphism transport `comp_of_hasEventualInverses` at the degenerate pro-isomorphism,
carrying the projections along).

Earlier prose recorded that step as blocked by a clash between two names for the category of
modules on the slice: `AlgebraicGeometry.RingedSite.restrictModulesToSlice`, hence
`Stacks.Sites.idealSmulQuotientTower` and everything in this file, is valued in
`AlgebraicGeometry.RingedSite.Modules ((opensRingedSite X.sheaf).over V)`, while
`Stacks.Algebraization.isIso_comparison_of_affineOpens` is stated with
`SheafOfModules.overFunctor`, hence at
`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O).over V)`;
the derived category of the first was said to have no `CategoryTheory.Pretriangulated` instance
that search finds (nor `HasZeroObject`, `HasShift ℤ`, `Preadditive`, or the additivity of its
shifts), `AlgebraicGeometry.RingedSite.Modules` being a `def` instance search does not unfold.

**That is false, and no repair was needed.** `AlgebraicGeometry.RingedSite.Modules` of
`CategoryTheory/Sites/Cohomology/DerivedTensor/Interface.lean` is an `abbrev`, so instance search
crosses to the second spelling on its own: `CategoryTheory.Abelian`,
`CategoryTheory.HasDerivedCategory`, all five derived-category instances and
`DerivedCategory.singleFunctor` resolve at the `RingedSite.Modules` spelling, and the composite
isomorphism of towers crosses the two spellings in the unifier. Neither the five instances nor a
restatement of `Stacks.Sites.idealSmulQuotientTower` was installed. Nor is it a bridge between
ring-sheaf spellings: both sides are at `AlgebraicGeometry.RingedSite.ringSheaf`, i.e. at
`(sheafCompose J (forget₂ CommRingCat RingCat)).obj`.

What is genuinely not crossed is a `rw`, for the reason the implementation notes below record; that
is a tactic restriction, not an obstruction.

## Implementation notes

Both towers are towers of cokernels, so the whole identification is the identification of the
subsheaves being quotiented out, plus the exactness of restriction. The first is
`Stacks.Algebraization.idealPowerMultiple_eq_idealPowSmul` of
`Completion/IdealPowerSiteComparison.lean` — the scheme's `𝓘ⁿℱ` is the site's — composed with
`AlgebraicGeometry.RingedSite.overSubmodule_idealPowSmul` of
`DerivedCompletionRinged/IdealSmulRestriction.lean` — the site's `𝓘ⁿℱ` restricts to `(𝓘|_V)ⁿ` of
the restriction — and `overSubmodule_top`, since the product the quotients are formed with is
`𝓘ⁿ⊤`. The second is `AlgebraicGeometry.RingedSite.cokernelOverSubmoduleIsoOfEq` of the same
file.

Naturality in `n` is proved by cancelling the epimorphism `ℱ|_V ⟶ (ℱ/𝓘ⁿ⁺¹ℱ)|_V`: both legs of
the square compose with it to the quotient projection at the smaller index, by
`Stacks.Algebraization.quotientMapOfLE_π` upstairs and
`Stacks.Sites.idealSmulQuotientπ_comp_idealSmulQuotientTower_map_succ` downstairs. Only the
successive squares are needed, `CategoryTheory.NatTrans.ofOpSequence` supplying the rest. The
epimorphism cancelled is the one of the *slice*, `Stacks.Sites.idealSmulQuotientπ`, taken after
the inverse of the identification of the terms rather than the restricted quotient projection
directly, because `Epi` of the latter is not found by instance search at the spelling
`(restrictModulesToSlice …).map (cokernel.π …)` while `Epi (cokernel.π …)` in the slice is.

Every chain below is `Eq.trans`ed with `congrArg` rather than rewritten. `X.Modules` is a `def`
for `SheafOfModules X.ringCatSheaf` and `AlgebraicGeometry.RingedSite.Modules` of the opens
ringed site is a third spelling of the same category; the three are definitionally but not
reducibly equal, so a goal in which a tactic has brought two of them together is not type-correct
at the transparency `rw` builds its motive at and no rewrite fires on it — exactly as the
implementation notes of `DerivedCompletionRinged/StrictAdicRestrictionToAnOpen.lean` record for
the same crossing.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.SheafOfModules (opensRingedSite)
open AlgebraicGeometry.RingedSite (restrictModulesToSlice overIdeal)
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
attribute [local instance] Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp

variable {X : Scheme.{u}} (I : X.IdealSheafData) (ℱ : X.Modules) (V : X.Opens)

/-- **`(𝓘ⁿℱ)|_V = (𝓘|_V)ⁿ(ℱ|_V)`**: the subsheaf quotiented out by the `n`-th term of the
scheme's adic quotient tower restricts to the one quotiented out by the `n`-th term of the
slice's.

The scheme's `𝓘ⁿℱ` is the site's `𝓘ⁿ⊤` by
`Stacks.Algebraization.idealPowerMultiple_eq_idealPowSmul`, the site's commutes with restriction
by `AlgebraicGeometry.RingedSite.overSubmodule_idealPowSmul`, and `⊤` restricts to `⊤` by
`AlgebraicGeometry.RingedSite.overSubmodule_top`. -/
theorem overSubmodule_idealPowerMultiple (n : ℕ) :
    (idealPowerMultiple I n ℱ).over V =
      Stacks.Sites.idealPowSmul (O := ((opensRingedSite X.sheaf).over V).O)
        (overIdeal (idealSheafSiteSubmodule I) V) n ⊤ :=
  ((congrArg (fun N => SheafOfModules.Submodule.over N V)
        (idealPowerMultiple_eq_idealPowSmul I ℱ n)).trans
      (AlgebraicGeometry.RingedSite.overSubmodule_idealPowSmul (opensRingedSite X.sheaf) V
        (idealSheafSiteSubmodule I) ⊤ n)).trans
    (congrArg
      (fun N => Stacks.Sites.idealPowSmul (O := ((opensRingedSite X.sheaf).over V).O)
        (overIdeal (idealSheafSiteSubmodule I) V) n N)
      (AlgebraicGeometry.RingedSite.overSubmodule_top (opensRingedSite X.sheaf) V))

/-- **The `n`-th term of the restricted adic quotient tower is the `n`-th term of the slice's
own.** -/
def adicQuotientSliceIso (n : ℕ) :
    (restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ((adicQuotientSystem I ℱ).obj ⟨n⟩) ≅
      Stacks.Sites.idealSmulQuotient
        ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
        (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
          (overIdeal (idealSheafSiteSubmodule I) V) n) :=
  AlgebraicGeometry.RingedSite.cokernelOverSubmoduleIsoOfEq (opensRingedSite X.sheaf) V
    (overSubmodule_idealPowerMultiple I ℱ V n)

/-- **The identification of the `n`-th terms respects the quotient projections.** -/
@[reassoc]
theorem π_comp_adicQuotientSliceIso (n : ℕ) :
    (restrictModulesToSlice (opensRingedSite X.sheaf) V).map
          (cokernel.π (C := X.Modules) (idealPowerMultiple I n ℱ).ι) ≫
        (adicQuotientSliceIso I ℱ V n).hom =
      Stacks.Sites.idealSmulQuotientπ
        ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
        (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
          (overIdeal (idealSheafSiteSubmodule I) V) n) :=
  AlgebraicGeometry.RingedSite.π_comp_cokernelOverSubmoduleIsoOfEq (opensRingedSite X.sheaf) V
    (overSubmodule_idealPowerMultiple I ℱ V n)

/-- The quotient projection of the slice, read through the identification of the terms, is the
restriction of the quotient projection upstairs. -/
theorem π_comp_adicQuotientSliceIso_inv (n : ℕ) :
    Stacks.Sites.idealSmulQuotientπ
          ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
          (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
            (overIdeal (idealSheafSiteSubmodule I) V) n) ≫
        (adicQuotientSliceIso I ℱ V n).inv =
      (restrictModulesToSlice (opensRingedSite X.sheaf) V).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I n ℱ).ι) :=
  ((Iso.eq_comp_inv _).2 (π_comp_adicQuotientSliceIso I ℱ V n)).symm

/-- **The left leg of the naturality square, after the two cancellations.** The transition map
of the restricted tower, precomposed with the quotient projection of the slice read through the
identification of the terms, is the quotient projection of the slice at the smaller index. -/
theorem adicQuotientSliceNaturalityLeft (n : ℕ) :
    Stacks.Sites.idealSmulQuotientπ
      ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
      (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
        (overIdeal (idealSheafSiteSubmodule I) V) (n + 1)) ≫
        (adicQuotientSliceIso I ℱ V (n + 1)).inv ≫
          ((adicQuotientSystem I ℱ ⋙ restrictModulesToSlice (opensRingedSite X.sheaf) V).map
              (homOfLE (Nat.le_succ n)).op ≫
            (adicQuotientSliceIso I ℱ V n).hom) =
      Stacks.Sites.idealSmulQuotientπ
      ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
      (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
        (overIdeal (idealSheafSiteSubmodule I) V) n) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun w => w ≫
    ((adicQuotientSystem I ℱ ⋙ restrictModulesToSlice (opensRingedSite X.sheaf) V).map
        (homOfLE (Nat.le_succ n)).op ≫ (adicQuotientSliceIso I ℱ V n).hom))
    (π_comp_adicQuotientSliceIso_inv I ℱ V (n + 1))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun w => w ≫ (adicQuotientSliceIso I ℱ V n).hom)
    (((restrictModulesToSlice (opensRingedSite X.sheaf) V).map_comp _ _).symm.trans
      (congrArg (restrictModulesToSlice (opensRingedSite X.sheaf) V).map
        (quotientMapOfLE_π (idealPowerMultiple_antitone I ℱ (Nat.le_succ n)))))) ?_
  exact π_comp_adicQuotientSliceIso I ℱ V n

/-- **The right leg of the naturality square, after the two cancellations.** The identification
of the terms cancels against its own inverse, leaving the compatibility of the quotient
projections of the slice with the transition map of the slice's tower. -/
theorem adicQuotientSliceNaturalityRight (n : ℕ) :
    Stacks.Sites.idealSmulQuotientπ
      ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
      (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
        (overIdeal (idealSheafSiteSubmodule I) V) (n + 1)) ≫
        (adicQuotientSliceIso I ℱ V (n + 1)).inv ≫
          ((adicQuotientSliceIso I ℱ V (n + 1)).hom ≫
            (Stacks.Sites.idealSmulQuotientTower
              ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
              (overIdeal (idealSheafSiteSubmodule I) V)).map
              (homOfLE (Nat.le_succ n)).op) =
      Stacks.Sites.idealSmulQuotientπ
      ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
      (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
        (overIdeal (idealSheafSiteSubmodule I) V) n) := by
  refine Eq.trans (congrArg (fun w => Stacks.Sites.idealSmulQuotientπ
      ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
      (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
        (overIdeal (idealSheafSiteSubmodule I) V) (n + 1)) ≫ w)
    (Iso.inv_hom_id_assoc (adicQuotientSliceIso I ℱ V (n + 1)) _)) ?_
  exact Stacks.Sites.idealSmulQuotientπ_comp_idealSmulQuotientTower_map_succ
    ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
    (overIdeal (idealSheafSiteSubmodule I) V) n

/-- The identifications of the terms, assembled into a morphism of towers.

Naturality is checked after cancelling two epimorphisms into the restricted `(n+1)`-st term —
the inverse of the identification there, and the quotient projection of the slice — which
reduces both legs of the square to the quotient projection of the slice at `n`,
`Stacks.Algebraization.adicQuotientSliceNaturalityLeft` and
`adicQuotientSliceNaturalityRight`. -/
def adicQuotientSliceTowerNatTrans :
    adicQuotientSystem I ℱ ⋙ restrictModulesToSlice (opensRingedSite X.sheaf) V ⟶
      Stacks.Sites.idealSmulQuotientTower
        ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
        (overIdeal (idealSheafSiteSubmodule I) V) :=
  NatTrans.ofOpSequence (fun n => (adicQuotientSliceIso I ℱ V n).hom) fun n => by
    refine (cancel_epi (adicQuotientSliceIso I ℱ V (n + 1)).inv).1 ?_
    refine (cancel_epi (Stacks.Sites.idealSmulQuotientπ
      ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
      (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
        (overIdeal (idealSheafSiteSubmodule I) V) (n + 1)))).1 ?_
    exact (adicQuotientSliceNaturalityLeft I ℱ V n).trans
      (adicQuotientSliceNaturalityRight I ℱ V n).symm

/-- Each component of `Stacks.Algebraization.adicQuotientSliceTowerNatTrans` is an isomorphism. -/
instance isIso_adicQuotientSliceTowerNatTrans_app (n : ℕᵒᵖ) :
    IsIso ((adicQuotientSliceTowerNatTrans I ℱ V).app n) :=
  inferInstanceAs (IsIso (adicQuotientSliceIso I ℱ V n.unop).hom)

/-- **The restriction of the scheme's adic quotient tower to the slice over `V` is the slice's
own adic quotient tower**, naturally in the index. -/
def adicQuotientSliceTowerIso :
    adicQuotientSystem I ℱ ⋙ restrictModulesToSlice (opensRingedSite X.sheaf) V ≅
      Stacks.Sites.idealSmulQuotientTower
        ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
        (overIdeal (idealSheafSiteSubmodule I) V) :=
  haveI : IsIso (adicQuotientSliceTowerNatTrans I ℱ V) := NatIso.isIso_of_isIso_app _
  asIso (adicQuotientSliceTowerNatTrans I ℱ V)

/-- The identification of the towers acts termwise as
`Stacks.Algebraization.adicQuotientSliceIso`. -/
theorem adicQuotientSliceTowerIso_hom_app (n : ℕᵒᵖ) :
    (adicQuotientSliceTowerIso I ℱ V).hom.app n = (adicQuotientSliceIso I ℱ V n.unop).hom :=
  rfl

/-- **The identification of the towers respects the quotient projections.** This is what pins it
down: two quotients of one sheaf of modules are isomorphic over it exactly when they are
quotients by the same subsheaf. -/
@[reassoc]
theorem π_comp_adicQuotientSliceTowerIso_hom_app (n : ℕ) :
    (restrictModulesToSlice (opensRingedSite X.sheaf) V).map
          (cokernel.π (C := X.Modules) (idealPowerMultiple I n ℱ).ι) ≫
        (adicQuotientSliceTowerIso I ℱ V).hom.app ⟨n⟩ =
      Stacks.Sites.idealSmulQuotientπ
        ((restrictModulesToSlice (opensRingedSite X.sheaf) V).obj ℱ)
        (Stacks.Sites.idealPow (O := ((opensRingedSite X.sheaf).over V).O)
          (overIdeal (idealSheafSiteSubmodule I) V) n) :=
  π_comp_adicQuotientSliceIso I ℱ V n

end Stacks.Algebraization

end
