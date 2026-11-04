module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# A compatible family of weak Serre subcategories on the localizations of a ringed site

Let `(C, O_C)` be a ringed site and suppose given, for every object `U` of `C`, a weak Serre
subcategory `A_U` of the category of `O_U`-modules. The three conditions that the source imposes
on such a family are stated here one at a time:

* restriction along a morphism `U ⟶ V` of `C` sends `A_V` into `A_U`;
* membership in `A_U` is local: for a covering `{U_i ⟶ U}` an `O_U`-module lies in `A_U` if and
  only if its restriction to `C/U_i` lies in `A_{U_i}` for every `i`;
* there is a set `B` of objects of `C` such that every object of `C` has a covering by members
  of `B`, and every `V` in `B` carries an integer `d_V` and a cofinal system of coverings of `V`
  on whose members the cohomology of *every module of `A_V`* vanishes in degrees `> d_V`.

The third condition is required for the modules of `A_V` and not only for modules defined on all
of `C`, which is what makes it stronger than the hypothesis of the Olsson--Laszlo situation of
Tag 0D6R, recorded as `Stacks.Cohomology.OlssonLaszloSituation`.

A family satisfying all three is packaged as `LocalSerreFamily`, whose fields are exactly those
conditions. It is the family-indexed counterpart of `Stacks.Cohomology.OlssonLaszloSituation`,
which carries the same cohomological bound for a single subcategory of modules on `C` itself.

## Main definitions

* `Stacks.Cohomology.CohomologicalDescent.SliceProperties`: a property of modules on `C/U`, one
  for each object `U` of `C`.
* `Stacks.Cohomology.CohomologicalDescent.IsStableUnderRestriction`: the first condition.
* `Stacks.Cohomology.CohomologicalDescent.IsLocalOnCoverings`: the second condition.
* `Stacks.Cohomology.CohomologicalDescent.LocalCohomologicalBound`: the third condition, with the
  set of good objects, the degree bounds and the cofinal covering systems stored as witnesses.
* `Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily`: the three conditions together with
  the standing assumption that each `A_U` is a weak Serre subcategory.
* `Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily.globalProperty`: the property of an
  `O_C`-module that its restriction to `C/U` lies in `A_U` for every object `U` of `C`.

## Main results

* `Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily.isWeakSerreClass_globalProperty`:
  `globalProperty` is a weak Serre subcategory of the category of `O_C`-modules.

That consequence uses only the standing assumption that each `A_U` is a weak Serre subcategory
together with the exactness of restriction to a slice; none of the three conditions enters.

## Implementation notes

The site, its morphisms, its structure sheaf and the modules all live in a single universe `w`,
which makes the abelian structure, the injectives and the sheafification of abelian sheaves on
each localization available without further hypotheses.

A covering family of `U` is a `PreZeroHypercover U`, a covering exactly when the sieve it
generates belongs to the topology. Restriction along a morphism of `C` is
`SheafOfModules.overMap` and restriction from `C` to a slice is `SheafOfModules.overFunctor`.
Cohomology of a module on `C/V` over an object of `C/V` is `Stacks.Cohomology.moduleCohomology`
for the localized structure sheaf; the sheafification hypotheses it takes as instances are
supplied inside the statement from `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`
and `Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp`, which hold for every
site. As in `Stacks.Cohomology.OlssonLaszloSituation`, the cohomological bound is integer-valued
while the right derived functors are indexed by natural numbers, hence the comparison
`degreeBound V hV < (p : ℤ)`.

## References

* [Stacks Project, Tag 0DC2](https://stacks.math.columbia.edu/tag/0DC2)
* [Stacks Project, Tag 0DC3](https://stacks.math.columbia.edu/tag/0DC3)
* [Stacks Project, Tag 0DC4](https://stacks.math.columbia.edu/tag/0DC4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Stacks.Cohomology.CohomologicalDescent

universe w

variable (X : RingedSite.{w, w, w})

/-- A family of properties of sheaves of modules on the localizations of a ringed site, one
property for each object of the site: the data `U ↦ A_U`. -/
abbrev SliceProperties : Type (w + 1) :=
  ∀ U : X.C,
    ObjectProperty (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))

/-- The first condition on a family of subcategories `A_U` of the categories of modules on the
localizations of a ringed site: for every morphism `f : U ⟶ V` of the site, the restriction functor
from modules on `C/V` to modules on `C/U` sends `A_V` into `A_U`. -/
@[stacks 0DC2 "condition (1): restriction along U ⟶ V sends A_V into A_U"]
def IsStableUnderRestriction (A : SliceProperties X) : Prop :=
  ∀ ⦃U V : X.C⦄ (f : U ⟶ V)
    (F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)),
    A V F → A U ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).obj F)

/-- The second condition on a family of subcategories `A_U` of the categories of modules on the
localizations of a ringed site: for every covering `{U_i ⟶ U}` of the site, a module on `C/U` lies
in `A_U` if and only if its restriction to `C/U_i` lies in `A_{U_i}` for every `i`. -/
@[stacks 0DC3 "condition (2): membership in A_U is local on coverings of U"]
def IsLocalOnCoverings (A : SliceProperties X) : Prop :=
  ∀ (U : X.C) (𝒰 : PreZeroHypercover.{w} U), 𝒰.sieve₀ ∈ X.J U →
    ∀ F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U),
      A U F ↔ ∀ i, A (𝒰.X i)
        ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝒰.f i)).obj F)

/-- The third condition on a family of subcategories `A_U` of the categories of modules on the
localizations of a ringed site: there is a set `B` of objects of the site such that every object
has a covering by members of `B`, and every `V` in `B` carries an integer `d_V` and a cofinal
system of coverings of `V` on whose members the cohomology of every module of `A_V` vanishes in
degrees above `d_V`. The set, the bounds and the covering systems are stored as chosen data. -/
@[stacks 0DC4 "condition (3): a locally covering set, with coverings acyclic for A_V above d_V"]
structure LocalCohomologicalBound (A : SliceProperties X) where
  /-- The set of objects with controlled cohomology. -/
  B : Set X.C
  /-- Every object of the site has a covering whose members belong to `B`. -/
  basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{w} U, 𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i)
  /-- The integer cohomological bound attached to an object of `B`. -/
  degreeBound : ∀ V : X.C, B V → ℤ
  /-- The cofinal system of coverings attached to an object of `B`. -/
  coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V
  /-- On every member of every distinguished covering of an object `V` of `B`, the cohomology of
  every module of `A_V` vanishes above the bound attached to `V`. -/
  vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{w} V), (coverings V hV).cov 𝒰 →
    letI : HasSheafify (X.J.over V) AddCommGrpCat.{w} :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{w, w, w}
    letI : (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w} :=
      Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{w, w, w}
    ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V), A V F →
        IsZero (Stacks.Cohomology.moduleCohomology
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) (Over.mk (𝒰.f i)) p F)

/-- A family of weak Serre subcategories `A_U` of the categories of modules on the localizations
of a ringed site, subject to the conditions `IsStableUnderRestriction`, `IsLocalOnCoverings` and
`LocalCohomologicalBound`. -/
structure LocalSerreFamily where
  /-- The family of subcategories, represented by their object properties. -/
  A : SliceProperties X
  /-- The standing assumption: each member of the family is a weak Serre subcategory. -/
  weakSerre : ∀ U : X.C, (A U).IsWeakSerreClass
  /-- Restriction along a morphism of the site sends `A_V` into `A_U`. -/
  restriction : IsStableUnderRestriction X A
  /-- Membership in `A_U` is local on coverings. -/
  locality : IsLocalOnCoverings X A
  /-- The locally covering set of objects with cofinal coverings acyclic for the family. -/
  bound : LocalCohomologicalBound X A

namespace LocalSerreFamily

variable (T : LocalSerreFamily.{w} X)

/-- The subcategory of the category of `O_C`-modules cut out by a family `A_U`: a module belongs
to it when its restriction to `C/U` belongs to `A_U` for every object `U` of the site. -/
def globalProperty :
    ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  fun F ↦ ∀ U : X.C,
    T.A U ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj F)

/-- The subcategory of `O_C`-modules cut out by a family of weak Serre subcategories on the
localizations is itself a weak Serre subcategory. -/
instance isWeakSerreClass_globalProperty : T.globalProperty.IsWeakSerreClass := by
  have hsh : HasSheafify X.J AddCommGrpCat.{w} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{w, w, w}
  have hwl : X.J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{w, w, w}
  have hshU : ∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w} := fun _ ↦
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{w, w, w}
  have hwlU : ∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w} := fun _ ↦
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{w, w, w}
  have hadd : ∀ U : X.C,
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U :
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤ _).Additive :=
    fun _ ↦ ⟨by intros; ext W; rfl⟩
  have hlim := fun U : X.C ↦
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
  have hcolim := fun U : X.C ↦
    have := hshU U
    have := hwlU U
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
  have : T.globalProperty.IsClosedUnderIsomorphisms :=
    { of_iso := fun e h U ↦
        have := T.weakSerre U
        (T.A U).prop_of_iso
          ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapIso e)
          (h U) }
  have : T.globalProperty.ContainsZero :=
    ⟨0, isZero_zero _, fun U ↦
      have := T.weakSerre U
      have := hadd U
      (T.A U).prop_of_isZero
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero
          (isZero_zero _))⟩
  have : T.globalProperty.IsClosedUnderKernels :=
    { kernels_le := by
        rintro _ ⟨f, k, hk, hf⟩ U
        have := T.weakSerre U
        have := hadd U
        have := hlim U
        exact (T.A U).prop_of_isLimit_kernelFork
          (k.mapIsLimit hk
            (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))
          (hf.1 U) (hf.2 U) }
  have : T.globalProperty.IsClosedUnderCokernels :=
    { cokernels_le := by
        rintro _ ⟨f, k, hk, hf⟩ U
        have := T.weakSerre U
        have := hadd U
        have := hcolim U
        exact (T.A U).prop_of_isColimit_cokernelCofork
          (k.mapIsColimit hk
            (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))
          (hf.1 U) (hf.2 U) }
  have : T.globalProperty.IsClosedUnderExtensions :=
    { prop_X₂_of_shortExact := fun hS h₁ h₃ U ↦
        have := T.weakSerre U
        have := hadd U
        have := hlim U
        have := hcolim U
        ((T.A U).inverseImage (SheafOfModules.overFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)).prop_X₂_of_shortExact
          hS (h₁ U) (h₃ U) }
  exact {}

end LocalSerreFamily

end Stacks.Cohomology.CohomologicalDescent

end
