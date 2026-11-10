module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek for abelian sheaves on the flat-fppf site

Stacks 07AS (3) asserts, for an algebraic stack `𝒳`, that the lower-shriek functor
`g_! : Ab(𝒳_{flat,fppf}) ⥤ Ab(𝒳_{fppf})` of Stacks 0788 (2) has an unbounded left derived
functor

`Lg_! : D(𝒳_{flat,fppf}) ⟶ D(𝒳_{fppf})`,

that `Lg_!` is left adjoint to `g⁻¹`, and that `g⁻¹ ∘ Lg_! = id`.

This file assembles that from the two general theories it is the instance of:

* `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean`, which
  runs the criterion of Stacks 0794 for the lower shriek of an arbitrary continuous and
  cocontinuous functor of sites on abelian sheaves, and
* `StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfInclusion.lean`, which supplies the inclusion of
  the flat objects as such a functor, together with the invertibility of the ordinary unit
  (Stacks 077I) that turns the derived adjunction's unit into an isomorphism.

So all four of the displayed assertions of Stacks 07AS (3) — existence, the construction of
`Lg_!`, adjointness and `g⁻¹ Lg_! = id` — are reached here with no new homological algebra.

## The one remaining hypothesis, and what the tag says

The closure condition of Stacks 07AK (1) is **no longer a hypothesis**: it holds for every
algebraic stack, by `AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`. The statements
below still have to pass it to the declarations of `FlatFppfInclusion.lean`, which take it as an
argument, and they do so through `AlgebraicGeometry.Stack.FlatFppf.flatClosure`; none of them is
conditional on it.

What remains open is one hypothesis, carried explicitly by the tagged statements and named in
their tag notes:

* `AlgebraicGeometry.Stack.FlatFppf.AbelianLowerShriekAcyclic`, the acyclicity statement of
  Stacks 07AC for this inclusion: `g_!` carries a bounded above acyclic complex of abelian
  sheaves whose terms are direct sums of the extensions by zero `j_{U!} ℤ_U` to an acyclic
  complex. `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean`
  is what leaves it open, and `abelianLowerShriekAcyclic_of_ext_vanishing` below reduces it to the
  object-level vanishing `Ext^{≥1}(j_{U!} ℤ_U, g⁻¹ I) = 0` of Stacks 0D6X for an injective abelian
  sheaf `I` on `𝒳_{fppf}`. The library's form of 0D6X,
  `Stacks.CechSite.injective_sheaf_sheafCohomology_isZero_of_functor`, does not yet apply to
  this site: it requires the source site's morphism universe to be the coefficient universe,
  whereas the flat-fppf site has morphisms in `Type u` and coefficients in `Type (u + 1)`.

The tag of Stacks 07AS is placed on the covering set of its part (3), with the one condition
named in the note.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.AbelianLowerShriekAcyclic`: the acyclicity statement of
  Stacks 07AC for the flat-fppf inclusion.
* `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriek`: `Lg_!`, the unbounded total left
  derived functor of `g_!` on abelian sheaves.
* `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianRestriction`: `g⁻¹` on the unbounded derived
  categories, which needs no derivation, restriction being exact.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriek_additive` and
  `AlgebraicGeometry.Stack.FlatFppf.abelianRestriction_exact`: the two properties of the
  ordinary functors that make the derived statements well formed — `g_!` is additive, being a
  left adjoint, and `g⁻¹` is exact, having adjoints on both sides.
* `AlgebraicGeometry.Stack.FlatFppf.hasPointwiseLeftDerivedFunctor_abelianLowerShriek` and
  `AlgebraicGeometry.Stack.FlatFppf.hasLeftDerivedFunctor_abelianLowerShriek`: **Stacks 07AS
  (3)**, existence of `Lg_!`.
* `AlgebraicGeometry.Stack.FlatFppf.isIso_abelianLowerShriekAdjunction_unit`: **Stacks 077I**
  for this inclusion, as invertibility of the whole unit of `g_! ⊣ g⁻¹`.
* `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic_of_ext_vanishing`: the acyclicity
  statement follows from the object-level vanishing of **Stacks 0D6X**, so that is the only
  homological input still owed.
* `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekAdjunction`: **Stacks 07AS (3)**,
  `Lg_! ⊣ g⁻¹`.
* `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekRestrictionIso`: **Stacks 07AS
  (3)**, `g⁻¹ ∘ Lg_! = id`.

## Implementation notes

The coefficient category is `AbCat.{u, u + 1} = Ab.{u + 1}`, as in `FlatFppfInclusion.lean`:
the two sites live in `Type (u + 1)` with morphisms in `Type u`, and that is the universe in
which sheafification of abelian presheaves on them is available. In the language of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean` this is
the instance `w = u + 1` of its coefficient convention `AddCommGrpCat.{max v₁ w}`, with `v₁ = u` the
morphism universe of the flat-fppf site.

Each statement opens with the same block of local instances: continuity and cocontinuity of the
inclusion from the closure property, sheafification on the two sites and Grothendieck
abelianness of the abelian sheaves on `𝒳_{fppf}` from essential smallness of `𝒳`, and — for the
derived adjunction — the existence and absoluteness of `Lg_!` from the acyclicity statement.
They are local rather than global because they all depend on the closure property, which is a
hypothesis and not an instance.

## References

* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

section Closure

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The closure condition of Stacks 07AK (1) holds for every algebraic stack**, by
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`. It is given a short name with
implicit arguments here only because every declaration of
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfInclusion.lean` takes it as an explicit argument,
so each statement below has to pass it along. Nothing below is conditional on it. -/
abbrev flatClosure : ClosedUnderFlatMorphisms B S hS 𝒳 := closedUnderFlatMorphisms B S hS 𝒳

end Closure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- Grothendieck abelianness of the abelian sheaves on the fppf site of an algebraic stack. The
site is `Type (u + 1)` with morphisms in `Type u`, hence essentially small in `Type (u + 1)`,
and the coefficients are abelian groups in that same universe. -/
instance isGrothendieckAbelian_sheaf_fppfTopology :
    IsGrothendieckAbelian.{u + 1} (Sheaf (fppfTopology B S hS 𝒳) AbCat.{u, u + 1}) := by
  have : EssentiallySmall.{u + 1} 𝒳.val.val.obj := inferInstance
  have : IsGrothendieckAbelian.{u + 1} AbCat.{u, u + 1} := inferInstance
  have : ∀ X : 𝒳.val.val.objᵒᵖ, HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{u + 1} 𝒳.val.val.obj).inverse.op)
      AbCat.{u, u + 1} := inferInstance
  have : HasSheafify ((equivSmallModel.{u + 1} 𝒳.val.val.obj).inverse.inducedTopology
      (fppfTopology B S hS 𝒳)) AbCat.{u, u + 1} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _

/-- Grothendieck abelianness of the abelian sheaves on the flat-fppf site. As for the fppf site,
the site is `Type (u + 1)` with morphisms in `Type u`, hence essentially small in `Type (u + 1)`,
and the coefficients are abelian groups in that same universe. This is what supplies enough
injective abelian sheaves on it. -/
instance isGrothendieckAbelian_sheaf_inclusionTopology :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) := by
  have : EssentiallySmall.{u + 1}
      (ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) := inferInstance
  have : IsGrothendieckAbelian.{u + 1} AbCat.{u, u + 1} := inferInstance
  have : ∀ X : (ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳))ᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{u + 1}
        (ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳))).inverse.op)
      AbCat.{u, u + 1} := inferInstance
  have : HasSheafify ((equivSmallModel.{u + 1}
      (ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳))).inverse.inducedTopology
      (inclusionTopology B S hS 𝒳)) AbCat.{u, u + 1} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _

/-- **The lower-shriek functor on abelian sheaves is additive**, being a left adjoint between
additive categories. -/
theorem abelianLowerShriek_additive :
    (abelianLowerShriek B S hS 𝒳 flatClosure).Additive :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  Stacks.Cohomology.DerivedLowerShriek.additive_abelianLowerShriek.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι

/-- **Restriction of abelian sheaves from the fppf site to the flat-fppf site is exact.** Left
exactness is formal, restriction being the right adjoint of the lower shriek; right exactness is
cocontinuity of the inclusion, through which restriction acquires the right adjoint `g_*` of the
morphism of topoi. -/
theorem abelianRestriction_exact :
    exactFunctor _ _ (abelianInverseImage B S hS 𝒳 flatClosure) :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  Stacks.Cohomology.DerivedLowerShriek.abelianRestriction_exact.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι

/-- **Stacks 077I for the flat-fppf inclusion**, as invertibility of the whole unit: the unit
`F ⟶ g⁻¹ g_! F` of the adjunction defining the lower shriek on abelian sheaves is a natural
isomorphism. This is `AlgebraicGeometry.Stack.FlatFppf.isIso_abelianLowerShriek_unit` read as a
statement about the natural transformation rather than about its components. -/
theorem isIso_abelianLowerShriekAdjunction_unit :
    haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
    haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
    IsIso (abelianLowerShriekAdjunction B S hS 𝒳 flatClosure).unit := by
  have := isContinuous_inclusion B S hS 𝒳 flatClosure
  have := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  have : ∀ F, IsIso ((abelianLowerShriekAdjunction B S hS 𝒳 flatClosure).unit.app F) :=
    fun F => isIso_abelianLowerShriek_unit B S hS 𝒳 flatClosure F
  exact NatIso.isIso_of_isIso_app _

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The acyclicity statement of Stacks 07AC for the flat-fppf inclusion**: the lower-shriek
functor on abelian sheaves carries every bounded above acyclic complex whose terms are direct
sums of the extensions by zero `j_{U!} ℤ_U` of the constant sheaf `ℤ` on the localizations of
the flat-fppf site to an acyclic complex.

This is the one input of Stacks 07AS (3) that is open:
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean` reduces
the whole of Stacks 07AC for abelian sheaves to it. -/
abbrev AbelianLowerShriekAcyclic : Prop :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  Stacks.Cohomology.DerivedLowerShriek.AbelianLowerShriekAcyclic.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι

/-- **Stacks 0D6X is the last remaining input of Stacks 07AS (3).** The acyclicity statement for
the flat-fppf inclusion follows from the object-level vanishing

`Ext^n(j_{U!} ℤ_U, g⁻¹ I) = 0` for `U` a flat object, `I` an injective abelian sheaf on
`𝒳_{fppf}` and `n ≥ 1`,

which is exactly Stacks 0D6X for this inclusion: that `Ext` group is the degree-`n` cohomology
of `g⁻¹ I` over `U`, and it vanishes because the Čech cohomology of an injective abelian sheaf
vanishes in positive degrees and the flat-fppf site has, by the closure property, a cofinal
system of coverings closed under the iterated fibre products the Čech complex needs.

Once that vanishing is supplied, every statement in this file holds with
`AbelianLowerShriekAcyclic` discharged, and Stacks 07AS (3) carries its tag as soon as
`ClosedUnderFlatMorphisms` is discharged too. -/
theorem abelianLowerShriekAcyclic_of_ext_vanishing
    [HasExt.{u + 1} (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1})]
    (hExt : haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
      haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
      ∀ (U : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳))
        (I : Sheaf (fppfTopology B S hS 𝒳) AbCat.{u, u + 1}), Injective I → ∀ n : ℕ, 1 ≤ n →
        Subsingleton (Abelian.Ext
          (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{u + 1}
            (inclusionTopology B S hS 𝒳) U)
          ((abelianInverseImage B S hS 𝒳 flatClosure).obj I) n)) :
    AbelianLowerShriekAcyclic B S hS 𝒳 :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing.{u + 1, u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι hExt

/-- **Stacks 07AS (3), existence**, conditional on the closure property and on the acyclicity
statement: degreewise lower shriek of abelian sheaves, followed by the localization of the
homotopy category of `Ab(𝒳_{fppf})`, has a pointwise left derived functor along the localization
of the homotopy category of `Ab(𝒳_{flat,fppf})`. That is the assertion that the unbounded left
derived functor `Lg_!` exists and is defined at every object. -/
theorem hasPointwiseLeftDerivedFunctor_abelianLowerShriek
    (hFP : AbelianLowerShriekAcyclic B S hS 𝒳) :
    haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
    haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
    haveI := abelianLowerShriek_additive B S hS 𝒳
    ((abelianLowerShriek B S hS 𝒳 flatClosure).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  haveI := abelianLowerShriek_additive B S hS 𝒳
  Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι hFP

/-- **Stacks 07AS (3), existence**, in the form that asserts nothing about how `Lg_!` is
computed: degreewise lower shriek of abelian sheaves, followed by the localization of the
homotopy category of `Ab(𝒳_{fppf})`, has a left derived functor along the localization of the
homotopy category of `Ab(𝒳_{flat,fppf})`. This is the weakening of
`AlgebraicGeometry.Stack.FlatFppf.hasPointwiseLeftDerivedFunctor_abelianLowerShriek` that
forgets pointwise-ness. -/
@[stacks 07AS "part (3), existence; conditional on the acyclicity statement of 07AC"]
theorem hasLeftDerivedFunctor_abelianLowerShriek
    (hFP : AbelianLowerShriekAcyclic B S hS 𝒳) :
    haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
    haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
    haveI := abelianLowerShriek_additive B S hS 𝒳
    ((abelianLowerShriek B S hS 𝒳 flatClosure).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  haveI := abelianLowerShriek_additive B S hS 𝒳
  haveI := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳 hFP
  inferInstance

/-- **Restriction of abelian sheaves on the unbounded derived categories.** No derivation is
needed: restriction is exact, so it acts degreewise. -/
abbrev derivedAbelianRestriction :
    DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AbCat.{u, u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι

/-- **Stacks 07AS (3)**: the unbounded total left derived lower-shriek functor
`Lg_! : D(𝒳_{flat,fppf}) ⥤ D(𝒳_{fppf})` on abelian sheaves, conditional on the closure property
and on the acyclicity statement. -/
def derivedAbelianLowerShriek (hFP : AbelianLowerShriekAcyclic B S hS 𝒳) :
    DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) ⥤
      DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AbCat.{u, u + 1}) :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  haveI := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳 hFP
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι

open Stacks.Cohomology.DerivedLowerShriek
  (isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic) in
/-- **Stacks 07AS (3), adjointness**: the derived lower-shriek functor on abelian sheaves is
left adjoint to derived restriction, conditional on the closure property and on the acyclicity
statement. This is Stacks 09T5 on the unbounded derived category of the Grothendieck abelian
category `Ab(𝒳_{fppf})`, whose two inputs — existence of `Lg_!` and its absoluteness — both come
from the acyclicity statement. -/
@[stacks 07AS "part (3), adjointness; conditional on the acyclicity statement of 07AC"]
def derivedAbelianLowerShriekAdjunction (hFP : AbelianLowerShriekAcyclic B S hS 𝒳) :
    derivedAbelianLowerShriek B S hS 𝒳 hFP ⊣
      derivedAbelianRestriction B S hS 𝒳 :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  haveI := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳 hFP
  haveI := isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι hFP
      DerivedCategory.Qh
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι

open Stacks.Cohomology.DerivedLowerShriek
  (isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic) in
/-- **Stacks 07AS (3), the last assertion `g⁻¹ Lg_! = id`**: restriction after derived lower
shriek is canonically the identity of `D(𝒳_{flat,fppf})`, conditional on the closure property and
on the acyclicity statement.

The ordinary unit `F ⟶ g⁻¹ g_! F` is an isomorphism, the inclusion of the flat objects being
continuous, cocontinuous and fully faithful — that is Stacks 077I, proved as
`AlgebraicGeometry.Stack.FlatFppf.isIso_abelianLowerShriek_unit` — and uniqueness of left
derived functors carries that to the unit of the derived adjunction. -/
@[stacks 07AS "part (3), g^{-1} Lg_! = id; conditional on the acyclicity statement of 07AC"]
def derivedAbelianLowerShriekRestrictionIso (hFP : AbelianLowerShriekAcyclic B S hS 𝒳) :
    derivedAbelianLowerShriek B S hS 𝒳 hFP ⋙
        derivedAbelianRestriction B S hS 𝒳 ≅
      𝟭 (DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1})) :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  haveI := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳 hFP
  haveI := isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι hFP
      DerivedCategory.Qh
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekRestrictionIso.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
    (isIso_abelianLowerShriekAdjunction_unit B S hS 𝒳)

open Stacks.Cohomology.DerivedLowerShriek
  (isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic) in
/-- **Stacks 07AS (3), the last assertion `g⁻¹ Lg_! = id`, in unit form**: the isomorphism of
`AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekRestrictionIso` is the inverse of the
unit of the derived adjunction, so the canonical map is the one that identifies the composite
with the identity. -/
theorem isIso_derivedAbelianLowerShriekAdjunction_unit
    (hFP : AbelianLowerShriekAcyclic B S hS 𝒳) :
    IsIso (derivedAbelianLowerShriekAdjunction B S hS 𝒳 hFP).unit :=
  haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
  haveI := hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳 hFP
  haveI := isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{u + 1}
      (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι hFP
      DerivedCategory.Qh
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
      (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι)
  Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekAdjunction_unit.{u + 1}
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι
    (isIso_abelianLowerShriekAdjunction_unit B S hS 𝒳)

end Derived

end AlgebraicGeometry.Stack.FlatFppf

end
