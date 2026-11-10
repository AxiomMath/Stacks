module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek for abelian sheaves on the lisse-étale site

**Stacks 07AS (1)** asserts, for an algebraic stack `𝒳`, that the lower-shriek functor
`g_! : Ab(𝒳_{lisse,étale}) ⥤ Ab(𝒳_{étale})` of Stacks 0788 (1) has an unbounded left derived
functor `Lg_! : D(𝒳_{lisse,étale}) ⟶ D(𝒳_{étale})`, that `Lg_!` is left adjoint to `g⁻¹`, and
that `g⁻¹ ∘ Lg_! = id`. All three are proved here, for every algebraic stack and with nothing
assumed.

This is the lisse-étale sibling of
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedLowerShriek.lean` together with
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedLowerShriekUnconditional.lean`, which do
the same for part (3). The two inputs are the same ones, both already available for this site:

* `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean`, which
  runs the criterion of Stacks 0794 for the lower shriek of an arbitrary continuous and
  cocontinuous functor of sites on abelian sheaves, reducing the whole of Stacks 07AC for
  abelian sheaves to one acyclicity statement and that in turn to an object-level `Ext`
  vanishing, and
* `StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleInclusion.lean`, which supplies the inclusion
  of the smooth objects as such a functor, together with the invertibility of the ordinary unit
  (Stacks 077I) that turns the derived adjunction's unit into an isomorphism.

Part (1) is the abelian-sheaf statement only. The source notes that it is not a priori evident
that `Lg_!` for modules agrees with `Lg_!` for abelian sheaves (Cohomology on Sites, Remark
21.37.3), and nothing here appeals to any such agreement; parts (2) and (4) are the module-level
statements and are not in scope.

## Nothing is assumed

The closure condition of Stacks 07AK (1) for the smooth objects is a theorem, by
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`; the statements below pass it to
the declarations of `LisseEtaleInclusion.lean`, which take it as an argument, through
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`. Grothendieck abelianness of the
abelian sheaves on both sites, and with it enough injectives, comes from essential smallness of the
étale site of an algebraic stack. The acyclicity statement of Stacks 07AC is discharged by
`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic` below, out of the object-level
vanishing of Stacks 0D6X, which is `AlgebraicGeometry.Stack.LisseEtale.objectAcyclic`.

## Main definitions

* `AlgebraicGeometry.Stack.LisseEtale.AbelianLowerShriekAcyclic`: the acyclicity statement of
  Stacks 07AC for the lisse-étale inclusion.
* `AlgebraicGeometry.Stack.LisseEtale.derivedAbelianRestriction`: `g⁻¹` on the unbounded derived
  categories, which needs no derivation, restriction being exact.
* `AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriek`: `Lg_!`, the unbounded total
  left derived functor of `g_!` on abelian sheaves.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriek_additive` and
  `AlgebraicGeometry.Stack.LisseEtale.abelianRestriction_exact`: the two properties of the
  ordinary functors that make the derived statements well formed.
* `AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic`: the acyclicity statement of
  Stacks 07AC, discharged.
* `AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriek_hasLeftDerivedFunctor`: **Stacks 07AS
  (1)**, existence of `Lg_!`.
* `AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriekAdjunction`: **Stacks 07AS (1)**,
  `Lg_! ⊣ g⁻¹`.
* `AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriekRestrictionIso`: **Stacks 07AS
  (1)**, `g⁻¹ ∘ Lg_! = id`.

## Implementation notes

The coefficient category is `AbCat.{u, u + 1} = Ab.{u + 1}`, as in `LisseEtaleInclusion.lean`:
the two sites live in `Type (u + 1)` with morphisms in `Type u`, and that is the universe in
which sheafification of abelian presheaves on them is available. In the language of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean` this is
the instance `w = u + 1` of its coefficient convention `AddCommGrpCat.{max v₁ w}`, with `v₁ = u` the
morphism universe of the lisse-étale site. The smallness hypothesis of
`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic` is
`Small.{max v₁ w} C`, here `Small.{u + 1}` of a category in `Type (u + 1)`, which is automatic —
the same good behaviour as in the flat-fppf abelian case.

Each statement opens with the same block of local instances: continuity and cocontinuity of the
inclusion from the closure property, and — for the derived statements — the existence and
absoluteness of `Lg_!` from the acyclicity statement. They are local rather than global because
the declarations of `LisseEtaleInclusion.lean` take the closure property as an argument.

## References

* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

section Closure

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

end Closure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- Grothendieck abelianness of the abelian sheaves on the étale site of an algebraic stack. The
site is `Type (u + 1)` with morphisms in `Type u`, hence essentially small in `Type (u + 1)`,
and the coefficients are abelian groups in that same universe. -/
instance isGrothendieckAbelian_sheaf_etaleTopology :
    IsGrothendieckAbelian.{u + 1} (Sheaf
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AbCat.{u, u + 1}) := by
  have : EssentiallySmall.{u + 1} 𝒳.val.val.obj := inferInstance
  have : IsGrothendieckAbelian.{u + 1} AbCat.{u, u + 1} := inferInstance
  have : ∀ X : 𝒳.val.val.objᵒᵖ, HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{u + 1} 𝒳.val.val.obj).inverse.op)
      AbCat.{u, u + 1} := inferInstance
  have : HasSheafify ((equivSmallModel.{u + 1} 𝒳.val.val.obj).inverse.inducedTopology
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))) AbCat.{u, u + 1} :=
    inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _

/-- Grothendieck abelianness of the abelian sheaves on the lisse-étale site. As for the étale
site: a full subcategory of an essentially small category is essentially small, so the
lisse-étale site is essentially small in `Type (u + 1)`, the universe of the coefficients. This
is what supplies enough injective abelian sheaves on it. -/
instance isGrothendieckAbelian_sheaf_lisseEtale :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) := by
  have : EssentiallySmall.{u + 1} (LisseEtale.{u, w} B S hS 𝒳) := inferInstance
  have : IsGrothendieckAbelian.{u + 1} AbCat.{u, u + 1} := inferInstance
  have : ∀ X : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{u + 1} (LisseEtale.{u, w} B S hS 𝒳)).inverse.op)
      AbCat.{u, u + 1} := inferInstance
  have : HasSheafify ((equivSmallModel.{u + 1}
      (LisseEtale.{u, w} B S hS 𝒳)).inverse.inducedTopology
      (inclusionTopology.{u, w} B S hS 𝒳)) AbCat.{u, u + 1} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _

/-- Continuity of the inclusion of the smooth objects, with the closure property supplied. -/
private instance isContinuous_inclusion_of_closed :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsContinuous (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)

/-- Cocontinuity of the inclusion of the smooth objects, with the closure property supplied. -/
private instance isCocontinuous_inclusion_of_closed :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsCocontinuous (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)

/-- **The lower-shriek functor on abelian sheaves is additive**, being a left adjoint between
additive categories. -/
theorem abelianLowerShriek_additive :
    (abelianLowerShriek.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).Additive :=
  Stacks.Cohomology.DerivedLowerShriek.additive_abelianLowerShriek.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι

/-- Additivity of the lower shriek, as an instance. -/
private instance abelianLowerShriek_additive_of_closed :
    (abelianLowerShriek.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).Additive :=
  abelianLowerShriek_additive.{u, w} B S hS 𝒳

/-- **Restriction of abelian sheaves from the étale site to the lisse-étale site is exact.**
Left exactness is formal, restriction being the right adjoint of the lower shriek; right
exactness is cocontinuity of the inclusion, through which restriction acquires the right adjoint
`g_*` of the morphism of topoi. -/
theorem abelianRestriction_exact :
    exactFunctor _ _
      (abelianInverseImage.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)) :=
  Stacks.Cohomology.DerivedLowerShriek.abelianRestriction_exact.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι

/-- **Stacks 077I for the lisse-étale inclusion**, as invertibility of the whole unit: the unit
`F ⟶ g⁻¹ g_! F` of the adjunction defining the lower shriek on abelian sheaves is a natural
isomorphism. This is `AlgebraicGeometry.Stack.LisseEtale.isIso_abelianLowerShriek_unit` read as
a statement about the natural transformation rather than about its components. -/
theorem isIso_abelianLowerShriekAdjunction_unit :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    IsIso (abelianLowerShriekAdjunction.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).unit := by
  have : ∀ F, IsIso ((abelianLowerShriekAdjunction.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).unit.app F) :=
    fun F => isIso_abelianLowerShriek_unit.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳) F
  exact NatIso.isIso_of_isIso_app _

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The acyclicity statement of Stacks 07AC for the lisse-étale inclusion**: the lower-shriek
functor on abelian sheaves carries every bounded above acyclic complex whose terms are direct
sums of the extensions by zero `j_{U!} ℤ_U` of the constant sheaf `ℤ` on the localizations of
the lisse-étale site to an acyclic complex.

`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean` reduces
the whole of Stacks 07AC for abelian sheaves to it, and
`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic` proves it. -/
abbrev AbelianLowerShriekAcyclic : Prop :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  Stacks.Cohomology.DerivedLowerShriek.AbelianLowerShriekAcyclic.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι

/-- **The acyclicity statement of Stacks 07AC reduces to the object-level vanishing of
Stacks 0D6X.** If

`Ext^n(j_{U!} ℤ_U, g⁻¹ I) = 0` for `U` a smooth object, `I` an injective abelian sheaf on
`𝒳_{étale}` and `n ≥ 1`,

then the acyclicity statement holds for the lisse-étale inclusion. That `Ext` group is the
degree-`n` cohomology of `g⁻¹ I` over `U`, so the hypothesis is exactly Stacks 0D6X for this
inclusion. -/
theorem abelianLowerShriekAcyclic_of_ext_vanishing
    [HasExt.{u + 1} (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1})]
    (hExt : haveI :=
        isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
      haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
      ∀ (U : LisseEtale.{u, w} B S hS 𝒳)
        (I : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) AbCat.{u, u + 1}),
        Injective I → ∀ n : ℕ, 1 ≤ n →
        Subsingleton (Abelian.Ext
          (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{u + 1}
            (inclusionTopology.{u, w} B S hS 𝒳) U)
          ((abelianInverseImage.{u, w} B S hS 𝒳
            (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).obj I) n)) :
    AbelianLowerShriekAcyclic.{u, w} B S hS 𝒳 :=
  Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing.{u + 1, u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι hExt

/-- **The acyclicity statement of Stacks 07AC for the lisse-étale inclusion, discharged.** The
lower-shriek functor on abelian sheaves carries every bounded above acyclic complex whose terms
are direct sums of the extensions by zero `j_{U!} ℤ_U` to an acyclic complex.

`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic_of_ext_vanishing` reduces it to
the object-level vanishing of Stacks 0D6X, which is
`AlgebraicGeometry.Stack.LisseEtale.objectAcyclic`. -/
theorem abelianLowerShriekAcyclic : AbelianLowerShriekAcyclic.{u, w} B S hS 𝒳 := by
  refine abelianLowerShriekAcyclic_of_ext_vanishing.{u, w} B S hS 𝒳 ?_
  intro U I hI n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨fun a b ↦ by
    rw [objectAcyclic.{u, w} B S hS 𝒳 I hI U m a, objectAcyclic.{u, w} B S hS 𝒳 I hI U m b]⟩

/-- **Stacks 07AS (1), existence, in pointwise form.** Degreewise lower shriek of abelian
sheaves, followed by the localization of the homotopy category of `Ab(𝒳_{étale})`, has a
pointwise left derived functor along the localization of the homotopy category of
`Ab(𝒳_{lisse,étale})`. That is the assertion that the unbounded left derived functor `Lg_!`
exists and is defined at every object. -/
theorem abelianLowerShriek_hasPointwiseLeftDerivedFunctor :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := abelianLowerShriek_additive.{u, w} B S hS 𝒳
    ((abelianLowerShriek.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι (abelianLowerShriekAcyclic.{u, w} B S hS 𝒳)

/-- Pointwise existence of `Lg_!`, as an instance. -/
private instance abelianLowerShriek_hasPointwiseLeftDerivedFunctor_of_closed :
    ((abelianLowerShriek.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) :=
  abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳

/-- **Stacks 07AS (1), existence of `Lg_!`, for every algebraic stack.** Degreewise lower shriek
of abelian sheaves, followed by the localization of the homotopy category of `Ab(𝒳_{étale})`,
has a left derived functor along the localization of the homotopy category of
`Ab(𝒳_{lisse,étale})`. This is the weakening of
`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriek_hasPointwiseLeftDerivedFunctor` that
forgets pointwise-ness. -/
@[stacks 07AS "part (1), existence of the unbounded left derived functor `Lg_!` on abelian \
sheaves for the lisse-étale site, with NO hypothesis. The acyclicity statement of Tag 07AC is \
discharged by `AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic`, which is proved \
for every algebraic stack out of the object-level vanishing of Tag 0D6X, \
`AlgebraicGeometry.Stack.LisseEtale.objectAcyclic`. The closure condition of Tag 07AK (1) for \
the smooth objects is likewise a theorem here, not a hypothesis, namely \
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`. Only the abelian-sheaf \
statement for the lisse-étale site is covered: parts (2) and (4) are the module-level \
statements, which the source does not know to agree with the abelian one, and part (3) is the \
flat-fppf site"]
theorem abelianLowerShriek_hasLeftDerivedFunctor :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := abelianLowerShriek_additive.{u, w} B S hS 𝒳
    ((abelianLowerShriek.{u, w} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) :=
  inferInstance

/-- **Restriction of abelian sheaves on the unbounded derived categories.** No derivation is
needed: restriction is exact, so it acts degreewise. -/
abbrev derivedAbelianRestriction :
    DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        AbCat.{u, u + 1}) ⥤
      DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι

/-- **The unbounded total left derived lower-shriek functor `Lg_!` on abelian sheaves** for the
lisse-étale site of an algebraic stack, `Lg_! : D(𝒳_{lisse,étale}) ⥤ D(𝒳_{étale})`. -/
abbrev derivedAbelianLowerShriek :
    DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) ⥤
      DerivedCategory (Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        AbCat.{u, u + 1}) :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι

open Stacks.Cohomology.DerivedLowerShriek
  (isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic) in
/-- The absoluteness of `Lg_!` on abelian sheaves for the lisse-étale site: the composite of
`Lg_!` with any functor out of `D(𝒳_{étale})` is again a left derived functor. This is the
second hypothesis of the derived adjunction of Stacks 09T5, and it comes from the same
acyclicity statement as the existence of `Lg_!`. -/
theorem isLeftDerivedFunctor_derivedAbelianLowerShriek_comp :
    haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
    (derivedAbelianLowerShriek.{u, w} B S hS 𝒳 ⋙
        derivedAbelianRestriction.{u, w} B S hS 𝒳).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedAbelianLowerShriek.{u, w} B S hS 𝒳)
        (derivedAbelianRestriction.{u, w} B S hS 𝒳)).inv ≫
        Functor.whiskerRight
          (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{u + 1}
            (inclusionTopology.{u, w} B S hS 𝒳)
            (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
            (smoothObject.{u, w} B S hS 𝒳).ι)
          (derivedAbelianRestriction.{u, w} B S hS 𝒳))
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι (abelianLowerShriekAcyclic.{u, w} B S hS 𝒳)
    DerivedCategory.Qh (derivedAbelianLowerShriek.{u, w} B S hS 𝒳)
    (Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{u + 1}
      (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι)
    (derivedAbelianRestriction.{u, w} B S hS 𝒳)

/-- **Stacks 07AS (1), adjointness, for every algebraic stack.** The unbounded derived
lower-shriek functor on abelian sheaves is left adjoint to derived restriction. This is Stacks
09T5 on the unbounded derived category of the Grothendieck abelian category `Ab(𝒳_{étale})`,
whose two inputs — existence of `Lg_!` and its absoluteness — both come from the acyclicity
statement. -/
@[stacks 07AS "part (1), the adjunction `Lg_! ⊣ g⁻¹` on abelian sheaves for the lisse-étale \
site, with NO hypothesis: the acyclicity statement of Tag 07AC that supplies both the existence \
of `Lg_!` and its absoluteness is discharged by \
`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic`, itself proved out of the \
object-level vanishing of Tag 0D6X, `AlgebraicGeometry.Stack.LisseEtale.objectAcyclic`, and the \
closure condition of Tag 07AK (1) by \
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`. Only the abelian-sheaf \
statement for the lisse-étale site: parts (2) and (4) are the module-level statements and part \
(3) is the flat-fppf site"]
def derivedAbelianLowerShriekAdjunction :
    derivedAbelianLowerShriek.{u, w} B S hS 𝒳 ⊣ derivedAbelianRestriction.{u, w} B S hS 𝒳 :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
  haveI := isLeftDerivedFunctor_derivedAbelianLowerShriek_comp.{u, w} B S hS 𝒳
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι

/-- **Stacks 07AS (1), `g⁻¹ Lg_! = id`, for every algebraic stack.** Restriction after derived
lower shriek is canonically the identity of `D(𝒳_{lisse,étale})`.

The ordinary unit `F ⟶ g⁻¹ g_! F` is an isomorphism, the inclusion of the smooth objects being
continuous, cocontinuous and fully faithful — that is Stacks 077I, which for this inclusion is
`AlgebraicGeometry.Stack.LisseEtale.isIso_abelianLowerShriek_unit` — and uniqueness of left
derived functors carries that to the unit of the derived adjunction. -/
@[stacks 07AS "part (1), `g⁻¹ ∘ Lg_! = id` on abelian sheaves for the lisse-étale site, with NO \
hypothesis: the acyclicity statement of Tag 07AC is discharged by \
`AlgebraicGeometry.Stack.LisseEtale.abelianLowerShriekAcyclic`, out of the object-level \
vanishing of Tag 0D6X, `AlgebraicGeometry.Stack.LisseEtale.objectAcyclic`; the closure \
condition of Tag 07AK (1) by \
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`; and the invertibility of the \
ordinary unit is Tag 077I, \
`AlgebraicGeometry.Stack.LisseEtale.isIso_abelianLowerShriek_unit`. Only the abelian-sheaf \
statement for the lisse-étale site: parts (2) and (4) are the module-level statements and part \
(3) is the flat-fppf site"]
def derivedAbelianLowerShriekRestrictionIso :
    derivedAbelianLowerShriek.{u, w} B S hS 𝒳 ⋙ derivedAbelianRestriction.{u, w} B S hS 𝒳 ≅
      𝟭 (DerivedCategory (Sheaf (inclusionTopology.{u, w} B S hS 𝒳) AbCat.{u, u + 1})) :=
  haveI := isContinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := isCocontinuous_inclusion.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  haveI := abelianLowerShriek_hasPointwiseLeftDerivedFunctor.{u, w} B S hS 𝒳
  haveI := isLeftDerivedFunctor_derivedAbelianLowerShriek_comp.{u, w} B S hS 𝒳
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekRestrictionIso.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι
    (isIso_abelianLowerShriekAdjunction_unit.{u, w} B S hS 𝒳)

/-- **Stacks 07AS (1), `g⁻¹ Lg_! = id`, in unit form**: the isomorphism of
`AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriekRestrictionIso` is the inverse of
the unit of the derived adjunction, so the canonical map is the one that identifies the
composite with the identity. -/
theorem isIso_derivedAbelianLowerShriekAdjunction_unit :
    IsIso (derivedAbelianLowerShriekAdjunction.{u, w} B S hS 𝒳).unit :=
  have := isLeftDerivedFunctor_derivedAbelianLowerShriek_comp.{u, w} B S hS 𝒳
  Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekAdjunction_unit.{u + 1}
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (smoothObject.{u, w} B S hS 𝒳).ι
    (isIso_abelianLowerShriekAdjunction_unit.{u, w} B S hS 𝒳)

end Derived

end AlgebraicGeometry.Stack.LisseEtale

end
