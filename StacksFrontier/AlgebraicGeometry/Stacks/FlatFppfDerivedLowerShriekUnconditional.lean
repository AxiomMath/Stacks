module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek on the flat-fppf site, with its acyclicity input discharged

Let `𝒳` be an algebraic stack and let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the comparison
morphism of topoi whose inverse image is restriction to the flat objects. **Stacks 07AS (3)**
asserts that the lower-shriek functor `g_! : Ab(𝒳_{flat,fppf}) ⥤ Ab(𝒳_{fppf})` has an unbounded
left derived functor `Lg_! : D(𝒳_{flat,fppf}) ⟶ D(𝒳_{fppf})`, that `Lg_!` is left adjoint to
`g⁻¹`, and that `g⁻¹ ∘ Lg_! = id`.

`AlgebraicGeometry.Stack.FlatFppf.hasLeftDerivedFunctor_abelianLowerShriek`,
`AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekAdjunction` and
`AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekRestrictionIso` prove the three with the
acyclicity statement of **Stacks 07AC** for this inclusion as an explicit hypothesis `hFP`, and
`AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic` proves that acyclicity statement for
every algebraic stack, out of the object-level vanishing of **Stacks 0D6X**. This file states the
three assertions with `hFP` discharged by it.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriek_hasLeftDerivedFunctor`: **Stacks 07AS
  (3)**, existence of `Lg_!`, for every algebraic stack.
* `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekFunctor`: the functor `Lg_!` itself.
* `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekFunctorAdjunction`: **Stacks 07AS
  (3)**, `Lg_! ⊣ g⁻¹`.
* `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekFunctorRestrictionIso`:
  **Stacks 07AS (3)**, `g⁻¹ ∘ Lg_! = id`.

## Implementation notes

Nothing is assumed. The closure condition of **Stacks 07AK** (1) holds for every algebraic stack
by `AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`; Grothendieck abelianness of the
abelian sheaves on both sites and the existence of `g_!` and `g_*` come from essential smallness
of the site of an algebraic stack; and the acyclicity statement of **Stacks 07AC** is
`AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic`. The declarations here are the
statements carrying `hFP` instantiated at that theorem.

Only part (3) of **Stacks 07AS**, the abelian-sheaf statement for the flat-fppf site, is treated
here. Part (1) is the lisse-étale analogue
(`AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriekAdjunction`), and parts (2) and (4)
are the module-level statements, which rest on the module-level acyclicity input of
**Stacks 07AC** rather than the abelian-sheaf one used here.

## References

* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 077I](https://stacks.math.columbia.edu/tag/077I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AS (3), existence, in pointwise form and with no hypothesis.** Degreewise lower
shriek of abelian sheaves, followed by the localization of the homotopy category of
`Ab(𝒳_{fppf})`, has a pointwise left derived functor along the localization of the homotopy
category of `Ab(𝒳_{flat,fppf})`. -/
theorem abelianLowerShriek_hasPointwiseLeftDerivedFunctor :
    haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
    haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
    haveI := abelianLowerShriek_additive B S hS 𝒳
    ((abelianLowerShriek B S hS 𝒳 flatClosure).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) :=
  hasPointwiseLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳
    (abelianLowerShriekAcyclic B S hS 𝒳)

/-- **Stacks 07AS (3), existence of `Lg_!`, for every algebraic stack.** Degreewise lower shriek
of abelian sheaves, followed by the localization of the homotopy category of `Ab(𝒳_{fppf})`, has
a left derived functor along the localization of the homotopy category of `Ab(𝒳_{flat,fppf})`. -/
@[stacks 07AS "part (3), existence of the unbounded left derived functor `Lg_!` on abelian \
sheaves for the flat-fppf site, with NO hypothesis. The acyclicity statement of Tag 07AC that \
`AlgebraicGeometry.Stack.FlatFppf.hasLeftDerivedFunctor_abelianLowerShriek` carries as the \
argument `hFP` is discharged here by \
`AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic`, which is proved for every \
algebraic stack out of the object-level vanishing of Tag 0D6X; that theorem lives downstream of \
the file carrying the conditional form, which is why the conditional form could not cite it. \
The closure condition of Tag 07AK (1) is likewise a theorem here, not a hypothesis. Only part \
(3) is covered: parts (1), (2) and (4) are elsewhere"]
theorem abelianLowerShriek_hasLeftDerivedFunctor :
    haveI := isContinuous_inclusion B S hS 𝒳 flatClosure
    haveI := isCocontinuous_inclusion B S hS 𝒳 flatClosure
    haveI := abelianLowerShriek_additive B S hS 𝒳
    ((abelianLowerShriek B S hS 𝒳 flatClosure).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_abelianLowerShriek B S hS 𝒳 (abelianLowerShriekAcyclic B S hS 𝒳)

/-- **The unbounded total left derived lower-shriek functor `Lg_!` on abelian sheaves** for the
flat-fppf site of an algebraic stack, with no hypothesis. -/
abbrev derivedAbelianLowerShriekFunctor :
    DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1}) ⥤
      DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AbCat.{u, u + 1}) :=
  derivedAbelianLowerShriek B S hS 𝒳 (abelianLowerShriekAcyclic B S hS 𝒳)

/-- **Stacks 07AS (3), adjointness, for every algebraic stack.** The unbounded derived
lower-shriek functor on abelian sheaves is left adjoint to derived restriction. -/
@[stacks 07AS "part (3), the adjunction `Lg_! ⊣ g⁻¹` on abelian sheaves for the flat-fppf site, \
with NO hypothesis: the acyclicity statement of Tag 07AC that \
`AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekAdjunction` carries as `hFP` is \
discharged by `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic`. Only part (3)"]
def derivedAbelianLowerShriekFunctorAdjunction :
    derivedAbelianLowerShriekFunctor B S hS 𝒳 ⊣ derivedAbelianRestriction B S hS 𝒳 :=
  derivedAbelianLowerShriekAdjunction B S hS 𝒳 (abelianLowerShriekAcyclic B S hS 𝒳)

/-- **Stacks 07AS (3), `g⁻¹ Lg_! = id`, for every algebraic stack.** Restriction after derived
lower shriek is canonically the identity of `D(𝒳_{flat,fppf})`. -/
@[stacks 07AS "part (3), `g⁻¹ ∘ Lg_! = id` on abelian sheaves for the flat-fppf site, with NO \
hypothesis: the acyclicity statement of Tag 07AC that \
`AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekRestrictionIso` carries as `hFP` is \
discharged by `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic`. Only part (3)"]
def derivedAbelianLowerShriekFunctorRestrictionIso :
    derivedAbelianLowerShriekFunctor B S hS 𝒳 ⋙ derivedAbelianRestriction B S hS 𝒳 ≅
      𝟭 (DerivedCategory (Sheaf (inclusionTopology B S hS 𝒳) AbCat.{u, u + 1})) :=
  derivedAbelianLowerShriekRestrictionIso B S hS 𝒳 (abelianLowerShriekAcyclic B S hS 𝒳)

end AlgebraicGeometry.Stack.FlatFppf

end
