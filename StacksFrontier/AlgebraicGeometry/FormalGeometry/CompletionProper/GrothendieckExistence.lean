module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Grothendieck's existence theorem with proper support, over a proper base

**Stacks 088E** states that for a Noetherian ring `A` complete with respect to an ideal `I` and a
separated scheme `X` of finite type over `A`, completion along `𝓘 = I · 𝒪_X` is an equivalence

  `Coh_{support proper over A}(𝒪_X) ⥤ Coh_{support proper over A}(X, 𝓘)`.

This file records that when the structure morphism `f : X ⟶ Spec A` is itself **proper** both
support conditions are vacuous: every closed subset of `X` is proper over `A`, because a closed
immersion followed by a proper morphism is proper. Stacks 088E itself, at the source's hypotheses, is
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver_holds`.

## Main results

* `Stacks.Algebraization.hasProperSupport_of_isProper` — over a proper base every finite type
  sheaf of modules has support proper over the base.
* `Stacks.Algebraization.hasProperSupport_coherentAdicSystem_of_isProper` — the same for the first
  term of a coherent adic system.

## Implementation notes

Properness of the support is expressed, as in `CompletionProper/Basic.lean`, through the canonical
reduced closed subscheme of the vanishing ideal sheaf of the support; `IsProper.comp_iff` then
discharges it, since the immersion of that subscheme is a closed immersion and hence proper.

## References

* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088D](https://stacks.math.columbia.edu/tag/088D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-- **Over a proper base all supports are proper.** If `f : X ⟶ S` is proper then the support of a
finite type sheaf of modules on `X`, a closed subset of `X`, is proper over `S`: its reduced
closed subscheme structure is immersed in `X` by a closed immersion, and a closed immersion
followed by a proper morphism is proper. -/
public theorem hasProperSupport_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (M : X.Modules) [M.IsFiniteType] : HasProperSupport f M := by
  refine ⟨⟨_root_.SheafOfModules.supp M, _root_.SheafOfModules.isClosed_supp M⟩, rfl, ?_⟩
  show IsProper ((Scheme.IdealSheafData.vanishingIdeal
    (⟨_root_.SheafOfModules.supp M, _root_.SheafOfModules.isClosed_supp M⟩ :
      Closeds X)).subschemeι ≫ f)
  exact (IsProper.comp_iff (g := f)).2 inferInstance

/-- **Over a proper base the first term of a coherent adic system has proper support.** Its terms
are coherent, hence of finite type, so `hasProperSupport_of_isProper` applies. -/
public theorem hasProperSupport_coherentAdicSystem_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (J : X.IdealSheafData) (M : Stacks.Coherent.CoherentAdicSystems J) :
    HasProperSupport f (M.obj.obj (op 0)) :=
  have hcoh : (M.obj.obj (op 0)).IsCoherent := M.property.1 0
  have : (M.obj.obj (op 0)).IsFiniteType := hcoh.isFiniteType
  hasProperSupport_of_isProper f (M.obj.obj (op 0))

end Stacks.Algebraization

end
