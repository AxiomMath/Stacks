module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.RelativeProjQuasiCompact
public import StacksFrontier.AlgebraicGeometry.RelativeProj.LocalAtBase

/-!
# Universal closedness of the relative homogeneous spectrum

Let `S` be a scheme carrying a quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra
`𝒜`. If `𝒪_S → 𝒜_0` is integral and `𝒜` is of finite type over `𝒜_0`, then the structure
morphism of `Proj_S(𝒜)` is universally closed.

Over an affine open `U` of the base the chart structure morphism factors as
`Proj (𝒜(U)) ⟶ Spec (𝒜_0(U)) ⟶ U`. The first leg is universally closed because `𝒜(U)` is a
finite type algebra over its degree-zero part, the second because `Γ(S, U) → 𝒜_0(U)` is
integral. Universal closedness is stable under composition and Zariski-local at the target, so
it passes from the charts to the structure morphism.

## Main definitions

* `Stacks.RelativeProj.Situation.IsIntegralInDegreeZero` — over every affine open of the base
  the degree-zero piece of the graded ring of sections is integral over the sections of the
  structure sheaf.

## Main results

* `Stacks.RelativeProj.Situation.universallyClosed_relativeProjToBase_of_isIntegralInDegreeZero`
  — **Stacks 07ZZ**: the structure morphism of the relative homogeneous spectrum is universally
  closed.

## Implementation notes

`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/SectionRings.lean` carries an untagged
`universallyClosed_relativeProjToBase` in this same namespace which assumes `sectionRingZeroMap`
is an isomorphism.  That is a special case: an isomorphism of rings is in particular integral, so
the hypothesis here — the degree-zero map is integral, which is what Stacks 07ZZ asks — is
strictly weaker, and the name is qualified by it to keep the two apart.

Both hypotheses are read over every affine open of the base, as the sibling predicate
`Stacks.RelativeProj.Situation.IsFiniteTypeOverDegreeZero` of Stacks 07ZX already is. That is
the affine-local reading the source's own proof uses — it begins by reducing to an affine base —
and it is the shape the chart transfer `Stacks.RelativeProj.Data.prop_toBase_of_comp` consumes.

The source quotes the existence part of the valuative criterion for
`Proj (𝒜(U)) ⟶ Spec (𝒜_0(U))`. Here that leg is Mathlib's `AlgebraicGeometry.Proj.toSpecZero`,
which is proper, hence universally closed, under exactly the finite type hypothesis. The other
leg is universally closed because an integral morphism of schemes is, which is Stacks 01WM.

## References

* [Stacks Project, Tag 07ZZ](https://stacks.math.columbia.edu/tag/07ZZ)
* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
* [Stacks Project, Tag 07ZX](https://stacks.math.columbia.edu/tag/07ZX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- The degree-zero part of the graded algebra of a relative `Proj` situation is integral over
the structure sheaf: over every affine open `U` of the base, the degree-zero piece of the graded
ring of sections is integral over `Γ(S, U)` along
`Stacks.RelativeProj.Situation.sectionRingZeroMap`. This is the first hypothesis of
Stacks 07ZZ. -/
def IsIntegralInDegreeZero : Prop :=
  ∀ U : s.base.Opens, IsAffineOpen U → (s.sectionRingZeroMap U).hom.IsIntegral

/-- **Stacks 07ZZ.** If the degree-zero part of the graded algebra of a relative `Proj`
situation is integral over the structure sheaf and the graded algebra is of finite type over its
degree-zero part, then the structure morphism of the relative homogeneous spectrum is
universally closed. -/
@[stacks 07ZZ]
theorem universallyClosed_relativeProjToBase_of_isIntegralInDegreeZero
    (hint : s.IsIntegralInDegreeZero)
    (hft : s.IsFiniteTypeOverDegreeZero) :
    UniversallyClosed (relativeProjToBase s) := by
  refine (chartData s).prop_toBase_of_comp @UniversallyClosed ?_ ?_
  · intro W
    have := hft W.1 W.2
    infer_instance
  · intro W
    have : IsIntegralHom (Spec.map ((chartData s).base W)) :=
      IsIntegralHom.SpecMap_iff.mpr (hint W.1 W.2)
    infer_instance

end Stacks.RelativeProj.Situation

end
