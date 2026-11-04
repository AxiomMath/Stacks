module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# Pointwise multiplication of global sections of the twists on Proj

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ`. A global section of the
`n`-th twist `𝒪(n)` on `Proj(S)` is a family of fractions, one in the localization of `S` at
each homogeneous prime, locally of the shape `a / b` with `b` homogeneous of some degree `p`
and `a` homogeneous of degree `p + n`. All these fractions live in one and the same ring,
whatever `n` is, so two such families can be multiplied pointwise; this file proves that the
result is again a section, of the twist `𝒪(n + m)`, and records the resulting multiplication
with its pointwise formula.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul`: the pointwise product of a global
  section of `𝒪(n)` and one of `𝒪(m)`, as a global section of `𝒪(n + m)`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.one`: the global section of `𝒪(0)` attached
  to the homogeneous element `1`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mem_twistGrading_natCast`: a reading of
  membership in the shifted grading in terms of the original one, with both degrees natural
  numbers.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_mem_moduleSections`: the pointwise
  product of two twist sections is a twist section.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_apply`,
  `Stacks.AlgebraicGeometry.ProjTwistSectionRing.one_apply`: the pointwise formulas.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection`: the product of the
  sections attached to two homogeneous elements is the section attached to their product.

## Implementation notes

The fibre of the sheaf associated to a graded module at a homogeneous prime is the full
localization of the module, with no reference to the grading, so for the twists of the regular
module every fibre is the localized *ring* `S_(p)` and the grading enters only through the
local-fraction condition on sections. That is what makes a pointwise product available at all:
nothing has to be transported between fibres, and the multiplication map is the restriction of
the pointwise product of dependent families to the submodule of sections.

Membership in the shifted grading is the only computation. `twistGrading 𝒮 n p` is
`integerGrading 𝒮 (p + n)`, so when both `p` and `n` are natural numbers the two casts
collapse and membership is membership in `𝒮 (p + n)`; `mem_twistGrading_natCast` says this
once, and every degree bookkeeping below is an application of it together with a
rearrangement of natural-number sums. The sum of the two local denominators' degrees and the
sum of the two twists are added in the opposite order by `SetLike.mul_mem_graded`, which is
why the rearrangement is needed at all.

Sections are compared and constructed through
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafSectionsEquiv`, the identity
identification of the sections of the constructed sheaf with the displayed submodule of
locally-homogeneous families. Going through it rather than through the anonymous constructor
keeps the elaborator from having to unfold the sheaf-of-modules wrappers to reach a subtype.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.AlgebraicGeometry.ProjTwistSectionRing

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-! ### Membership in the shifted grading -/

omit [GradedRing 𝒮] in
/-- An element lies in the degree-`p` piece of the `n`-th shift of the regular graded module
exactly when it is homogeneous of degree `p + n`, for natural numbers `p` and `n`. -/
public theorem mem_twistGrading_natCast (n p : ℕ) (a : S) :
    a ∈ twistGrading (S := S) 𝒮 (n : ℤ) (p : ℤ) ↔ a ∈ 𝒮 (p + n) := by
  rw [twistGrading_apply, ← Nat.cast_add, integerGrading_natCast, mem_homogeneousSubmodule]

/-! ### The pointwise product -/

/-- Alias of `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSections_mul_mem`. -/
public alias mul_mem_moduleSections :=
  AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSections_mul_mem

/-- The pointwise product of a global section of `𝒪(n)` and a global section of `𝒪(m)`, as a
global section of `𝒪(n + m)`. -/
public def mul (n m : ℕ) (s : twistGlobalSections 𝒮 n) (t : twistGlobalSections 𝒮 m) :
    twistGlobalSections 𝒮 (n + m) :=
  (associatedModuleSheafSectionsEquiv 𝒮
      (twistGrading (S := S) 𝒮 ((n + m : ℕ) : ℤ)) ⊤).symm
    ⟨fun x => (associatedModuleSheafSectionsEquiv 𝒮
          (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤ s).1 x *
        (associatedModuleSheafSectionsEquiv 𝒮
          (twistGrading (S := S) 𝒮 (m : ℤ)) ⊤ t).1 x,
      mul_mem_moduleSections 𝒮 n m _ _⟩

/-- The value of `mul 𝒮 n m s t` at a point is the product of the values of `s` and `t`. -/
@[simp] public theorem mul_apply (n m : ℕ) (s : twistGlobalSections 𝒮 n)
    (t : twistGlobalSections 𝒮 m) (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (mul 𝒮 n m s t).1 x = s.1 x * t.1 x := rfl

/-- Two global sections of `𝒪(n)` with the same value at every point are equal. -/
public theorem section_ext {n : ℕ} {s t : twistGlobalSections 𝒮 n}
    (h : ∀ x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)), s.1 x = t.1 x) : s = t :=
  (associatedModuleSheafSectionsEquiv 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).injective
    (Subtype.ext (funext h))

/-! ### The unit section -/

/-- The global section of `𝒪(0)` attached to the homogeneous element `1` of degree `0`. -/
public def one : twistGlobalSections 𝒮 0 :=
  degreeSection 𝒮 0 ⟨1, SetLike.one_mem_graded 𝒮⟩

/-- The section `one 𝒮` takes the value `1` at every point. -/
@[simp] public theorem one_apply (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (one 𝒮).1 x = 1 := by
  rw [one, degreeSection_apply]
  exact (OreLocalization.one_def ..).symm

/-! ### Interaction with the homogeneous sections -/

/-- The product of the global sections attached to two homogeneous elements is the global
section attached to their product. -/
public theorem mul_degreeSection (n m : ℕ) (a : 𝒮 n) (b : 𝒮 m) :
    mul 𝒮 n m (degreeSection 𝒮 n a) (degreeSection 𝒮 m b) =
      degreeSection 𝒮 (n + m) ⟨(a : S) * (b : S), SetLike.mul_mem_graded a.2 b.2⟩ := by
  refine section_ext 𝒮 fun x => ?_
  rw [mul_apply, degreeSection_apply, degreeSection_apply, degreeSection_apply]
  have hden : LocalizedModule.mk ((a : S) * (b : S))
      ((1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) * 1) =
      LocalizedModule.mk ((a : S) * (b : S))
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    congrArg (LocalizedModule.mk ((a : S) * (b : S))) (mul_one 1)
  exact Eq.trans LocalizedModule.mk_mul_mk hden

end Stacks.AlgebraicGeometry.ProjTwistSectionRing

end
