module

public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.GradedRing

/-!
# The canonical graded ring map `S → ⨁ₙ Γ(Proj(S), 𝒪(n))`, Tag 01MP

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ`. Tag 01MP asserts that
the degreewise maps sending a homogeneous element of degree `n` to a global section of the
`n`-th twist assemble into a homomorphism of graded rings from `S` into the direct sum of the
twisted global-section groups, with the homogeneous multiplication characterized pointwise in
the localized ring at each point of `Proj(S)`. This file states and proves that assertion.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.GlobalSectionsRingMap`: the graded section
  ring, its canonical ring map, and their two characterizing formulas.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.degreeSectionSummandHom` and
  `sumSectionsRingHom`: the degreewise section maps and their assembly into a ring map out of
  `⨁ n, 𝒮 n`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.sectionsRingHom`: the ring map itself,
  `S →+* ⨁ n, Γ(Proj(S), 𝒪(n))`.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.globalSectionsRingMap`: **Tag 01MP.** The
  construction supplying all of it.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.degreeSection_eq_degreeZeroToGlobalSections`:
  the degree-`n` section map is the degree-zero global-section map of Tag 01M7 applied to the
  `n`-th shift of the regular graded module, with the membership read off by `simp`. This is
  the equation that identifies the section map with the one Tag 01MP's statement names.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.sectionsRingHom_apply_homogeneous`: on a
  homogeneous element of degree `n` the ring map is the degree-`n` section map, landed in the
  degree-`n` summand.

## The construction

`S` is the direct sum of its homogeneous pieces, so a ring map out of it is a map out of
`⨁ n, 𝒮 n`, and `DirectSum.toSemiring` builds one from a degreewise family of additive maps
that carries the graded unit to the unit and the graded product to the product. The family is
the degree-`n` section map
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSectionHom` followed by the inclusion of the
degree-`n` summand. The unit condition holds by `rfl`, because
the unit section *is* the section attached to the homogeneous element `1`; the product
condition is one `congrArg` on
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection`, read through
`DirectSum.of_mul_of`. So no computation is left inside the ring map.

The pointwise multiplication formula that Tag 01MP also asserts is, for this graded ring,
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_apply`: the product was *defined*
pointwise, so the formula holds by `rfl` and the content of the assertion sits in the proof
that the pointwise product is a section at all
(`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_mem_moduleSections`).

## Implementation notes

The graded ring structure is a field of `GlobalSectionsRingMap` rather than an instance, so
every later field opens with a `letI` that brings it into scope — without it the direct sum
has no multiplication and `hom` cannot be elaborated. The same `letI` opens the statement of
every declaration below whose type mentions the direct sum's ring structure. It has to be
`letI` and not `let` there: `letI` inlines the value, so the statement is literally the
universally quantified equation and a proof can `intro` straight into it, whereas `let` leaves
a binder that `intro` consumes first.

The two unit and product conditions are named (`degreeSectionSummandHom_gradedOne` and
`degreeSectionSummandHom_gradedMul`). Passing them to `DirectSum.toSemiring` as anonymous goals
costs nothing, but a later lemma about the resulting ring map cannot then be stated without
them: `DirectSum.toSemiring_of` takes the two proofs as arguments, so quoting it leaves them as
metavariables, and solving those metavariables forces the elaborator to whnf the assembled ring
map — which does not terminate inside the default heartbeat budget. For the same reason
`sumSectionsRingHom_of` is proved from `DirectSum.toAddMonoid_of`, which has no proof
arguments at all: the ring map's underlying function *is* `DirectSum.toAddMonoid` of the
family, so the summand formula is an additive fact and needs neither condition.

The graded-monoid unit and product of the *source* `fun i => 𝒮 i` are written with all their
arguments explicit. Left implicit, `GradedMonoid.GOne.one` and `GradedMonoid.GMul.mul` are
elaborated at a different family — the product was inferred at the pointwise-sum predicate
`(· ∈ 𝒮 n) + (· ∈ 𝒮 m)` — and the statement then says nothing about `S`.

`sectionsRingHom` and its formula on homogeneous elements are proved before the structure is
assembled, so `globalSectionsRingMap` costs nothing beyond naming its four fields.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
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

/-! ### The degree-`n` section map, in the spelling Tag 01MP uses -/

/-- The degree-`n` section map is the degree-zero global-section map of Tag 01M7 applied to the
`n`-th shift of the regular graded module, whose degree-zero piece is `𝒮 n`. -/
public theorem degreeSection_eq_degreeZeroToGlobalSections (n : ℕ) (a : 𝒮 n) :
    degreeSection 𝒮 n a =
      degreeZeroToGlobalSections 𝒮 (twistGrading (S := S) 𝒮 (n : ℤ))
        ⟨a.1, by
          simp [twistGrading, integerGrading, homogeneousSubmodule]⟩ :=
  rfl

/-! ### The graded ring of twisted global sections and its canonical map -/

/-- The graded section ring, its canonical ring map, and their characterizing formulas. The
product is the pointwise product of local fractions. -/
public structure GlobalSectionsRingMap where
  /-- The graded commutative ring structure on the twisted global sections. -/
  gradedRing : DirectSum.GCommRing (twistGlobalSections 𝒮)
  /-- The canonical ring map from `S` to the direct sum of the twisted global sections. -/
  hom : letI := gradedRing
    S →+* (⨁ n : ℕ, twistGlobalSections 𝒮 n)
  /-- In every degree the map is the degree-`n` section map of Tag 0AG2. -/
  map_homogeneous : letI := gradedRing
    ∀ (n : ℕ) (a : 𝒮 n), hom a.1 =
      DirectSum.of (twistGlobalSections 𝒮) n (degreeSection 𝒮 n a)
  /-- The homogeneous product is the pointwise product of local fractions. -/
  mul_sections : letI := gradedRing
    ∀ (n m : ℕ) (s : twistGlobalSections 𝒮 n)
      (t : twistGlobalSections 𝒮 m)
      (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))),
      ((associatedModuleSheafSectionsEquiv 𝒮
        (twistGrading (S := S) 𝒮 ((n + m : ℕ) : ℤ)) ⊤).toFun
          (GradedMonoid.GMul.mul s t)).1 x =
        ((associatedModuleSheafSectionsEquiv 𝒮
          (twistGrading (S := S) 𝒮 (n : ℤ)) ⊤).toFun s).1 x *
        ((associatedModuleSheafSectionsEquiv 𝒮
          (twistGrading (S := S) 𝒮 (m : ℤ)) ⊤).toFun t).1 x

/-- The degreewise family out of which the ring map is assembled: the degree-`n` section map
followed by the inclusion of the degree-`n` summand. -/
public def degreeSectionSummandHom (n : ℕ) :
    𝒮 n →+ (⨁ k : ℕ, twistGlobalSections 𝒮 k) :=
  (DirectSum.of (twistGlobalSections 𝒮) n).comp (degreeSectionHom 𝒮 n)

/-- The degreewise family carries the homogeneous element `1` to the unit of the direct sum. -/
public theorem degreeSectionSummandHom_gradedOne : letI := gradedRing 𝒮
    degreeSectionSummandHom 𝒮 0
        (@GradedMonoid.GOne.one ℕ (fun i : ℕ => (𝒮 i : Type u)) _ _) = 1 :=
  rfl

/-- The degreewise family carries the product of two homogeneous elements to the product of
their images. -/
public theorem degreeSectionSummandHom_gradedMul : letI := gradedRing 𝒮
    ∀ {n m : ℕ} (a : 𝒮 n) (b : 𝒮 m),
      degreeSectionSummandHom 𝒮 (n + m)
          (@GradedMonoid.GMul.mul ℕ (fun i : ℕ => (𝒮 i : Type u)) _ _ n m a b) =
        degreeSectionSummandHom 𝒮 n a * degreeSectionSummandHom 𝒮 m b := by
  let _inst := gradedRing 𝒮
  intro n m a b
  refine Eq.trans ?_ (DirectSum.of_mul_of
    (degreeSection 𝒮 n a) (degreeSection 𝒮 m b)).symm
  exact congrArg (DirectSum.of (twistGlobalSections 𝒮) (n + m))
    (mul_degreeSection 𝒮 n m a b).symm

/-- The degreewise section maps, assembled into a ring map out of the direct sum of the
homogeneous pieces of `S`. -/
public def sumSectionsRingHom : letI := gradedRing 𝒮
    (⨁ n : ℕ, 𝒮 n) →+* (⨁ n : ℕ, twistGlobalSections 𝒮 n) := by
  letI := gradedRing 𝒮
  refine DirectSum.toSemiring (degreeSectionSummandHom 𝒮) ?_ ?_
  · exact degreeSectionSummandHom_gradedOne 𝒮
  · exact degreeSectionSummandHom_gradedMul 𝒮

/-- On the degree-`n` summand the assembled ring map is the degree-`n` section map. -/
public theorem sumSectionsRingHom_of : letI := gradedRing 𝒮
    ∀ (n : ℕ) (a : 𝒮 n), sumSectionsRingHom 𝒮 (DirectSum.of (fun i => 𝒮 i) n a) =
      DirectSum.of (twistGlobalSections 𝒮) n (degreeSection 𝒮 n a) :=
  fun n a => DirectSum.toAddMonoid_of (degreeSectionSummandHom 𝒮) n a

/-- The canonical ring map `S → ⨁ n ≥ 0, Γ(Proj(S), 𝒪(n))`: decompose a ring element into its
homogeneous pieces and take the global section attached to each. -/
public def sectionsRingHom : letI := gradedRing 𝒮
    S →+* (⨁ n : ℕ, twistGlobalSections 𝒮 n) := by
  letI := gradedRing 𝒮
  exact (sumSectionsRingHom 𝒮).comp (DirectSum.decomposeRingEquiv 𝒮).toRingHom

/-- On a homogeneous element of degree `n` the canonical ring map is the degree-`n` section
map, landed in the degree-`n` summand. -/
public theorem sectionsRingHom_apply_homogeneous : letI := gradedRing 𝒮
    ∀ (n : ℕ) (a : 𝒮 n), sectionsRingHom 𝒮 a.1 =
      DirectSum.of (twistGlobalSections 𝒮) n (degreeSection 𝒮 n a) := by
  intro n a
  have hcomp : sectionsRingHom 𝒮 a.1 =
      sumSectionsRingHom 𝒮 (DirectSum.decompose 𝒮 a.1) := rfl
  have hdec : DirectSum.decompose 𝒮 a.1 = DirectSum.of (fun i => 𝒮 i) n a :=
    DirectSum.decompose_of_mem 𝒮 a.2
  rw [hcomp, hdec, sumSectionsRingHom_of]

/-- The canonical graded ring map
`S → ⨁ n ≥ 0, Γ(Proj(S), 𝒪(n))`. -/
@[stacks 01MP]
public def globalSectionsRingMap : GlobalSectionsRingMap 𝒮 where
  gradedRing := gradedRing 𝒮
  hom := sectionsRingHom 𝒮
  map_homogeneous := sectionsRingHom_apply_homogeneous 𝒮
  mul_sections := fun n m s t x => mul_apply 𝒮 n m s t x

end Stacks.AlgebraicGeometry.ProjTwistSectionRing

end
