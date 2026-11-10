module

public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Statement

/-!
# When the canonical graded ring map of Tag 01MP is an isomorphism

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded commutative ring and `X = Proj(S)`.
[Stacks, Tag 01MP] builds the canonical homomorphism of graded rings

`Stacks.AlgebraicGeometry.ProjTwistSectionRing.sectionsRingHom : S →+* ⨁ₙ Γ(X, 𝒪(n))`,

assembled from the degreewise section maps `a ↦ a / 1`. It asserts nothing about injectivity or
surjectivity, and for a general graded ring the map is neither. This file shows that the map is
bijective — hence an isomorphism of graded rings — exactly when every degreewise section map is,
which is how the bijectivity is established in practice: degree by degree.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.degreeSectionEquiv`: the degree-`k` section map
  as an additive equivalence.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.sectionsRingEquiv`: **the canonical map of
  [Stacks, Tag 01MP] as an isomorphism of graded rings.**

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.bijective_sumSectionsRingHom`: the assembled map
  out of `⨁ₙ 𝒮 n` is bijective as soon as every degreewise section map is.
* `Stacks.AlgebraicGeometry.ProjTwistSectionRing.bijective_sectionsRingHom`: hence so is
  `sectionsRingHom`.

## Implementation notes

The underlying additive map of `sumSectionsRingHom` is `DirectSum.toAddMonoid` of the degreewise
family, and the map whose bijectivity is visible is `DFinsupp.mapRange.addEquiv` of the same
family read as equivalences. The two agree because they agree on each `DirectSum.of`, which is
`DirectSum.addHom_ext`; nothing about the ring structure enters, and the multiplicativity of the
isomorphism is inherited from `sectionsRingHom` rather than reproved.

Every statement whose type mentions the direct sum's ring structure opens with
`letI := gradedRing 𝒮`, as in
`StacksFrontier/AlgebraicGeometry/ProjTwistSectionRing/Statement.lean`: the graded ring structure is
a field of a structure there rather than an instance, so without the `letI` the direct sum has no
multiplication.

## What is not claimed

No `stacks` attribute is attached. [Stacks, Tag 01MP] is the construction of the graded ring map,
and is formalized at `Stacks.AlgebraicGeometry.ProjTwistSectionRing.globalSectionsRingMap`; that it
is an isomorphism is a property of particular graded rings and is not part of the tag.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.AlgebraicGeometry.ProjTwistSectionRing

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The degree-`k` section map as an additive equivalence, when it is bijective. -/
def degreeSectionEquiv (h : ∀ k : ℕ, Function.Bijective (degreeSection 𝒮 k)) (k : ℕ) :
    𝒮 k ≃+ twistGlobalSections 𝒮 k :=
  AddEquiv.ofBijective (degreeSectionHom 𝒮 k) (h k)

/-- **The assembled map out of `⨁ₙ 𝒮 n` is bijective as soon as every degreewise section map
is.** -/
theorem bijective_sumSectionsRingHom
    (h : ∀ k : ℕ, Function.Bijective (degreeSection 𝒮 k)) : letI := gradedRing 𝒮
    Function.Bijective (sumSectionsRingHom 𝒮) := by
  let := gradedRing 𝒮
  have key : (sumSectionsRingHom 𝒮).toAddMonoidHom
      = (DFinsupp.mapRange.addEquiv (degreeSectionEquiv 𝒮 h)).toAddMonoidHom := by
    refine DirectSum.addHom_ext fun i y => ?_
    change sumSectionsRingHom 𝒮 (DirectSum.of (fun j => 𝒮 j) i y)
        = (DFinsupp.mapRange.addEquiv (degreeSectionEquiv 𝒮 h))
            (DirectSum.of (fun j => 𝒮 j) i y)
    rw [sumSectionsRingHom_of, DFinsupp.mapRange.addEquiv_apply,
      show (DirectSum.of (fun j => 𝒮 j) i y) = DFinsupp.single i y from rfl,
      DFinsupp.mapRange_single]
    rfl
  have hfun : (sumSectionsRingHom 𝒮 : (⨁ n : ℕ, 𝒮 n) → _)
      = (DFinsupp.mapRange.addEquiv (degreeSectionEquiv 𝒮 h) : (⨁ n : ℕ, 𝒮 n) → _) :=
    congrArg (fun f : (⨁ n : ℕ, 𝒮 n) →+ (⨁ n : ℕ, twistGlobalSections 𝒮 n) => (f : _ → _)) key
  rw [hfun]
  exact (DFinsupp.mapRange.addEquiv (degreeSectionEquiv 𝒮 h)).bijective

/-- **The canonical ring map `S → ⨁ₙ Γ(Proj(S), 𝒪(n))` of [Stacks, Tag 01MP] is bijective as
soon as every degreewise section map is.** -/
theorem bijective_sectionsRingHom
    (h : ∀ k : ℕ, Function.Bijective (degreeSection 𝒮 k)) : letI := gradedRing 𝒮
    Function.Bijective (sectionsRingHom 𝒮) := by
  let := gradedRing 𝒮
  have hcomp : (sectionsRingHom 𝒮 : S → (⨁ n : ℕ, twistGlobalSections 𝒮 n))
      = (sumSectionsRingHom 𝒮) ∘ (DirectSum.decomposeRingEquiv 𝒮) := rfl
  rw [hcomp]
  exact (bijective_sumSectionsRingHom 𝒮 h).comp (DirectSum.decomposeRingEquiv 𝒮).bijective

/-- **The canonical map of [Stacks, Tag 01MP] as an isomorphism of graded rings**, when every
degreewise section map is bijective. -/
def sectionsRingEquiv (h : ∀ k : ℕ, Function.Bijective (degreeSection 𝒮 k)) :
    letI := gradedRing 𝒮
    S ≃+* (⨁ n : ℕ, twistGlobalSections 𝒮 n) :=
  letI := gradedRing 𝒮
  RingEquiv.ofBijective (sectionsRingHom 𝒮) (bijective_sectionsRingHom 𝒮 h)

/-- The isomorphism is the canonical map. -/
theorem coe_sectionsRingEquiv (h : ∀ k : ℕ, Function.Bijective (degreeSection 𝒮 k)) :
    letI := gradedRing 𝒮
    (sectionsRingEquiv 𝒮 h : S → (⨁ n : ℕ, twistGlobalSections 𝒮 n)) = sectionsRingHom 𝒮 := rfl

end Stacks.AlgebraicGeometry.ProjTwistSectionRing

end
