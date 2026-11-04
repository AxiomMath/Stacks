module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison

/-!
# The twist comparison is compatible with multiplication

The twisting sheaves of `Proj 𝒜` multiply: a degree-`p` fraction family and a degree-`q` fraction
family over an open `U` of `Proj 𝒜` have a pointwise product, and it is a degree-`p + q` fraction
family. This file constructs that product and proves that the comparison
`Stacks.ProjTwistComparison.sectionsMap` of
`StacksFrontier/AlgebraicGeometry/RelativeProj/Twist/Comparison.lean` carries it to the
corresponding product on `Proj ℬ`.

The fibres of the twisting sheaves are the full localizations
`AlgebraicGeometry.ProjectiveSpectrum.Proj.ModuleFiber`, which do not depend on the twist index:
the index only enters the local-fraction predicate on *sections*. So the product of two sections
is the pointwise product in the fibres, and the only thing to check is that a product of local
fractions of degrees `p` and `q` is a local fraction of degree `p + q`, which is the
multiplicativity of the integer-extended grading.

Compatibility is then immediate: the fibre comparison
`Stacks.ProjTwistComparison.fibreMap` is `Localization.localRingHom`, a ring homomorphism, so it
is multiplicative, and the comparison on sections applies it at each point.

## Main definitions

* `Stacks.ProjTwistMultiplication.twistSectionsMul`: the product
  `𝒪(p)(U) × 𝒪(q)(U) → 𝒪(p + q)(U)` of twisted fraction families over an arbitrary open and for
  arbitrary integer twists.

## Main results

* `Stacks.ProjTwistMultiplication.mul_mem_integerGrading`: the integer-extended grading is
  multiplicative.
* `Stacks.ProjTwistComparison.sectionsMap_twistSectionsMul`: **the twist comparison is a
  homomorphism for the multiplication of twisted sections.**

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistMultiplication

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The integer-extended grading is multiplicative.** In a negative degree the piece is the
zero submodule, so the only case with content is the one where both degrees are non-negative,
where this is `SetLike.mul_mem_graded`. -/
theorem mul_mem_integerGrading {i j : ℤ} {x y : S}
    (hx : x ∈ integerGrading (S := S) 𝒜 i) (hy : y ∈ integerGrading (S := S) 𝒜 j) :
    x * y ∈ integerGrading (S := S) 𝒜 (i + j) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [integerGrading_neg _ _ hi, Submodule.mem_bot] at hx
    rw [hx, zero_mul]
    exact zero_mem _
  rcases lt_or_ge j 0 with hj | hj
  · rw [integerGrading_neg _ _ hj, Submodule.mem_bot] at hy
    rw [hy, mul_zero]
    exact zero_mem _
  lift i to ℕ using hi
  lift j to ℕ using hj
  rw [integerGrading_natCast, mem_homogeneousSubmodule] at hx hy
  rw [← Nat.cast_add, integerGrading_natCast, mem_homogeneousSubmodule]
  exact SetLike.mul_mem_graded hx hy

/-- **The product of two twisted fraction representatives is a twisted fraction
representative**, of the sum of the degrees. -/
theorem isModuleFraction_mul {p q : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {a b : ∀ x : U, ModuleFiber (M := S) 𝒜 x.1}
    (ha : IsModuleFraction 𝒜 (twistGrading (S := S) 𝒜 p) a)
    (hb : IsModuleFraction 𝒜 (twistGrading (S := S) 𝒜 q) b) :
    IsModuleFraction 𝒜 (twistGrading (S := S) 𝒜 (p + q)) (fun x => a x * b x) := by
  obtain ⟨n₁, m₁, s₁, hm₁, hs₁, hns₁, ha⟩ := ha
  obtain ⟨n₂, m₂, s₂, hm₂, hs₂, hns₂, hb⟩ := hb
  refine ⟨n₁ + n₂, m₁ * m₂, s₁ * s₂, ?_, SetLike.mul_mem_graded hs₁ hs₂,
    fun x => x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hns₁ x) (hns₂ x), fun x => ?_⟩
  · have hmul := mul_mem_integerGrading 𝒜 hm₁ hm₂
    have harg : (n₁ : ℤ) + p + ((n₂ : ℤ) + q) = ((n₁ + n₂ : ℕ) : ℤ) + (p + q) := by
      push_cast
      ring
    rw [harg] at hmul
    exact hmul
  · exact (congrArg₂ (· * ·) (ha x) (hb x)).trans (LocalizedModule.mk_mul_mk ..)

/-- **The pointwise product of two twisted sections is a twisted section**, of the sum of the
degrees. The local-fraction predicate is checked near each point, and near a point both factors
have fraction representatives. -/
theorem mul_mem_moduleSections {p q : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (a : moduleSections 𝒜 (twistGrading (S := S) 𝒜 p) U)
    (b : moduleSections 𝒜 (twistGrading (S := S) 𝒜 q) U) :
    (fun x => a.1 x * b.1 x) ∈ moduleSections 𝒜 (twistGrading (S := S) 𝒜 (p + q)) U := by
  intro x
  obtain ⟨V, hxV, iV, hfracV⟩ := a.2 x
  obtain ⟨W, hxW, iW, hfracW⟩ := b.2 x
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩, Opens.infLELeft _ _ ≫ iV, ?_⟩
  have hV := (moduleFractionPrelocal 𝒜 (twistGrading (S := S) 𝒜 p)).res
    (Opens.infLELeft V W) _ hfracV
  have hW := (moduleFractionPrelocal 𝒜 (twistGrading (S := S) 𝒜 q)).res
    (Opens.infLERight V W) _ hfracW
  exact isModuleFraction_mul 𝒜 hV hW

/-- **The product of twisted sections** `𝒪(p)(U) × 𝒪(q)(U) → 𝒪(p + q)(U)`, computed pointwise in
the module fibres. -/
def twistSectionsMul (p q : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : moduleSections 𝒜 (twistGrading (S := S) 𝒜 p) U)
    (b : moduleSections 𝒜 (twistGrading (S := S) 𝒜 q) U) :
    moduleSections 𝒜 (twistGrading (S := S) 𝒜 (p + q)) U :=
  ⟨fun x => a.1 x * b.1 x, mul_mem_moduleSections 𝒜 a b⟩

/-- The value of the product of twisted sections at a point `x` is the product of their values
at `x`. -/
@[simp] theorem twistSectionsMul_apply (p q : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : moduleSections 𝒜 (twistGrading (S := S) 𝒜 p) U)
    (b : moduleSections 𝒜 (twistGrading (S := S) 𝒜 q) U) (x : U) :
    (twistSectionsMul 𝒜 p q U a b).1 x = a.1 x * b.1 x := rfl

end Stacks.ProjTwistMultiplication

namespace Stacks.ProjTwistComparison

open Stacks.ProjTwistMultiplication

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)

/-- The fibre comparison is multiplicative: it is `Localization.localRingHom`, a ring
homomorphism, and the module fibres of the twisting sheaves are the localizations of the ring
itself. -/
theorem fibreMap_mul (y : ProjectiveSpectrum ℬ)
    (z w : ModuleFiber (M := A) 𝒜 (ProjectiveSpectrum.comapFun φ hφ y)) :
    fibreMap φ hφ y (z * w) = fibreMap φ hφ y z * fibreMap φ hφ y w :=
  map_mul (Localization.localRingHom _ _ φ.toRingHom rfl) z w

/-- **The twist comparison is compatible with the multiplication of twisted sections.** The
comparison of a product of a degree-`p` and a degree-`q` section is the product of the
comparisons; this is the multiplicativity of the comparison of local rings, applied at each
point. -/
@[stacks 01NO "the compatibility of the twist comparison with the multiplication of twisted \
sections, i.e. with the pointwise product of fraction families; the compatibility with the \
sheaf-level multiplication maps 𝒪(p) ⊗ 𝒪(q) ⟶ 𝒪(p + q) is not covered"]
theorem sectionsMap_twistSectionsMul (p q : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : moduleSections 𝒜 (twistGrading (S := A) 𝒜 p) U)
    (b : moduleSections 𝒜 (twistGrading (S := A) 𝒜 q) U) :
    sectionsMap φ hφ (p + q) U (twistSectionsMul 𝒜 p q U a b) =
      twistSectionsMul ℬ p q (U.comap (ProjectiveSpectrum.comap φ hφ))
        (sectionsMap φ hφ p U a) (sectionsMap φ hφ q U b) :=
  Subtype.ext (funext fun y => fibreMap_mul φ hφ y.1 _ _)

end Stacks.ProjTwistComparison

end
