module

public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.HomogeneousQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualBijective

/-!
# `Proj` of quotients by homogeneous ideals agreeing in large degrees

For homogeneous ideals `I ≤ J` of a graded ring `A`, the quotient map `A ⧸ I ⟶ A ⧸ J` is a graded
ring homomorphism. If `I` and `J` have the same homogeneous elements in every degree `d ≥ m`, it
is bijective in those degrees, and so ([Stacks, Tag 07ZE]) it induces an isomorphism
`Proj (A ⧸ J) ≅ Proj (A ⧸ I)`.

## Main definitions

* `Stacks.RingTheory.HomogeneousQuotient.quotientFactor`: the graded map `A ⧸ I ⟶ A ⧸ J`.

## Main results

* `Stacks.RingTheory.HomogeneousQuotient.bijective_gradedAddHom_quotientFactor`: it is bijective
  in every degree in which `J` has no homogeneous element outside `I`.
* `Stacks.RingTheory.HomogeneousQuotient.isIso_projMap_quotientFactor`: the induced morphism of
  projective spectra is an isomorphism when that holds in all large degrees.

## References

* [Stacks Project, Tag 07ZE](https://stacks.math.columbia.edu/tag/07ZE)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RingTheory.HomogeneousQuotient

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜] {I J : HomogeneousIdeal 𝒜}

/-- **The graded quotient map `A ⧸ I ⟶ A ⧸ J`** for homogeneous ideals `I ≤ J`. -/
def quotientFactor (h : I ≤ J) : quotientGrading 𝒜 I →+*ᵍ quotientGrading 𝒜 J where
  __ := Ideal.Quotient.factor (show I.toIdeal ≤ J.toIdeal from h)
  map_mem {i x} hx := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientGrading_iff 𝒜 I).1 hx
    exact quotientGrading_mk_mem 𝒜 J ha

/-- The graded quotient map `A ⧸ I ⟶ A ⧸ J` sends the class of `a` modulo `I` to its class
modulo `J`. -/
theorem quotientFactor_mk (h : I ≤ J) (a : A) :
    quotientFactor 𝒜 h (Ideal.Quotient.mk I.toIdeal a) = Ideal.Quotient.mk J.toIdeal a :=
  rfl

/-- **The graded quotient map is bijective in a degree in which `J` has no homogeneous element
outside `I`.** -/
theorem bijective_gradedAddHom_quotientFactor (h : I ≤ J) (d : ℕ)
    (hd : ∀ a ∈ 𝒜 d, a ∈ J.toIdeal → a ∈ I.toIdeal) :
    Function.Bijective (GradedRingHom.gradedAddHom (quotientFactor 𝒜 h) d) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, ha, hax⟩ := (mem_quotientGrading_iff 𝒜 I).1 x.2
    have h0 : Ideal.Quotient.mk J.toIdeal a = 0 := by
      rw [← quotientFactor_mk 𝒜 h, hax]
      exact congrArg Subtype.val hx
    exact Subtype.ext <| hax.symm.trans <|
      Ideal.Quotient.eq_zero_iff_mem.2 (hd a ha (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  · obtain ⟨a, ha, hay⟩ := (mem_quotientGrading_iff 𝒜 J).1 y.2
    exact ⟨⟨Ideal.Quotient.mk I.toIdeal a, quotientGrading_mk_mem 𝒜 I ha⟩, Subtype.ext hay⟩

/-- The irrelevant ideal of `A ⧸ J` is contained in the image of that of `A ⧸ I` under the graded
quotient map. -/
theorem irrelevant_le_map_quotientFactor (h : I ≤ J) :
    HomogeneousIdeal.irrelevant (quotientGrading 𝒜 J) ≤
      (HomogeneousIdeal.irrelevant (quotientGrading 𝒜 I)).map (quotientFactor 𝒜 h) := by
  refine (HomogeneousIdeal.irrelevant_le (quotientGrading 𝒜 J)).2 fun j hj x hx => ?_
  obtain ⟨a, ha, rfl⟩ := (mem_quotientGrading_iff 𝒜 J).1 hx
  show Ideal.Quotient.mk J.toIdeal a ∈
    ((HomogeneousIdeal.irrelevant (quotientGrading 𝒜 I)).map (quotientFactor 𝒜 h)).toAddSubmonoid
  rw [← quotientFactor_mk 𝒜 h a]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hj
    (quotientGrading_mk_mem 𝒜 I ha))

/-- If homogeneous ideals `I ≤ J` have the same homogeneous elements in every degree `d ≥ m`, the
graded quotient map induces an isomorphism `Proj (A ⧸ J) ≅ Proj (A ⧸ I)`. -/
theorem isIso_projMap_quotientFactor (h : I ≤ J) (m : ℕ)
    (hm : ∀ d, m ≤ d → ∀ a ∈ 𝒜 d, a ∈ J.toIdeal → a ∈ I.toIdeal) :
    IsIso (Proj.map (quotientFactor 𝒜 h) (irrelevant_le_map_quotientFactor 𝒜 h)) := by
  have hψ : ∀ᶠ d : ℕ in Filter.atTop,
      Function.Bijective (GradedRingHom.gradedAddHom (quotientFactor 𝒜 h) d) :=
    Filter.eventually_atTop.2 ⟨m, fun d hd => bijective_gradedAddHom_quotientFactor 𝒜 h d (hm d hd)⟩
  have hdom := Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_bijective
    _ _ _ hψ
  have := Stacks.AlgebraicGeometry.RelativeProjChain.isIso_mapHom_of_eventually_bijective _ _ _ hψ
  rw [← Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _ _
    (irrelevant_le_map_quotientFactor 𝒜 h) hdom,
    Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop]
  infer_instance

end Stacks.RingTheory.HomogeneousQuotient

end
