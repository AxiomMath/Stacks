module

public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic
public import StacksFrontier.LinearAlgebra.SymmetricPower.DegreeOneGeneration
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of the first twist on the projective bundle of a module

Let `A` be a commutative ring and `M` an `A`-module. The projective bundle of `M̃` over
`Spec A` is `𝐏(M̃) = Proj(Sym_A(M))`, and the canonical map
`Sym¹(M̃) → π_* 𝒪_{𝐏(M̃)}(1)` of Stacks 01OB reads on global sections as a map

`M = Sym¹_A(M) → Γ(Proj(Sym_A(M)), 𝒪(1))`.

This file constructs that map and gives the criterion for an element to die under it: it is
enough that the element be killed by every degree-one element of the symmetric algebra. The
criterion is sharp enough to witness non-injectivity, which is what Stacks 01OC does.

## Main definitions

* `SymmetricAlgebra.grading`: the grading of `Sym_A(M)` by symmetric powers, whose `Proj` is the
  projective bundle of `M̃`.
* `SymmetricAlgebra.toGradingOne`: `M` as the degree-one part of `Sym_A(M)`.
* `SymmetricAlgebra.toTwistSections`: **the canonical map `M → Γ(Proj(Sym_A(M)), 𝒪(1))`.**

## Main results

* `SymmetricAlgebra.toTwistSections_eq_zero_of_forall_mul_eq_zero`: an element of `M` whose
  product with every degree-one generator vanishes has vanishing section on the first twist.
* `SymmetricAlgebra.not_injective_toTwistSections`: consequently such an element, if nonzero,
  witnesses that `M → Γ(Proj(Sym_A(M)), 𝒪(1))` is **not injective**.
* `SymmetricAlgebra.iSup_basicOpen_toGradingOne_eq_top`: the standard opens of the degree-one
  elements cover `Proj(Sym_A(M))`; `SymmetricAlgebra.iSup_basicOpen_eq_top_of_span` gives the
  same for the image of any spanning set of `M`, which is how a finite affine covering of the
  projective bundle is produced.

## Implementation notes

The vanishing criterion is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_of_annihilating_degree`, which
asks for a whole homogeneous component annihilating the element and for the graded ring to be
generated in degree one over its degree-zero part. Here the component is the degree-one one and
the generation hypothesis is
`SymmetricAlgebra.adjoin_symmetricPower_one_eq_top`, so neither has to be assumed.

Everything is stated for an abstract `A` with `[CommRing A]`. That matters at the point of use:
when `A` is a quotient ring, elaborating `SymPow.symmetricPower n A _` against an ascription
`Submodule A _` picks the quotient's own `Semiring` instance on one side and `Ring.toSemiring` on
the other, and the `AddSubgroupClass (Submodule A _) _` that the `Proj` API needs is then not
found. Instantiating a statement proved for abstract `A` derives every instance from the single
`CommRing` instance found at the application site and so does not meet that diamond.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace SymmetricAlgebra

variable (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]

/-- The grading of `Sym_A(M)` by its symmetric powers. `Proj` of this graded ring is the
projective bundle `𝐏(M̃)` of `M̃` over `Spec A`. -/
@[ega "II 1.7.1"]
public abbrev grading (n : ℕ) : Submodule A (SymmetricAlgebra A M) :=
  SymPow.symmetricPower n A M

/-- `Sym_A(M)` is generated in degree one, the hypothesis the `Proj` API asks for. -/
public theorem adjoin_grading_one_eq_top :
    Algebra.adjoin (grading A M 0) (grading A M 1 : Set (SymmetricAlgebra A M)) = ⊤ :=
  adjoin_symmetricPower_one_eq_top A M

/-- `M` as the degree-one part `Sym¹_A(M)` of the symmetric algebra. -/
public def toGradingOne : M →ₗ[A] grading A M 1 :=
  (ι A M).codRestrict _ fun m =>
    show ι A M m ∈ SymPow.symmetricPower 1 A M by
      rw [SymPow.symmetricPower, pow_one]
      exact LinearMap.mem_range_self _ m

/-- `toGradingOne` is `ι` followed by the inclusion of the degree-one part. -/
@[simp] public theorem coe_toGradingOne (m : M) :
    (toGradingOne A M m : SymmetricAlgebra A M) = ι A M m := rfl

/-- The degree-one part of `Sym_A(M)` is the range of `ι`. -/
private theorem mem_symmetricPower_one_iff {x : SymmetricAlgebra A M} :
    x ∈ SymPow.symmetricPower 1 A M ↔ x ∈ LinearMap.range (ι A M) := by
  rw [SymPow.symmetricPower, pow_one]

/-- **The canonical map `M = Sym¹_A(M) → Γ(Proj(Sym_A(M)), 𝒪(1))`**, which is the map
`Sym¹(M̃) → π_* 𝒪_{𝐏(M̃)}(1)` of Stacks 01OB read on global sections over the affine base. -/
public def toTwistSections (m : M) : twistGlobalSections (grading A M) 1 :=
  degreeSection (grading A M) 1 (toGradingOne A M m)

/-- **An element of `M` killed by every degree-one generator of `Sym_A(M)` has vanishing section
on the first twist.** The degree-one component annihilates it, and the symmetric algebra is
generated in degree one, so the criterion
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_eq_zero_of_annihilating_degree`
applies. -/
public theorem toTwistSections_eq_zero_of_forall_mul_eq_zero {m : M}
    (h : ∀ z : M, ι A M z * ι A M m = 0) : toTwistSections A M m = 0 := by
  refine degreeSection_eq_zero_of_annihilating_degree (grading A M)
    (adjoin_grading_one_eq_top A M) _ ⟨1, fun y hy => ?_⟩
  obtain ⟨z, rfl⟩ := (mem_symmetricPower_one_iff A M).1 hy
  exact h z

/-- The canonical map sends `0` to the zero section. -/
@[simp] public theorem toTwistSections_zero : toTwistSections A M 0 = 0 :=
  toTwistSections_eq_zero_of_forall_mul_eq_zero A M (by simp)

/-- **A nonzero element of `M` killed by every degree-one generator of `Sym_A(M)` witnesses that
`M → Γ(Proj(Sym_A(M)), 𝒪(1))` is not injective.** -/
public theorem not_injective_toTwistSections {m : M} (hm : m ≠ 0)
    (h : ∀ z : M, ι A M z * ι A M m = 0) :
    ¬ Function.Injective (toTwistSections A M) := fun hinj =>
  hm (hinj ((toTwistSections_eq_zero_of_forall_mul_eq_zero A M h).trans
    (toTwistSections_zero A M).symm))

/-- The standard opens of the degree-one elements cover `Proj(Sym_A(M))`. -/
public theorem iSup_basicOpen_toGradingOne_eq_top :
    ⨆ f : grading A M 1, Proj.basicOpen (grading A M) (f : SymmetricAlgebra A M) = ⊤ :=
  Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top (grading A M)
    (adjoin_grading_one_eq_top A M)

/-- Every degree-one element of `Sym_A(M)` is `ι` of an element of `M`. -/
public theorem mem_grading_one_iff {x : SymmetricAlgebra A M} :
    x ∈ grading A M 1 ↔ x ∈ LinearMap.range (ι A M) :=
  mem_symmetricPower_one_iff A M

/-- **The standard opens of the images of a spanning family of `M` cover `Proj(Sym_A(M))`.**
For `M` generated by two elements this is the two-chart affine covering of the projective bundle
that Stacks 01OC records. -/
public theorem iSup_basicOpen_eq_top_of_span {ι' : Type*} (v : ι' → M)
    (hv : Submodule.span A (Set.range v) = ⊤) :
    ⨆ i, Proj.basicOpen (grading A M) (ι A M (v i)) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' (grading A M) (fun i => ι A M (v i))
    (fun i => ⟨1, (mem_grading_one_iff A M).mpr (LinearMap.mem_range_self _ _)⟩) ?_
  have hbase : ∀ a : A, algebraMap A (SymmetricAlgebra A M) a ∈ grading A M 0 := fun a => by
    change algebraMap A (SymmetricAlgebra A M) a ∈ SymPow.symmetricPower 0 A M
    rw [SymPow.symmetricPower, pow_zero, Submodule.one_eq_range]
    exact ⟨a, rfl⟩
  have hsub : ∀ m ∈ Submodule.span A (Set.range v), ι A M m ∈
      Algebra.adjoin (grading A M 0) (Set.range fun i => ι A M (v i)) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Algebra.subset_adjoin ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
        rw [map_smul, Algebra.smul_def]
        exact mul_mem (Subalgebra.algebraMap_mem _ (⟨_, hbase a⟩ : grading A M 0)) hx
  refine le_antisymm le_top ?_
  rw [← adjoin_grading_one_eq_top A M]
  refine Algebra.adjoin_le fun x hx => ?_
  obtain ⟨m, rfl⟩ := (mem_grading_one_iff A M).mp hx
  exact hsub m (hv ▸ Submodule.mem_top)

end SymmetricAlgebra

end
