module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.VanishingAfterBaseChange
public import StacksFrontier.RingTheory.Flat.MakeMapZeroIdeal

/-!
# The least ideal through which a map into a projective module factors

Let `R` be a commutative ring and let `u : M →ₗ[R] N` be a map of `R`-modules whose target is
projective.  Among the ideals `J` of `R` with `u(M) ⊆ J · N` there is a least one, and the
condition on `J` is exactly that it contain that least ideal.  Equivalently: the ideals killing
the map modulo themselves form a principal filter in the lattice of ideals.

This is the flattening ideal of Stacks 083L read through the elementwise condition
`u m ∈ J • (⊤ : Submodule R N)`, which is the form in which a chart-wise geometric consumer meets
it: `Stacks.Flattening.rTensor_quotient_eq_zero_iff_forall_mem_smul_top` identifies that condition
with the vanishing of the base change of `u` to `R ⧸ J`, and
`Module.exists_ideal_rTensor_eq_zero_iff_map_eq_bot` identifies *that* with containment of the
flattening ideal.

## Main results

* `Stacks.Flattening.exists_least_ideal_forall_mem_smul_top`: for a projective target there is an
  ideal `I` with `(∀ m, u m ∈ J • ⊤) ↔ I ≤ J` for every ideal `J`.
* `Stacks.Flattening.forall_mem_smul_top_of_forall_le`: the consequence actually used — if
  `u(M) ⊆ J · N` for every `J` in a family of ideals, then `u(M) ⊆ J₀ · N` for any ideal `J₀`
  containing every element common to the family.  No intersection is formed: the hypothesis is
  stated as a containment of the common elements, which is what a closure argument in `Spec R`
  produces.

## Implementation notes

The universe of the test ring in `Module.exists_ideal_rTensor_eq_zero_iff_map_eq_bot` is a free
variable of that statement, so it may be instantiated at the universe of `R` itself, which is
where `R ⧸ J` lives; no universe constraint is placed on `M` or `N`.

No tag is claimed.  Stacks 083L asserts the existence of the ideal detecting base changes on
which the map vanishes, and that is
`Module.exists_ideal_rTensor_eq_zero_iff_map_eq_bot`; what is added here is the elementwise
reading and the closure property it gives, neither of which the tag states.

## References

* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
-/

@[expose] public section

namespace Stacks.Flattening

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- **An ideal `J` kills a map into a projective module modulo `J` exactly when it contains one
fixed ideal.**  For `u : M →ₗ[R] N` with `N` projective there is an ideal `I` of `R` such that
`u m ∈ J • N` for every `m` precisely when `I ≤ J`.

`I` is the flattening ideal of Stacks 083L: the condition `∀ m, u m ∈ J • N` is the vanishing of
the base change of `u` to `R ⧸ J`
(`Stacks.Flattening.rTensor_quotient_eq_zero_iff_forall_mem_smul_top`), which Stacks 083L
identifies with the vanishing of the image of `I` in `R ⧸ J`, i.e. with `I ≤ J`. -/
theorem exists_least_ideal_forall_mem_smul_top (u : M →ₗ[R] N) (hN : Module.Projective R N) :
    ∃ I : Ideal R, ∀ J : Ideal R,
      (∀ m : M, u m ∈ J • (⊤ : Submodule R N)) ↔ I ≤ J := by
  obtain ⟨I, hI⟩ :=
    Module.exists_ideal_rTensor_eq_zero_iff_map_eq_bot.{u, v, w, u} u hN
  refine ⟨I, fun J => ?_⟩
  have h := hI (R ⧸ J) (algebraMap R (R ⧸ J))
  rw [show (algebraMap R (R ⧸ J)).toAlgebra = _ from toAlgebra_algebraMap] at h
  rw [← rTensor_quotient_eq_zero_iff_forall_mem_smul_top u, h,
    Ideal.map_eq_bot_iff_le_ker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- **A map into a projective module whose values lie in `J · N` for every `J` in a family lies in
`J₀ · N` for every ideal `J₀` containing the elements common to the family.**

The least ideal `I` of `Stacks.Flattening.exists_least_ideal_forall_mem_smul_top` is contained in
every member of the family, hence in `J₀`, hence `u(M) ⊆ J₀ · N`.  Stating the hypothesis as a
containment of common elements rather than as `⨅ J ≤ J₀` is what a closure argument in `Spec R`
supplies: there one knows of each individual function that it vanishes at the limit point. -/
theorem forall_mem_smul_top_of_forall_le (u : M →ₗ[R] N) (hN : Module.Projective R N)
    {ι : Type*} (𝒥 : ι → Ideal R) (J₀ : Ideal R)
    (hu : ∀ i, ∀ m : M, u m ∈ 𝒥 i • (⊤ : Submodule R N))
    (hcommon : ∀ a : R, (∀ i, a ∈ 𝒥 i) → a ∈ J₀) :
    ∀ m : M, u m ∈ J₀ • (⊤ : Submodule R N) := by
  obtain ⟨I, hI⟩ := exists_least_ideal_forall_mem_smul_top u hN
  exact (hI J₀).mpr fun a ha => hcommon a fun i => (hI (𝒥 i)).mp (hu i) ha

end Stacks.Flattening

end
