module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Localization
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantQuotientFunctor
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.VanishingKernel

/-!
# The irrelevant modules are exactly the kernel of `M ↦ M̃`, and the induced functor is faithful

Let `A` be a graded ring which is Noetherian as a ring, generated over `A₀` by finitely many
homogeneous elements `f i` of positive degrees `deg i`, and let `d` be a positive integer
divisible by every `deg i` — the degree of Stacks 0BXE, taken there to be the least common
multiple of the `deg i`. This file proves the kernel identification of Stacks 0BXF,

`Mod^fg_{A, irrelevant} = Ker (M ↦ M̃)`,

and deduces from it, through Stacks 06XK, that the induced functor on the quotient category
`Mod^fg_A / Mod^fg_{A, irrelevant}` is **faithful**.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.irrelevantModules_eq_kernel`: **the
  irrelevant finitely generated graded modules are exactly the kernel of `M ↦ M̃`.**
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.faithful_irrelevantQuotientFunctor`: **the
  functor of Stacks 0BXF is faithful.**
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_pos_faithful_irrelevantQuotientFunctor`:
  for `A` Noetherian graded, some positive degree `d` makes the functor faithful.

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 06XK](https://stacks.math.columbia.edu/tag/06XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] [IsNoetherianRing S]

/-- **Stacks 0BXF, the kernel identification.** The irrelevant finitely generated graded modules
are exactly the objects killed by `M ↦ M̃`. -/
public theorem irrelevantModules_eq_kernel
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    {d : ℕ} (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d) :
    irrelevantModules.{u, u, w} 𝒮 d = (finiteAssociatedSheafFunctor.{u, w} 𝒮).kernel := by
  refine le_antisymm (irrelevantModules_le_kernel 𝒮 hd) fun M hM ↦ ?_
  have := M.property
  exact isIrrelevant_of_isZero 𝒮 f deg hdeg hf hgen hd hdvd (X := M.obj) (hX := hM)

/-- **The functor of Stacks 0BXF is faithful.** -/
public theorem faithful_irrelevantQuotientFunctor
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    {d : ℕ} (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d) :
    (irrelevantQuotientFunctor.{u, w} 𝒮 hd).Faithful := by
  have := isSerreClass_irrelevantModules 𝒮 hd
  have := preservesFiniteLimits_finiteAssociatedSheafFunctor.{u, w} 𝒮
  have := preservesFiniteColimits_finiteAssociatedSheafFunctor.{u, w} 𝒮
  exact (ObjectProperty.SerreClassLocalization.faithful_iff
    (toIrrelevantQuotient.{u, u, w} 𝒮 hd) (irrelevantModules.{u, u, w} 𝒮 d)
    (irrelevantQuotientFunctor.{u, w} 𝒮 hd)
    (irrelevantQuotientFunctorFac 𝒮 hd)).2
    (irrelevantModules_eq_kernel 𝒮 f deg hdeg hf hgen hd hdvd)

/-! ### For Noetherian graded rings -/

/-- **Faithfulness for `A` Noetherian graded.** There is a positive degree `d` for which the
functor of Stacks 0BXF out of `Mod^fg_A / Mod^fg_{A, irrelevant}` is faithful. -/
public theorem exists_pos_faithful_irrelevantQuotientFunctor :
    ∃ (d : ℕ) (hd : 0 < d), (irrelevantQuotientFunctor.{u, w} 𝒮 hd).Faithful := by
  obtain ⟨r, f, deg, hdeg, hf, hgen⟩ := exists_homogeneous_generators_of_isNoetherianRing 𝒮
  have hd : 0 < Finset.univ.lcm deg := Nat.pos_of_ne_zero fun h0 ↦ by
    obtain ⟨i, -, hi⟩ := Finset.lcm_eq_zero_iff.mp h0
    exact (hdeg i).ne' hi
  exact ⟨_, hd, faithful_irrelevantQuotientFunctor 𝒮 f deg hdeg hf hgen hd
    fun i ↦ Finset.dvd_lcm (Finset.mem_univ i)⟩

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
