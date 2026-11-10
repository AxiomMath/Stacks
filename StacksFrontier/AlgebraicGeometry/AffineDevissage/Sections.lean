module

public import StacksFrontier.AlgebraicGeometry.IdealPowerSectionsSurjective.Basic
public import StacksFrontier.AlgebraicGeometry.AffineDevissage.Torsion

/-!
# The affine case of Tag 01YB for a finite module, with no torsion hypothesis

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `M` a **finite** `A`-module. This file proves
that the canonical map

`colim_n Hom_A(Iⁿ, M) → Γ(Spec(A) \ V(I), M̃)`

is bijective. Injectivity is
`Stacks.AlgebraicGeometry.IdealPowerSections.canonicalMapToSections_injective`, which needs only
that `I` is finitely generated. Surjectivity is proved here: the torsion hypothesis of
`Stacks.AlgebraicGeometry.IdealPowerSections.canonicalMapToSections_surjective` is removed by the
Artin–Rees devissage of
`Stacks.AlgebraicGeometry.IdealPowerSections.exists_forall_smul_eq_zero_imp_eq_zero`.

This is the affine case of the second displayed isomorphism of [Stacks, Tag 01YB] for a coherent
module, and the affine input to the global statement.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerSections.exists_sectionOfHom_eq_of_finite`: surjectivity in
  representative form.
* `Stacks.AlgebraicGeometry.IdealPowerSections.canonicalMapToSections_surjective_of_finite`,
  `canonicalMapToSections_bijective_of_finite`, `isIso_canonicalMapToSections_of_finite`.

## Implementation notes

The source replaces the sheaf `F` by `Iᵐ F`, which has the same sections away from `V(I)`, and
applies the torsion-free case to it; carrying that out literally would need the comparison
`Γ(U, (Iᵐ M)˜) ≅ Γ(U, M̃)`. The route taken here avoids that comparison entirely by shifting the
**numerators** instead of the module: given a section `t` of `M̃` on `Spec(A) \ V(I)`,
`Stacks.AlgebraicGeometry.IdealPowerSections.exists_uniform_fractions` writes it as `y f / f ⁿ`
on each `D(f)`, `f` in a generating set of `I`, with the exact cross relations
`f' ⁿ • y f = f ⁿ • y f'`; multiplying every numerator by `f ᵐ` gives numerators **inside** the
submodule `Iᵐ M`, satisfying the same cross relations at the exponent `n + m`, and the same
fraction, by `Stacks.AlgebraicGeometry.IdealPowerSections.mk_pow_cancel_le`. The representative
is then built by
`Stacks.AlgebraicGeometry.IdealPowerSections.exists_hom_of_crossRelations` **in the module
`Iᵐ M`**, where the uniqueness it needs is exactly what Artin–Rees supplies, and pushed into `M`
along the inclusion.

The shifted numerators are only defined on the generating set, so the total function handed to
`exists_hom_of_crossRelations` is a `dite` which is zero off that set; `shiftedNumerator_val` is
the one rewrite that unfolds it, and everything else is stated through that lemma.

## References

* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.StructureSheaf
open PrimeSpectrum (basicOpen)

universe u v

namespace Stacks.AlgebraicGeometry.IdealPowerSections

section Devissage

variable (A : Type u) [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- **Surjectivity of the canonical map of [Stacks, Tag 01PM] with no torsion hypothesis**, in
representative form: for a Noetherian ring `A` and a finite `A`-module `M`, every section of `M̃`
on `Spec(A) \ V(I)` is the section attached to some `φ : Iⁿ → M`. -/
public theorem exists_sectionOfHom_eq_of_finite [IsNoetherianRing A] [Module.Finite A M]
    (t : sectionsOnComplement A I M) :
    ∃ (n : ℕ) (φ : (I ^ n : Ideal A) →ₗ[A] M), sectionOfHom A I M n φ = t := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : (I : Submodule A A).FG)
  obtain ⟨m, hm⟩ := exists_forall_smul_eq_zero_imp_eq_zero A M I
  have haI : ∀ a ∈ s, a ∈ I := fun a ha => hs ▸ Ideal.subset_span ha
  -- the lifted generating set, and its basic opens inside the complement
  have hmemJ : ∀ a ∈ s, (ULift.up a : ULift.{v} A) ∈ liftedIdeal.{u, v} A I := fun a ha =>
    (mem_liftedIdeal A I).mpr (haI a ha)
  have hGW : ∀ f ∈ s.image (ULift.up : A → ULift.{v} A),
      basicOpen f ≤ complementVanishing (ULift.{v} A) (liftedIdeal.{u, v} A I) := by
    intro f hf
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
    exact basicOpen_le_liftedComplement A I _ (hmemJ a ha)
  -- one exponent and exact cross relations
  obtain ⟨n, Y, hY, hYcross⟩ := exists_uniform_fractions t.1 t.2
    (s.image (ULift.up : A → ULift.{v} A)) hGW
  have hcross : ∀ a ∈ s, ∀ b ∈ s,
      b ^ n • (Y (ULift.up a)).down = a ^ n • (Y (ULift.up b)).down := fun a ha b hb =>
    congrArg ULift.down (hYcross _ (Finset.mem_image_of_mem _ ha) _ (Finset.mem_image_of_mem _ hb))
  -- the numerators, shifted into the submodule `I ^ m • M`
  have hyMem : ∀ a ∈ s, a ^ m • (Y (ULift.up a)).down ∈ I ^ m • (⊤ : Submodule A M) :=
    fun a ha => Submodule.smul_mem_smul
      (Ideal.pow_mem_pow (haI a ha) m) Submodule.mem_top
  set yN : A → ↥(I ^ m • (⊤ : Submodule A M)) := fun a =>
    if ha : a ∈ s then ⟨a ^ m • (Y (ULift.up a)).down, hyMem a ha⟩ else 0 with hyNdef
  have hyN : ∀ a ∈ s, ((yN a : M)) = a ^ m • (Y (ULift.up a)).down := by
    intro a ha
    simp only [hyNdef, ha, ↓reduceDIte]
  have hcrossN : ∀ f ∈ s, ∀ f' ∈ s, f' ^ (n + m) • yN f = f ^ (n + m) • yN f' := by
    intro f hf f' hf'
    have h : (f ^ m * f' ^ m) • (f' ^ n • (Y (ULift.up f)).down)
        = (f ^ m * f' ^ m) • (f ^ n • (Y (ULift.up f')).down) :=
      congrArg _ (hcross f hf f' hf')
    rw [smul_smul, smul_smul] at h
    refine Subtype.ext ?_
    change f' ^ (n + m) • ((yN f : M)) = f ^ (n + m) • ((yN f' : M))
    rw [hyN f hf, hyN f' hf', smul_smul, smul_smul,
      show f' ^ (n + m) * f ^ m = f ^ m * f' ^ m * f' ^ n by ring,
      show f ^ (n + m) * f' ^ m = f ^ m * f' ^ m * f ^ n by ring]
    exact h
  -- the representative, built inside `I ^ m • M`
  obtain ⟨ψ, hψ⟩ := exists_hom_of_crossRelations A ↥(I ^ m • (⊤ : Submodule A M))
    hs hm (n + m) yN hcrossN
  have hψ' : ∀ (b : ↥(Ideal.span ((· ^ (n + m)) '' (s : Set A)))) (f : A), f ∈ s →
      f ^ (n + m) • ((ψ b : M)) = (b : A) • (f ^ m • (Y (ULift.up f)).down) := by
    intro b f hf
    rw [← hyN f hf]
    exact congrArg Subtype.val (hψ b f hf)
  -- a power of `I` lands in the ideal generated by the `(n + m)`-th powers of the generators
  have hrad : I ≤ Ideal.radical (Ideal.span ((· ^ (n + m)) '' (s : Set A))) := by
    rw [← hs]
    exact Ideal.span_le.mpr fun a ha => ⟨n + m, Ideal.subset_span ⟨a, ha, rfl⟩⟩
  obtain ⟨N₀, hN₀⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad ⟨s, hs⟩
  have hIN : I ^ (N₀ + (n + m)) ≤ Ideal.span ((· ^ (n + m)) '' (s : Set A)) :=
    le_trans (Ideal.pow_le_pow_right (Nat.le_add_right N₀ (n + m))) hN₀
  refine ⟨N₀ + (n + m),
    (I ^ m • (⊤ : Submodule A M)).subtype ∘ₗ ψ ∘ₗ Submodule.inclusion hIN,
    Subtype.ext (funext fun x => ?_)⟩
  -- pointwise comparison, at a generator avoiding the prime
  obtain ⟨a, ha, hax⟩ := exists_generator_notMem A I hs x.1 x.2
  -- `t` as a fraction with denominator `a ^ (n + m)` and numerator inside `I ^ m • M`
  have hshift : t.1 x = LocalizedModule.mk
      (((ULift.up a : ULift.{v} A) ^ m) • Y (ULift.up a))
      ⟨(ULift.up a : ULift.{v} A) ^ (n + m), Submonoid.pow_mem _ hax (n + m)⟩ := by
    have hcan := mk_pow_cancel_le (N := ULift.{u} M) hax (Nat.le_add_right n m)
      (Y (ULift.up a))
    rw [Nat.add_sub_cancel_left] at hcan
    exact (hY _ (Finset.mem_image_of_mem _ ha) x.1 hax x.2).trans hcan.symm
  refine Eq.trans (fractionSectionFun_apply
    (liftedNumerator_cross A I M (N₀ + (n + m))
      ((I ^ m • (⊤ : Submodule A M)).subtype ∘ₗ ψ ∘ₗ Submodule.inclusion hIN)) x
    ⟨ULift.up a, hmemJ a ha⟩ hax) ?_
  refine Eq.trans (LocalizedModule.mk_eq.mpr ⟨1, ?_⟩) hshift.symm
  refine congrArg (fun z => (1 : (x.1 : PrimeSpectrum (ULift.{v} A)).asIdeal.primeCompl) • z)
    (ULift.ext ?_)
  exact hψ' ⟨a ^ (N₀ + (n + m)),
    hIN (Ideal.pow_mem_pow (haI a ha) (N₀ + (n + m)))⟩ a ha

/-- **Surjectivity of the canonical map of [Stacks, Tag 01PM] with no torsion hypothesis.** For a
Noetherian ring `A`, an ideal `I` and a finite `A`-module `M`, the canonical map
`colim_n Hom_A(Iⁿ, M) → Γ(Spec(A) \ V(I), M̃)` is surjective. -/
public theorem canonicalMapToSections_surjective_of_finite [IsNoetherianRing A]
    [Module.Finite A M] :
    Function.Surjective (canonicalMapToSections A I M) := by
  intro t
  obtain ⟨n, φ, hφ⟩ := exists_sectionOfHom_eq_of_finite A I M t
  exact ⟨colimit.ι (idealPowersHom A I M) n φ,
    (canonicalMapToSections_colimit_ι A I M n φ).trans hφ⟩

/-- **The affine case of the second isomorphism of [Stacks, Tag 01YB].** For a Noetherian ring
`A`, an ideal `I` and a finite `A`-module `M`, the canonical map
`colim_n Hom_A(Iⁿ, M) → Γ(Spec(A) \ V(I), M̃)` is bijective, with no hypothesis on the torsion of
`M`. -/
public theorem canonicalMapToSections_bijective_of_finite [IsNoetherianRing A]
    [Module.Finite A M] :
    Function.Bijective (canonicalMapToSections A I M) :=
  ⟨canonicalMapToSections_injective A I M (IsNoetherian.noetherian I),
    canonicalMapToSections_surjective_of_finite A I M⟩

/-- The canonical map of [Stacks, Tag 01PM] is an isomorphism for a finite module over a
Noetherian ring. -/
public theorem isIso_canonicalMapToSections_of_finite [IsNoetherianRing A] [Module.Finite A M] :
    IsIso (canonicalMapToSections A I M) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact canonicalMapToSections_bijective_of_finite A I M

end Devissage

end Stacks.AlgebraicGeometry.IdealPowerSections

end
