module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactHomology

/-!
# Injectivity and surjectivity in the long exact sequence of `Hⁱ_c(X_k̄, -)`

A short exact sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes of sheaves of
`Λ`-modules on `X_étale` gives a distinguished triangle of `RΓ_c(X_k̄, -)`
(`Stacks.EtaleCohomology.compactSupportFrobeniusTriangle`), hence a long exact sequence of the
`Hⁱ_c(X_k̄, -)`. This file records the four consequences of a vanishing neighbour in it:

* `Hⁱ_c(K₁) → Hⁱ_c(K₂)` is injective when `Hⁱ⁻¹_c(K₃) = 0`, and surjective when `Hⁱ_c(K₃) = 0`;
* `Hⁱ_c(K₂) → Hⁱ_c(K₃)` is surjective when `Hⁱ⁺¹_c(K₁) = 0`, and injective when `Hⁱ_c(K₁) = 0`.

With the vanishing of `Hⁱ_c` in negative degrees, the first gives the left exactness of
`H⁰_c(X_k̄, -)`; with its vanishing above `2 dim X` (in the namespace `Stacks.EtaleCohomology`,
`isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le`) the third
gives the right exactness of `H^{2 dim X}_c(X_k̄, -)`.

## Main results

* `Stacks.EtaleCohomology.mono_homology_compactSupportFrobeniusFunctor_map_f`
* `Stacks.EtaleCohomology.epi_homology_compactSupportFrobeniusFunctor_map_f`
* `Stacks.EtaleCohomology.epi_homology_compactSupportFrobeniusFunctor_map_g`
* `Stacks.EtaleCohomology.mono_homology_compactSupportFrobeniusFunctor_map_g`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]
  {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)} (hS : S.ShortExact)
  (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
  (h₃ : CochainComplex.plus _ S.X₃)

omit [Finite k] in
/-- For some Frobenius datum on the finite field `k`, the triangle of `RΓ_c` is distinguished;
exactness does not depend on the datum. -/
private lemma exists_compactSupportFrobeniusTriangle_distinguished [Fintype k] :
    ∃ (p n : ℕ) (_ : Fact p.Prime) (_ : CharP k p) (hn : Fintype.card k = p ^ n),
      compactSupportFrobeniusTriangle.{u, r} Λ f j kbar p n hn hS h₁ h₂ h₃ ∈
        distTriang (DerivedCategory (ModuleCat.{max (u + 1) r} Λ)) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨n, hpr, hn⟩ := FiniteField.card k p
  have : Fact p.Prime := ⟨hpr⟩
  exact ⟨p, n, this, hp, hn, compactSupportFrobeniusTriangle_distinguished.{u, r} Λ f j kbar
    p n hn hS h₁ h₂ h₃⟩

include hS in
/-- **`Hⁱ_c(K₁) → Hⁱ_c(K₂)` is injective when `Hⁱ⁻¹_c(K₃) = 0`.** -/
public theorem mono_homology_compactSupportFrobeniusFunctor_map_f (i₀ i : ℤ) (hi : i₀ + 1 = i)
    (h : IsZero (compactSupportFrobeniusCohomologyGroup.{u, r} Λ f j kbar ⟨S.X₃, h₃⟩ i₀)) :
    Mono ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map
        (ObjectProperty.homMk S.f : (⟨S.X₁, h₁⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₂, h₂⟩))) := by
  have := Fintype.ofFinite k
  obtain ⟨p, n, _, _, hn, hT⟩ :=
    exists_compactSupportFrobeniusTriangle_distinguished Λ f j kbar hS h₁ h₂ h₃
  exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT i₀ i hi).2
    (h.eq_of_src _ _)

include hS in
/-- **`Hⁱ_c(K₁) → Hⁱ_c(K₂)` is surjective when `Hⁱ_c(K₃) = 0`.** -/
public theorem epi_homology_compactSupportFrobeniusFunctor_map_f (i : ℤ)
    (h : IsZero (compactSupportFrobeniusCohomologyGroup.{u, r} Λ f j kbar ⟨S.X₃, h₃⟩ i)) :
    Epi ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map
        (ObjectProperty.homMk S.f : (⟨S.X₁, h₁⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₂, h₂⟩))) := by
  have := Fintype.ofFinite k
  obtain ⟨p, n, _, _, hn, hT⟩ :=
    exists_compactSupportFrobeniusTriangle_distinguished Λ f j kbar hS h₁ h₂ h₃
  exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT i).2 (h.eq_of_tgt _ _)

include hS in
/-- **`Hⁱ_c(K₂) → Hⁱ_c(K₃)` is surjective when `Hⁱ⁺¹_c(K₁) = 0`.** -/
public theorem epi_homology_compactSupportFrobeniusFunctor_map_g (i i₁ : ℤ) (hi : i + 1 = i₁)
    (h : IsZero (compactSupportFrobeniusCohomologyGroup.{u, r} Λ f j kbar ⟨S.X₁, h₁⟩ i₁)) :
    Epi ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map
        (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩))) := by
  have := Fintype.ofFinite k
  obtain ⟨p, n, _, _, hn, hT⟩ :=
    exists_compactSupportFrobeniusTriangle_distinguished Λ f j kbar hS h₁ h₂ h₃
  exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT i i₁ hi).2
    (h.eq_of_tgt _ _)

include hS in
/-- **`Hⁱ_c(K₂) → Hⁱ_c(K₃)` is injective when `Hⁱ_c(K₁) = 0`.** -/
public theorem mono_homology_compactSupportFrobeniusFunctor_map_g (i : ℤ)
    (h : IsZero (compactSupportFrobeniusCohomologyGroup.{u, r} Λ f j kbar ⟨S.X₁, h₁⟩ i)) :
    Mono ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map
        (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩))) := by
  have := Fintype.ofFinite k
  obtain ⟨p, n, _, _, hn, hT⟩ :=
    exists_compactSupportFrobeniusTriangle_distinguished Λ f j kbar hS h₁ h₂ h₃
  exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff _ hT i).2 (h.eq_of_src _ _)

end Stacks.EtaleCohomology

end
