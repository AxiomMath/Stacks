module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# `Hⁱ_c(X_k̄, -)` is exact in the middle on short exact sequences

A short exact sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes of sheaves of
`Λ`-modules on `X_étale` gives a distinguished triangle of `RΓ_c(X_k̄, -)`
(`Stacks.EtaleCohomology.compactSupportFrobeniusTriangle`), and the homology functors of the
derived category are homological, so

`Hⁱ_c(X_k̄, K₁) → Hⁱ_c(X_k̄, K₂) → Hⁱ_c(X_k̄, K₃)`

is exact, the maps being `Hⁱ_c` of the maps of the sequence.  For the open–closed sequence
`0 → j_! j⁻¹ K → K → i_* i⁻¹ K → 0` this is the excision sequence through which the weight bound
of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) is propagated over a
stratification; the maps commute with the geometric Frobenius `π_X^*` because
`Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusNatTrans` is natural.

## Main results

* `Stacks.EtaleCohomology.exact_homology_compactSupportFrobeniusFunctor_map`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **Exactness in the middle of `Hⁱ_c(X_k̄, -)` on a short exact sequence** of bounded below
complexes of sheaves of `Λ`-modules on `X_étale`. -/
public theorem exact_homology_compactSupportFrobeniusFunctor_map
    {S : ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ)} (hS : S.ShortExact)
    (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
    (h₃ : CochainComplex.plus _ S.X₃) (i : ℤ) :
    Function.Exact
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map
          (ObjectProperty.homMk S.f : (⟨S.X₁, h₁⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₂, h₂⟩))).hom
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, r} Λ f j kbar).map
          (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩))).hom := by
  -- the characteristic of `k` plays no role in exactness; any Frobenius datum builds the triangle
  have := Fintype.ofFinite k
  obtain ⟨p, hp⟩ := CharP.exists k
  have : CharP k p := hp
  obtain ⟨n, hpr, hn⟩ := FiniteField.card k p
  have : Fact p.Prime := ⟨hpr⟩
  have hT := compactSupportFrobeniusTriangle_distinguished.{u, r} Λ f j kbar p n hn hS h₁ h₂ h₃
  have hex :=
    (DerivedCategory.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map_distinguished_exact _ hT
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hex

end Stacks.EtaleCohomology

end
