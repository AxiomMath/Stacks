module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AdjointGeometricCohomologyTwo

/-!
# The deformation ring of `ρ₀` with fixed determinant is finite flat over `ℤ_ℓ` (Tag 03W1)

Let `X` be a smooth, geometrically irreducible, proper (equivalently projective) curve over a
finite field `k` of characteristic `p`, `k̄` an algebraic closure of `k`, `ℓ ≠ p` a prime and
`ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` a continuous representation. Assume

1. de Jong's conjecture holds for `X`: for every `m` and every continuous
   `ρ : π₁(X) → GL_m(𝐅_ℓ[[t]])` the image `ρ(π₁(X_k̄))` is finite;
2. `ρ₀|_{π₁(X_k̄)}` is absolutely irreducible;
3. `ℓ ∤ n`.

Then for every continuous character `δ : π₁(X) → ℤ_ℓ^*` lifting `det ρ₀`, the universal
deformation ring `R_univ` of `ρ₀` with determinant fixed to `δ` is finite and flat over `ℤ_ℓ`
(`AlgebraicGeometry.finite_flat_of_isUniversalFixedDeterminantDeformation`).

The source states the theorem with "determinant fixed to `δ`"; without that condition the
universal deformation ring is not finite over `ℤ_ℓ`
(`Deformation.IsUniversalDeformation.not_moduleFinite`, twists by characters into
`𝐅_ℓ[[T]]/(T^{ℓ^j})`), so the determinant-fixed statement is the one formalized.

## Proof

* finiteness: `AlgebraicGeometry.moduleFinite_of_isUniversalFixedDeterminantDeformation_of_normal`
  with the normality of `π₁(X_k̄) ⊆ π₁(X)` (Tag 0BTX);
* flatness: `AlgebraicGeometry.flat_of_isUniversalFixedDeterminantDeformation_of_vanishesTwo`,
  whose input `H ²(π₁(X_k̄), ad⁰ ρ₀) = 0` is trivial in genus `0` (`π₁(X_k̄) = 1`) and in genus
  `≥ 1` is `AlgebraicGeometry.vanishesTwo_adZero_of_one_le_genus`: the comparison
  `H ²(π₁(X_k̄), ad⁰) ≅ H ²(X_k̄, ℱ_{ad⁰})` (Tag 03VM), `H ² = H ²_c` for proper `X` and
  `H ²_c(X_k̄, ℱ_{ad⁰}) ≅ (ad⁰)_{π₁(X_k̄)}` (Tag 03VK), and the vanishing of these coinvariants
  by the trace pairing (`Deformation.AdZero.span_smul_sub_eq_top`).

## Implementation notes

`X_k̄` is `pullback f (Spec k̄ ⟶ Spec k)` and `π₁(X_k̄) → π₁(X)` is
`AlgebraicGeometry.etaleFundamentalGroupMap` of the projection, at a geometric point `x` of
`X_k̄`. The connectedness of `X` and `X_k̄` that the fundamental groups need is derived inside
the statement from `X` being a geometrically irreducible curve. The universal deformation ring is
`Deformation.IsUniversalFixedDeterminantDeformation`, the universal property of the source's
explanation following the theorem (with `δ` lifting `det ρ₀` as its first field).

## References

* [Stacks Project, Tag 03W1](https://stacks.math.columbia.edu/tag/03W1)
* [dJ-conjecture, Theorem 3.5]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology
open scoped PowerSeries.WithPiTopology

universe u v

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 03W1.** Let `X` be a smooth, geometrically irreducible, proper curve
over a finite field `k` of characteristic `p`, `k̄` an algebraic closure of `k`, `x` a geometric
point of `X_k̄`, `ℓ ≠ p` a prime and `ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` continuous. Assume de Jong's
conjecture for `X` (in every rank `m`, every continuous `ρ : π₁(X) → GL_m(𝐅_ℓ[[t]])` has finite
image on `π₁(X_k̄)`), that `ρ₀|_{π₁(X_k̄)}` is absolutely irreducible and that `ℓ ∤ n`. Then for
every continuous character `δ : π₁(X) → ℤ_ℓ^*`, the universal deformation ring `R` of `ρ₀` with
determinant fixed to `δ` (`δ` lifts `det ρ₀`, a field of the universal property) is finite and
flat over `ℤ_ℓ`. -/
@[stacks 03W1 "the theorem in full, with the determinant fixed to delta: the universal \
deformation ring is finite and flat over Z_l"]
theorem finite_flat_of_isUniversalFixedDeterminantDeformation
    (k kbar : Type u) [Field k] [Finite k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (p ℓ n : ℕ) [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hn : ¬ ℓ ∣ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] [GeometricallyIrreducible f] :
    letI : ConnectedSpace X :=
      haveI : IsIntegral X := (inferInstance : IsCurve k f).toIsIntegral
      inferInstance
    letI : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) :=
      @IrreducibleSpace.connectedSpace _ _
        ((inferInstance : GeometricallyIrreducible f).geometrically_irreducibleSpace
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (pullback.fst _ _) (pullback.snd _ _)
          (IsPullback.of_hasPullback _ _))
    ∀ (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
      (ρ₀ : EtaleFundamentalGroup X (x.map (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
          Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
      (δ : EtaleFundamentalGroup X (x.map (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ* ℤ_[ℓ]ˣ),
      (∀ (m : ℕ) (ρ : EtaleFundamentalGroup X (x.map (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
          Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
        (Set.range fun g : EtaleFundamentalGroup _ x => ρ (etaleFundamentalGroupMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x g)).Finite) →
      (Deformation.IsAbsolutelyIrreducible fun g : EtaleFundamentalGroup _ x =>
        ρ₀ (etaleFundamentalGroupMap (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x g)) →
      ∀ (R : Type v) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
        (reduce : R →+* ZMod ℓ)
        (ρuniv : EtaleFundamentalGroup X (x.map (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
            Matrix.GeneralLinearGroup (Fin n) R),
        Deformation.IsUniversalFixedDeterminantDeformation ℓ n _ ρ₀ δ R reduce ρuniv →
        Module.Finite ℤ_[ℓ] R ∧ Module.Flat ℤ_[ℓ] R := by
  have : ConnectedSpace X :=
    have : IsIntegral X := (inferInstance : IsCurve k f).toIsIntegral
    inferInstance
  have : ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) :=
    @IrreducibleSpace.connectedSpace _ _
      ((inferInstance : GeometricallyIrreducible f).geometrically_irreducibleSpace
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) (pullback.fst _ _) (pullback.snd _ _)
        (IsPullback.of_hasPullback _ _))
  intro x ρ₀ δ hconj hirred R _ _ _ _ reduce ρuniv hR
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  have := forall_finite_finiteEtaleFiberFunctor_obj
    (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
  have hbc : IsPullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))) :=
    IsPullback.of_hasPullback _ _
  have hNn := normal_range_etaleFundamentalGroupMap_of_isPullback_isAlgClosed k kbar f _ _ hbc x
  refine ⟨moduleFinite_of_isUniversalFixedDeterminantDeformation_of_normal k kbar p ℓ n hℓp hn X
    f _ _ _ hbc x ρ₀ δ hconj hirred hNn R reduce ρuniv hR, ?_⟩
  refine flat_of_isUniversalFixedDeterminantDeformation_of_vanishesTwo k kbar p ℓ n hℓp hn X f x
    ρ₀ δ hconj hirred R reduce ρuniv hR ?_
  have := isCurve_pullback_snd k kbar f
  by_cases hg : genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) = 0
  · have := subsingleton_etaleFundamentalGroup_of_genus_eq_zero kbar _ hg x
    exact vanishesTwo_of_subsingleton _ _
  · exact vanishesTwo_adZero_of_one_le_genus k kbar p ℓ n hℓp hn X f x ρ₀ hirred
      (Nat.one_le_iff_ne_zero.2 hg)

end AlgebraicGeometry

end
