module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.RingTheory.NoetherNormalization

/-!
# A dense affine open fibred in curves over affine space

Let `k` be a field and `X` a scheme of finite type over `k` of dimension at most `d + 1`. Then
there is a dense affine open `U = Spec A` of `X` together with a morphism `g : U → 𝔸^d_k` over `k`
all of whose fibres have dimension at most one.

## Main results

* `Stacks.NoetherFibration.ringKrullDim_tensorProduct_le_one`: if `S` is integral over `R[b]` then
  `dim (K ⊗_R S) ≤ 1` for every field `K` over `R`.
* `Stacks.NoetherFibration.exists_eval₂RingHom_isIntegral`: a finitely generated `k`-algebra of
  dimension at most `d + 1` is integral over `R[b]` for some `k`-algebra map
  `R = k[X_0, …, X_{d-1}] → A` and some `b ∈ A`.
* `AlgebraicGeometry.exists_dense_isOpenImmersion_fiber_le_one`: the dense affine open fibred in
  curves over `𝔸^d_k = Spec k[X_0, …, X_{d-1}]`.

## References

* [Stacks Project, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.NoetherFibration

/-- **Fibres of relative dimension at most one.** If `S` is integral over `R[b]`, the subring
generated over `R` by one element `b`, then for every field `K` over `R` the fibre ring `K ⊗_R S`
has dimension at most one. -/
theorem ringKrullDim_tensorProduct_le_one {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (b : S) (hb : (Polynomial.eval₂RingHom (algebraMap R S) b).IsIntegral)
    (K : Type*) [Field K] [Algebra R K] : ringKrullDim (K ⊗[R] S) ≤ 1 := by
  set c : K ⊗[R] S := 1 ⊗ₜ b with hc
  let A := Algebra.adjoin K {c}
  let c' : A := ⟨c, Algebra.self_mem_adjoin_singleton K c⟩
  have hint : Algebra.IsIntegral A (K ⊗[R] S) := by
    refine ⟨fun t => ?_⟩
    induction t using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul x s =>
      have h1 : IsIntegral A ((1 : K) ⊗ₜ[R] s) := by
        obtain ⟨F, hFm, hF⟩ := hb s
        let ρ : Polynomial R →+* A :=
          Polynomial.eval₂RingHom ((algebraMap K A).comp (algebraMap R K)) c'
        refine ⟨F.map ρ, hFm.map ρ, ?_⟩
        have hcomp : (algebraMap A (K ⊗[R] S)).comp ρ =
            (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := S)).toRingHom.comp
              (Polynomial.eval₂RingHom (algebraMap R S) b) := by
          refine Polynomial.ringHom_ext (fun r => ?_) ?_
          · simp only [RingHom.comp_apply, ρ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
              AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
            rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
              Algebra.TensorProduct.algebraMap_apply']
          · simp [ρ, c', hc]
        have hs : (1 : K) ⊗ₜ[R] s =
            (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := S)).toRingHom s := rfl
        rw [Polynomial.eval₂_map, hcomp, hs, ← Polynomial.hom_eval₂, hF, map_zero]
      have hx : x ⊗ₜ[R] s = algebraMap A (K ⊗[R] S) (algebraMap K A x) * (1 ⊗ₜ s) := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [hx]
      exact (isIntegral_algebraMap).mul h1
    | add _ _ h₁ h₂ => exact h₁.add h₂
  have h1 : ringKrullDim (K ⊗[R] S) ≤ ringKrullDim A :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A (K ⊗[R] S)))
      fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h
  have hsurj : Function.Surjective (Polynomial.aeval (R := K) c') := by
    rintro ⟨t, ht⟩
    have ht' : t ∈ (Polynomial.aeval (R := K) c).range := by
      rwa [← Algebra.adjoin_singleton_eq_range_aeval]
    obtain ⟨p, rfl⟩ := ht'
    exact ⟨p, Subtype.ext (by simp [c', Polynomial.aeval_subalgebra_coe])⟩
  have h2 : ringKrullDim A ≤ ringKrullDim (Polynomial K) :=
    ringKrullDim_le_of_surjective (Polynomial.aeval (R := K) c').toRingHom hsurj
  have h3 : ringKrullDim (Polynomial K) = 1 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]; rfl
  exact h1.trans (h2.trans h3.le)

/-- **Noether normalization, projected to one fewer variable.** A finitely generated algebra `S`
over a field `k` of dimension at most `d + 1` is integral over `R[b]`, for the `k`-algebra map
`R = k[X_0, …, X_{d-1}] → S` sending `X_i` to some `a_i` and some `b ∈ S`. -/
theorem exists_eval₂RingHom_isIntegral (k : Type*) [Field k] (S : Type*) [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (d : ℕ)
    (hS : ringKrullDim S ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (a : Fin d → S) (b : S),
      (Polynomial.eval₂RingHom (MvPolynomial.aeval (R := k) a).toRingHom b).IsIntegral := by
  classical
  rcases subsingleton_or_nontrivial S with h | h
  · refine ⟨0, 0, fun x => ?_⟩
    rw [Subsingleton.elim x 0]
    exact RingHom.isIntegralElem_zero _
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k S).FG)
  obtain ⟨r, y, -, -, hfin, hdim⟩ :=
    exists_finite_inj_aeval_ringKrullDim_eq_of_adjoin_eq_top k t.finite_toSet ht
  have hr : r ≤ d + 1 := by
    rw [hdim] at hS
    exact_mod_cast hS
  let a : Fin d → S := fun i => if h : (i : ℕ) < r then y ⟨i, h⟩ else 0
  let b : S := if h : d < r then y ⟨d, h⟩ else 0
  let θ : MvPolynomial (Fin r) k →+* Polynomial (MvPolynomial (Fin d) k) :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun j =>
      if h : (j : ℕ) < d then Polynomial.C (MvPolynomial.X ⟨j, h⟩) else Polynomial.X
  refine ⟨a, b, RingHom.IsIntegral.tower_top θ _ ?_⟩
  have hθ : (Polynomial.eval₂RingHom (MvPolynomial.aeval (R := k) a).toRingHom b).comp θ =
      (MvPolynomial.aeval y : MvPolynomial (Fin r) k →ₐ[k] S).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp [θ]
    · by_cases hj : (j : ℕ) < d
      · simp [θ, hj, a]
      · have hjd : (j : ℕ) = d := by omega
        have hdr : d < r := hjd ▸ j.2
        have hj' : j = ⟨d, hdr⟩ := Fin.ext hjd
        subst hj'
        simp [θ, b, hdr]
  rw [hθ]
  exact hfin.to_isIntegral

end Stacks.NoetherFibration

namespace AlgebraicGeometry

/-- **A dense affine open fibred in curves over affine space.** Let `X` be a scheme of finite type
over a field `k` of dimension at most `d + 1`. Then there are a dense affine open
`j_U : U = Spec A ⟶ X` and a morphism `g : U ⟶ 𝔸^d_k = Spec k[X_0, …, X_{d-1}]` over `k` all of
whose fibres have dimension at most one. -/
theorem exists_dense_isOpenImmersion_fiber_le_one {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (d : ℕ)
    (hX : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (A : CommRingCat.{u}) (jU : Spec A ⟶ X) (_ : IsOpenImmersion jU)
      (g : Spec A ⟶ Spec (.of (MvPolynomial (Fin d) k))),
      Dense (Set.range jU.base) ∧
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k))) = jU ≫ f ∧
      ∀ y, topologicalKrullDim (g.fiber y) ≤ 1 := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  obtain ⟨V, hV, hdense⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ Dense (V : Set X) := by
    let η : irreducibleComponents X → X := fun Z => Z.2.1.genericPoint
    have hη (Z : irreducibleComponents X) : IsGenericPoint (η Z) Z.1 :=
      Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
    obtain ⟨V, hV, hηV⟩ := exists_affine_open_containing_generic_points
      (fun Z : irreducibleComponents X => Z.1) (fun Z => Z.2) Subtype.val_injective η hη
    refine ⟨V, hV, fun x => ?_⟩
    let Z : irreducibleComponents X :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    have hZ : Z.1 ⊆ closure (V : Set X) := by
      rw [← (hη Z).def]
      exact closure_mono (Set.singleton_subset_iff.mpr (hηV Z))
    exact hZ mem_irreducibleComponent
  let A := Γ(X, V)
  let ψ : CommRingCat.of k ⟶ A := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V (by simp)
  let : Algebra k A := ψ.hom.toAlgebra
  have : Algebra.FiniteType k A := by
    have h1 : (f.appLE ⊤ V (by simp)).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
    exact h1.comp h2
  have hdimA : ringKrullDim A ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (IsHomeomorph.topologicalKrullDim_eq _
        hV.isoSpec.hom.homeomorph.isHomeomorph).symm.le.trans
      ((topologicalKrullDim_subspace_le X V).trans hX)
  obtain ⟨a, b, hb⟩ := Stacks.NoetherFibration.exists_eval₂RingHom_isIntegral k A d hdimA
  let φ : MvPolynomial (Fin d) k →ₐ[k] A := MvPolynomial.aeval a
  refine ⟨A, hV.fromSpec, inferInstance, Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_, ?_⟩
  · rwa [hV.range_fromSpec]
  · rw [← Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV (by simp),
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x
  · intro y
    let : Algebra (MvPolynomial (Fin d) k) A := φ.toRingHom.toAlgebra
    have e := Spec.fiberToSpecResidueFieldIso (MvPolynomial (Fin d) k) A y
    refine (IsHomeomorph.topologicalKrullDim_eq _
      (Arrow.leftFunc.mapIso e).hom.homeomorph.isHomeomorph).le.trans ?_
    have := y.isPrime
    show topologicalKrullDim (PrimeSpectrum (y.asIdeal.Fiber A)) ≤ 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact Stacks.NoetherFibration.ringKrullDim_tensorProduct_le_one b hb _

end AlgebraicGeometry

end
