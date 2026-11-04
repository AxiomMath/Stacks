module

public import StacksFrontier.Deformation.FlatAlgebraLiftHenselization
public import StacksFrontier.Deformation.FlatAlgebraLiftLocalizationRelative
public import StacksFrontier.Deformation.SquareZero.ConormalCokernelBaseChange
public import StacksFrontier.Deformation.SquareZero.ConormalTorsion
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleTorsion

/-!
# Stacks 0DZB: the forward implication

`StacksFrontier.Deformation.FlatAlgebraLiftHenselization` proves Stacks 0DZB — flat lifts of a
finite type flat `A`-algebra `B` to `A'` exist exactly when flat lifts of the henselization `Bʰ`
of the pair `(B, 𝔟)` do — from the hypothesis
`Deformation.FlatModuleLiftBaseChangeStatement`, Stacks 0DZ2 quantified over every surjection
`A' → A`. This file does for Stacks 0DZB what
`StacksFrontier.Deformation.FlatAlgebraLiftCompletionRelative` does for Stacks 0DZ3 and
`StacksFrontier.Deformation.FlatAlgebraLiftLocalizationRelative` for Stacks 0DZ7.

**The forward implication is unconditional.** The henselization of a flat lift is a flat lift of
the henselization: `A' → B' → (B')ʰ` with the second map flat by Stacks 0AGU, and the base change
identified by Stacks 0DYE.
`Deformation.hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective` assumes
nothing beyond surjectivity of `A' → A` — not Noetherianness, not finite type, not flatness of
`B` over `A`, not nilpotence of the kernel and not the syntomic hypothesis.

## Main results

* `Deformation.hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective`: the forward
  implication of Stacks 0DZB, unconditionally.
* `Deformation.syntomic_quotient_X_sq`, `Deformation.not_formallySmooth_quotient_X_sq`: syntomy
  does not imply formal smoothness.

## References

* [Stacks Project, Tag 0DZB](https://stacks.math.columbia.edu/tag/0DZB)
* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
* [Stacks Project, Tag 0DYE](https://stacks.math.columbia.edu/tag/0DYE)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### The first implication, without Stacks 0DZ2 -/

/-- **The henselization of a flat algebra lift is a flat algebra lift of the henselization.**
Let `A' → A` be a surjection of commutative rings, let `B` be an `A`-algebra, let `𝔟 ⊆ B` be an
ideal and let `(Bʰ, 𝔟Bʰ)` be the henselization of the pair `(B, 𝔟)`. If `B` has a flat lift
`B'` to `A'`, then the henselization `C'` of the pair `(B', 𝔟')` at the preimage `𝔟'` of `𝔟` is
a flat lift of `Bʰ` to `A'`.

This is the first implication of Stacks 0DZB, and it carries none of that lemma's hypotheses
beyond surjectivity of `A' → A`: neither Noetherianness, nor finite type, nor flatness of `B`
over `A`, nor nilpotence of the kernel, nor the syntomy hypothesis is used. The proof is the
one the source's first proof gives for this direction. Flatness of `C'` over `A'` is flatness
of `B' → C'`, which is Stacks 0AGU, composed with flatness of `A' → B'`; and the
identification `A ⊗_{A'} C' ≅ Bʰ` is Stacks 0DYE for the surjective — hence integral — map of
pairs `(B', 𝔟') → (B, 𝔟)`, whose equality of vanishing loci is automatic because `𝔟` is the
image of `𝔟'`, composed with the identification of `A ⊗_{A'} C'` with `B ⊗_{B'} C'`: both are
`C'` modulo `ker(A' → A)·C'`, because `ker(B' → B) = ker(A' → A)·B'`. -/
public theorem hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (b : Ideal B)
    (Bh : Type u) [CommRing Bh] [Algebra B Bh] [Algebra A Bh] [IsScalarTower A B Bh]
    (hhens : HenselianPair Bh (b.map (algebraMap B Bh)))
    (huniv : ∀ (D : Type u) (_ : CommRing D) (K : Ideal D), HenselianPair D K →
      ∀ f : B →+* D, b ≤ K.comap f →
        ∃! g : Bh →+* D, g.comp (algebraMap B Bh) = f ∧
          b.map (algebraMap B Bh) ≤ K.comap g) :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A Bh := by
  classical
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  rintro ⟨B', _, _, hflatB', ⟨eB'⟩⟩
  have := hflatB'
  -- the reduction of the lift: a surjection with kernel `ker(A' → A)·B'`
  set rho : B' →ₐ[A'] B :=
    (eB'.restrictScalars A').toAlgHom.comp Algebra.TensorProduct.includeRight
  have hrhosurj : Function.Surjective rho :=
    (eB'.restrictScalars A').surjective.comp (surjective_includeRight A' A B' hsurjA)
  have hrhoker : RingHom.ker rho = (RingHom.ker (algebraMap A' A)).map (algebraMap A' B') :=
    ker_comp_includeRight B B' hsurjA (eB'.restrictScalars A')
  let : Algebra B' B := rho.toRingHom.toAlgebra
  have hsurjP : Function.Surjective (algebraMap B' B) := hrhosurj
  have hkerP : RingHom.ker (algebraMap B' B) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' B') := hrhoker
  have : IsScalarTower A' B' B :=
    IsScalarTower.of_algebraMap_eq fun a' => (rho.commutes a').symm
  have : Algebra.IsIntegral B' B := Algebra.isIntegral_of_surjective hsurjP
  -- the henselization of the pair `(B', 𝔟')`, flat over `A'` by Stacks 0AGU
  set b' : Ideal B' := b.comap (algebraMap B' B) with hb'def
  let C' : Type u := (henselization B' b' : Type u)
  let : Algebra A' C' := ((algebraMap B' C').comp (algebraMap A' B')).toAlgebra
  have : IsScalarTower A' B' C' := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hflatC', -⟩ := flat_henselization_and_bijective_quotientMap B' b' C'
    (henselianPair_henselization B' b') (henselization_universalProperty B' b')
  have : Module.Flat B' C' := hflatC'
  -- the comparison `C' ⊗_{B'} B ≅ Bʰ`, Stacks 0DYE
  let : Algebra B' Bh := ((algebraMap B Bh).comp (algebraMap B' B)).toAlgebra
  have : IsScalarTower B' B Bh := IsScalarTower.of_algebraMap_eq' rfl
  have hb'Bh : b' ≤ (b.map (algebraMap B Bh)).comap (algebraMap B' Bh) := by
    intro x hx
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply B' B Bh]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨g₀, ⟨hg₀1, hg₀2⟩, -⟩ := henselization_universalProperty B' b' Bh inferInstance
    (b.map (algebraMap B Bh)) hhens (algebraMap B' Bh) hb'Bh
  let g : C' →ₐ[B'] Bh := { g₀ with commutes' := fun x => RingHom.congr_fun hg₀1 x }
  have hzero : PrimeSpectrum.zeroLocus (b : Set B) =
      PrimeSpectrum.zeroLocus (b'.map (algebraMap B' B) : Set B) := by
    rw [hb'def, Ideal.map_comap_of_surjective (algebraMap B' B) hsurjP b]
  have hbij := henselization_tensorProduct_bijective_of_isIntegral B' C' B Bh b' b le_rfl
    hzero (henselianPair_henselization B' b') hhens
    (henselization_universalProperty B' b') huniv g hg₀2
  -- the two base changes of `C'` agree, so `A ⊗_{A'} C' ≅ Bʰ`
  let : Algebra A (B ⊗[B'] C') :=
    ((algebraMap B (B ⊗[B'] C')).comp (algebraMap A B)).toAlgebra
  obtain ⟨e1, -⟩ := exists_algEquiv_tensorBaseChange A' A B' B C' hsurjA hsurjP hkerP
    (fun _ => rfl)
  let e2 : (B ⊗[B'] C') ≃ₐ[B'] (C' ⊗[B'] B) := Algebra.TensorProduct.comm B' B C'
  let e3 : (C' ⊗[B'] B) ≃ₐ[B'] Bh := AlgEquiv.ofBijective
    (Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom B' B Bh)
      (fun _ _ => Commute.all _ _)) hbij
  refine ⟨C', inferInstance, inferInstance, Module.Flat.trans A' B' C',
    ⟨AlgEquiv.ofRingEquiv (f := e1.toRingEquiv.trans
      (e2.toRingEquiv.trans e3.toRingEquiv)) fun a => ?_⟩⟩
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
  show e3 (e2 (e1 (algebraMap A (A ⊗[A'] C') a))) = algebraMap A Bh a
  rw [e1.commutes a]
  show e3 (e2 ((algebraMap A B a) ⊗ₜ[B'] (1 : C'))) = algebraMap A Bh a
  rw [show e2 ((algebraMap A B a) ⊗ₜ[B'] (1 : C')) =
    (1 : C') ⊗ₜ[B'] (algebraMap A B a) from Algebra.TensorProduct.comm_tmul _ _ _]
  show Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom B' B Bh)
    (fun _ _ => Commute.all _ _) ((1 : C') ⊗ₜ[B'] (algebraMap A B a)) = algebraMap A Bh a
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  exact (IsScalarTower.algebraMap_apply A B Bh a).symm

/-- **The first implication of Stacks 0DZB at the canonical henselization.** This is
`Deformation.hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective` with its
henselian-pair hypothesis `hhens` and universal property `huniv` discharged by the canonical
construction `henselization B 𝔟`, so it also witnesses that those two hypotheses are
satisfiable. -/
public theorem hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective'
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (b : Ideal B)
    [Algebra A (henselization B b : Type u)]
    [IsScalarTower A B (henselization B b : Type u)] :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A (henselization B b : Type u) :=
  hasFlatAlgebraLift_henselization_of_hasFlatAlgebraLift_of_surjective A' A B hsurjA b
    (henselization B b : Type u) (henselianPair_henselization B b)
    (henselization_universalProperty B b)

/-- **`A[x]/(x²)` is not formally smooth over `A`**, for any nonzero commutative ring `A`. Were
it, the square-zero extension `A[x]/(x³) → A[x]/(x²)` would admit an `A`-algebra section `σ`;
`σ` must send the class of `x` to the class of some `x + a·x²`, whose square is the class of
`x² + x³·(2a + a²x)`, i.e. the class of `x²`, while the class of `x` squares to zero. So `x²`
would lie in `(x³)`, which its coefficient in degree two refutes.

This is what makes the smooth narrowing of `h0DZ2` discussed in the implementation notes a
narrowing to a statement that is *not* refuted: the counterexample's `P'` is
`A'[x]/(x² − t·x − t²·Y)` over `A' = NC[t]/t³`, flat over `A'`, and its base change along
`A' → A = NC` — which is `P` there, the kernel of `P' → P` being generated by that of `A' → A`
— is `A[x]/(x²)`. Formal smoothness is stable under base change, so `P'` is not formally smooth
over `A'`, let alone a polynomial algebra. The identification of `P` with `A[x]/(x²)` is a fact
of the counterexample's own tree, which is not in this module's import closure; what is proved
here is the ring-theoretic half, which is the half that is not bookkeeping. -/
public theorem not_formallySmooth_quotient_X_sq (A : Type u) [CommRing A] [Nontrivial A] :
    ¬ Algebra.FormallySmooth A
      (Polynomial A ⧸ Ideal.span {(Polynomial.X : Polynomial A) ^ 2}) := by
  intro _
  set J2 : Ideal (Polynomial A) := Ideal.span {(Polynomial.X : Polynomial A) ^ 2} with hJ2
  set J3 : Ideal (Polynomial A) := Ideal.span {(Polynomial.X : Polynomial A) ^ 3} with hJ3
  have hmem3 : ∀ c : Polynomial A, Polynomial.X ^ 3 * c ∈ J3 := fun c =>
    (Ideal.mem_span_singleton (y := (Polynomial.X : Polynomial A) ^ 3)).2 ⟨c, rfl⟩
  have hle : J3 ≤ J2 := by
    rw [hJ3, hJ2, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Ideal.mem_span_singleton]
    exact ⟨Polynomial.X, by ring⟩
  -- the square-zero extension `A[x]/(x³) → A[x]/(x²)`
  set I : Ideal (Polynomial A ⧸ J3) := J2.map (Ideal.Quotient.mkₐ A J3) with hI
  have hImem : ∀ z ∈ I, ∃ c : Polynomial A,
      z = Ideal.Quotient.mk J3 (Polynomial.X ^ 2 * c) := by
    intro z hz
    rw [hI, Ideal.mem_map_iff_of_surjective _ (Ideal.Quotient.mkₐ_surjective A J3)] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hp
    exact ⟨c, rfl⟩
  have hI2 : I ^ 2 = ⊥ := by
    rw [pow_two, ← le_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    obtain ⟨c, rfl⟩ := hImem a ha
    obtain ⟨d, rfl⟩ := hImem b hb
    rw [Ideal.mem_bot, ← map_mul]
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [show (Polynomial.X : Polynomial A) ^ 2 * c * (Polynomial.X ^ 2 * d) =
      Polynomial.X ^ 3 * (Polynomial.X * (c * d)) by ring]
    exact hmem3 _
  -- the section formal smoothness would supply
  obtain ⟨σ, hσ⟩ := Algebra.FormallySmooth.exists_lift (R := A)
    (A := Polynomial A ⧸ J2) I ⟨2, hI2⟩
    (DoubleQuot.quotQuotEquivQuotOfLEₐ A hle).symm.toAlgHom
  have hx2 : (Ideal.Quotient.mk J2 (Polynomial.X : Polynomial A)) ^ 2 = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      ((Ideal.mem_span_singleton (y := (Polynomial.X : Polynomial A) ^ 2)).2
        ⟨1, (mul_one _).symm⟩)
  have hu2 : (σ (Ideal.Quotient.mk J2 (Polynomial.X : Polynomial A))) ^ 2 = 0 := by
    rw [← map_pow, hx2, map_zero]
  -- the section reduces to the class of `x`, hence is the class of some `x + a·x²`
  have hred : Ideal.Quotient.mk I (σ (Ideal.Quotient.mk J2 (Polynomial.X : Polynomial A))) =
      Ideal.Quotient.mk I (Ideal.Quotient.mk J3 (Polynomial.X : Polynomial A)) := by
    have hs := AlgHom.congr_fun hσ (Ideal.Quotient.mk J2 (Polynomial.X : Polynomial A))
    rwa [show (DoubleQuot.quotQuotEquivQuotOfLEₐ A hle).symm.toAlgHom
        (Ideal.Quotient.mk J2 (Polynomial.X : Polynomial A)) =
        (DoubleQuot.quotQuotEquivQuotOfLE hle).symm
          (Ideal.Quotient.mk J2 (Polynomial.X : Polynomial A)) from rfl,
      DoubleQuot.quotQuotEquivQuotOfLE_symm_mk] at hs
  have hdiff : σ (Ideal.Quotient.mk J2 (Polynomial.X : Polynomial A)) -
      Ideal.Quotient.mk J3 (Polynomial.X : Polynomial A) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hred, sub_self]
  obtain ⟨c, hc⟩ := hImem _ hdiff
  have hσval : σ (Ideal.Quotient.mk J2 (Polynomial.X : Polynomial A)) =
      Ideal.Quotient.mk J3 ((Polynomial.X : Polynomial A) + Polynomial.X ^ 2 * c) := by
    rw [map_add, ← hc]
    ring
  -- squaring it puts `x²` in `(x³)`, which degree two refutes
  have hsq : ((Polynomial.X : Polynomial A) + Polynomial.X ^ 2 * c) ^ 2 ∈ J3 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← hσval, hu2]
  have hX2 : (Polynomial.X : Polynomial A) ^ 2 ∈ J3 := by
    rw [show (Polynomial.X : Polynomial A) ^ 2 =
      ((Polynomial.X : Polynomial A) + Polynomial.X ^ 2 * c) ^ 2 -
        Polynomial.X ^ 3 * (2 * c + Polynomial.X * c ^ 2) by ring]
    exact Ideal.sub_mem _ hsq (hmem3 _)
  rw [hJ3, Ideal.mem_span_singleton] at hX2
  obtain ⟨q, hq⟩ := hX2
  have hc := congrArg (fun p : Polynomial A => Polynomial.coeff p 2) hq
  simp only [Polynomial.coeff_X_pow, mul_comm ((Polynomial.X : Polynomial A) ^ 3) q,
    Polynomial.coeff_mul_X_pow'] at hc
  norm_num at hc

/-- **`A[x]/(x²)` is syntomic over `A`**, for every commutative ring `A`.

Together with `Deformation.not_formallySmooth_quotient_X_sq` above this is the witness separating
Stacks 0DZB's hypothesis from the one its converse needs: `A → A[x]/(x²)` is syntomic and not
formally smooth, so the `𝔟`-power torsion of `Ext¹_B(NL_{B/A}, -)` — which by
`Deformation.surjective_precomp_cotangentComplex_iff_formallySmooth` below *is* smoothness off
`V(𝔟)` — does not follow from syntomy.

The proof is Stacks 00SW. One variable and one relation present `A[x]/(x²)`, and that
presentation is square, so `Algebra.IsRelativeGlobalCompleteIntersection.of_card_eq` applies as
soon as the algebra is quasi-finite, which it is because it is finite as a module —
`Polynomial.Monic.finite_quotient` at the monic `x²`. Then
`Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection` is Stacks 00SW. In particular the
fibre dimension side-condition of `IsLocalCompleteIntersection` is discharged rather than cited:
a square presentation of a quasi-finite algebra has artinian fibres, so every nonempty fibre has
Krull dimension `0 = 1 − 1`. -/
public theorem syntomic_quotient_X_sq (A : Type u) [CommRing A] :
    Algebra.Syntomic A (Polynomial A ⧸ Ideal.span {(Polynomial.X : Polynomial A) ^ 2}) := by
  have hfin : Module.Finite A
      (Polynomial A ⧸ Ideal.span {(Polynomial.X : Polynomial A) ^ 2}) :=
    (Polynomial.monic_X_pow 2).finite_quotient
  let e : MvPolynomial (Fin 1) A ≃ₐ[A] Polynomial A := MvPolynomial.uniqueAlgEquiv A (Fin 1)
  have hgci : Algebra.IsRelativeGlobalCompleteIntersection A
      (Polynomial A ⧸ Ideal.span {(Polynomial.X : Polynomial A) ^ 2}) :=
    Algebra.IsRelativeGlobalCompleteIntersection.of_card_eq
      ((Algebra.Presentation.naive
            (v := fun _ : Fin 1 => e.symm ((Polynomial.X : Polynomial A) ^ 2))).ofAlgEquiv
        (Ideal.quotientEquivAlg _ (Ideal.span {(Polynomial.X : Polynomial A) ^ 2}) e
          (by rw [Ideal.map_span]; simp [e]))) rfl
  exact Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection _ _

end Deformation

end
