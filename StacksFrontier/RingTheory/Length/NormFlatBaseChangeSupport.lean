module

public import StacksFrontier.RingTheory.Length.NormFlatBaseChange
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition

/-!
# The maximal ideals of `S ⊗_A B` containing `π`

Let `A → S` be a homomorphism of local rings, let `B` be a local `A`-algebra along a local
homomorphism with `κ(B) / κ(A)` finite, and let `π ∈ B` with `B / πB` of finite length. Then
`S ⊗_A B / π` is a finite `S`-algebra, so the maximal ideals `𝔮` of `T = S ⊗_A B` containing `π`
are finite in number, lie over the maximal ideal of `S`, and have residue fields `κ(T_𝔮)` finite
over `κ(S)`. These are the instances that
`Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length_support` takes, so the identity
(Stacks 0GU1) holds without them.

## Main results

* `Stacks.Length.finite_tensorSupport`, `Stacks.Length.isLocalHom_algebraMap_tensorSupport`,
  `Stacks.Length.finite_residueField_tensorSupport` — the three facts above.
* `Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length_of_isFiniteLength` — the identity
  (Stacks 0GU1) for a flat local homomorphism `A → S`, with the product over the maximal ideals of
  `T` containing `π`.

## References

* [Stacks Project, Tag 0GU1](https://stacks.math.columbia.edu/tag/0GU1)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w

namespace Stacks.Length

section TensorSupport

variable {A : Type u} {S : Type v} {B : Type w} [CommRing A] [CommRing S] [CommRing B]
  [Algebra A S] [Algebra A B] {π : B}

/-- The maximal ideal of `S ⊗_A B / π` under a maximal ideal of `S ⊗_A B` containing `π`. -/
private theorem isMaximal_map_tensorSupport (r : tensorSupport A S π) :
    (Ideal.map (Ideal.Quotient.mk
      (Ideal.map (Algebra.TensorProduct.includeRight (A := S)) (Ideal.span {π})))
      r.1.asIdeal).IsMaximal := by
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
  rw [Ideal.mk_ker]
  exact Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr r.2))

/-- A maximal ideal of `S ⊗_A B` containing `π` is the preimage of its image in
`S ⊗_A B / π`. -/
private theorem comap_map_tensorSupport (r : tensorSupport A S π) :
    (Ideal.map (Ideal.Quotient.mk
      (Ideal.map (Algebra.TensorProduct.includeRight (A := S)) (Ideal.span {π})))
      r.1.asIdeal).comap (Ideal.Quotient.mk _) = r.1.asIdeal := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left]
  exact Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr r.2))

variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
  [Module.Finite (ResidueField A) (ResidueField B)]
  (hM : IsFiniteLength B (B ⧸ Ideal.span {π}))

include hM

/-- `S ⊗_A B / π` is a finite `S`-algebra when `B / πB` has finite length. -/
private theorem finite_tensor_quotient :
    Module.Finite S (S ⊗[A] B ⧸
      Ideal.map (Algebra.TensorProduct.includeRight (A := S)) (Ideal.span {π})) := by
  have hMA : IsFiniteLength A (B ⧸ Ideal.span {π}) :=
    isFiniteLength_restrictScalars_of_finite_residueField A B (B ⧸ Ideal.span {π}) hM
  have : IsNoetherian A (B ⧸ Ideal.span {π}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hMA).1
  exact Module.Finite.equiv
    (Algebra.TensorProduct.tensorQuotientEquiv (R := A) S B S (Ideal.span {π})).toLinearEquiv

variable [IsLocalRing S]

/-- The maximal ideals of `S ⊗_A B` containing `π` are finite in number. -/
theorem finite_tensorSupport : Finite (tensorSupport A S π) := by
  have := finite_tensor_quotient (A := A) (S := S) hM
  have := finite_maximalSpectrum (A := S)
    (B := S ⊗[A] B ⧸ Ideal.map (Algebra.TensorProduct.includeRight (A := S)) (Ideal.span {π}))
  exact Finite.of_injective
    (fun r : tensorSupport A S π => (⟨_, isMaximal_map_tensorSupport r⟩ :
      MaximalSpectrum (S ⊗[A] B ⧸
        Ideal.map (Algebra.TensorProduct.includeRight (A := S)) (Ideal.span {π}))))
    fun r r' h => Subtype.ext <| MaximalSpectrum.ext <| by
      have h' := congrArg MaximalSpectrum.asIdeal h
      dsimp only at h'
      rw [← comap_map_tensorSupport r, ← comap_map_tensorSupport r', h']

/-- A maximal ideal of `S ⊗_A B` containing `π` lies over the maximal ideal of `S`. -/
theorem comap_tensorSupport_eq_maximalIdeal (r : tensorSupport A S π) :
    r.1.asIdeal.comap (algebraMap S (S ⊗[A] B)) = maximalIdeal S := by
  have := finite_tensor_quotient (A := A) (S := S) hM
  have h := comap_asIdeal_eq_maximalIdeal (A := S)
    (⟨_, isMaximal_map_tensorSupport r⟩ : MaximalSpectrum (S ⊗[A] B ⧸
      Ideal.map (Algebra.TensorProduct.includeRight (A := S)) (Ideal.span {π})))
  rwa [IsScalarTower.algebraMap_eq S (S ⊗[A] B), ← Ideal.comap_comap, Ideal.Quotient.algebraMap_eq,
    comap_map_tensorSupport r] at h

/-- At a maximal ideal `𝔮` of `S ⊗_A B` containing `π`, the map `S → (S ⊗_A B)_𝔮` is local. -/
theorem isLocalHom_algebraMap_tensorSupport (r : tensorSupport A S π) :
    IsLocalHom (algebraMap S (Localization.AtPrime r.1.asIdeal)) := by
  apply ((local_hom_TFAE (algebraMap S (Localization.AtPrime r.1.asIdeal))).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq S (S ⊗[A] B) (Localization.AtPrime r.1.asIdeal),
    ← Ideal.comap_comap, show Ideal.comap (algebraMap (S ⊗[A] B) (Localization.AtPrime r.1.asIdeal))
      (maximalIdeal (Localization.AtPrime r.1.asIdeal)) = r.1.asIdeal from
      IsLocalization.AtPrime.under_maximalIdeal _ _, comap_tensorSupport_eq_maximalIdeal hM r]

/-- At a maximal ideal `𝔮` of `S ⊗_A B` containing `π`, the residue field of `(S ⊗_A B)_𝔮` is a
finite extension of `κ(S)`. -/
theorem finite_residueField_tensorSupport (r : tensorSupport A S π) :
    letI := isLocalHom_algebraMap_tensorSupport hM r
    Module.Finite (ResidueField S) (ResidueField (Localization.AtPrime r.1.asIdeal)) := by
  have := isLocalHom_algebraMap_tensorSupport hM r
  have := finite_tensor_quotient (A := A) (S := S) hM
  let I := Ideal.map (Algebra.TensorProduct.includeRight (A := S) (R := A) (B := B))
    (Ideal.span {π})
  have hI : I ≤ RingHom.ker (algebraMap (S ⊗[A] B) r.1.asIdeal.ResidueField) := by
    rw [Ideal.ker_algebraMap_residueField]
    exact Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr r.2))
  let f := Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom S (S ⊗[A] B)
    r.1.asIdeal.ResidueField) hI
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective r.1.asIdeal y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  have : Module.Finite S (ResidueField (Localization.AtPrime r.1.asIdeal)) :=
    Module.Finite.of_surjective f.toLinearMap hf
  exact Module.Finite.of_restrictScalars_finite S _ _

end TensorSupport

/-- **The identity (0GU1) in the proof of Stacks 0EPG.** Let `A → S` be a flat local
homomorphism of local rings with `m = length_S(S / 𝔪_A S)`, let `B` be a local `A`-algebra along a
local homomorphism with `κ(B) / κ(A)` finite (for instance the localization `B_𝔪ⱼ` of a finite
`A`-algebra at a maximal ideal), and let `π`, `u ∈ B` with `B / πB` of finite length. Then,
writing `T = S ⊗_A B`,

`(Norm_{κ(B)/κ(A)}(ū) ^ length_B(B / πB)) ^ m
  = ∏_𝔮 Norm_{κ(T_𝔮)/κ(S)}(ū) ^ length_{T_𝔮}(T_𝔮 / πT_𝔮)`

in `κ(S)`, the product running over the maximal ideals `𝔮` of `T` containing `π`. These are
finite in number, lie over the maximal ideal of `S` and have residue fields finite over `κ(S)`
(`Stacks.Length.finite_tensorSupport`, `Stacks.Length.isLocalHom_algebraMap_tensorSupport`,
`Stacks.Length.finite_residueField_tensorSupport`). -/
@[stacks 0GU1 "with `B` a local `A`-algebra standing for `B_j` and `B'_{j,l}` the local rings of
`A' ⊗_A B_j` at its maximal ideals containing `π_j`; at a maximal ideal of `B'` over `𝔪_j` not
containing `π_j` the factor is `1`"]
theorem map_norm_pow_length_eq_prod_norm_pow_length_of_isFiniteLength
    {A : Type u} {S : Type v} {B : Type w}
    [CommRing A] [CommRing S] [CommRing B]
    [IsLocalRing A] [IsLocalRing S] [IsLocalRing B]
    [Algebra A S] [Algebra A B] [IsLocalHom (algebraMap A S)]
    [IsLocalHom (algebraMap A B)] [Module.Flat A S]
    [Module.Finite (ResidueField A) (ResidueField B)]
    (π u : B) (hM : IsFiniteLength B (B ⧸ Ideal.span {π}))
    {m : ℕ} (hm : Module.length S (S ⧸ extendedMaximalIdeal A S) = m) :
    letI := @Fintype.ofFinite _ (finite_tensorSupport (A := A) (S := S) hM)
    ResidueField.map (algebraMap A S)
      ((Algebra.norm (ResidueField A) (residue B u) ^
        (Module.length B (B ⧸ Ideal.span {π})).toNat) ^ m) =
      ∏ r : tensorSupport A S π,
        letI := isLocalHom_algebraMap_tensorSupport hM r
        Algebra.norm (ResidueField S)
          (residue (Localization.AtPrime r.1.asIdeal)
            ((algebraMap (S ⊗[A] B) (Localization.AtPrime r.1.asIdeal))
              (Algebra.TensorProduct.includeRight u))) ^
            (Module.length (Localization.AtPrime r.1.asIdeal)
            (Localization.AtPrime r.1.asIdeal ⧸
              Ideal.span {((algebraMap (S ⊗[A] B) (Localization.AtPrime r.1.asIdeal))
                (Algebra.TensorProduct.includeRight π))})).toNat := by
  let := @Fintype.ofFinite _ (finite_tensorSupport (A := A) (S := S) hM)
  have := fun r => isLocalHom_algebraMap_tensorSupport (A := A) (S := S) hM r
  have := fun r => finite_residueField_tensorSupport (A := A) (S := S) hM r
  exact map_norm_pow_length_eq_prod_norm_pow_length_support π u hM hm

end Stacks.Length

end
