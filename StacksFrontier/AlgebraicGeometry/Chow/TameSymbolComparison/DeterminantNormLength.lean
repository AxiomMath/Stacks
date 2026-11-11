module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison.Invariance
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.DeterminantNorm
public import Mathlib.RingTheory.LocalRing.Length

/-!
# The residue-field determinant of a multiplication is a power of a norm

Let `R → R'` be a local homomorphism of local rings with finite residue-field extension
`κ(R') / κ(R)`, let `M` be an `R'`-module of finite length, regarded as an `R`-module, and let
`u` be a unit of `R'`. The residue-field determinant of Stacks 02PN of multiplication by `u` on
`M`, taken over `R`, is

`det_{κ(R)}(u : M → M) = Norm_{κ(R')/κ(R)}(ū) ^ length_{R'}(M)`

(`Stacks.Chow.determinantAutomorphism_eq_norm_pow_length`). This is the identity the source
quotes as More on Algebra, Lemma 0GSZ in the proof of Stacks 0EAT, here for the determinant
`AlgebraicGeometry.determinantAutomorphism` of the determinant functor, the one in which the
symbols of Stacks 02PZ are written.

The proof is by induction on a composition series of `M` over `R'`: the determinant is
multiplicative in short exact sequences (Stacks 02PO applied to the periodic complexes
`(u, 0)`, with Stacks 02PN identifying their periodic determinants with the determinants of
`u`), and on a simple module `M ≅ κ(R')` it is the norm, by
`Stacks.Chow.determinantAutomorphism_eq_norm`.

## Main results

* `Stacks.Chow.determinantAutomorphism_eq_of_linearEquiv` — conjugation invariance.
* `Stacks.Chow.determinantAutomorphism_eq_mul_of_exact` — multiplicativity in a short exact
  sequence.
* `Stacks.Chow.determinantAutomorphism_eq_norm_pow_length` — the formula above.

## References

* [Stacks Project, Tag 0GSZ](https://stacks.math.columbia.edu/tag/0GSZ)
* [Stacks Project, Tag 02PN](https://stacks.math.columbia.edu/tag/02PN)
* [Stacks Project, Tag 02PO](https://stacks.math.columbia.edu/tag/02PO)
-/

@[expose] public noncomputable section

open IsLocalRing Module.FiniteLength AlgebraicGeometry

universe u v w w₁ w₂ w₃

namespace Stacks.Chow

section General

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **The residue-field determinant is invariant under conjugation** by a linear
equivalence. -/
theorem determinantAutomorphism_eq_of_linearEquiv {M : Type w₁} {N : Type w₂}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] M) (f : N ≃ₗ[R] N) (φ : M ≃ₗ[R] N) (h : ∀ x, φ (e x) = f (φ x))
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) :
    determinantAutomorphism e hM = determinantAutomorphism f hN := by
  rw [← periodicDeterminant_equiv_zero e hM, ← periodicDeterminant_equiv_zero f hN]
  exact periodicDeterminant_eq_of_linearEquiv _ _ _ _ _ _ _ _ φ
    (LinearMap.ext h) (by ext; simp) hM hN

/-- **The residue-field determinant is multiplicative in a short exact sequence** of modules
of finite length carrying compatible automorphisms. -/
theorem determinantAutomorphism_eq_mul_of_exact {M₁ : Type w₁} {M₂ : Type w₂} {M₃ : Type w₃}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (e₁ : M₁ ≃ₗ[R] M₁) (e₂ : M₂ ≃ₗ[R] M₂) (e₃ : M₃ ≃ₗ[R] M₃)
    (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (h₁ : ∀ x, e₂ (i x) = i (e₁ x)) (h₃ : ∀ x, e₃ (p x) = p (e₂ x))
    (hM₁ : IsFiniteLength R M₁) (hM₂ : IsFiniteLength R M₂) (hM₃ : IsFiniteLength R M₃) :
    determinantAutomorphism e₂ hM₂ =
      determinantAutomorphism e₁ hM₁ * determinantAutomorphism e₃ hM₃ := by
  rw [← periodicDeterminant_equiv_zero e₁ hM₁, ← periodicDeterminant_equiv_zero e₂ hM₂,
    ← periodicDeterminant_equiv_zero e₃ hM₃]
  exact periodicDeterminant_short_exact _ _ _ _ _ _ i p hi hp hip (LinearMap.ext h₁)
    (by ext; simp) (LinearMap.ext h₃) (by ext; simp) _ _ _ _ _ _ hM₁ hM₂ hM₃

/-- The residue-field determinant of an automorphism of a zero module is `1`. -/
theorem determinantAutomorphism_of_subsingleton {M : Type w₁} [AddCommGroup M] [Module R M]
    [Subsingleton M] (e : M ≃ₗ[R] M) (hM : IsFiniteLength R M) :
    determinantAutomorphism e hM = 1 := by
  have h := determinantAutomorphism_eq_mul_of_exact e e e LinearMap.id 0
    (fun _ _ h ↦ h) (fun x ↦ ⟨0, Subsingleton.elim _ _⟩)
    (fun x ↦ ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ Subsingleton.elim _ _⟩)
    (fun _ ↦ rfl) (fun _ ↦ Subsingleton.elim _ _) hM hM hM
  exact left_eq_mul.mp h

end General

section Norm

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
  [Module.Finite (ResidueField R) (ResidueField R')]

/-- An `R'`-module of finite length has finite length over `R`, the residue-field extension being
finite. -/
theorem isFiniteLength_restrictScalars_of_finite_residueField (M : Type w) [AddCommGroup M]
    [Module R M] [Module R' M] [IsScalarTower R R' M] (hM : IsFiniteLength R' M) :
    IsFiniteLength R M :=
  Module.length_ne_top_iff.mp <| by
    rw [IsLocalRing.length_restrictScalars R R' M]
    exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM) (by
      rw [Module.length_eq_finrank]
      exact ENat.natCast_ne_top _)

/-- A simple module over a local ring is isomorphic to its residue field. -/
private theorem nonempty_linearEquiv_residueField_of_isSimpleModule' (M : Type w) [AddCommGroup M]
    [Module R' M] [IsSimpleModule R' M] : Nonempty (M ≃ₗ[R'] ResidueField R') := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R' M›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

private theorem determinantAutomorphism_eq_norm_pow_length_aux (a : R'ˣ)
    (M : Type w) [AddCommGroup M] [Module R' M] (hM' : IsFiniteLength R' M) :
    letI : Module R M := Module.compHom M (algebraMap R R')
    letI : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    ∀ (e : M ≃ₗ[R] M) (_ : ∀ x, e x = (a : R') • x) (hM : IsFiniteLength R M),
      (determinantAutomorphism e hM : ResidueField R) =
        Algebra.norm (ResidueField R) (residue R' (a : R')) ^ (Module.length R' M).toNat := by
  induction hM' with
  | @of_subsingleton M _ _ hsub =>
      let : Module R M := Module.compHom M (algebraMap R R')
      intro e _ hM
      rw [determinantAutomorphism_of_subsingleton, Module.length_eq_zero]
      simp
  | @of_simple_quotient M _ _ N _ hN ih =>
      let : Module R M := Module.compHom M (algebraMap R R')
      let : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      let : Module R N := Module.compHom N (algebraMap R R')
      let : IsScalarTower R R' N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      let Q := M ⧸ N
      let : Module R Q := Module.compHom Q (algebraMap R R')
      let : IsScalarTower R R' Q := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      intro e he hM
      have hQ' : IsFiniteLength R' Q :=
        isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
      have hN₀ := isFiniteLength_restrictScalars_of_finite_residueField R R' N hN
      have hQ₀ := isFiniteLength_restrictScalars_of_finite_residueField R R' Q hQ'
      let eN : N ≃ₗ[R] N := (LinearEquiv.smulOfUnit a).restrictScalars R
      let eQ : Q ≃ₗ[R] Q := (LinearEquiv.smulOfUnit a).restrictScalars R
      have hmul := determinantAutomorphism_eq_mul_of_exact eN e eQ
        (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R) N.subtype_injective
        N.mkQ_surjective (LinearMap.exact_iff.mpr (by
          rw [LinearMap.ker_restrictScalars, LinearMap.range_restrictScalars]
          congr 1
          rw [N.ker_mkQ]
          exact (Submodule.range_subtype N).symm))
        (fun x ↦ by rw [he]; rfl) (fun x ↦ by rw [he]; rfl) hN₀ hM hQ₀
      rw [hmul, Units.val_mul, ih eN (fun _ ↦ rfl) hN₀]
      let K := ResidueField R'
      obtain ⟨φ⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule' R' Q
      have : IsSimpleModule R' K := IsSimpleModule.congr φ.symm
      have hK : IsFiniteLength R K := isFiniteLength_restrictScalars_of_finite_residueField R R' K
        (Module.length_ne_top_iff.mp (by
          rw [Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R' K)]
          simp))
      let eK : K ≃ₗ[R] K :=
        (LinearEquiv.smulOfUnit (Units.map (residue R').toMonoidHom a)).restrictScalars R
      have hconj := determinantAutomorphism_eq_of_linearEquiv eQ eK (φ.restrictScalars R)
        (fun x ↦ by
          change φ ((a : R') • x) = (residue R' (a : R')) • φ x
          rw [φ.map_smul, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]
          rfl) hQ₀ hK
      have hnorm := determinantAutomorphism_eq_norm (R := R) (L := K) eK hK
        (residue R' (a : R')) (fun x ↦ rfl)
      rw [hconj, hnorm,
        Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective
          N.mkQ_surjective (LinearMap.exact_iff.mpr (by rw [N.ker_mkQ, Submodule.range_subtype])),
        Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R' Q), ENat.toNat_add]
      all_goals simp [Module.length_ne_top_iff.mpr hN, pow_succ]

/-- **Stacks 0GSZ for the residue-field determinant of Stacks 02PN.** For a local homomorphism
`R → R'` with finite residue-field extension, an `R'`-module `M` of finite length and a unit `a`
of `R'`, the determinant over `κ(R)` of multiplication by `a` on `M` is
`Norm_{κ(R')/κ(R)}(ā) ^ length_{R'}(M)`. -/
theorem determinantAutomorphism_eq_norm_pow_length (a : R'ˣ)
    (M : Type w) [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
    (hM' : IsFiniteLength R' M) (e : M ≃ₗ[R] M) (he : ∀ x, e x = (a : R') • x)
    (hM : IsFiniteLength R M) :
    (determinantAutomorphism e hM : ResidueField R) =
      Algebra.norm (ResidueField R) (residue R' (a : R')) ^ (Module.length R' M).toNat := by
  have hmodule : (inferInstance : Module R M) = Module.compHom M (algebraMap R R') := by
    apply Module.ext'
    intro r x
    exact (IsScalarTower.algebraMap_smul R' r x).symm
  cases hmodule
  exact determinantAutomorphism_eq_norm_pow_length_aux R R' a M hM' e he hM

end Norm

end Stacks.Chow

end
