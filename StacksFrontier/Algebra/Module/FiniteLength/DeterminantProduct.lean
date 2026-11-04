module

public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksFrontier.Algebra.Module.FiniteLength.Determinant

/-!
# Determinants of finite-length endomorphisms on products

Let `R` be a local ring. The determinant `det_R(φ)` of an endomorphism `φ` of a finite-length
`R`-module, built from a stable composition series, is multiplicative in equivariant short exact
sequences (Stacks 0GSY). Consequently it is invariant under equivariant isomorphisms, and it is
multiplicative on finite products: `det_R(∏ φ_i) = ∏ det_R(φ_i)`.

For an `R`-algebra `T` of finite length over `R` (an Artinian ring), `T` is the product of its
localizations at its maximal ideals, so the determinant of multiplication by `x ∈ T` is the
product of the determinants of multiplication by `x` on the localizations `T_𝔫`.

## Main results

* `FiniteLengthEndomorphism.det_eq_of_linearEquiv` — invariance under an intertwining
  isomorphism.
* `FiniteLengthEndomorphism.det_piMap` — multiplicativity on finite products.
* `FiniteLengthEndomorphism.det_lsmul_eq_prod_localization` — the determinant of multiplication
  on a finite-length algebra is the product of the local determinants.

## References

* [Stacks Project, Tag 0GSY](https://stacks.math.columbia.edu/tag/0GSY)
-/

@[expose] public section

universe u v w

namespace FiniteLengthEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **The determinant is invariant under an intertwining isomorphism.** If `e : M ≃ N`
satisfies `e ∘ φ = ψ ∘ e`, then `det_R(φ) = det_R(ψ)`. -/
theorem det_eq_of_linearEquiv {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (φ : Module.End R M) (ψ : Module.End R N) (e : M ≃ₗ[R] N)
    (hφ : e.toLinearMap.comp φ = ψ.comp e.toLinearMap) :
    det R hM φ = det R hN ψ := by
  let g : N →ₗ[R] PUnit.{1} := 0
  have hexact : Function.Exact e.toLinearMap g := by
    rw [LinearMap.exact_iff]
    simp [g]
  have hcomm : g.comp ψ = (0 : Module.End R PUnit.{1}).comp g := by
    ext x
  simpa using (det_exact R M N PUnit.{1} hM hN IsFiniteLength.of_subsingleton φ ψ 0
    e.toLinearMap g e.injective hexact (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩) hφ hcomm).symm

omit [IsLocalRing R] in
/-- The product of two modules of finite length has finite length. -/
theorem isFiniteLength_prod {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hM : IsFiniteLength R M) (hN : IsFiniteLength R N) :
    IsFiniteLength R (M × N) := by
  rw [← Module.length_ne_top_iff, Module.length_prod]
  exact WithTop.add_ne_top.mpr ⟨Module.length_ne_top_iff.mpr hM, Module.length_ne_top_iff.mpr hN⟩

/-- The determinant of a product endomorphism is the product of the determinants. -/
theorem det_prodMap {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (hMN : IsFiniteLength R (M × N)) (φ : Module.End R M) (ψ : Module.End R N) :
    det R hMN (φ.prodMap ψ) = det R hM φ * det R hN ψ := by
  refine det_exact R M (M × N) N hM hMN hN φ (φ.prodMap ψ) ψ (LinearMap.inl R M N)
    (LinearMap.snd R M N) LinearMap.inl_injective .inl_snd LinearMap.snd_surjective ?_ ?_ <;>
    ext x <;> simp

omit [IsLocalRing R] in
/-- A finite product of modules of finite length has finite length. -/
theorem isFiniteLength_pi {ι : Type*} [Finite ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (hM : ∀ i, IsFiniteLength R (M i)) :
    IsFiniteLength R (∀ i, M i) := by
  have : ∀ i, IsNoetherian R (M i) := fun i ↦
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hM i)).1
  have : ∀ i, IsArtinian R (M i) := fun i ↦
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hM i)).2
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- **The determinant is multiplicative on finite products**: for endomorphisms `φ_i` of
finite-length modules `M_i`, `det_R(∏ φ_i) = ∏ det_R(φ_i)`. -/
theorem det_piMap {ι : Type v} [Fintype ι] (M : ι → Type w) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (hM : ∀ i, IsFiniteLength R (M i)) (h : IsFiniteLength R (∀ i, M i))
    (φ : ∀ i, Module.End R (M i)) :
    det R h (LinearMap.piMap φ) = ∏ i, det R (hM i) (φ i) := by
  classical
  revert M
  refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ (M : ι → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (hM : ∀ i, IsFiniteLength R (M i))
    (h : IsFiniteLength R (∀ i, M i)) (φ : ∀ i, Module.End R (M i)),
    det R h (LinearMap.piMap φ) = ∏ i, det R (hM i) (φ i)) ?_ ?_ ?_ ι
  · intro α β _ e IH M _ _ hM h φ
    let : Fintype α := Fintype.ofEquiv β e.symm
    let E := LinearEquiv.piCongrLeft R M e
    have hcomm : E.toLinearMap.comp (LinearMap.piMap fun a ↦ φ (e a)) =
        (LinearMap.piMap φ).comp E.toLinearMap := by
      refine LinearMap.ext fun x ↦ E.symm.injective ?_
      show E.symm (E _) = E.symm _
      rw [LinearEquiv.symm_apply_apply]
      funext a
      show φ (e a) (x a) = φ (e a) ((Equiv.piCongrLeft M e) x (e a))
      rw [Equiv.piCongrLeft_apply_apply]
    have h' : IsFiniteLength R (∀ a, M (e a)) := isFiniteLength_pi _ fun a ↦ hM (e a)
    rw [← det_eq_of_linearEquiv h' h _ _ E hcomm, IH (fun a ↦ M (e a)) (fun a ↦ hM (e a)) h']
    exact Equiv.prod_comp e (fun b ↦ det R (hM b) (φ b))
  · intro M _ _ hM h φ
    have : Subsingleton (∀ i : PEmpty, M i) := ⟨fun x y ↦ funext fun i ↦ PEmpty.elim i⟩
    simp [det, smallValues_subsingleton]
  · intro α _ IH M _ _ hM h φ
    have hRest : IsFiniteLength R (∀ i : α, M (some i)) := isFiniteLength_pi _ fun i ↦ hM _
    let E := LinearEquiv.piOptionEquivProd R (M := M)
    have hcomm : E.toLinearMap.comp (LinearMap.piMap φ) =
        ((φ none).prodMap (LinearMap.piMap fun i ↦ φ (some i))).comp E.toLinearMap := by
      ext x : 1
      rfl
    rw [det_eq_of_linearEquiv h (isFiniteLength_prod (hM none) hRest) _ _ E hcomm,
      det_prodMap (hM none) hRest, IH (fun i ↦ M (some i)) (fun i ↦ hM (some i)) hRest,
      Fintype.prod_option]

/-- An `R`-algebra of finite length over `R` is an Artinian ring. -/
private theorem isArtinianRing_of_isFiniteLength {R : Type u} [CommRing R] {T : Type v}
    [CommRing T] [Algebra R T]
    (hT : IsFiniteLength R T) : IsArtinianRing T :=
  isArtinianRing_iff.mpr
    (isArtinian_of_tower R (isFiniteLength_iff_isNoetherian_isArtinian.mp hT).2)

omit [IsLocalRing R] in
/-- If an `R`-algebra `T` has finite length over `R`, then so does its localization at each
maximal ideal of `T`. -/
theorem isFiniteLength_localization {T : Type v} [CommRing T] [Algebra R T]
    (hT : IsFiniteLength R T) (q : MaximalSpectrum T) :
    IsFiniteLength R (Localization.AtPrime q.asIdeal) := by
  classical
  have := isArtinianRing_of_isFiniteLength hT
  let E := (MaximalSpectrum.toPiLocalizationEquiv T).restrictScalars R
  refine IsFiniteLength.of_surjective (f := (LinearMap.proj q).comp E.toLinearMap) hT
    fun y ↦ ?_
  obtain ⟨z, hz⟩ := E.surjective (Pi.single q y)
  exact ⟨z, by simpa using congr_fun hz q⟩

/-- **The determinant of multiplication on a finite-length algebra is the product of the local
determinants.** For an `R`-algebra `T` of finite length over `R` and `x ∈ T`,
`det_R(x : T → T) = ∏_𝔫 det_R(x : T_𝔫 → T_𝔫)`, the product over the maximal ideals of `T`. -/
theorem det_lsmul_eq_prod_localization {T : Type v} [CommRing T] [Algebra R T]
    [Fintype (MaximalSpectrum T)] (hT : IsFiniteLength R T) (x : T) :
    det R hT ((LinearMap.lsmul T T x).restrictScalars R) =
      ∏ q : MaximalSpectrum T, det R (isFiniteLength_localization hT q)
        ((LinearMap.lsmul (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)
          (algebraMap T (Localization.AtPrime q.asIdeal) x)).restrictScalars R) := by
  have := isArtinianRing_of_isFiniteLength hT
  let L (q : MaximalSpectrum T) := Localization.AtPrime q.asIdeal
  let E : T ≃ₐ[R] (∀ q : MaximalSpectrum T, L q) :=
    (MaximalSpectrum.toPiLocalizationEquiv T).restrictScalars R
  have hcomm : E.toLinearMap.comp ((LinearMap.lsmul T T x).restrictScalars R) =
      (LinearMap.piMap fun q ↦ (LinearMap.lsmul (L q) (L q)
        (algebraMap T (L q) x)).restrictScalars R).comp E.toLinearMap := by
    refine LinearMap.ext fun z ↦ funext fun q ↦ ?_
    show E (x * z) q = algebraMap T (L q) x * E z q
    simp only [E, AlgEquiv.restrictScalars_apply, map_mul, Pi.mul_apply,
      MaximalSpectrum.toPiLocalizationEquiv_apply_apply]
    rfl
  have hPi := isFiniteLength_pi L (isFiniteLength_localization hT)
  exact (det_eq_of_linearEquiv hT hPi _ _ E.toLinearEquiv hcomm).trans (det_piMap L _ hPi _)

end FiniteLengthEndomorphism

namespace FiniteLengthEndomorphism

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The determinant of multiplication is invariant under an isomorphism of algebras. -/
theorem det_lsmul_eq_of_algEquiv {S : Type v} {U : Type w} [CommRing S] [CommRing U]
    [Algebra R S] [Algebra R U] (e : S ≃ₐ[R] U) (s : S) (hS : IsFiniteLength R S)
    (hU : IsFiniteLength R U) :
    det R hS ((LinearMap.lsmul S S s).restrictScalars R) =
      det R hU ((LinearMap.lsmul U U (e s)).restrictScalars R) :=
  det_eq_of_linearEquiv hS hU _ _ e.toLinearEquiv (LinearMap.ext fun z ↦ map_mul e s z)

omit [IsLocalRing R] in
/-- Multiplication by `y` on `C / J`, as a `C`-module, is multiplication by the class of `y` on
the ring `C / J`. -/
theorem lsmul_quotient_restrictScalars {C : Type v} [CommRing C] [Algebra R C] (J : Ideal C)
    (y : C) :
    (LinearMap.lsmul (C ⧸ J) (C ⧸ J) (Ideal.Quotient.mk J y)).restrictScalars R =
      (LinearMap.lsmul C (C ⧸ J) y).restrictScalars R := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-- If an algebra isomorphism `S ≃ C / J` sends `s` to the class of `y`, then multiplication by
`s` on `S` and by `y` on `C / J` have the same determinant. -/
theorem det_lsmul_eq_of_algEquiv_quotient {S : Type v} {C : Type w} [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] {J : Ideal C} (e : S ≃ₐ[R] C ⧸ J) {s : S} {y : C}
    (h : e s = Ideal.Quotient.mk J y) (hS : IsFiniteLength R S)
    (hU : IsFiniteLength R (C ⧸ J)) :
    det R hS ((LinearMap.lsmul S S s).restrictScalars R) =
      det R hU ((LinearMap.lsmul C (C ⧸ J) y).restrictScalars R) := by
  rw [det_lsmul_eq_of_algEquiv e s hS hU, h, lsmul_quotient_restrictScalars]

end FiniteLengthEndomorphism
