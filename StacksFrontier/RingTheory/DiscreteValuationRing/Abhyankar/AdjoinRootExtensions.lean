module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.FiniteFractionFieldExtension

/-!
# Abhyankar's lemma: root extensions of the base

Auxiliary results for Abhyankar's lemma on extensions obtained by adjoining roots: étaleness of
`AdjoinRoot` of separable polynomials and of `X ^ n - u` for units `u`, the reduced tensor product
of fields as a finite product of fields, integral closures in products, and finite separable
extensions in which a given element, in particular the uniformizer, becomes an `n`-th power.

## Main results

* `IsDiscreteValuationRing.exists_tensorProduct_quotNilradical_equiv_pi_fields`: the reduced
  tensor product of two field extensions, one of them finite, is a finite product of fields.

## References

* [The Stacks Project, Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe u v w x y z

open scoped TensorProduct

open Polynomial

private theorem etale_adjoinRoot_of_monic_of_separable
    {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := hs
  let P : StandardEtalePair R :=
    { f := f
      monic_f := hf
      g := 1
      cond := ⟨b, a, 0, by simpa [mul_comm, add_comm] using hab⟩ }
  have hunit : IsUnit (AdjoinRoot.mk f P.g) := by
    change IsUnit (AdjoinRoot.mk f 1)
    simp
  let : IsLocalization.Away (AdjoinRoot.mk f P.g) (AdjoinRoot f) :=
    IsLocalization.away_of_isUnit_of_bijective _ hunit Function.bijective_id
  exact Algebra.Etale.of_equiv
    (P.equivAwayAdjoinRoot.trans
      ((IsLocalization.algEquiv (Submonoid.powers (AdjoinRoot.mk f P.g))
        (Localization.Away (AdjoinRoot.mk f P.g)) (AdjoinRoot f)).restrictScalars R))

private theorem etale_adjoinRoot_X_pow_sub_C_unit
    {R : Type*} [CommRing R] (u : Rˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) :
    Algebra.Etale R (AdjoinRoot (X ^ n - C (u : R))) :=
  etale_adjoinRoot_of_monic_of_separable (monic_X_pow_sub_C _ hn)
    (separable_X_pow_sub_C_unit u hunit)

theorem isUnit_natCast_of_residueChar {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : n ≠ 0)
    (hc : ringChar (IsLocalRing.ResidueField R) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField R)) n) : IsUnit (n : R) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  intro hzero
  have hdvd := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R)
    (ringChar (IsLocalRing.ResidueField R)) n).mp hzero
  rcases hc with hc | hc
  · rw [hc, zero_dvd_iff] at hdvd
    exact hn hdvd
  · have hchar := Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hdvd
    have hz := CharP.cast_eq_zero (IsLocalRing.ResidueField R)
      (ringChar (IsLocalRing.ResidueField R))
    rw [hchar, Nat.cast_one] at hz
    exact one_ne_zero hz

private theorem isIntegrallyClosedIn_tensorProduct_of_smooth
    (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [IsIntegrallyClosedIn R B] [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] B) := by
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
  · exact Algebra.TensorProduct.includeLeft_injective (S := S)
      (IsIntegralClosure.algebraMap_injective R R B)
  · intro x hx
    obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := B)).surjective ⟨x, hx⟩
    have hmem : (TensorProduct.toIntegralClosure R S B z : S ⊗[R] B) ∈
        (⊥ : Subalgebra S (S ⊗[R] B)) := by
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul s b =>
        obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral b.2
        change s ⊗ₜ[R] (b : B) ∈ (⊥ : Subalgebra S (S ⊗[R] B))
        rw [← hr]
        refine ⟨s * algebraMap R S r, ?_⟩
        change (s * algebraMap R S r) ⊗ₜ[R] 1 = s ⊗ₜ[R] algebraMap R B r
        simpa [Algebra.smul_def, mul_comm] using
          (TensorProduct.smul_tmul r s (1 : B))
      | add z w hz hw => simpa only [map_add, AddMemClass.coe_add] using
          Subalgebra.add_mem (⊥ : Subalgebra S (S ⊗[R] B)) hz hw
    rwa [hz] at hmem

private theorem exists_finite_separable_extension_pow_eq
    (K : Type u) [Field K] (u : Kˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      Module.Finite K L ∧ Algebra.IsSeparable K L ∧
        ∃ θ : L, θ ^ n = algebraMap K L (u : K) ∧ Algebra.adjoin K {θ} = ⊤ := by
  let f : K[X] := X ^ n - C (u : K)
  let : Algebra.IsSeparable K f.SplittingField :=
    Algebra.isSeparable_of_separable_splitting_field K f.SplittingField
      (separable_X_pow_sub_C_unit u hunit)
  obtain ⟨θ, hθ⟩ := (Polynomial.SplittingField.splits f).exists_eval_eq_zero (by
    simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)]
    exact_mod_cast hn)
  have hpow : θ ^ n = algebraMap K f.SplittingField (u : K) := by
    simpa [f, sub_eq_zero] using hθ
  refine ⟨(IntermediateField.adjoin K {θ}), inferInstance, inferInstance,
    inferInstance, inferInstance,
    IntermediateField.AdjoinSimple.gen K θ, ?_, ?_⟩
  · apply Subtype.ext
    exact hpow
  · simpa only [IntermediateField.adjoin.powerBasis_gen] using
      (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral θ)).adjoin_gen_eq_top

private theorem exists_integralClosure_equiv_tensorProduct_of_smooth
    (R S B : Type*) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [IsIntegrallyClosedIn R B]
    [Algebra.Smooth R S] [Algebra.IsIntegral R S] :
    ∃ e : S ≃ₐ[R] integralClosure R (S ⊗[R] B),
      ∀ s : S, (e s : S ⊗[R] B) = s ⊗ₜ[R] (1 : B) := by
  let := isIntegrallyClosedIn_tensorProduct_of_smooth R S B
  let : IsIntegralClosure S R (S ⊗[R] B) :=
    IsIntegralClosure.of_isIntegrallyClosedIn
  refine ⟨IsIntegralClosure.equiv R S (S ⊗[R] B) _, ?_⟩
  intro s
  exact IsIntegralClosure.algebraMap_equiv R S (S ⊗[R] B)
    (integralClosure R (S ⊗[R] B)) s

private theorem adjoinRoot_root_X_pow_sub_C_pow {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    AdjoinRoot.root (X ^ n - C a) ^ n = algebraMap R _ a := by
  have h := AdjoinRoot.eval₂_root (X ^ n - C a)
  simpa [sub_eq_zero] using h

private theorem exists_adjoinRoot_X_pow_sub_C_mul_pow_equiv
    {R : Type*} [CommRing R] (a : R) (c : Rˣ) (n : ℕ) :
    ∃ e : AdjoinRoot (X ^ n - C ((c : R) ^ n * a)) ≃ₐ[R]
        AdjoinRoot (X ^ n - C a),
      e (AdjoinRoot.root _) =
        algebraMap R _ (c : R) * AdjoinRoot.root (X ^ n - C a) := by
  let f : R[X] := X ^ n - C ((c : R) ^ n * a)
  let g : R[X] := X ^ n - C a
  let φ : AdjoinRoot f →ₐ[R] AdjoinRoot g :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R _)
      (algebraMap R _ (c : R) * AdjoinRoot.root g) (by
        simp only [f, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, mul_pow]
        rw [adjoinRoot_root_X_pow_sub_C_pow]
        simp [g])
  let ψ : AdjoinRoot g →ₐ[R] AdjoinRoot f :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId R _)
      (algebraMap R _ (↑c⁻¹ : R) * AdjoinRoot.root f) (by
        simp only [g, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, mul_pow]
        rw [adjoinRoot_root_X_pow_sub_C_pow]
        change (algebraMap R (AdjoinRoot f) (↑c⁻¹ : R)) ^ n *
          algebraMap R (AdjoinRoot f) ((c : R) ^ n * a) - algebraMap R _ a = 0
        rw [← map_pow, ← map_mul]
        simp [← mul_assoc, ← mul_pow])
  have hφψ : φ.comp ψ = AlgHom.id R _ := by
    apply AdjoinRoot.algHom_ext
    change φ (ψ (AdjoinRoot.root g)) = AdjoinRoot.root g
    simp only [φ, ψ, AdjoinRoot.liftAlgHom_root, map_mul, AlgHom.commutes]
    rw [← mul_assoc, ← map_mul]
    simp
  have hψφ : ψ.comp φ = AlgHom.id R _ := by
    apply AdjoinRoot.algHom_ext
    change ψ (φ (AdjoinRoot.root f)) = AdjoinRoot.root f
    simp only [φ, ψ, AdjoinRoot.liftAlgHom_root, map_mul, AlgHom.commutes]
    rw [← mul_assoc, ← map_mul]
    simp
  refine ⟨AlgEquiv.ofAlgHom φ ψ hφψ hψφ, ?_⟩
  change φ (AdjoinRoot.root f) = _
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem exists_quotNilradical_algEquiv_pi_fields
    (R : Type u) (K : Type v) [CommRing R] [Nontrivial R] [Field K] [Algebra K R]
    [Module.Finite K R] :
    ∃ (n : ℕ) (E : Fin n → Type (max u w))
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra R (E i))
      (_ : ∀ i, Algebra K (E i)) (_ : ∀ i, IsScalarTower K R (E i))
      (_ : ∀ i, Module.Finite K (E i)),
      0 < n ∧ Nonempty ((R ⧸ nilradical R) ≃ₐ[R] ∀ i, E i) := by
  classical
  let : IsArtinianRing R := isArtinian_of_tower K inferInstance
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let t := (Fintype.equivFin (MaximalSpectrum R)).symm
  let E (i : Fin (Fintype.card (MaximalSpectrum R))) :=
    ULift.{w} (R ⧸ (t i).asIdeal)
  let : ∀ m : MaximalSpectrum R, Field (R ⧸ m.asIdeal) :=
    fun m ↦ Ideal.Quotient.field m.asIdeal
  let : ∀ i, Field (E i) := fun i ↦ inferInstanceAs (Field (ULift (R ⧸ (t i).asIdeal)))
  let : ∀ i, Algebra R (E i) := fun i ↦ inferInstance
  let : ∀ i, Algebra K (E i) := fun i ↦ inferInstance
  let : ∀ i, IsScalarTower K R (E i) := fun i ↦ inferInstance
  let : ∀ i, Module.Finite K (E i) := fun i ↦ inferInstance
  refine ⟨_, E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Fintype.card_pos, ⟨?_⟩⟩
  exact (IsArtinianRing.quotNilradicalEquivPi R).trans
    ((AlgEquiv.piCongrLeft R (fun m : MaximalSpectrum R ↦ R ⧸ m.asIdeal) t).symm.trans
      (AlgEquiv.piCongrRight fun _ ↦ ULift.algEquiv.symm))

theorem exists_tensorProduct_adjoinRoot_equiv
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (f : R[X]) :
    ∃ e : S ⊗[R] AdjoinRoot f ≃ₐ[S] AdjoinRoot (f.map (algebraMap R S)),
      e (1 ⊗ₜ[R] AdjoinRoot.root f) = AdjoinRoot.root (f.map (algebraMap R S)) := by
  let g : (S ⊗[R] R)[X] :=
    f.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom
  have h : g.map (Algebra.TensorProduct.rid R S S) = f.map (algebraMap R S) := by
    dsimp only [g]
    rw [Polynomial.map_map]
    congr 1
    ext r
    simp [Algebra.smul_def]
  let e := (AdjoinRoot.tensorAlgEquiv f g rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R S S) g
      (f.map (algebraMap R S)) (h ▸ Associated.refl _))
  refine ⟨e, ?_⟩
  simp [e, AdjoinRoot.mapAlgEquiv, AdjoinRoot.mapAlgHom, AdjoinRoot.map]

private theorem etale_integralClosure_adjoinRoot_map
    (R K : Type*) [CommRing R] [CommRing K] [Algebra R K]
    [IsIntegrallyClosedIn R K] (f : R[X]) (hf : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (integralClosure R (AdjoinRoot (f.map (algebraMap R K)))) := by
  let : Algebra.Etale R (AdjoinRoot f) := etale_adjoinRoot_of_monic_of_separable hf hs
  let : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  obtain ⟨e, _⟩ := exists_integralClosure_equiv_tensorProduct_of_smooth R (AdjoinRoot f) K
  obtain ⟨t, _⟩ := exists_tensorProduct_adjoinRoot_equiv R K f
  let e' := (Algebra.TensorProduct.comm R (AdjoinRoot f) K).trans (t.restrictScalars R)
  exact Algebra.Etale.of_equiv (e.trans e'.mapIntegralClosure)

private theorem etale_integralClosure_adjoinRoot_X_pow_sub_C
    (R K : Type*) [CommRing R] [CommRing K] [Algebra R K]
    [IsIntegrallyClosedIn R K] (b : Rˣ) (c : Kˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) :
    Algebra.Etale R (integralClosure R
      (AdjoinRoot (X ^ n - C ((c : K) ^ n * algebraMap R K (b : R))))) := by
  let f : R[X] := X ^ n - C (b : R)
  have hf := etale_integralClosure_adjoinRoot_map R K f (monic_X_pow_sub_C _ hn)
    (separable_X_pow_sub_C_unit b hunit)
  let := hf
  have hmap : f.map (algebraMap R K) = X ^ n - C (algebraMap R K (b : R)) := by
    simp [f]
  let e₀ : AdjoinRoot (f.map (algebraMap R K)) ≃ₐ[R]
      AdjoinRoot (X ^ n - C (algebraMap R K (b : R))) :=
    AdjoinRoot.algEquivOfEq R _ _ hmap
  let : Algebra.Etale R (integralClosure R
      (AdjoinRoot (X ^ n - C (algebraMap R K (b : R))))) :=
    Algebra.Etale.of_equiv e₀.mapIntegralClosure
  obtain ⟨e, _⟩ := exists_adjoinRoot_X_pow_sub_C_mul_pow_equiv
    (algebraMap R K (b : R)) c n
  exact Algebra.Etale.of_equiv (e.restrictScalars R).mapIntegralClosure.symm

private theorem isIntegral_pi_iff_of_finite
    (R : Type*) [CommRing R] {ι : Type*} [Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] (x : ∀ i, S i) :
    IsIntegral R x ↔ ∀ i, IsIntegral R (x i) := by
  constructor
  · intro hx i
    exact hx.map (Pi.evalAlgHom R S i)
  · intro hx
    have hp : IsIntegral (ι → R) x := (isIntegral_pi_iff ι (fun _ ↦ R) S x).mpr hx
    exact isIntegral_trans x hp

private theorem exists_integralClosure_pi_equiv
    (R : Type*) [CommRing R] {ι : Type*} [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] :
    ∃ e : integralClosure R (∀ i, S i) ≃ₐ[R] ∀ i, integralClosure R (S i),
      ∀ x i, (e x i : S i) = (x : ∀ i, S i) i := by
  let φ : integralClosure R (∀ i, S i) →ₐ[R] ∀ i, integralClosure R (S i) :=
    { toFun := fun x i ↦ ⟨x.1 i, (isIntegral_pi_iff_of_finite R x.1).mp x.2 i⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  refine ⟨AlgEquiv.ofBijective φ ⟨?_, ?_⟩, fun _ _ ↦ rfl⟩
  · intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro x
    exact ⟨⟨fun i ↦ (x i).1, (isIntegral_pi_iff_of_finite R _).mpr fun i ↦ (x i).2⟩, rfl⟩

theorem exists_integralClosure_hom
    (A B K L : Type*) [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] :
    ∃ f : integralClosure A K →+* integralClosure B L,
      (∀ z : integralClosure A K, ((f z : integralClosure B L) : L) =
        algebraMap K L (z : K)) ∧
      (∀ z : A, f (algebraMap A (integralClosure A K) z) =
        algebraMap B (integralClosure B L) (algebraMap A B z)) := by
  let g := (IsScalarTower.toAlgHom A K L).comp (integralClosure A K).val
  let f : integralClosure A K →ₐ[A] (integralClosure B L).restrictScalars A :=
    g.codRestrict _ fun x ↦ (x.2.map (IsScalarTower.toAlgHom A K L)).tower_top
  refine ⟨f.toRingHom, fun _ ↦ rfl, ?_⟩
  intro z
  apply Subtype.ext
  change algebraMap K L (algebraMap A K z) = algebraMap B L (algebraMap A B z)
  rw [← IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply A B L]

theorem exists_injective_localRingHom
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f)
    (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime] (hpq : q.comap f = p) :
    ∃ φ : Localization.AtPrime p →+* Localization.AtPrime q,
      Function.Injective φ ∧ IsLocalHom φ ∧
        ∀ a, φ (algebraMap A _ a) = algebraMap B _ (f a) := by
  refine ⟨Localization.localRingHom p q f hpq.symm, ?_, inferInstance,
    Localization.localRingHom_to_map p q f hpq.symm⟩
  exact IsLocalization.map_injective_of_injective' p.primeCompl B
    (Localization.AtPrime q) _ (by simp) hf

theorem formallySmoothNAdic_of_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] (I : Ideal S) :
    RingHom.FormallySmoothNAdic.{w} (algebraMap R S) I := by
  intro T _ J hJ f ψ hψ _
  let : Algebra R T := f.toAlgebra
  let ψ' : S →ₐ[R] T ⧸ J :=
    { ψ with commutes' := fun r ↦ RingHom.congr_fun hψ r }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ ψ'
  refine ⟨g.toRingHom, congrArg AlgHom.toRingHom hg, ?_⟩
  ext r
  exact g.commutes r

private theorem formallySmoothNAdic_of_formallySmooth_square
    (A : Type u) (B : Type v) (C : Type w) (D : Type z)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra A B] [Algebra A C] [Algebra B D] [Algebra C D] [Algebra A D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    [IsExtension A B] [IsExtension A C]
    [IsExtension B D] [IsExtension C D]
    [IsExtension A D]
    (hAC : RingHom.FormallySmoothNAdic.{max u w} (algebraMap A C)
      (IsLocalRing.maximalIdeal C))
    (hCD : RingHom.FormallySmoothNAdic.{max w z} (algebraMap C D)
      (IsLocalRing.maximalIdeal D)) :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B)
      (IsLocalRing.maximalIdeal B) :=
  formallySmoothNAdic_tower_bot A B D (formallySmoothNAdic_trans A C D hAC hCD)

/-- For field extensions `L / K` and `K₁ / K` with `K₁` finite over `K`, the reduced ring
`(L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)` is isomorphic as a `K`-algebra to a nonempty finite
product of fields `E i`, each a finite extension of `L` and an extension of `K₁`, such that the
isomorphism is compatible with the maps from `L` and from `K₁`. -/
theorem exists_tensorProduct_quotNilradical_equiv_pi_fields
    (K : Type u) (L : Type v) (K₁ : Type w)
    [Field K] [Field L] [Field K₁] [Algebra K L] [Algebra K K₁]
    [Module.Finite K K₁] :
    ∃ (n : ℕ) (E : Fin n → Type (max v w z))
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra K (E i))
      (_ : ∀ i, Algebra L (E i)) (_ : ∀ i, Algebra K₁ (E i))
      (_ : ∀ i, IsScalarTower K L (E i))
      (_ : ∀ i, IsScalarTower K K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i))
      (decomp : ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] ∀ i, E i),
      0 < n ∧
      (∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
          algebraMap L (E i) l) ∧
      (∀ i (a : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) a)) i =
          algebraMap K₁ (E i) a) := by
  let T := L ⊗[K] K₁
  obtain ⟨n, E, hE, hTE, hLE, htower, hfinite, hn, ⟨e⟩⟩ :=
    exists_quotNilradical_algEquiv_pi_fields.{max v w, v, z} T L
  let := hE
  let := hTE
  let := hLE
  let := htower
  let := hfinite
  let (i : Fin n) : Algebra K (E i) := (algebraMap L (E i)).comp (algebraMap K L) |>.toAlgebra
  let (i : Fin n) : IsScalarTower K L (E i) := .of_algebraMap_eq fun _ ↦ rfl
  let (i : Fin n) : IsScalarTower K T (E i) := .of_algebraMap_eq fun k ↦ by
    rw [IsScalarTower.algebraMap_apply K L T, ← IsScalarTower.algebraMap_apply L T (E i)]
    rfl
  let (i : Fin n) : Algebra K₁ (E i) :=
    ((algebraMap T (E i)).comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
  let (i : Fin n) : IsScalarTower K K₁ (E i) := .of_algebraMap_eq fun k ↦ by
    change algebraMap K (E i) k = algebraMap T (E i)
      (Algebra.TensorProduct.includeRight (algebraMap K K₁ k))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply K T (E i)]
  refine ⟨n, E, hE, inferInstance, hLE, inferInstance, inferInstance, inferInstance,
    hfinite, e.restrictScalars K, hn, ?_, ?_⟩
  · intro i l
    have h := congrFun (e.commutes (algebraMap L T l)) i
    exact h.trans (IsScalarTower.algebraMap_apply L T (E i) l).symm
  · intro i a
    exact congrFun (e.commutes (1 ⊗ₜ[K] a : T)) i

private theorem etale_integralClosure_of_adjoinRoot_equiv
    {R K T : Type*} [CommRing R] [CommRing K] [CommRing T]
    [Algebra R K] [Algebra K T] [Algebra R T] [IsScalarTower R K T]
    [IsIntegrallyClosedIn R K] (b : Rˣ) (c : Kˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R))
    (e : T ≃ₐ[K] AdjoinRoot (X ^ n - C ((c : K) ^ n * algebraMap R K (b : R)))) :
    Algebra.Etale R (integralClosure R T) := by
  let := etale_integralClosure_adjoinRoot_X_pow_sub_C R K b c hn hunit
  exact Algebra.Etale.of_equiv (e.restrictScalars R).mapIntegralClosure.symm

private theorem formallySmooth_integralClosure_of_algEquiv_pi
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    {ι : Type*} [Finite ι] (S : ι → Type*)
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [Algebra.FormallySmooth R (integralClosure R T)]
    (e : T ≃ₐ[R] ∀ i, S i) (i : ι) :
    Algebra.FormallySmooth R (integralClosure R (S i)) := by
  obtain ⟨f, _⟩ := exists_integralClosure_pi_equiv R S
  let := Algebra.FormallySmooth.of_equiv (e.mapIntegralClosure.trans f)
  exact Algebra.FormallySmooth.of_pi (fun i ↦ integralClosure R (S i)) i

private theorem formallySmooth_integralClosure_of_surjective
    {R T S : Type*} [CommRing R] [CommRing T] [Field S]
    [Algebra R T] [Algebra R S] [IsArtinianRing T] [IsReduced T]
    [Algebra.FormallySmooth R (integralClosure R T)]
    (f : T →ₐ[R] S) (hf : Function.Surjective f) :
    Algebra.FormallySmooth R (integralClosure R S) := by
  let m : MaximalSpectrum T := ⟨RingHom.ker f,
    RingHom.ker_isMaximal_of_surjective f hf⟩
  let := formallySmooth_integralClosure_of_algEquiv_pi
    (fun q : MaximalSpectrum T ↦ T ⧸ q.asIdeal)
    ((IsArtinianRing.equivPi T).restrictScalars R) m
  exact Algebra.FormallySmooth.of_equiv
    (Ideal.quotientKerAlgEquivOfSurjective hf).mapIntegralClosure

private theorem isSeparableExtension_of_surjective_base
    (k K L : Type*) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra.IsSeparableExtension k L]
    (h : Function.Surjective (algebraMap k K)) :
    Algebra.IsSeparableExtension K L := by
  let : Algebra.FormallySmooth k L :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k L).mpr inferInstance
  let : Algebra.FormallyUnramified k K :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId k K) h
  exact (Algebra.FormallySmooth.iff_isSeparableExtension K L).mp
    (Algebra.FormallySmooth.of_restrictScalars k K L)

theorem formallySmoothNAdic_of_ramificationIndex_eq
    (A : Type u) (B : Type v) (C : Type w) (D : Type z)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra A B] [Algebra A C] [Algebra B D] [Algebra C D] [Algebra A D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    [IsExtension A B] [IsExtension A C]
    [IsExtension B D] [IsExtension C D]
    [IsExtension A D]
    (he : ramificationIndex A B = ramificationIndex A C)
    [Algebra.IsSeparableExtension (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (hres : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)))
    (hBD : RingHom.FormallySmoothNAdic.{max v z} (algebraMap B D)
      (IsLocalRing.maximalIdeal D)) :
    RingHom.FormallySmoothNAdic.{max w z} (algebraMap C D)
      (IsLocalRing.maximalIdeal D) := by
  obtain ⟨heBD, hsBD⟩ :=
    (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension B D).mp hBD
  apply (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension C D).mpr
  constructor
  · have h₁ := (ramificationIdx_and_inertiaDeg_tower A B D).1
    have h₂ := (ramificationIdx_and_inertiaDeg_tower A C D).1
    change ramificationIndex B D = 1 at heBD
    rw [ramificationIndex_eq_ramificationIdx] at heBD
    rw [ramificationIndex_eq_ramificationIdx A B,
      ramificationIndex_eq_ramificationIdx A C] at he
    change ramificationIndex C D = 1
    rw [ramificationIndex_eq_ramificationIdx]
    have hpos := (ramificationIndex_characterization A C).1
    rw [ramificationIndex_eq_ramificationIdx] at hpos
    rw [heBD, mul_one, he] at h₁
    nlinarith
  · let := hsBD
    let := isSeparableExtension_trans (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)
    exact isSeparableExtension_of_surjective_base (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField D) hres

private theorem formallyEtale_integralClosure_of_surjective
    {R T S : Type*} [CommRing R] [CommRing T] [Field S]
    [Algebra R T] [Algebra R S] [IsArtinianRing T] [IsReduced T]
    [Algebra.FormallyEtale R (integralClosure R T)]
    (f : T →ₐ[R] S) (hf : Function.Surjective f) :
    Algebra.FormallyEtale R (integralClosure R S) := by
  let m : MaximalSpectrum T := ⟨RingHom.ker f,
    RingHom.ker_isMaximal_of_surjective f hf⟩
  obtain ⟨e, _⟩ := exists_integralClosure_pi_equiv R
    (fun q : MaximalSpectrum T ↦ T ⧸ q.asIdeal)
  let := Algebra.FormallyEtale.of_equiv
    (((IsArtinianRing.equivPi T).restrictScalars R).mapIntegralClosure.trans e)
  let := (Algebra.FormallyEtale.pi_iff
    (fun q : MaximalSpectrum T ↦ integralClosure R (T ⧸ q.asIdeal))).mp
      (show Algebra.FormallyEtale R (∀ q : MaximalSpectrum T,
        integralClosure R (T ⧸ q.asIdeal)) from inferInstance) m
  exact Algebra.FormallyEtale.of_equiv
    (Ideal.quotientKerAlgEquivOfSurjective hf).mapIntegralClosure

/-- `AdjoinRoot (X ^ n - C (c ^ n * b))` over a field `K` is Artinian and reduced, and the
integral closure of `R` in it is étale over `R`. -/
private theorem isArtinianRing_isReduced_etale_integralClosure_adjoinRoot
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsIntegrallyClosedIn R K] (b : Rˣ) (c : Kˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) :
    IsArtinianRing (AdjoinRoot (X ^ n - C ((c : K) ^ n * algebraMap R K (b : R)))) ∧
      IsReduced (AdjoinRoot (X ^ n - C ((c : K) ^ n * algebraMap R K (b : R)))) ∧
      Algebra.Etale R
        (integralClosure R (AdjoinRoot (X ^ n - C ((c : K) ^ n * algebraMap R K (b : R))))) := by
  let g : K[X] := X ^ n - C ((c : K) ^ n * algebraMap R K (b : R))
  let : Module.Finite K (AdjoinRoot g) := (monic_X_pow_sub_C _ hn).finite_adjoinRoot
  let d : Kˣ := c ^ n * Units.map (algebraMap R K).toMonoidHom b
  have : Algebra.Etale K (AdjoinRoot g) :=
    etale_adjoinRoot_X_pow_sub_C_unit d hn
      (by simpa only [map_natCast] using hunit.map (algebraMap R K))
  exact ⟨IsArtinianRing.of_finite K _, Algebra.FormallyUnramified.isReduced_of_field K _,
    etale_integralClosure_adjoinRoot_X_pow_sub_C R K b c hn hunit⟩

private theorem formallyEtale_integralClosure_adjoinRoot_factor
    {R K E : Type*} [CommRing R] [Field K] [Field E]
    [Algebra R K] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    [IsIntegrallyClosedIn R K] (b : Rˣ) (c : Kˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R))
    (f : AdjoinRoot (X ^ n - C ((c : K) ^ n * algebraMap R K (b : R))) →ₐ[K] E)
    (hf : Function.Surjective f) :
    Algebra.FormallyEtale R (integralClosure R E) := by
  obtain ⟨_, _, _⟩ := isArtinianRing_isReduced_etale_integralClosure_adjoinRoot b c hn hunit
  exact formallyEtale_integralClosure_of_surjective (f.restrictScalars R) hf

theorem isSeparableExtension_of_ringChar_eq_zero
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (h : ringChar k = 0) : Algebra.IsSeparableExtension k K := by
  let : CharP k 0 := h ▸ inferInstanceAs (CharP k (ringChar k))
  let : CharZero k := CharP.charP_to_charZero k
  refine ⟨fun F _ ↦ ⟨?_⟩⟩
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  exact ⟨s, hs, hsep⟩

theorem exists_surjective_tensorProduct_projection
    {K L K₁ : Type*} [Field K] [Field L] [Field K₁]
    [Algebra K L] [Algebra K K₁]
    {ι : Type*} (E : ι → Type*) [∀ i, Field (E i)]
    [∀ i, Algebra K (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]
    (e : ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] ∀ i, E i)
    (hl : ∀ i l, e (Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
        algebraMap L (E i) l)
    (hr : ∀ i a, e (Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) a)) i =
        algebraMap K₁ (E i) a) (i : ι) :
    ∃ f : L ⊗[K] K₁ →ₐ[L] E i, Function.Surjective f ∧
      ∀ a, f ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) a) =
        algebraMap K₁ (E i) a := by
  classical
  let f : L ⊗[K] K₁ →ₐ[L] E i :=
    { toRingHom := (Pi.evalRingHom E i).comp (e.toRingHom.comp (Ideal.Quotient.mk _))
      commutes' := hl i }
  refine ⟨f, ?_, hr i⟩
  intro x
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (e.symm (Pi.single i x))
  refine ⟨t, ?_⟩
  change e (Ideal.Quotient.mk _ t) i = x
  rw [ht, e.apply_symm_apply]
  exact Pi.single_eq_same i x

theorem formallyEtale_integralClosure_of_tensorProduct_adjoinRoot_factor
    {R K L E : Type*} [CommRing R] [CommRing K] [Field L] [Field E]
    [Algebra K L] [Algebra R L] [Algebra L E] [Algebra R E]
    [IsScalarTower R L E] [IsIntegrallyClosedIn R L]
    (a : K) (b : Rˣ) (c : Lˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R))
    (ha : algebraMap K L a = (c : L) ^ n * algebraMap R L (b : R))
    (f : L ⊗[K] AdjoinRoot (X ^ n - C a) →ₐ[L] E) (hf : Function.Surjective f) :
    Algebra.FormallyEtale R (integralClosure R E) := by
  obtain ⟨e, _⟩ := exists_tensorProduct_adjoinRoot_equiv K L (X ^ n - C a)
  have hmap : (X ^ n - C a).map (algebraMap K L) =
      X ^ n - C ((c : L) ^ n * algebraMap R L (b : R)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, ha]
  let e' := e.trans (AdjoinRoot.algEquivOfEq L _ _ hmap)
  exact formallyEtale_integralClosure_adjoinRoot_factor b c hn hunit
    (f.comp e'.symm.toAlgHom) (hf.comp e'.symm.surjective)

theorem formallySmoothNAdic_localization_of_formallySmooth
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] (q : Ideal S) [q.IsPrime] :
    RingHom.FormallySmoothNAdic.{z} (algebraMap R (Localization.AtPrime q))
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
  formallySmoothNAdic_of_formallySmooth _

theorem surjective_mapIntegralClosure_of_isArtinianRing
    {R T S : Type*} [CommRing R] [CommRing T] [Field S]
    [Algebra R T] [Algebra R S] [IsArtinianRing T] [IsReduced T]
    (f : T →ₐ[R] S) (hf : Function.Surjective f) :
    Function.Surjective f.mapIntegralClosure := by
  classical
  let m : MaximalSpectrum T := ⟨RingHom.ker f,
    RingHom.ker_isMaximal_of_surjective f hf⟩
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let d := (IsArtinianRing.equivPi T).restrictScalars R
  obtain ⟨g, hg⟩ := exists_integralClosure_pi_equiv R
    (fun q : MaximalSpectrum T ↦ T ⧸ q.asIdeal)
  let h := d.mapIntegralClosure.trans g
  intro x
  let y : ∀ q : MaximalSpectrum T, integralClosure R (T ⧸ q.asIdeal) :=
    Pi.single m (e.mapIntegralClosure.symm x)
  refine ⟨h.symm y, ?_⟩
  apply Subtype.ext
  have heval : ((h (h.symm y)) m : T ⧸ m.asIdeal) =
      Ideal.Quotient.mk m.asIdeal (h.symm y : T) :=
    hg (d.mapIntegralClosure (h.symm y)) m
  rw [h.apply_symm_apply] at heval
  have hx : e (y m : T ⧸ m.asIdeal) = (x : S) := by
    dsimp only [y]
    rw [Pi.single_eq_same]
    exact congrArg Subtype.val (e.mapIntegralClosure.apply_symm_apply x)
  rwa [heval] at hx

private theorem etale_integralClosure_adjoinRoot_factor
    {R K E : Type*} [CommRing R] [IsNoetherianRing R] [Field K] [Field E]
    [Algebra R K] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
    [IsIntegrallyClosedIn R K] (b : Rˣ) (c : Kˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R))
    (f : AdjoinRoot (X ^ n - C ((c : K) ^ n * algebraMap R K (b : R))) →ₐ[K] E)
    (hf : Function.Surjective f) :
    Module.Finite R (integralClosure R E) ∧ Algebra.Etale R (integralClosure R E) := by
  obtain ⟨_, _, _⟩ := isArtinianRing_isReduced_etale_integralClosure_adjoinRoot b c hn hunit
  let : Module.Finite R (integralClosure R (AdjoinRoot
      (X ^ n - C ((c : K) ^ n * algebraMap R K (b : R))))) := Algebra.IsIntegral.finite
  let : Module.Finite R (integralClosure R E) :=
    Module.Finite.of_surjective (f.restrictScalars R).mapIntegralClosure.toLinearMap
      (surjective_mapIntegralClosure_of_isArtinianRing (f.restrictScalars R) hf)
  let := formallyEtale_integralClosure_adjoinRoot_factor b c hn hunit f hf
  let : Algebra.FinitePresentation R (integralClosure R E) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

theorem surjective_adjoinRoot_liftAlgHom_of_adjoin_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R[X]) (x : S) (hx : f.eval₂ (algebraMap R S) x = 0)
    (hgen : Algebra.adjoin R {x} = ⊤) :
    Function.Surjective (AdjoinRoot.liftAlgHom f (Algebra.ofId R S) x hx) := by
  apply (AlgHom.range_eq_top _).mp
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  intro y hy
  obtain rfl : y = x := Set.mem_singleton_iff.mp hy
  exact ⟨AdjoinRoot.root f, AdjoinRoot.liftAlgHom_root _ _ _ _⟩

private theorem exists_finite_separable_extension_pow_eq_of_unit
    (R : Type u) (K : Type v) [CommRing R] [IsNoetherianRing R] [Field K]
    [Algebra R K] [IsIntegrallyClosedIn R K] (b : Rˣ) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) :
    ∃ (E : Type v) (_ : Field E) (_ : Algebra K E) (_ : Algebra R E)
      (_ : IsScalarTower R K E),
      Module.Finite K E ∧ Algebra.IsSeparable K E ∧
        Module.Finite R (integralClosure R E) ∧ Algebra.Etale R (integralClosure R E) ∧
        ∃ θ : E, θ ^ n = algebraMap R E (b : R) ∧ Algebra.adjoin K {θ} = ⊤ := by
  let bK : Kˣ := Units.map (algebraMap R K).toMonoidHom b
  obtain ⟨E, hE, hKE, hfin, hsep, θ, hθ, hgen⟩ :=
    exists_finite_separable_extension_pow_eq K bK hn
      (by simpa only [map_natCast] using hunit.map (algebraMap R K))
  let := hE
  let := hKE
  let : Algebra R E := ((algebraMap K E).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let f : K[X] := X ^ n - C ((↑(1 : Kˣ) : K) ^ n * algebraMap R K (b : R))
  have hf : f.eval₂ (algebraMap K E) θ = 0 := by
    simpa [f, bK, sub_eq_zero] using hθ
  let φ : AdjoinRoot f →ₐ[K] E := AdjoinRoot.liftAlgHom f (Algebra.ofId K E) θ hf
  have hφ : Function.Surjective φ :=
    surjective_adjoinRoot_liftAlgHom_of_adjoin_eq_top f θ hf hgen
  obtain ⟨hfinite, hetale⟩ := etale_integralClosure_adjoinRoot_factor b (1 : Kˣ) hn hunit φ hφ
  exact ⟨E, hE, hKE, inferInstance, inferInstance, hfin, hsep, hfinite, hetale, θ, hθ, hgen⟩

private theorem exists_finite_separable_extension_pow_eq_of_dvd
    (R : Type u) (K : Type v) [CommRing R] [IsNoetherianRing R] [Field K]
    [Algebra R K] [IsIntegrallyClosedIn R K]
    (a t : R) (b : Rˣ) {n m : ℕ} (hn : n ≠ 0) (hunit : IsUnit (n : R))
    (hdiv : n ∣ m) (ha : a = (b : R) * t ^ m) :
    ∃ (E : Type v) (_ : Field E) (_ : Algebra K E) (_ : Algebra R E)
      (_ : IsScalarTower R K E),
      Module.Finite K E ∧ Algebra.IsSeparable K E ∧
        Module.Finite R (integralClosure R E) ∧ Algebra.Etale R (integralClosure R E) ∧
        ∃ θ : E, θ ^ n = algebraMap R E a := by
  obtain ⟨d, rfl⟩ := hdiv
  obtain ⟨E, hE, hKE, hRE, ht, hfin, hsep, hfinite, hetale, α, hα, _⟩ :=
    exists_finite_separable_extension_pow_eq_of_unit R K b hn hunit
  let := hE
  let := hKE
  let := hRE
  refine ⟨E, hE, hKE, hRE, ht, hfin, hsep, hfinite, hetale,
    α * algebraMap R E t ^ d, ?_⟩
  rw [mul_pow, hα, ← pow_mul, Nat.mul_comm d n, ha, map_mul, map_pow]

theorem exists_finite_separable_extension_uniformizer_pow_eq
    (A : Type u) (R : Type v) (K : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [IsExtension A R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : A) (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0)
    (hunit : IsUnit (n : R)) (hdiv : n ∣ ramificationIndex A R) :
    ∃ (E : Type w) (_ : Field E) (_ : Algebra K E) (_ : Algebra R E)
      (_ : IsScalarTower R K E),
      Module.Finite K E ∧ Algebra.IsSeparable K E ∧
        Module.Finite R (integralClosure R E) ∧ Algebra.Etale R (integralClosure R E) ∧
        ∃ θ : E, θ ^ n = algebraMap R E (algebraMap A R π) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_prime R
  obtain ⟨b, hb⟩ := (ramificationIndex_characterization A R).2.2.2
    π hπ t ht.irreducible
  exact exists_finite_separable_extension_pow_eq_of_dvd R K (algebraMap A R π) t b
    hn hunit hdiv hb

end

end IsDiscreteValuationRing
