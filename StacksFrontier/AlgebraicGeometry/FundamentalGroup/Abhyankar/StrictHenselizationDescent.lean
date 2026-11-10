module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerBaseChange
public import StacksFrontier.RingTheory.Algebra.DirectLimit.Hom
public import StacksFrontier.RingTheory.FormalFibres.HenselizationShared
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.AtPrime
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel

/-!
# Descending a decomposition into standard tamely ramified algebras from the strict henselization

Let `R` be a ring, `φ ∈ R`, `p ⊆ R` a prime and `Λ` the strict henselization of `R` at `p`. If a
finite étale `R_φ`-algebra `B` becomes, after base change to `Λ_φ`, a finite product of standard
tamely ramified algebras `Λ[x]/(x^{eᵢ} - φ)_φ` with invertible exponents, then the same holds over
an étale `R`-algebra `D` with a prime over `p`. This is the descent step of the proof of
Abhyankar's lemma for a regular divisor ([Stacks, Tag 0EYG]); the mechanism is Stacks 05N8 for the
presentation of `Λ` as a directed colimit of étale `R`-algebras.

## Main results

* `AlgebraicGeometry.Abhyankar.awayTensorEquiv`: `T ⊗_R B ≅ T_φ ⊗_{R_φ} B` for an `R_φ`-algebra
  `B`.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
* [Stacks Project, Tag 05N8](https://stacks.math.columbia.edu/tag/05N8)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

section AwayTensor

variable {R : Type u} [CommRing R] (φ : R) (T : Type u) [CommRing T] [Algebra R T]
  (B : Type u) [CommRing B] [Algebra (Localization.Away φ) B] [Algebra R B]
  [IsScalarTower R (Localization.Away φ) B]
  [Algebra (Localization.Away φ) (Localization.Away (algebraMap R T φ))]
  [IsScalarTower R (Localization.Away φ) (Localization.Away (algebraMap R T φ))]

/-- For an `R_φ`-algebra `B` and an `R`-algebra `T`, `T ⊗_R B ≅ T_φ ⊗_{R_φ} B` as `T`-algebras. -/
def awayTensorEquiv :
    T ⊗[R] B ≃ₐ[T] Localization.Away (algebraMap R T φ) ⊗[Localization.Away φ] B := by
  let Tφ := Localization.Away (algebraMap R T φ)
  have hRTφ : ∀ r, algebraMap (Localization.Away φ) Tφ (algebraMap R _ r) =
      algebraMap T Tφ (algebraMap R T r) := fun r ↦ by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let C := Tφ ⊗[Localization.Away φ] B
  let F : T ⊗[R] B →ₐ[T] C := Algebra.TensorProduct.lift (Algebra.ofId T C)
    ((Algebra.TensorProduct.includeRight : B →ₐ[Localization.Away φ] C).restrictScalars R)
    (fun _ _ ↦ Commute.all _ _)
  letI : Algebra (Localization.Away φ) (T ⊗[R] B) :=
    ((Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B).toRingHom.comp
      (algebraMap (Localization.Away φ) B)).toAlgebra
  have hφu : IsUnit (algebraMap T (T ⊗[R] B) (algebraMap R T φ)) := by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',
      IsScalarTower.algebraMap_apply R (Localization.Away φ) B]
    exact ((IsLocalization.Away.algebraMap_isUnit φ).map _).map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B)
  let Gφ : Tφ →+* T ⊗[R] B := IsLocalization.Away.lift (algebraMap R T φ) hφu
  have hGφ : ∀ t, Gφ (algebraMap T Tφ t) = algebraMap T (T ⊗[R] B) t :=
    IsLocalization.Away.lift_eq _ hφu
  have hGφR : Gφ.comp (algebraMap (Localization.Away φ) Tφ) =
      algebraMap (Localization.Away φ) (T ⊗[R] B) :=
    IsLocalization.ringHom_ext (Submonoid.powers φ) (RingHom.ext fun a ↦ by
      simp only [RingHom.comp_apply]
      rw [hRTφ, hGφ, ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',
        IsScalarTower.algebraMap_apply R (Localization.Away φ) B]
      rfl)
  let Gφa : Tφ →ₐ[Localization.Away φ] T ⊗[R] B :=
    { Gφ with commutes' := fun r ↦ RingHom.congr_fun hGφR r }
  let Gb : B →ₐ[Localization.Away φ] T ⊗[R] B :=
    { (Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B) with commutes' := fun _ ↦ rfl }
  let G : C →ₐ[Localization.Away φ] T ⊗[R] B :=
    Algebra.TensorProduct.lift Gφa Gb (fun _ _ ↦ Commute.all _ _)
  haveI : IsScalarTower R (Localization.Away φ) (T ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = (1 : T) ⊗ₜ[R] algebraMap (Localization.Away φ) B (algebraMap R _ r)
      rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  have hG : ∀ τ b, G (τ ⊗ₜ b) = Gφ τ * ((1 : T) ⊗ₜ b) := fun τ b ↦
    Algebra.TensorProduct.lift_tmul _ _ _ τ b
  have hF : ∀ t b, F (t ⊗ₜ b) = (algebraMap T Tφ t ⊗ₜ 1) * ((1 : Tφ) ⊗ₜ b) := fun t b ↦ by
    rw [← Algebra.TensorProduct.algebraMap_apply]
    exact Algebra.TensorProduct.lift_tmul _ _ _ t b
  have hGF : (G.restrictScalars R).comp (F.restrictScalars R) = AlgHom.id R (T ⊗[R] B) := by
    apply Algebra.TensorProduct.ext
    · ext t
      change G (F (t ⊗ₜ 1)) = t ⊗ₜ 1
      rw [hF, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hG, hGφ,
        ← Algebra.TensorProduct.one_def, mul_one, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
    · ext b
      change G (F (1 ⊗ₜ b)) = 1 ⊗ₜ b
      rw [hF, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, hG, map_one,
        one_mul]
  let Fφ : T ⊗[R] B →ₐ[Localization.Away φ] C :=
    { F.toRingHom with
      commutes' := fun r ↦ by
        change F ((1 : T) ⊗ₜ algebraMap _ B r) = _
        rw [hF, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
          Algebra.TensorProduct.algebraMap_apply'] }
  have hFG : Fφ.comp G = AlgHom.id (Localization.Away φ) C := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.toRingHom_injective
      refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R T φ))
        (RingHom.ext fun t ↦ ?_)
      change F (G (algebraMap T Tφ t ⊗ₜ 1)) = algebraMap T Tφ t ⊗ₜ 1
      rw [hG, hGφ, ← Algebra.TensorProduct.one_def, mul_one, F.commutes,
        Algebra.TensorProduct.algebraMap_apply]
    · ext b
      change F (G (1 ⊗ₜ b)) = 1 ⊗ₜ b
      rw [hG, map_one, one_mul, hF, map_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        one_mul]
  let GT : C →ₐ[T] T ⊗[R] B :=
    { G.toRingHom with
      commutes' := fun t ↦ by
        change G (algebraMap T C t) = _
        rw [Algebra.TensorProduct.algebraMap_apply, hG, hGφ, ← Algebra.TensorProduct.one_def,
          mul_one] }
  exact AlgEquiv.ofAlgHom F GT
    (AlgHom.toRingHom_injective (congrArg AlgHom.toRingHom hFG))
    (AlgHom.toRingHom_injective (congrArg AlgHom.toRingHom hGF))

/-- An isomorphism `∏ᵢ T[x]/(x^{eᵢ} - φ)_φ ≅ T_φ ⊗_{R_φ} B` over `T`, read as
`T ⊗_R ∏ᵢ R[x]/(x^{eᵢ} - φ)_φ ≅ T ⊗_R B`. -/
def tensorEquivOfKummerAwayEquiv {n : ℕ} (e : Fin n → ℕ)
    (σ : (∀ i, Localization.Away (algebraMap T
        (standardTamelyRamifiedAlgebra T (algebraMap R T φ) (e i)) (algebraMap R T φ))) ≃ₐ[T]
      Localization.Away (algebraMap R T φ) ⊗[Localization.Away φ] B) :
    T ⊗[R] (∀ i, Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ (e i)) φ))
      ≃ₐ[T] T ⊗[R] B :=
  (kummerAwayPiBaseChange φ T e).trans (σ.trans (awayTensorEquiv φ T B).symm)

end AwayTensor


section Bijective

/-- **Bijectivity of a base change persists along further base change.** If `u : C → B` is a map
of `A`-algebras whose base change to `A'` is bijective, its base change to any `A'`-algebra `A''`
is bijective. -/
theorem bijective_lTensor_of_bijective_lTensor {A A' A'' B C : Type u} [CommRing A] [CommRing A']
    [CommRing A''] [CommRing B] [CommRing C] [Algebra A A'] [Algebra A' A''] [Algebra A A'']
    [IsScalarTower A A' A''] [Algebra A B] [Algebra A C] (u : C →ₐ[A] B)
    (h : Function.Bijective (Algebra.TensorProduct.lTensor (S := A') A' u)) :
    Function.Bijective (Algebra.TensorProduct.lTensor (S := A'') A'' u) := by
  let e := AlgEquiv.ofBijective _ h
  let cC := Algebra.TensorProduct.cancelBaseChange A A' A'' A'' C
  let cB := Algebra.TensorProduct.cancelBaseChange A A' A'' A'' B
  let c := Algebra.TensorProduct.congr (AlgEquiv.refl (R := A'') (A₁ := A'')) e
  have key : ∀ z, Algebra.TensorProduct.lTensor (S := A'') A'' u z =
      cB (c (cC.symm z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      simp [cC, cB, c, e, Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rw [show (Algebra.TensorProduct.lTensor (S := A'') A'' u : _ → _) = cB ∘ c ∘ cC.symm from
    funext key]
  exact cB.bijective.comp (c.bijective.comp cC.symm.bijective)

/-- A base change `D ⊗_A (A ⊗_R P) → D ⊗_A (A ⊗_R B)` of an `A`-algebra map which is bijective
gives `D ⊗_R P ≅ D ⊗_R B` over `D`. -/
theorem nonempty_algEquiv_of_bijective_lTensor {R A D P B : Type u} [CommRing R] [CommRing A]
    [CommRing D] [CommRing P] [CommRing B] [Algebra R A] [Algebra R D] [Algebra A D]
    [IsScalarTower R A D] [Algebra R P] [Algebra R B] (v : A ⊗[R] P →ₐ[A] A ⊗[R] B)
    (h : Function.Bijective (Algebra.TensorProduct.lTensor (S := D) D v)) :
    Nonempty (D ⊗[R] P ≃ₐ[D] D ⊗[R] B) :=
  ⟨(Algebra.TensorProduct.cancelBaseChange R A D D P).symm.trans
    ((AlgEquiv.ofBijective _ h).trans (Algebra.TensorProduct.cancelBaseChange R A D D B))⟩

/-- The two previous statements together: a bijective base change to `A'` of an `A`-algebra map
`A ⊗_R P → A ⊗_R B` gives `A'' ⊗_R P ≅ A'' ⊗_R B` for every `A'`-algebra `A''`. -/
theorem nonempty_algEquiv_of_bijective_lTensor_of_le {R A A' A'' P B : Type u} [CommRing R]
    [CommRing A] [CommRing A'] [CommRing A''] [CommRing P] [CommRing B] [Algebra A A']
    [Algebra A' A''] [Algebra A A''] [IsScalarTower A A' A''] [Algebra R A] [Algebra R A'']
    [IsScalarTower R A A''] [Algebra R P] [Algebra R B] (v : A ⊗[R] P →ₐ[A] A ⊗[R] B)
    (h : Function.Bijective (Algebra.TensorProduct.lTensor (S := A') A' v)) :
    Nonempty (A'' ⊗[R] P ≃ₐ[A''] A'' ⊗[R] B) :=
  nonempty_algEquiv_of_bijective_lTensor v (bijective_lTensor_of_bijective_lTensor v h)

/-- The localization map `R_φ → A_φ` makes `R → R_φ → A_φ` a scalar tower. -/
private theorem isScalarTower_awayMap {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (φ : R) :
    letI := (Localization.awayMap (algebraMap R A) φ).toAlgebra
    IsScalarTower R (Localization.Away φ) (Localization.Away (algebraMap R A φ)) :=
  let := (Localization.awayMap (algebraMap R A) φ).toAlgebra
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = Localization.awayMap (algebraMap R A) φ _
    exact (IsScalarTower.algebraMap_apply R A _ r).trans (IsLocalization.map_eq _ _).symm

/-- The descended isomorphism in its final form: a bijective base change to `A'` of an `A`-algebra
map `A ⊗_R ∏ᵢ R[x]/(x^{eᵢ} - φ)_φ → A ⊗_R B` gives, over every `A'`-algebra `A''`,
`∏ᵢ A''[x]/(x^{eᵢ} - φ)_φ ≅ A''_φ ⊗_{R_φ} B`. -/
theorem nonempty_kummerAway_algEquiv_of_bijective_lTensor {R A A' A'' : Type u} [CommRing R]
    [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A' A''] [Algebra A A'']
    [IsScalarTower A A' A''] [Algebra R A] [Algebra R A''] [IsScalarTower R A A''] (φ : R)
    (B : Type u) [CommRing B] [Algebra (Localization.Away φ) B] [Algebra R B]
    [IsScalarTower R (Localization.Away φ) B] {n : ℕ} (e : Fin n → ℕ)
    (v : A ⊗[R] (∀ i, Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ (e i)) φ))
      →ₐ[A] A ⊗[R] B)
    (h : Function.Bijective (Algebra.TensorProduct.lTensor (S := A') A' v)) :
    letI := (Localization.awayMap (algebraMap R A'') φ).toAlgebra
    Nonempty ((∀ i, Localization.Away (algebraMap A''
        (standardTamelyRamifiedAlgebra A'' (algebraMap R A'' φ) (e i))
          (algebraMap R A'' φ))) ≃ₐ[A'']
      Localization.Away (algebraMap R A'' φ) ⊗[Localization.Away φ] B) := by
  let : Algebra (Localization.Away φ) (Localization.Away (algebraMap R A'' φ)) :=
    (Localization.awayMap (algebraMap R A'') φ).toAlgebra
  have : IsScalarTower R (Localization.Away φ) (Localization.Away (algebraMap R A'' φ)) :=
    isScalarTower_awayMap φ
  obtain ⟨ε⟩ := nonempty_algEquiv_of_bijective_lTensor_of_le (A'' := A'') v h
  exact ⟨(kummerAwayPiBaseChange φ A'' e).symm.trans (ε.trans (awayTensorEquiv φ A'' B))⟩

/-- A base change `L ⊗_A v` of an `A`-algebra map `v : A ⊗_R P → A ⊗_R B` is bijective as soon
as `v` becomes an isomorphism `τ : L ⊗_R P ≅ L ⊗_R B` after base change along `A → L`. -/
private theorem bijective_lTensor_of_rTensor_comp_eq {R A L P B : Type u} [CommRing R] [CommRing A]
    [CommRing L] [CommRing P] [CommRing B] [Algebra R A] [Algebra R L] [Algebra A L]
    [IsScalarTower R A L] [Algebra R P] [Algebra R B] (τ : L ⊗[R] P ≃ₐ[L] L ⊗[R] B)
    (v : A ⊗[R] P →ₐ[A] A ⊗[R] B)
    (hsq : (τ.toAlgHom.restrictScalars R).comp
        (Algebra.TensorProduct.rTensor P (IsScalarTower.toAlgHom R A L)) =
      (Algebra.TensorProduct.rTensor B (IsScalarTower.toAlgHom R A L)).comp
        (v.restrictScalars R)) :
    Function.Bijective (Algebra.TensorProduct.lTensor (S := L) L v) := by
  let cP := Algebra.TensorProduct.cancelBaseChange R A L L P
  let cB := Algebra.TensorProduct.cancelBaseChange R A L L B
  have hc : ∀ {X : Type u} [CommRing X] [Algebra R X] (w : A ⊗[R] X),
      Algebra.TensorProduct.cancelBaseChange R A L L X (1 ⊗ₜ w) =
        Algebra.TensorProduct.rTensor X (IsScalarTower.toAlgHom R A L) w := by
    intro X _ _ w
    induction w using TensorProduct.inductionOn with
    | tmul t x =>
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
      rfl
    | add w₁ w₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, h₁, h₂, map_add]
  have hsq' : ∀ w, τ (Algebra.TensorProduct.rTensor P (IsScalarTower.toAlgHom R A L) w) =
      Algebra.TensorProduct.rTensor B (IsScalarTower.toAlgHom R A L) (v w) :=
    fun w ↦ congrArg (fun F ↦ F w) hsq
  have key : ∀ z, cB (Algebra.TensorProduct.lTensor (S := L) L v z) = τ (cP z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul l w =>
      have h₁ : ∀ {X : Type u} [CommRing X] [Algebra R X] (y : A ⊗[R] X),
          l ⊗ₜ[A] y = algebraMap L (L ⊗[A] (A ⊗[R] X)) l * (1 ⊗ₜ y) := by
        intro X _ _ y
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul]
        rfl
      simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
        id_eq]
      rw [h₁, h₁ w, map_mul, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
        AlgEquiv.commutes, hc, hc, hsq']
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rw [show (Algebra.TensorProduct.lTensor (S := L) L v : _ → _) = cB.symm ∘ τ ∘ cP from
    funext fun z ↦ by simp only [Function.comp_apply, ← key, AlgEquiv.symm_apply_apply]]
  exact cB.symm.bijective.comp (τ.bijective.comp cP.bijective)

end Bijective

/-- A natural number invertible in a filtered colimit `L` of `A`-algebras `G j` is already
invertible in some `G j`. -/
private theorem exists_isUnit_natCast_of_isUnit {A L ι : Type*} [CommRing A] [CommRing L]
    [Algebra A L] [Preorder ι] {G : ι → Type*} [∀ i, CommRing (G i)] [∀ i, Algebra A (G i)]
    (f : (i j : ι) → i ≤ j → G i →ₐ[A] G j) (g : (i : ι) → G i →ₐ[A] L)
    (hsurj : ∀ b : L, ∃ i, ∃ x : G i, g i x = b)
    (hinj : ∀ i (x y : G i), g i x = g i y → ∃ j, ∃ h : i ≤ j, f i j h x = f i j h y)
    {m : ℕ} (hm : IsUnit (m : L)) : ∃ j, IsUnit (m : G j) := by
  obtain ⟨j, y, hy⟩ := hsurj hm.unit⁻¹.1
  have h₁ : g j ((m : G j) * y) = g j 1 := by
    rw [map_mul, map_natCast, hy, map_one]
    exact hm.mul_val_inv
  obtain ⟨j', _, hj'⟩ := hinj j _ _ h₁
  rw [map_mul, map_natCast, map_one] at hj'
  exact ⟨j', IsUnit.of_mul_eq_one _ hj'⟩

/-- Finitely many natural numbers invertible in a directed colimit `L` of `A`-algebras `G j` are
all invertible in some `G ν` beyond any given stage `μ`. -/
private theorem exists_ge_forall_isUnit_natCast {A L ι : Type*} [CommRing A] [CommRing L]
    [Algebra A L] [Preorder ι] [IsDirected ι (· ≤ ·)] {G : ι → Type*} [∀ i, CommRing (G i)]
    [∀ i, Algebra A (G i)] (f : (i j : ι) → i ≤ j → G i →ₐ[A] G j) (g : (i : ι) → G i →ₐ[A] L)
    (hsurj : ∀ b : L, ∃ i, ∃ x : G i, g i x = b)
    (hinj : ∀ i (x y : G i), g i x = g i y → ∃ j, ∃ h : i ≤ j, f i j h x = f i j h y)
    {n : ℕ} {e : Fin n → ℕ} (he : ∀ k, IsUnit (e k : L)) (μ : ι) :
    ∃ ν, μ ≤ ν ∧ ∀ k, IsUnit (e k : G ν) := by
  classical
  have : Nonempty ι := ⟨μ⟩
  choose j hj using fun k ↦ exists_isUnit_natCast_of_isUnit f g hsurj hinj (he k)
  obtain ⟨ν, hν⟩ := Finset.exists_le (insert μ (Finset.univ.image j))
  refine ⟨ν, hν μ (Finset.mem_insert_self _ _), fun k ↦ ?_⟩
  simpa using (hj k).map (f (j k) ν (hν (j k) (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem j (Finset.mem_univ k)))))

/-- The localization `R[x]/(x^m - φ)_φ` is a finitely presented `R`-algebra. -/
private theorem finitePresentation_away_standardTamelyRamifiedAlgebra {R : Type u} [CommRing R]
    (φ : R) (m : ℕ) : Algebra.FinitePresentation R
      (Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ m) φ)) := by
  have : Algebra.FinitePresentation R (standardTamelyRamifiedAlgebra R φ m) :=
    Algebra.FinitePresentation.quotient ⟨{Polynomial.X ^ m - Polynomial.C φ}, by simp⟩
  have : Algebra.FinitePresentation (standardTamelyRamifiedAlgebra R φ m)
      (Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ m) φ)) :=
    IsLocalization.Away.finitePresentation (algebraMap R (standardTamelyRamifiedAlgebra R φ m) φ)
  exact Algebra.FinitePresentation.trans R (standardTamelyRamifiedAlgebra R φ m) _

section Descent

variable {R : Type u} [CommRing R] (φ : R) (p : Ideal R) [p.IsPrime]

/-- **Descent from the strict henselization.** Let `Λ` be the strict henselization of `R` at the
prime `p` and `B` a finite étale `R_φ`-algebra. If `Λ_φ ⊗_{R_φ} B ≅ ∏ᵢ Λ[x]/(x^{eᵢ} - φ)_φ` over
`Λ` with every `eᵢ` invertible in `Λ`, then there is an étale `R`-algebra `D` with a prime over
`p` such that every `eᵢ` is invertible in `D` and `D_φ ⊗_{R_φ} B ≅ ∏ᵢ D[x]/(x^{eᵢ} - φ)_φ` over
`D`. -/
theorem exists_etale_algEquiv_of_strictHenselization
    (B : Type u) [CommRing B] [Algebra (Localization.Away φ) B]
    [Module.Finite (Localization.Away φ) B] [Algebra.Etale (Localization.Away φ) B]
    {n : ℕ} (e : Fin n → ℕ)
    (he : ∀ i, IsUnit (e i : StacksDraft.strictHenselizationAtPrime R p))
    (σ : letI := (Localization.awayMap
        (algebraMap R (StacksDraft.strictHenselizationAtPrime R p)) φ).toAlgebra
      (∀ i, Localization.Away (algebraMap (StacksDraft.strictHenselizationAtPrime R p)
        (standardTamelyRamifiedAlgebra (StacksDraft.strictHenselizationAtPrime R p)
          (algebraMap R _ φ) (e i)) (algebraMap R _ φ)))
        ≃ₐ[StacksDraft.strictHenselizationAtPrime R p]
        Localization.Away (algebraMap R (StacksDraft.strictHenselizationAtPrime R p) φ)
          ⊗[Localization.Away φ] B) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D), Algebra.Etale R D ∧
      ∃ q : Ideal D, q.IsPrime ∧ q.comap (algebraMap R D) = p ∧ (∀ i, IsUnit (e i : D)) ∧
      letI := (Localization.awayMap (algebraMap R D) φ).toAlgebra
      Nonempty ((∀ i, Localization.Away (algebraMap D
          (standardTamelyRamifiedAlgebra D (algebraMap R D φ) (e i)) (algebraMap R D φ))) ≃ₐ[D]
        Localization.Away (algebraMap R D φ) ⊗[Localization.Away φ] B) := by
  classical
  let Λ := StacksDraft.strictHenselizationAtPrime R p
  let : Algebra R B := ((algebraMap (Localization.Away φ) B).comp
    (algebraMap R (Localization.Away φ))).toAlgebra
  have : IsScalarTower R (Localization.Away φ) B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let P := ∀ i, Localization.Away (algebraMap R (standardTamelyRamifiedAlgebra R φ (e i)) φ)
  have := fun k ↦ finitePresentation_away_standardTamelyRamifiedAlgebra φ (e k)
  have hPfp : Algebra.FinitePresentation R P := inferInstance
  have : Algebra.FinitePresentation R (Localization.Away φ) :=
    IsLocalization.Away.finitePresentation φ
  have hBfp : Algebra.FinitePresentation R B :=
    Algebra.FinitePresentation.trans R (Localization.Away φ) B
  -- The isomorphism over `Λ`, as `Λ ⊗_R P ≅ Λ ⊗_R B`.
  let : Algebra (Localization.Away φ) (Localization.Away (algebraMap R Λ φ)) :=
    (Localization.awayMap (algebraMap R Λ) φ).toAlgebra
  have : IsScalarTower R (Localization.Away φ) (Localization.Away (algebraMap R Λ φ)) :=
    isScalarTower_awayMap φ
  let τ : Λ ⊗[R] P ≃ₐ[Λ] Λ ⊗[R] B := tensorEquivOfKummerAwayEquiv φ Λ B e σ
  -- `Λ` as a directed colimit of étale `R`-algebras.
  obtain ⟨ι, _, _, _, G, _, _, hGet, f, hds, g, hg, hsurj, hinj⟩ :=
    Stacks.Henselization.Shared.isFilteredColimitEtale_of_ind R Λ
      (StacksDraft.indEtale_iff.mp (StacksDraft.indEtale_strictHenselizationAtPrime R p))
  have hz : ∀ j (x : G j), g j x = 0 → ∃ k, ∃ h : j ≤ k, f j k h x = 0 := by
    intro j x hx
    obtain ⟨k, h, hk⟩ := hinj j x 0 (by rw [hx, map_zero])
    exact ⟨k, h, by rw [hk, map_zero]⟩
  have : IsDirectedOrder ι := ⟨fun a b ↦ directed_of (· ≤ ·) a b⟩
  have hR := DirectLimit.Algebra.bijective_lift_of_directed f g hg hsurj hz
  -- The isomorphism descends to a stage as a map, and becomes bijective at a later stage.
  obtain ⟨i, vᵢ, hsq⟩ := (Algebra.TensorProduct.exists_of_directLimit f g hg hR).2.2.1 hPfp
    τ.toAlgHom
  -- Over `Λ`, the base change of `vᵢ` is `τ`, hence bijective.
  let : Algebra (G i) Λ := (g i).toRingHom.toAlgebra
  have : IsScalarTower R (G i) Λ := IsScalarTower.of_algHom (g i)
  have hL := bijective_lTensor_of_rTensor_comp_eq τ vᵢ hsq
  have : DirectedSystem G fun i j h ↦ ⇑((f i j h).toRingHom) := hds
  obtain ⟨μ, hiμ, hbij⟩ := Module.Flat.DirectedModel.exists_lTensor_bijective
    (B := fun j ↦ G j ⊗[R] B) (fun i j h ↦ (f i j h).toRingHom) (fun j ↦ (g j).toRingHom)
    (fun i j h x ↦ hg i j h x) hsurj hz (i₁ := i) vᵢ hL
  -- A later stage at which the exponents are invertible.
  obtain ⟨ν, hμν, hunitν⟩ := exists_ge_forall_isUnit_natCast f g hsurj hinj he μ
  -- The bijectivity at `ν`.
  let : Algebra (G i) (G μ) := (f i μ hiμ).toRingHom.toAlgebra
  let : Algebra (G μ) (G ν) := (f μ ν hμν).toRingHom.toAlgebra
  let : Algebra (G i) (G ν) := (f i ν (hiμ.trans hμν)).toRingHom.toAlgebra
  have : IsScalarTower (G i) (G μ) (G ν) := IsScalarTower.of_algebraMap_eq fun x ↦
    (DirectedSystem.map_map' f hiμ hμν x).symm
  have : IsScalarTower R (G i) (G ν) := IsScalarTower.of_algHom (f i ν (hiμ.trans hμν))
  refine ⟨G ν, inferInstance, inferInstance, hGet ν,
    (IsLocalRing.maximalIdeal Λ).comap (g ν).toRingHom, Ideal.comap_isPrime _ _, ?_, hunitν,
    nonempty_kummerAway_algEquiv_of_bijective_lTensor (A' := G μ) (A'' := G ν) φ B e vᵢ hbij⟩
  rw [Ideal.comap_comap, show (g ν).toRingHom.comp (algebraMap R (G ν)) = algebraMap R Λ from
    (g ν).comp_algebraMap]
  exact StacksDraft.under_maximalIdeal_strictHenselizationAtPrime R p

end Descent

end AlgebraicGeometry.Abhyankar
