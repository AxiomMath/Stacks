module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafBlockWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsFiltration

/-!
# Weights of the restriction of scalars of a graded upper-triangular representation

Let `E/ℚ_ℓ` be an extension with a basis `b` and `Y : π₁(X, x̄) → GL_m(E)` a representation which
is graded upper triangular for a grading `δ`.  Filtering `E^m` by the grade, the sheaf
`ℱ_{Res_b Y}` has a filtration whose graded pieces are the sheaves of `Res_b` of the diagonal
blocks of `Y`.  Hence a weight bound for `Hⁱ_c` of `ℱ_{Res_b Y'}`, for every `Y'` whose Frobenius
characteristic polynomials satisfy a property `Pc` (for instance purity along every embedding of
`E`), gives the bound for `ℱ_{Res_b Y}` as soon as every diagonal block of `Y` satisfies `Pc`
(Kedlaya, *Fourier transforms and p-adic Weil II*, §6, the dévissage of Theorem main1).

## Main results

* `Stacks.EtaleCohomology.charpoly_submatrix_eq_charpoly_toSquareBlock`.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_restrictScalarsRep_of_isGradedUpper`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

/-- The characteristic polynomial of a diagonal block, read along an enumeration of its
coordinates. -/
public theorem charpoly_submatrix_eq_charpoly_toSquareBlock {R : Type*} [CommRing R] {m n : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (δ : Fin m → ℤ) (t : ℤ) {e : Fin n → Fin m}
    (he : Function.Injective e) (hre : ∀ i, δ i = t ↔ ∃ j, e j = i) :
    (M.submatrix e e).charpoly = (M.toSquareBlock δ t).charpoly := by
  let σ : Fin n ≃ {i // δ i = t} := Equiv.ofBijective (fun j => ⟨e j, (hre _).2 ⟨j, rfl⟩⟩)
    ⟨fun j j' h => he (congrArg Subtype.val h), fun ⟨i, hi⟩ =>
      ((hre i).1 hi).imp fun _ => Subtype.ext⟩
  have : M.submatrix e e = reindex σ.symm σ.symm (M.toSquareBlock δ t) := by
    ext j j'
    simp [σ, Matrix.toSquareBlock, Matrix.toSquareBlockProp, Matrix.toBlock]
    rfl
  rw [this, charpoly_reindex]

/-- An enumeration of the coordinates satisfying a predicate. -/
public theorem exists_injective_forall_iff_exists {m : ℕ} (P : Fin m → Prop) :
    ∃ (n : ℕ) (e : Fin n → Fin m), Function.Injective e ∧ ∀ i, P i ↔ ∃ j, e j = i := by
  classical
  exact ⟨Fintype.card {i // P i}, fun j => ((Fintype.equivFin {i // P i}).symm j).1,
      fun j j' h => (Fintype.equivFin {i // P i}).symm.injective (Subtype.ext h),
      fun i => ⟨fun h => ⟨Fintype.equivFin {i // P i} ⟨i, h⟩, by simp⟩,
        fun ⟨j, hj⟩ => hj ▸ ((Fintype.equivFin {i // P i}).symm j).2⟩⟩

/-- The block of a graded upper-triangular matrix from coordinates of lower grade to coordinates
of higher grade vanishes. -/
public theorem transpose_coordMatrix_mul_mul_coordMatrix_eq_zero_of_isGradedUpper {R : Type*}
    [CommRing R] {m a c : ℕ} {δ : Fin m → ℤ} {M : Matrix (Fin m) (Fin m) R}
    (hM : IsGradedUpper δ M) {e₁ : Fin a → Fin m} {e₂ : Fin c → Fin m}
    (hlt : ∀ j j', δ (e₁ j') < δ (e₂ j)) :
    (coordMatrix (R := R) e₂)ᵀ * M * coordMatrix (R := R) e₁ = 0 := by
  refine (transpose_coordMatrix_mul_mul_coordMatrix M).trans ?_
  ext j j'
  simp only [Matrix.submatrix_apply, Matrix.zero_apply]
  exact hM _ _ (hlt j j')

/-- A diagonal block of `M` along an enumeration `e` of the coordinates of grade `≠ t₀` is the
diagonal block of `M.submatrix e e` for the induced grading, as long as it has grade `≠ t₀`. -/
public theorem charpoly_toSquareBlock_submatrix_of_ne {R : Type*} [CommRing R] {m c : ℕ}
    (M : Matrix (Fin m) (Fin m) R) {δ : Fin m → ℤ} {t₀ t : ℤ} {e : Fin c → Fin m}
    (he : Function.Injective e) (hre : ∀ i, δ i ≠ t₀ ↔ ∃ j, e j = i) (ht : t ≠ t₀) :
    ((M.submatrix e e).toSquareBlock (δ ∘ e) t).charpoly = (M.toSquareBlock δ t).charpoly := by
  classical
  obtain ⟨n', e', he', hre'⟩ := exists_injective_forall_iff_exists fun j => δ (e j) = t
  have hre'' : ∀ i, δ i = t ↔ ∃ j, (e ∘ e') j = i := fun i => by
    refine ⟨fun hi => ?_, ?_⟩
    · obtain ⟨j'', rfl⟩ := (hre i).1 (hi ▸ ht)
      obtain ⟨j', rfl⟩ := (hre' j'').1 hi
      exact ⟨j', rfl⟩
    · rintro ⟨j', rfl⟩
      exact (hre' (e' j')).2 ⟨j', rfl⟩
  rw [← charpoly_submatrix_eq_charpoly_toSquareBlock _ (δ ∘ e) t he' hre',
    Matrix.submatrix_submatrix,
    charpoly_submatrix_eq_charpoly_toSquareBlock _ δ t (he.comp he') hre'']

/-- The diagonal block of grade `t₀` of `M.submatrix e e` is empty when `e` avoids grade `t₀`. -/
public theorem charpoly_toSquareBlock_submatrix_eq_one {R : Type*} [CommRing R] {m c : ℕ}
    (M : Matrix (Fin m) (Fin m) R) {δ : Fin m → ℤ} {t₀ : ℤ} {e : Fin c → Fin m}
    (he : ∀ j, δ (e j) ≠ t₀) : ((M.submatrix e e).toSquareBlock (δ ∘ e) t₀).charpoly = 1 :=
  have : IsEmpty {j // (δ ∘ e) j = t₀} := ⟨fun ⟨j, hj⟩ => he j hj⟩
  charpoly_isEmpty

/-- A property of the families of diagonal blocks of a family of matrices, holding for the trivial
family, passes to the diagonal blocks of the submatrices along the coordinates of grade `≠ t₀`. -/
public theorem forall_charpoly_toSquareBlock_submatrix {R : Type*} [CommRing R] {m c : ℕ}
    {Ys : Type*} (Pc : (Ys → Polynomial R) → Prop) (hPc : Pc fun _ => 1)
    (M : Ys → Matrix (Fin m) (Fin m) R) {δ : Fin m → ℤ} {t₀ : ℤ} {e : Fin c → Fin m}
    (he : Function.Injective e) (hre : ∀ i, δ i ≠ t₀ ↔ ∃ j, e j = i)
    (hM : ∀ t, Pc fun y => ((M y).toSquareBlock δ t).charpoly) (t : ℤ) :
    Pc fun y => (((M y).submatrix e e).toSquareBlock (δ ∘ e) t).charpoly := by
  rcases eq_or_ne t t₀ with rfl | ht
  · simpa only [charpoly_toSquareBlock_submatrix_eq_one _ fun j => (hre _).2 ⟨j, rfl⟩] using hPc
  · simpa only [charpoly_toSquareBlock_submatrix_of_ne _ he hre ht] using hM t

/-- Restriction of scalars of a splitting by coordinates is a splitting by coordinates. -/
public theorem isSplitting_coordMatrix_resIndex {R : Type*} [CommRing R] {r a c d : ℕ}
    {e₁ : Fin a → Fin r} {e₂ : Fin c → Fin r} (he₁ : Function.Injective e₁)
    (he₂ : Function.Injective e₂) (hdisj : ∀ j j', e₁ j ≠ e₂ j')
    (hcov : ∀ i, (∃ j, e₁ j = i) ∨ ∃ j, e₂ j = i) :
    IsSplitting (coordMatrix (R := R) (resIndex (d := d) e₁)) (coordMatrix (resIndex (d := d) e₁))ᵀ
      (coordMatrix (resIndex (d := d) e₂))ᵀ (coordMatrix (resIndex (d := d) e₂)) := by
  refine isSplitting_coordMatrix (resIndex_injective he₁) (resIndex_injective he₂)
    (fun p₁ p₂ h => hdisj _ _ (congrArg Prod.fst (finProdFinEquiv.injective h))) fun p' => ?_
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p'
  rcases hcov i with ⟨j', rfl⟩ | ⟨j', rfl⟩
  · exact Or.inl ⟨finProdFinEquiv (j', l), resIndex_apply _ _ _⟩
  · exact Or.inr ⟨finProdFinEquiv (j', l), resIndex_apply _ _ _⟩

section Res

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
  {G : Type*} [Group G] {r a c : ℕ} {e₁ : Fin a → Fin r} {e₂ : Fin c → Fin r}
  (h : IsSplitting (coordMatrix (R := E) e₁) (coordMatrix e₁)ᵀ (coordMatrix e₂)ᵀ (coordMatrix e₂))
  (Y : G →* GL (Fin r) E)

/-- Restriction of scalars of a sub-representation on coordinates. -/
public theorem restrictScalarsMatrix_subRep_val
    (hY : ∀ g, (Y g).val * coordMatrix e₁ = coordMatrix e₁ * ((coordMatrix e₁)ᵀ * (Y g).val *
      coordMatrix e₁)) (g : G) :
    restrictScalarsMatrix b (h.subRep Y hY g).val =
      (coordMatrix (R := F) (resIndex (d := d) e₁))ᵀ * (restrictScalarsRep b Y g).val *
        coordMatrix (resIndex e₁) := by
  rw [IsSplitting.subRep_val, restrictScalarsMatrix_mul, restrictScalarsMatrix_mul,
    restrictScalarsMatrix_transpose_coordMatrix, restrictScalarsMatrix_coordMatrix]
  rfl

/-- Restriction of scalars of a quotient representation along coordinates. -/
public theorem restrictScalarsMatrix_quotRep_val
    (hY : ∀ g, (coordMatrix e₂)ᵀ * (Y g).val = ((coordMatrix e₂)ᵀ * (Y g).val * coordMatrix e₂) *
      (coordMatrix e₂)ᵀ) (g : G) :
    restrictScalarsMatrix b (h.quotRep Y hY g).val =
      (coordMatrix (R := F) (resIndex (d := d) e₂))ᵀ * (restrictScalarsRep b Y g).val *
        coordMatrix (resIndex e₂) := by
  rw [IsSplitting.quotRep_val, restrictScalarsMatrix_mul, restrictScalarsMatrix_mul,
    restrictScalarsMatrix_transpose_coordMatrix, restrictScalarsMatrix_coordMatrix]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace F] [IsTopologicalRing F]

/-- `Res_b Z` is continuous if `Res_b` of each `Z g` is a fixed two-sided multiple of `Res_b Y g`
for a continuous `Res_b Y`. -/
private theorem continuous_restrictScalarsRep_of_eq_mul {n : ℕ} (Z : G →* GL (Fin n) E)
    (A : Matrix (Fin (n * d)) (Fin (r * d)) F) (B : Matrix (Fin (r * d)) (Fin (n * d)) F)
    (hZ : ∀ g, restrictScalarsMatrix b (Z g).val = A * (restrictScalarsRep b Y g).val * B)
    (hYc : Continuous (restrictScalarsRep b Y)) : Continuous (restrictScalarsRep b Z) :=
  continuous_restrictScalarsRep b _ <| by
    rw [show (fun g => restrictScalarsMatrix b (Z g).val) = _ from funext hZ]
    exact (continuous_const.matrix_mul (Units.continuous_val.comp hYc)).matrix_mul continuous_const

/-- Restriction of scalars of a sub-representation on coordinates is continuous. -/
public theorem continuous_restrictScalarsRep_subRep
    (hY : ∀ g, (Y g).val * coordMatrix e₁ = coordMatrix e₁ * ((coordMatrix e₁)ᵀ * (Y g).val *
      coordMatrix e₁)) (hYc : Continuous (restrictScalarsRep b Y)) :
    Continuous (restrictScalarsRep b (h.subRep Y hY)) :=
  continuous_restrictScalarsRep_of_eq_mul b Y _ _ _
    (restrictScalarsMatrix_subRep_val b h Y hY) hYc

/-- Restriction of scalars of a quotient representation along coordinates is continuous. -/
public theorem continuous_restrictScalarsRep_quotRep
    (hY : ∀ g, (coordMatrix e₂)ᵀ * (Y g).val = ((coordMatrix e₂)ᵀ * (Y g).val * coordMatrix e₂) *
      (coordMatrix e₂)ᵀ) (hYc : Continuous (restrictScalarsRep b Y)) :
    Continuous (restrictScalarsRep b (h.quotRep Y hY)) :=
  continuous_restrictScalarsRep_of_eq_mul b Y _ _ _
    (restrictScalarsMatrix_quotRep_val b h Y hY) hYc

end Res

section Integral

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type*} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {G : Type*} [Group G] {r a c : ℕ} {e₁ : Fin a → Fin r}
  {e₂ : Fin c → Fin r}
  (h : IsSplitting (coordMatrix (R := E) e₁) (coordMatrix e₁)ᵀ (coordMatrix e₂)ᵀ (coordMatrix e₂))
  (Y : G →* GL (Fin r) E)

/-- The integral coordinate inclusion intertwines `Res_b Y` with `Res_b` of the
sub-representation. -/
public theorem restrictScalarsRep_mul_coordMatrix_map
    (hY : ∀ g, (Y g).val * coordMatrix e₁ = coordMatrix e₁ * ((coordMatrix e₁)ᵀ * (Y g).val *
      coordMatrix e₁)) (g : G) :
    (restrictScalarsRep b Y g).val *
      (coordMatrix (R := ℤ_[ℓ]) (resIndex (d := d) e₁)).map (PadicInt.Coe.ringHom (p := ℓ)) =
      (coordMatrix (R := ℤ_[ℓ]) (resIndex (d := d) e₁)).map (PadicInt.Coe.ringHom (p := ℓ)) *
        (restrictScalarsRep b (h.subRep Y hY) g).val := by
  rw [coordMatrix_map, restrictScalarsRep_val, restrictScalarsRep_val,
    ← restrictScalarsMatrix_coordMatrix b, ← restrictScalarsMatrix_mul,
    ← restrictScalarsMatrix_mul, IsSplitting.subRep_val, ← hY g]

/-- The integral coordinate projection intertwines `Res_b Y` with `Res_b` of the quotient
representation. -/
public theorem coordMatrix_transpose_map_mul_restrictScalarsRep
    (hY : ∀ g, (coordMatrix e₂)ᵀ * (Y g).val = ((coordMatrix e₂)ᵀ * (Y g).val * coordMatrix e₂) *
      (coordMatrix e₂)ᵀ) (g : G) :
    ((coordMatrix (R := ℤ_[ℓ]) (resIndex (d := d) e₂))ᵀ).map (PadicInt.Coe.ringHom (p := ℓ)) *
        (restrictScalarsRep b Y g).val =
      (restrictScalarsRep b (h.quotRep Y hY) g).val *
        ((coordMatrix (R := ℤ_[ℓ]) (resIndex (d := d) e₂))ᵀ).map
          (PadicInt.Coe.ringHom (p := ℓ)) := by
  rw [Matrix.transpose_map, coordMatrix_map, restrictScalarsRep_val, restrictScalarsRep_val,
    ← restrictScalarsMatrix_transpose_coordMatrix b, ← restrictScalarsMatrix_mul,
    ← restrictScalarsMatrix_mul, IsSplitting.quotRep_val, ← hY g]

end Integral

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)

/-- **Weights of `Res_b Y` by dévissage along the grading.**  Let `Pc` be a property of families
of polynomials over `E` (indexed by `Ys`, through `Fr : Ys → π₁(X, x̄)`) which holds for the
constant family `1`.  Suppose the bound `q, ι, w` holds on `Hⁱ_c(X_k̄, ℱ_{Res_b Y'} ⊗ ℚ_ℓ)` for
every `Y'` whose Frobenius characteristic polynomials satisfy `Pc`, that all the cohomology groups
in sight are finite (rationally, and at every finite level).  Then it holds for every
graded upper-triangular `Y` each of whose diagonal blocks satisfies `Pc`. -/
public theorem isCharpolyNormMixedOfWeightLE_restrictScalarsRep_of_isGradedUpper
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) (i : ℤ)
    {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ} {Ys : Type*} (Fr : Ys → EtaleFundamentalGroup X.1 x)
    (Pc : (Ys → Polynomial E) → Prop) (hPc : Pc fun _ => 1)
    (hFD : ∀ {N : ℕ} (τ : EtaleFundamentalGroup X.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ),
      FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
        kbar (LAdicSheaf.representationSheaf B X x τ hτ) i))
    (hfin : ∀ {N : ℕ} (τ : EtaleFundamentalGroup X.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ)
      (m : ℕ), Finite ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) m)))
    (hbase : ∀ {m : ℕ} (Y' : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
      (hY' : Continuous (restrictScalarsRep b Y'))
      [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
        kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b Y') hY') i)],
      Pc (fun y => (Y' (Fr y)).val.charpoly) →
      IsCharpolyNormMixedOfWeightLE q ι w
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b Y') hY') i).hom) :
    ∀ (m : ℕ) (Y : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (δ : Fin m → ℤ)
      (_ : ∀ g, IsGradedUpper δ (Y g).val) (hY : Continuous (restrictScalarsRep b Y))
      (_ : ∀ t, Pc fun y => ((Y (Fr y)).val.toSquareBlock δ t).charpoly),
      ∃ _ : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
        f j kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b Y) hY) i),
      IsCharpolyNormMixedOfWeightLE q ι w
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b Y) hY) i).hom := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro Y δ hup hY hblk
  have := hFD (restrictScalarsRep b Y) hY
  refine ⟨inferInstance, ?_⟩
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · exact hbase Y hY (by simpa only [charpoly_isEmpty] using hPc)
  obtain ⟨i₀, ht₀⟩ := Finite.exists_min δ
  obtain ⟨a, e₁, he₁, hre₁⟩ := exists_injective_forall_iff_exists fun i => δ i = δ i₀
  obtain ⟨c, e₂, he₂, hre₂⟩ := exists_injective_forall_iff_exists fun i => δ i ≠ δ i₀
  have hdisj : ∀ j j', e₁ j ≠ e₂ j' := fun j j' h =>
    (hre₂ (e₂ j')).2 ⟨j', rfl⟩ (h ▸ (hre₁ (e₁ j)).2 ⟨j, rfl⟩)
  have hcov : ∀ i, (∃ j, e₁ j = i) ∨ ∃ j, e₂ j = i := fun i =>
    (em (δ i = δ i₀)).imp (hre₁ i).1 (hre₂ i).1
  have hc : c < m := by
    simpa using Fintype.card_lt_of_injective_of_notMem e₂ he₂ (b := i₀)
      fun ⟨j, hj⟩ => (hre₂ i₀).2 ⟨j, hj⟩ rfl
  have hsE := isSplitting_coordMatrix (R := E) he₁ he₂ hdisj hcov
  have hst := fun g => hsE.stable_of_comp_eq_zero
    (transpose_coordMatrix_mul_mul_coordMatrix_eq_zero_of_isGradedUpper (hup g) fun j j' =>
      Eq.trans_lt ((hre₁ _).2 ⟨j', rfl⟩) (lt_of_le_of_ne (ht₀ _) (Ne.symm ((hre₂ _).2 ⟨j, rfl⟩))))
  set α := hsE.subRep Y (fun g => (hst g).1)
  set γ := hsE.quotRep Y (fun g => (hst g).2)
  have hαv : ∀ g, (α g).val = (Y g).val.submatrix e₁ e₁ := fun g =>
    (IsSplitting.subRep_val _ _ _ _).trans (transpose_coordMatrix_mul_mul_coordMatrix (Y g).val)
  have hγv : ∀ g, (γ g).val = (Y g).val.submatrix e₂ e₂ := fun g =>
    (IsSplitting.quotRep_val _ _ _ _).trans (transpose_coordMatrix_mul_mul_coordMatrix (Y g).val)
  have hα : Continuous (restrictScalarsRep b α) := continuous_restrictScalarsRep_subRep b hsE Y _ hY
  have hγ : Continuous (restrictScalarsRep b γ) :=
    continuous_restrictScalarsRep_quotRep b hsE Y _ hY
  have hαP : Pc fun y => (α (Fr y)).val.charpoly := by
    simpa only [hαv, charpoly_submatrix_eq_charpoly_toSquareBlock _ δ _ he₁ hre₁] using hblk (δ i₀)
  have hγP : ∀ t, Pc fun y => ((γ (Fr y)).val.toSquareBlock (δ ∘ e₂) t).charpoly := fun t => by
    simpa only [hγv] using
      forall_charpoly_toSquareBlock_submatrix Pc hPc (fun y => (Y (Fr y)).val) he₂ hre₂ hblk t
  obtain ⟨hγd, hγw⟩ := ih c hc γ (δ ∘ e₂)
    (fun g j' j'' h => by rw [hγv]; exact hup g _ _ h) hγ hγP
  have := hFD _ hα
  exact isCharpolyNormMixedOfWeightLE_representationSheaf_of_isSplitting B X x f j kbar p n hcard
    (isSplitting_coordMatrix_resIndex (R := ℤ_[ℓ]) (d := d) he₁ he₂ hdisj hcov) hY hα hγ
    (restrictScalarsRep_mul_coordMatrix_map b hsE Y _)
    (coordMatrix_transpose_map_mul_restrictScalarsRep b hsE Y _) i (hfin _ hα) (hbase α hα hαP)
    hγw

end Stacks.EtaleCohomology

end
