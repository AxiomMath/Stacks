module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingValuation

/-!
# Integral models over the integers of an extension of the field of coefficients

Let `E` be a finite extension of `ℚ_ℓ`, `L` a field extension of `E`, and `σ : G → GL_m(E)` a
representation of a compact group whose restriction of scalars along a `ℚ_ℓ`-basis of `E` is
continuous. The model `σ'` of `σ` over the integers `O_E` (`Stacks.EtaleCohomology.modelRep`) is
the matrix of `σ` in a basis `T` of a `σ`-stable `O_E`-lattice; pushed along `O_E → O_L` it is an
integral model of `σ ⊗_E L` over the integers `O_L` of `L`, conjugate to `σ` by the image of `T`
(`Stacks.EtaleCohomology.exists_padicIntegerRing_model`). Its reductions modulo `ℓⁿ` have open
kernels: if the restriction of scalars of `σ'(g)` along a `ℤ_ℓ`-basis of `O_E` is congruent to `1`
modulo `ℓⁿ` (an open condition, that restriction of scalars being continuous), then so is `σ'(g)`
itself (`Stacks.EtaleCohomology.sub_one_mem_map_of_coefficientMatrixRingHom`).

This supplies the coefficient-ring side of piece L6 of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), where the level dichotomy of the Fourier
transform is run with coefficients `O_L / ℓᴺ⁺¹` for finite extensions `L` of `E`.

## Main definitions

* `Stacks.EtaleCohomology.padicIntegerRingMap`: the ring map `O_E → O_L`.

## Main results

* `Stacks.EtaleCohomology.mem_map_of_leftMulMatrix_mem`: an element whose multiplication matrix
  has entries in an ideal `I` lies in `I O`.
* `Stacks.EtaleCohomology.sub_one_mem_map_of_coefficientMatrixRingHom`: a matrix whose restriction
  of scalars is congruent to `1` modulo `I` is congruent to `1` modulo `I O`.
* `Stacks.EtaleCohomology.exists_padicIntegerRing_model`: an integral model of `σ ⊗_E L` over
  `O_L`, conjugate to `σ`, whose reductions modulo `ℓⁿ` have open kernels.

## References

* [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Module Matrix

namespace Stacks.EtaleCohomology

section Coefficients

variable {R O : Type*} [CommRing R] [CommRing O] [Algebra R O] {D : ℕ} (β : Basis (Fin D) R O)

/-- **An element whose multiplication matrix has entries in an ideal `I` lies in `I O`.** -/
theorem mem_map_of_leftMulMatrix_mem (I : Ideal R) (x : O)
    (hx : ∀ k l, Algebra.leftMulMatrix β x k l ∈ I) : x ∈ I.map (algebraMap R O) := by
  have hrepr : ∀ k, β.repr x k ∈ I := by
    intro k
    have h := congrFun (Algebra.leftMulMatrix_mulVec_repr β x 1) k
    rw [mul_one] at h
    rw [← h, Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx k l)
  rw [← β.sum_repr x]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hrepr k))

/-- **A matrix over `O` whose restriction of scalars is congruent to `1` modulo `I` is congruent
to `1` modulo `I O`.** -/
theorem sub_one_mem_map_of_coefficientMatrixRingHom (I : Ideal R) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) O)
    (hM : ∀ p q,
      coefficientMatrixRingHom β m M p q - (1 : Matrix (Fin (m * D)) (Fin (m * D)) R) p q ∈ I)
    (i j : Fin m) :
    M i j - (1 : Matrix (Fin m) (Fin m) O) i j ∈ I.map (algebraMap R O) := by
  refine mem_map_of_leftMulMatrix_mem β I _ fun k l => ?_
  have h := hM (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l))
  have h1 : (1 : Matrix (Fin (m * D)) (Fin (m * D)) R) = coefficientMatrixRingHom β m 1 :=
    (map_one _).symm
  rwa [h1, ← Matrix.sub_apply, ← map_sub, coefficientMatrixRingHom_apply, Matrix.sub_apply] at h

end Coefficients

attribute [local instance] padicIntAlgebraOfRat

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Map

variable (ℓ) (E L : Type) [Field E] [Algebra ℚ_[ℓ] E] [Field L] [Algebra E L] [Algebra ℚ_[ℓ] L]
  [IsScalarTower ℚ_[ℓ] E L]

/-- `ℤ_ℓ → E → L` is a scalar tower for the `ℤ_ℓ`-algebra structures through `ℚ_ℓ`. -/
theorem isScalarTower_padicInt_padicIntAlgebraOfRat : IsScalarTower ℤ_[ℓ] E L :=
  IsScalarTower.of_algebraMap_eq fun z => by
    change algebraMap ℚ_[ℓ] L (algebraMap ℤ_[ℓ] ℚ_[ℓ] z) =
      algebraMap E L (algebraMap ℚ_[ℓ] E (algebraMap ℤ_[ℓ] ℚ_[ℓ] z))
    exact IsScalarTower.algebraMap_apply ℚ_[ℓ] E L _

/-- **The ring map `O_E → O_L`** between the integers of `E` and of an extension `L` of `E`. -/
def padicIntegerRingMap : integralClosure ℤ_[ℓ] E →+* integralClosure ℤ_[ℓ] L :=
  haveI := isScalarTower_padicInt_padicIntAlgebraOfRat ℓ E L
  ((algebraMap E L).comp (integralClosure ℤ_[ℓ] E).val.toRingHom).codRestrict
    (integralClosure ℤ_[ℓ] L) fun x =>
      (mem_integralClosure_iff _ _).2 (x.2.map (IsScalarTower.toAlgHom ℤ_[ℓ] E L))

/-- The image of `x` under `padicIntegerRingMap` is `algebraMap E L x`, as an element of `L`. -/
@[simp]
theorem padicIntegerRingMap_apply (x : integralClosure ℤ_[ℓ] E) :
    (padicIntegerRingMap ℓ E L x : L) = algebraMap E L x :=
  rfl

/-- `padicIntegerRingMap` sends the natural number `k` to `k`. -/
theorem padicIntegerRingMap_natCast (k : ℕ) :
    padicIntegerRingMap ℓ E L (k : integralClosure ℤ_[ℓ] E) = k :=
  map_natCast _ k

end Map

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
  (b : Basis (Fin d) ℚ_[ℓ] E) (L : Type) [Field L] [Algebra E L] [Algebra ℚ_[ℓ] L]
  [IsScalarTower ℚ_[ℓ] E L]

/-- **The reductions modulo `ℓⁿ` of the model of `σ` over `O_E`, pushed to `O_L`, have open
kernels.** -/
private theorem isOpen_ker_map_padicIntegerRingMap_modelRep {m : ℕ} (σ : G →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (n : ℕ) :
    IsOpen (((GeneralLinearGroup.map (Ideal.Quotient.mk
      (Ideal.span {((ℓ : ℕ) : integralClosure ℤ_[ℓ] L) ^ n}))).comp
      ((GeneralLinearGroup.map (padicIntegerRingMap ℓ E L)).comp (modelRep b σ hσ))).ker :
        Set G) := by
  classical
  set ι := padicIntegerRingMap ℓ E L
  set σ' := modelRep b σ hσ
  let U : Set G := ⋂ p, ⋂ q, {g | PadicInt.toZModPow n
      ((modelRestrictScalarsRep b σ hσ g).val p q) =
    PadicInt.toZModPow n ((1 : Matrix (Fin (m * d)) (Fin (m * d)) ℤ_[ℓ]) p q)}
  have hU : IsOpen U := isOpen_iInter_of_finite fun p => isOpen_iInter_of_finite fun q =>
    (isOpen_setOf_toZModPow_eq n _).preimage
      ((Units.continuous_val.comp (continuous_modelRestrictScalarsRep b σ hσ)).matrix_elem p q)
  have h1U : (1 : G) ∈ U := by simp [U]
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1U) fun g hg => ?_)
  have hent : ∀ i j, (σ' g).val i j - (1 : Matrix (Fin m) (Fin m) (integralClosure ℤ_[ℓ] E)) i j ∈
      Ideal.span {((ℓ : ℕ) : integralClosure ℤ_[ℓ] E) ^ n} := by
    intro i j
    have h := sub_one_mem_map_of_coefficientMatrixRingHom (padicIntegerRingBasisOf b)
      (Ideal.span {((ℓ : ℕ) : ℤ_[ℓ]) ^ n}) (σ' g).val (fun p q => by
        rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
        exact Set.mem_iInter.1 (Set.mem_iInter.1 hg p) q) i j
    simpa [Ideal.map_span] using h
  rw [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, Units.val_one]
  change ((σ' g).val.map ι).map (Ideal.Quotient.mk _) = 1
  ext i j
  have h1 : (1 : Matrix (Fin m) (Fin m)
      (integralClosure ℤ_[ℓ] L ⧸ Ideal.span {((ℓ : ℕ) : integralClosure ℤ_[ℓ] L) ^ n})) i j =
      Ideal.Quotient.mk _ (ι ((1 : Matrix (Fin m) (Fin m) (integralClosure ℤ_[ℓ] E)) i j)) := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [Matrix.map_apply, Matrix.map_apply, h1, Ideal.Quotient.eq, ← map_sub]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hent i j)
  exact Ideal.mem_span_singleton'.2 ⟨ι c, by rw [← hc, map_mul, map_pow, map_natCast]⟩

/-- **An integral model of `σ ⊗_E L` over the integers of `L`, with open kernels at every
level.** For a representation `σ : G → GL_m(E)` of a compact group with `Res_b σ` continuous and an
extension `L` of `E`, there are `σ_O : G → GL_m(O_L)` and `T ∈ GL_m(L)` with
`σ_O(g) = T⁻¹ σ(g) T` for all `g`, and the reduction of `σ_O` modulo `ℓⁿ` has an open kernel for
every `n`. -/
theorem exists_padicIntegerRing_model {m : ℕ} (σ : G →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) :
    ∃ (σO : G →* GL (Fin m) (integralClosure ℤ_[ℓ] L)) (T : GL (Fin m) L),
      (∀ g, (σO g).val.map (algebraMap (integralClosure ℤ_[ℓ] L) L) =
          (T⁻¹ : GL (Fin m) L).val * (σ g).val.map (algebraMap E L) * T.val) ∧
      ∀ n : ℕ, IsOpen (((GeneralLinearGroup.map (Ideal.Quotient.mk
        (Ideal.span {((ℓ : ℕ) : integralClosure ℤ_[ℓ] L) ^ n}))).comp σO).ker : Set G) := by
  classical
  set ι := padicIntegerRingMap ℓ E L
  set σ' := modelRep b σ hσ
  set v := modelBasisE b σ hσ
  set std := Pi.basisFun E (Fin m)
  set A := std.toMatrix v
  set A' := v.toMatrix std
  let f := algebraMap E L
  have hinv : ∀ X Y : Matrix (Fin m) (Fin m) E, X * Y = 1 → X.map f * Y.map f = 1 := fun X Y h => by
    simp [← Matrix.map_mul, h]
  let T : GL (Fin m) L := ⟨A.map f, A'.map f, hinv _ _ (Basis.toMatrix_mul_toMatrix_flip std v),
    hinv _ _ (Basis.toMatrix_mul_toMatrix_flip v std)⟩
  have hconj : ∀ g, (σ' g).val.map (algebraMap (integralClosure ℤ_[ℓ] E) E) =
      A' * (σ g).val * A := by
    intro g
    rw [map_modelRep, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := v)
      (b' := std) (c := v) (c' := std), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  refine ⟨(GeneralLinearGroup.map ι).comp σ', T, fun g => ?_,
    isOpen_ker_map_padicIntegerRingMap_modelRep b L σ hσ⟩
  change ((σ' g).val.map ι).map (algebraMap (integralClosure ℤ_[ℓ] L) L) = A'.map f * _ * A.map f
  rw [Matrix.map_map, show (algebraMap (integralClosure ℤ_[ℓ] L) L) ∘ ι =
      f ∘ (algebraMap (integralClosure ℤ_[ℓ] E) E) from rfl, ← Matrix.map_map, hconj,
    Matrix.map_mul, Matrix.map_mul]

end Stacks.EtaleCohomology

end
