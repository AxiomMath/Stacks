module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOrigin

/-!
# The self-product of the chart of the twisted doubled origin splits

For a degree two Galois extension `K/k` with nonidentity automorphism `σ`, the ring
`K ⊗[k] K` is `K × K`, the two factors being multiplication and multiplication twisted by
`σ`.  Tensoring with `k[x]` turns this into a splitting
`K[x] ⊗[k[x]] K[x] ≃ K[x] × K[x]`, and on spectra into

    `U ×_S U ≅ U ⨿ U`,  `U = Spec K[x]`, `S = Spec k[x]`,

whose first summand is the diagonal `Δ(U)` and whose second summand is the twisted diagonal
`Δ' = (1, σ)`.  This is the decomposition the twisted doubled origin is built from.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.quadraticTensorProductSplit` splits `K ⊗[k] K` as
  `K × K`.
* `AlgebraicGeometry.TwistedDoubledOrigin.polynomialCoefficientEquiv` identifies `K[x]` with
  `k[x] ⊗[k] K` as a `k[x]`-algebra, and
  `AlgebraicGeometry.TwistedDoubledOrigin.polynomialFiberProductTensorSplit` splits
  `K[x] ⊗[k[x]] K[x]` as `K[x] × K[x]`.
* `AlgebraicGeometry.TwistedDoubledOrigin.polynomialGaloisAlgHom` is `σ` acting on
  coefficients, and
  `AlgebraicGeometry.TwistedDoubledOrigin.polynomialTensorSplitMap` is the pair of the
  identity and that action, the map which the splitting turns out to be.
* `AlgebraicGeometry.TwistedDoubledOrigin.coverFiberProductSplitIso` is the resulting
  isomorphism `U ×_S U ≅ U ⨿ U`.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin`
  `.polynomialFiberProductTensorSplit_eq_polynomialTensorSplitMap` computes the splitting:
  it is the pair of the identity and the Galois action.
* `AlgebraicGeometry.TwistedDoubledOrigin.coverFiberProductSplitIso_inl` says that the
  first summand of `U ⨿ U` is the diagonal, and
  `AlgebraicGeometry.TwistedDoubledOrigin.coverFiberProductSplitIso_inr_fst`,
  `AlgebraicGeometry.TwistedDoubledOrigin.coverFiberProductSplitIso_inr_snd` say that the
  second summand is the graph of the Galois automorphism.
* `AlgebraicGeometry.TwistedDoubledOrigin.coverFiberProductSplitIso_second_factor`
  identifies the second projection of `U ×_S U` on the two summands at once.

## Implementation notes

`Polynomial.algebra`, which makes `K[x]` a `k[x]`-algebra, is not a global instance because
it would form a diamond with the coefficient-wise algebra structure; it is made a local
instance here, which is what lets the tensor product `K[x] ⊗[k[x]] K[x]` be written at all.

The splitting of `K ⊗[k] K` is constructed from the idempotent cutting out the twisted
factor: the pair of multiplication and `σ`-twisted multiplication is surjective because that
idempotent is in its image, and it is injective because source and target have the same
`K`-dimension, which is where the degree hypothesis enters.  The splitting of
`K[x] ⊗[k[x]] K[x]` is then obtained by base change, and identified with the explicit pair
map on monomials; every subsequent computation goes through that identification rather than
through the chain of base-change isomorphisms.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

attribute [local instance] Polynomial.algebra

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The polynomial ring over an extension field is the base change of the polynomial ring
over the ground field, as an algebra over the latter. -/
def polynomialCoefficientEquiv :
    Polynomial K ≃ₐ[Polynomial k] (TensorProduct k (Polynomial k) K) := by
  let e₀ := (polyEquivTensor k K).trans (Algebra.TensorProduct.comm k K (Polynomial k))
  let f₀ : Polynomial k →ₐ[k] Polynomial K := Polynomial.mapAlgHom (Algebra.ofId k K)
  let g₀ : Polynomial k →ₐ[k] TensorProduct k (Polynomial k) K :=
    (Algebra.TensorProduct.includeLeft :
      Polynomial k →ₐ[k] TensorProduct k (Polynomial k) K)
  have hbaseMap : e₀.toAlgHom.comp f₀ = g₀ := by
    apply Polynomial.algHom_ext
    simp [e₀, f₀, g₀, polyEquivTensor_apply]
  have he : ∀ p : Polynomial k,
      e₀ (algebraMap (Polynomial k) (Polynomial K) p) =
        algebraMap (Polynomial k) (TensorProduct k (Polynomial k) K) p := fun p => by
    simpa [f₀, g₀, Polynomial.algebraMap_def] using AlgHom.congr_fun hbaseMap p
  exact AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) he

/-- **Stacks 03FN.** For a degree two Galois extension with nonidentity automorphism `σ`,
the ring `K ⊗[k] K` is `K × K`, the two factors being multiplication and multiplication
twisted by `σ`. -/
def quadraticTensorProductSplit [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    K ⊗[k] K ≃ₐ[K] K × K := by
  let φ : K ⊗[k] K →ₐ[K] K × K := Algebra.TensorProduct.lift
    (Algebra.ofId K (K × K)) (AlgHom.prod (AlgHom.id k K) σ.toAlgHom)
    (fun _ _ => Commute.all _ _)
  have hx : ∃ x : K, σ x ≠ x := by
    by_contra! h
    exact hσ (AlgEquiv.ext h)
  classical
  let x := Classical.choose hx
  have hx : σ x ≠ x := Classical.choose_spec hx
  let e : K ⊗[k] K := algebraMap K (K ⊗[k] K) ((σ x - x)⁻¹) *
    ((1 : K) ⊗ₜ[k] x - (x : K) ⊗ₜ[k] (1 : K))
  have he : φ e = (0, 1) := by
    apply Prod.ext
    · simp [e, φ, Algebra.TensorProduct.lift_tmul, AlgHom.prod_apply]
    · have hplus : σ x + -x ≠ 0 := by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hx
      simp [e, φ, Algebra.TensorProduct.lift_tmul, AlgHom.prod_apply, sub_eq_add_neg, hplus]
  have hsurj : Function.Surjective φ := by
    intro z
    refine ⟨algebraMap K (K ⊗[k] K) z.1 * (1 - e) + algebraMap K (K ⊗[k] K) z.2 * e, ?_⟩
    ext <;> simp [φ, he]
  have hdim : Module.finrank K (K ⊗[k] K) = Module.finrank K (K × K) := by
    rw [Module.finrank_tensorProduct, Module.finrank_prod, hdegree]
    simp
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  exact AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩

/-- The splitting `K ⊗[k] K ≃ K × K` sends `a ⊗ₜ b` to `(a * b, a * σ b)`. -/
@[simp]
lemma quadraticTensorProductSplit_tmul [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (a b : K) :
    quadraticTensorProductSplit k K hdegree σ hσ (a ⊗ₜ[k] b) = (a * b, a * σ b) := by
  change (Algebra.TensorProduct.lift (Algebra.ofId K (K × K))
    (AlgHom.prod (AlgHom.id k K) σ.toAlgHom) (fun _ _ => Commute.all _ _)) (a ⊗ₜ[k] b) = _
  simp [Algebra.TensorProduct.lift_tmul, AlgHom.prod_apply]

/-- **Stacks 03FN.** The splitting of `K[x] ⊗[k[x]] K[x]` as `K[x] × K[x]`, obtained from
the splitting of `K ⊗[k] K` by base change along `k ⟶ k[x]`. -/
def polynomialFiberProductTensorSplit [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    Polynomial K ⊗[Polynomial k] Polynomial K ≃ₐ[Polynomial K]
      Polynomial K × Polynomial K := by
  let c := polynomialCoefficientEquiv k K
  let e1 := Algebra.TensorProduct.congr
    (R := Polynomial k) (S := Polynomial K) (A := Polynomial K) (B := Polynomial K)
    (C := Polynomial K) (D := Polynomial k ⊗[k] K)
    (AlgEquiv.refl (R := Polynomial K) (A₁ := Polynomial K)) c
  let e2 := Algebra.TensorProduct.cancelBaseChange k (Polynomial k)
    (Polynomial K) (Polynomial K) K
  let e3 := (Algebra.TensorProduct.cancelBaseChange k K
    (Polynomial K) (Polynomial K) K).symm
  let e4 := Algebra.TensorProduct.congr
    (R := K) (S := Polynomial K) (A := Polynomial K) (B := K ⊗[k] K)
    (C := Polynomial K) (D := K × K)
    (AlgEquiv.refl (R := Polynomial K) (A₁ := Polynomial K))
    (quadraticTensorProductSplit k K hdegree σ hσ)
  let e5 := Algebra.TensorProduct.prodRight K (Polynomial K) (Polynomial K) K K
  let e6 := AlgEquiv.prodCongr
    (Algebra.TensorProduct.rid K (Polynomial K) (Polynomial K))
    (Algebra.TensorProduct.rid K (Polynomial K) (Polynomial K))
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))

/-- A Galois automorphism of the extension acting on coefficients, as an algebra map over
the polynomial ring of the ground field. -/
def polynomialGaloisAlgHom (σ : K ≃ₐ[k] K) : Polynomial K →ₐ[Polynomial k] Polynomial K where
  toRingHom := Polynomial.mapRingHom σ.toRingEquiv.toRingHom
  commutes' := by
    intro p
    change Polynomial.map σ.toRingEquiv.toRingHom
      (Polynomial.map (algebraMap k K) p) = Polynomial.map (algebraMap k K) p
    rw [Polynomial.map_map]
    congr 1
    ext x
    exact σ.commutes x

/-- The pair of the identity and the coefficientwise Galois action, as a `K[x]`-algebra map
out of `K[x] ⊗[k[x]] K[x]`. -/
def polynomialTensorSplitMap (σ : K ≃ₐ[k] K) :
    Polynomial K ⊗[Polynomial k] Polynomial K →ₐ[Polynomial K]
      Polynomial K × Polynomial K :=
  Algebra.TensorProduct.lift (Algebra.ofId (Polynomial K) (Polynomial K × Polynomial K))
    (AlgHom.prod (AlgHom.id (Polynomial k) (Polynomial K)) (polynomialGaloisAlgHom k K σ))
    (fun _ _ => Commute.all _ _)

/-- The splitting of `K[x] ⊗[k[x]] K[x]` is the pair of the identity and the coefficientwise
Galois action. -/
theorem polynomialFiberProductTensorSplit_eq_polynomialTensorSplitMap
    [FiniteDimensional k K] [IsGalois k K] (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (polynomialFiberProductTensorSplit k K hdegree σ hσ).toAlgHom =
      polynomialTensorSplitMap k K σ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply AlgHom.ext
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial n a =>
        simp [polynomialFiberProductTensorSplit, polynomialTensorSplitMap,
          polynomialCoefficientEquiv, polyEquivTensor_apply,
          Algebra.TensorProduct.cancelBaseChange_symm_tmul,
          quadraticTensorProductSplit_tmul, Algebra.TensorProduct.prodRight_tmul,
          Algebra.smul_def, Polynomial.C_mul_X_pow_eq_monomial, polynomialGaloisAlgHom,
          Polynomial.map_monomial]

/-- The first component of the pair map, namely multiplication in `K[x]`. -/
def polynomialTensorSplitFirstMap :
    Polynomial K ⊗[Polynomial k] Polynomial K →ₐ[Polynomial K] Polynomial K :=
  Algebra.TensorProduct.lift (AlgHom.id (Polynomial K) (Polynomial K))
    (AlgHom.id (Polynomial k) (Polynomial K)) (fun _ _ => Commute.all _ _)

/-- The first component of `polynomialTensorSplitMap` is `polynomialTensorSplitFirstMap`. -/
lemma polynomialTensorSplitMap_fst (σ : K ≃ₐ[k] K) :
    (AlgHom.fst (Polynomial K) (Polynomial K) (Polynomial K)).comp
      (polynomialTensorSplitMap k K σ) = polynomialTensorSplitFirstMap k K := by
  apply Algebra.TensorProduct.ext
  · simp [polynomialTensorSplitMap, polynomialTensorSplitFirstMap, AlgHom.comp_assoc]
  · change (AlgHom.restrictScalars (Polynomial k)
        (AlgHom.fst (Polynomial K) (Polynomial K) (Polynomial K))).comp
      ((AlgHom.restrictScalars (Polynomial k)
          (polynomialTensorSplitMap k K σ)).comp Algebra.TensorProduct.includeRight) = _
    ext x
    rfl

variable [FiniteDimensional k K] [IsGalois k K]

/-- The splitting of `K[x] ⊗[k[x]] K[x]`, evaluated at an element, is the pair map. -/
private lemma polynomialFiberProductTensorSplit_apply (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (x : Polynomial K ⊗[Polynomial k] Polynomial K) :
    polynomialFiberProductTensorSplit k K hdegree σ hσ x = polynomialTensorSplitMap k K σ x :=
  DFunLike.congr_fun
    (polynomialFiberProductTensorSplit_eq_polynomialTensorSplitMap k K hdegree σ hσ) x

/-- The first component of the splitting restricts to the identity on the left factor. -/
lemma polynomialTensorSplitFirst_includeLeft (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (RingHom.fst (Polynomial K) (Polynomial K)).comp
      ((polynomialFiberProductTensorSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : Polynomial K →+*
          Polynomial K ⊗[Polynomial k] Polynomial K)) = RingHom.id _ := by
  apply RingHom.ext
  intro p
  change (polynomialFiberProductTensorSplit k K hdegree σ hσ
    (Algebra.TensorProduct.includeLeftRingHom p)).1 = p
  rw [polynomialFiberProductTensorSplit_apply]
  simp [polynomialTensorSplitMap, Algebra.TensorProduct.lift_tmul, AlgHom.prod_apply,
    polynomialGaloisAlgHom]

/-- The first component of the splitting restricts to the identity on the right factor. -/
lemma polynomialTensorSplitFirst_includeRight (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (RingHom.fst (Polynomial K) (Polynomial K)).comp
      ((polynomialFiberProductTensorSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeRight.toRingHom : Polynomial K →+*
          Polynomial K ⊗[Polynomial k] Polynomial K)) = RingHom.id _ := by
  apply RingHom.ext
  intro p
  change (polynomialFiberProductTensorSplit k K hdegree σ hσ
    (Algebra.TensorProduct.includeRight p)).1 = p
  rw [polynomialFiberProductTensorSplit_apply]
  simp [polynomialTensorSplitMap, Algebra.TensorProduct.lift_tmul, AlgHom.prod_apply,
    polynomialGaloisAlgHom]

/-- The second component of the splitting restricts to the identity on the left factor. -/
lemma polynomialTensorSplitSecond_includeLeft (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (RingHom.snd (Polynomial K) (Polynomial K)).comp
      ((polynomialFiberProductTensorSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
        Algebra.TensorProduct.includeLeftRingHom) = RingHom.id _ := by
  apply RingHom.ext
  intro p
  change (polynomialFiberProductTensorSplit k K hdegree σ hσ
    (Algebra.TensorProduct.includeLeftRingHom p)).2 = p
  rw [polynomialFiberProductTensorSplit_apply]
  simp [polynomialTensorSplitMap, Algebra.TensorProduct.lift_tmul, AlgHom.prod_apply,
    polynomialGaloisAlgHom]

/-- The second component of the splitting restricts to the Galois action on the right
factor: the second summand of the self-product is the twisted diagonal. -/
lemma polynomialTensorSplitSecond_includeRight (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (RingHom.snd (Polynomial K) (Polynomial K)).comp
      ((polynomialFiberProductTensorSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom) =
      Polynomial.mapRingHom σ.toRingEquiv.toRingHom := by
  apply RingHom.ext
  intro p
  change (polynomialFiberProductTensorSplit k K hdegree σ hσ
    (Algebra.TensorProduct.includeRight p)).2 =
      Polynomial.mapRingHom σ.toRingEquiv.toRingHom p
  rw [polynomialFiberProductTensorSplit_apply]
  simp [polynomialTensorSplitMap, Algebra.TensorProduct.lift_tmul, AlgHom.prod_apply,
    polynomialGaloisAlgHom]

/-- The splitting of the self-product of the chart, on spectra. -/
def coverTensorSplitSpecIso (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    Spec (.of (Polynomial K ⊗[Polynomial k] Polynomial K)) ≅
      Spec (.of (Polynomial K × Polynomial K)) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (polynomialFiberProductTensorSplit k K hdegree σ hσ).symm.toRingEquiv).op

/-- **Stacks 03FN.** The self-product of the chart over the base is the disjoint union of
two copies of the chart, the diagonal and the twisted diagonal. -/
def coverFiberProductSplitIso (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) : pullback (coverMap k K) (coverMap k K) ≅ cover K ⨿ cover K :=
  (AlgebraicGeometry.pullbackSpecIso (Polynomial k) (Polynomial K) (Polynomial K)).trans
    ((coverTensorSplitSpecIso k K hdegree σ hσ).trans
      (asIso (AlgebraicGeometry.coprodSpec (Polynomial K) (Polynomial K))).symm)

/-- Composing the inverse of the splitting with a map out of the coproduct and a projection of
the pullback is `Spec.map` of the corresponding composite of ring maps. -/
private lemma coprod_comp_splitIso_inv_comp_eq (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (i : cover K ⟶ cover K ⨿ cover K)
    (P : pullback (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (Polynomial K))))
      (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (Polynomial K)))) ⟶ cover K)
    (c : Polynomial K × Polynomial K →+* Polynomial K)
    (ι : Polynomial K →+* Polynomial K ⊗[Polynomial k] Polynomial K)
    (r : Polynomial K →+* Polynomial K)
    (hi : i ≫ AlgebraicGeometry.coprodSpec (Polynomial K) (Polynomial K) =
      Spec.map (CommRingCat.ofHom c))
    (hP : (AlgebraicGeometry.pullbackSpecIso (Polynomial k) (Polynomial K) (Polynomial K)).inv ≫
      P = Spec.map (CommRingCat.ofHom ι))
    (hr : c.comp ((polynomialFiberProductTensorSplit k K hdegree σ hσ).toRingEquiv.toRingHom.comp
      ι) = r) :
    i ≫ (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫ P = Spec.map (CommRingCat.ofHom r) := by
  change (i ≫ AlgebraicGeometry.coprodSpec (Polynomial K) (Polynomial K) ≫
    (coverTensorSplitSpecIso k K hdegree σ hσ).inv ≫
      (AlgebraicGeometry.pullbackSpecIso (Polynomial k) (Polynomial K) (Polynomial K)).inv) ≫
        P = _
  rw [← Category.assoc, hi]
  simp only [Category.assoc, hP, coverTensorSplitSpecIso, Scheme.Spec.mapIso_inv]
  rw [Scheme.Spec_map (f := (RingEquiv.toCommRingCatIso
    (polynomialFiberProductTensorSplit k K hdegree σ hσ).symm.toRingEquiv).op.inv),
    ← Spec.map_comp, ← Spec.map_comp, ← hr]
  rfl

/-- The first summand of the split self-product is the diagonal of the chart. -/
lemma coverFiberProductSplitIso_inl (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    (coprod.inl : cover K ⟶ cover K ⨿ cover K) ≫
      (coverFiberProductSplitIso k K hdegree σ hσ).inv =
        pullback.diagonal (coverMap k K) := by
  apply pullback.hom_ext
  · refine (coprod_comp_splitIso_inv_comp_eq k K hdegree σ hσ _ _ _ _ _
      (AlgebraicGeometry.coprodSpec_inl ..) (AlgebraicGeometry.pullbackSpecIso_inv_fst ..)
      (polynomialTensorSplitFirst_includeLeft k K hdegree σ hσ)).trans ?_
    simp
  · refine (coprod_comp_splitIso_inv_comp_eq k K hdegree σ hσ _ _ _ _ _
      (AlgebraicGeometry.coprodSpec_inl ..) (AlgebraicGeometry.pullbackSpecIso_inv_snd ..)
      (polynomialTensorSplitFirst_includeRight k K hdegree σ hσ)).trans ?_
    simp

/-- The second summand of the split self-product projects to the chart by the identity in
the first coordinate. -/
lemma coverFiberProductSplitIso_inr_fst (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    (coprod.inr : cover K ⟶ cover K ⨿ cover K) ≫
      (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.fst (coverMap k K) (coverMap k K) = 𝟙 (cover K) := by
  refine (coprod_comp_splitIso_inv_comp_eq k K hdegree σ hσ _ _ _ _ _
    (AlgebraicGeometry.coprodSpec_inr ..) (AlgebraicGeometry.pullbackSpecIso_inv_fst ..)
    (polynomialTensorSplitSecond_includeLeft k K hdegree σ hσ)).trans ?_
  simp

/-- The second summand of the split self-product is the graph of the Galois automorphism:
its second coordinate is that automorphism. -/
lemma coverFiberProductSplitIso_inr_snd (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K)
    (hσ : σ ≠ 1) :
    (coprod.inr : cover K ⟶ cover K ⨿ cover K) ≫
      (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.snd (coverMap k K) (coverMap k K) = galoisAction k K σ :=
  coprod_comp_splitIso_inv_comp_eq k K hdegree σ hσ _ _ _ _ _
    (AlgebraicGeometry.coprodSpec_inr ..) (AlgebraicGeometry.pullbackSpecIso_inv_snd ..)
    (polynomialTensorSplitSecond_includeRight k K hdegree σ hσ)

/-- The second projection of the self-product of the chart, read through the splitting: it
is the identity on the diagonal summand and the Galois automorphism on the twisted one. -/
theorem coverFiberProductSplitIso_second_factor (hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) :
    (coverFiberProductSplitIso k K hdegree σ hσ).inv ≫
        pullback.snd (coverMap k K) (coverMap k K) =
      coprod.desc (𝟙 (cover K)) (galoisAction k K σ) := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc, ← Category.assoc, coverFiberProductSplitIso_inl, pullback.diagonal_snd]
  · rw [coprod.inr_desc, coverFiberProductSplitIso_inr_snd]

end AlgebraicGeometry.TwistedDoubledOrigin

end
