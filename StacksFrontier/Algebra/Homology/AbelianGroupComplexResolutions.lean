module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Resolutions of complexes of abelian groups and the product total complex

Let `M^•` be a complex of abelian groups and let `0 → M^• → A_0^• → A_1^• → A_2^• → ⋯` be an
exact complex of complexes of abelian groups such that for every `p ∈ ℤ` the induced complex
`0 → Coker(d_M^p) → Coker(d_{A_0}^p) → Coker(d_{A_1}^p) → ⋯` is exact as well. Setting
`A^{p, q} = A_p^q` gives a double complex, and the map from `M^•` to its product total complex
`Tot_π(A^{•, •})`, with `Tot_π^n = ∏_{p + q = n} A^{p, q}` and differential
`∏_{p + q = n} (f_p^q + (-1)^p d_{A_p}^q)`, is a quasi-isomorphism.

The proof is a diagram chase. The two exactness hypotheses together imply that the rows of
cohomology `0 → H^q(M^•) → H^q(A_0^•) → H^q(A_1^•) → ⋯` are exact. A cocycle of `Tot_π` is first
corrected by the image of a cocycle of `M^•` in its `A^{0, •}`-component, and then shown to be a
coboundary by constructing the components of a primitive one at a time; at each step exactness
of the rows of cohomology is used to modify the component just constructed so that the next one
exists. Injectivity uses the exactness of the cokernel complexes in the first column only.

## Main definitions

* `HomologicalComplex₂.productTotal`: the product total complex `Tot_π(K)` of a double complex
  `K` of abelian groups whose first index runs over `ℕ`.
* `HomologicalComplex₂.toProductTotal`: the map `M^• → Tot_π(K)` induced by a map
  `ε : M^• → K^{0, •}` with `d_1 ∘ ε = 0`.

## Main results

* `HomologicalComplex₂.quasiIso_toProductTotal`: if the augmented complex of complexes
  `0 → M^• → K^{0, •} → K^{1, •} → ⋯` is exact and so are its induced complexes of cokernels
  `Coker(d^p)`, then `M^• → Tot_π(K)` is a quasi-isomorphism.

## Implementation notes

The double complex `A^{p, q} = A_p^q` is a `HomologicalComplex₂` whose first index runs over `ℕ`
(the complex `p ↦ A_p^•` of complexes), and the exact complex `0 → M^• → A_0^• → ⋯` is its
augmentation `CochainComplex.augment` by `M^• → A_0^•`; exactness of a complex of complexes is
exactness in the abelian category of cochain complexes, which is degreewise exactness. The
cokernel `Coker(d^p) = X^{p + 1} / Im(d^p)` is the object of opcycles of `X^•` in degree `p + 1`,
so the exactness of the cokernel complexes for all `p` is the acyclicity, for all `q`, of the
image of the augmented complex under the functor of opcycles in degree `q`.

The term `Tot_π^n` is the product of abelian groups `∏_{p + q = n} K^{p, q}` indexed by the pairs
`(p, q) ∈ ℕ × ℤ` with `p + q = n`, realised as a group of dependent functions.

## References

* [Stacks 09J0](https://stacks.math.columbia.edu/tag/09J0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace HomologicalComplex₂

/-! ### The product total complex -/

section

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ))

/-- The term of degree `n` of the product total complex: `∏_{p + q = n} K^{p, q}`. -/
def productTotalX (n : ℤ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (∀ i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}, (K.X i.1.1).X i.1.2)

/-- The component in `K^{p, q}` of the differential of the product total complex. -/
def productTotalDComp (n : ℤ) (x : K.productTotalX n) :
    (p : ℕ) → (q : ℤ) → (p : ℤ) + q = n + 1 → (K.X p).X q
  | 0, q, h => (K.X 0).d (q - 1) q (x ⟨(0, q - 1), by push_cast at h ⊢; omega⟩)
  | p + 1, q, h => (K.d p (p + 1)).f q (x ⟨(p, q), by push_cast at h ⊢; omega⟩) +
      (-1 : ℤ) ^ (p + 1) • (K.X (p + 1)).d (q - 1) q
        (x ⟨(p + 1, q - 1), by push_cast at h ⊢; omega⟩)

/-- Each component of the differential of the product total complex is additive. -/
lemma productTotalDComp_add (n : ℤ) (x y : K.productTotalX n) (p : ℕ) (q : ℤ)
    (h : (p : ℤ) + q = n + 1) :
    K.productTotalDComp n (x + y) p q h =
      K.productTotalDComp n x p q h + K.productTotalDComp n y p q h := by
  cases p
  · exact map_add _ _ _
  · simp only [productTotalDComp]
    rw [show (x + y) = fun i => x i + y i from rfl]
    simp only [map_add, smul_add]
    abel

/-- Each component of the differential of the product total complex vanishes at `0`. -/
lemma productTotalDComp_zero (n : ℤ) (p : ℕ) (q : ℤ) (h : (p : ℤ) + q = n + 1) :
    K.productTotalDComp n 0 p q h = 0 := by
  cases p
  · exact map_zero _
  · simp only [productTotalDComp]
    rw [show (0 : K.productTotalX n) = fun i => 0 from rfl]
    simp

/-- The differential of the product total complex. -/
def productTotalD (n : ℤ) : K.productTotalX n ⟶ K.productTotalX (n + 1) :=
  AddCommGrpCat.ofHom
    { toFun x i := K.productTotalDComp n x i.1.1 i.1.2 i.2
      map_zero' := funext fun i => K.productTotalDComp_zero n _ _ i.2
      map_add' x y := funext fun i => K.productTotalDComp_add n x y _ _ i.2 }

/-- The component in `K^{p, q}` of the differential of the product total complex applied to `x` is
`productTotalDComp`. -/
@[simp]
lemma productTotalD_apply (n : ℤ) (x : K.productTotalX n)
    (i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n + 1}) :
    K.productTotalD n x i = K.productTotalDComp n x i.1.1 i.1.2 i.2 :=
  rfl

/-- The component in `K^{0, q}` of the differential of the product total complex is
`d_2^{0, q - 1}`. -/
@[simp]
lemma productTotalDComp_zero_left (n : ℤ) (x : K.productTotalX n) (q : ℤ)
    (h : ((0 : ℕ) : ℤ) + q = n + 1) :
    K.productTotalDComp n x 0 q h =
      (K.X 0).d (q - 1) q (x ⟨(0, q - 1), by push_cast at h ⊢; omega⟩) :=
  rfl

/-- The component in `K^{p + 1, q}` of the differential of the product total complex is
`d_1^{p, q} + (-1)^{p + 1} d_2^{p + 1, q - 1}`. -/
@[simp]
lemma productTotalDComp_succ (n : ℤ) (x : K.productTotalX n) (p : ℕ) (q : ℤ)
    (h : ((p + 1 : ℕ) : ℤ) + q = n + 1) :
    K.productTotalDComp n x (p + 1) q h =
      (K.d p (p + 1)).f q (x ⟨(p, q), by push_cast at h ⊢; omega⟩) +
      (-1 : ℤ) ^ (p + 1) • (K.X (p + 1)).d (q - 1) q
        (x ⟨(p + 1, q - 1), by push_cast at h ⊢; omega⟩) :=
  rfl

/-- The component in `K^{0, q}` of the differential of the product total complex is
`d_2^{0, q'}` for any `q'` with `q' + 1 = q`. -/
lemma productTotalD_apply_zero_left (n : ℤ) (x : K.productTotalX n) (q q' : ℤ)
    (hq : q' + 1 = q) (h : ((0 : ℕ) : ℤ) + q = n + 1) (h' : ((0 : ℕ) : ℤ) + q' = n) :
    K.productTotalD n x ⟨(0, q), h⟩ = (K.X 0).d q' q (x ⟨(0, q'), h'⟩) := by
  obtain rfl : q' = q - 1 := by omega
  rfl

/-- The component in `K^{p + 1, q}` of the differential of the product total complex is
`d_1^{p, q} + (-1)^{p + 1} d_2^{p + 1, q'}` for any `q'` with `q' + 1 = q`. -/
lemma productTotalD_apply_succ (n : ℤ) (x : K.productTotalX n) (p : ℕ) (q q' : ℤ)
    (hq : q' + 1 = q) (h : ((p + 1 : ℕ) : ℤ) + q = n + 1) (h' : ((p + 1 : ℕ) : ℤ) + q' = n) :
    K.productTotalD n x ⟨(p + 1, q), h⟩ =
      (K.d p (p + 1)).f q (x ⟨(p, q), by push_cast at h ⊢; omega⟩) +
        (-1 : ℤ) ^ (p + 1) • (K.X (p + 1)).d q' q (x ⟨(p + 1, q'), h'⟩) := by
  obtain rfl : q' = q - 1 := by omega
  rfl

omit K in
private lemma d_d_apply {L : CochainComplex AddCommGrpCat.{u} ℤ} (i j k : ℤ) (a : L.X i) :
    L.d j k (L.d i j a) = 0 := by
  rw [← ConcreteCategory.comp_apply, L.d_comp_d]; rfl

private lemma f_d_apply (i j : ℕ) (a b : ℤ) (x : (K.X i).X a) :
    (K.d i j).f b ((K.X i).d a b x) = (K.X j).d a b ((K.d i j).f a x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (K.d i j).comm]

private lemma f_f_apply (i j k : ℕ) (b : ℤ) (x : (K.X i).X b) :
    (K.d j k).f b ((K.d i j).f b x) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, K.d_comp_d]; rfl

/-- The differential of the product total complex squares to zero. -/
lemma productTotalD_comp_productTotalD (n : ℤ) :
    K.productTotalD n ≫ K.productTotalD (n + 1) = 0 := by
  ext x
  funext ⟨⟨p, q⟩, h⟩
  show K.productTotalDComp (n + 1) (K.productTotalD n x) p q h = 0
  rcases p with _ | _ | p
  · simp [d_d_apply]
  · simp [d_d_apply, f_d_apply]
  · simp only [productTotalDComp_succ, productTotalD_apply, map_add, map_zsmul,
      f_f_apply, d_d_apply, f_d_apply, smul_zero, add_zero, zero_add]
    rw [pow_succ (-1 : ℤ) (p + 1), mul_neg_one, neg_smul, add_neg_cancel]

/-- The product total complex `Tot_π(K)` of a double complex of abelian groups `K` whose first
index runs over `ℕ`: its term of degree `n` is `∏_{p + q = n} K^{p, q}` and the component of its
differential in `K^{p, q}` is `d_1^{p - 1, q} + (-1)^p d_2^{p, q - 1}`. -/
def productTotal : CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.of K.productTotalX K.productTotalD K.productTotalD_comp_productTotalD

/-- The term of degree `n` of `Tot_π(K)` is `∏_{p + q = n} K^{p, q}`. -/
@[simp]
lemma productTotal_X (n : ℤ) : K.productTotal.X n = K.productTotalX n :=
  rfl

/-- The differential of `Tot_π(K)` from degree `n` to degree `n + 1` is `productTotalD`. -/
@[simp]
lemma productTotal_d (n : ℤ) : K.productTotal.d n (n + 1) = K.productTotalD n :=
  CochainComplex.of_d _ _ n

variable {K} {M : CochainComplex AddCommGrpCat.{u} ℤ} (ε : M ⟶ K.X 0)

/-- The components of the map `M^• → Tot_π(K)` induced by `ε : M^• → K^{0, •}`. -/
def toProductTotalComp (n : ℤ) (m : M.X n) : (p : ℕ) → (q : ℤ) → (p : ℤ) + q = n → (K.X p).X q
  | 0, q, h => ε.f q ((M.XIsoOfEq (by push_cast at h; omega)).hom m)
  | _ + 1, _, _ => 0

/-- The component in `K^{0, q}` of the map `M^• → Tot_π(K)` is given by `ε`. -/
@[simp]
lemma toProductTotalComp_zero_left (n : ℤ) (m : M.X n) (q : ℤ) (h : ((0 : ℕ) : ℤ) + q = n) :
    toProductTotalComp ε n m 0 q h = ε.f q ((M.XIsoOfEq (by push_cast at h; omega)).hom m) :=
  rfl

/-- The component in `K^{p + 1, q}` of the map `M^• → Tot_π(K)` vanishes. -/
@[simp]
lemma toProductTotalComp_succ (n : ℤ) (m : M.X n) (p : ℕ) (q : ℤ)
    (h : ((p + 1 : ℕ) : ℤ) + q = n) : toProductTotalComp ε n m (p + 1) q h = 0 :=
  rfl

/-- The degree `n` component of the map `M^• → Tot_π(K)` induced by `ε : M^• → K^{0, •}`. -/
def toProductTotalF (n : ℤ) : M.X n ⟶ K.productTotalX n :=
  AddCommGrpCat.ofHom
    { toFun m i := toProductTotalComp ε n m i.1.1 i.1.2 i.2
      map_zero' := funext fun ⟨⟨p, q⟩, h⟩ => by cases p <;> simp
      map_add' x y := funext fun ⟨⟨p, q⟩, h⟩ => by cases p <;> simp }

/-- The component in `K^{p, q}` of the degree `n` map `M^n → Tot_π^n(K)` is
`toProductTotalComp`. -/
@[simp]
lemma toProductTotalF_apply (n : ℤ) (m : M.X n) (i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}) :
    toProductTotalF ε n m i = toProductTotalComp ε n m i.1.1 i.1.2 i.2 :=
  rfl

variable (w : ε ≫ K.d 0 1 = 0)

include w in
/-- The degreewise maps `M^n → Tot_π^n(K)` commute with the differentials. -/
lemma toProductTotalF_comm (n : ℤ) :
    toProductTotalF ε n ≫ K.productTotalD n = M.d n (n + 1) ≫ toProductTotalF ε (n + 1) := by
  ext m
  funext ⟨⟨p, q⟩, h⟩
  show K.productTotalDComp n (toProductTotalF ε n m) p q h =
    toProductTotalComp ε (n + 1) (M.d n (n + 1) m) p q h
  rcases p with _ | _ | p
  · simp only [productTotalDComp_zero_left, toProductTotalF_apply, toProductTotalComp_zero_left]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ε.comm,
      ← Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d,
      ← HomologicalComplex.d_comp_XIsoOfEq_hom M (show n + 1 = q by push_cast at h; omega)]
    rfl
  · simp only [productTotalDComp_succ, toProductTotalF_apply, toProductTotalComp_zero_left,
      toProductTotalComp_succ, map_zero, smul_zero, add_zero]
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, w]
    rfl
  · simp

/-- The map `M^• → Tot_π(K)` induced by a map `ε : M^• → K^{0, •}` with `d_1^{0, •} ∘ ε = 0`. -/
def toProductTotal : M ⟶ K.productTotal where
  f := toProductTotalF ε
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [productTotal_d]
    exact toProductTotalF_comm ε w i

/-- The degree `n` component of `M^• → Tot_π(K)` is `toProductTotalF`. -/
@[simp]
lemma toProductTotal_f (n : ℤ) : (toProductTotal ε w).f n = toProductTotalF ε n :=
  rfl

end

/-! ### Element-wise consequences of the hypotheses -/

section Exactness

variable {B : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ)}

private lemma row_exact_succ (hB : B.Acyclic) (j : ℕ) (q : ℤ) (x : (B.X (j + 1)).X q)
    (hx : (B.d (j + 1) (j + 2)).f q x = 0) : ∃ y : (B.X j).X q, (B.d j (j + 1)).f q y = x := by
  have h := hB (j + 1)
  rw [HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 2) (by simp) (by simp)] at h
  exact (ShortComplex.ab_exact_iff _).mp (h.map (HomologicalComplex.eval _ _ q)) x hx

private lemma row_exact_zero (hB : B.Acyclic) (q : ℤ) (x : (B.X 0).X q)
    (hx : (B.d 0 1).f q x = 0) : x = 0 := by
  have h := hB 0
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)] at h
  obtain ⟨y, rfl⟩ :=
    (ShortComplex.ab_exact_iff _).mp (h.map (HomologicalComplex.eval _ _ q)) x hx
  show (B.d 0 0).f q y = 0
  rw [B.shape 0 0 (by simp)]
  rfl

private lemma pOpcycles_eq_zero_iff (L : CochainComplex AddCommGrpCat.{u} ℤ) (a b : ℤ)
    (hab : a + 1 = b) (x : L.X b) : L.pOpcycles b x = 0 ↔ ∃ z, L.d a b z = x := by
  have hS := ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk (L.d a b) (L.pOpcycles b)
    (L.d_pOpcycles a b)) (L.opcyclesIsCokernel a b (by simp [← hab]))
  refine ⟨fun hx => (ShortComplex.ab_exact_iff _).mp hS x hx, ?_⟩
  rintro ⟨z, rfl⟩
  rw [← ConcreteCategory.comp_apply, L.d_pOpcycles]
  rfl

private lemma opcyclesMap_pOpcycles {L L' : CochainComplex AddCommGrpCat.{u} ℤ} (φ : L ⟶ L')
    (b : ℤ) (x : L.X b) :
    HomologicalComplex.opcyclesMap φ b (L.pOpcycles b x) = L'.pOpcycles b (φ.f b x) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.p_opcyclesMap]
  rfl

private lemma coker_exact_succ
    (hC : ∀ b : ℤ, (((HomologicalComplex.opcyclesFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      b).mapHomologicalComplex (ComplexShape.up ℕ)).obj B).Acyclic)
    (j : ℕ) (a b : ℤ) (hab : a + 1 = b) (x : (B.X (j + 1)).X b)
    (hx : ∃ z, (B.X (j + 2)).d a b z = (B.d (j + 1) (j + 2)).f b x) :
    ∃ y z, (B.d j (j + 1)).f b y + (B.X (j + 1)).d a b z = x := by
  have h := hC b (j + 1)
  rw [HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 2) (by simp) (by simp)] at h
  have hx' : HomologicalComplex.opcyclesMap (B.d (j + 1) (j + 2)) b
      ((B.X (j + 1)).pOpcycles b x) = 0 := by
    rw [opcyclesMap_pOpcycles, pOpcycles_eq_zero_iff _ a b hab]
    exact hx
  obtain ⟨y', hy'⟩ := (ShortComplex.ab_exact_iff _).mp h _ hx'
  obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective ((B.X j).pOpcycles b)).mp inferInstance y'
  change HomologicalComplex.opcyclesMap (B.d j (j + 1)) b _ = _ at hy'
  rw [opcyclesMap_pOpcycles] at hy'
  obtain ⟨z, hz⟩ := (pOpcycles_eq_zero_iff _ a b hab (x - (B.d j (j + 1)).f b y)).mp
    (by rw [map_sub, hy', sub_self])
  exact ⟨y, z, by rw [hz, add_sub_cancel]⟩

private lemma coker_exact_zero
    (hC : ∀ b : ℤ, (((HomologicalComplex.opcyclesFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      b).mapHomologicalComplex (ComplexShape.up ℕ)).obj B).Acyclic)
    (a b : ℤ) (hab : a + 1 = b) (x : (B.X 0).X b)
    (hx : ∃ z, (B.X 1).d a b z = (B.d 0 1).f b x) : ∃ z, (B.X 0).d a b z = x := by
  have h := hC b 0
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)] at h
  have hx' : HomologicalComplex.opcyclesMap (B.d 0 1) b ((B.X 0).pOpcycles b x) = 0 := by
    rw [opcyclesMap_pOpcycles, pOpcycles_eq_zero_iff _ a b hab]
    exact hx
  obtain ⟨y', hy'⟩ := (ShortComplex.ab_exact_iff _).mp h _ hx'
  rw [← pOpcycles_eq_zero_iff _ a b hab, ← hy']
  show HomologicalComplex.opcyclesMap (B.d 0 0) b _ = 0
  rw [B.shape 0 0 (by simp), HomologicalComplex.opcyclesMap_zero]
  rfl

private lemma coker_exact_uniform
    (hC : ∀ b : ℤ, (((HomologicalComplex.opcyclesFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      b).mapHomologicalComplex (ComplexShape.up ℕ)).obj B).Acyclic)
    (i : ℕ) (a b : ℤ) (hab : a + 1 = b) (e : (B.X i).X b)
    (he : ∃ z, (B.X (i + 1)).d a b z = (B.d i (i + 1)).f b e) :
    ∃ h, (B.d i (i + 1)).f b ((B.X i).d a b h) = (B.d i (i + 1)).f b e := by
  cases i with
  | zero =>
    obtain ⟨z, hz⟩ := coker_exact_zero hC a b hab e he
    exact ⟨z, by rw [hz]⟩
  | succ j =>
    obtain ⟨y, z, rfl⟩ := coker_exact_succ hC j a b hab e he
    exact ⟨z, by rw [map_add, f_f_apply, zero_add]⟩

/-- The homology rows `H(B^{0, •}) → H(B^{1, •}) → ⋯` are exact. -/
private lemma homology_exact (hA : B.Acyclic)
    (hC : ∀ b : ℤ, (((HomologicalComplex.opcyclesFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      b).mapHomologicalComplex (ComplexShape.up ℕ)).obj B).Acyclic)
    (i : ℕ) (o q r : ℤ) (hoq : o + 1 = q) (hqr : q + 1 = r) (w : (B.X (i + 2)).X q)
    (hw : (B.X (i + 2)).d q r w = 0)
    (hf : ∃ u, (B.X (i + 3)).d o q u = (B.d (i + 2) (i + 3)).f q w) :
    ∃ c : (B.X (i + 1)).X q, (B.X (i + 1)).d q r c = 0 ∧
      ∃ v, (B.X (i + 2)).d o q v = w - (B.d (i + 1) (i + 2)).f q c := by
  obtain ⟨y, z, hyz⟩ := coker_exact_succ hC (i + 1) o q hoq w hf
  change (B.d (i + 1) (i + 2)).f q y + (B.X (i + 2)).d o q z = w at hyz
  have ht : (B.d (i + 1) (i + 2)).f r ((B.X (i + 1)).d q r y) = 0 := by
    rw [f_d_apply, eq_sub_of_add_eq hyz, map_sub, hw, d_d_apply, sub_zero]
  obtain ⟨e, he⟩ := row_exact_succ hA i r _ ht
  obtain ⟨h, hh⟩ := coker_exact_uniform hC i q r hqr e ⟨y, he.symm⟩
  refine ⟨y - (B.d i (i + 1)).f q h, ?_, z, ?_⟩
  · rw [map_sub, ← f_d_apply, hh, he, sub_self]
  · rw [map_sub, f_f_apply, sub_zero, ← hyz, add_sub_cancel_left]

end Exactness


/-! ### A criterion for quasi-isomorphisms of complexes of abelian groups -/

section

/-- The free abelian group on the underlying set of `A` covers `A`. -/
lemma epi_freeCover (A : AddCommGrpCat.{u}) :
    Epi (AddCommGrpCat.ofHom (FreeAbelianGroup.lift (id : A → A))) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro a
  exact ⟨FreeAbelianGroup.of a, by simp⟩

/-- Two maps out of a free abelian group agree as soon as they agree on the generators. -/
lemma freeCover_hom_ext {A Z : AddCommGrpCat.{u}}
    {f g : AddCommGrpCat.of (FreeAbelianGroup A) ⟶ Z}
    (h : ∀ a, f (FreeAbelianGroup.of a) = g (FreeAbelianGroup.of a)) : f = g := by
  ext1
  exact FreeAbelianGroup.lift_ext _ _ h

/-- A morphism of cochain complexes of abelian groups is a quasi-isomorphism in degree `n + 1`
when every cycle lifts to a cycle modulo a boundary, and a cycle that becomes a boundary was
already one. -/
lemma quasiIsoAt_of_elements {L L' : CochainComplex AddCommGrpCat.{u} ℤ} (φ : L ⟶ L')
    (n : ℤ)
    (hsurj : ∀ y : L'.X (n + 1), L'.d (n + 1) (n + 1 + 1) y = 0 →
      ∃ x : L.X (n + 1), L.d (n + 1) (n + 1 + 1) x = 0 ∧
        ∃ z : L'.X n, y = φ.f (n + 1) x + L'.d n (n + 1) z)
    (hinj : ∀ x : L.X (n + 1), L.d (n + 1) (n + 1 + 1) x = 0 → ∀ y : L'.X n,
      φ.f (n + 1) x = L'.d n (n + 1) y → ∃ z : L.X n, L.d n (n + 1) z = x) :
    QuasiIsoAt φ (n + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap φ (n + 1)) := by
    rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements φ n (n + 1) (n + 1 + 1)
      (by simp) (by simp)]
    intro A x₂ hx₂ y₁ hy₁
    have hz (a : A) : ∃ z : L.X n, L.d n (n + 1) z = x₂ a :=
      hinj _ (by simpa using ConcreteCategory.congr_hom hx₂ a) (y₁ a)
        (by simpa using ConcreteCategory.congr_hom hy₁ a)
    refine ⟨_, _, epi_freeCover A,
      AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun a => (hz a).choose), ?_⟩
    exact freeCover_hom_ext fun a => by simp [(hz a).choose_spec]
  have hepi : Epi (HomologicalComplex.homologyMap φ (n + 1)) := by
    rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements φ n (n + 1) (n + 1 + 1)
      (by simp) (by simp)]
    intro A y₂ hy₂
    have hx (a : A) := hsurj (y₂ a) (by simpa using ConcreteCategory.congr_hom hy₂ a)
    refine ⟨_, _, epi_freeCover A,
      AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun a => (hx a).choose), ?_,
      AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun a => (hx a).choose_spec.2.choose), ?_⟩
    · exact freeCover_hom_ext fun a => by simp [(hx a).choose_spec.1]
    · exact freeCover_hom_ext fun a => by simp [← (hx a).choose_spec.2.choose_spec]
  exact isIso_of_mono_of_epi _

end

/-! ### The diagram chase -/

section

variable {K : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ)}
  {M : CochainComplex AddCommGrpCat.{u} ℤ}

private lemma neg_one_pow_succ_smul {G : Type*} [AddCommGroup G] (k : ℕ) (v : G) :
    (-1 : ℤ) ^ (k + 1) • v = -((-1 : ℤ) ^ k • v) := by
  rw [pow_succ, mul_neg_one, neg_smul]

private lemma neg_one_pow_smul_smul {G : Type*} [AddCommGroup G] (k : ℕ) (v : G) :
    (-1 : ℤ) ^ k • (-1 : ℤ) ^ k • v = v := by
  rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

private lemma apply_eq_zero {n : ℤ} {x : K.productTotalX n} (hx : x = 0)
    (i : {pq : ℕ × ℤ // (pq.1 : ℤ) + pq.2 = n}) : x i = 0 := by
  rw [hx]; rfl

/-- The property of `a ∈ K^{p, n - p}` that `x^{p + 1, n - p} - d_1(a)` is a vertical boundary. -/
private def IsAdjusted (n : ℤ) (x : K.productTotalX (n + 1)) (p : ℕ) (a : (K.X p).X (n - p)) :
    Prop :=
  ∃ u : (K.X (p + 1)).X (n - (p + 1 : ℕ)), (K.X (p + 1)).d (n - (p + 1 : ℕ)) (n - p) u =
    x ⟨(p + 1, n - p), by push_cast; omega⟩ - (K.d p (p + 1)).f (n - p) a

variable (ε : M ⟶ K.X 0) (w : ε ≫ K.d 0 1 = 0)

variable (hA : (CochainComplex.augment K ε w).Acyclic)
  (hC : ∀ b : ℤ, (((HomologicalComplex.opcyclesFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      b).mapHomologicalComplex (ComplexShape.up ℕ)).obj (CochainComplex.augment K ε w)).Acyclic)

include hA in
private lemma ε_injective (b : ℤ) (m : M.X b) (hm : ε.f b m = 0) : m = 0 :=
  row_exact_zero hA b m hm

include hC in
private lemma coker_exact_zero_left (a b : ℤ) (hab : a + 1 = b) (x : (K.X 0).X b)
    (hx : ∃ z, (K.X 1).d a b z = (K.d 0 1).f b x) :
    ∃ (m : M.X b) (z : (K.X 0).X a), ε.f b m + (K.X 0).d a b z = x :=
  coker_exact_succ hC 0 a b hab x hx

include hA hC in
/-- Given `s - d_1 r` a vertical cocycle whose `d_1` is a vertical boundary by `e`, the
homology exactness lets us correct `r` by a vertical cocycle `c` so that `s - d_1 (r + c)` is a
vertical boundary. -/
private lemma homology_exact_succ (i : ℕ) (o q r : ℤ) (hoq : o + 1 = q) (hqr : q + 1 = r)
    (s : (K.X (i + 1)).X q) (r' : (K.X i).X q) (t : (K.X (i + 1 + 1)).X o)
    (hw : (K.X (i + 1)).d q r (s - (K.d i (i + 1)).f q r') = 0)
    (e : (K.d (i + 1) (i + 1 + 1)).f q s + (-1 : ℤ) ^ (i + 1 + 1) • (K.X (i + 1 + 1)).d o q t = 0) :
    ∃ c : (K.X i).X q, (K.X i).d q r c = 0 ∧
      ∃ v, (K.X (i + 1)).d o q v = s - (K.d i (i + 1)).f q (r' + c) := by
  have hf : ∃ u, (K.X (i + 1 + 1)).d o q u =
      (K.d (i + 1) (i + 1 + 1)).f q (s - (K.d i (i + 1)).f q r') := by
    refine ⟨-((-1 : ℤ) ^ (i + 1 + 1) • t), ?_⟩
    rw [map_sub, f_f_apply, sub_zero, map_neg, map_zsmul]
    exact (eq_neg_of_add_eq_zero_left e).symm
  obtain ⟨c, hc, v, hv⟩ := homology_exact hA hC i o q r hoq hqr _ hw hf
  refine ⟨c, hc, v, ?_⟩
  erw [map_add, ← sub_sub]
  exact hv

include hA hC in
private lemma adjusted_step
    (n : ℤ) (x : K.productTotalX (n + 1)) (hx : K.productTotalD (n + 1) x = 0) (p : ℕ)
    (a : (K.X p).X (n - p)) (ha : IsAdjusted n x p a) :
    ∃ b : (K.X (p + 1)).X (n - (p + 1 : ℕ)),
      (-1 : ℤ) ^ (p + 1) • (K.X (p + 1)).d (n - (p + 1 : ℕ)) (n - p) b =
        x ⟨(p + 1, n - p), by push_cast; omega⟩ - (K.d p (p + 1)).f (n - p) a ∧
      IsAdjusted n x (p + 1) b := by
  obtain ⟨u, hu⟩ := ha
  have e2 := apply_eq_zero hx ⟨(p + 1 + 1, n - p), by push_cast; omega⟩
  rw [productTotalD_apply_succ (q' := n - (p + 1 : ℕ)) (hq := by push_cast; omega)
    (h' := by push_cast; omega)] at e2
  have e3 := apply_eq_zero hx ⟨(p + 1 + 1 + 1, n - (p + 1 : ℕ)), by push_cast; omega⟩
  rw [productTotalD_apply_succ (q' := n - (p + 1 + 1 : ℕ)) (hq := by push_cast; omega)
    (h' := by push_cast; omega)] at e3
  rw [neg_one_pow_succ_smul, ← sub_eq_add_neg, sub_eq_zero] at e2
  have hw : (K.X (p + 1 + 1)).d (n - (p + 1 : ℕ)) (n - p)
      (x ⟨(p + 1 + 1, n - (p + 1 : ℕ)), by push_cast; omega⟩ -
        (K.d (p + 1) (p + 1 + 1)).f (n - (p + 1 : ℕ)) ((-1 : ℤ) ^ (p + 1) • u)) = 0 := by
    rw [map_sub, ← f_d_apply, map_zsmul, map_zsmul, hu, map_sub, f_f_apply, sub_zero, e2,
      neg_one_pow_smul_smul, sub_self]
  obtain ⟨c, hc, v, hv⟩ := homology_exact_succ ε w hA hC (p + 1) (n - (p + 1 + 1 : ℕ))
    (n - (p + 1 : ℕ)) (n - p) (by push_cast; omega) (by push_cast; omega) _ _
    (x ⟨(p + 1 + 1 + 1, n - (p + 1 + 1 : ℕ)), by push_cast; omega⟩) hw e3
  refine ⟨(-1 : ℤ) ^ (p + 1) • u + c, ?_, v, ?_⟩
  · rw [map_add, hc, add_zero, map_zsmul, neg_one_pow_smul_smul, hu]
  · exact hv

private lemma ε_comm_apply (i j : ℤ) (m : M.X i) :
    ε.f j (M.d i j m) = (K.X 0).d i j (ε.f i m) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ε.comm]

include w in
private lemma f_ε_apply (b : ℤ) (m : M.X b) : (K.d 0 1).f b (ε.f b m) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, w]; rfl

include hA hC in
private lemma adjusted_base (n : ℤ) (x : K.productTotalX (n + 1))
    (hx : K.productTotalD (n + 1) x = 0) :
    ∃ m : M.X (n + 1), M.d (n + 1) (n + 1 + 1) m = 0 ∧
      ∃ a : (K.X 0).X (n - (0 : ℕ)), (K.X 0).d (n - (0 : ℕ)) (n + 1) a =
        x ⟨(0, n + 1), by push_cast; omega⟩ - ε.f (n + 1) m ∧ IsAdjusted n x 0 a := by
  have e0 := apply_eq_zero hx ⟨(0, n + 1 + 1), by push_cast; omega⟩
  rw [productTotalD_apply_zero_left (q' := n + 1) (hq := rfl)
    (h' := by push_cast; omega)] at e0
  have e1 := apply_eq_zero hx ⟨(0 + 1, n + 1), by push_cast; omega⟩
  rw [productTotalD_apply_succ (q' := n - (0 : ℕ)) (hq := by push_cast; omega)
    (h' := by push_cast; omega)] at e1
  rw [neg_one_pow_succ_smul, pow_zero, one_smul, ← sub_eq_add_neg, sub_eq_zero] at e1
  have e2 := apply_eq_zero hx ⟨(0 + 1 + 1, n - (0 : ℕ)), by push_cast; omega⟩
  rw [productTotalD_apply_succ (q' := n - (0 + 1 : ℕ)) (hq := by push_cast; omega)
    (h' := by push_cast; omega)] at e2
  obtain ⟨m, y, hmy⟩ := coker_exact_zero_left ε w hC (n - (0 : ℕ)) (n + 1)
    (by push_cast; omega) _ ⟨_, e1.symm⟩
  have hm : M.d (n + 1) (n + 1 + 1) m = 0 := by
    refine ε_injective ε w hA _ _ ?_
    rw [ε_comm_apply, eq_sub_of_add_eq hmy, map_sub, e0, d_d_apply, sub_zero]
  have hw : (K.X (0 + 1)).d (n - (0 : ℕ)) (n + 1)
      (x ⟨(0 + 1, n - (0 : ℕ)), by push_cast; omega⟩ - (K.d 0 (0 + 1)).f (n - (0 : ℕ)) y) =
        0 := by
    rw [map_sub, ← f_d_apply, eq_sub_of_add_eq' hmy, map_sub, ← e1]
    show _ - (_ - (K.d 0 1).f (n + 1) (ε.f (n + 1) m)) = 0
    rw [f_ε_apply ε w]
    abel
  obtain ⟨c, hc, v, hv⟩ := homology_exact_succ ε w hA hC 0 (n - (0 + 1 : ℕ))
    (n - (0 : ℕ)) (n + 1) (by push_cast; omega) (by push_cast; omega) _ _
    (x ⟨(0 + 1 + 1, n - (0 + 1 : ℕ)), by push_cast; omega⟩) hw e2
  refine ⟨m, hm, y + c, ?_, v, ?_⟩
  · rw [map_add, hc, add_zero, eq_sub_of_add_eq' hmy]
  · exact hv

include hA hC in
private lemma exists_preimage_up_to_boundary (n : ℤ) (x : K.productTotalX (n + 1))
    (hx : K.productTotalD (n + 1) x = 0) :
    ∃ m : M.X (n + 1), M.d (n + 1) (n + 1 + 1) m = 0 ∧
      ∃ y : K.productTotalX n, x = toProductTotalF ε (n + 1) m + K.productTotalD n y := by
  obtain ⟨m, hm, a₀, ha₀, hI₀⟩ := adjusted_base ε w hA hC n x hx
  choose b hb₁ hb₂ using adjusted_step ε w hA hC n x hx
  let Y : ∀ p : ℕ, {a : (K.X p).X (n - p) // IsAdjusted n x p a} := fun p =>
    Nat.rec (motive := fun p => {a : (K.X p).X (n - p) // IsAdjusted n x p a}) ⟨a₀, hI₀⟩
      (fun p a => ⟨b p a.1 a.2, hb₂ p a.1 a.2⟩) p
  let y : K.productTotalX n := fun i =>
    ((K.X i.1.1).XIsoOfEq (show n - (i.1.1 : ℤ) = i.1.2 by have := i.2; omega)).hom (Y i.1.1).1
  refine ⟨m, hm, y, ?_⟩
  funext ⟨⟨p, q⟩, h⟩
  show _ = toProductTotalF ε (n + 1) m ⟨(p, q), h⟩ + K.productTotalD n y ⟨(p, q), h⟩
  rcases p with _ | p
  · obtain rfl : q = n + 1 := by push_cast at h; omega
    rw [productTotalD_apply_zero_left (q' := n - (0 : ℕ)) (hq := by push_cast; omega)
      (h' := by push_cast; omega)]
    simp only [toProductTotalF_apply, toProductTotalComp_zero_left, y,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ConcreteCategory.id_apply]
    show _ = ε.f (n + 1) m + (K.X 0).d (n - (0 : ℕ)) (n + 1) a₀
    rw [ha₀, add_sub_cancel]
  · obtain rfl : q = n - p := by push_cast at h; omega
    rw [productTotalD_apply_succ (q' := n - (p + 1 : ℕ)) (hq := by push_cast; omega)
      (h' := by push_cast; omega)]
    simp only [toProductTotalF_apply, toProductTotalComp_succ, y,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ConcreteCategory.id_apply, zero_add]
    show _ = (K.d p (p + 1)).f (n - p) (Y p).1 +
      (-1 : ℤ) ^ (p + 1) • (K.X (p + 1)).d (n - (p + 1 : ℕ)) (n - p) (b p (Y p).1 (Y p).2)
    rw [hb₁, add_sub_cancel]

include hA hC in
private lemma eq_boundary_of_eq_boundary (n : ℤ) (m : M.X (n + 1))
    (y : K.productTotalX n) (hy : toProductTotalF ε (n + 1) m = K.productTotalD n y) :
    ∃ z : M.X n, M.d n (n + 1) z = m := by
  have e0 := congrFun hy ⟨(0, n + 1), by push_cast; omega⟩
  rw [productTotalD_apply_zero_left (q' := n) (hq := rfl) (h' := by push_cast; omega)] at e0
  simp only [toProductTotalF_apply, toProductTotalComp_zero_left,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ConcreteCategory.id_apply] at e0
  have e1 := congrFun hy ⟨(0 + 1, n), by push_cast; omega⟩
  rw [productTotalD_apply_succ (q' := n - 1) (hq := by omega) (h' := by push_cast; omega)] at e1
  simp only [toProductTotalF_apply, toProductTotalComp_succ] at e1
  rw [neg_one_pow_succ_smul, pow_zero, one_smul, ← sub_eq_add_neg, eq_comm, sub_eq_zero] at e1
  obtain ⟨z, z', hzz'⟩ := coker_exact_zero_left ε w hC (n - 1) n (by omega) _ ⟨_, e1.symm⟩
  refine ⟨z, (sub_eq_zero.mp (ε_injective ε w hA _ _ ?_)).symm⟩
  rw [map_sub, ε_comm_apply]
  show ε.f (n + 1) m - _ = 0
  rw [e0, ← hzz', map_add, d_d_apply, add_zero, sub_self]

end

/-! ### The main theorem -/

section

variable {K : HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ)}
  {M : CochainComplex AddCommGrpCat.{u} ℤ}

/-- Let `0 → M^• → A_0^• → A_1^• → ⋯` be an exact complex of complexes of abelian groups such
that for every `p` the induced complex `0 → Coker(d_M^p) → Coker(d_{A_0}^p) → ⋯` is exact. Then
the map `M^• → Tot_π(A^{•, •})` induced by `M^• → A_0^•` is a quasi-isomorphism. Here `K` is the
double complex `A^{p, q} = A_p^q`, `ε` is the map `M^• → A_0^•`, the exact complex of complexes
is the augmentation of `K` by `ε`, and `Coker(d^p)` is the object of opcycles in degree `p + 1`. -/
@[stacks 09J0]
theorem quasiIso_toProductTotal (ε : M ⟶ K.X 0) (w : ε ≫ K.d 0 1 = 0)
    (hA : (CochainComplex.augment K ε w).Acyclic)
    (hC : ∀ q : ℤ, (((HomologicalComplex.opcyclesFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      q).mapHomologicalComplex (ComplexShape.up ℕ)).obj (CochainComplex.augment K ε w)).Acyclic) :
    QuasiIso (toProductTotal ε w) := by
  rw [quasiIso_iff]
  intro i
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, n + 1 = i := ⟨i - 1, by omega⟩
  apply quasiIsoAt_of_elements
  · intro x hx
    rw [productTotal_d] at hx
    obtain ⟨m, hm, y, hy⟩ := exists_preimage_up_to_boundary ε w hA hC n x hx
    refine ⟨m, hm, y, ?_⟩
    rw [productTotal_d]
    exact hy
  · intro m _ y hy
    rw [productTotal_d] at hy
    exact eq_boundary_of_eq_boundary ε w hA hC n m y hy

end

end HomologicalComplex₂
