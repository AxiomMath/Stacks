module

public import StacksFrontier.Homology.HomComplex.Evaluation

/-!
# Differentials of iterated Hom complexes and evaluation into a double Hom complex

Let `R` be a commutative ring and let `K`, `L`, `M` be cochain complexes of `R`-modules. This
file records three homogeneous computations in the calculus of Hom complexes. First, the
differential of a cochain in the iterated Hom complex `Hom^•(Hom^•(K, L), M)` is, on each
homogeneous component, the sum of three terms coming from the differentials of `M`, of `L` and
of `K`, carrying the signs `1`, `-(-1)^n` and `(-1)^(p+1)`. Second, the differential of the
total complex `Tot(Hom^•(L, M) ⊗ K)` restricted to a homogeneous summand
`Hom(L^{-q}, M^p) ⊗ K^r` is the sum of postcomposition by `d_M`, `-(-1)^(p+q)` times
precomposition by `d_L`, and `(-1)^(p+q)` times `d_K`. Third, the identity cochain of `M`
together with tensor–Hom evaluation produces a canonical morphism `K ⟶ Hom^•(Hom^•(K, M), M)`
which on homogeneous elements is evaluation with the Koszul sign `(-1)^(nm)`.

## Main definitions

* `CochainComplex.HomComplex.homComponent`: the inclusion of a homogeneous component
  `Hom_R(L^{-q}, M^p)` into degree `p + q` of the Hom complex `Hom^•(L, M)`.
* `CochainComplex.HomComplex.postcomposeDifferential`,
  `CochainComplex.HomComplex.precomposeDifferential`: postcomposition by `d_M` and
  precomposition by `d_L` on a homogeneous Hom component.
* `CochainComplex.HomComplex.evaluationToDoubleHom`: the canonical evaluation morphism
  `K ⟶ Hom^•(Hom^•(K, M), M)`.

## Main results

* `CochainComplex.HomComplex.iteratedHomComplex_differential_apply` ([stacks 0FNE]): the
  three-term component formula for the differential of `Hom^•(Hom^•(K, L), M)`.
* `CochainComplex.HomComplex.tensorHomComplex_differential_component` ([stacks 0FNF]): the
  three-term component formula for the differential of `Tot(Hom^•(L, M) ⊗ K)`.
* `CochainComplex.HomComplex.evaluationToDoubleHom_apply` ([stacks 0FNM]): the homogeneous sign
  formula for `evaluationToDoubleHom`, together with its naturality in `K` and its dinaturality
  in the coefficient complex `M`.

## Implementation notes

The source states the first two identities "in some unspecified sense", because the three
displayed terms live in different tridegrees. They are made precise here in the two ways the
respective situations allow. For the iterated Hom complex the identity is an equality of
elements: the component of the differential is evaluated at a homogeneous cochain
`f ∈ Hom^{-s-1}(K, L)`, and the indices are chosen so that every term lies in `M^p`. For the
tensor product the identity is an equality of morphisms: each term is inserted into the
appropriate homogeneous summand of the total complex through `homComponent` and the summand
inclusions `ιTensorObj`.

The evaluation morphism of Stacks 0FNM is the morphism of Stacks 0A60, namely
`ChainEvaluation.chainEvaluation`, specialized to `L = M` and precomposed with the insertion of
the identity cochain through the tensor unit. The identity cochain itself is produced by the
tensor–Hom morphism `Stacks.HomComplex.TensorHomMap.Phi` of Stacks 0A62 followed by the left
  unitor, and
`identityCochain` below is the computation identifying the result with `Cochain.ofHom (𝟙 M)`.
Dinaturality in `M` is the correct formulation, since the coefficient complex occurs both
covariantly (as the target) and contravariantly (inside the inner Hom complex).

Mathlib's monoidal structure on `ModuleCat R` requires the module universe to agree with the
universe of `R`, so the two statements involving a tensor product are stated for
`ModuleCat.{u} R` with `R : Type u`, while the purely Hom-complex computation of Stacks 0FNE is
stated for `ModuleCat.{v} R` with `R : Type u`.

## References

* [The Stacks Project, Tag 0FNE](https://stacks.math.columbia.edu/tag/0FNE)
* [The Stacks Project, Tag 0FNF](https://stacks.math.columbia.edu/tag/0FNF)
* [The Stacks Project, Tag 0FNM](https://stacks.math.columbia.edu/tag/0FNM)
-/

@[expose] public section

universe u v

namespace CochainComplex.HomComplex

/-! ## The differential of an iterated Hom complex -/

section IteratedHom

open CochainComplex CochainComplex.HomComplex

/-- **Stacks 0FNE.** The differential of a degree-`n` cochain in `Hom^•(Hom^•(K, L), M)`,
evaluated on `f ∈ Hom^{-s-1}(K, L)`, is the sum of the target, middle and source differential
terms, with respective signs `1`, `-(-1)^n` and `(-1)^(p+1)`. -/
@[stacks 0FNE]
theorem iteratedHomComplex_differential_apply
    {R : Type u} [CommRing R]
    (K L M : CochainComplex (ModuleCat.{v} R) ℤ)
    (n p s : ℤ) (hps : p + s = n)
    (β : Cochain (HomComplexR R K L) M n)
    (f : Cochain K L (-s - 1)) :
    ((δ n (n + 1) β).v (-s - 1) p (by omega)).hom f =
      (M.d (p - 1) p).hom ((β.v (-s - 1) (p - 1) (by omega)).hom f) -
        n.negOnePow •
          ((β.v (-s) p (by omega)).hom
            (f.comp (Cochain.diff L) (by omega))) +
        (p + 1).negOnePow •
          ((β.v (-s) p (by omega)).hom
            ((Cochain.diff K).comp f (by omega))) := by
  have hdiff : δ (-s - 1) (-s) f =
      f.comp (Cochain.diff L) (by omega) +
        (-s).negOnePow • ((Cochain.diff K).comp f (by omega)) := by
    apply Cochain.ext
    intro a b hab
    rw [δ_v (-s - 1) (-s) (by omega) f a b hab (b - 1) (a + 1) (by omega) rfl]
    change _ =
      (f.comp (Cochain.diff L) (by omega)).v a b hab +
        (-s).negOnePow • ((Cochain.diff K).comp f (by omega)).v a b hab
    rw [Cochain.comp_v f (Cochain.diff L) (by omega) a (b - 1) b (by omega) (by omega),
      Cochain.comp_v (Cochain.diff K) f (by omega) a (a + 1) b (by omega) (by omega),
      Cochain.diff_v, Cochain.diff_v]
  rw [δ_v n (n + 1) rfl β (-s - 1) p (by omega) (p - 1) (-s) (by omega) (by omega)]
  let bmap : Cochain K L (-s) →ₗ[R] M.X p := (β.v (-s) p (by omega)).hom
  change
    (M.d (p - 1) p).hom ((β.v (-s - 1) (p - 1) (by omega)).hom f) +
      (n + 1).negOnePow • bmap (δ (-s - 1) (-s) f) = _
  rw [hdiff, bmap.map_add]
  rw [show bmap ((-s).negOnePow • ((Cochain.diff K).comp f (by omega))) =
      (-s).negOnePow • bmap ((Cochain.diff K).comp f (by omega)) by
        simp only [Units.smul_def, map_zsmul]]
  have hsign : (n + 1).negOnePow * (-s).negOnePow = (p + 1).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    omega
  rw [smul_add, smul_smul, hsign, Int.negOnePow_succ, Units.neg_smul]
  dsimp [bmap]
  abel

end IteratedHom

/-! ## The differential on a tensor product with a Hom complex -/

section TensorHom

open CategoryTheory CategoryTheory.MonoidalCategory

variable (R : Type u) [CommRing R]

/-- The inclusion of the component `Hom_R(L^{-q}, M^p)` into degree `p + q` of the `R`-linear
Hom complex `Hom^•(L, M)`. -/
def homComponent (L M : CochainComplex (ModuleCat R) ℤ) (p q : ℤ) :
    ModuleCat.of R (L.X (-q) ⟶ M.X p) ⟶ (HomComplexR R L M).X (p + q) :=
  ModuleCat.ofHom
    { toFun := fun f ↦ Cochain.single f (p + q)
      map_add' := by
        intro f g
        ext a b hab
        simp only [Cochain.add_v]
        by_cases h : -q = a ∧ p = b
        · rcases h with ⟨rfl, rfl⟩
          simp
        · simp [Cochain.single, h]
      map_smul' := by
        intro r f
        ext a b hab
        simp only [Cochain.smul_v]
        by_cases h : -q = a ∧ p = b
        · rcases h with ⟨rfl, rfl⟩
          simp
        · simp [Cochain.single, h] }

/-- Postcomposition by the differential of the target complex, on a homogeneous Hom
component. -/
def postcomposeDifferential (L M : CochainComplex (ModuleCat R) ℤ) (p q : ℤ) :
    ModuleCat.of R (L.X (-q) ⟶ M.X p) ⟶ ModuleCat.of R (L.X (-q) ⟶ M.X (p + 1)) :=
  ModuleCat.ofHom
    { toFun := fun f ↦ f ≫ M.d p (p + 1)
      map_add' := by simp
      map_smul' := by simp }

/-- Precomposition by the differential of the source complex, on a homogeneous Hom
component. -/
def precomposeDifferential (L M : CochainComplex (ModuleCat R) ℤ) (p q : ℤ) :
    ModuleCat.of R (L.X (-q) ⟶ M.X p) ⟶ ModuleCat.of R (L.X (-(q + 1)) ⟶ M.X p) :=
  ModuleCat.ofHom
    { toFun := fun f ↦ L.d (-(q + 1)) (-q) ≫ f
      map_add' := by simp
      map_smul' := by simp }

/-- Two summand inclusions of the total complex agree once their degrees are identified. -/
private theorem single_tensor_ι_congr (L M K : CochainComplex (ModuleCat R) ℤ)
    {a b n n' r j : ℤ} (f : L.X a ⟶ M.X b) (k : K.X r)
    (h : n = n') (hn : n + r = j) (hn' : n' + r = j) :
    (HomologicalComplex.ιTensorObj (HomComplexR R L M) K n r j hn).hom
        (Cochain.single f n ⊗ₜ[R] k) =
      (HomologicalComplex.ιTensorObj (HomComplexR R L M) K n' r j hn').hom
        (Cochain.single f n' ⊗ₜ[R] k) := by
  subst n'
  rfl

/-- The Hom-complex differential of a cochain concentrated in a single degree is
postcomposition by `d_M` minus `(-1)^(p+q)` times precomposition by `d_L`, again concentrated in
a single degree. -/
private theorem differential_single (L M : CochainComplex (ModuleCat R) ℤ) (p q : ℤ)
    (f : L.X (-q) ⟶ M.X p) :
    δ (p + q) (p + q + 1) (Cochain.single f (p + q)) =
      Cochain.single (f ≫ M.d p (p + 1)) (p + q + 1) +
        -(p + q).negOnePow • Cochain.single (L.d (-(q + 1)) (-q) ≫ f) (p + q + 1) := by
  apply Cochain.ext
  intro a b hab
  rw [δ_v (p + q) (p + q + 1) (by omega) _ a b hab (b - 1) (a + 1) rfl rfl]
  by_cases h₁ : a = -q ∧ b = p + 1
  · rcases h₁ with ⟨rfl, rfl⟩
    simp [Cochain.single]
  · by_cases h₂ : a = -(q + 1) ∧ b = p
    · rcases h₂ with ⟨rfl, rfl⟩
      simp [Cochain.single, Int.negOnePow_succ]
    · have h₃ : ¬(-q = a ∧ p = b - 1) := by omega
      have h₄ : ¬(-q = a + 1 ∧ p = b) := by omega
      have h₅ : ¬(-q = a ∧ p + 1 = b) := by omega
      have h₇ : ¬(-1 + -q = a ∧ p = b) := by omega
      simp [Cochain.single, h₃, h₄, h₅, h₇]

/-- **Stacks 0FNF.** On the `(p, q, r)`-component of `Tot(Hom^•(L, M) ⊗ K)`, the total
differential is the Hom-complex differential plus `(-1)^(p+q)` times the differential of `K`;
the Hom-complex differential itself is postcomposition by `d_M` minus `(-1)^(p+q)` times
precomposition by `d_L`. Thus the total differential is the three-term expression
`d_M - (-1)^(p+q) d_L + (-1)^(p+q) d_K`. -/
@[stacks 0FNF]
theorem tensorHomComplex_differential_component
    (L M K : CochainComplex (ModuleCat R) ℤ) (p q r : ℤ) :
    let H := HomComplexR R L M
    let T := HomologicalComplex.tensorObj H K
    ((homComponent R L M p q ▷ K.X r) ≫
          HomologicalComplex.ιTensorObj H K (p + q) r (p + q + r) rfl ≫
          T.d (p + q + r) (p + q + r + 1) =
        (postcomposeDifferential R L M p q ▷ K.X r) ≫
            (homComponent R L M (p + 1) q ▷ K.X r) ≫
            HomologicalComplex.ιTensorObj H K (p + 1 + q) r
              (p + q + r + 1) (by omega) +
          -(p + q).negOnePow •
            ((precomposeDifferential R L M p q ▷ K.X r) ≫
              (homComponent R L M p (q + 1) ▷ K.X r) ≫
              HomologicalComplex.ιTensorObj H K (p + (q + 1)) r
                (p + q + r + 1) (by omega)) +
          (p + q).negOnePow •
            ((homComponent R L M p q ⊗ₘ K.d r (r + 1)) ≫
              HomologicalComplex.ιTensorObj H K (p + q) (r + 1)
                (p + q + r + 1) (by omega))) := by
  dsimp only
  change (homComponent R L M p q ▷ K.X r) ≫
      HomologicalComplex.ιTensorObj (HomComplexR R L M) K
        (p + q) r (p + q + r) (by omega) ≫
      ((HomComplexR R L M) ⊗ K).d (p + q + r) (p + q + r + 1) = _
  rw [CochainComplex.ιTensorObj_d R (HomComplexR R L M) K
    (p + q) r (p + q + r) (p + q + r + 1) (by omega) (by omega)]
  simp only [Preadditive.comp_add]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f k =>
      change (HomologicalComplex.ιTensorObj (HomComplexR R L M) K
            (p + q + 1) r (p + q + r + 1) (by omega)).hom
          (δ (p + q) (p + q + 1) (Cochain.single f (p + q)) ⊗ₜ[R] k) +
        (p + q).negOnePow •
          (HomologicalComplex.ιTensorObj (HomComplexR R L M) K
            (p + q) (r + 1) (p + q + r + 1) (by omega)).hom
              (Cochain.single f (p + q) ⊗ₜ[R] (K.d r (r + 1)).hom k) =
        (HomologicalComplex.ιTensorObj (HomComplexR R L M) K
            (p + 1 + q) r (p + q + r + 1) (by omega)).hom
              (Cochain.single (f ≫ M.d p (p + 1)) (p + 1 + q) ⊗ₜ[R] k) +
          -(p + q).negOnePow •
            (HomologicalComplex.ιTensorObj (HomComplexR R L M) K
              (p + (q + 1)) r (p + q + r + 1) (by omega)).hom
                (Cochain.single (L.d (-(q + 1)) (-q) ≫ f) (p + (q + 1)) ⊗ₜ[R] k) +
        (p + q).negOnePow •
          (HomologicalComplex.ιTensorObj (HomComplexR R L M) K
            (p + q) (r + 1) (p + q + r + 1) (by omega)).hom
              (Cochain.single f (p + q) ⊗ₜ[R] (K.d r (r + 1)).hom k)
      rw [differential_single]
      erw [TensorProduct.add_tmul, map_add]
      apply congrArg₂ (· + ·)
      · apply congrArg₂ (· + ·)
        · exact single_tensor_ι_congr R L M K _ _ (by omega) _ _
        · rw [← single_tensor_ι_congr R L M K
            (L.d (-(q + 1)) (-q) ≫ f) k
            (show p + q + 1 = p + (q + 1) by omega)
            (by omega) (by omega)]
          erw [TensorProduct.smul_tmul]
          simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R]
          erw [TensorProduct.tmul_smul, map_smul]
      · rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end TensorHom

/-! ## Evaluation into a double Hom complex -/

section DoubleHom

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex
  HomologicalComplex

variable {R : Type u} [CommRing R]

/-- **Stacks 0FNM.** The canonical evaluation morphism `K ⟶ Hom^•(Hom^•(K, M), M)`, obtained
from the evaluation morphism of Stacks 0A60 by inserting the identity cochain of `M` through the
tensor unit. -/
noncomputable def evaluationToDoubleHom
    (K M : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ HomComplexR R (HomComplexR R K M) M :=
  (λ_ K).inv ≫
    ((Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) M ≫
      Stacks.HomComplex.TensorHomMap.postcomp R M
        ((𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⊗ M) M (λ_ M).hom) ▷ K) ≫
    ChainEvaluation.chainEvaluation K M M

section

/-- On a summand `K^{i₁} ⊗ L^{i₂}` of a total complex, the morphism `f ▷ L` restricts to
`f^{i₁} ▷ L^{i₂}`. -/
private theorem ιTensorObj_whiskerRight (K K' L : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : K ⟶ K') (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) :
    ιTensorObj K L i₁ i₂ j h ≫ (f ▷ L).f j =
      (f.f i₁ ▷ L.X i₂) ≫ ιTensorObj K' L i₁ i₂ j h := by
  rw [← tensorHom_id f L, CochainComplex.ιTensorObj_tensorHom, HomologicalComplex.id_f,
    tensorHom_id]

/-- The tensor–Hom map of Stacks 0A62 out of the tensor unit is the inverse left unitor followed
by the unit identification. -/
private lemma unitTensorMap (M : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
    Stacks.HomComplex.TensorHomMap.tmulLeft R
        ((ConcreteCategory.hom
          (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv) 1) =
      (λ_ (M.X p)).inv ≫
        ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv ▷ M.X p) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  simp [Stacks.HomComplex.TensorHomMap.tmulLeft]
  rfl

/-- The unit of the monoidal structure, applied to an element of `K^n`, is the pure tensor of
the generator with that element. -/
private lemma unitTensorElement (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) (x : K.X n) :
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv ▷ K.X n).hom
        ((λ_ (K.X n)).inv.hom x) =
      (ConcreteCategory.hom
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv) 1 ⊗ₜ[R] x := by
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The composite of the tensor–Hom map of Stacks 0A62 with the left unitor sends the generator
of the tensor unit to the identity cochain of `M`. -/
private lemma identityCochain (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((Stacks.HomComplex.TensorHomMap.postcomp R M
        ((𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⊗ M) M (λ_ M).hom).f 0).hom
      (((Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) M).f 0).hom
        ((ConcreteCategory.hom
          (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv) 1)) =
      Cochain.ofHom (𝟙 M) := by
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain rfl : p = q := by omega
  change (ModuleCat.Hom.hom
      (((Stacks.HomComplex.TensorHomMap.Phiv R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) M 0 _).comp
        (Cochain.ofHom (λ_ M).hom) (add_zero 0)).v p p _)) y = _
  rw [Cochain.comp_v _ _ (add_zero 0) p p p (by omega) (by omega),
    Cochain.ofHom_v, Stacks.HomComplex.TensorHomMap.Phiv_v, unitTensorMap M p]
  have hu : (λ_ M).inv.f p =
      (λ_ (M.X p)).inv ≫
        ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv ▷ M.X p) ≫
          ιTensorObj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) M
            0 p p (by omega) :=
    HomologicalComplex.leftUnitor'_inv M p
  have hu_assoc := congrArg (fun z => z ≫ (λ_ M).hom.f p) hu
  simp only [← Category.assoc] at hu_assoc
  rw [← hu_assoc, ← HomologicalComplex.comp_f]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The first two factors of `evaluationToDoubleHom` insert `x ∈ K^n` as the pure tensor of the
identity cochain of `M` with `x`. -/
private lemma identityCochainTensor_apply
    (K M : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (x : K.X n) :
    ModuleCat.Hom.hom (((λ_ K).inv ≫
      ((Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) M ≫
        Stacks.HomComplex.TensorHomMap.postcomp R M
          ((𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⊗ M) M (λ_ M).hom) ▷ K)).f n) x =
      (GradedObject.Monoidal.ιTensorObj (HomComplexR R M M).X K.X
        0 n n (zero_add n)).hom (Cochain.ofHom (𝟙 M) ⊗ₜ[R] x) := by
  rw [HomologicalComplex.comp_f,
    show (λ_ K).inv.f n = (HomologicalComplex.leftUnitor' K).inv n from rfl,
    HomologicalComplex.leftUnitor'_inv]
  simp only [Category.assoc]
  rw [ιTensorObj_whiskerRight]
  change (ModuleCat.Hom.hom
      (ιTensorObj (HomComplexR R M M) K 0 n n (zero_add n))) _ =
    (ModuleCat.Hom.hom
      (ιTensorObj (HomComplexR R M M) K 0 n n (zero_add n))) _
  apply congrArg (ModuleCat.Hom.hom
    (ιTensorObj (HomComplexR R M M) K 0 n n (zero_add n)))
  change ((ModuleCat.Hom.hom
      ((Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) M ≫
        Stacks.HomComplex.TensorHomMap.postcomp R M
          ((𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⊗ M) M (λ_ M).hom).f 0)
      ((ConcreteCategory.hom
        (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv) 1)) ⊗ₜ[R] x) = _
  exact congrArg (fun z : Cochain M M 0 => z ⊗ₜ[R] x) (identityCochain M)

/-- Precomposition and postcomposition in the Hom complex commute. -/
private lemma precomp_postcomp' (A B C D : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : A ⟶ B) (g : C ⟶ D) :
    Stacks.HomComplex.TensorHomMap.precomp R A B C f ≫ Stacks.HomComplex.TensorHomMap.postcomp R A C
      D g =
      Stacks.HomComplex.TensorHomMap.postcomp R B C D g ≫ Stacks.HomComplex.TensorHomMap.precomp R A
        B D f := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (z : Cochain B C n)
  apply Cochain.ext
  intro p q hpq
  change (((Cochain.ofHom f).comp z (zero_add n)).comp (Cochain.ofHom g) (add_zero n)).v p q hpq =
    ((Cochain.ofHom f).comp (z.comp (Cochain.ofHom g) (add_zero n)) (zero_add n)).v p q hpq
  simp [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]

/-- The identity cochain is dinatural in the coefficient complex. -/
private lemma identityCochain_dinatural (M M' : CochainComplex (ModuleCat.{u} R) ℤ)
    (g : M ⟶ M') :
    (Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) M ≫
      Stacks.HomComplex.TensorHomMap.postcomp R M ((𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⊗ M) M
        (λ_ M).hom) ≫
        Stacks.HomComplex.TensorHomMap.postcomp R M M M' g =
    (Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) M' ≫
      Stacks.HomComplex.TensorHomMap.postcomp R M' ((𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⊗ M')
        M' (λ_ M').hom) ≫
        Stacks.HomComplex.TensorHomMap.precomp R M M' M' g := by
  rw [Category.assoc, ← Stacks.HomComplex.TensorHomMap.postcomp_comp,
    ← MonoidalCategory.leftUnitor_naturality, Stacks.HomComplex.TensorHomMap.postcomp_comp,
    ← Category.assoc, Stacks.HomComplex.TensorHomMap.Phi_dinatural_L, Category.assoc,
    precomp_postcomp', Category.assoc]

/-- The homogeneous formula of Stacks 0A60, in the indexing used below. -/
private lemma chainEvaluation_tmul'
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
    (t r a : ℤ) (φ : Cochain L M t) (k : K.X r) (ψ : Cochain K L (a - r)) :
    ((((ιTensorObj (HomComplexR R L M) K t r (t + r) rfl ≫
        (ChainEvaluation.chainEvaluation K L M).f (t + r)).hom) (φ ⊗ₜ[R] k)).v
          (a - r) (a + t) (by omega)).hom ψ =
      (r + (-a) * r).negOnePow •
        ((φ.v a (a + t) rfl).hom ((ψ.v r a (by omega)).hom k)) := by
  simpa only [ModuleCat.comp_apply] using
    ChainEvaluation.chainEvaluation_tmul K L M t r (t + r) (a - r) (a + t) a
      rfl (by omega) (by omega) (by omega) φ k ψ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the morphism of Stacks 0A60 at the identity cochain gives evaluation with the
Koszul sign `(-1)^(nm)`. -/
private lemma evaluation_identityCochain_apply
    (e : ∀ (K L M : CochainComplex (ModuleCat.{u} R) ℤ),
      (HomComplexR R L M ⊗ K) ⟶ HomComplexR R (HomComplexR R K L) M)
    (he : ∀ (K L M : CochainComplex (ModuleCat.{u} R) ℤ)
        (t r a : ℤ) (φ : Cochain L M t) (k : K.X r) (ψ : Cochain K L (a - r)),
      ((((ιTensorObj (HomComplexR R L M) K t r (t + r) rfl ≫
            (e K L M).f (t + r)).hom) (φ ⊗ₜ[R] k)).v (a - r) (a + t) (by omega)).hom ψ =
        (r + (-a) * r).negOnePow • ((φ.v a (a + t) rfl).hom ((ψ.v r a (by omega)).hom k)))
    (K M : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ) (x : K.X n) (f : Cochain K M m) :
    ((((ιTensorObj (HomComplexR R M M) K 0 n n (zero_add n) ≫
        (e K M M).f n).hom) (Cochain.ofHom (𝟙 M) ⊗ₜ[R] x)).v m (m + n) (by omega)).hom f =
      (n * m).negOnePow • (f.v n (m + n) (by omega)).hom x := by
  have key : ∀ (a d : ℤ) (hd : 0 + n = d) (s : ℤ) (hs : a - n = s) (q : ℤ) (hq : a + 0 = q)
      (g : Cochain K M s),
      ((((ιTensorObj (HomComplexR R M M) K 0 n d hd ≫
          (e K M M).f d).hom) (Cochain.ofHom (𝟙 M) ⊗ₜ[R] x)).v s q (by omega)).hom g =
        (n + (-a) * n).negOnePow • (g.v n q (by omega)).hom x := by
    intro a d hd s hs q hq g
    subst hd hs hq
    rw [he]
    congr 1
    have h0 : ∀ (q : ℤ) (hq : a + 0 = q) (hq' : n + (a - n) = q) (h3 : n + (a - n) = a),
        (ModuleCat.Hom.hom ((Cochain.ofHom (𝟙 M)).v a q hq))
            ((ModuleCat.Hom.hom (g.v n a h3)) x) =
          (ModuleCat.Hom.hom (g.v n q hq')) x := by
      intro q hq hq' h3
      obtain rfl : q = a := by omega
      simp
    exact h0 _ _ _ _
  rw [key (m + n) n (zero_add n) m (by omega) (m + n) (by omega) f]
  congr 1
  rw [Int.negOnePow_eq_iff]
  rw [show n + -(m + n) * n - n * m = -(n * (n - 1)) + 2 * (-(n * m)) by ring]
  exact (Int.even_mul_pred_self n).neg.add (even_two_mul _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0FNM.** The canonical evaluation into the double Hom complex sends homogeneous
`x ∈ K^n` and `f ∈ Hom^m(K, M)` to `(-1)^(nm) f(x)`. It is natural in `K` and dinatural in the
coefficient complex `M`. -/
@[stacks 0FNM]
theorem evaluationToDoubleHom_apply :
    (∀ (K M : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ)
        (x : K.X n) (f : Cochain K M m),
      ((((evaluationToDoubleHom K M).f n).hom x).v m (m + n) (by omega)).hom f =
        (n * m).negOnePow • (f.v n (m + n) (by omega)).hom x) ∧
    (∀ (K K' M : CochainComplex (ModuleCat.{u} R) ℤ) (g : K ⟶ K'),
      evaluationToDoubleHom K M ≫
          Stacks.HomComplex.TensorHomMap.precomp R (HomComplexR R K' M) (HomComplexR R K M) M
            (Stacks.HomComplex.TensorHomMap.precomp R K K' M g) =
        g ≫ evaluationToDoubleHom K' M) ∧
    (∀ (K M M' : CochainComplex (ModuleCat.{u} R) ℤ) (g : M ⟶ M'),
      evaluationToDoubleHom K M ≫
          Stacks.HomComplex.TensorHomMap.postcomp R (HomComplexR R K M) M M' g =
        evaluationToDoubleHom K M' ≫
          Stacks.HomComplex.TensorHomMap.precomp R (HomComplexR R K M) (HomComplexR R K M') M'
            (Stacks.HomComplex.TensorHomMap.postcomp R K M M' g)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K M n m x f
    have h := evaluation_identityCochain_apply _ chainEvaluation_tmul' K M n m x f
    rw [evaluationToDoubleHom]
    have hid := identityCochainTensor_apply K M n x
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h hid ⊢
    rw [hid]
    exact h
  · intro K K' M g
    dsimp only [evaluationToDoubleHom]
    rw [Category.assoc, Category.assoc, ← ChainEvaluation.chainEvaluation_natural_K K K' M M g,
      ← MonoidalCategory.whisker_exchange_assoc, ← MonoidalCategory.leftUnitor_inv_naturality_assoc]
  · intro K M M' g
    have hL := ChainEvaluation.chainEvaluation_natural_J K M M' M' g
    have hM := ChainEvaluation.chainEvaluation_natural_I K M M M' g
    dsimp only [evaluationToDoubleHom]
    simp only [Category.assoc]
    rw [← hM, ← hL, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, identityCochain_dinatural]

end

end DoubleHom

end CochainComplex.HomComplex

end
