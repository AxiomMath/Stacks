module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GlobalSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Condition (1) of Stacks 0FI0 implies condition (2)

Let `W` be data (D0)–(D3) satisfying (A), (B), (C) (`Stacks.WeilCohomology.WeilData`), `X` a
smooth projective scheme over `k` and `k' = Γ(X, 𝒪_X)`. Assume condition (1) of Stacks 0FI0:
there are closed points `x₁, …, x_r ∈ X` with separable residue fields such that
`H^0(X) → ⊕ᵢ H^0(xᵢ)` is injective. This file proves condition (2): `H^0(Spec(k')) → H^0(X)` is
an isomorphism. The proof is the source's, with the reduction to geometrically irreducible
schemes over a field done by one base change to a finite Galois extension `E/k`:

* `E` splits `k'` and contains every `κ(xᵢ)`. By Künneth (B)(a), as `H^*(Spec E)` sits in degree
  zero, `H^0(X ×_k Spec E)` is spanned by `pr₁^* a ∪ pr₂^* e`, `a ∈ H^0(X)`; and
  `xᵢ ×_k Spec E = ∐_τ Spec E` (Stacks 0FHQ's splitting), so the `E`-rational points
  `P_{i,τ} = (xᵢ ∘ Spec(τ), id)` of `X ×_k Spec E` detect `H^0(X ×_k Spec E)`
  (`Stacks.WeilCohomology.WeilData.eq_zero_of_pull_pointsBaseChange_eq_zero`).
* `X ×_k Spec E = ∐_σ Y_σ` over `Spec(k') ×_k Spec E = ∐_σ Spec E`, each `Y_σ` geometrically
  irreducible over `E` (`Concrete/GlobalSectionsBaseChange.lean`), and each `P_{i,τ}` is an
  `E`-rational point of one `Y_σ`. On `Y_σ` all rational points induce the same map
  `H^0(Y_σ) → H^0(Spec E)` (by Stacks 0FHV and (A)(b),
  `Stacks.WeilCohomology.WeilData.pullHom_ofOverFieldSection_eq`).
* Hence a class `b ∈ H^0(X ×_k Spec E)` agrees at every `P_{i,τ}` with the pullback of a class of
  `Spec(k') ×_k Spec E = ∐_σ Spec E`, so it is such a pullback; applied to `b = pr₁^* a` and read
  through Künneth, `a ∈ H^0(X)` comes from `H^0(Spec(k'))`.

## Main results

* `Stacks.WeilCohomology.WeilData.bijective_of_separablePointsDetectH0`: (1) ⇒ (2) of 0FI0.

## References

* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

attribute [local instance] residueFieldAlgebra

namespace SmoothProjectiveScheme

variable {X : (SmoothProjectiveScheme k).FullSubcategory} {x : X.obj.left}
  (hx : IsClosed ({x} : Set X.obj.left))
  (hsep : HasSeparableResidueField k X.obj.hom x)

/-- The inverse `x ⟶ Spec κ(x)` of `closedPointSpecHom`, the identity of `Spec κ(x)`. -/
def closedPointSpecInv : closedPointObj hx hsep ⟶ closedPointSpec hx hsep :=
  ObjectProperty.homMk (Over.homMk (𝟙 _)
    ((Category.id_comp _).trans (fromSpecResidueField_comp_hom x).symm))

/-- `closedPointSpecInv` followed by `closedPointSpecHom` is the identity of the point `x`. -/
theorem closedPointSpecInv_comp : closedPointSpecInv hx hsep ≫ closedPointSpecHom hx hsep = 𝟙 _ :=
  hom_ext_left (Category.id_comp _)

/-- The point `Spec κ(x)` of a closed point with separable residue field has dimension zero. -/
theorem topologicalKrullDim_closedPointSpec :
    topologicalKrullDim (closedPointSpec hx hsep).obj.left = 0 :=
  topologicalKrullDim_spec_field (X.obj.left.residueField x)

/-- A finite Galois extension `E` receiving `κ(x)` splits `Γ(Spec κ(x), 𝒪)`. -/
theorem splits_minpoly_globalSections_closedPointSpec {E : Type u} [Field E] [Algebra k E]
    [IsGalois k E] (ψ : X.obj.left.residueField x →ₐ[k] E)
    (c : globalSections (closedPointSpec hx hsep)) :
    ((minpoly k c).map (algebraMap k E)).Splits := by
  have := finite_residueField hx
  have : Algebra.IsSeparable k (X.obj.left.residueField x) := hsep
  have hinjc : Function.Injective (ψ.comp
      (FirstChernClassData.globalSectionsSpecAlgHom (k := k) (K' := X.obj.left.residueField x))) :=
    ψ.injective.comp (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (X.obj.left.residueField x))).hom).1
  rw [← minpoly.algHom_eq _ hinjc c]
  exact Normal.splits inferInstance _

end SmoothProjectiveScheme

namespace SmoothProjectiveScheme

variable (X : (SmoothProjectiveScheme k).FullSubcategory) [Nontrivial (globalSections X)]
  (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E]

/-- **Every `E`-rational point of `X ×_k Spec E` lies over one point `ι_σ` of
`Spec(k') ×_k Spec E`.** -/
theorem exists_baseChangeMap_eq_splitInj (P : spec k E ⟶ prod X (spec k E))
    (hP : P ≫ snd X (spec k E) = 𝟙 _) :
    ∃ s, P ≫ baseChangeMap X E = splitInj (topologicalKrullDim_specGlobalSections X) E s := by
  set hS := topologicalKrullDim_specGlobalSections X
  have := finite_globalSections hS
  have := etale_globalSections hS
  obtain ⟨θ, hθ⟩ := FirstChernClassData.exists_specMap_eq
    (P ≫ baseChangeMap X E ≫ fst _ _ ≫ (isoSpecOfDimensionZero hS).hom)
  refine ⟨θ, prod_hom_ext ?_ ?_⟩
  · rw [splitInj_fst, hθ]
    simp
  · rw [Category.assoc, SmoothProjectiveScheme.baseChangeMap_snd, hP, splitInj_snd]

variable (hsplit : ∀ a : globalSections (specGlobalSections X),
    ((minpoly k a).map (algebraMap k E)).Splits)
  (σ : globalSections (specGlobalSections X) →ₐ[k] E)

/-- An `E`-rational point of the piece `Y_σ`, as a morphism of smooth projective `k`-schemes. -/
def pieceSection (y : (fieldChowSituation E).S ⟶ piece X E σ) (hy : y ≫ pieceToSpec X E σ = 𝟙 _) :
    specField (k := k) E ⟶ pieceObj X E hsplit σ :=
  haveI := smooth_pieceToSpec X E hsplit σ
  ofOverFieldSection (k := k) (pieceToSpec X E σ) (isProjectiveMorphism_pieceToSpec X E σ) y hy

/-- A rational point of `X ×_k Spec E` over `ι_σ` is a rational point of `Y_σ`. -/
theorem exists_pieceSection (Q : spec k E ⟶ prod X (spec k E))
    (hQ : Q ≫ baseChangeMap X E = splitInj (topologicalKrullDim_specGlobalSections X) E σ) :
    ∃ (y : (fieldChowSituation E).S ⟶ piece X E σ) (hy : y ≫ pieceToSpec X E σ = 𝟙 _),
      pieceSection X E hsplit σ y hy ≫ pieceHom X E hsplit σ = Q := by
  refine ⟨Limits.pullback.lift Q.hom.left (𝟙 _) (by
      rw [Category.id_comp]
      exact congrArg (fun f ↦ f.hom.left) hQ),
    Limits.pullback.lift_snd _ _ _, hom_ext_left (Limits.pullback.lift_fst _ _ _)⟩

end SmoothProjectiveScheme

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

/-! ### Degrees and the Künneth map -/

/-- If `H^*(Y)` sits in degree zero, the degree-zero part of `κ(t)`, `κ` the Künneth map, is the
Künneth image of the degree-zero part of `t` in the first factor. -/
theorem decompose_kunnethMap_zero {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (hY : ∀ e : W.H Y, e ∈ W.grade Y 0) (t : W.H X ⊗[F] W.H Y) :
    (DirectSum.decompose (W.grade (prod X Y)) (W.kunnethMap X Y t) 0 : W.H (prod X Y)) =
      W.kunnethMap X Y (LinearMap.rTensor _ (_root_.GradedAlgebra.proj (W.grade X) 0) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a e =>
    rw [kunnethMap_tmul, LinearMap.rTensor_tmul, kunnethMap_tmul, _root_.GradedAlgebra.proj_apply,
      DirectSum.coe_decompose_mul_of_right_mem_zero _ (W.pull_grade _ 0 e (hY e)), pull_decompose]
  | add t t' ht ht' =>
    rw [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, ht, ht',
      map_add, map_add]

/-- Every class of a zero-dimensional `Z` has degree zero (Stacks 0FHQ (1)). -/
theorem mem_grade_zero_of_dimension_zero [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {Z : (SmoothProjectiveScheme k).FullSubcategory}
    (hZ : topologicalKrullDim Z.obj.left = 0) (e : W.H Z) : e ∈ W.grade Z 0 := by
  have h := H0_eq_top_of_grade_eq_bot (W := W) fun n hn ↦
    grade_eq_bot_of_dimension_zero hA hB hC hZ hn
  exact (h ▸ Algebra.mem_top : e ∈ W.H0 Z)

/-! ### Linear algebra -/

omit [Field k] in
/-- A tensor is the sum of its coordinates against a basis of the right factor. -/
theorem eq_sum_tmul_basis {M N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N]
    [Module F N] {ι : Type*} [Fintype ι] (b : Module.Basis ι F N) (t : M ⊗[F] N) :
    t = ∑ β, TensorProduct.rid F M (LinearMap.lTensor M (b.coord β) t) ⊗ₜ b β := by
  induction t using TensorProduct.inductionOn with
  | tmul m n =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_sum]
    congr 1
    exact (b.sum_repr n).symm
  | add t t' ht ht' =>
    conv_lhs => rw [ht, ht']
    simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]

omit [Field k] in
/-- The coordinates of a vanishing sum against a basis of the right factor vanish. -/
theorem eq_zero_of_sum_tmul_basis_eq_zero {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] {ι : Type*} [Fintype ι] (b : Module.Basis ι F N) (m : ι → M)
    (h : ∑ β, m β ⊗ₜ[F] b β = 0) (γ : ι) : m γ = 0 := by
  classical
  have := congrArg (fun t ↦ TensorProduct.rid F M (LinearMap.lTensor M (b.coord γ) t)) h
  simpa only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply, map_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using this

omit [Field k] in
/-- `id ⊗ λ` and `f ⊗ id` commute through `M ⊗ F = M`. -/
theorem rid_lTensor_rTensor {M M' N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup M']
    [Module F M'] [AddCommGroup N] [Module F N] (f : M →ₗ[F] M') (l : N →ₗ[F] F)
    (t : M ⊗[F] N) :
    TensorProduct.rid F M' (LinearMap.lTensor M' l (LinearMap.rTensor N f t)) =
      f (TensorProduct.rid F M (LinearMap.lTensor M l t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul m n => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-! ### Rational points of `X ×_k Spec E` over the points `xᵢ` -/

variable {E : Type u} [Field E] [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E]

/-- Pulling the Künneth class of `a ⊗ e` back along `f` multiplies the pullbacks of `a`, `e`
along the two components of `f`. -/
private theorem pull_kunnethMap_tmul_comp {X Y T : (SmoothProjectiveScheme k).FullSubcategory}
    (f : T ⟶ prod X Y) (a : W.H X) (e : W.H Y) :
    W.pull f (W.kunnethMap X Y (a ⊗ₜ e)) = W.pull (f ≫ fst X Y) a * W.pull (f ≫ snd X Y) e := by
  rw [kunnethMap_tmul, map_mul, W.pull_comp, W.pull_comp]
  rfl

/-- The value at `P_τ = (h ∘ Spec(τ), id)` of the Künneth class of `h^* a ⊗ e` is the
`τ`-coordinate of the splitting map at `h^* a ⊗ e`. -/
theorem splitMap_pull_tmul_apply {X Z : (SmoothProjectiveScheme k).FullSubcategory}
    (hZ : topologicalKrullDim Z.obj.left = 0) (h : Z ⟶ X) (a : W.H X) (e : W.H (spec k E))
    (τ : globalSections Z →ₐ[k] E) :
    W.splitMap hZ E (W.pull h a ⊗ₜ e) τ =
      W.pull (splitInj hZ E τ ≫ prodLift (fst _ _ ≫ h) (snd _ _)) (W.kunnethMap X _ (a ⊗ₜ e)) := by
  rw [splitMap_tmul, pull_kunnethMap_tmul_comp, Category.assoc, Category.assoc, prodLift_fst,
    prodLift_snd, splitInj_snd, W.pull_id, AlgHom.id_apply, ← Category.assoc, splitInj_fst,
    W.pull_comp]
  rfl

/-- **The rational points `P_{i,τ}` of `X ×_k Spec E` detect `H^0(X ×_k Spec E)`.** Let
`hᵢ : Zᵢ ⟶ X` be finitely many morphisms from zero-dimensional smooth projective schemes, with
`H^0(X) → ∏ᵢ H^0(Zᵢ)` injective, and `E/k` finite Galois splitting every `Γ(Zᵢ, 𝒪)`. Then a
class `b ∈ H^0(X ×_k Spec E)` vanishing at every `P_{i,τ} = (hᵢ ∘ Spec(τ), id)`,
`τ ∈ Hom_k(Γ(Zᵢ, 𝒪), E)`, is zero. By Künneth `b = Σ_β a_β ⊗ e_β` for a basis `e_β` of
`H^*(Spec E)` and `a_β ∈ H^0(X)`; its value at `P_{i,τ}` is the `τ`-coordinate of
`Σ_β hᵢ^* a_β ⊗ e_β` under `H^*(Zᵢ) ⊗ H^*(Spec E) = ∏_τ H^*(Spec E)`. -/
theorem eq_zero_of_pull_pointsBaseChange_eq_zero [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing) [IsGalois k E]
    {X : (SmoothProjectiveScheme k).FullSubcategory} {ι : Type*} [Finite ι]
    {Z : ι → (SmoothProjectiveScheme k).FullSubcategory}
    (hZ : ∀ i, topologicalKrullDim (Z i).obj.left = 0) (h : ∀ i, Z i ⟶ X)
    (hinj : Function.Injective fun a : W.grade X 0 ↦ fun i ↦ W.pullDeg (h i) 0 a)
    (hsplit : ∀ i (a : globalSections (Z i)), ((minpoly k a).map (algebraMap k E)).Splits)
    {b : W.H (prod X (spec k E))} (hb : b ∈ W.grade _ 0)
    (hP : ∀ i (τ : globalSections (Z i) →ₐ[k] E),
      W.pull (splitInj (hZ i) E τ ≫ prodLift (fst _ _ ≫ h i) (snd _ _)) b = 0) : b = 0 := by
  classical
  have hE0 := topologicalKrullDim_spec_eq_zero (k := k) E
  have hY : ∀ e : W.H (spec k E), e ∈ W.grade _ 0 := mem_grade_zero_of_dimension_zero hA hB hC hE0
  have := finiteDimensional_spec (L := E) hA hB hC
  obtain ⟨t, rfl⟩ := (hB.kunnethIsomorphism X (spec k E)).2 b
  set p0 := _root_.GradedAlgebra.proj (W.grade X) 0
  have hb0 : W.kunnethMap X _ t = W.kunnethMap X _ (LinearMap.rTensor _ p0 t) := by
    rw [← decompose_kunnethMap_zero hY, DirectSum.decompose_of_mem_same _ hb]
  rw [hb0] at hP ⊢
  let bas := Module.Free.chooseBasis F (W.H (spec k E))
  let a : Module.Free.ChooseBasisIndex F (W.H (spec k E)) → W.H X := fun β ↦
    p0 (TensorProduct.rid F _ (LinearMap.lTensor _ (bas.coord β) t))
  have ha0 : ∀ β, a β ∈ W.grade X 0 := fun β ↦ by
    simp only [a, p0, _root_.GradedAlgebra.proj_apply]
    exact (DirectSum.decompose (W.grade X) _ 0).2
  have ht : LinearMap.rTensor _ p0 t = ∑ β, a β ⊗ₜ bas β := by
    conv_lhs => rw [eq_sum_tmul_basis bas t]
    simp only [map_sum, LinearMap.rTensor_tmul, a]
  have hcoord : ∀ i β, W.pull (h i) (a β) = 0 := by
    intro i
    refine eq_zero_of_sum_tmul_basis_eq_zero bas _
      ((W.splitMap_bijective (hZ i) E hA hB hC (hsplit i)).1 ?_)
    rw [map_zero]
    funext τ
    have := hP i τ
    rw [ht, map_sum, map_sum] at this
    rw [map_sum, Finset.sum_apply]
    exact Eq.trans (Finset.sum_congr rfl fun β _ ↦ splitMap_pull_tmul_apply (hZ i) (h i) _ _ τ) this
  have hzero : ∀ β, a β = 0 := fun β ↦
    congrArg Subtype.val (hinj (a₁ := ⟨a β, ha0 β⟩) (a₂ := 0) (funext fun i ↦ Subtype.ext (by
      change W.pull (h i) (a β) = W.pull (h i) 0
      rw [hcoord i β, map_zero])))
  rw [ht]
  simp [hzero]

/-- If finitely many points `Spec κ(xᵢ) ⟶ X` detect `H^0(X)`, so do the composites
`Spec κ(xᵢ) ⟶ xᵢ ⟶ X`. -/
theorem injective_pullDeg_closedPointSpec {X : (SmoothProjectiveScheme k).FullSubcategory}
    {ι : Type*} {x : ι → X.obj.left} (hx : ∀ i, IsClosed ({x i} : Set X.obj.left))
    (hs : ∀ i, HasSeparableResidueField k X.obj.hom (x i))
    (hinj : Function.Injective fun a : W.grade X 0 ↦ fun i ↦
      W.pullDeg (closedPointHom (hx i) (hs i)) 0 a) :
    Function.Injective fun a : W.grade X 0 ↦ fun i ↦
      W.pullDeg (closedPointSpecHom (hx i) (hs i) ≫ closedPointHom (hx i) (hs i)) 0 a := by
  intro a a' haa
  apply hinj
  funext i
  have key : ∀ c : W.H X, W.pull (closedPointSpecInv (hx i) (hs i))
      (W.pull (closedPointSpecHom (hx i) (hs i) ≫ closedPointHom (hx i) (hs i)) c) =
        W.pull (closedPointHom (hx i) (hs i)) c := fun c ↦ by
    rw [← AlgHom.comp_apply, ← W.pull_comp, ← Category.assoc, closedPointSpecInv_comp,
      Category.id_comp]
  apply Subtype.ext
  change W.pull _ a.1 = W.pull _ a'.1
  rw [← key, ← key]
  exact congrArg _ (congrArg Subtype.val (congrFun haa i))

/-! ### The pieces `Y_σ` and the proof of (1) ⇒ (2) -/

variable (X : (SmoothProjectiveScheme k).FullSubcategory) [Nontrivial (globalSections X)]
  (hsplit : ∀ a : globalSections (specGlobalSections X),
    ((minpoly k a).map (algebraMap k E)).Splits)

omit [Nontrivial (globalSections X)] in
/-- Pulling a Künneth class back along `X ×_k Spec E ⟶ Spec(k') ×_k Spec E` pulls back its first
factor along `X ⟶ Spec(k')`. -/
theorem pull_baseChangeMap_kunnethMap (u : W.H (specGlobalSections X) ⊗[F] W.H (spec k E)) :
    W.pull (baseChangeMap X E) (W.kunnethMap _ _ u) =
      W.kunnethMap X _ (LinearMap.rTensor _ (W.pull (toSpecGlobalSections X)).toLinearMap u) := by
  induction u using TensorProduct.inductionOn with
  | tmul s e =>
    rw [pull_kunnethMap_tmul_comp, SmoothProjectiveScheme.baseChangeMap_fst,
      SmoothProjectiveScheme.baseChangeMap_snd, LinearMap.rTensor_tmul, kunnethMap_tmul,
      W.pull_comp]
    rfl
  | add u u' hu hu' => rw [map_add, map_add, hu, hu', map_add, map_add]

/-- **On a piece `Y_σ`, all `E`-rational points induce the same map on `H^0`** (Stacks 0FHV and
(A)(b): `Y_σ` is geometrically irreducible over `E`). -/
theorem pullHom_pieceSection_eq [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (σ : globalSections (specGlobalSections X) →ₐ[k] E)
    (y y' : (fieldChowSituation E).S ⟶ piece X E σ) (hy : y ≫ pieceToSpec X E σ = 𝟙 _)
    (hy' : y' ≫ pieceToSpec X E σ = 𝟙 _) :
    H0.pullHom W (pieceSection X E hsplit σ y hy) =
      H0.pullHom W (pieceSection X E hsplit σ y' hy') := by
  have := smooth_pieceToSpec X E hsplit σ
  have := geometricallyIrreducible_pieceToSpec X E hsplit σ
  exact pullHom_ofOverFieldSection_eq hA hB hC _ _ y y' hy hy'

include hsplit in
/-- Two rational points of `X ×_k Spec E` over the same `ι_σ` take the same value on
`H^0(X ×_k Spec E)`. -/
theorem pull_eq_of_baseChangeMap_eq [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {σ : globalSections (specGlobalSections X) →ₐ[k] E}
    {P P' : spec k E ⟶ prod X (spec k E)}
    (hP : P ≫ baseChangeMap X E = splitInj (topologicalKrullDim_specGlobalSections X) E σ)
    (hP' : P' ≫ baseChangeMap X E = splitInj (topologicalKrullDim_specGlobalSections X) E σ)
    {b : W.H (prod X (spec k E))} (hb : b ∈ W.grade _ 0) : W.pull P b = W.pull P' b := by
  obtain ⟨y, hy, rfl⟩ := exists_pieceSection X E hsplit σ P hP
  obtain ⟨y', hy', rfl⟩ := exists_pieceSection X E hsplit σ P' hP'
  have := congrArg (fun f ↦ (f ⟨W.pull (pieceHom X E hsplit σ) b, W.pull_grade _ 0 _ hb⟩).1)
    (W.pullHom_pieceSection_eq X hsplit hA hB hC σ y y' hy hy')
  simpa only [W.pull_comp, AlgHom.comp_apply, H0.coe_pullHom] using this

include hsplit in
/-- **A degree-zero class of `X ×_k Spec E` comes from `Spec(k') ×_k Spec E`** when finitely many
morphisms `hᵢ : Zᵢ ⟶ X` from zero-dimensional schemes split by `E` detect `H^0(X)`. -/
theorem exists_eq_pull_baseChangeMap [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) [IsGalois k E] {ι : Type*} [Finite ι]
    {Z : ι → (SmoothProjectiveScheme k).FullSubcategory}
    (hZ : ∀ i, topologicalKrullDim (Z i).obj.left = 0) (h : ∀ i, Z i ⟶ X)
    (hinj : Function.Injective fun a : W.grade X 0 ↦ fun i ↦ W.pullDeg (h i) 0 a)
    (hsplitZ : ∀ i (a : globalSections (Z i)), ((minpoly k a).map (algebraMap k E)).Splits)
    {b : W.H (prod X (spec k E))} (hb : b ∈ W.grade _ 0) :
    ∃ c, b = W.pull (baseChangeMap X E) c := by
  classical
  set hS := topologicalKrullDim_specGlobalSections X
  let P : ∀ i, (globalSections (Z i) →ₐ[k] E) → (spec k E ⟶ prod X (spec k E)) := fun i τ ↦
    splitInj (hZ i) E τ ≫ prodLift (fst _ _ ≫ h i) (snd _ _)
  have hPsnd : ∀ i τ, P i τ ≫ snd X (spec k E) = 𝟙 _ := fun i τ ↦ by
    simp only [P, Category.assoc, prodLift_snd, splitInj_snd]
  choose σ hσ using fun i τ ↦ exists_baseChangeMap_eq_splitInj X E (P i τ) (hPsnd i τ)
  let c' : (globalSections (specGlobalSections X) →ₐ[k] E) → W.H (spec k E) := fun s ↦
    if hex : ∃ p : (Σ i, (globalSections (Z i) →ₐ[k] E)), σ p.1 p.2 = s then
      W.pull (P hex.choose.1 hex.choose.2) b else 0
  have hc' : ∀ i τ, c' (σ i τ) = W.pull (P i τ) b := by
    intro i τ
    have hex : ∃ p : (Σ i, (globalSections (Z i) →ₐ[k] E)), σ p.1 p.2 = σ i τ := ⟨⟨i, τ⟩, rfl⟩
    simp only [c', dite_eq_left hex]
    exact W.pull_eq_of_baseChangeMap_eq X hsplit hA hB hC
      ((hσ _ _).trans (by rw [hex.choose_spec])) (hσ i τ) hb
  obtain ⟨t, ht⟩ := (W.splitMap_bijective hS E hA hB hC hsplit).2 c'
  set c := W.kunnethMap _ (spec k E) t
  have hcσ : ∀ s, W.pull (splitInj hS E s) c = c' s := fun s ↦ congrFun ht s
  have hSE : topologicalKrullDim (prod (specGlobalSections X) (spec k E)).obj.left = 0 :=
    topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional
      (isNonemptyEquidimensional_prod_spec hS E)
  refine ⟨c, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_pull_pointsBaseChange_eq_zero hA hB hC hZ h hinj hsplitZ
    (Submodule.sub_mem _ hb (W.pull_grade _ 0 _
      (mem_grade_zero_of_dimension_zero hA hB hC hSE c))) (fun i τ ↦ ?_)
  rw [map_sub, sub_eq_zero, ← AlgHom.comp_apply (W.pull (P i τ)), ← W.pull_comp, hσ i τ, hcσ,
    hc']

omit [Nontrivial (globalSections X)] in
/-- **A class of `X` whose pullback to `X ×_k Spec E` comes from `Spec(k') ×_k Spec E` comes from
`Spec(k')`** (Künneth (B)(a)). -/
theorem exists_pull_toSpecGlobalSections_eq [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing) {a : W.H X}
    {c : W.H (prod (specGlobalSections X) (spec k E))}
    (hac : W.pull (fst X (spec k E)) a = W.pull (baseChangeMap X E) c) :
    ∃ a', W.pull (toSpecGlobalSections X) a' = a := by
  obtain ⟨t, rfl⟩ := (hB.kunnethIsomorphism _ (spec k E)).2 c
  have hat := (hB.kunnethIsomorphism X _).1 (show W.kunnethMap X (spec k E) (a ⊗ₜ 1) =
      W.kunnethMap X _ (LinearMap.rTensor _ (W.pull (toSpecGlobalSections X)).toLinearMap t) by
    rw [kunnethMap_tmul, map_one, mul_one, ← pull_baseChangeMap_kunnethMap X, hac])
  have := nontrivial_spec (L := E) hA hB hC
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one F
    (one_ne_zero : (1 : W.H (spec k E)) ≠ 0)
  have key := congrArg (fun u ↦ TensorProduct.rid F _ (LinearMap.lTensor _ l u)) hat
  simp only [LinearMap.lTensor_tmul, hl, TensorProduct.rid_tmul, one_smul] at key
  rw [rid_lTensor_rTensor] at key
  exact ⟨TensorProduct.rid F _ (LinearMap.lTensor _ l t), key.symm⟩

omit [Nontrivial (globalSections X)] in
/-- **(1) ⇒ (2) of Stacks 0FI0.** If `H^0(X) → ⊕ᵢ H^0(xᵢ)` is injective for finitely many closed
points `xᵢ` with separable residue fields, then `H^0(Spec(k')) → H^0(X)` is an isomorphism,
`k' = Γ(X, 𝒪_X)`. -/
theorem bijective_of_separablePointsDetectH0 [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (h1 : W.SeparablePointsDetectH0 X) :
    Function.Bijective (W.pullDeg (toSpecGlobalSections X) 0) := by
  classical
  refine ⟨fun a a' haa ↦ Subtype.ext (W.injective_pull_toSpecGlobalSections hA hB hC X
    (congrArg Subtype.val haa)), fun a ↦ ?_⟩
  rcases isEmpty_or_nonempty X.obj.left with hX | ⟨⟨x0⟩⟩
  · have := W.subsingleton_of_isEmpty hB.kunnethIsomorphism hC.pullback hC.mul hC.point X
    exact ⟨0, Subtype.ext (Subsingleton.elim _ _)⟩
  have : Nontrivial (globalSections X) :=
    RingHom.domain_nontrivial (X.obj.left.Γevaluation x0).hom
  obtain ⟨r, x, hx, hs, hinj⟩ := h1
  obtain ⟨r', xc, hxc, hsc, hcov⟩ := exists_separablePoints_toSpecΓ X
  let y : Fin r ⊕ Fin r' → X.obj.left := Sum.elim x xc
  have hy : ∀ j, IsClosed ({y j} : Set X.obj.left) := by
    rintro (j | j)
    exacts [hx j, hxc j]
  have hys : ∀ j, HasSeparableResidueField k X.obj.hom (y j) := by
    rintro (j | j)
    exacts [hs j, hsc j]
  let L : ULift.{u} (Fin r ⊕ Fin r') → Type u := fun j ↦ X.obj.left.residueField (y j.down)
  have : ∀ j, FiniteDimensional k (L j) := fun j ↦ finite_residueField (hy j.down)
  have : ∀ j, Algebra.IsSeparable k (L j) := fun j ↦ hys j.down
  obtain ⟨E, _, _, _, _, ψ, hE⟩ := FirstChernClassData.exists_isGalois_embeddings (k := k) L
  have hsplitS : ∀ a : globalSections (specGlobalSections X),
      ((minpoly k a).map (algebraMap k E)).Splits := by
    intro a
    have hinjS : Function.Injective
        ((AlgHom.pi (R := k) (A := L) fun j ↦ evaluationAlgHom (y j.down)).comp
          (FirstChernClassData.globalSectionsSpecAlgHom (k := k) (K' := globalSections X))) := by
      intro c c' hcc
      apply (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (globalSections X))).hom).1
      apply injective_Γevaluation_of_toSpecΓ X xc hcov
      funext i
      exact congrFun hcc ⟨Sum.inr i⟩
    rw [← minpoly.algHom_eq _ hinjS a]
    exact hE _
  obtain ⟨c, hc⟩ := exists_eq_pull_baseChangeMap X hsplitS hA hB hC
    (Z := fun i ↦ closedPointSpec (hx i) (hs i))
    (fun i ↦ topologicalKrullDim_closedPointSpec (hx i) (hs i))
    (fun i ↦ closedPointSpecHom (hx i) (hs i) ≫ closedPointHom (hx i) (hs i))
    (injective_pullDeg_closedPointSpec hx hs hinj)
    (fun i ↦ splits_minpoly_globalSections_closedPointSpec (hx i) (hs i) (ψ ⟨Sum.inl i⟩))
    (b := W.pull (fst X (spec k E)) a.1) (W.pull_grade _ 0 _ a.2)
  obtain ⟨a', ha'⟩ := exists_pull_toSpecGlobalSections_eq X hA hB hC hc
  exact ⟨⟨a', mem_grade_zero_of_dimension_zero hA hB hC
    (topologicalKrullDim_specGlobalSections X) a'⟩, Subtype.ext ha'⟩

end WeilData

end Stacks.WeilCohomology

end
