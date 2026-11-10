module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CohomologyOfPoint
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.CycleClassComplements
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalGysinPoint
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalPairing

/-!
# The Künneth components of the class of the diagonal and the classes of rational points

In the proof of axiom (A6) for de Rham cohomology (Stacks, Proposition 0FWD) the source writes
`γ([Δ]) = γ_0 + … + γ_{2d}` with `γ_i ∈ H^i(X) ⊗ H^{2d-i}(X)` the Künneth components, notes that
only `γ_0` matters for `(1 ⊗ λ)γ([Δ])`, and identifies `γ_0` by pulling `γ([Δ])` back along
`x × id : X ⟶ X × X` for a rational point `x`: the result is `γ([x])`. This file proves these
steps for any data (D0), (D1), (D2') satisfying (A5), with `γ` the cycle class map of Lemma 0FIF
(`Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter.codimensionCycleClass`,
for a rule `ch` with `h : 𝔇.IsCohomologicalChernCharacter ch`), `X × X` the product
`Stacks.WeilCohomology.SmoothProjectiveScheme.prod` and `[Δ]` the class
`Stacks.WeilCohomology.SmoothProjectiveScheme.diagonalClass`.

* The Künneth isomorphism `K : H^*(X) ⊗ H^*(Y) ≅ H^*(X × Y)` of (A5) is graded: if
  `z ∈ H^N(X × Y)`, the component of `K⁻¹(z)` in `H^m(X) ⊗ H^n(Y)` vanishes for `m + n ≠ N`
  (`Stacks.WeilDeRham.map_proj_kunnethEquiv_symm_eq_zero`). Hence `(1 ⊗ λ)(K⁻¹ z)`, for `λ`
  supported in degree `2d` and `z ∈ H^{2d}(X × X)`, lies in `H^0(X)`
  (`Stacks.WeilDeRham.contractRight_kunnethEquiv_symm_mem_grade_zero`).
* For a rational point `x` (a morphism `x̂ : Spec(k) ⟶ X`), evaluation `ε_x : H^*(X) ⟶ F` is
  `x̂^*` followed by `H^*(Spec(k)) = F` (`Stacks.WeilDeRham.pointEval`). Pulling back along
  `j = x × id` is `ε_x ⊗ id` on `H^*(X) ⊗ H^*(X)`
  (`Stacks.WeilDeRham.pull_kunnethEquiv_eq_lid_rTensor_pointEval`), and
  `ε_x((1 ⊗ λ)s) = λ((ε_x ⊗ 1)s)` (`Stacks.WeilDeRham.apply_contractRight`,
  `Stacks.WeilDeRham.pointEval_contractRight_eq`).
* `j^*γ([Δ]) = γ([x])` (`Stacks.WeilDeRham.pullTw_codimensionCycleClass_diagonalClass`), from
  the Chow identity `j^![Δ] = [x]` (`Stacks.WeilDeRham.codimensionGysin_diagonalClass`) and the
  compatibility of `γ` with Gysin pullbacks
  (`…IsCohomologicalChernCharacter.codimensionCycleClass_codimensionGysin`).
* Together: `ε_x((1 ⊗ λ)γ([Δ])) = λ(γ([x]))`
  (`Stacks.WeilDeRham.pointEval_traceContract_diagonalClass` in
  `StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosed`).

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct DirectSum
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.WeilCohomology.DiagonalExpansion (contractRight contractRight_tmul)

universe u w

namespace Stacks.WeilDeRham

/-! ### Graded linear algebra -/

section Graded

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A] (𝒜 : ℤ → Submodule F A)
  [_root_.GradedAlgebra 𝒜]

/-- The degree-`i` projection fixes an element of degree `i`. -/
theorem gradedAlgebraProj_of_mem_same {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) :
    _root_.GradedAlgebra.proj 𝒜 i a = a := by
  rw [_root_.GradedAlgebra.proj_apply, decompose_of_mem_same _ ha]

/-- The degree-`i` projection kills an element of degree `j ≠ i`. -/
theorem gradedAlgebraProj_of_mem_ne {i j : ℤ} {a : A} (ha : a ∈ 𝒜 j) (hij : j ≠ i) :
    _root_.GradedAlgebra.proj 𝒜 i a = 0 := by
  rw [_root_.GradedAlgebra.proj_apply, decompose_of_mem_ne _ ha hij]

/-- An element all of whose homogeneous components of nonzero degree vanish lies in degree `0`. -/
theorem mem_zero_of_forall_gradedAlgebraProj_eq_zero {a : A}
    (h : ∀ m : ℤ, m ≠ 0 → _root_.GradedAlgebra.proj 𝒜 m a = 0) : a ∈ 𝒜 0 := by
  have hd : decompose 𝒜 a = DirectSum.of (fun i => 𝒜 i) 0 (decompose 𝒜 a 0) := by
    ext m
    by_cases hm : m = 0
    · subst hm
      rw [DirectSum.of_eq_same]
    · have h0 : (DirectSum.of (fun i => 𝒜 i) 0 (decompose 𝒜 a 0)) m = 0 :=
        DirectSum.of_eq_of_ne _ _ _ hm
      rw [h0, ZeroMemClass.coe_zero]
      have := h m hm
      rwa [_root_.GradedAlgebra.proj_apply] at this
  have : a = (decompose 𝒜).symm (decompose 𝒜 a) := ((decompose 𝒜).symm_apply_apply a).symm
  rw [this, hd, decompose_symm_of]
  exact SetLike.coe_mem _

end Graded

/-! ### Contractions -/

section Contract

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- `id ⊗ μ` commutes with `f ⊗ id`. -/
theorem contractRight_rTensor (μ : A →ₗ[F] F) (f : A →ₗ[F] A) (t : A ⊗[F] A) :
    contractRight μ (LinearMap.rTensor A f t) = f (contractRight μ t) := by
  induction t using TensorProduct.inductionOn <;> simp_all

/-- `id ⊗ μ` after `id ⊗ g` is `id ⊗ (μ ∘ g)`. -/
theorem contractRight_lTensor (μ : A →ₗ[F] F) (g : A →ₗ[F] A) (t : A ⊗[F] A) :
    contractRight μ (LinearMap.lTensor A g t) = contractRight (μ ∘ₗ g) t := by
  induction t using TensorProduct.inductionOn <;> simp_all

/-- **`ε((1 ⊗ μ)s) = μ((ε ⊗ 1)s)`** for linear forms `ε`, `μ` on `A` and `s ∈ A ⊗ A`. -/
theorem apply_contractRight (ε μ : A →ₗ[F] F) (t : A ⊗[F] A) :
    ε (contractRight μ t) = μ (TensorProduct.lid F A (LinearMap.rTensor A ε t)) := by
  induction t using TensorProduct.inductionOn <;> simp_all [mul_comm]

end Contract

variable {k : Type u} [Field k] {F : Type w} [Field F] {𝔇 : FirstChernClassData k F}

/-! ### The Künneth isomorphism is graded -/

section Kunneth

variable (hA5 : 𝔇.KunnethAxiom) (X Y : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The Künneth isomorphism is graded.** For `z ∈ H^N(X × Y)`, the component of `K⁻¹(z)` in
`H^m(X) ⊗ H^n(Y)` vanishes when `m + n ≠ N`. -/
theorem map_proj_kunnethEquiv_symm_eq_zero {N : ℤ} {z : 𝔇.H (prod X Y)}
    (hz : z ∈ 𝔇.grade (prod X Y) N) {m n : ℤ} (hmn : m + n ≠ N) :
    TensorProduct.map (_root_.GradedAlgebra.proj (𝔇.grade X) m)
      (_root_.GradedAlgebra.proj (𝔇.grade Y) n) ((𝔇.kunnethEquiv hA5 X Y).symm z) = 0 := by
  set κ := 𝔇.kunnethEquiv hA5 X Y
  have key : ∀ t : 𝔇.H X ⊗[F] 𝔇.H Y,
      TensorProduct.map (_root_.GradedAlgebra.proj (𝔇.grade X) m)
        (_root_.GradedAlgebra.proj (𝔇.grade Y) n)
        (κ.symm (_root_.GradedAlgebra.proj (𝔇.grade (prod X Y)) N (κ t))) = 0 := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, ht, ht', add_zero]
    | tmul x y =>
      induction x using DirectSum.Decomposition.inductionOn (ℳ := 𝔇.grade X) with
      | zero => simp
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx', add_zero]
      | homogeneous x =>
        rename_i i
        induction y using DirectSum.Decomposition.inductionOn (ℳ := 𝔇.grade Y) with
        | zero => simp
        | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy', add_zero]
        | homogeneous y =>
          rename_i j
          have hmem : κ ((x : 𝔇.H X) ⊗ₜ (y : 𝔇.H Y)) ∈ 𝔇.grade (prod X Y) (i + j) := by
            change 𝔇.pull (fst X Y) (x : 𝔇.H X) * 𝔇.pull (snd X Y) (y : 𝔇.H Y) ∈ _
            exact SetLike.GradedMul.mul_mem (𝔇.pull_grade _ i _ x.2) (𝔇.pull_grade _ j _ y.2)
          by_cases hij : i + j = N
          · rw [← hij, gradedAlgebraProj_of_mem_same _ hmem, LinearEquiv.symm_apply_apply,
              TensorProduct.map_tmul]
            by_cases hmi : i = m
            · have hnj : j ≠ n := fun h => hmn (by rw [← hmi, ← h, hij])
              rw [gradedAlgebraProj_of_mem_ne _ y.2 hnj, TensorProduct.tmul_zero]
            · rw [gradedAlgebraProj_of_mem_ne _ x.2 hmi, TensorProduct.zero_tmul]
          · rw [gradedAlgebraProj_of_mem_ne _ hmem hij, map_zero, map_zero]
  have h := key (κ.symm z)
  rwa [LinearEquiv.apply_symm_apply, gradedAlgebraProj_of_mem_same _ hz] at h

/-- **`(1 ⊗ λ)(K⁻¹ z)` lies in `H^0(X)`** for `z ∈ H^{2d}(X × X)` and a linear form `λ` on
`H^*(X)` supported in degree `2d`. -/
theorem contractRight_kunnethEquiv_symm_mem_grade_zero (d : ℤ) {z : 𝔇.H (prod X X)}
    (hz : z ∈ 𝔇.grade (prod X X) d) (μ : 𝔇.H X →ₗ[F] F)
    (hμ : ∀ y, μ y = μ (_root_.GradedAlgebra.proj (𝔇.grade X) d y)) :
    contractRight μ ((𝔇.kunnethEquiv hA5 X X).symm z) ∈ 𝔇.grade X 0 := by
  refine mem_zero_of_forall_gradedAlgebraProj_eq_zero _ fun m hm => ?_
  have hμ' : μ ∘ₗ _root_.GradedAlgebra.proj (𝔇.grade X) d = μ :=
    LinearMap.ext fun y => (hμ y).symm
  rw [← contractRight_rTensor, ← hμ', ← contractRight_lTensor, ← LinearMap.comp_apply
    (LinearMap.lTensor _ _), LinearMap.lTensor_comp_rTensor,
    map_proj_kunnethEquiv_symm_eq_zero hA5 X X hz (by omega), map_zero]

end Kunneth

/-! ### Rational points and evaluation -/

section Point

/-- A rational point `x : Spec(k) ⟶ X` as a morphism of smooth projective schemes. -/
def pointHom {X : (SmoothProjectiveScheme k).FullSubcategory}
    (x : Spec (.of k) ⟶ (toScheme k).obj X) (hx : x ≫ X.obj.hom = 𝟙 _) : point k ⟶ X :=
  homMk x hx

/-- The inclusion `X_U ⟶ X` of an open and closed subscheme, as a morphism of smooth projective
schemes; it is the morphism of `Stacks.WeilCohomology.SmoothProjectiveScheme.clopenSubobject`,
typed as a morphism of the full subcategory. -/
def clopenInclusion (X : (SmoothProjectiveScheme k).FullSubcategory)
    (U : ((toScheme k).obj X).Opens) (hU : IsClopen (U : Set ((toScheme k).obj X))) :
    clopen X U hU ⟶ X :=
  homMk U.ι rfl

/-- `clopenInclusion` is the morphism of `clopenSubobject`. -/
theorem clopenInclusion_eq (X : (SmoothProjectiveScheme k).FullSubcategory)
    (U : ((toScheme k).obj X).Opens) (hU : IsClopen (U : Set ((toScheme k).obj X))) :
    clopenInclusion X U hU = (clopenSubobject X U hU).hom :=
  rfl

/-- **The class `[x] = x_*[Spec(k)] ∈ CH^d(X)` of a rational point**, read in codimension `d`. -/
def pointChowClass {X : (SmoothProjectiveScheme k).FullSubcategory}
    (x : Spec (.of k) ⟶ (toScheme k).obj X) (hx : x ≫ X.obj.hom = 𝟙 _) (d : ℕ) :
    Stacks.Chow.codimensionChowGroup k X.obj.hom d :=
  haveI : IsSeparated X.obj.hom := (isProjective X).isSeparated
  haveI : IsProper x := isProper_of_comp_eq_id hx
  chowCodimPushforward k (𝟙 _) X.obj.hom x hx 0 d (chowCodimFundamental k (𝟙 _))

variable (hA5 : 𝔇.KunnethAxiom)

/-- `F ≅ H^*(Spec(k))`, the unit map, bijective by (A5). -/
def pointUnitEquiv : F ≃ₗ[F] 𝔇.H (point k) :=
  LinearEquiv.ofBijective (Algebra.linearMap F (𝔇.H (point k))) hA5.1

/-- **Evaluation at a rational point**, `ε_x : H^*(X) ⟶ H^*(Spec(k)) = F`. -/
def pointEval {X : (SmoothProjectiveScheme k).FullSubcategory} (x : point k ⟶ X) :
    𝔇.H X →ₗ[F] F :=
  (pointUnitEquiv hA5).symm.toLinearMap ∘ₗ (𝔇.pull x).toLinearMap

/-- `ε_x(a)`, viewed in `H^*(Spec(k))` through the unit map, is the pullback `x^* a`. -/
theorem algebraMap_pointEval {X : (SmoothProjectiveScheme k).FullSubcategory} (x : point k ⟶ X)
    (a : 𝔇.H X) : algebraMap F (𝔇.H (point k)) (pointEval hA5 x a) = 𝔇.pull x a := by
  have := (pointUnitEquiv hA5).apply_symm_apply (𝔇.pull x a)
  exact this

/-- Evaluation at a rational point is the identity on scalars: `ε_x(c · 1) = c`. -/
theorem pointEval_algebraMap {X : (SmoothProjectiveScheme k).FullSubcategory} (x : point k ⟶ X)
    (c : F) : pointEval hA5 x (algebraMap F (𝔇.H X) c) = c := by
  apply hA5.1.1
  rw [Algebra.linearMap_apply, Algebra.linearMap_apply, algebraMap_pointEval, AlgHom.commutes]

/-- **Pulling back along `x × id` is `ε_x ⊗ id`.** For `j : X ⟶ X × X` with `pr₁ ∘ j = x ∘ s_X`
and `pr₂ ∘ j = id`, `j^*(K(s)) = (ε_x ⊗ 1)(s)`. -/
theorem pull_kunnethEquiv_eq_lid_rTensor_pointEval {X : (SmoothProjectiveScheme k).FullSubcategory}
    (x : point k ⟶ X) {j : X ⟶ prod X X} (hjp : j ≫ fst X X = toPoint X ≫ x)
    (hjq : j ≫ snd X X = 𝟙 X) (s : 𝔇.H X ⊗[F] 𝔇.H X) :
    𝔇.pull j (𝔇.kunnethEquiv hA5 X X s) =
      TensorProduct.lid F (𝔇.H X) (LinearMap.rTensor (𝔇.H X) (pointEval hA5 x) s) := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' => simp only [map_add, hs, hs']
  | tmul a b =>
    change 𝔇.pull j (𝔇.pull (fst X X) a * 𝔇.pull (snd X X) b) = _
    rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← 𝔇.pull_comp,
      ← 𝔇.pull_comp, hjp, hjq, 𝔇.pull_id, 𝔇.pull_comp, AlgHom.comp_apply, AlgHom.id_apply,
      ← algebraMap_pointEval hA5 x a, AlgHom.commutes, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, Algebra.smul_def]

/-- **`ε_x((1 ⊗ μ)s) = μ(j^*K(s))`** for `j = x × id`. -/
theorem pointEval_contractRight_eq {X : (SmoothProjectiveScheme k).FullSubcategory}
    (x : point k ⟶ X) {j : X ⟶ prod X X} (hjp : j ≫ fst X X = toPoint X ≫ x)
    (hjq : j ≫ snd X X = 𝟙 X) (μ : 𝔇.H X →ₗ[F] F) (z : 𝔇.H (prod X X)) :
    pointEval hA5 x (contractRight μ ((𝔇.kunnethEquiv hA5 X X).symm z)) = μ (𝔇.pull j z) := by
  rw [apply_contractRight, ← pull_kunnethEquiv_eq_lid_rTensor_pointEval hA5 x hjp hjq,
    LinearEquiv.apply_symm_apply]

end Point

/-! ### `j^*γ([Δ]) = γ([x])` -/

section CycleClass

/-- **`j^![Δ] = [x]`**, for `j : X ⟶ X × X` with `pr₁ ∘ j = x ∘ s_X` and `pr₂ ∘ j = id`: the
identity `Stacks.WeilDeRham.codimensionGysin_diagonal_eq_point` for the class `[Δ]` of the
diagonal (`Stacks.WeilCohomology.SmoothProjectiveScheme.diagonalClass`), read in the category of
smooth projective schemes. -/
theorem codimensionGysin_diagonalClass {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hd : RelativeDimension X.obj.hom d)
    (x : Spec (.of k) ⟶ (toScheme k).obj X) (hx : x ≫ X.obj.hom = 𝟙 _) {j : X ⟶ prod X X}
    (hjp : j ≫ fst X X = toPoint X ≫ pointHom x hx) (hjq : j ≫ snd X X = 𝟙 X) :
    Stacks.Chow.codimensionGysin X.obj.hom (prod X X).obj.hom (w j) (d : ℤ)
        (diagonalClass X d) =
      pointChowClass x hx d := by
  have : IsSeparated X.obj.hom := (isProjective X).isSeparated
  have h := codimensionGysin_diagonal_eq_point (k := k) X.obj.hom hd x hx
    (isPullback_fst_snd X X) (δ := (toScheme k).map (diag X)) (j := (toScheme k).map j)
    (by rw [← Functor.map_comp, diag_fst, CategoryTheory.Functor.map_id]; rfl)
    (by rw [← Functor.map_comp, diag_snd, CategoryTheory.Functor.map_id]; rfl)
    (by rw [← Functor.map_comp, hjp, Functor.map_comp]; rfl)
    (by rw [← Functor.map_comp, hjq, CategoryTheory.Functor.map_id]; rfl)
  rw [diagonalClass, closedSubschemeClass_eq_chowCodimPushforward X.obj.hom (prod X X).obj.hom
    (diag X).hom.left (w (diag X)) hd d]
  exact h

variable [CharZero F] {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((toScheme k).obj X) → ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch)

/-- **`j^*γ([Δ]) = γ([x])`** in `H^{2d}(X)(d)`, for `j = x × id`. -/
theorem pullTw_codimensionCycleClass_diagonalClass
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (hd : RelativeDimension X.obj.hom d)
    (x : Spec (.of k) ⟶ (toScheme k).obj X) (hx : x ≫ X.obj.hom = 𝟙 _) {j : X ⟶ prod X X}
    (hjp : j ≫ fst X X = toPoint X ≫ pointHom x hx) (hjq : j ≫ snd X X = 𝟙 X) :
    𝔇.pullTw j d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) =
      h.codimensionCycleClass X d (pointChowClass x hx d) := by
  rw [← h.codimensionCycleClass_codimensionGysin, codimensionGysin_diagonalClass hd x hx hjp hjq]

/-- **`j^*γ([Δ]) = γ([x])`**, read in coordinates, for `j = x × id`. -/
theorem pull_untwistClass_diagonalClass
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} (hd : RelativeDimension X.obj.hom d)
    (x : Spec (.of k) ⟶ (toScheme k).obj X) (hx : x ≫ X.obj.hom = 𝟙 _) {j : X ⟶ prod X X}
    (hjp : j ≫ fst X X = toPoint X ≫ pointHom x hx) (hjq : j ≫ snd X X = 𝟙 X) :
    𝔇.pull j (𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d))) =
      𝔇.κ X d (h.codimensionCycleClass X d (pointChowClass x hx d)) := by
  rw [FirstChernClassData.untwistClass, ← FirstChernClassData.κ_pullTw,
    pullTw_codimensionCycleClass_diagonalClass h hd x hx hjp hjq]

variable (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom)

/-- The coordinates of the graded cycle class `γ(β) ∈ H^{2i}(X)(i)` are those of the cycle class
`γ(β) ∈ H^*(X)(i)`. -/
theorem coe_tateTwistCoordinates_cycleClassGrade (X : (SmoothProjectiveScheme k).FullSubcategory)
    (i : ℕ) (β : Stacks.Chow.codimensionChowGroup k X.obj.hom i) :
    ((tateTwistCoordinates 𝔇.coord (i : ℤ) (h.cycleClassGrade hA1 hA3 X i β) :
        𝔇.grade X (2 * (i : ℤ))) : 𝔇.H X) =
      𝔇.κ X i (h.codimensionCycleClass X i β) := by
  simp only [FirstChernClassData.IsCohomologicalChernCharacter.cycleClassGrade,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.apply_symm_apply]

end CycleClass

end Stacks.WeilDeRham

end
