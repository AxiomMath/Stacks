module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIdempotent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationTrace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The action of a cohomology class of `X × Y` from `H^*(X)` to `H^*(Y)`

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A) and (B), and let `X`, `Y` be
nonempty smooth projective schemes over `k`, equidimensional of dimensions `d` and `e`. The proof
of Stacks 0FHL lets a correspondence `c ∈ Corr⁰(X, Y)` act on cohomology by

  `a ↦ pr₂,*(γ(c) ∪ pr₁^*a)`.

This file defines that action for an arbitrary class `z ∈ H^*(X × Y)` in place of `γ(c)`,
degree by degree, through Poincaré duality on `Y`: `blockAct z a ∈ H^i(Y)` is the class with

  `∫_Y blockAct z a ∪ b = ∫_{X × Y} z ∪ pr₁^*a ∪ pr₂^*b`   for `b ∈ H^{2e-i}(Y)`,

which is the trace equation characterising `pr₂,*(z ∪ pr₁^*a)` (`blockAct_spec`). It then proves
the cohomological half of every step of the source's proof, for classes `z` with the trace
properties that the cycle classes of the source have:

* **composition** (`blockAct_comp`): if `w ∈ H^*(X × Z)` satisfies
  `∫_{X × Z} w ∪ v = ∫_{X × Y × Z} pr₁₂^*z ∪ pr₂₃^*z' ∪ pr₁₃^*v` — the trace form of
  `w = pr₁₃,*(pr₁₂^*z ∪ pr₂₃^*z')` — then `blockAct w = blockAct z' ∘ blockAct z`. This is the
  displayed chain of equalities of the source; the base change `pr₂^* pr₂,* = pr₂₃,* pr₁₂^*`
  (the second equality, from Stacks 0FHC) is replaced by its trace form, proved from (B)(a) and
  (B)(b) (`traceProj_pull_fst_mul_eq`);
* **graphs and the identity** (`blockAct_graph`, `blockAct_eq_self`): if
  `∫_{X × Y} z ∪ v = ∫_{Y'} (g, ι)^*v` for morphisms `g : Y' ⟶ X`, `ι : Y' ⟶ Y` — the trace form
  of `z = (g, ι)_*1`, the class of a graph — then `∫_Y blockAct z a ∪ b = ∫_{Y'} g^*a ∪ ι^*b`;
  for the diagonal this is `blockAct z = id`, the step "`G([Δ]) = id` by Lemmas 0FHH and 0FHC";
* **tensor products** (`blockAct_tensor`): the action of `pr₁₃^*z ∪ pr₂₄^*z'` on
  `(X × X') × (Y × Y')` is the tensor product of the actions, through the Künneth maps;
* **open and closed pieces** (`blockAct_prodMap`): if `∫_{P × Q} w ∪ v = ∫_{U × V} z ∪ (i×j)^*v`
  then `∫_Q blockAct w a ∪ b = ∫_V blockAct z (i^*a) ∪ j^*b`.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHC](https://stacks.math.columbia.edu/tag/0FHC)
* [Stacks Project, Tag 0FHB](https://stacks.math.columbia.edu/tag/0FHB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The projection `pr₂₃ : (X × Y) × Z ⟶ Y × Z`. -/
def prodPr₂₃ (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) : prod (prod X Y) Z ⟶ prod Y Z :=
  prodLift (fst (prod X Y) Z ≫ snd X Y) (snd (prod X Y) Z)

/-- The projection `pr₁₃ : (X × Y) × Z ⟶ X × Z`. -/
def prodPr₁₃ (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) : prod (prod X Y) Z ⟶ prod X Z :=
  prodLift (fst (prod X Y) Z ≫ fst X Y) (snd (prod X Y) Z)

/-- The first component of `pr₂₃` is the projection to `Y`. -/
@[reassoc (attr := simp)]
theorem prodPr₂₃_fst (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    prodPr₂₃ X Y Z ≫ fst Y Z = fst (prod X Y) Z ≫ snd X Y :=
  prodLift_fst _ _

/-- The second component of `pr₂₃` is the projection to `Z`. -/
@[reassoc (attr := simp)]
theorem prodPr₂₃_snd (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    prodPr₂₃ X Y Z ≫ snd Y Z = snd (prod X Y) Z :=
  prodLift_snd _ _

/-- The first component of `pr₁₃` is the projection to `X`. -/
@[reassoc (attr := simp)]
theorem prodPr₁₃_fst (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    prodPr₁₃ X Y Z ≫ fst X Z = fst (prod X Y) Z ≫ fst X Y :=
  prodLift_fst _ _

/-- The second component of `pr₁₃` is the projection to `Z`. -/
@[reassoc (attr := simp)]
theorem prodPr₁₃_snd (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    prodPr₁₃ X Y Z ≫ snd X Z = snd (prod X Y) Z :=
  prodLift_snd _ _

/-- The projection `pr₁₃ : (X × X') × (Y × Y') ⟶ X × Y`. -/
def prodTensorPr₁₃ (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    prod (prod X X') (prod Y Y') ⟶ prod X Y :=
  prodLift (fst _ _ ≫ fst X X') (snd _ _ ≫ fst Y Y')

/-- The projection `pr₂₄ : (X × X') × (Y × Y') ⟶ X' × Y'`. -/
def prodTensorPr₂₄ (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    prod (prod X X') (prod Y Y') ⟶ prod X' Y' :=
  prodLift (fst _ _ ≫ snd X X') (snd _ _ ≫ snd Y Y')

/-- The first component of `pr₁₃ : (X × X') × (Y × Y') ⟶ X × Y` is the projection to `X`. -/
@[reassoc (attr := simp)]
theorem prodTensorPr₁₃_fst (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    prodTensorPr₁₃ X X' Y Y' ≫ fst X Y = fst _ _ ≫ fst X X' :=
  prodLift_fst _ _

/-- The second component of `pr₁₃ : (X × X') × (Y × Y') ⟶ X × Y` is the projection to `Y`. -/
@[reassoc (attr := simp)]
theorem prodTensorPr₁₃_snd (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    prodTensorPr₁₃ X X' Y Y' ≫ snd X Y = snd _ _ ≫ fst Y Y' :=
  prodLift_snd _ _

/-- The first component of `pr₂₄ : (X × X') × (Y × Y') ⟶ X' × Y'` is the projection to `X'`. -/
@[reassoc (attr := simp)]
theorem prodTensorPr₂₄_fst (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    prodTensorPr₂₄ X X' Y Y' ≫ fst X' Y' = fst _ _ ≫ snd X X' :=
  prodLift_fst _ _

/-- The second component of `pr₂₄ : (X × X') × (Y × Y') ⟶ X' × Y'` is the projection to `Y'`. -/
@[reassoc (attr := simp)]
theorem prodTensorPr₂₄_snd (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    prodTensorPr₂₄ X X' Y Y' ≫ snd X' Y' = snd _ _ ≫ snd Y Y' :=
  prodLift_snd _ _

/-- The middle interchange `(X × X') × (Y × Y') ⟶ (X × Y) × (X' × Y')`, `(pr₁₃, pr₂₄)`. -/
def prodTensorShuffle (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    prod (prod X X') (prod Y Y') ⟶ prod (prod X Y) (prod X' Y') :=
  prodLift (prodTensorPr₁₃ X X' Y Y') (prodTensorPr₂₄ X X' Y Y')

/-- The inverse of the middle interchange. -/
def prodTensorShuffleInv (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    prod (prod X Y) (prod X' Y') ⟶ prod (prod X X') (prod Y Y') :=
  prodLift (prodLift (fst _ _ ≫ fst X Y) (snd _ _ ≫ fst X' Y'))
    (prodLift (fst _ _ ≫ snd X Y) (snd _ _ ≫ snd X' Y'))

/-- The middle interchange is an isomorphism, with inverse `prodTensorShuffleInv`. -/
instance (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    IsIso (prodTensorShuffle X X' Y Y') :=
  ⟨prodTensorShuffleInv X X' Y Y',
    prod_hom_ext (prod_hom_ext (by simp [prodTensorShuffle, prodTensorShuffleInv])
        (by simp [prodTensorShuffle, prodTensorShuffleInv]))
      (prod_hom_ext (by simp [prodTensorShuffle, prodTensorShuffleInv])
        (by simp [prodTensorShuffle, prodTensorShuffleInv])),
    prod_hom_ext (prod_hom_ext (by simp [prodTensorShuffle, prodTensorShuffleInv])
        (by simp [prodTensorShuffle, prodTensorShuffleInv]))
      (prod_hom_ext (by simp [prodTensorShuffle, prodTensorShuffleInv])
        (by simp [prodTensorShuffle, prodTensorShuffleInv]))⟩

/-- The underlying morphism of schemes of the middle interchange is an isomorphism. -/
instance (X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory) :
    IsIso (prodTensorShuffle X X' Y Y').hom.left :=
  inferInstanceAs (IsIso ((ObjectProperty.ι _ ⋙ Over.forget _).map (prodTensorShuffle X X' Y Y')))

end SmoothProjectiveScheme

namespace WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

/-! ### Classes of even degree are central -/

/-- A class of even degree commutes with every class: graded commutativity (D1). -/
theorem mul_comm_of_mem_grade_two_mul {X : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ}
    {x : W.H X} (hx : x ∈ W.grade X (2 * n)) (y : W.H X) : x * y = y * x := by
  induction y using DirectSum.Decomposition.inductionOn (W.grade X) with
  | zero => simp
  | @homogeneous j y =>
    rw [W.graded_comm X (2 * n) j x _ hx y.2, Int.negOnePow_even _ ⟨n * j, by ring⟩]
    simp
  | add y y' hy hy' => rw [mul_add, add_mul, hy, hy']

/-- Pullbacks compose: `f^* g^* x = (f ≫ g)^* x`. -/
theorem pull_pull {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : W.H Z) : W.pull f (W.pull g x) = W.pull (f ≫ g) x := by
  rw [W.pull_comp]
  rfl

/-! ### The action -/

variable (W)

/-- The bilinear form `(a, b) ↦ ∫_{X × Y} z ∪ pr₁^*a ∪ pr₂^*b`. -/
def blockForm {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (z : W.H (prod X Y)) (i j : ℤ) :
    W.grade X i →ₗ[F] W.grade Y j →ₗ[F] F :=
  LinearMap.mk₂ F (fun a b ↦ W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY)
      (z * W.pull (fst X Y) a * W.pull (snd X Y) b))
    (fun a a' b ↦ by simp [mul_add, add_mul]) (fun c a b ↦ by simp)
    (fun a b b' ↦ by simp [mul_add]) (fun c a b ↦ by simp)

/-- The value of `blockForm z i j` on `(a, b)` is `∫_{X × Y} z ∪ pr₁^*a ∪ pr₂^*b`. -/
theorem blockForm_apply {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (z : W.H (prod X Y)) (i j : ℤ) (a : W.grade X i) (b : W.grade Y j) :
    W.blockForm hX hY z i j a b = W.traceProj (prod X Y) (d + e)
      (isNonemptyEquidimensional_prod hX hY) (z * W.pull (fst X Y) a * W.pull (snd X Y) b) :=
  rfl

/-- **The action of a class `z ∈ H^*(X × Y)` on `H^i(X)`**, `a ↦ pr₂,*(z ∪ pr₁^*a)`, for `X`, `Y`
nonempty equidimensional of dimensions `d`, `e`: the class of `H^i(Y)` representing
`b ↦ ∫_{X × Y} z ∪ pr₁^*a ∪ pr₂^*b` on `H^{2e-i}(Y)` (axiom (A)(b)). -/
def blockAct (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (z : W.H (prod X Y)) (i : ℤ) : W.grade X i →ₗ[F] W.grade Y i :=
  W.traceDual hA Y hY i ∘ₗ W.blockForm hX hY z i (2 * e - i)

variable {W}

/-- **The trace equation of the action**: `∫_Y blockAct z a ∪ b = ∫_{X × Y} z ∪ pr₁^*a ∪ pr₂^*b`
for `b ∈ H^{2e-i}(Y)`. -/
theorem blockAct_spec (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (z : W.H (prod X Y)) {i : ℤ} (a : W.grade X i) (b : W.grade Y (2 * e - i)) :
    W.traceProj Y e hY ((W.blockAct hA hX hY z i a : W.H Y) * b) =
      W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY)
        (z * W.pull (fst X Y) a * W.pull (snd X Y) b) :=
  traceProj_traceDual_mul hA Y hY i _ b

/-- The trace equation of the action against every class `b ∈ H^*(Y)`, for `z ∈ H^{2d}(X × Y)`:
off the complementary degree both sides vanish. -/
theorem blockAct_spec' (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    {z : W.H (prod X Y)} (hz : z ∈ W.grade (prod X Y) (2 * d)) {i : ℤ} (a : W.grade X i)
    (b : W.H Y) :
    W.traceProj Y e hY ((W.blockAct hA hX hY z i a : W.H Y) * b) =
      W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY)
        (z * W.pull (fst X Y) a * W.pull (snd X Y) b) := by
  induction b using DirectSum.Decomposition.inductionOn (W.grade Y) with
  | zero => simp
  | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add, map_add]
  | @homogeneous m b =>
    by_cases hm : m = 2 * e - i
    · subst hm
      exact blockAct_spec hA hX hY z a b
    · rw [W.traceProj_of_mem_ne Y e hY (SetLike.GradedMul.mul_mem (W.blockAct hA hX hY z i a).2
          b.2) (by omega),
        W.traceProj_of_mem_ne _ _ _ (SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem hz
          (W.pull_grade _ i _ a.2)) (W.pull_grade _ m _ b.2)) (by push_cast; omega)]

/-- The action is characterised by its trace equation. -/
theorem eq_blockAct_iff (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (z : W.H (prod X Y)) {i : ℤ} (a : W.grade X i) (u : W.grade Y i) :
    u = W.blockAct hA hX hY z i a ↔ ∀ b : W.grade Y (2 * e - i),
      W.traceProj Y e hY ((u : W.H Y) * b) =
        W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY)
          (z * W.pull (fst X Y) a * W.pull (snd X Y) b) :=
  eq_traceDual_iff hA hY _ u

/-- A linear map satisfying the trace equation of the action of `z` is the action of `z`. -/
private theorem blockAct_eq_of_forall (hA : W.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (z : W.H (prod X Y)) (i : ℤ) (φ : W.grade X i →ₗ[F] W.grade Y i)
    (h : ∀ (a : W.grade X i) (b : W.grade Y (2 * e - i)),
      W.traceProj Y e hY ((φ a : W.H Y) * b) =
        W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY)
          (z * W.pull (fst X Y) a * W.pull (snd X Y) b)) :
    W.blockAct hA hX hY z i = φ := by
  ext a
  exact congrArg Subtype.val ((eq_blockAct_iff hA hX hY z a _).2 (h a)).symm

/-- The action is additive in the class. -/
theorem blockAct_add (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (z z' : W.H (prod X Y)) (i : ℤ) :
    W.blockAct hA hX hY (z + z') i = W.blockAct hA hX hY z i + W.blockAct hA hX hY z' i := by
  refine blockAct_eq_of_forall hA hX hY _ _ _ fun a b ↦ ?_
  rw [LinearMap.add_apply, Submodule.coe_add, add_mul, map_add, blockAct_spec, blockAct_spec,
    add_mul, add_mul, map_add]

/-- The action is linear in the class. -/
theorem blockAct_smul (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (c : F) (z : W.H (prod X Y)) (i : ℤ) :
    W.blockAct hA hX hY (c • z) i = c • W.blockAct hA hX hY z i := by
  refine blockAct_eq_of_forall hA hX hY _ _ _ fun a b ↦ ?_
  rw [LinearMap.smul_apply, Submodule.coe_smul, smul_mul_assoc, map_smul, blockAct_spec,
    smul_mul_assoc, smul_mul_assoc, map_smul]

/-- The action of the zero class is zero. -/
theorem blockAct_zero (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (i : ℤ) :
    W.blockAct hA hX hY 0 i = 0 := by
  simpa using blockAct_smul hA hX hY 0 0 i

/-! ### Composition -/

/-- **The trace form of the base change `pr₂^* pr₂,* = pr₂₃,* pr₁₂^*`** (Stacks 0FHC): for
`u = blockAct z a`, `∫_{Y × Z} pr₁^*u ∪ v = ∫_{X × Y × Z} pr₁₂^*(z ∪ pr₁^*a) ∪ pr₂₃^*v` for every
`v ∈ H^*(Y × Z)`. -/
theorem traceProj_pull_fst_mul_eq (hA : W.PerfectPairing) (hBa : W.KunnethIsomorphism)
    (hK : W.KunnethTrace) {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {d e f : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hZ : IsNonemptyEquidimensional Z f) {z : W.H (prod X Y)}
    (hz : z ∈ W.grade (prod X Y) (2 * d)) {i : ℤ} (a : W.grade X i) (v : W.H (prod Y Z)) :
    W.traceProj (prod Y Z) (e + f) (isNonemptyEquidimensional_prod hY hZ)
        (W.pull (fst Y Z) (W.blockAct hA hX hY z i a) * v) =
      W.traceProj (prod (prod X Y) Z) (d + e + f)
        (isNonemptyEquidimensional_prod (isNonemptyEquidimensional_prod hX hY) hZ)
        (W.pull (fst (prod X Y) Z) (z * W.pull (fst X Y) a) * W.pull (prodPr₂₃ X Y Z) v) := by
  obtain ⟨t, rfl⟩ := (hBa Y Z).2 v
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, mul_add, map_add, ht, ht', map_add, mul_add, map_add]
  | tmul y c =>
    have hXY := isNonemptyEquidimensional_prod hX hY
    have key : W.pull (fst (prod X Y) Z) (z * W.pull (fst X Y) (a : W.H X)) *
        W.pull (prodPr₂₃ X Y Z) (W.pull (fst Y Z) y * W.pull (snd Y Z) c) =
        W.pull (fst (prod X Y) Z) (z * W.pull (fst X Y) (a : W.H X) * W.pull (snd X Y) y) *
          W.pull (snd (prod X Y) Z) c := by
      simp only [map_mul, pull_pull, prodPr₂₃_fst, prodPr₂₃_snd, mul_assoc]
    rw [kunnethMap_tmul, ← mul_assoc, ← map_mul,
      traceProj_pull_fst_mul_pull_snd hK hY hZ, blockAct_spec' hA hX hY hz, key,
      traceProj_pull_fst_mul_pull_snd hK hXY hZ]

/-- **Composition of the actions** (the displayed computation of the proof of Stacks 0FHL): if
`w ∈ H^*(X × Z)` satisfies `∫_{X × Z} w ∪ v = ∫_{X × Y × Z} pr₁₂^*z ∪ pr₂₃^*z' ∪ pr₁₃^*v` for
all `v` — the trace form of `w = pr₁₃,*(pr₁₂^*z ∪ pr₂₃^*z')` — then
`blockAct w = blockAct z' ∘ blockAct z`. -/
theorem blockAct_comp (hA : W.PerfectPairing) (hBa : W.KunnethIsomorphism) (hK : W.KunnethTrace)
    {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {d e f : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hZ : IsNonemptyEquidimensional Z f) {z : W.H (prod X Y)}
    (hz : z ∈ W.grade (prod X Y) (2 * d)) {z' : W.H (prod Y Z)}
    (hz' : z' ∈ W.grade (prod Y Z) (2 * e)) (w : W.H (prod X Z))
    (hw : ∀ v : W.H (prod X Z),
      W.traceProj (prod X Z) (d + f) (isNonemptyEquidimensional_prod hX hZ) (w * v) =
        W.traceProj (prod (prod X Y) Z) (d + e + f)
          (isNonemptyEquidimensional_prod (isNonemptyEquidimensional_prod hX hY) hZ)
          (W.pull (fst (prod X Y) Z) z * W.pull (prodPr₂₃ X Y Z) z' *
            W.pull (prodPr₁₃ X Y Z) v)) (i : ℤ) :
    W.blockAct hA hX hZ w i = W.blockAct hA hY hZ z' i ∘ₗ W.blockAct hA hX hY z i := by
  refine blockAct_eq_of_forall hA hX hZ _ _ _ fun a b ↦ ?_
  rw [LinearMap.comp_apply, blockAct_spec, mul_assoc w, hw,
    mul_comm_of_mem_grade_two_mul hz' (W.pull (fst Y Z) _), mul_assoc,
    traceProj_pull_fst_mul_eq hA hBa hK hX hY hZ hz a]
  have hz'' := W.pull_grade (prodPr₂₃ X Y Z) (2 * e) z' hz'
  congr 1
  simp only [map_mul, pull_pull, prodPr₁₃_fst, prodPr₁₃_snd]
  rw [← prodPr₂₃_snd X Y Z, ← pull_pull (prodPr₂₃ X Y Z) (snd Y Z),
    ← pull_pull (fst (prod X Y) Z) (fst X Y)]
  simp only [mul_assoc]
  rw [← mul_assoc (W.pull (fst (prod X Y) Z) (W.pull (fst X Y) (a : W.H X))),
    ← mul_comm_of_mem_grade_two_mul hz'', mul_assoc]

/-! ### Graphs and the identity -/

/-- **The action of the class of a graph.** If `z ∈ H^*(X × Y)` satisfies
`∫_{X × Y} z ∪ v = ∫_{Y'} (g, ι)^*v` for all `v`, for morphisms `g : Y' ⟶ X` and `ι : Y' ⟶ Y`
with `Y'` nonempty and equidimensional of dimension `e` — the trace form of `z = (g, ι)_*1` —
then `∫_Y blockAct z a ∪ b = ∫_{Y'} g^*a ∪ ι^*b`. -/
theorem blockAct_graph (hA : W.PerfectPairing) {X Y Y' : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hY' : IsNonemptyEquidimensional Y' e) (g : Y' ⟶ X) (ι : Y' ⟶ Y) {z : W.H (prod X Y)}
    (hz : ∀ v : W.H (prod X Y),
      W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY) (z * v) =
        W.traceProj Y' e hY' (W.pull (prodLift g ι) v))
    {i : ℤ} (a : W.grade X i) (b : W.grade Y (2 * e - i)) :
    W.traceProj Y e hY ((W.blockAct hA hX hY z i a : W.H Y) * b) =
      W.traceProj Y' e hY' (W.pull g a * W.pull ι b) := by
  rw [blockAct_spec, mul_assoc, hz]
  simp only [map_mul, pull_pull, prodLift_fst, prodLift_snd]

/-- **The diagonal acts as the identity**: if `∫_{X × X} z ∪ v = ∫_X Δ^*v` for all `v` — the trace
form of `z = Δ_*1 = γ([Δ])` (Stacks 0FHG, 0FHH) — then `blockAct z = id`. -/
theorem blockAct_eq_self (hA : W.PerfectPairing) {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) {z : W.H (prod X X)}
    (hz : ∀ v : W.H (prod X X),
      W.traceProj (prod X X) (d + d) (isNonemptyEquidimensional_prod hX hX) (z * v) =
        W.traceProj X d hX (W.pull (diag X) v)) (i : ℤ) :
    W.blockAct hA hX hX z i = LinearMap.id := by
  refine blockAct_eq_of_forall hA hX hX _ _ _ fun a b ↦ ?_
  rw [LinearMap.id_apply, mul_assoc, hz, pull_diag_mul]

/-! ### Open and closed pieces -/

/-- **Restricting the action to pieces.** If `∫_{P × Q} w ∪ v = ∫_{U × V} z ∪ (i × j)^*v` for all
`v`, for morphisms `i : U ⟶ P`, `j : V ⟶ Q` between nonempty equidimensional schemes of the same
dimensions, then `∫_Q blockAct w a ∪ b = ∫_V blockAct z (i^*a) ∪ j^*b`. -/
theorem blockAct_prodMap (hA : W.PerfectPairing)
    {P Q U V : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hP : IsNonemptyEquidimensional P d) (hQ : IsNonemptyEquidimensional Q e)
    (hU : IsNonemptyEquidimensional U d) (hV : IsNonemptyEquidimensional V e) (ι : U ⟶ P)
    (j : V ⟶ Q) {w : W.H (prod P Q)} {z : W.H (prod U V)} (hz : z ∈ W.grade (prod U V) (2 * d))
    (hw : ∀ v : W.H (prod P Q),
      W.traceProj (prod P Q) (d + e) (isNonemptyEquidimensional_prod hP hQ) (w * v) =
        W.traceProj (prod U V) (d + e) (isNonemptyEquidimensional_prod hU hV)
          (z * W.pull (prodLift (fst U V ≫ ι) (snd U V ≫ j)) v))
    {n : ℤ} (a : W.grade P n) (b : W.grade Q (2 * e - n)) :
    W.traceProj Q e hQ ((W.blockAct hA hP hQ w n a : W.H Q) * b) =
      W.traceProj V e hV ((W.blockAct hA hU hV z n (W.pullDeg ι n a) : W.H V) * W.pull j b) := by
  rw [blockAct_spec, mul_assoc, hw, blockAct_spec' hA hU hV hz, coe_pullDeg, mul_assoc]
  simp only [map_mul, pull_pull, prodLift_fst, prodLift_snd]

/-! ### Tensor products -/

/-- The exterior products multiply with the Koszul sign:
`(pr₁^*a ∪ pr₂^*b) ∪ (pr₁^*u ∪ pr₂^*v) = (-1)^{sp} pr₁^*(a ∪ u) ∪ pr₂^*(b ∪ v)` for `b ∈ H^s(Y)`
and `u ∈ H^p(X)`. -/
theorem pull_fst_mul_pull_snd_mul (X Y : (SmoothProjectiveScheme k).FullSubcategory) {s p : ℤ}
    (a : W.H X) {b : W.H Y} {u : W.H X} (hb : b ∈ W.grade Y s) (hu : u ∈ W.grade X p) (v : W.H Y) :
    W.pull (fst X Y) a * W.pull (snd X Y) b * (W.pull (fst X Y) u * W.pull (snd X Y) v) =
      ((s * p).negOnePow : ℤ) • (W.pull (fst X Y) (a * u) * W.pull (snd X Y) (b * v)) := by
  have hc := W.graded_comm _ s p _ _ (W.pull_grade (snd X Y) s b hb)
    (W.pull_grade (fst X Y) p u hu)
  rw [map_mul, map_mul, mul_assoc, ← mul_assoc (W.pull _ b), hc, smul_mul_assoc, mul_smul_comm]
  simp only [mul_assoc]

/-- **The trace on `(X × X') × (Y × Y')`**: `∫ pr₁₃^*A ∪ pr₂₄^*B = ∫_{X × Y} A · ∫_{X' × Y'} B`.
-/
theorem traceProj_tensorPr (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory}
    {d d' e e' : ℕ} (hX : IsNonemptyEquidimensional X d) (hX' : IsNonemptyEquidimensional X' d')
    (hY : IsNonemptyEquidimensional Y e) (hY' : IsNonemptyEquidimensional Y' e')
    (A : W.H (prod X Y)) (B : W.H (prod X' Y')) :
    W.traceProj (prod (prod X X') (prod Y Y')) (d + d' + (e + e'))
        (isNonemptyEquidimensional_prod (isNonemptyEquidimensional_prod hX hX')
          (isNonemptyEquidimensional_prod hY hY'))
        (W.pull (prodTensorPr₁₃ X X' Y Y') A * W.pull (prodTensorPr₂₄ X X' Y Y') B) =
      W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY) A *
        W.traceProj (prod X' Y') (d' + e') (isNonemptyEquidimensional_prod hX' hY') B := by
  have hP := isNonemptyEquidimensional_prod (isNonemptyEquidimensional_prod hX hY)
    (isNonemptyEquidimensional_prod hX' hY')
  have hdim : d + d' + (e + e') = d + e + (d' + e') := by ring
  have h₄ : IsNonemptyEquidimensional (prod (prod X X') (prod Y Y')) (d + e + (d' + e')) :=
    hdim ▸ isNonemptyEquidimensional_prod (isNonemptyEquidimensional_prod hX hX')
      (isNonemptyEquidimensional_prod hY hY')
  rw [W.traceProj_congr _ hdim _ h₄]
  rw [← traceProj_pull_fst_mul_pull_snd hB.kunnethTrace (isNonemptyEquidimensional_prod hX hY)
    (isNonemptyEquidimensional_prod hX' hY') hP]
  have hσ₁ : prodTensorPr₁₃ X X' Y Y' = prodTensorShuffle X X' Y Y' ≫ fst _ _ :=
    (prodLift_fst _ _).symm
  have hσ₂ : prodTensorPr₂₄ X X' Y Y' = prodTensorShuffle X X' Y Y' ≫ snd _ _ :=
    (prodLift_snd _ _).symm
  rw [hσ₁, hσ₂, ← pull_pull, ← pull_pull, ← map_mul]
  generalize W.pull (fst (prod X Y) (prod X' Y')) A * W.pull (snd (prod X Y) (prod X' Y')) B = x
  induction x using DirectSum.Decomposition.inductionOn (W.grade _) with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | @homogeneous m x =>
    obtain ⟨x, hxm⟩ := x
    change W.traceProj _ _ _ (W.pull _ x) = W.traceProj _ _ hP x
    by_cases hm : m = 2 * ((d + e + (d' + e') : ℕ) : ℤ)
    · subst hm
      have h := W.trace_pullTw_of_isIso hA hB hC (prodTensorShuffle X X' Y Y') h₄ hP
        ((W.twCoord _ _ _).symm ⟨x, hxm⟩)
      rwa [trace_eq_traceProj, trace_eq_traceProj, twCoord_pullTw, coe_pullDeg,
        LinearEquiv.apply_symm_apply] at h
    · rw [W.traceProj_of_mem_ne _ _ hP hxm hm, W.traceProj_of_mem_ne _ _ _
        (W.pull_grade _ m x hxm) hm]

/-- For `Z₂ ∈ H^{2n}`, `A₂ ∈ H^{i'}` and `Y₁ ∈ H^p`,
`Z₁ ∪ Z₂ ∪ (A₁ ∪ A₂) ∪ (Y₁ ∪ Y₂) = (-1)^{i'p} (Z₁ ∪ A₁ ∪ Y₁) ∪ (Z₂ ∪ A₂ ∪ Y₂)`. -/
theorem mul_rearrange_tensor {R : (SmoothProjectiveScheme k).FullSubcategory} {n i' p : ℤ}
    {Z₁ A₁ Y₁ Z₂ A₂ Y₂ : W.H R} (hZ₂ : Z₂ ∈ W.grade R (2 * n)) (hA₂ : A₂ ∈ W.grade R i')
    (hY₁ : Y₁ ∈ W.grade R p) :
    Z₁ * Z₂ * (A₁ * A₂) * (Y₁ * Y₂) =
      ((i' * p).negOnePow : ℤ) • (Z₁ * A₁ * Y₁ * (Z₂ * A₂ * Y₂)) := by
  calc Z₁ * Z₂ * (A₁ * A₂) * (Y₁ * Y₂) = Z₁ * (Z₂ * A₁) * (A₂ * Y₁) * Y₂ := by
        simp only [mul_assoc]
    _ = Z₁ * A₁ * (Z₂ * (((i' * p).negOnePow : ℤ) • (Y₁ * A₂))) * Y₂ := by
        rw [mul_comm_of_mem_grade_two_mul hZ₂ A₁, W.graded_comm R i' p A₂ Y₁ hA₂ hY₁]
        simp only [mul_assoc]
    _ = ((i' * p).negOnePow : ℤ) • (Z₁ * A₁ * (Z₂ * Y₁) * A₂ * Y₂) := by
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = ((i' * p).negOnePow : ℤ) • (Z₁ * A₁ * Y₁ * (Z₂ * A₂ * Y₂)) := by
        rw [mul_comm_of_mem_grade_two_mul hZ₂ Y₁]
        simp only [mul_assoc]

/-- **The action of a tensor product of classes** (`[Γ] ⊗ [Γ']` in the source): for
`z ∈ H^{2d}(X × Y)`, `z' ∈ H^{2d'}(X' × Y')`, the class `pr₁₃^*z ∪ pr₂₄^*z'` of
`(X × X') × (Y × Y')` acts on `pr₁^*a ∪ pr₂^*a'` as
`pr₁^*(blockAct z a) ∪ pr₂^*(blockAct z' a')`. -/
theorem blockAct_tensor (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory}
    {d d' e e' : ℕ} (hX : IsNonemptyEquidimensional X d) (hX' : IsNonemptyEquidimensional X' d')
    (hY : IsNonemptyEquidimensional Y e) (hY' : IsNonemptyEquidimensional Y' e')
    {z : W.H (prod X Y)} (hz : z ∈ W.grade (prod X Y) (2 * d)) {z' : W.H (prod X' Y')}
    (hz' : z' ∈ W.grade (prod X' Y') (2 * d')) {i i' : ℤ} (a : W.grade X i) (a' : W.grade X' i') :
    (W.blockAct hA.perfectPairing (isNonemptyEquidimensional_prod hX hX')
        (isNonemptyEquidimensional_prod hY hY')
        (W.pull (prodTensorPr₁₃ X X' Y Y') z * W.pull (prodTensorPr₂₄ X X' Y Y') z') (i + i')
        ⟨W.pull (fst X X') a * W.pull (snd X X') a',
          SetLike.GradedMul.mul_mem (W.pull_grade _ i _ a.2) (W.pull_grade _ i' _ a'.2)⟩ :
        W.H (prod Y Y')) =
      W.pull (fst Y Y') (W.blockAct hA.perfectPairing hX hY z i a) *
        W.pull (snd Y Y') (W.blockAct hA.perfectPairing hX' hY' z' i' a') := by
  have ht : W.pull (prodTensorPr₁₃ X X' Y Y') z * W.pull (prodTensorPr₂₄ X X' Y Y') z' ∈
      W.grade (prod (prod X X') (prod Y Y')) (2 * ((d + d' : ℕ) : ℤ)) := by
    have := SetLike.GradedMul.mul_mem (W.pull_grade (prodTensorPr₁₃ X X' Y Y') _ _ hz)
      (W.pull_grade (prodTensorPr₂₄ X X' Y Y') _ _ hz')
    rwa [show 2 * (d : ℤ) + 2 * d' = 2 * ((d + d' : ℕ) : ℤ) by push_cast; ring] at this
  have hu := (W.blockAct hA.perfectPairing hX hY z i a).2
  have hu' := (W.blockAct hA.perfectPairing hX' hY' z' i' a').2
  have hr : W.pull (fst Y Y') (W.blockAct hA.perfectPairing hX hY z i a : W.H Y) *
      W.pull (snd Y Y') (W.blockAct hA.perfectPairing hX' hY' z' i' a' : W.H Y') ∈
      W.grade (prod Y Y') (i + i') :=
    SetLike.GradedMul.mul_mem (W.pull_grade _ i _ hu) (W.pull_grade _ i' _ hu')
  suffices H : (⟨_, hr⟩ : W.grade (prod Y Y') (i + i')) =
      W.blockAct hA.perfectPairing (isNonemptyEquidimensional_prod hX hX')
        (isNonemptyEquidimensional_prod hY hY') _ (i + i') _ from (congrArg Subtype.val H).symm
  refine eq_of_traceProj_mul_eq hA.perfectPairing (isNonemptyEquidimensional_prod hY hY')
    fun b ↦ ?_
  rw [blockAct_spec' hA.perfectPairing _ _ ht]
  obtain ⟨t, ht'⟩ := (hB.kunnethIsomorphism Y Y').2 (b : W.H (prod Y Y'))
  rw [← ht']
  clear ht' b
  dsimp only
  induction t using TensorProduct.inductionOn with
  | add t t' h₁ h₂ => rw [map_add, mul_add, map_add, h₁, h₂, map_add, mul_add, map_add]
  | tmul y y' =>
    induction y using DirectSum.Decomposition.inductionOn (W.grade Y) with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      rw [TensorProduct.add_tmul, map_add, mul_add, map_add, h₁, h₂, map_add, mul_add, map_add]
    | @homogeneous p y =>
      obtain ⟨y, hyp⟩ := y
      change W.traceProj _ _ _ (_ * W.kunnethMap Y Y' (y ⊗ₜ y')) =
        W.traceProj _ _ _ (_ * _ * W.pull _ (W.kunnethMap Y Y' (y ⊗ₜ y')))
      rw [kunnethMap_tmul, pull_fst_mul_pull_snd_mul Y Y' _ hu' hyp, map_zsmul,
        traceProj_pull_fst_mul_pull_snd hB.kunnethTrace hY hY',
        blockAct_spec' hA.perfectPairing hX hY hz, blockAct_spec' hA.perfectPairing hX' hY' hz',
        ← traceProj_tensorPr hA hB hC hX hX' hY hY', ← map_zsmul]
      congr 1
      have h₁ := W.pull_grade (prodTensorPr₂₄ X X' Y Y') _ _ hz'
      have h₂ := W.pull_grade (fst (prod X X') (prod Y Y') ≫ snd X X') _ _ a'.2
      have h₃ := W.pull_grade (snd (prod X X') (prod Y Y') ≫ fst Y Y') _ _ hyp
      simp only [map_mul, pull_pull, prodTensorPr₁₃_fst, prodTensorPr₁₃_snd, prodTensorPr₂₄_fst,
        prodTensorPr₂₄_snd]
      exact (mul_rearrange_tensor h₁ h₂ h₃).symm

end WeilData

end Stacks.WeilCohomology

end
