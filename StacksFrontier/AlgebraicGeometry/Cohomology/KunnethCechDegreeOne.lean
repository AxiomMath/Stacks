module

public import StacksFrontier.AlgebraicGeometry.Scheme.AffineProductSections
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleFlat
public import StacksFrontier.Algebra.Module.TotKunnethDegreeOne
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The Künneth formula in degree one for Čech cochains of a product

Let `k` be a field, `X` and `Y` schemes over `k` with finite affine open covers `U` and `V`
whose finite intersections are affine, and let `T = X ×_k Y`, covered by the products
`W (a, b) = U a ×_k V b`. A Čech cochain of the structure sheaf of `T` for this cover is a
family of functions on the intersections of the `W`'s; we work with these raw cochains
(`Stacks.KunnethCech.RawCochain`), whose differential `rawD` is the usual alternating sum.

## Main definitions

* `Stacks.KunnethCech.RawCochain`: raw Čech cochains of the structure sheaf.
* `Stacks.KunnethCech.rawD`: the Čech differential on raw cochains.
* `Stacks.KunnethCech.Φ`: the external product of cochains of `X` and of `Y`, as a `k`-linear map
  out of their tensor product.

## Main results

* `Stacks.KunnethCech.exists_rawD_eq_of_cocycle`: the injectivity of
  `H¹(T, 𝒪) ⟶ H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` at the level of these cochains: if `X` and `Y` have only
  constant global functions and carry rational points `x₀ ∈ U a₀`, `y₀ ∈ V b₀`, then a
  one-cocycle of `T` whose restrictions to `X × y₀` (on the indices `(·, b₀)`) and to `x₀ × Y`
  (on the indices `(a₀, ·)`) are coboundaries is a coboundary.

## References

* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.KunnethCech

/-! ### Raw Čech cochains of the structure sheaf -/

section Raw

variable {Z : Scheme.{u}} {I : Type u} (W : I → Z.Opens)

/-- A raw degree-`p` Čech cochain of the structure sheaf: a function on every `(p+1)`-fold
intersection. -/
abbrev RawCochain (p : ℕ) : Type u := ∀ i : Fin (p + 1) → I, Γ(Z, CechCochains.inter W i)

/-- Restriction of functions along an inclusion of opens. -/
noncomputable def res {O O' : Z.Opens} (h : O ≤ O') : Γ(Z, O') →+* Γ(Z, O) :=
  (Z.presheaf.map (homOfLE h).op).hom

/-- Restricting along `O' ≤ O''` and then along `O ≤ O'` is restricting along `O ≤ O''`. -/
theorem res_res {O O' O'' : Z.Opens} (h₁ : O ≤ O') (h₂ : O' ≤ O'') (x : Γ(Z, O'')) :
    res h₁ (res h₂ x) = res (h₁.trans h₂) x := by
  simp only [res, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp, ← op_comp]
  rfl

/-- Restriction along `O ≤ O` is the identity. -/
theorem res_refl {O : Z.Opens} (h : O ≤ O) (x : Γ(Z, O)) : res h x = x := by
  simp only [res]
  rw [show homOfLE h = 𝟙 O from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restrictions of the values of a cochain at two equal tuples to a common open agree. -/
theorem res_congr {p : ℕ} (s : RawCochain W p) {i i' : Fin (p + 1) → I} (hi : i = i')
    {O : Z.Opens} (h : O ≤ CechCochains.inter W i) (h' : O ≤ CechCochains.inter W i') :
    res h (s i) = res h' (s i') := by
  subst hi; rfl

/-- The Čech differential on raw cochains. -/
noncomputable def rawD (p : ℕ) (s : RawCochain W p) : RawCochain W (p + 1) := fun i =>
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    (res (CechCochains.inter_le_omit W i j) (s (i ∘ j.succAbove)))

/-- The Čech differential is additive. -/
theorem rawD_add (p : ℕ) (s t : RawCochain W p) : rawD W p (s + t) = rawD W p s + rawD W p t := by
  funext i
  simp only [rawD, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

/-- The alternating sum over `Fin 2` is the difference of the two terms. -/
private theorem sum_fin_two_neg_one_pow_smul {M : Type*} [AddCommGroup M] (g : Fin 2 → M) :
    ∑ l : Fin 2, ((-1 : ℤ) ^ (l : ℕ)) • g l = g 0 - g 1 := by
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, sub_eq_add_neg]

/-- The Čech differential of a degree-zero cochain at a pair `i` is the difference of the
restrictions of its values at the two faces of `i`. -/
theorem rawD_zero_apply (s : RawCochain W 0) (i : Fin 2 → I) :
    rawD W 0 s i = res (CechCochains.inter_le_omit W i 0) (s (i ∘ (0 : Fin 2).succAbove)) -
      res (CechCochains.inter_le_omit W i 1) (s (i ∘ (1 : Fin 2).succAbove)) := by
  exact sum_fin_two_neg_one_pow_smul _

/-- The alternating sum over `Fin 3` is the alternating combination of the three terms. -/
private theorem sum_fin_three_neg_one_pow_smul {M : Type*} [AddCommGroup M] (g : Fin 3 → M) :
    ∑ l : Fin 3, ((-1 : ℤ) ^ (l : ℕ)) • g l = g 0 - g 1 + g 2 := by
  simp only [Fin.sum_univ_three, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, Fin.val_two, sub_eq_add_neg, even_two, Even.neg_pow, one_pow]

/-- The Čech differential of a degree-one cochain at a triple `i` is the alternating sum of the
restrictions of its values at the three faces of `i`. -/
theorem rawD_one_apply (s : RawCochain W 1) (i : Fin 3 → I) :
    rawD W 1 s i = res (CechCochains.inter_le_omit W i 0) (s (i ∘ (0 : Fin 3).succAbove)) -
      res (CechCochains.inter_le_omit W i 1) (s (i ∘ (1 : Fin 3).succAbove)) +
      res (CechCochains.inter_le_omit W i 2) (s (i ∘ (2 : Fin 3).succAbove)) := by
  exact sum_fin_three_neg_one_pow_smul _

section Linear

variable {k : Type u} [Field k] (h : Z ⟶ Spec (.of k))

/-- The `k`-module structure on functions over every open, through the structure morphism. -/
@[instance_reducible]
noncomputable def sectionsAlgebra (O : Z.Opens) : Algebra k Γ(Z, O) :=
  Stacks.AffineProduct.sectionsAlgebra h O

/-- The `k`-module structure on raw cochains. -/
@[instance_reducible]
noncomputable def cochainModule (p : ℕ) : Module k (RawCochain W p) :=
  letI := fun O => sectionsAlgebra h O
  inferInstanceAs (Module k (∀ i : Fin (p + 1) → I, Γ(Z, CechCochains.inter W i)))

/-- Restriction sends the function given by a scalar `c : k` to the function given by `c`. -/
theorem res_algebraMap {O O' : Z.Opens} (hO : O ≤ O') (c : k) :
    letI := fun O => sectionsAlgebra h O
    res hO (algebraMap k Γ(Z, O') c) = algebraMap k Γ(Z, O) c :=
  Stacks.Cech.map_baseRingHom_apply h (homOfLE hO).op c

/-- Restriction commutes with multiplication by a scalar `c : k`. -/
theorem res_smul {O O' : Z.Opens} (hO : O ≤ O') (c : k) (x : Γ(Z, O')) :
    letI := fun O => sectionsAlgebra h O
    res hO (c • x) = c • res hO x := by
  let := fun O => sectionsAlgebra h O
  rw [Algebra.smul_def, map_mul, res_algebraMap, ← Algebra.smul_def]

/-- The Čech differential as a `k`-linear map. -/
noncomputable def rawDₗ (p : ℕ) :
    letI := cochainModule W h p
    letI := cochainModule W h (p + 1)
    RawCochain W p →ₗ[k] RawCochain W (p + 1) :=
  letI := cochainModule W h p
  letI := cochainModule W h (p + 1)
  { toFun := rawD W p
    map_add' := rawD_add W p
    map_smul' := fun c s => by
      let := fun O => sectionsAlgebra h O
      funext i
      simp only [rawD, RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [res_smul, smul_comm] }

/-- The `k`-linear Čech differential `rawDₗ` agrees with `rawD`. -/
theorem rawDₗ_apply (p : ℕ) (s : RawCochain W p) :
    letI := cochainModule W h p
    letI := cochainModule W h (p + 1)
    rawDₗ W h p s = rawD W p s := rfl

end Linear

end Raw

/-! ### Degree zero: global functions -/

section DegreeZero

variable {k : Type u} [Field k] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k)) {I : Type u}
  (W : I → Z.Opens)

/-- The constant cochain `1`. -/
def one : RawCochain W 0 := fun _ => 1

/-- **A degree-zero cocycle of a covering is a constant**, when the global functions are the
constants. -/
theorem exists_eq_smul_one_of_rawD_eq_zero (hcov : (⊤ : Z.Opens) = ⨆ i, W i)
    (hconst : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop))
    (s : RawCochain W 0) (hs : rawD W 0 s = 0) :
    letI := cochainModule W h 0
    ∃ c : k, s = c • one W := by
  let := fun O => sectionsAlgebra h O
  let := cochainModule W h 0
  let t : ∀ i, Γ(Z, W i) := fun i =>
    res (le_of_eq (by simp [CechCochains.inter])) (s (fun _ => i))
  have hcompat : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (t i) =
      res (inf_le_right : W i ⊓ W j ≤ W j) (t j) := by
    intro i j
    have h0 := congrFun hs (![i, j])
    rw [rawD_zero_apply] at h0
    have hij : W i ⊓ W j = CechCochains.inter W ![i, j] := by
      ext x
      simp [CechCochains.inter, TopologicalSpace.Opens.coe_iInf, Fin.forall_fin_two]
    have h0' := congrArg (res (O := W i ⊓ W j) (le_of_eq hij)) (sub_eq_zero.mp h0)
    simp only [t, res_res] at h0' ⊢
    refine ((res_congr W s ?_ _ _).trans (h0'.symm.trans (res_congr W s ?_ _ _)))
    · funext m; fin_cases m; rfl
    · funext m; fin_cases m; rfl
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' (Z.sheaf) W ⊤
    (fun i => homOfLE le_top) (le_of_eq hcov) t hcompat
  obtain ⟨c, hc⟩ := hconst g
  refine ⟨c, ?_⟩
  funext i
  have hi : CechCochains.inter W i = W (i 0) := by
    simp [CechCochains.inter]
  change s i = c • (1 : Γ(Z, CechCochains.inter W i))
  rw [Algebra.smul_def, mul_one]
  have key : res (le_top : CechCochains.inter W i ≤ ⊤) g = s i := by
    rw [← res_res (le_of_eq hi) (le_top : W (i 0) ≤ ⊤) g]
    change res _ ((Z.sheaf.1.map (homOfLE le_top).op) g) = _
    rw [hg (i 0)]
    simp only [t, res_res]
    exact res_congr W s (by funext m; fin_cases m; rfl) _ (le_refl _) |>.trans (res_refl _ _)
  rw [← key, ← hc]
  change res _ (h.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) = _
  rfl

end DegreeZero

/-! ### Generalities on restriction and pullback of functions -/

section Generalities

variable {Z Z' : Scheme.{u}}

/-- Pulling back along `r` a restriction from `O'` to `O` is pulling back from `O'`. -/
theorem appLE_res (r : Z' ⟶ Z) {O O' : Z.Opens} (h : O ≤ O') {O'' : Z'.Opens}
    (e : O'' ≤ r ⁻¹ᵁ O) (x : Γ(Z, O')) :
    r.appLE O O'' e (res h x) = r.appLE O' O'' (e.trans (Scheme.Hom.preimage_mono r h)) x := by
  simp only [res, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]

/-- Restricting to `O''` a pullback along `r` to `O'` is the pullback along `r` to `O''`. -/
theorem res_appLE (r : Z' ⟶ Z) {O : Z.Opens} {O' O'' : Z'.Opens} (h : O'' ≤ O')
    (e : O' ≤ r ⁻¹ᵁ O) (x : Γ(Z, O)) :
    res h (r.appLE O O' e x) = r.appLE O O'' (h.trans e) x := by
  simp only [res, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

/-- Restriction between two opens, each contained in the other, is injective. -/
theorem res_injective_of_le {O O' : Z.Opens} (h : O ≤ O') (h' : O' ≤ O) :
    Function.Injective (res h) := by
  intro x y hxy
  have := congrArg (res h') hxy
  rwa [res_res, res_res, res_refl, res_refl] at this

/-- Pulling back along `r` and then along `r'` is pulling back along `r' ≫ r`. -/
theorem appLE_comp {Z'' : Scheme.{u}} (r : Z' ⟶ Z) (r' : Z'' ⟶ Z') {O : Z.Opens} {O' : Z'.Opens}
    {O'' : Z''.Opens} (e : O' ≤ r ⁻¹ᵁ O) (e' : O'' ≤ r' ⁻¹ᵁ O') (x : Γ(Z, O)) :
    r'.appLE O' O'' e' (r.appLE O O' e x) =
      (r' ≫ r).appLE O O'' (e'.trans (Scheme.Hom.preimage_mono r' e)) x := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

variable {k : Type u} [Field k]

/-- Pullback along a morphism of `k`-schemes sends the function given by a scalar `c : k` to the
function given by `c`. -/
theorem appLE_algebraMap (hZ : Z ⟶ Spec (.of k)) (hZ' : Z' ⟶ Spec (.of k)) (r : Z' ⟶ Z)
    (hr : r ≫ hZ = hZ') {O : Z.Opens} {O' : Z'.Opens} (e : O' ≤ r ⁻¹ᵁ O) (c : k) :
    r.appLE O O' e ((Stacks.Cech.baseRingHom hZ O).hom c) =
      (Stacks.Cech.baseRingHom hZ' O').hom c := by
  rw [← hr, ← Stacks.AffineProduct.baseRingHom_comp_appLE hZ r O O' e]
  rfl

end Generalities

/-! ### The product cover and its bicochains -/

section Product

variable {k : Type u} [Field k] {X Y T : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {g : Y ⟶ Spec (.of k)} (p : T ⟶ X) (q : T ⟶ Y)
  {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (U : ι → X.Opens) (V : κ → Y.Opens)

/-- The product cover `W (a, b) = U a ×_k V b`. -/
noncomputable def prodCover : ι × κ → T.Opens := fun ab =>
  Stacks.AffineProduct.prodOpen p q (U ab.1) (V ab.2)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The intersection of the product cover along a tuple `t` is the product of the intersections
of `U` and of `V` along the two coordinate tuples of `t`. -/
theorem inter_prodCover {n : ℕ} (t : Fin (n + 1) → ι × κ) :
    CechCochains.inter (prodCover p q U V) t =
      Stacks.AffineProduct.prodOpen p q (CechCochains.inter U (fun m => (t m).1))
        (CechCochains.inter V (fun m => (t m).2)) := by
  ext x
  simp only [CechCochains.inter, prodCover, Stacks.AffineProduct.prodOpen, Opens.coe_iInf,
    Opens.coe_inf, Scheme.Hom.coe_preimage, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
    forall_and]

/-- Bicochains: functions on `U_i ×_k V_j` for every pair of tuples. -/
abbrev BiCochain (m n : ℕ) : Type u :=
  ∀ (i : Fin (m + 1) → ι) (j : Fin (n + 1) → κ),
    Γ(T, Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i) (CechCochains.inter V j))

/-- The horizontal differential of bicochains. -/
noncomputable def dHor (m n : ℕ) (F : BiCochain p q U V m n) : BiCochain p q U V (m + 1) n :=
  fun i j => ∑ l : Fin (m + 2), ((-1 : ℤ) ^ (l : ℕ)) •
    (res (Stacks.AffineProduct.prodOpen_mono p q (CechCochains.inter_le_omit U i l) le_rfl)
      (F (i ∘ l.succAbove) j))

/-- The vertical differential of bicochains. -/
noncomputable def dVert (m n : ℕ) (F : BiCochain p q U V m n) : BiCochain p q U V m (n + 1) :=
  fun i j => ∑ l : Fin (n + 2), ((-1 : ℤ) ^ (l : ℕ)) •
    (res (Stacks.AffineProduct.prodOpen_mono p q le_rfl (CechCochains.inter_le_omit V j l))
      (F i (j ∘ l.succAbove)))

/-- The `k`-module structure on bicochains. -/
@[instance_reducible]
noncomputable def biModule (m n : ℕ) : Module k (BiCochain p q U V m n) :=
  letI := fun O => sectionsAlgebra (p ≫ f) O
  inferInstanceAs (Module k (∀ (_ : Fin (m + 1) → ι) (_ : Fin (n + 1) → κ), Γ(T, _)))

variable {p q}
variable (H : IsPullback p q f g)

/-- The external product of a cochain of `X` and a cochain of `Y`. -/
noncomputable def extProd {m n : ℕ} (a : RawCochain U m) (b : RawCochain V n) :
    BiCochain p q U V m n := fun i j =>
  p.appLE _ _ (Stacks.AffineProduct.prodOpen_le_fst p q _ _) (a i) *
    q.appLE _ _ (Stacks.AffineProduct.prodOpen_le_snd p q _ _) (b j)

/-- The external product, as a `k`-linear map out of the tensor product. -/
noncomputable def Φ (m n : ℕ) :
    letI := cochainModule U f m
    letI := cochainModule V g n
    letI := biModule (f := f) p q U V m n
    RawCochain U m ⊗[k] RawCochain V n →ₗ[k] BiCochain p q U V m n :=
  letI := fun O => sectionsAlgebra f O
  letI := fun O => sectionsAlgebra g O
  letI := fun O => sectionsAlgebra (p ≫ f) O
  letI := cochainModule U f m
  letI := cochainModule V g n
  letI := biModule (f := f) p q U V m n
  TensorProduct.lift (LinearMap.mk₂ k (extProd U V)
    (fun a a' b => by funext i j; simp [extProd, add_mul])
    (fun c a b => by
      funext i j
      simp only [extProd, Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc]
      congr 1
      exact appLE_algebraMap f (p ≫ f) p rfl _ c)
    (fun a b b' => by funext i j; simp [extProd, mul_add])
    (fun c a b => by
      funext i j
      simp only [extProd, Pi.smul_apply, Algebra.smul_def, map_mul]
      rw [mul_left_comm]
      congr 1
      exact appLE_algebraMap g (p ≫ f) q H.w.symm _ c))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The map `Φ` sends `a ⊗ₜ b` to the external product of `a` and `b`. -/
theorem Φ_tmul {m n : ℕ} (a : RawCochain U m) (b : RawCochain V n) :
    letI := cochainModule U f m
    letI := cochainModule V g n
    Φ U V H m n (a ⊗ₜ b) = extProd U V a b := by
  simp [Φ]

end Product

section ProductMain

variable {k : Type u} [Field k] {X Y T : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {g : Y ⟶ Spec (.of k)} {p : T ⟶ X} {q : T ⟶ Y}
  {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (U : ι → X.Opens) (V : κ → Y.Opens) (H : IsPullback p q f g)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The external product is an isomorphism, when all intersections are affine. -/
theorem Φ_bijective [Finite ι] [Finite κ]
    (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
    (hV : ∀ (n : ℕ) (j : Fin (n + 1) → κ), IsAffineOpen (CechCochains.inter V j)) (m n : ℕ) :
    Function.Bijective (Φ U V H m n) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  let := fun O => sectionsAlgebra f O
  let := fun O => sectionsAlgebra g O
  let := fun O => sectionsAlgebra (p ≫ f) O
  let := cochainModule U f m
  let := cochainModule V g n
  let := biModule (f := f) p q U V m n
  let e : RawCochain U m ⊗[k] RawCochain V n ≃ₗ[k] BiCochain p q U V m n :=
    TensorProduct.piLeft (R := k) (N := RawCochain V n)
        (M := fun i => Γ(X, CechCochains.inter U i)) ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => TensorProduct.piRight k k (Γ(X, CechCochains.inter U i))
        (fun j => Γ(Y, CechCochains.inter V j)) ≪≫ₗ
        LinearEquiv.piCongrRight (fun j =>
          Stacks.AffineProduct.prodSectionsEquiv H (hU m i) (hV n j)))
  have he : (Φ U V H m n) = e.toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    rw [Φ_tmul]
    funext i j
    simp only [e, LinearEquiv.coe_coe, LinearEquiv.trans_apply, TensorProduct.piLeft,
      LinearEquiv.piCongrRight_apply, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul, TensorProduct.comm_tmul]
    rw [Stacks.AffineProduct.prodSectionsEquiv_tmul]
    rfl
  rw [he]
  exact e.bijective

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The external product intertwines the Čech differential of `X` on the first tensor factor
with the horizontal differential `dHor`. -/
theorem Φ_rTensor_rawD (m n : ℕ) :
    letI := cochainModule U f m
    letI := cochainModule U f (m + 1)
    letI := cochainModule V g n
    ∀ x : RawCochain U m ⊗[k] RawCochain V n,
    Φ U V H (m + 1) n ((rawDₗ U f m).rTensor _ x) = dHor p q U V m n (Φ U V H m n x) := by
  let := fun O => sectionsAlgebra f O
  let := fun O => sectionsAlgebra g O
  let := fun O => sectionsAlgebra (p ≫ f) O
  let := cochainModule U f m
  let := cochainModule U f (m + 1)
  let := cochainModule V g n
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, Φ_tmul, Φ_tmul, rawDₗ_apply]
    funext i j
    simp only [extProd, dHor, rawD, map_sum, map_zsmul, Finset.sum_mul, smul_mul_assoc, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [appLE_res, res_appLE, res_appLE]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    funext i j
    simp only [dHor, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The external product intertwines the Čech differential of `Y` on the second tensor factor
with the vertical differential `dVert`. -/
theorem Φ_lTensor_rawD (m n : ℕ) :
    letI := cochainModule U f m
    letI := cochainModule V g n
    letI := cochainModule V g (n + 1)
    ∀ x : RawCochain U m ⊗[k] RawCochain V n,
    Φ U V H m (n + 1) ((rawDₗ V g n).lTensor _ x) = dVert p q U V m n (Φ U V H m n x) := by
  let := fun O => sectionsAlgebra f O
  let := fun O => sectionsAlgebra g O
  let := fun O => sectionsAlgebra (p ≫ f) O
  let := cochainModule U f m
  let := cochainModule V g n
  let := cochainModule V g (n + 1)
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, Φ_tmul, Φ_tmul, rawDₗ_apply]
    funext i j
    simp only [extProd, dVert, rawD, map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [appLE_res, res_appLE, res_appLE]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    funext i j
    simp only [dVert, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

end ProductMain

section Main

variable {k : Type u} [Field k] {X Y T : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {g : Y ⟶ Spec (.of k)} {p : T ⟶ X} {q : T ⟶ Y}
  {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (U : ι → X.Opens) (V : κ → Y.Opens) (H : IsPullback p q f g)

/-- The Čech differential squares to zero. -/
theorem rawD_rawD {Z : Scheme.{u}} {I : Type u} (W : I → Z.Opens) (n : ℕ) (s : RawCochain W n) :
    rawD W (n + 1) (rawD W n s) = 0 :=
  CechCochains.cechD_cechD W
    (Z.presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) n s

/-- A point lies in the intersection along `i` if and only if it lies in every `W (i m)`. -/
theorem mem_inter {Z : Scheme.{u}} {I : Type u} (W : I → Z.Opens) {n : ℕ} (i : Fin n → I)
    (z : Z) : z ∈ CechCochains.inter W i ↔ ∀ m, z ∈ W (i m) := by
  rw [← SetLike.mem_coe, CechCochains.inter, Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- A point `z` of `T` lies in `prodOpen p q O O'` if and only if `p z ∈ O` and `q z ∈ O'`. -/
theorem mem_prodOpen (O : X.Opens) (O' : Y.Opens) (z : T) :
    z ∈ Stacks.AffineProduct.prodOpen p q O O' ↔ p z ∈ O ∧ q z ∈ O' := Iff.rfl

/-- Restrictions to a common open of heterogeneously equal functions on equal opens agree. -/
theorem res_congr' {Z : Scheme.{u}} {O O' O'' : Z.Opens} (hO : O' = O'') (h : O ≤ O')
    (h' : O ≤ O'') (x : Γ(Z, O')) (x' : Γ(Z, O''))
    (hx : HEq x x') : res h x = res h' x' := by
  subst hO; cases hx; rfl

/-- The face `X × y₀` of `T`. -/
noncomputable def faceX (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ g = 𝟙 _) : X ⟶ T :=
  H.lift (𝟙 X) (f ≫ y₀) (by rw [Category.id_comp, Category.assoc, hy₀, Category.comp_id])

/-- The face `x₀ × Y` of `T`. -/
noncomputable def faceY (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 _) : Y ⟶ T :=
  H.lift (g ≫ x₀) (𝟙 Y) (by rw [Category.id_comp, Category.assoc, hx₀, Category.comp_id])

/-- The face `faceX` is a section of the first projection. -/
@[reassoc (attr := simp)]
theorem faceX_fst (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ g = 𝟙 _) : faceX H y₀ hy₀ ≫ p = 𝟙 X :=
  IsPullback.lift_fst H _ _ _

/-- The face `faceX` followed by the second projection is the constant map `f ≫ y₀`. -/
@[reassoc (attr := simp)]
theorem faceX_snd (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ g = 𝟙 _) :
    faceX H y₀ hy₀ ≫ q = f ≫ y₀ :=
  IsPullback.lift_snd H _ _ _

/-- The face `faceY` followed by the first projection is the constant map `g ≫ x₀`. -/
@[reassoc (attr := simp)]
theorem faceY_fst (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 _) :
    faceY H x₀ hx₀ ≫ p = g ≫ x₀ :=
  IsPullback.lift_fst H _ _ _

/-- The face `faceY` is a section of the second projection. -/
@[reassoc (attr := simp)]
theorem faceY_snd (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 _) : faceY H x₀ hx₀ ≫ q = 𝟙 Y :=
  IsPullback.lift_snd H _ _ _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- When `y₀` lies in `V b₀`, the intersection of `U` along `i` is contained in the preimage under
`faceX` of the intersection of the product cover along the tuple `(i l, b₀)`. -/
theorem le_faceX (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ g = 𝟙 _) (b₀ : κ)
    (hb₀ : y₀ ⁻¹ᵁ V b₀ = ⊤) {n : ℕ} (i : Fin (n + 1) → ι) :
    CechCochains.inter U i ≤
      faceX H y₀ hy₀ ⁻¹ᵁ CechCochains.inter (prodCover p q U V) (fun l => (i l, b₀)) := by
  intro z hz
  rw [Scheme.Hom.mem_preimage, inter_prodCover, mem_prodOpen, mem_inter, mem_inter]
  have h1 : p (faceX H y₀ hy₀ z) = z := by
    rw [← Scheme.Hom.comp_apply, faceX, IsPullback.lift_fst]; rfl
  have h2 : q (faceX H y₀ hy₀ z) = y₀ (f z) := by
    rw [← Scheme.Hom.comp_apply, faceX, IsPullback.lift_snd, Scheme.Hom.comp_apply]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · rw [h1]; exact (mem_inter U i z).mp hz m
  · rw [h2]
    exact (hb₀ ▸ trivial : f z ∈ y₀ ⁻¹ᵁ V b₀)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- When `x₀` lies in `U a₀`, the intersection of `V` along `j` is contained in the preimage under
`faceY` of the intersection of the product cover along the tuple `(a₀, j l)`. -/
theorem le_faceY (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 _) (a₀ : ι)
    (ha₀ : x₀ ⁻¹ᵁ U a₀ = ⊤) {n : ℕ} (j : Fin (n + 1) → κ) :
    CechCochains.inter V j ≤
      faceY H x₀ hx₀ ⁻¹ᵁ CechCochains.inter (prodCover p q U V) (fun l => (a₀, j l)) := by
  intro z hz
  rw [Scheme.Hom.mem_preimage, inter_prodCover, mem_prodOpen, mem_inter, mem_inter]
  have h1 : q (faceY H x₀ hx₀ z) = z := by
    rw [← Scheme.Hom.comp_apply, faceY, IsPullback.lift_snd]; rfl
  have h2 : p (faceY H x₀ hx₀ z) = x₀ (g z) := by
    rw [← Scheme.Hom.comp_apply, faceY, IsPullback.lift_fst, Scheme.Hom.comp_apply]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · rw [h2]
    exact (ha₀ ▸ trivial : g z ∈ x₀ ⁻¹ᵁ U a₀)
  · rw [h1]; exact (mem_inter V j z).mp hz m

end Main

section Theorem

variable {k : Type u} [Field k] {X Y T : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {g : Y ⟶ Spec (.of k)} {p : T ⟶ X} {q : T ⟶ Y}
  {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (U : ι → X.Opens) (V : κ → Y.Opens) (H : IsPullback p q f g)

/-- If every entry of `i'` is an entry of `i`, the intersection along `i` is contained in the
intersection along `i'`. -/
theorem inter_le_of_range {Z : Scheme.{u}} {I : Type u} (W : I → Z.Opens) {n m : ℕ}
    (i : Fin n → I) (i' : Fin m → I) (h : ∀ l, ∃ l', i' l = i l') :
    CechCochains.inter W i ≤ CechCochains.inter W i' := by
  intro z hz
  rw [mem_inter] at hz ⊢
  intro l
  obtain ⟨l', hl'⟩ := h l
  exact hl' ▸ hz l'

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- If every entry of `t'` is an entry of `t`, the intersection of the product cover along `t` is
contained in its intersection along `t'`. -/
theorem prodCover_le {n m : ℕ} (t : Fin n → ι × κ) (t' : Fin m → ι × κ)
    (h : ∀ l, ∃ l', t' l = t l') :
    CechCochains.inter (prodCover p q U V) t ≤ CechCochains.inter (prodCover p q U V) t' :=
  inter_le_of_range _ t t' h

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- If the two coordinates of every entry of `t` are entries of `i` and of `j` respectively, the
product of the intersections along `i` and `j` is contained in the intersection of the product
cover along `t`. -/
theorem prodOpen_le_prodCover {n n' m : ℕ} (i : Fin n → ι) (j : Fin n' → κ) (t : Fin m → ι × κ)
    (hi : ∀ l, ∃ l', (t l).1 = i l') (hj : ∀ l, ∃ l', (t l).2 = j l') :
    Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i) (CechCochains.inter V j) ≤
      CechCochains.inter (prodCover p q U V) t := by
  intro z ⟨hzi, hzj⟩
  rw [mem_inter]
  intro l
  obtain ⟨l', hl'⟩ := hi l
  obtain ⟨l'', hl''⟩ := hj l
  refine ⟨?_, ?_⟩
  · change p z ∈ U (t l).1
    rw [hl']; exact (mem_inter U i (p z)).mp hzi l'
  · change q z ∈ V (t l).2
    rw [hl'']; exact (mem_inter V j (q z)).mp hzj l''

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- If every entry of `i` is a first coordinate and every entry of `j` a second coordinate of an
entry of `t`, the intersection of the product cover along `t` is contained in the product of the
intersections along `i` and `j`. -/
theorem prodCover_le_prodOpen {n m m' : ℕ} (t : Fin n → ι × κ) (i : Fin m → ι) (j : Fin m' → κ)
    (hi : ∀ l, ∃ l', i l = (t l').1) (hj : ∀ l, ∃ l', j l = (t l').2) :
    CechCochains.inter (prodCover p q U V) t ≤
      Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i) (CechCochains.inter V j) := by
  intro z hz
  rw [mem_inter] at hz
  refine ⟨(mem_inter U i (p z)).mpr fun l => ?_, (mem_inter V j (q z)).mpr fun l => ?_⟩
  · obtain ⟨l', hl'⟩ := hi l
    rw [hl']; exact (hz l').1
  · obtain ⟨l', hl'⟩ := hj l
    rw [hl']; exact (hz l').2

/-- The restriction of the value of a cochain at `i` equals the restriction of its value at an
equal tuple `i'`. -/
theorem res_tuple {Z : Scheme.{u}} {I : Type u} (W : I → Z.Opens) {n : ℕ} (s : RawCochain W n)
    {i i' : Fin (n + 1) → I} (hi : i = i') {O : Z.Opens} (h : O ≤ CechCochains.inter W i) :
    res h (s i) = res (h.trans (le_of_eq (congrArg (CechCochains.inter W) hi))) (s i') := by
  subst hi; rfl

/-- A degree-one cocycle restricts to a vanishing alternating sum over the faces of a triple. -/
private theorem res_rawD_one_eq_zero {Z : Scheme.{u}} {I : Type u} {W : I → Z.Opens}
    {c : RawCochain W 1} (hc : rawD W 1 c = 0) (τ : Fin 3 → I) {O : Z.Opens}
    (h : O ≤ CechCochains.inter W τ) :
    res (h.trans (CechCochains.inter_le_omit W τ 0)) (c (τ ∘ (0 : Fin 3).succAbove)) -
      res (h.trans (CechCochains.inter_le_omit W τ 1)) (c (τ ∘ (1 : Fin 3).succAbove)) +
      res (h.trans (CechCochains.inter_le_omit W τ 2)) (c (τ ∘ (2 : Fin 3).succAbove)) = 0 := by
  have := congrArg (res h) (congrFun hc τ)
  rwa [Pi.zero_apply, map_zero, rawD_one_apply, map_add, map_sub, res_res, res_res,
    res_res] at this

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The restriction of the value of a bicochain at `(i, j)` equals the restriction of its value at
an equal pair of tuples `(i', j')`. -/
theorem res_bituple {m n : ℕ} (F : BiCochain p q U V m n) {i i' : Fin (m + 1) → ι}
    {j j' : Fin (n + 1) → κ} (hi : i = i') (hj : j = j') {O : T.Opens}
    (h : O ≤ Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i) (CechCochains.inter V j)) :
    res h (F i j) = res (h.trans (le_of_eq (by rw [hi, hj]))) (F i' j') := by
  subst hi hj; rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The horizontal differential of a bicochain of horizontal degree zero at `(i, j)` is the
difference of the restrictions of its values at the two faces of `i`. -/
theorem dHor_zero_apply {n : ℕ} (F : BiCochain p q U V 0 n) (i : Fin 2 → ι)
    (j : Fin (n + 1) → κ) :
    dHor p q U V 0 n F i j =
      res (Stacks.AffineProduct.prodOpen_mono p q (CechCochains.inter_le_omit U i 0) le_rfl)
          (F (i ∘ (0 : Fin 2).succAbove) j) -
        res (Stacks.AffineProduct.prodOpen_mono p q (CechCochains.inter_le_omit U i 1) le_rfl)
          (F (i ∘ (1 : Fin 2).succAbove) j) := by
  exact sum_fin_two_neg_one_pow_smul _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The vertical differential of a bicochain of vertical degree zero at `(i, j)` is the
difference of the restrictions of its values at the two faces of `j`. -/
theorem dVert_zero_apply {m : ℕ} (F : BiCochain p q U V m 0) (i : Fin (m + 1) → ι)
    (j : Fin 2 → κ) :
    dVert p q U V m 0 F i j =
      res (Stacks.AffineProduct.prodOpen_mono p q le_rfl (CechCochains.inter_le_omit V j 0))
          (F i (j ∘ (0 : Fin 2).succAbove)) -
        res (Stacks.AffineProduct.prodOpen_mono p q le_rfl (CechCochains.inter_le_omit V j 1))
          (F i (j ∘ (1 : Fin 2).succAbove)) := by
  exact sum_fin_two_neg_one_pow_smul _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Restrictions to a common open of the values of a bicochain at two equal pairs of tuples
agree. -/
theorem res_congr₂ {m n : ℕ} (F : BiCochain p q U V m n) {i i' : Fin (m + 1) → ι}
    {j j' : Fin (n + 1) → κ} (hi : i = i') (hj : j = j') {O : T.Opens}
    (h : O ≤ Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i) (CechCochains.inter V j))
    (h' : O ≤ Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i')
      (CechCochains.inter V j')) :
    res h (F i j) = res h' (F i' j') := by
  subst hi hj; rfl

/-- Pullbacks of a function along equal morphisms agree. -/
theorem appLE_congr {Z Z' : Scheme.{u}} {r r' : Z' ⟶ Z} (hr : r = r') {O : Z.Opens}
    {O' : Z'.Opens} (e : O' ≤ r ⁻¹ᵁ O) (x : Γ(Z, O)) :
    r.appLE O O' e x = r'.appLE O O' (hr ▸ e) x := by
  subst hr; rfl

/-- Pullback along the identity is restriction. -/
theorem id_appLE {Z : Scheme.{u}} {O O' : Z.Opens} (e : O' ≤ (𝟙 Z) ⁻¹ᵁ O) (x : Γ(Z, O)) :
    Scheme.Hom.appLE (𝟙 Z) O O' e x = res e x := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, res]
  rfl

/-- Pullback along the identity from an open to itself is the identity. -/
theorem id_appLE_self {Z : Scheme.{u}} {O : Z.Opens} (e : O ≤ (𝟙 Z) ⁻¹ᵁ O) (x : Γ(Z, O)) :
    Scheme.Hom.appLE (𝟙 Z) O O e x = x := by
  rw [id_appLE]
  exact res_refl _ _

/-- The pullback along `h` of a global function `y` of `Spec k` is the function given by the
scalar corresponding to `y` under `Scheme.ΓSpecIso`. -/
theorem baseRingHom_eq_appLE_ΓSpecIso {Z : Scheme.{u}} (h : Z ⟶ Spec (.of k)) (O : Z.Opens)
    (y : Γ(Spec (.of k), ⊤)) :
    h.appLE ⊤ O (Stacks.AffineProduct.le_preimage_top h O) y =
      (Stacks.Cech.baseRingHom h O).hom ((Scheme.ΓSpecIso (.of k)).hom y) := by
  rw [Stacks.Cech.baseRingHom_eq_appLE h O (Stacks.AffineProduct.le_preimage_top h O)]
  change _ = (h.appLE ⊤ O _).hom ((Scheme.ΓSpecIso (.of k)).inv.hom
    ((Scheme.ΓSpecIso (.of k)).hom.hom y))
  congr 1
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of k)) y).symm

/-- For `Spec k` over itself, the global function given by a scalar `c` corresponds to `c` under
`Scheme.ΓSpecIso`. -/
theorem baseRingHom_id_top (c : k) :
    (Scheme.ΓSpecIso (.of k)).hom ((Stacks.Cech.baseRingHom (𝟙 (Spec (.of k))) ⊤).hom c) = c := by
  have : Stacks.Cech.baseRingHom (𝟙 (Spec (.of k))) ⊤ = (Scheme.ΓSpecIso (.of k)).inv := by
    simp only [Stacks.Cech.baseRingHom, Stacks.Cech.globalRingHom, Scheme.Hom.id_appTop]
    rw [show homOfLE (le_top : (⊤ : (Spec (.of k)).Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  rw [this, Iso.inv_hom_id_apply]

/-- Evaluation of a degree-zero cochain of `Y` at the rational point `y₀ ∈ V b₀`. -/
noncomputable def evalAt (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ g = 𝟙 _) (b₀ : κ)
    (hb₀ : y₀ ⁻¹ᵁ V b₀ = ⊤) :
    letI := cochainModule V g 0
    RawCochain V 0 →ₗ[k] k :=
  letI := fun O => sectionsAlgebra g O
  letI := cochainModule V g 0
  have hle : (⊤ : (Spec (.of k)).Opens) ≤ y₀ ⁻¹ᵁ CechCochains.inter V (fun _ => b₀) := by
    intro z _
    rw [Scheme.Hom.mem_preimage, mem_inter]
    intro _
    have : z ∈ y₀ ⁻¹ᵁ V b₀ := by rw [hb₀]; trivial
    exact this
  { toFun := fun b => (Scheme.ΓSpecIso (.of k)).hom (y₀.appLE _ ⊤ hle (b (fun _ => b₀)))
    map_add' := fun b b' => by simp
    map_smul' := fun c b => by
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingHom.id_apply]
      congr 1
      rw [show (algebraMap k Γ(Y, CechCochains.inter V fun _ => b₀)) c =
        (Stacks.Cech.baseRingHom g _).hom c from rfl,
        appLE_algebraMap g (𝟙 _) y₀ hy₀ hle c]
      exact baseRingHom_id_top c }

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- When `y₀` lies in `V b₀`, the intersection of `U` along `i` is contained in the preimage under
`faceX` of the product of this intersection with `V b₀`. -/
theorem le_faceX_prodOpen (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ g = 𝟙 _) (b₀ : κ)
    (hb₀ : y₀ ⁻¹ᵁ V b₀ = ⊤) {n : ℕ} (i : Fin (n + 1) → ι) :
    CechCochains.inter U i ≤ faceX H y₀ hy₀ ⁻¹ᵁ
      Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i)
        (CechCochains.inter V (fun _ : Fin 1 => b₀)) :=
  (le_faceX U V H y₀ hy₀ b₀ hb₀ i).trans (Scheme.Hom.preimage_mono _
    ((inter_prodCover p q U V _).le.trans (Stacks.AffineProduct.prodOpen_mono p q le_rfl
      (inter_le_of_range V _ _ fun _ => ⟨0, rfl⟩))))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- When `x₀` lies in `U a₀`, the intersection of `V` along `j` is contained in the preimage under
`faceY` of the product of `U a₀` with this intersection. -/
theorem le_faceY_prodOpen (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 _) (a₀ : ι)
    (ha₀ : x₀ ⁻¹ᵁ U a₀ = ⊤) {n : ℕ} (j : Fin (n + 1) → κ) :
    CechCochains.inter V j ≤ faceY H x₀ hx₀ ⁻¹ᵁ
      Stacks.AffineProduct.prodOpen p q (CechCochains.inter U (fun _ : Fin 1 => a₀))
        (CechCochains.inter V j) :=
  (le_faceY U V H x₀ hx₀ a₀ ha₀ j).trans (Scheme.Hom.preimage_mono _
    ((inter_prodCover p q U V _).le.trans (Stacks.AffineProduct.prodOpen_mono p q
      (inter_le_of_range U _ _ fun _ => ⟨0, rfl⟩) le_rfl)))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Restricting an external product to `X × y₀` evaluates the second factor at `y₀`. -/
theorem faceX_appLE_Φ (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ g = 𝟙 _) (b₀ : κ)
    (hb₀ : y₀ ⁻¹ᵁ V b₀ = ⊤) (m : ℕ) :
    letI := cochainModule U f m
    letI := cochainModule V g 0
    ∀ (x : RawCochain U m ⊗[k] RawCochain V 0) (i : Fin (m + 1) → ι),
      TensorProduct.rid k _ ((evalAt V y₀ hy₀ b₀ hb₀).lTensor _ x) i =
        (faceX H y₀ hy₀).appLE _ _ (le_faceX_prodOpen U V H y₀ hy₀ b₀ hb₀ i)
          (Φ U V H m 0 x i (fun _ => b₀)) := by
  let := fun O => sectionsAlgebra f O
  let := fun O => sectionsAlgebra g O
  let := fun O => sectionsAlgebra (p ≫ f) O
  let := cochainModule U f m
  let := cochainModule V g 0
  intro x i
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Φ_tmul]
    simp only [extProd, map_mul, appLE_comp]
    rw [appLE_congr (faceX_fst H y₀ hy₀), appLE_congr (faceX_snd H y₀ hy₀),
      id_appLE_self, ← appLE_comp (r' := f) (r := y₀) (O' := ⊤) _
        (Stacks.AffineProduct.le_preimage_top f _), baseRingHom_eq_appLE_ΓSpecIso, mul_comm]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Restricting an external product to `x₀ × Y` evaluates the first factor at `x₀`. -/
theorem faceY_appLE_Φ (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 _) (a₀ : ι)
    (ha₀ : x₀ ⁻¹ᵁ U a₀ = ⊤) (n : ℕ) :
    letI := cochainModule U f 0
    letI := cochainModule V g n
    ∀ (x : RawCochain U 0 ⊗[k] RawCochain V n) (j : Fin (n + 1) → κ),
      Stacks.TotKunneth.evalLeft (evalAt U x₀ hx₀ a₀ ha₀) _ x j =
        (faceY H x₀ hx₀).appLE _ _ (le_faceY_prodOpen U V H x₀ hx₀ a₀ ha₀ j)
          (Φ U V H 0 n x (fun _ => a₀) j) := by
  let := fun O => sectionsAlgebra f O
  let := fun O => sectionsAlgebra g O
  let := fun O => sectionsAlgebra (p ≫ f) O
  let := cochainModule U f 0
  let := cochainModule V g n
  intro x j
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Stacks.TotKunneth.evalLeft_tmul, Φ_tmul]
    simp only [extProd, map_mul, appLE_comp]
    rw [appLE_congr (faceY_snd H x₀ hx₀), appLE_congr (faceY_fst H x₀ hx₀),
      id_appLE_self, ← appLE_comp (r' := g) (r := x₀) (O' := ⊤) _
        (Stacks.AffineProduct.le_preimage_top g _), baseRingHom_eq_appLE_ΓSpecIso]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- The constant cochain `1` is a cocycle. -/
theorem rawD_one {Z : Scheme.{u}} {I : Type u} (W : I → Z.Opens) :
    rawD W 0 (one W) = 0 := by
  funext i
  rw [rawD_zero_apply]
  simp only [one, map_one, sub_self]
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- **Künneth in degree one for Čech cochains of a product.** Let the finite intersections of
`U` and `V` be affine, let `X` and `Y` have only constant global functions, and let
`x₀ ∈ U a₀`, `y₀ ∈ V b₀` be rational points. A Čech one-cocycle `c` of the product cover of `T`
whose restrictions to `X × y₀` (on the indices `(·, b₀)`) and to `x₀ × Y` (on the indices
`(a₀, ·)`) are coboundaries is a coboundary. -/
theorem exists_rawD_eq_of_cocycle [Finite ι] [Finite κ]
    (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
    (hV : ∀ (n : ℕ) (j : Fin (n + 1) → κ), IsAffineOpen (CechCochains.inter V j))
    (hUcov : (⊤ : X.Opens) = ⨆ a, U a) (hVcov : (⊤ : Y.Opens) = ⨆ b, V b)
    (hXc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
    (hYc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop))
    (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 _) (a₀ : ι) (ha₀ : x₀ ⁻¹ᵁ U a₀ = ⊤)
    (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ g = 𝟙 _) (b₀ : κ) (hb₀ : y₀ ⁻¹ᵁ V b₀ = ⊤)
    (c : RawCochain (prodCover p q U V) 1) (hc : rawD _ 1 c = 0)
    (hfX : ∃ w : RawCochain U 0, ∀ i : Fin 2 → ι,
      (faceX H y₀ hy₀).appLE _ _ (le_faceX U V H y₀ hy₀ b₀ hb₀ i) (c (fun l => (i l, b₀))) =
        rawD U 0 w i)
    (hfY : ∃ w : RawCochain V 0, ∀ j : Fin 2 → κ,
      (faceY H x₀ hx₀).appLE _ _ (le_faceY U V H x₀ hx₀ a₀ ha₀ j) (c (fun l => (a₀, j l))) =
        rawD V 0 w j) :
    ∃ F : RawCochain (prodCover p q U V) 0, rawD _ 0 F = c := by
  classical
  let := fun O => sectionsAlgebra f O
  let := fun O => sectionsAlgebra g O
  let := fun O => sectionsAlgebra (p ≫ f) O
  let := cochainModule U f 0
  let := cochainModule U f 1
  let := cochainModule U f 2
  let := cochainModule V g 0
  let := cochainModule V g 1
  let := cochainModule V g 2
  have hHle : ∀ {n m : ℕ} (i : Fin n → ι) (j : Fin (m + 1) → κ),
      Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i) (CechCochains.inter V j) ≤
        CechCochains.inter (prodCover p q U V) (fun l => (i l, j 0)) := fun i j =>
    (prodOpen_le_prodCover U V i (fun _ => j 0) _ (fun l => ⟨l, rfl⟩) (fun l => ⟨l, rfl⟩)).trans'
      (Stacks.AffineProduct.prodOpen_mono p q le_rfl (inter_le_of_range V _ _ fun _ => ⟨0, rfl⟩))
  have hVle : ∀ {n m : ℕ} (i : Fin (m + 1) → ι) (j : Fin n → κ),
      Stacks.AffineProduct.prodOpen p q (CechCochains.inter U i) (CechCochains.inter V j) ≤
        CechCochains.inter (prodCover p q U V) (fun l => (i 0, j l)) := fun i j =>
    (prodOpen_le_prodCover U V (fun _ => i 0) j _ (fun l => ⟨l, rfl⟩) (fun l => ⟨l, rfl⟩)).trans'
      (Stacks.AffineProduct.prodOpen_mono p q (inter_le_of_range U _ _ fun _ => ⟨0, rfl⟩) le_rfl)
  let Hc : BiCochain p q U V 1 0 := fun i j => res (hHle i j) (c (fun l => (i l, j 0)))
  let Vc : BiCochain p q U V 0 1 := fun i j => res (hVle i j) (c (fun l => (i 0, j l)))
  have hΦ := Φ_bijective U V H hU hV
  set e10 := LinearEquiv.ofBijective (Φ U V H 1 0) (hΦ 1 0)
  set e01 := LinearEquiv.ofBijective (Φ U V H 0 1) (hΦ 0 1)
  set h := e10.symm Hc with hh_def
  set v := e01.symm Vc with hv_def
  have hΦh : Φ U V H 1 0 h = Hc := e10.apply_symm_apply Hc
  have hΦv : Φ U V H 0 1 v = Vc := e01.apply_symm_apply Vc
  have hA : ∀ a : RawCochain U 0, rawDₗ U f 0 a = 0 → ∃ c : k, a = c • one U :=
    exists_eq_smul_one_of_rawD_eq_zero f U hUcov hXc
  have hB : ∀ b : RawCochain V 0, rawDₗ V g 0 b = 0 → ∃ c : k, b = c • one V :=
    exists_eq_smul_one_of_rawD_eq_zero g V hVcov hYc
  have hεA : evalAt U x₀ hx₀ a₀ ha₀ (one U) = 1 := by
    simp [evalAt, one]
  have hεB : evalAt V y₀ hy₀ b₀ hb₀ (one V) = 1 := by
    simp [evalAt, one]
  have hhor : dHor p q U V 1 0 Hc = 0 := by
    funext i j
    have key := res_rawD_one_eq_zero hc (fun l => (i l, j 0)) (hHle i j)
    refine ((sum_fin_three_neg_one_pow_smul _).trans ?_).trans key
    simp only [Hc, res_res]
    rfl
  have hmixed : dVert p q U V 1 0 Hc = dHor p q U V 0 1 Vc := by
    funext i j
    have k1 := res_rawD_one_eq_zero hc ![(i 0, j 0), (i 1, j 0), (i 1, j 1)]
      (prodOpen_le_prodCover U V i j _ (fun l => by fin_cases l <;> exact ⟨_, rfl⟩)
        (fun l => by fin_cases l <;> exact ⟨_, rfl⟩))
    have k2 := res_rawD_one_eq_zero hc ![(i 0, j 0), (i 0, j 1), (i 1, j 1)]
      (prodOpen_le_prodCover U V i j _ (fun l => by fin_cases l <;> exact ⟨_, rfl⟩)
        (fun l => by fin_cases l <;> exact ⟨_, rfl⟩))
    rw [res_tuple _ c (show ![(i 0, j 0), (i 1, j 0), (i 1, j 1)] ∘ (0 : Fin 3).succAbove =
        fun l => (i 1, j l) by funext l; fin_cases l <;> rfl),
      res_tuple _ c (show ![(i 0, j 0), (i 1, j 0), (i 1, j 1)] ∘ (1 : Fin 3).succAbove =
        fun l => (i l, j l) by funext l; fin_cases l <;> rfl),
      res_tuple _ c (show ![(i 0, j 0), (i 1, j 0), (i 1, j 1)] ∘ (2 : Fin 3).succAbove =
        fun l => (i l, j 0) by funext l; fin_cases l <;> rfl)] at k1
    rw [res_tuple _ c (show ![(i 0, j 0), (i 0, j 1), (i 1, j 1)] ∘ (0 : Fin 3).succAbove =
        fun l => (i l, j 1) by funext l; fin_cases l <;> rfl),
      res_tuple _ c (show ![(i 0, j 0), (i 0, j 1), (i 1, j 1)] ∘ (1 : Fin 3).succAbove =
        fun l => (i l, j l) by funext l; fin_cases l <;> rfl),
      res_tuple _ c (show ![(i 0, j 0), (i 0, j 1), (i 1, j 1)] ∘ (2 : Fin 3).succAbove =
        fun l => (i 0, j l) by funext l; fin_cases l <;> rfl)] at k2
    change ∑ l : Fin 2, _ = ∑ l : Fin 2, _
    simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
      neg_smul, Hc, Vc, res_res]
    rw [res_tuple _ c (show (fun l => (i l, (j ∘ (0 : Fin 2).succAbove) 0)) =
        fun l => (i l, j 1) from rfl),
      res_tuple _ c (show (fun l => (i l, (j ∘ (1 : Fin 2).succAbove) 0)) =
        fun l => (i l, j 0) from rfl),
      res_tuple _ c (show (fun l => ((i ∘ (0 : Fin 2).succAbove) 0, j l)) =
        fun l => (i 1, j l) from rfl),
      res_tuple _ c (show (fun l => ((i ∘ (1 : Fin 2).succAbove) 0, j l)) =
        fun l => (i 0, j l) from rfl)]
    linear_combination (exp := 1) k2 - k1
  have hh : (rawDₗ U f 1).rTensor (RawCochain V 0) h = 0 := by
    apply (hΦ 2 0).1
    rw [Φ_rTensor_rawD, hΦh, hhor, map_zero]
  have hmix : (rawDₗ V g 0).lTensor (RawCochain U 1) h =
      (rawDₗ U f 0).rTensor (RawCochain V 1) v := by
    apply (hΦ 1 1).1
    rw [Φ_lTensor_rawD, Φ_rTensor_rawD, hΦh, hΦv, hmixed]
  obtain ⟨wX, hwX⟩ := hfX
  obtain ⟨wY, hwY⟩ := hfY
  have hfaceB : (evalAt V y₀ hy₀ b₀ hb₀).lTensor (RawCochain U 1) h ∈
      LinearMap.range ((rawDₗ U f 0).rTensor k) := by
    refine ⟨wX ⊗ₜ 1, ?_⟩
    apply (TensorProduct.rid k (RawCochain U 1)).injective
    rw [LinearMap.rTensor_tmul, TensorProduct.rid_tmul, one_smul]
    funext i
    rw [faceX_appLE_Φ U V H y₀ hy₀ b₀ hb₀ 1 h i, hΦh, rawDₗ_apply, ← hwX i]
    simp only [Hc]
    rw [appLE_res]
  have hfaceA : Stacks.TotKunneth.evalLeft (evalAt U x₀ hx₀ a₀ ha₀) (RawCochain V 1) v ∈
      LinearMap.range (rawDₗ V g 0) := by
    refine ⟨wY, ?_⟩
    funext j
    rw [faceY_appLE_Φ U V H x₀ hx₀ a₀ ha₀ 1 v j, hΦv, rawDₗ_apply, ← hwY j]
    simp only [Vc]
    rw [appLE_res]
  obtain ⟨f₀, hf₀h, hf₀v⟩ := Stacks.TotKunneth.exists_eq_of_cocycle (rawDₗ U f 0) (rawDₗ U f 1)
    (LinearMap.ext fun s => rawD_rawD U 0 s) (rawDₗ V g 0) (one U) hA (rawD_one U)
    (evalAt U x₀ hx₀ a₀ ha₀) hεA (one V) hB (evalAt V y₀ hy₀ b₀ hb₀) hεB h v hh hmix hfaceB
    hfaceA
  set F₀ := Φ U V H 0 0 f₀
  have hHF : Hc = dHor p q U V 0 0 F₀ := by
    rw [← hΦh, ← hf₀h, Φ_rTensor_rawD]
  have hVF : Vc = dVert p q U V 0 0 F₀ := by
    rw [← hΦv, ← hf₀v, Φ_lTensor_rawD]
  refine ⟨fun t => res (prodCover_le_prodOpen U V t (fun _ => (t 0).1) (fun _ => (t 0).2)
    (fun _ => ⟨0, rfl⟩) (fun _ => ⟨0, rfl⟩)) (F₀ (fun _ => (t 0).1) (fun _ => (t 0).2)), ?_⟩
  funext t
  set τ : Fin 3 → ι × κ := ![((t 0).1, (t 0).2), ((t 1).1, (t 0).2), ((t 1).1, (t 1).2)]
  have hPτ : CechCochains.inter (prodCover p q U V) t ≤ CechCochains.inter (prodCover p q U V) τ :=
    (prodCover_le_prodOpen U V t (fun l => (t l).1) (fun l => (t l).2)
      (fun l => ⟨l, rfl⟩) (fun l => ⟨l, rfl⟩)).trans
      (prodOpen_le_prodCover U V _ _ τ (fun l => by fin_cases l <;> exact ⟨_, rfl⟩)
        (fun l => by fin_cases l <;> exact ⟨_, rfl⟩))
  have kτ := res_rawD_one_eq_zero hc τ hPτ
  rw [res_tuple _ c (show τ ∘ (0 : Fin 3).succAbove = fun l => ((t 1).1, (t l).2) by
      funext l; fin_cases l <;> rfl),
    res_tuple _ c (show τ ∘ (1 : Fin 3).succAbove = t by funext l; fin_cases l <;> rfl),
    res_tuple _ c (show τ ∘ (2 : Fin 3).succAbove = fun l => ((t l).1, (t 0).2) by
      funext l; fin_cases l <;> rfl), res_refl] at kτ
  have eV := congrArg (res (prodCover_le_prodOpen U V t (fun _ => (t 1).1) (fun l => (t l).2)
    (fun _ => ⟨1, rfl⟩) (fun l => ⟨l, rfl⟩)))
    (congrFun (congrFun hVF (fun _ => (t 1).1)) (fun l => (t l).2))
  rw [dVert_zero_apply, map_sub, res_res, res_res] at eV
  simp only [res_res] at eV
  rw [res_bituple U V F₀ rfl (show (fun l => (t l).2) ∘ (0 : Fin 2).succAbove =
      fun _ => (t 1).2 by funext l; fin_cases l; rfl),
    res_bituple U V F₀ rfl (show (fun l => (t l).2) ∘ (1 : Fin 2).succAbove =
      fun _ => (t 0).2 by funext l; fin_cases l; rfl)] at eV
  have eH := congrArg (res (prodCover_le_prodOpen U V t (fun l => (t l).1) (fun _ => (t 0).2)
    (fun l => ⟨l, rfl⟩) (fun _ => ⟨0, rfl⟩)))
    (congrFun (congrFun hHF (fun l => (t l).1)) (fun _ => (t 0).2))
  rw [dHor_zero_apply, map_sub, res_res, res_res] at eH
  simp only [res_res] at eH
  rw [res_bituple U V F₀ (show (fun l => (t l).1) ∘ (0 : Fin 2).succAbove =
      fun _ => (t 1).1 by funext l; fin_cases l; rfl) rfl,
    res_bituple U V F₀ (show (fun l => (t l).1) ∘ (1 : Fin 2).succAbove =
      fun _ => (t 0).1 by funext l; fin_cases l; rfl) rfl] at eH
  rw [rawD_zero_apply, res_res, res_res]
  change res _ (F₀ (fun _ => (t 1).1) (fun _ => (t 1).2)) -
    res _ (F₀ (fun _ => (t 0).1) (fun _ => (t 0).2)) = c t
  linear_combination (exp := 1) kτ - eV - eH

end Theorem

end Stacks.KunnethCech

end
