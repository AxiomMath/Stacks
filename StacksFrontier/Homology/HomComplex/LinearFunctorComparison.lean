module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantIdeal
public import StacksFrontier.Homology.HomComplex.Basic

/-!
# Hom complexes out of a bounded complex of finite projectives and linear functors

Let `R` be a commutative ring and `E` an additive `R`-linear endofunctor of the category of
`R`-modules. For complexes `K` and `L` of `R`-modules there is a canonical morphism of complexes

`E(Hom^•(K, L)) ⟶ Hom^•(K, E(L))`,

sending `x` to the cochain whose component `K^p → E(L^q)` is `m ↦ E(ev_m)(x)`, where
`ev_m : Hom^n(K, L) → L^q` evaluates the component `K^p → L^q` of a cochain at `m`. It is natural
in `L` and in `E`, and it is an isomorphism when `K` is bounded with finite projective terms:
a finite dual basis `(e_i, φ_i)` of each `K^p` writes the identity of `Hom^n(K, L)` as a finite
sum of maps factoring through the evaluations at the `e_i`, and the `R`-linearity of `E` carries
this decomposition across.

## Main definitions

* `Stacks.HomComplex.LinearFunctor.cochainEval`: evaluation of a component of a cochain at an
  element, as a morphism of `R`-modules.
* `Stacks.HomComplex.LinearFunctor.comparison`: the comparison morphism
  `E(Hom^•(K, L)) ⟶ Hom^•(K, E(L))`.

## Main results

* `Stacks.HomComplex.LinearFunctor.comparison_naturality`: naturality in `L`.
* `Stacks.HomComplex.LinearFunctor.comparison_natTrans`: naturality in the functor `E`.
* `Stacks.HomComplex.LinearFunctor.bijective_comparisonLinearMap`,
  `Stacks.HomComplex.LinearFunctor.isIso_comparison`: the comparison is an isomorphism when `K`
  is bounded with finite projective terms.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe v u

namespace Stacks.HomComplex.LinearFunctor

open Stacks.HomComplex.TensorHomMap (postcomp postcomp_f_apply)

variable {R : Type u} [CommRing R]

section Eval

/-- `F(g) (F(f) x) = F(f ≫ g) x` for a functor of module categories. -/
lemma map_hom_map_hom (F : ModuleCat.{v} R ⥤ ModuleCat.{v} R) {X Y Z : ModuleCat.{v} R}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj X) :
    (F.map g).hom ((F.map f).hom x) = (F.map (f ≫ g)).hom x := by
  rw [F.map_comp]
  rfl


variable (K L : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)

/-- Evaluation of the component `K^p → L^q` of a degree-`n` cochain at an element `m` of `K^p`,
as a morphism of `R`-modules `Hom^n(K, L) ⟶ L^q`. -/
def cochainEval {p q : ℤ} (hpq : p + n = q) (m : K.X p) :
    (HomComplexR R K L).X n ⟶ L.X q :=
  ModuleCat.ofHom
    { toFun z := (z.v p q hpq).hom m
      map_add' z z' := by simp
      map_smul' r z := by simp }

/-- `cochainEval K L n hpq m` sends a cochain `z` to `z.v p q hpq m`. -/
@[simp]
lemma cochainEval_apply {p q : ℤ} (hpq : p + n = q) (m : K.X p)
    (z : (HomComplexR R K L).X n) :
    (cochainEval K L n hpq m).hom z = (Cochain.v (z : Cochain K L n) p q hpq).hom m :=
  rfl

/-- Evaluation of cochains is additive in the element evaluated at. -/
lemma cochainEval_add {p q : ℤ} (hpq : p + n = q) (m m' : K.X p) :
    cochainEval K L n hpq (m + m') = cochainEval K L n hpq m + cochainEval K L n hpq m' := by
  refine ModuleCat.hom_ext (LinearMap.ext fun (z : Cochain K L n) => ?_)
  exact map_add (z.v p q hpq).hom m m'

/-- Evaluation of cochains is `R`-linear in the element evaluated at. -/
lemma cochainEval_smul {p q : ℤ} (hpq : p + n = q) (r : R) (m : K.X p) :
    cochainEval K L n hpq (r • m) = r • cochainEval K L n hpq m := by
  refine ModuleCat.hom_ext (LinearMap.ext fun (z : Cochain K L n) => ?_)
  exact map_smul (z.v p q hpq).hom r m

/-- The evaluation of the differential of a cochain, by the formula for the differential of the
Hom complex. -/
lemma δ_comp_cochainEval {m : ℤ} (hnm : n + 1 = m) {p q : ℤ} (hpq : p + m = q) (x : K.X p) :
    (HomComplexR R K L).d n m ≫ cochainEval K L m hpq x =
      cochainEval K L n (show p + n = q - 1 by omega) x ≫ L.d (q - 1) q +
        ((m.negOnePow : ℤˣ) : ℤ) •
          cochainEval K L n (show p + 1 + n = q by omega) ((K.d p (p + 1)).hom x) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun (z : Cochain K L n) => ?_)
  show ((δ n m z).v p q hpq).hom x = _
  rw [δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl]
  simp [Units.smul_def]
  all_goals rfl

/-- Evaluation after postcomposition with a morphism of complexes. -/
lemma postcomp_comp_cochainEval {L' : CochainComplex (ModuleCat.{v} R) ℤ} (h : L ⟶ L')
    {p q : ℤ} (hpq : p + n = q) (x : K.X p) :
    (postcomp R K L L' h).f n ≫ cochainEval K L' n hpq x = cochainEval K L n hpq x ≫ h.f q := by
  refine ModuleCat.hom_ext (LinearMap.ext fun (z : Cochain K L n) => ?_)
  show ((z.comp (Cochain.ofHom h) (add_zero n)).v p q hpq).hom x = _
  rw [Cochain.comp_zero_cochain_v]
  rfl

end Eval

section Comparison

variable (K L : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
  (E : ModuleCat.{v} R ⥤ ModuleCat.{v} R) [E.Additive] [E.Linear R]

/-- The cochain `E(Hom^n(K, L)) → Hom^n(K, E(L))` attached to `x`: its component `K^p → E(L^q)`
is `m ↦ E(ev_m)(x)`. -/
def comparisonCochain (x : E.obj ((HomComplexR R K L).X n)) :
    Cochain K ((E.mapHomologicalComplex _).obj L) n :=
  Cochain.mk fun p q hpq => ModuleCat.ofHom
    { toFun m := (E.map (cochainEval K L n hpq m)).hom x
      map_add' m m' := by rw [cochainEval_add, E.map_add]; rfl
      map_smul' r m := by rw [cochainEval_smul, E.map_smul]; rfl }

/-- The component `K^p → E(L^q)` of `comparisonCochain K L n E x` sends `m` to `E(ev_m)(x)`. -/
@[simp]
lemma comparisonCochain_v_apply (x : E.obj ((HomComplexR R K L).X n)) {p q : ℤ}
    (hpq : p + n = q) (m : K.X p) :
    ((comparisonCochain K L n E x).v p q hpq).hom m = (E.map (cochainEval K L n hpq m)).hom x := by
  simp [comparisonCochain]

/-- The comparison `E(Hom^n(K, L)) → Hom^n(K, E(L))` in degree `n`, as an `R`-linear map. -/
def comparisonLinearMap :
    E.obj ((HomComplexR R K L).X n) →ₗ[R] Cochain K ((E.mapHomologicalComplex _).obj L) n
    where
  toFun := comparisonCochain K L n E
  map_add' x y := by
    ext p q hpq m
    change (E.map (cochainEval K L n hpq m)).hom (x + y) =
      (E.map (cochainEval K L n hpq m)).hom x + (E.map (cochainEval K L n hpq m)).hom y
    exact map_add _ x y
  map_smul' r x := by
    ext p q hpq m
    change (E.map (cochainEval K L n hpq m)).hom (r • x) =
      r • (E.map (cochainEval K L n hpq m)).hom x
    exact map_smul _ r x

/-- `comparisonLinearMap K L n E` sends `x` to `comparisonCochain K L n E x`. -/
@[simp]
lemma comparisonLinearMap_apply (x : E.obj ((HomComplexR R K L).X n)) :
    comparisonLinearMap K L n E x = comparisonCochain K L n E x :=
  rfl

/-- **The comparison of Hom complexes with a linear functor**: the morphism of complexes
`E(Hom^•(K, L)) ⟶ Hom^•(K, E(L))` sending `x` to the cochain with components
`m ↦ E(ev_m)(x)`. -/
def comparison :
    (E.mapHomologicalComplex _).obj (HomComplexR R K L) ⟶
      HomComplexR R K ((E.mapHomologicalComplex _).obj L) where
  f n := ModuleCat.ofHom (comparisonLinearMap K L n E)
  comm' n m hnm := by
    have hnm' : n + 1 = m := hnm
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : E.obj ((HomComplexR R K L).X n)) =>
      Cochain.ext _ _ fun p q hpq => ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
    change ((δ n m (comparisonCochain K L n E x)).v p q hpq).hom y =
      (E.map (cochainEval K L m hpq y)).hom ((E.map ((HomComplexR R K L).d n m)).hom x)
    have key := congrArg (fun f => (E.map f).hom x) (δ_comp_cochainEval K L n hnm' hpq y)
    simp only [E.map_comp, E.map_add, E.map_zsmul, ModuleCat.hom_comp, ModuleCat.hom_add,
      ModuleCat.hom_zsmul, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply] at key
    rw [δ_v n m hnm' _ p q hpq (q - 1) (p + 1) rfl rfl, key]
    simp [Units.smul_def]
    all_goals rfl

/-- The degree-`n` component of `comparison K L E` sends `x` to `comparisonCochain K L n E x`. -/
@[simp]
lemma comparison_f_apply (x : E.obj ((HomComplexR R K L).X n)) :
    ((comparison K L E).f n).hom x = comparisonCochain K L n E x :=
  rfl

/-- **Naturality of the comparison in the target complex.** -/
@[reassoc]
lemma comparison_naturality {L L' : CochainComplex (ModuleCat.{v} R) ℤ} (h : L ⟶ L') :
    (E.mapHomologicalComplex _).map (postcomp R K L L' h) ≫ comparison K L' E =
      comparison K L E ≫ postcomp R K _ _ ((E.mapHomologicalComplex _).map h) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext
    fun (x : E.obj ((HomComplexR R K L).X n)) =>
      Cochain.ext _ _ fun p q hpq => ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
  show (E.map (cochainEval K L' n hpq y)).hom ((E.map ((postcomp R K L L' h).f n)).hom x) =
    (((comparisonCochain K L n E x).comp (Cochain.ofHom ((E.mapHomologicalComplex _).map h))
      (add_zero n)).v p q hpq).hom y
  rw [map_hom_map_hom, postcomp_comp_cochainEval, E.map_comp, Cochain.comp_zero_cochain_v]
  rfl

/-- **Naturality of the comparison in the linear functor.** -/
@[reassoc]
lemma comparison_natTrans {E' : ModuleCat.{v} R ⥤ ModuleCat.{v} R} [E'.Additive] [E'.Linear R]
    (α : E ⟶ E') :
    (NatTrans.mapHomologicalComplex α _).app (HomComplexR R K L) ≫ comparison K L E' =
      comparison K L E ≫ postcomp R K _ _ ((NatTrans.mapHomologicalComplex α _).app L) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext
    fun (x : E.obj ((HomComplexR R K L).X n)) =>
      Cochain.ext _ _ fun p q hpq => ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
  show (E'.map (cochainEval K L n hpq y)).hom ((α.app _).hom x) =
    (((comparisonCochain K L n E x).comp
      (Cochain.ofHom ((NatTrans.mapHomologicalComplex α _).app L)) (add_zero n)).v p q hpq).hom y
  rw [Cochain.comp_zero_cochain_v]
  exact (ConcreteCategory.congr_hom (α.naturality (cochainEval K L n hpq y)) x).symm

end Comparison

section Bijective

variable {K : CochainComplex (ModuleCat.{v} R) ℤ} (L : CochainComplex (ModuleCat.{v} R) ℤ)
  (n : ℤ)

/-- The degree-`n` cochain with the single component `K^p → L^{p+n}`, `m ↦ φ(m) w`, as a
function of `w`. -/
def singleSmulRight {p : ℤ} (φ : Module.Dual R (K.X p)) :
    L.X (p + n) ⟶ (HomComplexR R K L).X n :=
  ModuleCat.ofHom
    { toFun w := Cochain.single (ModuleCat.ofHom (φ.smulRight w)) n
      map_add' w w' := by
        ext p' q' hpq' m
        by_cases hp : p' = p
        · subst hp
          obtain rfl : q' = p' + n := hpq'.symm
          simp [Cochain.single_v]
        · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]
      map_smul' r w := by
        ext p' q' hpq' m
        by_cases hp : p' = p
        · subst hp
          obtain rfl : q' = p' + n := hpq'.symm
          simp [Cochain.single_v, smul_smul, mul_comm]
        · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp] }

/-- Evaluating `singleSmulRight L n φ w` at `m : K^p` gives `φ m • w`. -/
lemma cochainEval_singleSmulRight_self {p : ℤ} (φ : Module.Dual R (K.X p)) (m : K.X p)
    (w : L.X (p + n)) :
    (cochainEval K L n rfl m).hom ((singleSmulRight L n φ).hom w) = φ m • w := by
  show ((Cochain.single (ModuleCat.ofHom (φ.smulRight w)) n).v p (p + n) rfl).hom m = _
  rw [Cochain.single_v]
  rfl

/-- The component of `singleSmulRight L n φ w` out of `K^{p'}` vanishes for `p' ≠ p`. -/
lemma cochainEval_singleSmulRight_of_ne {p p' q' : ℤ} (φ : Module.Dual R (K.X p))
    (hp : p' ≠ p) (hpq' : p' + n = q') (m : K.X p') (w : L.X (p + n)) :
    (cochainEval K L n hpq' m).hom ((singleSmulRight L n φ).hom w) = 0 := by
  show ((Cochain.single (ModuleCat.ofHom (φ.smulRight w)) n).v p' q' hpq').hom m = _
  rw [Cochain.single_v_eq_zero _ _ _ _ _ hp]
  rfl

/-- `singleSmulRight L n φ` followed by evaluation at `m : K^p` is multiplication by `φ m`. -/
lemma singleSmulRight_comp_cochainEval_self {p : ℤ} (φ : Module.Dual R (K.X p)) (m : K.X p) :
    singleSmulRight L n φ ≫ cochainEval K L n rfl m = φ m • 𝟙 _ := by
  ext w
  exact cochainEval_singleSmulRight_self L n φ m w

/-- `singleSmulRight L n φ` followed by evaluation at an element of `K^{p'}`, for `p' ≠ p`, is
zero. -/
lemma singleSmulRight_comp_cochainEval_of_ne {p p' q' : ℤ} (φ : Module.Dual R (K.X p))
    (hp : p' ≠ p) (hpq' : p' + n = q') (m : K.X p') :
    singleSmulRight L n φ ≫ cochainEval K L n hpq' m = 0 := by
  ext w
  exact cochainEval_singleSmulRight_of_ne L n φ hp hpq' m w

/-- An element of a zero module is zero. -/
lemma eq_zero_of_isZero {X : ModuleCat.{v} R} (hX : Limits.IsZero X) (m : X) : m = 0 := by
  have := (ModuleCat.isZero_iff_subsingleton).1 hX
  exact Subsingleton.elim _ _

/-- A complex strictly concentrated in degrees `[a, b]` has zero term `K^p` for `p ∉ [a, b]`. -/
lemma isZero_X_of_notMem_Icc (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] {p : ℤ}
    (hp : p ∉ Finset.Icc a b) : Limits.IsZero (K.X p) := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hp
  rcases hp with hp | hp
  · exact K.isZero_of_isStrictlyGE a p hp
  · exact K.isZero_of_isStrictlyLE b p hp

/-- If `g p i` vanishes for `p ≠ p'` and `g p' i = φ p' i m • f (e p' i)` for a dual basis, then
the sum of the `g p i` over `p ∈ [a, b]` is `f m`, whether or not `p'` lies in `[a, b]`. -/
private lemma sum_Icc_sum_eq_of_dual_basis {K : CochainComplex (ModuleCat.{v} R) ℤ} (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] {k : ℤ → ℕ} {e : ∀ p, Fin (k p) → K.X p}
    {φ : ∀ p, Fin (k p) → Module.Dual R (K.X p)} (he : ∀ p m, ∑ i, φ p i m • e p i = m)
    {M : Type*} [AddCommGroup M] [Module R M] {p' : ℤ} (m : K.X p') (f : K.X p' →ₗ[R] M)
    (g : ∀ p, Fin (k p) → M) (hne : ∀ p, p ≠ p' → ∀ i, g p i = 0)
    (heq : ∀ i, g p' i = φ p' i m • f (e p' i)) :
    ∑ p ∈ Finset.Icc a b, ∑ i, g p i = f m := by
  by_cases hp' : p' ∈ Finset.Icc a b
  · rw [Finset.sum_eq_single p' (fun p _ hp => Finset.sum_eq_zero fun i _ => hne p hp i)
      (fun h => (h hp').elim)]
    simp only [heq]
    simpa only [map_sum, map_smul] using congrArg f (he p' m)
  · rw [eq_zero_of_isZero (isZero_X_of_notMem_Icc a b hp') m, map_zero]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun i _ => hne p ?_ i
    rintro rfl
    exact hp' hp

/-- **A finite dual basis decomposes the identity of the Hom complex.** If `K` is concentrated in
`[a, b]` and `(e p i, φ p i)` is a finite dual basis of each `K^p`, the identity of
`Hom^n(K, L)` is the sum over `p ∈ [a, b]` and `i` of the evaluation at `e p i` followed by the
single cochain `m ↦ φ p i (m) w`. -/
lemma sum_cochainEval_comp_singleSmulRight (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (k : ℤ → ℕ) (e : ∀ p, Fin (k p) → K.X p)
    (φ : ∀ p, Fin (k p) → Module.Dual R (K.X p))
    (he : ∀ p m, ∑ i, φ p i m • e p i = m) :
    ∑ p ∈ Finset.Icc a b, ∑ i, cochainEval K L n rfl (e p i) ≫ singleSmulRight L n (φ p i) =
      𝟙 ((HomComplexR R K L).X n) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => Cochain.ext _ _ fun p' q' hpq' =>
    ModuleCat.hom_ext (LinearMap.ext fun m => ?_))
  subst hpq'
  show (cochainEval K L n rfl m).hom
      ((∑ p ∈ Finset.Icc a b, ∑ i, cochainEval K L n rfl (e p i) ≫
        singleSmulRight L n (φ p i)).hom z) = (cochainEval K L n rfl m).hom z
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    map_sum]
  refine sum_Icc_sum_eq_of_dual_basis a b he m (Cochain.v (z : Cochain K L n) p' (p' + n) rfl).hom
    _ (fun p hp i => ?_) fun i => ?_
  · exact cochainEval_singleSmulRight_of_ne L n _ hp.symm _ _ _
  · exact cochainEval_singleSmulRight_self L n _ m _

variable (E : ModuleCat.{v} R ⥤ ModuleCat.{v} R) [E.Additive] [E.Linear R]

/-- **The comparison is bijective for a bounded complex of finite projectives.** -/
theorem bijective_comparisonLinearMap (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) :
    Function.Bijective (comparisonLinearMap K L n E) := by
  classical
  have hdb : ∀ p, ∃ (k : ℕ) (e : Fin k → K.X p) (φ : Fin k → Module.Dual R (K.X p)),
      ∀ m, ∑ i, φ i m • e i = m := fun p => by
    have := (hK p).1
    have := (hK p).2
    obtain ⟨k, e, φ, h, -⟩ := Stacks.Discriminant.exists_finite_dual_basis R (K.X p)
    exact ⟨k, e, φ, h⟩
  choose k e φ he using hdb
  have hdec := congrArg E.map (sum_cochainEval_comp_singleSmulRight L n a b k e φ he)
  simp only [Functor.map_sum, Functor.map_comp] at hdec
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun ψ => ?_⟩
  · have hev : ∀ p i, (E.map (cochainEval K L n rfl (e p i))).hom x = 0 := fun p i => by
      have h1 := congrArg (fun f => f.hom (e p i)) (Cochain.congr_v hx p (p + n) rfl)
      rw [comparisonLinearMap_apply, comparisonCochain_v_apply] at h1
      exact h1
    have := congrArg (fun f => f.hom x) hdec
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, hev, map_zero, Finset.sum_const_zero] at this
    simpa using this.symm
  · refine ⟨∑ p ∈ Finset.Icc a b, ∑ i,
      (E.map (singleSmulRight L n (φ p i))).hom ((ψ.v p (p + n) rfl).hom (e p i)), ?_⟩
    ext p' q' hpq' m
    rw [comparisonLinearMap_apply, comparisonCochain_v_apply]
    simp only [map_sum, map_hom_map_hom]
    subst hpq'
    refine sum_Icc_sum_eq_of_dual_basis a b he m (ψ.v p' (p' + n) rfl).hom _
      (fun p hp i => ?_) fun i => ?_
    · rw [singleSmulRight_comp_cochainEval_of_ne L n _ hp.symm, E.map_zero]
      rfl
    · simp only [singleSmulRight_comp_cochainEval_self, E.map_smul, E.map_id,
        ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply]

/-- **The comparison of Hom complexes is an isomorphism for a bounded complex of finite
projectives**: `E(Hom^•(K, L)) ≅ Hom^•(K, E(L))` when `K` is bounded with finite projective
terms and `E` is an additive `R`-linear functor. -/
theorem isIso_comparison (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) :
    IsIso (comparison K L E) := by
  have (n : ℤ) : IsIso ((comparison K L E).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_comparisonLinearMap L n E a b hK)
  exact HomologicalComplex.Hom.isIso_of_components _

end Bijective

end Stacks.HomComplex.LinearFunctor

end
