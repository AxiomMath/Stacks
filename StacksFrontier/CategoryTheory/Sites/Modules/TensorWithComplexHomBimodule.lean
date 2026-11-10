module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherent

/-!
# The bimodule `Hom(L, K)` and the comparison with `Hom(L, - ⊗_E K)`

Let `(C, O)` be a ringed site over a base ring `R` (Stacks 0CS6), let `K` and `L` be complexes of
`O`-modules, and let `A = End(K)` and `B = End(L)` be their endomorphism differential graded
`R`-algebras (Tag 09LE). The Hom complex `Ω' = Hom_{Comp^dg(O)}(L, K)` is a differential graded
`(A, B)`-bimodule: `A` acts by postcomposition and `B` by precomposition.

Tensoring with `K` (Tag 09LV) followed by `Hom(L, -)` is a functor of differential graded
categories `Φ : Mod^dg_(A, d) ⥤ Mod^dg_(B, d)`, and `Φ(A) = Hom(L, A ⊗_A K)`. The isomorphism
`K ≅ A ⊗_A K`, `y ↦ 1 ⊗ y`, identifies the bimodule `Ω'` with the bimodule `Φ(A)` of
`DifferentialGraded.Bimodule.ofDGFunctorRegular`, so the comparison of
`StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorTensorComparison` is a natural map
`M ⊗_A Ω' ⟶ Hom(L, M ⊗_A K)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.complexHomBimodule`: `Hom(L, K)` as a differential graded
  `(End(K), End(L))`-bimodule.
* `AlgebraicGeometry.RingedSite.tensorHomDGFunctor`: the functor `M ↦ Hom(L, M ⊗_A K)` of
  differential graded categories.

## Main results

* `AlgebraicGeometry.RingedSite.exists_isIso_regularPure`: `y ↦ 1 ⊗ y` is an isomorphism
  `K ⟶ A ⊗_A K`.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
* [Stacks Project, Tag 0DK9](https://stacks.math.columbia.edu/tag/0DK9)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

universe u v w t s

namespace AlgebraicGeometry.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type (max u v w t s)) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, max u v w t s} X R]

/-- **`Hom(L, K)` as a differential graded `(End(K), End(L))`-bimodule.** The right module is the
value at `K` of the representable functor `Hom(L, -)` of Tag 09LE, and a homogeneous element of
`End(K)` acts through that functor, that is, by postcomposition. -/
abbrev complexHomBimodule (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    DifferentialGraded.Bimodule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra
      (Rep.{u, v, w, t, s, max u v w t s} X R L).algebra :=
  DifferentialGraded.Bimodule.ofDGFunctor (Rep.{u, v, w, t, s, max u v w t s} X R K)
    (Rep.{u, v, w, t, s, max u v w t s} X R L).functor

/-- **`M ↦ Hom(L, M ⊗_A K)`**, as a functor of differential graded categories from the
differential graded modules over `A = End(K)` to those over `B = End(L)`. -/
abbrev tensorHomDGFunctor (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    DGCategory.DGFunctor
      (dgCategory.{max u v w t s, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
      (dgCategory.{max u v w t s, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, max u v w t s} X R L).algebra) :=
  (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.comp
    (Rep.{u, v, w, t, s, max u v w t s} X R L).functor


/-! ### Index transport -/

omit [ScalarSections.{u, v, w, t, s, max u v w t s} X R] in
/-- Pure tensors of equal elements in equal degrees agree, as a heterogeneous equality. -/
theorem TensorWithComplexData.pure_heq {K : CochainComplex (ModO.{u, v, w, t} X) ℤ}
    (D : TensorWithComplexData.{u, v, w, t, s, max u v w t s} X R K)
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Obj)
    (U : X.Cᵒᵖ) {p p' q q' : ℤ} (hp : p = p') (hq : q = q')
    (x : M.grading p) (x' : M.grading p')
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U)
    (y' : ((liftComplex.{u, v, w, t, s} X K).X q').val.obj U)
    (hx : (x : M.M) = x') (hy : HEq y y') :
    HEq (D.pure M p q U x y) (D.pure M p' q' U x' y') := by
  subst p'
  subst q'
  cases Subtype.ext hx
  cases hy
  rfl

/-- The components of a cochain of complexes of `O`-modules at equal degrees agree on equal
sections, as a heterogeneous equality. -/
theorem cochain_v_app_heq_of_heq {F G : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ} {n : ℤ}
    (c : Cochain F G n) (U : X.Cᵒᵖ) {p p' q q' : ℤ} (hp : p = p') (hq : q = q')
    (h : p + n = q) (h' : p' + n = q') (z : (F.X p).val.obj U) (z' : (F.X p').val.obj U)
    (hz : HEq z z') :
    HEq ((c.v p q h).val.app U z) ((c.v p' q' h').val.app U z') := by
  subst p'
  subst q'
  cases hz
  rfl

omit [ScalarSections.{u, v, w, t, s, max u v w t s} X R] in
/-- The unit of the endomorphism algebra of `K`, read in the representable module `Hom(K, K)`,
is the identity of `K`. -/
theorem rep_moduleHom_symm_id_eq_one (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    ((((Rep.{u, v, w, t, s, max u v w t s} X R K).moduleHom
          (liftComplex.{u, v, w, t, s} X K) 0).symm
        ((CompDG.{u, v, w, t, s, max u v w t s} X R).id (liftComplex.{u, v, w, t, s} X K)) :
        ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.obj
          (liftComplex.{u, v, w, t, s} X K)).grading 0) :
        ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.obj
          (liftComplex.{u, v, w, t, s} X K)).M) =
      (1 : (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra.A) := by
  obtain ⟨e, he, hid⟩ := (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra_one
  rw [← he, ← hid]
  exact congrArg Subtype.val
    (((Rep.{u, v, w, t, s, max u v w t s} X R K).algebraHom 0).symm_apply_apply e)

/-- **`y ↦ 1 ⊗ y` is an isomorphism `K ⟶ A ⊗_A K`**, for `A = End(K)` its endomorphism
differential graded algebra acting on itself on the right. It is the isomorphism of
`AlgebraicGeometry.RingedSite.TensorWithComplexData.exists_isIso_pure_regular`, carried from
`Hom(K, K)` to the regular module along the identification of the two, which is the identity of
the underlying module. -/
theorem exists_isIso_regularPure (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    ∃ θ : (liftComplex.{u, v, w, t, s} X K : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) ⟶
        (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj
          (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra),
      IsIso θ ∧ ∀ (q : ℤ) (U : X.Cᵒᵖ) (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U),
        HEq ((θ.f q).val.app U y)
          ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).pure
            (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) 0 q U
            ⟨1, SetLike.one_mem_graded _⟩ y) := by
  let D := tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K
  obtain ⟨j, hj, hspec⟩ := D.exists_isIso_pure_regular
  let εi := DGCategory.representableSelfIsoRegular (A := CompDG.{u, v, w, t, s, max u v w t s} X R)
      (x := liftComplex.{u, v, w, t, s} X K)
  let ε := εi.hom
  let e := (dgFunctorToComplexes D.functor).mapIso εi
  have := hj
  refine ⟨(asIso j ≪≫ e).hom, Iso.isIso_hom _, fun q U y => ?_⟩
  change HEq (((D.functor.map (cocycleOfHom _ ε).1).v q q (add_zero q)).val.app U
    ((j.f q).val.app U y)) _
  refine (cochain_v_app_heq_of_heq.{u, v, w, t, s} X
      (D.functor.map (cocycleOfHom _ ε).1) U (zero_add q).symm
    ((zero_add q).symm.trans (add_zero (0 + q)).symm) (add_zero q) rfl _ _ (hspec q U y)).trans ?_
  refine (D.map_pure (cocycleOfHom _ ε).1 0 q U _ y).trans ?_
  exact D.pure_heq.{u, v, w, t, s} X R _ U (add_zero 0) rfl _ _ y y
    (rep_moduleHom_symm_id_eq_one.{u, v, w, t, s} X R K) HEq.rfl

/-- The isomorphism `K ⟶ A ⊗_A K`, `y ↦ 1 ⊗ y`, of
`AlgebraicGeometry.RingedSite.exists_isIso_regularPure`. -/
def regularPure (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    (liftComplex.{u, v, w, t, s} X K : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) ⟶
      (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj
        (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) :=
  (exists_isIso_regularPure.{u, v, w, t, s} X R K).choose

/-- The morphism `regularPure`, `y ↦ 1 ⊗ y`, is an isomorphism. -/
instance isIso_regularPure (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    IsIso (regularPure.{u, v, w, t, s} X R K) :=
  (exists_isIso_regularPure.{u, v, w, t, s} X R K).choose_spec.1

/-- In each degree, `regularPure` sends a section `y` of `K` to the pure tensor `1 ⊗ y`. -/
theorem regularPure_apply (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) (q : ℤ) (U : X.Cᵒᵖ)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    HEq (((regularPure.{u, v, w, t, s} X R K).f q).val.app U y)
      ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).pure
        (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) 0 q U
        ⟨1, SetLike.one_mem_graded _⟩ y) :=
  (exists_isIso_regularPure.{u, v, w, t, s} X R K).choose_spec.2 q U y

/-- **`y ↦ 1 ⊗ y` intertwines the two actions of `A = End(K)`**: left multiplication by a
homogeneous `a` on `A ⊗_A K` (tensored with `K`) and `a` itself acting on `K`. On pure tensors
this is `a ⊗ y = (1 · a) ⊗ y = 1 ⊗ a(y)`, the balancing relation of Tag 09LV. -/
theorem regularPure_comp_regularLeftMul (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) {n : ℤ}
    (a : (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra.grading n) :
    (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K)).comp
        ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.map (regularLeftMul a))
        (zero_add n) =
      ((Rep.{u, v, w, t, s, max u v w t s} X R K).algebraHom n a).comp
        (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K)) (add_zero n) := by
  let D := tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) hpq,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q), Cochain.ofHom_v, Cochain.ofHom_v]
  ext U y
  change ((D.functor.map (regularLeftMul a)).v p q hpq).val.app U
      (((regularPure.{u, v, w, t, s} X R K).f p).val.app U y) =
    ((regularPure.{u, v, w, t, s} X R K).f q).val.app U
      ((((Rep.{u, v, w, t, s, max u v w t s} X R K).algebraHom n a).v p q hpq).val.app U y)
  refine eq_of_heq ?_
  have hL := (cochain_v_app_heq_of_heq.{u, v, w, t, s} X (D.functor.map (regularLeftMul a)) U
    (zero_add p).symm (show q = 0 + p + n by omega) hpq rfl _ _
      (regularPure_apply.{u, v, w, t, s} X R K p U y)).trans
    (D.map_pure (regularLeftMul a) 0 p U ⟨1, SetLike.one_mem_graded _⟩ y)
  have hR := (regularPure_apply.{u, v, w, t, s} X R K q U _).trans
    ((D.pure_heq.{u, v, w, t, s} X R _ U rfl hpq.symm ⟨1, SetLike.one_mem_graded _⟩
      ⟨1, SetLike.one_mem_graded _⟩ _ _ rfl
      (cochain_v_app_heq_of_heq.{u, v, w, t, s} X _ U rfl hpq.symm hpq rfl y y HEq.rfl)).trans
    (D.pure_balance (regularModule _) 0 p n U ⟨1, SetLike.one_mem_graded _⟩ a y).symm)
  refine hL.trans (HEq.trans ?_ hR.symm)
  refine D.pure_heq.{u, v, w, t, s} X R _ U rfl rfl _ _ y y ?_ HEq.rfl
  change (a : (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra.A) * 1 =
    MulOpposite.op (a : (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra.A) • 1
  rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_one, one_mul]

/-- The closed degree-zero cochain of a chain map, as a cocycle of the differential graded
category of complexes. -/
abbrev compDGCocycleOfHom {F G : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ} (φ : F ⟶ G) :
    (CompDG.{u, v, w, t, s, max u v w t s} X R).Cocycle F G :=
  ⟨Cochain.ofHom φ, δ_ofHom φ⟩

/-- `y ↦ 1 ⊗ y`, read through `Hom(L, -)`, intertwines the left actions of `A = End(K)` on
`Hom(L, K)` and on `Hom(L, A ⊗_A K)`. -/
theorem complexHomBimodule_map_left_aux (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) {n : ℤ}
    (a : (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra.grading n) :
    ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.map
          (regularLeftMul a))).1 ∘ₗ
      ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))).1 =
    ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))).1 ∘ₗ
      ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        ((Rep.{u, v, w, t, s, max u v w t s} X R K).algebraHom n a)).1 := by
  have h := congrArg (fun f => ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map f).1)
    (regularPure_comp_regularLeftMul.{u, v, w, t, s} X R K a)
  change ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
      ((CompDG.{u, v, w, t, s, max u v w t s} X R).comp (add_zero n) _ _)).1 =
    ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
      ((CompDG.{u, v, w, t, s, max u v w t s} X R).comp (zero_add n) _ _)).1 at h
  rw [DGCategory.DGFunctor.map_comp, DGCategory.DGFunctor.map_comp] at h
  exact h

/-- **The homomorphism of bimodules `Hom(L, K) ⟶ Hom(L, A ⊗_A K)`**, postcomposition with
`y ↦ 1 ⊗ y`. -/
def complexHomBimoduleToRegular (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    complexHomBimodule.{u, v, w, t, s} X R K L ⟶
      DifferentialGraded.Bimodule.ofDGFunctorRegular
        (tensorHomDGFunctor.{u, v, w, t, s} X R K L) where
  rightHom := homOfCocycle _ ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.mapCocycle
    (compDGCocycleOfHom.{u, v, w, t, s} X R (regularPure.{u, v, w, t, s} X R K)))
  map_left _ _ a y :=
    LinearMap.congr_fun (complexHomBimodule_map_left_aux.{u, v, w, t, s} X R K L a).symm y.1

omit [ScalarSections.{u, v, w, t, s, max u v w t s} X R] in
/-- A functor of differential graded categories out of the complexes of `O`-modules carries the
cochain of a composite of chain maps to the composite of the images. -/
theorem dgFunctor_map_ofHom_comp {D : DGCategory R}
    (G : DGCategory.DGFunctor (CompDG.{u, v, w, t, s, max u v w t s} X R) D)
    {F₁ F₂ F₃ : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ} (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    G.map (Cochain.ofHom (f ≫ g)) = D.comp (add_zero 0) (G.map (Cochain.ofHom g))
      (G.map (Cochain.ofHom f)) := by
  rw [Cochain.ofHom_comp]
  exact G.map_comp (add_zero 0) (Cochain.ofHom g) (Cochain.ofHom f)

omit [ScalarSections.{u, v, w, t, s, max u v w t s} X R] in
/-- A functor of differential graded categories out of the complexes of `O`-modules carries the
cochain of an identity chain map to the identity. -/
theorem dgFunctor_map_ofHom_id {D : DGCategory R}
    (G : DGCategory.DGFunctor (CompDG.{u, v, w, t, s, max u v w t s} X R) D)
    (F : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) :
    G.map (Cochain.ofHom (𝟙 F)) = D.id (G.obj F) :=
  G.map_id F

/-- Postcomposition with `y ↦ 1 ⊗ y` followed by postcomposition with its inverse, read through
`Hom(L, -)`, is the identity. -/
theorem rep_map_regularPure_inv_comp (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        (Cochain.ofHom (inv (regularPure.{u, v, w, t, s} X R K)))).1 ∘ₗ
      ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))).1 = LinearMap.id := by
  simpa [dgFunctor_map_ofHom_id] using
    (congrArg Subtype.val (dgFunctor_map_ofHom_comp.{u, v, w, t, s} X R
      (Rep.{u, v, w, t, s, max u v w t s} X R L).functor (regularPure.{u, v, w, t, s} X R K)
      (inv (regularPure.{u, v, w, t, s} X R K)))).symm

/-- Postcomposition with the inverse of `y ↦ 1 ⊗ y` followed by postcomposition with `y ↦ 1 ⊗ y`,
read through `Hom(L, -)`, is the identity. -/
theorem rep_map_regularPure_comp_inv (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))).1 ∘ₗ
      ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        (Cochain.ofHom (inv (regularPure.{u, v, w, t, s} X R K)))).1 = LinearMap.id := by
  simpa [dgFunctor_map_ofHom_id] using
    (congrArg Subtype.val (dgFunctor_map_ofHom_comp.{u, v, w, t, s} X R
      (Rep.{u, v, w, t, s, max u v w t s} X R L).functor (inv (regularPure.{u, v, w, t, s} X R K))
      (regularPure.{u, v, w, t, s} X R K))).symm

/-- The underlying map of `complexHomBimoduleToRegular` is postcomposition with `y ↦ 1 ⊗ y`. -/
theorem complexHomBimoduleToRegular_toFun (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    (complexHomBimoduleToRegular.{u, v, w, t, s} X R K L).rightHom.toFun =
      ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.map
        (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))).1 := rfl

/-- **The inverse homomorphism of bimodules `Hom(L, A ⊗_A K) ⟶ Hom(L, K)`**, postcomposition with
the inverse of `y ↦ 1 ⊗ y`. -/
def complexHomBimoduleFromRegular (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    DifferentialGraded.Bimodule.ofDGFunctorRegular (tensorHomDGFunctor.{u, v, w, t, s} X R K L) ⟶
      complexHomBimodule.{u, v, w, t, s} X R K L where
  rightHom := homOfCocycle _ ((Rep.{u, v, w, t, s, max u v w t s} X R L).functor.mapCocycle
    (compDGCocycleOfHom.{u, v, w, t, s} X R (inv (regularPure.{u, v, w, t, s} X R K))))
  map_left n p a y := by
    let G := (Rep.{u, v, w, t, s, max u v w t s} X R L).functor
    have hθ := rep_map_regularPure_inv_comp.{u, v, w, t, s} X R K L
    have hθ' := rep_map_regularPure_comp_inv.{u, v, w, t, s} X R K L
    have hm := complexHomBimodule_map_left_aux.{u, v, w, t, s} X R K L a
    have H : (G.map (Cochain.ofHom (inv (regularPure.{u, v, w, t, s} X R K)))).1 ∘ₗ
        (G.map ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.map
          (regularLeftMul a))).1 =
        (G.map ((Rep.{u, v, w, t, s, max u v w t s} X R K).algebraHom n a)).1 ∘ₗ
          (G.map (Cochain.ofHom (inv (regularPure.{u, v, w, t, s} X R K)))).1 := by
      calc _ = (G.map (Cochain.ofHom (inv (regularPure.{u, v, w, t, s} X R K)))).1 ∘ₗ
            ((G.map ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.map
              (regularLeftMul a))).1 ∘ₗ
              (G.map (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))).1) ∘ₗ
            (G.map (Cochain.ofHom (inv (regularPure.{u, v, w, t, s} X R K)))).1 := by
            rw [LinearMap.comp_assoc, hθ', LinearMap.comp_id]
        _ = _ := by
            rw [hm, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, hθ, LinearMap.id_comp]
    exact LinearMap.congr_fun H y.1

/-- **`Hom(L, K) ≅ Hom(L, A ⊗_A K)` as differential graded `(A, B)`-bimodules.** -/
def complexHomBimoduleIsoRegular (K L : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    complexHomBimodule.{u, v, w, t, s} X R K L ≅
      DifferentialGraded.Bimodule.ofDGFunctorRegular
        (tensorHomDGFunctor.{u, v, w, t, s} X R K L) where
  hom := complexHomBimoduleToRegular.{u, v, w, t, s} X R K L
  inv := complexHomBimoduleFromRegular.{u, v, w, t, s} X R K L
  hom_inv_id := by
    refine DifferentialGraded.Bimodule.Hom.ext (DifferentialGradedModule.Hom.ext ?_)
    exact rep_map_regularPure_inv_comp.{u, v, w, t, s} X R K L
  inv_hom_id := by
    refine DifferentialGraded.Bimodule.Hom.ext (DifferentialGradedModule.Hom.ext ?_)
    exact rep_map_regularPure_comp_inv.{u, v, w, t, s} X R K L

end AlgebraicGeometry.RingedSite
