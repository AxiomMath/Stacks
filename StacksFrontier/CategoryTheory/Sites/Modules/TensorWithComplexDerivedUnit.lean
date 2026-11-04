module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexHomComparison

/-!
# The unit of the derived tensor--Hom adjunction at the shifts of the regular module

Let `(C, O)` be a ringed site over a base ring `R`, let `K` be a K-injective complex of
`O`-modules and `E = End(K)`. The unit of the adjunction `- ⊗_E^𝐋 K ⊣ RHom(K, -)` of Tag 09LY is
an isomorphism at every shift `E[k]` of the regular module. On differential graded modules the
unit of the tensor--Hom adjunction of Tag 09LV sends `x` to `y ↦ x ⊗ y`; at `E` this is
`a ↦ (1 ⊗ -) ∘ a`, an isomorphism `E ≅ Hom(K, E ⊗_E K)` since `y ↦ 1 ⊗ y` is one, and it passes
to the shifts of `E`. Since `E[k] ⊗_E K ≅ K[k]` is K-injective, `RHom(K, -)` is computed there by
`Hom(K, -)`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexDG_homEquiv_id_moduleHom`: the unit of the
  adjunction of Tag 09LV on pure tensors.
* `AlgebraicGeometry.RingedSite.bijective_tensorUnitDG_shift_regular`: `x ↦ (y ↦ x ⊗ y)` is
  bijective at every shift of the regular module.
* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDG_unit_app_shift`: the unit of the
  adjunction of Tag 09LV is invertible at every shift of the regular module.
* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerived_adj_unit_app_shift`: the unit of
  the derived adjunction of Tag 09LY is invertible at every shift of the regular module, for `K`
  K-injective.

## References

* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
* [Stacks Project, Tag 09LY](https://stacks.math.columbia.edu/tag/09LY)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

universe u v w t s

namespace AlgebraicGeometry.RingedSite

/-- The unit of a composite of adjunctions is invertible at `Y` as soon as the unit of the first
is invertible at `Y` and the right adjoint of the first sends the unit of the second at `F Y` to
an isomorphism. -/
theorem isIso_comp_unit_app_of_isIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (Y : C)
    (h₁ : IsIso (adj₁.unit.app Y)) (h₂ : IsIso (G.map (adj₂.unit.app (F.obj Y)))) :
    IsIso ((adj₁.comp adj₂).unit.app Y) := by
  rw [Adjunction.comp_unit_app]
  infer_instance

/-- A component of the right whiskering of an isomorphism of functors is an isomorphism. -/
theorem isIso_whiskerRight_hom_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) (Y : C) :
    IsIso ((Functor.whiskerRight e.hom H).app Y) := by
  rw [Functor.whiskerRight_app]
  infer_instance

/-- A component of the left whiskering of an isomorphism of functors is an isomorphism. -/
theorem isIso_whiskerLeft_hom_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D} (H : E ⥤ C) (e : F ≅ G) (Y : E) :
    IsIso ((Functor.whiskerLeft H e.hom).app Y) := by
  rw [Functor.whiskerLeft_app]
  infer_instance

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type (max u v w t s)) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, max u v w t s} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- The unit of the tensor--Hom adjunction on homotopy categories is invertible at the class of a
module at which the unit on modules is invertible. -/
theorem isIso_tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver_unit_app_of_isIso
    (M : DifferentialGradedModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
    (hM : IsIso ((tensorWithComplexComplexes_adj_homWithComplexOver.{u, v, w, t, s,
      max u v w t s} X R K).unit.app M)) :
    IsIso ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s,
      max u v w t s} X R K).unit.app ((toHomotopyCategory _).obj M)) := by
  simp only [tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver,
    CategoryTheory.Quotient.adjunctionOfSquares]
  dsimp only [Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft]
  simp only [NatTrans.comp_app]
  refine IsIso.comp_isIso' (IsIso.comp_isIso' ?_ ?_) ?_
  · change IsIso ((CategoryTheory.Quotient.functor (homotopyRel _)).map
      ((tensorWithComplexComplexes_adj_homWithComplexOver.{u, v, w, t, s, max u v w t s}
        X R K).unit.app M))
    exact Functor.map_isIso _ _
  · exact isIso_whiskerRight_hom_app _ _ _
  · exact isIso_whiskerLeft_hom_app _ _ _


/-- The identity of a complex of `O`-modules, as a cocycle of the differential graded category of
complexes. -/
abbrev compDGIdCocycle (P : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) :
    (CompDG.{u, v, w, t, s, max u v w t s} X R).Cocycle P P :=
  ⟨(CompDG.{u, v, w, t, s, max u v w t s} X R).id P,
    (CompDG.{u, v, w, t, s, max u v w t s} X R).d_id P⟩

/-- The unit of the tensor--Hom adjunction of Tag 09LV is the adjoint of the identity. -/
theorem tensorWithComplexDG_unit_eq_homEquiv
    (M : (dgCategory.{_, _, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Obj) :
    (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).adjunction.unit.app M =
      (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).adjunction.homEquiv M
        ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)
        (compDGIdCocycle.{u, v, w, t, s} X R _) := by
  refine Eq.symm ((Adjunction.homEquiv_unit _ _ _ _).trans ?_)
  refine (congrArg (fun f => _ ≫ f)
    ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.onComp.map_id
      ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.onComp.obj M))).trans
    (Category.comp_id _)

/-- **The unit of the tensor--Hom adjunction of Tag 09LV on pure tensors**, in its adjoint form:
the image of a homogeneous `x` in `Hom(K, M ⊗_E K)` is the cochain `y ↦ x ⊗ y`. -/
theorem tensorWithComplexDG_homEquiv_id_moduleHom
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Obj)
    (p q : ℤ) (U : X.Cᵒᵖ) (x : M.grading p)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    (((((Rep.{u, v, w, t, s, max u v w t s} X R K).moduleHom
        ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M) p
        ⟨((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).adjunction.homEquiv M
          ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)
          (compDGIdCocycle.{u, v, w, t, s} X R _)).1.1 x, by
          have h := ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).adjunction.homEquiv
            M ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)
            (compDGIdCocycle.{u, v, w, t, s} X R _)).1.2.1 p x x.property
          rw [add_zero] at h
          exact h⟩).v q (p + q) (by omega)).val.app U) y) =
      (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).pure M p q U x y := by
  refine (tensorWithComplexDG_adjunction_homEquiv_apply.{u, v, w, t, s, max u v w t s} X R K M
    ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)
    (compDGIdCocycle.{u, v, w, t, s} X R _) p q U x y).trans ?_
  change (((CompDG.{u, v, w, t, s, max u v w t s} X R).id
    ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)).v (p + q) (p + q)
      (add_zero _)).val.app U _ = _
  rw [CochainComplex.dgCategoryLinear_id_v]
  rfl

/-- The adjoint of the identity, `x ↦ (y ↦ x ⊗ y)`, as a closed degree-zero map of differential
graded `E`-modules `M ⟶ Hom(K, M ⊗_E K)`. -/
abbrev tensorUnitDG
    (M : (dgCategory.{_, _, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Obj) :=
  (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).adjunction.homEquiv M
    ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)
    (compDGIdCocycle.{u, v, w, t, s} X R _)

/-- The underlying linear map of `x ↦ (y ↦ x ⊗ y)`, with its codomain read as the module
`Hom(K, M ⊗_E K)`. -/
abbrev tensorUnitDGMap
    (M : (dgCategory.{_, _, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Obj) :
    M.M →ₗ[R] ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.obj
      ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)).M :=
  (tensorUnitDG.{u, v, w, t, s} X R K M).1.1

/-- The adjoint of the identity sends a homogeneous element to a homogeneous element of the same
degree. -/
private theorem tensorUnitDG_mem_grading
    (M : (dgCategory.{_, _, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Obj) {p : ℤ} (x : M.grading p) :
    (tensorUnitDG.{u, v, w, t, s} X R K M).1.1 x ∈
    ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.obj
      ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)).grading p := by
  have h := (tensorUnitDG.{u, v, w, t, s} X R K M).1.2.1 p x x.property
  rwa [add_zero] at h

/-- The value of `x ↦ (y ↦ x ⊗ y)` at a homogeneous element, read in `Hom(K, M ⊗_E K)` as a
cochain. -/
theorem tensorUnitDG_moduleHom
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Obj)
    (p : ℤ) (x : M.grading p) (hx : (tensorUnitDG.{u, v, w, t, s} X R K M).1.1 x ∈
      ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.obj
        ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M)).grading p)
    (q r : ℤ) (hqr : q + p = r) (U : X.Cᵒᵖ)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    HEq (((((Rep.{u, v, w, t, s, max u v w t s} X R K).moduleHom
        ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M) p
        ⟨(tensorUnitDG.{u, v, w, t, s} X R K M).1.1 x, hx⟩).v q r hqr).val.app U) y)
      ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).pure M p q U x y) := by
  refine (cochain_v_app_heq_of_heq.{u, v, w, t, s} X
      _ U rfl (by omega : r = p + q) hqr (by omega) y y
    HEq.rfl).trans
      (heq_of_eq (tensorWithComplexDG_homEquiv_id_moduleHom.{u, v, w, t, s} X R K M p q U x y))

/-- **At the regular module, `x ↦ (y ↦ x ⊗ y)` is postcomposition with `y ↦ 1 ⊗ y`**: for a
homogeneous `a ∈ E`, the cochain `y ↦ a ⊗ y` is `(1 ⊗ -) ∘ a`. -/
theorem tensorUnitDG_regular_apply {p : ℤ}
    (a : (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra.grading p) :
    (tensorUnitDG.{u, v, w, t, s} X R K
        (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)).1.1 a.1 =
      ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.map
        (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))).1 a.1 := by
  let T := (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K)
  let G := (Rep.{u, v, w, t, s, max u v w t s} X R K)
  have hL : (tensorUnitDG.{u, v, w, t, s} X R K (regularModule G.algebra)).1.1 a.1 ∈
      (G.functor.obj (T.functor.obj (regularModule G.algebra))).grading p := by
    exact tensorUnitDG_mem_grading.{u, v, w, t, s} X R K (regularModule G.algebra) a
  obtain ⟨c, hc, hcomp⟩ := G.map_comp (liftComplex.{u, v, w, t, s} X K)
    (T.functor.obj (regularModule G.algebra)) 0 p p (zero_add p)
    (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K)) a
  rw [← hc]
  have key : G.moduleHom (T.functor.obj (regularModule G.algebra)) p
      ⟨(tensorUnitDG.{u, v, w, t, s} X R K (regularModule G.algebra)).1.1 a.1, hL⟩ =
      G.moduleHom (T.functor.obj (regularModule G.algebra)) p c := by
    rw [hcomp]
    change _ = (G.algebraHom p a).comp (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))
      (add_zero p)
    rw [← regularPure_comp_regularLeftMul.{u, v, w, t, s} X R K a]
    refine Cochain.ext _ _ fun q r hqr => ?_
    rw [Cochain.comp_v _ _ (zero_add p) q q r (add_zero q) hqr, Cochain.ofHom_v]
    ext U y
    refine eq_of_heq ((tensorUnitDG_moduleHom.{u, v, w, t, s} X R K (regularModule G.algebra) p a hL
      q r hqr U y).trans ?_)
    change HEq _ (((T.functor.map (regularLeftMul a)).v q r hqr).val.app U
      (((regularPure.{u, v, w, t, s} X R K).f q).val.app U y))
    refine HEq.symm ((cochain_v_app_heq_of_heq.{u, v, w, t, s} X
        (T.functor.map (regularLeftMul a)) U
      (zero_add q).symm (show r = 0 + q + p by omega) hqr rfl _ _
        (regularPure_apply.{u, v, w, t, s} X R K q U y)).trans
      ((T.map_pure (regularLeftMul a) 0 q U ⟨1, SetLike.one_mem_graded _⟩ y).trans
        (T.pure_heq.{u, v, w, t, s} X R _ U (zero_add p) rfl _ _ y y (mul_one _) HEq.rfl)))
  exact congrArg Subtype.val ((G.moduleHom _ p).injective key)

/-- **`x ↦ (y ↦ x ⊗ y)` is natural against homogeneous maps of every degree**: for a homogeneous
`σ : M ⟶ M'`, `σ(x) ⊗ y = (σ ⊗ K)(x ⊗ y)`. -/
theorem tensorUnitDG_naturality
    {M M' : (dgCategory.{_, _, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Obj}
    {n : ℤ} (σ : (dgCategory.{_, _, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Hom M M' n) :
    (tensorUnitDGMap.{u, v, w, t, s} X R K M' ∘ₗ σ.1 : M.M →ₗ[R]
      ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.obj
        ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj M')).M) =
      ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.map
        ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.map σ)).1 ∘ₗ
        tensorUnitDGMap.{u, v, w, t, s} X R K M := by
  let T := (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K)
  let G := (Rep.{u, v, w, t, s, max u v w t s} X R K)
  refine DirectSum.decompose_lhom_ext M.grading fun p => LinearMap.ext fun x => ?_
  change tensorUnitDGMap.{u, v, w, t, s} X R K M' (σ.1 x.1) =
    (G.functor.map (T.functor.map σ)).1 (tensorUnitDGMap.{u, v, w, t, s} X R K M x.1)
  let x' : M'.grading (p + n) := ⟨σ.1 x, σ.2.1 p x x.property⟩
  have hL : tensorUnitDGMap.{u, v, w, t, s} X R K M' x'.1 ∈
      (G.functor.obj (T.functor.obj M')).grading (p + n) := by
    exact tensorUnitDG_mem_grading.{u, v, w, t, s} X R K M' x'
  have hR : tensorUnitDGMap.{u, v, w, t, s} X R K M x.1 ∈
      (G.functor.obj (T.functor.obj M)).grading p := by
    exact tensorUnitDG_mem_grading.{u, v, w, t, s} X R K M x
  obtain ⟨c, hc, hcomp⟩ := G.map_comp (T.functor.obj M) (T.functor.obj M') n p (p + n)
    (add_comm n p) (T.functor.map σ) ⟨_, hR⟩
  change tensorUnitDGMap.{u, v, w, t, s} X R K M' x'.1 = _
  rw [← hc]
  have key : G.moduleHom (T.functor.obj M') (p + n) ⟨_, hL⟩ =
      G.moduleHom (T.functor.obj M') (p + n) c := by
    rw [hcomp]
    refine Cochain.ext _ _ fun q r hqr => ?_
    change _ = ((G.moduleHom (T.functor.obj M) p ⟨_, hR⟩).comp (T.functor.map σ)
      (by omega : p + n = p + n)).v q r hqr
    rw [Cochain.comp_v _ _ (by omega : p + n = p + n) q (q + p) r rfl (by omega)]
    ext U y
    refine eq_of_heq ((tensorUnitDG_moduleHom.{u, v, w, t, s} X R K M' (p + n) x' hL
      q r hqr U y).trans ?_)
    change HEq _ (((T.functor.map σ).v (q + p) r (by omega)).val.app U
      (((G.moduleHom (T.functor.obj M) p ⟨_, hR⟩).v q (q + p) rfl).val.app U y))
    refine HEq.symm ((cochain_v_app_heq_of_heq.{u, v, w, t, s} X (T.functor.map σ) U
      (show q + p = p + q by omega) (show r = p + q + n by omega) (by omega) (by omega) _ _
        (tensorUnitDG_moduleHom.{u, v, w, t, s} X R K M p x hR q (q + p) rfl U y)).trans
      ((T.map_pure σ p q U x y).trans
        (T.pure_heq.{u, v, w, t, s} X R _ U rfl rfl _ _ y y rfl HEq.rfl)))
  exact congrArg Subtype.val ((G.moduleHom _ (p + n)).injective key)

/-- The image of a homogeneous map with a two-sided homogeneous inverse under a functor of
differential graded categories is bijective. -/
theorem DGFunctor_map_bijective_of_homogeneousIso {R' : Type*} [CommRing R'] {C : DGCategory R'}
    {B' : DifferentialGradedAlgebra R'}
    (Φ : DGCategory.DGFunctor C (dgCategory.{_, _, max u v w t s} B'))
    {M M' : C.Obj} {n m : ℤ} (hnm : n + m = 0) (hmn : m + n = 0)
    (σ : C.Hom M M' n) (τ : C.Hom M' M m)
    (hστ : C.comp hnm σ τ = C.id M') (hτσ : C.comp hmn τ σ = C.id M) :
    Function.Bijective (Φ.map σ).1 := by
  refine Function.bijective_iff_has_inverse.mpr ⟨(Φ.map τ).1, fun z => ?_, fun z => ?_⟩
  · have h := congrArg (fun f => f.1 z) (Φ.map_comp hmn τ σ)
    simp only [hτσ, Φ.map_id] at h
    exact h.symm
  · have h := congrArg (fun f => f.1 z) (Φ.map_comp hnm σ τ)
    simp only [hστ, Φ.map_id] at h
    exact h.symm

/-- **At the regular module `x ↦ (y ↦ x ⊗ y)` is bijective**: it is postcomposition with the
isomorphism `y ↦ 1 ⊗ y`. -/
theorem bijective_tensorUnitDG_regular :
    Function.Bijective (tensorUnitDGMap.{u, v, w, t, s} X R K
      (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)) := by
  have e : tensorUnitDGMap.{u, v, w, t, s} X R K
      (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) =
      ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.map
        (Cochain.ofHom (regularPure.{u, v, w, t, s} X R K))).1 :=
    DirectSum.decompose_lhom_ext (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra.grading
      fun p => LinearMap.ext fun a => tensorUnitDG_regular_apply.{u, v, w, t, s} X R K a
  rw [e]
  exact Function.bijective_iff_has_inverse.mpr
    ⟨((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.map
      (Cochain.ofHom (inv (regularPure.{u, v, w, t, s} X R K)))).1,
      LinearMap.congr_fun (rep_map_regularPure_inv_comp.{u, v, w, t, s} X R K K),
      LinearMap.congr_fun (rep_map_regularPure_comp_inv.{u, v, w, t, s} X R K K)⟩

/-- **At every shift of the regular module `x ↦ (y ↦ x ⊗ y)` is bijective**, by its naturality
against the homogeneous isomorphism `E ⟶ E[k]`. -/
theorem bijective_tensorUnitDG_shift_regular (k : ℤ) :
    Function.Bijective (tensorUnitDGMap.{u, v, w, t, s} X R K
      (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k)) := by
  let A := (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra
  let σ := homogeneousMapToShift (regularModule A) k
  have hΦ : Function.Bijective ((Rep.{u, v, w, t, s, max u v w t s} X R K).functor.map
      ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.map σ)).1 :=
    DGFunctor_map_bijective_of_homogeneousIso.{u, v, w, t, s}
      ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.comp
        (Rep.{u, v, w, t, s, max u v w t s} X R K).functor)
      (neg_add_cancel k) (add_neg_cancel k) σ (homogeneousMapFromShift (regularModule A) k)
      (homogeneousMapToShift_comp_fromShift _ k) (homogeneousMapFromShift_comp_toShift _ k)
  have hcomp : Function.Bijective (tensorUnitDGMap.{u, v, w, t, s} X R K
      (shift (regularModule A) k) ∘ σ.1) := by
    rw [← LinearMap.coe_comp, tensorUnitDG_naturality.{u, v, w, t, s} X R K σ, LinearMap.coe_comp]
    exact hΦ.comp (bijective_tensorUnitDG_regular.{u, v, w, t, s} X R K)
  exact (Function.Bijective.of_comp_iff _ Function.bijective_id).mp hcomp

/-- **The unit of the tensor--Hom adjunction of Tag 09LV is invertible at every shift of the
regular module.** -/
theorem isIso_tensorWithComplexDG_unit_app_shift (k : ℤ) :
    IsIso ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).adjunction.unit.app
      (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k)) := by
  let A := (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra
  rw [tensorWithComplexDG_unit_eq_homEquiv]
  have : IsIso ((compModulesEquivalence A).functor.map (tensorUnitDG.{u, v, w, t, s} X R K
      (shift (regularModule A) k))) :=
    isIso_of_bijective _ (bijective_tensorUnitDG_shift_regular.{u, v, w, t, s} X R K k)
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (compModulesEquivalence A).functor this _

/-- The unit of the tensor--Hom adjunction read on differential graded modules and complexes is
invertible at every shift of the regular module. -/
theorem isIso_tensorWithComplexComplexes_adj_unit_app_shift (k : ℤ) :
    IsIso ((tensorWithComplexComplexes_adj_homWithComplexOver.{u, v, w, t, s, max u v w t s}
      X R K).unit.app
        (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k)) := by
  refine isIso_comp_unit_app_of_isIso _ _ _ (isIso_comp_unit_app_of_isIso _ _ _ ?_ ?_) ?_
  · exact Iso.isIso_hom ((compModulesEquivalence _).symm.unitIso.app _)
  · have : IsIso ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).adjunction.unit.app
        ((compModulesEquivalence
          (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).symm.functor.obj
          (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k))) :=
      isIso_tensorWithComplexDG_unit_app_shift.{u, v, w, t, s} X R K k
    exact Functor.map_isIso _ _
  · have : IsIso ((CochainComplex.cochainCompEquivalence
        (TensorModO.{u, v, w, t, s} X)).toAdjunction.unit.app
        (((compModulesEquivalence (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).symm.functor ⋙
          (tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.onComp).obj
            (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k))) :=
      Iso.isIso_hom ((CochainComplex.cochainCompEquivalence
        (TensorModO.{u, v, w, t, s} X)).unitIso.app _)
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ this

/-- **The unit of the derived tensor--Hom adjunction of Tag 09LY at the class of a module**, read
through the comparisons of the two derived functors: the derived unit followed by `RHom(K, -)` of
the comparison of Tag 09LX is the unit on homotopy categories followed by the comparison of
`Hom(K, -)` with its derived functor. -/
theorem tensorWithComplexDerived_adj_unit_app_fac
    (P : DifferentialGradedModule.HomotopyCategory
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) :
    (tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s}
        X R K).unit.app
          ((quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.obj P) ≫
      (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).map
        ((tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K).app P) =
    (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.map
        ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s, max u v w t s}
          X R K).unit.app P) ≫
      (derivedHomWithComplexUnitOver.{u, v, w, t, s, max u v w t s} X R K).app
        ((tensorWithComplexHomotopy.{u, v, w, t, s, max u v w t s} X R K).obj P) := by
  let : HasDerivedCategory (TensorModO.{u, v, w, t, s} X) := HasDerivedCategory.standard _
  have hα : (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).IsLeftDerivedFunctor
      (show (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q ⋙
            tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⟶
          tensorWithComplexHomotopy.{u, v, w, t, s, max u v w t s} X R K ⋙ DerivedCategory.Qh from
        tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) :=
    tensorWithComplexDerived_isLeftDerivedFunctor.{u, v, w, t, s, max u v w t s} X R K
  have hleft := Functor.isLeftDerivedFunctor_comp_of_resolutions
    (L := (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q)
    (W := quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q ⋙
          tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⟶
        tensorWithComplexHomotopy.{u, v, w, t, s, max u v w t s} X R K ⋙ DerivedCategory.Qh from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K)
    (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K)
    (exists_resolution_q_map_bijective_rep.{u, v, w, t, s, max u v w t s} X R K)
  exact Adjunction.derivedη_fac_app
    (tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s, max u v w t s} X R K)
    (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q ⋙
          tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⟶
        tensorWithComplexHomotopy.{u, v, w, t, s, max u v w t s} X R K ⋙ DerivedCategory.Qh from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K)
    (show homWithComplexHomotopyOver.{u, v, w, t, s, max u v w t s} X R K ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q ⟶
        DerivedCategory.Qh ⋙ derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K from
      derivedHomWithComplexUnitOver.{u, v, w, t, s, max u v w t s} X R K) P

/-- **The unit of the derived tensor--Hom adjunction of Tag 09LY is invertible at every shift of
the regular module, for `K` K-injective.** -/
theorem isIso_tensorWithComplexDerived_adj_unit_app_shift
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] (k : ℤ) :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s}
      X R K).unit.app ((quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.obj
        ((toHomotopyCategory _).obj
          (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k)))) := by
  let P := (toHomotopyCategory (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).obj
    (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k)
  have h₁ : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K).app P) :=
    isIso_tensorWithComplexDerivedCounit_app_of_leftOrthogonal _ _ _
      (leftOrthogonal_acyclic_shift_regularModule _ k)
  have h₂ :=
    isIso_tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver_unit_app_of_isIso.{u, v, w,
      t, s} X R K _ (isIso_tensorWithComplexComplexes_adj_unit_app_shift.{u, v, w, t, s} X R K k)
  have := isKInjective_tensorWithComplexDG_obj_shift_regularModule.{u, v, w, t, s} X R K k
  have h₃ := isIso_derivedHomWithComplexOverUnit_app_of_isKInjective.{u, v, w, t, s} X R K
    ((tensorWithComplexDG.{u, v, w, t, s, max u v w t s} X R K).functor.obj
      (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) k))
  have h₄ : IsIso ((quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.map
        ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s, max u v w t s}
          X R K).unit.app P) ≫
      (derivedHomWithComplexUnitOver.{u, v, w, t, s, max u v w t s} X R K).app
        ((tensorWithComplexHomotopy.{u, v, w, t, s, max u v w t s} X R K).obj P)) :=
    IsIso.comp_isIso' (Functor.map_isIso _ _) h₃
  rw [← tensorWithComplexDerived_adj_unit_app_fac.{u, v, w, t, s} X R K P] at h₄
  have h₅ : IsIso ((derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).map
      ((tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K).app P)) :=
    Functor.map_isIso _ _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).map
      ((tensorWithComplexDerivedCounit.{u, v, w, t, s, max u v w t s} X R K).app P)) h₅ h₄

end AlgebraicGeometry.RingedSite
