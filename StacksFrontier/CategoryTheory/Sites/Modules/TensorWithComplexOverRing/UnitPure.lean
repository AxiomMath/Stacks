module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex

/-!
# The unit of the differential graded tensor-Hom adjunction on pure tensors

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules with endomorphism differential
graded algebra `(E, d) = Hom_{Comp^dg(O)}(K, K)`, and let `M` be a differential graded
`E`-module. The tensor product `M ⊗_E K` of Tag 09LV is left adjoint to `Hom(K, -)`, and the unit
of that adjunction sends a homogeneous `x ∈ M^p` to the degree-`p` morphism `K → M ⊗_E K` which is
`y ↦ x ⊗ y` on sections: it is the pure-tensor map. This is the formula which the adjunction of
`AlgebraicGeometry.RingedSite.TensorWithComplexData` does not record, read off its construction.

Two consequences are recorded: the unit is compatible with homogeneous morphisms of *every*
degree, not only with the closed degree-zero ones of the category of complexes, since the
differential graded tensor functor acts on pure tensors through its first factor without a sign;
and it is compatible with the right action of `E`, by the balancing relation.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexDG_unit_pure`: the formula.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDG_unit_map`: compatibility with homogeneous
  morphisms of any degree.

## References

* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, o} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- The unit of the differential graded tensor-Hom adjunction, at a homogeneous element. -/
theorem tensorWithComplexDG_unit_mem
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (p : ℤ) (x : M.grading p) :
    ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.unit.app M).1.1 (x : M.M) ∈
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M)).grading p := by
  have h := ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.unit.app M).1.2.1 p
    (x : M.M) x.property
  rw [add_zero] at h
  exact h

/-- **The unit of the adjunction of Tag 09LV is the pure-tensor map.** For a homogeneous
`x ∈ M^p`, the unit sends `x` to the degree-`p` morphism `K → M ⊗_E K` whose value on a section
`y` of `K^q` is the pure tensor `x ⊗ y`. -/
theorem tensorWithComplexDG_unit_pure
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (p q : ℤ) (x : M.grading p) (U : X.Cᵒᵖ)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    ((((Rep.{u, v, w, t, s, o} X R K).moduleHom
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M) p
        ⟨_, tensorWithComplexDG_unit_mem.{u, v, w, t, s, o} X R K M p x⟩).v q (p + q)
          (by omega)).val.app U) y =
      (tensorWithComplexDG.{u, v, w, t, s, o} X R K).pure M p q U x y := by
  have key : (⟨_, tensorWithComplexDG_unit_mem.{u, v, w, t, s, o} X R K M p x⟩ :
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M)).grading p) =
      (cocycleHom (tensorHomEquiv.{u, v, w, t, s, o} X R K M
        ((tensorDG.{u, v, w, t, s, o} X R K).obj M)
        (𝟙 (show (CompDG.{u, v, w, t, s, o} X R).Comp from
          (tensorDG.{u, v, w, t, s, o} X R K).obj M)))).gradedMap p x := by
    apply Subtype.ext
    rfl
  rw [key]
  have h := tensorHomEquiv_pure.{u, v, w, t, s, o} X R K M
    ((tensorDG.{u, v, w, t, s, o} X R K).obj M)
    (𝟙 (show (CompDG.{u, v, w, t, s, o} X R).Comp from (tensorDG.{u, v, w, t, s, o} X R K).obj M))
    p q (p + q) rfl U x y
  refine h.trans ?_
  change (((Cochain.ofHom (𝟙 (show CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ from
    (tensorDG.{u, v, w, t, s, o} X R K).obj M))).v (p + q) (p + q)
    (add_zero _)).val.app U) _ = _
  rw [Cochain.ofHom_v]
  rfl

/-- The pure-tensor formula for the unit, with the target degree of the component free. -/
theorem tensorWithComplexDG_unit_pure_heq
    (M : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj)
    (p q d : ℤ) (hd : q + p = d) (x : M.grading p) (U : X.Cᵒᵖ)
    (y : ((liftComplex.{u, v, w, t, s} X K).X q).val.obj U) :
    HEq ((((Rep.{u, v, w, t, s, o} X R K).moduleHom
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M) p
        ⟨_, tensorWithComplexDG_unit_mem.{u, v, w, t, s, o} X R K M p x⟩).v q d hd).val.app U y)
      ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).pure M p q U x y) := by
  obtain rfl : d = p + q := by omega
  exact heq_of_eq (tensorWithComplexDG_unit_pure.{u, v, w, t, s, o} X R K M p q x U y)

/-- A component of the image of a homogeneous morphism under a functor, at heterogeneously equal
arguments. -/
theorem cochain_v_app_heq {P Q : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ} {n : ℤ}
    (z : Cochain P Q n) {e e' d d' : ℤ} (he : e = e') (hd : d = d') (h : e + n = d)
    (h' : e' + n = d') (U : X.Cᵒᵖ) {a : (P.X e).val.obj U} {a' : (P.X e').val.obj U}
    (ha : HEq a a') :
    HEq (((z.v e d h).val.app U) a) (((z.v e' d' h').val.app U) a') := by
  subst he hd
  rw [eq_of_heq ha]

/-- **The unit of Tag 09LV is compatible with homogeneous morphisms of every degree.** For a
homogeneous morphism `f : M ⟶ M'` of degree `n` and a homogeneous `x ∈ M^p`, the unit sends
`f x` to the composite of `x ⊗ -` with the image of `f` under the tensor functor: on pure tensors
both are `y ↦ f(x) ⊗ y`, the tensor functor acting through its first factor without a sign. -/
theorem tensorWithComplexDG_unit_map
    {M M' : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Obj}
    {n p : ℤ} (f : (dgCategory.{_, _, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra).Hom
      M M' n) (x : M.grading p) :
    (Rep.{u, v, w, t, s, o} X R K).moduleHom
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M') (p + n)
        ⟨_, tensorWithComplexDG_unit_mem.{u, v, w, t, s, o} X R K M' (p + n)
          ⟨f.1 x, f.2.1 p x x.property⟩⟩ =
      (CompDG.{u, v, w, t, s, o} X R).comp (show n + p = p + n by omega)
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.map f)
        ((Rep.{u, v, w, t, s, o} X R K).moduleHom
          ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M) p
          ⟨_, tensorWithComplexDG_unit_mem.{u, v, w, t, s, o} X R K M p x⟩) := by
  refine Cochain.ext _ _ fun q d hqd => ?_
  rw [CochainComplex.dgCategoryLinear_comp_v (B := TensorModO.{u, v, w, t, s} X) (R := R) _ _ _
    q (q + p) d rfl (by omega)]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext y
  refine eq_of_heq ((tensorWithComplexDG_unit_pure_heq.{u, v, w, t, s, o} X R K M' (p + n) q d
    (by omega) ⟨f.1 x, f.2.1 p x x.property⟩ U y).trans ?_)
  change HEq _ ((((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.map f).v (q + p) d
    (by omega)).val.app U (((((Rep.{u, v, w, t, s, o} X R K).moduleHom
      ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M) p
        ⟨_, tensorWithComplexDG_unit_mem.{u, v, w, t, s, o} X R K M p x⟩).v q (q + p)
          rfl).val.app U) y))
  refine HEq.symm ((cochain_v_app_heq.{u, v, w, t, s} X _ (show q + p = p + q by omega)
    (show d = p + q + n by omega) (by omega) (by omega) U
    (tensorWithComplexDG_unit_pure_heq.{u, v, w, t, s, o} X R K M p q (q + p) rfl x U y)).trans ?_)
  exact (tensorWithComplexDG.{u, v, w, t, s, o} X R K).map_pure f p q U x y

end AlgebraicGeometry.RingedSite

end
