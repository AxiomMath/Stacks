module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Defs
public import StacksFrontier.Algebra.DifferentialGraded.LeftModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex

/-!
# The left action of a left differential graded module on its underlying complex

A left differential graded module `L` over a differential graded `R`-algebra `A` has an underlying
cochain complex of `R`-modules, namely its homogeneous pieces with the restriction of its
differential, and `A` acts on that complex by left multiplication. This file constructs that
complex and that action.

The action is constructed relative to a chosen isomorphism of the underlying complex with another
complex `M`, so that a client may present the same complex differently; taking the isomorphism to
be the identity gives the action on the underlying complex itself.

## Main definitions

* `DifferentialGraded.LeftModule.gradedDifferential`: the differential on a homogeneous piece.
* `DifferentialGraded.LeftModule.toCochainComplex`: the underlying cochain complex.
* `DifferentialGraded.LeftModule.actionLinear`: left multiplication by a homogeneous element, on
  a homogeneous piece.
* `DifferentialGraded.LeftModule.leftAction`: the resulting left differential graded action on a
  complex identified with the underlying one.
* `DifferentialGraded.LeftModule.oppositeGradingEquiv` and
  `DifferentialGraded.LeftModule.oppositeCochainIso`: the identification of the homogeneous pieces
  and of the underlying complex with those of the right module over the graded opposite that the
  left module corresponds to.

## Main results

* `DifferentialGraded.LeftModule.leftAction_apply`: on each homogeneous piece the action is left
  multiplication, transported through the chosen isomorphism.

## Implementation notes

The Leibniz rule of the action is the one place where the Koszul sign has to be moved between
`Int.negOnePow`, its image in `R` and the `ℤ`-action; this is isolated in the last field of
`leftAction`, whose computation is carried out on the homogeneous pieces after transporting
through the isomorphism with `Chain`-level helper lemmas
`toCochainComplexIso_hom_d_apply` and `toCochainComplexIso_inv_d_apply`.

## References

* [Stacks Project, Tag 0FQ3](https://stacks.math.columbia.edu/tag/0FQ3)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u

namespace DifferentialGraded.LeftModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- The differential of a left differential graded module, restricted to its homogeneous pieces. -/
def gradedDifferential (L : LeftModule A) (n : ℤ) : L.grading n →ₗ[R] L.grading (n + 1) where
  toFun x := ⟨L.d x, L.d_mem n x x.property⟩
  map_add' x y := Subtype.ext (L.d.map_add (x : L.M) (y : L.M))
  map_smul' r x := Subtype.ext (L.d.map_smul r (x : L.M))

/-- The cochain complex of `R`-modules underlying a left differential graded module. -/
def toCochainComplex (L : LeftModule A) : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (L.grading n))
    (fun n => ModuleCat.ofHom (gradedDifferential A L n)) (fun n => by
      ext x
      exact LinearMap.congr_fun L.d_comp_d x)

/-- An isomorphism of complexes of modules commutes with the differentials, elementwise. -/
private theorem iso_hom_d_apply {M N : CochainComplex (ModuleCat.{u} R) ℤ} (i : M ≅ N)
    (p q : ℤ) (x : M.X p) : N.d p q (i.hom.f p x) = i.hom.f q (M.d p q x) :=
  ConcreteCategory.congr_hom (i.hom.comm p q) x

/-- The inverse of an identification of the underlying complex with `M` commutes with the
differentials. -/
theorem toCochainComplexIso_inv_d_apply (L : LeftModule A)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (i : toCochainComplex A L ≅ M) (p : ℤ) (x : M.X p) :
    (toCochainComplex A L).d p (p + 1) (i.inv.f p x) = i.inv.f (p + 1) (M.d p (p + 1) x) :=
  iso_hom_d_apply i.symm p (p + 1) x

/-- An identification of the underlying complex with `M` commutes with the differentials. -/
theorem toCochainComplexIso_hom_d_apply (L : LeftModule A)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (i : toCochainComplex A L ≅ M) (p q : ℤ)
    (x : (toCochainComplex A L).X p) :
    M.d p q (i.hom.f p x) = i.hom.f q ((toCochainComplex A L).d p q x) :=
  iso_hom_d_apply i p q x

/-- Left multiplication by a homogeneous element of `A`, on a homogeneous piece of `L`. -/
def actionLinear (L : LeftModule A) (n p q : ℤ) (h : p + n = q) (a : A.grading n) :
    L.grading p →ₗ[R] L.grading q where
  toFun x := ⟨(a : A.A) • (x : L.M), by
    have hx := L.smul_mem n p (a : A.A) (x : L.M) a.property x.property
    have hx' : (a : A.A) • (x : L.M) ∈ L.grading (p + n) := by
      simpa only [add_comm] using hx
    exact h ▸ hx'⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' r x := Subtype.ext (by
    change (a : A.A) • (r • (x : L.M)) = r • ((a : A.A) • (x : L.M))
    exact (smul_comm r (a : A.A) (x : L.M)).symm)

/-- Left multiplication by a homogeneous element of `A`, as a cochain of `M`. -/
def actionCochain (L : LeftModule A) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : toCochainComplex A L ≅ M) (n : ℤ) (a : A.grading n) : Cochain M M n :=
  Cochain.mk fun p q hpq =>
    i.inv.f p ≫ ModuleCat.ofHom (actionLinear A L n p q hpq a) ≫ i.hom.f q

/-- A left differential graded module gives a left differential graded action of `A` on its
underlying complex; the identification `i` permits a different presentation of that complex. -/
noncomputable def leftAction (L : LeftModule A) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : toCochainComplex A L ≅ M) : A.LeftAction M := by
  refine {
    action := fun n => {
      toFun := actionCochain A L M i n
      map_add' := ?_
      map_smul' := ?_ }
    map_one := ?_
    map_mul := ?_
    map_d := ?_ }
  · intro a b
    apply Cochain.ext
    intro p q hpq
    apply ModuleCat.hom_ext
    ext x
    change i.hom.f q (actionLinear A L n p q hpq (a + b) (i.inv.f p x)) =
      i.hom.f q (actionLinear A L n p q hpq a (i.inv.f p x)) +
        i.hom.f q (actionLinear A L n p q hpq b (i.inv.f p x))
    calc
      _ = i.hom.f q (actionLinear A L n p q hpq a (i.inv.f p x) +
            actionLinear A L n p q hpq b (i.inv.f p x)) := by
        congr 1
        apply Subtype.ext
        simp [actionLinear, add_smul]
      _ = _ := map_add (i.hom.f q).hom _ _
  · intro r a
    apply Cochain.ext
    intro p q hpq
    apply ModuleCat.hom_ext
    ext x
    change i.hom.f q (actionLinear A L n p q hpq (r • a) (i.inv.f p x)) =
      r • i.hom.f q (actionLinear A L n p q hpq a (i.inv.f p x))
    calc
      _ = i.hom.f q (r • actionLinear A L n p q hpq a (i.inv.f p x)) := by
        congr 1
        apply Subtype.ext
        let xL : L.grading p := i.inv.f p x
        let y : L.M := xL
        change ((r • (a : A.A)) • y) = r • ((a : A.A) • y)
        exact smul_assoc r (a : A.A) y
      _ = _ := map_smul (i.hom.f q).hom r _
  · apply Cochain.ext₀
    intro p
    apply ModuleCat.hom_ext
    ext x
    change i.hom.f p (actionLinear A L 0 p p (add_zero p)
      ⟨1, SetLike.one_mem_graded A.grading⟩ (i.inv.f p x)) = x
    have hx : i.hom.f p (i.inv.f p x) = x := by
      change (i.inv.f p ≫ i.hom.f p) x = x
      exact congrArg (fun f => f x) (congrArg (fun f => f.f p) i.inv_hom_id)
    simpa [actionLinear, one_smul] using hx
  · intro n m a b
    apply Cochain.ext
    intro p q hpq
    apply ModuleCat.hom_ext
    ext x
    rw [Cochain.comp_v _ _ _ p (p + m) q rfl (by omega)]
    let xL : L.grading p := i.inv.f p x
    change i.hom.f q (actionLinear A L (n + m) p q hpq
        ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ xL) =
      i.hom.f q (actionLinear A L n (p + m) q (by omega) a
        (i.inv.f (p + m) (i.hom.f (p + m) (actionLinear A L m p (p + m) rfl b xL))))
    have hcancel (y : L.grading (p + m)) : i.inv.f (p + m) (i.hom.f (p + m) y) = y := by
      change (i.hom.f (p + m) ≫ i.inv.f (p + m)) y = y
      exact congrArg (fun f => f y) (congrArg (fun f => f.f (p + m)) i.hom_inv_id)
    apply congrArg (i.hom.f q)
    apply Subtype.ext
    simp [actionLinear, hcancel, mul_smul]
  · intro n a
    change actionCochain A L M i (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ =
      δ n (n + 1) (actionCochain A L M i n a)
    apply Cochain.ext
    intro p q hpq
    have hq : p + n + 1 = q := by omega
    cases hq
    rw [δ_v (n := n) (m := n + 1) rfl _ p (p + n + 1) (by omega) (p + n) (p + 1) (by omega) rfl]
    apply ModuleCat.hom_ext
    ext x
    change i.hom.f (p + n + 1) (actionLinear A L (n + 1) p (p + n + 1) (by omega)
        ⟨A.d a, A.d_mem n a a.property⟩ (i.inv.f p x)) =
      M.d (p + n) (p + n + 1)
          (i.hom.f (p + n) (actionLinear A L n p (p + n) rfl a (i.inv.f p x))) +
        (n + 1).negOnePow • i.hom.f (p + n + 1)
          (actionLinear A L n (p + 1) (p + n + 1) (by omega) a (i.inv.f (p + 1) (M.d p (p + 1) x)))
    rw [toCochainComplexIso_hom_d_apply A L M i (p + n) (p + n + 1)
      (actionLinear A L n p (p + n) rfl a (i.inv.f p x)),
      ← toCochainComplexIso_inv_d_apply A L M i p x]
    let xL : L.grading p := i.inv.f p x
    let daX : L.grading (p + n + 1) :=
      actionLinear A L (n + 1) p (p + n + 1) (by omega) ⟨A.d a, A.d_mem n a a.property⟩ xL
    let dAX : L.grading (p + n + 1) :=
      gradedDifferential A L (p + n) (actionLinear A L n p (p + n) rfl a xL)
    let dx : L.grading (p + 1) := gradedDifferential A L p xL
    let aDx : L.grading (p + n + 1) :=
      actionLinear A L n (p + 1) (p + n + 1) (by omega) a dx
    have hda : actionLinear A L (n + 1) p (p + n + 1) hpq
        ⟨A.d a, A.d_mem n a a.property⟩ (i.inv.f p x) = daX := rfl
    have hdAX : (toCochainComplex A L).d (p + n) (p + n + 1)
        (actionLinear A L n p (p + n) rfl a (i.inv.f p x)) = dAX := by
      simp [toCochainComplex, gradedDifferential, actionLinear, dAX, xL]
      rfl
    have haDx : actionLinear A L n (p + 1) (p + n + 1) (by omega) a
        ((toCochainComplex A L).d p (p + 1) (i.inv.f p x)) = aDx := by
      simp [toCochainComplex, gradedDifferential, actionLinear, aDx, dx, xL]
      rfl
    rw [hda, hdAX, haDx, Int.negOnePow_succ]
    have hLeibniz := L.leibniz n p (a : A.A) (xL : L.M) a.property xL.property
    rw [← Int.cast_smul_eq_zsmul R (n.negOnePow : ℤ), Int.coe_negOnePow R n] at hLeibniz
    have hLeibniz' : (A.d a : A.A) • (xL : L.M) =
        L.d ((a : A.A) • (xL : L.M)) - (n.negOnePow : R) • ((a : A.A) • L.d (xL : L.M)) := by
      rw [hLeibniz, Int.coe_negOnePow R n]
      abel
    have hSub : daX = dAX - (n.negOnePow : R) • aDx := by
      apply Subtype.ext
      simpa [daX, dAX, aDx, dx, actionLinear, gradedDifferential] using hLeibniz'
    rw [hSub]
    refine (map_sub (i.hom.f (p + n + 1)).hom dAX _).trans ?_
    rw [map_smul (i.hom.f (p + n + 1)).hom (n.negOnePow : R) aDx, sub_eq_add_neg, ← neg_smul,
      ← Int.cast_neg, Int.cast_smul_eq_zsmul]
    rfl

/-- On each homogeneous piece, the action attached to a left differential graded module is its
scalar multiplication, transported through the chosen isomorphism of complexes. -/
theorem leftAction_apply (L : LeftModule A) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : toCochainComplex A L ≅ M) (n p : ℤ) (a : A.grading n) (x : L.grading p) :
    ((leftAction A L M i).action n a).v p (p + n) (by omega) (i.hom.f p x) =
      i.hom.f (p + n)
        (⟨(a : A.A) • (x : L.M), by
          simpa only [add_comm] using
            L.smul_mem n p (a : A.A) (x : L.M) a.property x.property⟩ : L.grading (p + n)) := by
  unfold leftAction
  change i.hom.f (p + n) (actionLinear A L n p (p + n) rfl a (i.inv.f p (i.hom.f p x))) =
    i.hom.f (p + n) ⟨(a : A.A) • (x : L.M), _⟩
  have hx : i.inv.f p (i.hom.f p x) = x := by
    change (i.hom.f p ≫ i.inv.f p) x = x
    exact congrArg (fun f => f x) (congrArg (fun f => f.f p) i.hom_inv_id)
  rw [hx]
  rfl

/-- The homogeneous pieces of a left differential graded module agree with those of the right
module over the graded opposite that it corresponds to. -/
noncomputable def oppositeGradingEquiv (L : LeftModule A) (n : ℤ) :
    L.grading n ≃ₗ[R] ((leftRightEquivalence R A).equivalence.functor.obj L).grading n := by
  let E := leftRightEquivalence R A
  let e := E.underlying L
  refine
    { toFun := fun x => ⟨e.symm x, (E.grading L n (e.symm x)).mpr (by simp [e])⟩
      invFun := fun x => ⟨e x, (E.grading L n x).mp x.property⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    apply Subtype.ext
    simp [e]
  · intro r x
    apply Subtype.ext
    simp [e]
  · intro x
    apply Subtype.ext
    simp [e]
  · intro x
    apply Subtype.ext
    simp [e]

/-- The complex underlying a left differential graded module agrees with the complex underlying the
right module over the graded opposite that it corresponds to. -/
noncomputable def oppositeCochainIso (L : LeftModule A) :
    toCochainComplex A L ≅
      ((leftRightEquivalence R A).equivalence.functor.obj L).toCochainComplex := by
  let E := leftRightEquivalence R A
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (oppositeGradingEquiv A L n).toModuleIso) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  simp only [toCochainComplex, DifferentialGradedModule.toCochainComplex_X,
    DifferentialGradedModule.toCochainComplex_d]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  ext x
  simp only [LinearMap.comp_apply]
  simp only [LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, CochainComplex.of_d]
  change (E.equivalence.functor.obj L).d
      ((oppositeGradingEquiv A L i x : (E.equivalence.functor.obj L).M)) =
    (E.underlying L).symm (L.d (x : L.M))
  have h := E.differential L ((E.underlying L).symm (x : L.M))
  simpa [E, oppositeGradingEquiv, gradedDifferential] using congrArg (E.underlying L).symm h

end DifferentialGraded.LeftModule
