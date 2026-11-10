module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Defs
public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction

/-!
# Left actions on a complex versus homomorphisms into its endomorphism algebra

Let `R` be a commutative ring, `A` a differential graded `R`-algebra, `M` a cochain complex of
`R`-modules and `E` an endomorphism differential graded algebra of `M`. A left differential graded
action of `A` on `M` is the same thing as a homomorphism of differential graded algebras
`A ⟶ E.algebra`: in one direction one extends the degreewise action by the direct-sum
decomposition of `A`, and in the other one restricts a homomorphism to the homogeneous pieces and
transports it along the identification of `E.algebra` with the cochains of `M`.

Everything here is proved for an *arbitrary* presentation `E` of the endomorphism algebra, so that
the canonical construction only has to be plugged in once; that is done in
`StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Basic`.

## Main definitions

* `CochainComplex.EndomorphismDGA.ofLeftAction`: the homomorphism `A ⟶ E.algebra` attached to a
  left action.
* `CochainComplex.EndomorphismDGA.toLeftAction`: the left action attached to a homomorphism.

## Main results

* `CochainComplex.EndomorphismDGA.ofLeftAction_cochainEquiv`: on a homogeneous element,
  `ofLeftAction` is given by the action of that element as a cochain. This is what makes the
  correspondence canonical.
* `CochainComplex.EndomorphismDGA.toAlgHom_toLeftAction`: `ofLeftAction` and `toLeftAction` are
  mutually inverse, in the form needed to build the equivalence.
* `DifferentialGradedAlgebra.LeftAction.ext_action` and
  `CochainComplex.EndomorphismDGA.hom_ext`: the two extensionality principles the equivalence
  needs.

## Implementation notes

A homomorphism out of `A` is determined by its restrictions to the homogeneous pieces, so
`toLinearMap` is assembled with `DirectSum.toModule` out of the decomposition of `A`, and all of
its multiplicativity statements are proved by `DirectSum.Decomposition.inductionOn`. The one
genuinely degreewise identity, `toLinearMap_apply_grading`, is therefore proved first and used
throughout.

## References

* [Stacks Project, Tag 0FQ3](https://stacks.math.columbia.edu/tag/0FQ3)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u

variable {R : Type u} [CommRing R]

namespace DifferentialGradedAlgebra.LeftAction

variable {M : CochainComplex (ModuleCat.{u} R) ℤ} {A : DifferentialGradedAlgebra R}

/-- A left differential graded action is determined by its values on homogeneous elements. -/
theorem ext_action {L L' : A.LeftAction M}
    (h : ∀ n (a : A.grading n), L.action n a = L'.action n a) : L = L' := by
  cases L with
  | mk f hone hmul hd =>
    cases L' with
    | mk g hone' hmul' hd' =>
      obtain rfl : f = g := funext fun n => LinearMap.ext (h n)
      rfl

end DifferentialGradedAlgebra.LeftAction

namespace CochainComplex.EndomorphismDGA

variable {M : CochainComplex (ModuleCat.{u} R) ℤ} (A : DifferentialGradedAlgebra R)
  (E : EndomorphismDGA M)

/-- A homomorphism of differential graded algebras is determined by its underlying algebra
homomorphism. -/
theorem hom_ext {B : DifferentialGradedAlgebra R} {φ ψ : A.Hom B}
    (h : φ.toAlgebraHom = ψ.toAlgebraHom) : φ = ψ := by
  cases φ with
  | mk φ hφd hφmap =>
    cases ψ with
    | mk ψ hψd hψmap =>
      dsimp at h
      cases h
      rfl

/-! ### From a left action to a homomorphism -/

variable (L : A.LeftAction M)

/-- The degree-`n` part of the homomorphism attached to a left action, obtained by transporting
the action along the identification of `E.algebra` with the cochains of `M`. -/
def componentMap (n : ℤ) : A.grading n →ₗ[R] E.algebra.grading n :=
  (E.cochainEquiv n).symm.toLinearMap.comp (L.action n)

/-- The `R`-linear map `A ⟶ E.algebra` attached to a left action, assembled from its degreewise
parts by the direct-sum decomposition of `A`. -/
noncomputable def toLinearMap : A.A →ₗ[R] E.algebra.A :=
  (DirectSum.toModule R ℤ E.algebra.A
      (fun n => (E.algebra.grading n).subtype.comp (componentMap A E L n))).comp
    (DirectSum.decomposeAlgEquiv A.grading).toLinearMap

/-- On a homogeneous element, the assembled linear map agrees with its degreewise part. -/
theorem toLinearMap_apply_grading (n : ℤ) (a : A.grading n) :
    toLinearMap A E L a = componentMap A E L n a := by
  change DirectSum.toModule R ℤ E.algebra.A
      (fun i => (E.algebra.grading i).subtype.comp (componentMap A E L i))
      (DirectSum.decompose A.grading (a : A.A)) = _
  rw [DirectSum.decompose_of_mem A.grading a.property,
    ← DirectSum.lof_eq_of (R := R) (ι := ℤ) (M := fun i => A.grading i) n a,
    DirectSum.toModule_lof]
  rfl

/-- Viewed as a cochain, the degreewise part of the homomorphism is the action. -/
private theorem cochainEquiv_componentMap (n : ℤ) (a : A.grading n) :
    E.cochainEquiv n (componentMap A E L n a) = L.action n a :=
  (E.cochainEquiv n).apply_symm_apply _

/-- The linear map attached to a left action is unital. -/
theorem toLinearMap_one : toLinearMap A E L 1 = 1 := by
  let a : A.grading 0 := ⟨1, SetLike.one_mem_graded A.grading⟩
  have h := toLinearMap_apply_grading A E L 0 a
  rw [show (a : A.A) = 1 from rfl] at h
  rw [h]
  have hg : componentMap A E L 0 a = ⟨1, SetLike.one_mem_graded E.algebra.grading⟩ := by
    apply (E.cochainEquiv 0).injective
    rw [cochainEquiv_componentMap, E.map_one]
    exact L.map_one
  exact congrArg Subtype.val hg

/-- The linear map attached to a left action is multiplicative. -/
theorem toLinearMap_mul (x y : A.A) :
    toLinearMap A E L (x * y) = toLinearMap A E L x * toLinearMap A E L y := by
  induction x using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp [toLinearMap]
  | homogeneous a =>
    rename_i i
    induction y using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp [toLinearMap]
    | homogeneous b =>
      rename_i j
      let ab : A.grading (i + j) :=
        ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩
      have ha := toLinearMap_apply_grading A E L i a
      have hb := toLinearMap_apply_grading A E L j b
      have hab := toLinearMap_apply_grading A E L (i + j) ab
      change toLinearMap A E L ((a : A.A) * (b : A.A)) = _ at hab
      rw [hab, ha, hb]
      have hmul : componentMap A E L (i + j) ab =
          ⟨(componentMap A E L i a : E.algebra.A) * (componentMap A E L j b : E.algebra.A),
            SetLike.mul_mem_graded (componentMap A E L i a).property
              (componentMap A E L j b).property⟩ := by
        apply (E.cochainEquiv (i + j)).injective
        rw [E.map_mul, cochainEquiv_componentMap, cochainEquiv_componentMap,
          cochainEquiv_componentMap]
        exact L.map_mul i j a b
      exact congrArg Subtype.val hmul
    | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz, mul_add]
  | add x z hx hz => rw [add_mul, map_add, map_add, hx, hz, add_mul]

/-- The `R`-algebra homomorphism `A ⟶ E.algebra` attached to a left action. -/
noncomputable def toAlgHom : A.A →ₐ[R] E.algebra.A :=
  AlgHom.ofLinearMap (toLinearMap A E L) (toLinearMap_one A E L) (toLinearMap_mul A E L)

/-- The algebra homomorphism attached to a left action preserves the grading. -/
theorem toAlgHom_mem_grading (n : ℤ) {x : A.A} (hx : x ∈ A.grading n) :
    toAlgHom A E L x ∈ E.algebra.grading n := by
  let a : A.grading n := ⟨x, hx⟩
  change toLinearMap A E L (a : A.A) ∈ E.algebra.grading n
  rw [toLinearMap_apply_grading A E L n a]
  exact (componentMap A E L n a).property

/-- The algebra homomorphism attached to a left action commutes with the differentials. -/
theorem toAlgHom_map_d (x : A.A) :
    toAlgHom A E L (A.d x) = E.algebra.d (toAlgHom A E L x) := by
  change toLinearMap A E L (A.d x) = E.algebra.d (toLinearMap A E L x)
  induction x using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | homogeneous a =>
    rename_i n
    let da : A.grading (n + 1) := ⟨A.d a, A.d_mem n a a.property⟩
    rw [toLinearMap_apply_grading A E L (n + 1) da, toLinearMap_apply_grading A E L n a]
    change (componentMap A E L (n + 1) da : E.algebra.A) =
      E.algebra.d (componentMap A E L n a : E.algebra.A)
    have hsub : componentMap A E L (n + 1) da =
        ⟨E.algebra.d (componentMap A E L n a),
          E.algebra.d_mem n (componentMap A E L n a) (componentMap A E L n a).property⟩ := by
      apply (E.cochainEquiv (n + 1)).injective
      rw [E.map_d, cochainEquiv_componentMap, cochainEquiv_componentMap]
      exact L.map_d n a
    exact congrArg Subtype.val hsub
  | add x y hx hy => simp only [A.d.map_add, map_add, hx, hy, E.algebra.d.map_add]

/-- The homomorphism of differential graded algebras `A ⟶ E.algebra` attached to a left
differential graded action of `A` on `M`. -/
noncomputable def ofLeftAction : A.Hom E.algebra where
  toAlgebraHom := toAlgHom A E L
  map_grading := fun n _ hx => toAlgHom_mem_grading A E L n hx
  map_d := fun x => toAlgHom_map_d A E L x

/-- On a homogeneous element, `ofLeftAction` is the action of that element as a cochain. -/
theorem ofLeftAction_cochainEquiv (n : ℤ) (a : A.grading n) :
    E.cochainEquiv n
        ⟨(ofLeftAction A E L).toAlgebraHom a,
          (ofLeftAction A E L).map_grading n a a.property⟩ = L.action n a := by
  have hsub : (⟨(ofLeftAction A E L).toAlgebraHom a,
      (ofLeftAction A E L).map_grading n a a.property⟩ : E.algebra.grading n) =
      componentMap A E L n a := Subtype.ext (toLinearMap_apply_grading A E L n a)
  rw [hsub]
  exact cochainEquiv_componentMap A E L n a

/-! ### From a homomorphism to a left action -/

/-- The restriction of a homomorphism of differential graded algebras to the degree-`n` parts. -/
def homComponentMap (φ : A.Hom E.algebra) (n : ℤ) :
    A.grading n →ₗ[R] E.algebra.grading n where
  toFun a := ⟨φ.toAlgebraHom (a : A.A), φ.map_grading n (a : A.A) a.property⟩
  map_add' a b := Subtype.ext (map_add φ.toAlgebraHom (a : A.A) (b : A.A))
  map_smul' r a := Subtype.ext (map_smul φ.toAlgebraHom r (a : A.A))

/-- The left differential graded action of `A` on `M` attached to a homomorphism of differential
graded algebras `A ⟶ E.algebra`. -/
noncomputable def toLeftAction (φ : A.Hom E.algebra) : A.LeftAction M := by
  refine ⟨fun n => (E.cochainEquiv n).toLinearMap.comp (homComponentMap A E φ n), ?_, ?_, ?_⟩
  · let oneA : A.grading 0 := ⟨1, SetLike.one_mem_graded A.grading⟩
    let oneE : E.algebra.grading 0 := ⟨1, SetLike.one_mem_graded E.algebra.grading⟩
    have hφ : homComponentMap A E φ 0 oneA = oneE :=
      Subtype.ext φ.toAlgebraHom.map_one
    change (E.cochainEquiv 0) (homComponentMap A E φ 0 oneA) = Cochain.ofHom (𝟙 M)
    rw [hφ, E.map_one]
  · intro n m a b
    let ab : A.grading (n + m) :=
      ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩
    let fa := homComponentMap A E φ n a
    let fb := homComponentMap A E φ m b
    let fab := homComponentMap A E φ (n + m) ab
    have hmul : fab =
        ⟨(fa : E.algebra.A) * (fb : E.algebra.A),
          SetLike.mul_mem_graded fa.property fb.property⟩ :=
      Subtype.ext (φ.toAlgebraHom.map_mul (a : A.A) (b : A.A))
    change E.cochainEquiv (n + m) fab = _
    rw [hmul, E.map_mul]
    rfl
  · intro n a
    let da : A.grading (n + 1) := ⟨A.d a, A.d_mem n a a.property⟩
    let fa := homComponentMap A E φ n a
    let fda := homComponentMap A E φ (n + 1) da
    have hd : fda = ⟨E.algebra.d fa, E.algebra.d_mem n fa fa.property⟩ :=
      Subtype.ext (φ.map_d a)
    change E.cochainEquiv (n + 1) fda = _
    rw [hd, E.map_d]
    rfl

/-- The degreewise part of the action attached to `φ` is the restriction of `φ`. -/
theorem componentMap_toLeftAction (φ : A.Hom E.algebra) (n : ℤ) (a : A.grading n) :
    componentMap A E (toLeftAction A E φ) n a = homComponentMap A E φ n a := by
  apply Subtype.ext
  simp [componentMap, toLeftAction]

/-- On a homogeneous element, `ofLeftAction` undoes `toLeftAction`. -/
theorem toAlgHom_toLeftAction_apply_grading (φ : A.Hom E.algebra) (n : ℤ) (a : A.grading n) :
    toAlgHom A E (toLeftAction A E φ) a = φ.toAlgebraHom a :=
  (toLinearMap_apply_grading A E (toLeftAction A E φ) n a).trans
    (congrArg Subtype.val (componentMap_toLeftAction A E φ n a))

/-- `ofLeftAction` is a left inverse of `toLeftAction`, at the level of algebra homomorphisms. -/
theorem toAlgHom_toLeftAction (φ : A.Hom E.algebra) :
    toAlgHom A E (toLeftAction A E φ) = φ.toAlgebraHom := by
  apply AlgHom.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | homogeneous a =>
    rename_i n
    exact toAlgHom_toLeftAction_apply_grading A E φ n a
  | add x y hx hy => simp [hx, hy]

end CochainComplex.EndomorphismDGA
