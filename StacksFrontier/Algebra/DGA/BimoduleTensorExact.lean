module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorShift
public import StacksFrontier.Algebra.DGA.Pretriangulated

/-!
# Tensoring with a bimodule is exact on homotopy categories

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let `N` be a
differential graded `(A, B)`-bimodule. The functor `M ↦ M ⊗_A N` on homotopy categories of
Tag 09LM commutes with the translation and carries distinguished triangles to distinguished
triangles, so it is an exact functor of triangulated categories.

## Main results

* `DifferentialGraded.Bimodule.tensorObj_hom_ext`: two homomorphisms out of `M ⊗_A N` that agree
  on pure tensors are equal.
* `DifferentialGraded.Bimodule.tensorCompFunctorCommShift`: tensoring with `N` commutes with the
  shift, through the comparison of Tag 0FQN.
* `DifferentialGraded.Bimodule.tensorConeTriangleIso`: tensoring with `N` carries the cone
  triangle of `f` to the cone triangle of `f ⊗_A N`.
* `DifferentialGraded.Bimodule.tensorQuotientLift_isTriangulated`: the induced functor on
  homotopy categories is triangulated.

## Implementation notes

*Everything is read off the universal property.* The value `M ⊗_A N` of the tensor functor is
specified by `DifferentialGraded.Bimodule.TensorDGFunctorData` and not by a presentation, so the
only available handle is the universal property. `tensorObj_hom_ext` turns its uniqueness half
into the extensionality principle used throughout: two homomorphisms out of `M ⊗_A N` agreeing
on pure tensors are equal. It applies to homomorphisms into *any* right differential graded
`B`-module, and that is what makes the two off-diagonal computations below available.

*The commutation with the shift is the sign-free comparison of Tag 0FQN.* The component of
`Functor.CommShift.commShiftIso` is the inverse of
`DifferentialGraded.Bimodule.tensorShiftIso`, and its three axioms are all proved by
extensionality on pure tensors: the comparison isomorphisms of
`DifferentialGradedModule.shiftMkCore` are the identity on underlying modules, so each side of
each axiom sends a pure tensor to the same pure tensor.

*The cone is compared through a degree `-1` homogeneous morphism.* The forward comparison
`(cone f) ⊗_A N ⟶ cone (f ⊗_A N)` is the lift of the balanced bilinear map
`(l, k) ⊗ y ↦ (l ⊗ y, k ⊗ y)`. Its inverse is assembled from the image of the inclusion of `L`
and the image of the *graded* section `k ↦ (0, k)` of the cone, which is a homogeneous morphism
of degree `-1` and not a homomorphism of differential graded modules. That the two composites
are the identity is proved by extensionality in both directions: the second off-diagonal
identity is an equality of degree `-1` homogeneous maps, which becomes an equality of
homomorphisms into the shift `(-1)` of the target, because the differential of a shift by `-1`
carries the sign `-1` and the defect of each of the two maps from being a chain map is the same.

*Universes are collapsed to one, inherited and not chosen here.*
`DifferentialGraded.Bimodule.TensorDGFunctorData` — and with it `tensorCompFunctor`,
`tensorHomotopyFunctor` and `tensorShiftIso` of Tags 09LM and 0FQN — is stated for
`DifferentialGradedAlgebra.{u, u} R` and `DifferentialGradedModule.{u, u, u}`, so this file is
too. The statement of Tag 09LR has independent universes for `R`, for `A`, for `B` and for the
modules; the narrowing comes down the chain from `TensorDGFunctorData` and is not decided here.

## References

* [Stacks Project, Tag 09LR](https://stacks.math.columbia.edu/tag/09LR)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R]
variable {A B : DifferentialGradedAlgebra.{u, u} R}

open DifferentialGradedModule

/-! ### Extensionality for homomorphisms out of a relative tensor product -/

/-- The value `M ⊗_A N` of the tensor functor, with its type read as a right differential graded
`B`-module rather than as an object of the differential graded category. The two are the same by
unfolding, but only this spelling lets the category notation `⟶` resolve. -/
noncomputable abbrev tensorObj (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A) :
    DifferentialGradedModule.{u, u, u} B :=
  (tensorDGFunctor N).functor.obj M

/-- The universal pure tensors into `M ⊗_A N`. -/
noncomputable abbrev tensorPure (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A) :
    BalancedBilinearMap M N (tensorObj N M) :=
  (tensorDGFunctor N).pure M

/-- A balanced bilinear map composed with a homomorphism of its target. -/
noncomputable def BalancedBilinearMap.postcomp {M : DifferentialGradedModule.{u, u, u} A}
    {N : Bimodule A B} {P Q : DifferentialGradedModule.{u, u, u} B}
    (t : BalancedBilinearMap M N P) (g : P ⟶ Q) : BalancedBilinearMap M N Q where
  toLinearMap := t.toLinearMap.compr₂ g.toFun
  map_grading p q x y := g.map_grading _ _ (t.map_grading p q x y)
  map_d p x y := by
    have hg (z : P.M) : g.toFun (P.d z) = Q.d (g.toFun z) := LinearMap.congr_fun g.map_d z
    change Q.d (g.toFun (t.toLinearMap x y)) =
      g.toFun (t.toLinearMap (M.d x) y) + (p.negOnePow : ℤ) • g.toFun (t.toLinearMap x _)
    rw [← hg, t.map_d p x y, map_add, map_zsmul]
  balance p q n x y a := congrArg g.toFun (t.balance p q n x y a)
  map_right x y b := by
    change g.toFun (t.toLinearMap x (MulOpposite.op b • y)) =
      MulOpposite.op b • g.toFun (t.toLinearMap x y)
    rw [t.map_right x y b, g.map_smul]

/-- **Extensionality.** Two homomorphisms out of `M ⊗_A N` that agree on the pure tensors are
equal: both are the unique lift of the balanced bilinear map obtained by composing the universal
pure tensors with either of them. -/
theorem tensorObj_hom_ext (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    {P : DifferentialGradedModule.{u, u, u} B}
    (g h : tensorObj N M ⟶ P)
    (H : ∀ (x : M.M) (y : N.rightModule.M),
      g.toFun ((tensorPure N M).toLinearMap x y) =
        h.toFun ((tensorPure N M).toLinearMap x y)) :
    g = h := by
  obtain ⟨_, _, huniq⟩ :=
    (tensorDGFunctor N).universal M P ((tensorPure N M).postcomp g)
  exact (huniq g fun _ _ => rfl).trans (huniq h fun x y => (H x y).symm).symm

/-- Equal homomorphisms of differential graded modules have equal underlying functions. -/
private theorem hom_toFun_congr {C : DifferentialGradedAlgebra.{u, u} R}
    {P Q : DifferentialGradedModule.{u, u, u} C} {g h : P ⟶ Q} (e : g = h) (x : P.M) :
    g.toFun x = h.toFun x :=
  e ▸ rfl

/-- The ordinary tensor functor on a homomorphism, evaluated at a pure tensor. -/
theorem tensorCompFunctor_map_pure (N : Bimodule A B)
    {M P : DifferentialGradedModule.{u, u, u} A} (g : M ⟶ P) (x : M.M) (y : N.rightModule.M) :
    ((tensorCompFunctor N).map g).toFun ((tensorPure N M).toLinearMap x y) =
      (tensorPure N P).toLinearMap (g.toFun x) y :=
  (tensorDGFunctor N).map_pure (cocycleOfHom A g).1 x y

/-! ### The tensor functor commutes with the shift -/

/-- The comparison `M[k] ⊗_A N ⟶ (M ⊗_A N)[k]`, the inverse of the sign-free isomorphism of
Tag 0FQN. -/
noncomputable def tensorShiftBack (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (k : ℤ) :
    tensorObj N (shift M k) ⟶ shift (tensorObj N M) k :=
  (tensorShiftIso N M k).1.inv

/-- The comparison `M[k] ⊗_A N ⟶ (M ⊗_A N)[k]` is the identity on pure tensors. -/
theorem tensorShiftBack_pure (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (k : ℤ) (x : M.M) (y : N.rightModule.M) :
    (tensorShiftBack N M k).toFun
        ((tensorPure N (shift M k)).toLinearMap x y) =
      (tensorPure N M).toLinearMap x y := by
  rw [← (tensorShiftIso N M k).2 x y]
  exact hom_toFun_congr (tensorShiftIso N M k).1.hom_inv_id _

/-- The naturality square of the comparison of Tag 0FQN, with both sides written as
homomorphisms out of `M[k] ⊗_A N`. -/
theorem tensorShiftBack_naturality (N : Bimodule A B)
    {M P : DifferentialGradedModule.{u, u, u} A} (g : M ⟶ P) (k : ℤ) :
    ((tensorCompFunctor N).map (shiftMap g k) ≫ tensorShiftBack N P k :
      tensorObj N (shift M k) ⟶ shift (tensorObj N P) k) =
      tensorShiftBack N M k ≫ shiftMap ((tensorCompFunctor N).map g) k := by
  refine tensorObj_hom_ext N (shift M k) _ _ fun x y => ?_
  show (tensorShiftBack N P k).toFun
      (((tensorCompFunctor N).map (shiftMap g k)).toFun
        ((tensorPure N (shift M k)).toLinearMap x y)) =
    ((tensorCompFunctor N).map g).toFun
      ((tensorShiftBack N M k).toFun ((tensorPure N (shift M k)).toLinearMap x y))
  rw [tensorCompFunctor_map_pure, tensorShiftBack_pure, tensorShiftBack_pure,
    tensorCompFunctor_map_pure]
  rfl

/-- Tensoring with `N` commutes with the shift: the comparison is the one of Tag 0FQN. -/
noncomputable def tensorCompCommShiftIso (N : Bimodule A B) (k : ℤ) :
    CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, u, u} A) k ⋙ tensorCompFunctor N ≅
      tensorCompFunctor N ⋙
        CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, u, u} B) k :=
  NatIso.ofComponents (fun M => (tensorShiftIso N M k).1.symm)
    (fun g => tensorShiftBack_naturality N g k)

/-- The component at `M` of the shift isomorphism of the tensor functor is the comparison of
Tag 0FQN. -/
@[simp] theorem tensorCompCommShiftIso_hom_app (N : Bimodule A B) (k : ℤ)
    (M : DifferentialGradedModule.{u, u, u} A) :
    (tensorCompCommShiftIso N k).hom.app M = tensorShiftBack N M k := rfl

/-- The comparison for the shift by `0` agrees with the one built from
`CategoryTheory.shiftFunctorZero`: both are the identity on pure tensors. -/
theorem tensorShiftBack_zero (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A) :
    (tensorShiftBack N M 0 : tensorObj N (shift M 0) ⟶ shift (tensorObj N M) 0) =
      (tensorCompFunctor N).map
          ((CategoryTheory.shiftFunctorZero
            (DifferentialGradedModule.{u, u, u} A) ℤ).hom.app M) ≫
        (CategoryTheory.shiftFunctorZero
          (DifferentialGradedModule.{u, u, u} B) ℤ).inv.app (tensorObj N M) := by
  refine tensorObj_hom_ext N (shift M 0) _ _ fun x y => ?_
  have h : ((tensorCompFunctor N).map
        ((CategoryTheory.shiftFunctorZero
          (DifferentialGradedModule.{u, u, u} A) ℤ).hom.app M)).toFun
      ((tensorPure N (shift M 0)).toLinearMap x y) = (tensorPure N M).toLinearMap x y :=
    tensorCompFunctor_map_pure N _ x y
  exact (tensorShiftBack_pure N M 0 x y).trans h.symm

/-- The comparison for the shift by `a + b` is the composite of the comparisons for `a` and for
`b`: both are the identity on pure tensors. -/
theorem tensorShiftBack_add (N : Bimodule A B) (M : DifferentialGradedModule.{u, u, u} A)
    (a b : ℤ) :
    (tensorShiftBack N M (a + b) :
        tensorObj N (shift M (a + b)) ⟶ shift (tensorObj N M) (a + b)) =
      (tensorCompFunctor N).map
          ((CategoryTheory.shiftFunctorAdd
            (DifferentialGradedModule.{u, u, u} A) a b).hom.app M) ≫
        tensorShiftBack N (shift M a) b ≫
          shiftMap (tensorShiftBack N M a) b ≫
            (CategoryTheory.shiftFunctorAdd
              (DifferentialGradedModule.{u, u, u} B) a b).inv.app (tensorObj N M) := by
  refine tensorObj_hom_ext N (shift M (a + b)) _ _ fun x y => ?_
  have h : ((tensorCompFunctor N).map
        ((CategoryTheory.shiftFunctorAdd
          (DifferentialGradedModule.{u, u, u} A) a b).hom.app M)).toFun
      ((tensorPure N (shift M (a + b))).toLinearMap x y) =
      (tensorPure N (shift (shift M a) b)).toLinearMap x y :=
    tensorCompFunctor_map_pure N _ x y
  have h' : (tensorShiftBack N M a).toFun
      ((tensorShiftBack N (shift M a) b).toFun
        ((tensorPure N (shift (shift M a) b)).toLinearMap x y)) =
      (tensorPure N M).toLinearMap x y := by
    rw [tensorShiftBack_pure, tensorShiftBack_pure]
  exact (tensorShiftBack_pure N M (a + b) x y).trans
    (h'.symm.trans (congrArg
      (fun z : (tensorObj N (shift (shift M a) b)).M =>
        (tensorShiftBack N M a).toFun ((tensorShiftBack N (shift M a) b).toFun z)) h.symm))

/-- The ordinary tensor functor, as a functor commuting with the shift by `ℤ`, with the shift
isomorphism `tensorCompCommShiftIso`.

Deliberately not an instance. `DifferentialGraded.Bimodule.tensorCompFunctorCommShift'`
(`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensorTriangulated.lean`) is a
`CommShift ℤ` on the same functor built instead from `tensorCompCommShiftIso'`, and 54 modules
have both files in their import closure. `CommShift` carries data, so two instances there would
leave which shift isomorphism a proof sees to the order of instance resolution. The two
isomorphisms are expected to agree, but that is unproved, so the one declared downstream is the
instance and this one is available by name for the proofs of this file. -/
@[instance_reducible]
noncomputable def tensorCompFunctorCommShift (N : Bimodule A B) :
    (tensorCompFunctor N).CommShift ℤ where
  commShiftIso := tensorCompCommShiftIso N
  commShiftIso_zero := by
    ext M
    rw [tensorCompCommShiftIso_hom_app, Functor.CommShift.isoZero_hom_app]
    exact tensorShiftBack_zero N M
  commShiftIso_add a b := by
    ext M
    rw [tensorCompCommShiftIso_hom_app, Functor.CommShift.isoAdd_hom_app,
      tensorCompCommShiftIso_hom_app, tensorCompCommShiftIso_hom_app]
    exact tensorShiftBack_add N M a b

-- an instance in this file only: see the docstring above for why it is not a global one
attribute [local instance] tensorCompFunctorCommShift

/-- The shift isomorphism of the tensor functor, for the local `CommShift` instance of this file,
is `tensorCompCommShiftIso`. -/
@[simp] theorem commShiftIso_tensorCompFunctor (N : Bimodule A B) (k : ℤ) :
    Functor.commShiftIso (tensorCompFunctor N) k = tensorCompCommShiftIso N k := rfl

/-! ### Tensoring commutes with the cone -/

/-- The tensor functor on a homomorphism, with its type read as a homomorphism of right
differential graded `B`-modules. -/
noncomputable abbrev tensorModuleMap (N : Bimodule A B) {K L : DifferentialGradedModule.{u, u, u} A}
    (f : K ⟶ L) : tensorObj N K ⟶ tensorObj N L :=
  (tensorCompFunctor N).map f

section Cone

variable {K L : DifferentialGradedModule.{u, u, u} A}

/-- The bilinear map `(l, k) ⊗ y ↦ (l ⊗ y, k ⊗ y)` out of the cone, assembled from the two
direct-sum injections of the cone of the tensored morphism. -/
noncomputable def coneBilinearMap (N : Bimodule A B) (f : K ⟶ L) :
    (coneObject f).M →ₗ[R] N.rightModule.M →ₗ[R] (coneObject (tensorModuleMap N f)).M :=
  ((tensorPure N L).toLinearMap.comp (LinearMap.fst R L.M K.M)).compr₂
      (LinearMap.inl R (tensorObj N L).M (tensorObj N K).M) +
    ((tensorPure N K).toLinearMap.comp (LinearMap.snd R L.M K.M)).compr₂
      (LinearMap.inr R (tensorObj N L).M (tensorObj N K).M)

/-- The bilinear map out of the cone, evaluated at `z` and `y`: its two coordinates are the pure
tensors of the two coordinates of `z` with `y`. -/
@[simp] theorem coneBilinearMap_apply (N : Bimodule A B) (f : K ⟶ L)
    (z : (coneObject f).M) (y : N.rightModule.M) :
    coneBilinearMap N f z y =
      ((tensorPure N L).toLinearMap z.1 y, (tensorPure N K).toLinearMap z.2 y) := by
  show ((tensorPure N L).toLinearMap z.1 y, (0 : (tensorObj N K).M)) +
    ((0 : (tensorObj N L).M), (tensorPure N K).toLinearMap z.2 y) = _
  simp

/-- The balanced bilinear map out of the cone: the degrees work out because the degree `n` part
of the cone has its `K`-coordinate in degree `n + 1`, and the two signs in the Leibniz rule for
the cone differential are the two signs of the Leibniz rules of the two coordinates. -/
noncomputable def tensorConeBilinear (N : Bimodule A B) (f : K ⟶ L) :
    BalancedBilinearMap (coneObject f) N (coneObject (tensorModuleMap N f)) where
  toLinearMap := coneBilinearMap N f
  map_grading p q x y := by
    obtain ⟨hx1, hx2⟩ := (coneGrading_mem p x.val).mp x.2
    refine (coneGrading_mem (p + q) _).mpr ?_
    rw [coneBilinearMap_apply]
    refine ⟨(tensorPure N L).map_grading p q ⟨x.val.1, hx1⟩ y, ?_⟩
    have h := (tensorPure N K).map_grading (p + 1) q ⟨x.val.2, hx2⟩ y
    rwa [show p + q + 1 = p + 1 + q by omega]
  map_d p x y := by
    obtain ⟨hx1, hx2⟩ := (coneGrading_mem p x.val).mp x.2
    have hL : (tensorObj N L).d ((tensorPure N L).toLinearMap x.val.1 y) =
        (tensorPure N L).toLinearMap (L.d x.val.1) y +
          ((p.negOnePow : ℤ)) •
            (tensorPure N L).toLinearMap x.val.1 (N.rightModule.d y) :=
      (tensorPure N L).map_d p ⟨x.val.1, hx1⟩ y
    have hK : (tensorObj N K).d ((tensorPure N K).toLinearMap x.val.2 y) =
        (tensorPure N K).toLinearMap (K.d x.val.2) y +
          (((p + 1).negOnePow : ℤ)) •
            (tensorPure N K).toLinearMap x.val.2 (N.rightModule.d y) :=
      (tensorPure N K).map_d (p + 1) ⟨x.val.2, hx2⟩ y
    have hf : (tensorModuleMap N f).toFun ((tensorPure N K).toLinearMap x.val.2 y) =
        (tensorPure N L).toLinearMap (f.toFun x.val.2) y :=
      tensorCompFunctor_map_pure N f x.val.2 y
    have hsign : (((p + 1).negOnePow : ℤ)) = -((p.negOnePow : ℤ)) := by
      rw [Int.negOnePow_succ]; simp
    change (coneObject (tensorModuleMap N f)).d (coneBilinearMap N f x.val y) =
      coneBilinearMap N f ((coneObject f).d x.val) y +
        ((p.negOnePow : ℤ)) • coneBilinearMap N f x.val (N.rightModule.d y)
    rw [coneBilinearMap_apply, coneBilinearMap_apply, coneBilinearMap_apply]
    refine Prod.ext ?_ ?_
    · change (tensorObj N L).d ((tensorPure N L).toLinearMap x.val.1 y) +
        (tensorModuleMap N f).toFun ((tensorPure N K).toLinearMap x.val.2 y) =
        (tensorPure N L).toLinearMap (L.d x.val.1 + f.toFun x.val.2) y +
          ((p.negOnePow : ℤ)) • (tensorPure N L).toLinearMap x.val.1 (N.rightModule.d y)
      rw [hL, hf, map_add, LinearMap.add_apply]
      abel
    · have hz : ((-(p.negOnePow : ℤ))) •
          (tensorPure N K).toLinearMap x.val.2 (N.rightModule.d y) =
          -(((p.negOnePow : ℤ)) •
            (tensorPure N K).toLinearMap x.val.2 (N.rightModule.d y)) := by
        simp
      change -((tensorObj N K).d ((tensorPure N K).toLinearMap x.val.2 y)) =
        (tensorPure N K).toLinearMap (-(K.d x.val.2)) y +
          ((p.negOnePow : ℤ)) • (tensorPure N K).toLinearMap x.val.2 (N.rightModule.d y)
      rw [hK, hsign, hz, map_neg, LinearMap.neg_apply]
      abel
  balance p q n x y a := by
    obtain ⟨hx1, hx2⟩ := (coneGrading_mem p x.val).mp x.2
    have hL := (tensorPure N L).balance p q n ⟨x.val.1, hx1⟩ y a
    have hK := (tensorPure N K).balance (p + 1) q n ⟨x.val.2, hx2⟩ y a
    change coneBilinearMap N f (MulOpposite.op (a : A.A) • x.val) y =
      coneBilinearMap N f x.val _
    rw [coneBilinearMap_apply, coneBilinearMap_apply]
    exact Prod.ext hL hK
  map_right z y b := by
    rw [coneBilinearMap_apply, coneBilinearMap_apply]
    exact Prod.ext ((tensorPure N L).map_right z.1 y b) ((tensorPure N K).map_right z.2 y b)

/-- The comparison `(cone f) ⊗_A N ⟶ cone (f ⊗_A N)`. -/
noncomputable def tensorConeFwd (N : Bimodule A B) (f : K ⟶ L) :
    tensorObj N (coneObject f) ⟶ coneObject (tensorModuleMap N f) :=
  ((tensorDGFunctor N).universal (coneObject f) (coneObject (tensorModuleMap N f))
    (tensorConeBilinear N f)).choose

/-- The forward cone comparison on a pure tensor: `(l, k) ⊗ y ↦ (l ⊗ y, k ⊗ y)`. -/
theorem tensorConeFwd_pure (N : Bimodule A B) (f : K ⟶ L) (z : (coneObject f).M)
    (y : N.rightModule.M) :
    (tensorConeFwd N f).toFun ((tensorPure N (coneObject f)).toLinearMap z y) =
      ((tensorPure N L).toLinearMap z.1 y, (tensorPure N K).toLinearMap z.2 y) :=
  (((tensorDGFunctor N).universal (coneObject f) (coneObject (tensorModuleMap N f))
    (tensorConeBilinear N f)).choose_spec.1 z y).trans (coneBilinearMap_apply N f z y)

/-- The graded section `k ↦ (0, k)` of the cone, a homogeneous morphism of degree `-1`. It is
*not* a homomorphism of differential graded modules; its differential in the Hom-complex is
computed by `coneSection_d`. -/
def coneSection (f : K ⟶ L) : (dgCategory.{u, u, u} A).Hom K (coneObject f) (-1) :=
  ⟨LinearMap.inr R L.M K.M, by
    refine ⟨?_, ?_⟩
    · intro i x hx
      refine (coneGrading_mem (i + -1) ((0 : L.M), x)).mpr
        ⟨(L.grading (i + -1)).zero_mem, ?_⟩
      rwa [show i + -1 + 1 = i by omega]
    · intro a x
      change ((0 : L.M), MulOpposite.op a • x) =
        ((MulOpposite.op a • (0 : L.M)), MulOpposite.op a • x)
      rw [smul_zero]⟩

/-- The graded sign in degree `-1` is `-1`. -/
private theorem gradedSign_neg_one : DifferentialGraded.gradedSign R (-1 : ℤ) = -1 := by
  simp [DifferentialGraded.gradedSign]

/-- The graded section of the cone sends `k` to `(0, k)`. -/
@[simp] theorem coneSection_val (f : K ⟶ L) (x : K.M) :
    (coneSection f).1 x = ((0 : L.M), x) := rfl

/-- The differential of the graded section of the cone, in the Hom-complex of the differential
graded category: it is the inclusion of `L` precomposed with `f`. The sign `(-1)` of degree `-1`
turns the difference in the Hom-complex differential into a sum, and the `K`-coordinates then
cancel. -/
theorem coneSection_d (f : K ⟶ L) :
    (dgCategory.{u, u, u} A).d (coneSection f) =
      (dgCategory.{u, u, u} A).comp (show (0 : ℤ) + 0 = -1 + 1 by norm_num)
        (cocycleOfHom A (coneIncl f)).1 (cocycleOfHom A f).1 := by
  apply Subtype.ext
  rw [dgCategory_d_val, dgCategory_comp_val]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, gradedSign_neg_one, neg_smul, one_smul, sub_neg_eq_add]
  show (coneD f ((0 : L.M), x)) + ((0 : L.M), K.d x) = ((f.toFun x), (0 : K.M))
  rw [coneD_apply]
  refine Prod.ext ?_ ?_
  · show L.d (0 : L.M) + f.toFun x + (0 : L.M) = f.toFun x
    rw [map_zero, zero_add, add_zero]
  · show -K.d x + K.d x = (0 : K.M)
    rw [neg_add_cancel]

/-- The image under the tensor functor of the graded section of the cone, as a linear map. -/
noncomputable def tensorConeSectionMap (N : Bimodule A B) (f : K ⟶ L) :
    (tensorObj N K).M →ₗ[R] (tensorObj N (coneObject f)).M :=
  ((tensorDGFunctor N).functor.map (coneSection f)).1

/-- The image of the graded section of the cone on a pure tensor: `k ⊗ y ↦ (0, k) ⊗ y`. -/
theorem tensorConeSectionMap_pure (N : Bimodule A B) (f : K ⟶ L) (x : K.M)
    (y : N.rightModule.M) :
    tensorConeSectionMap N f ((tensorPure N K).toLinearMap x y) =
      (tensorPure N (coneObject f)).toLinearMap ((0 : L.M), x) y :=
  (tensorDGFunctor N).map_pure (coneSection f) x y

/-- The image of the graded section of the cone lowers degrees by one. -/
theorem tensorConeSectionMap_grading (N : Bimodule A B) (f : K ⟶ L) (i : ℤ)
    (z : (tensorObj N K).M) (hz : z ∈ (tensorObj N K).grading i) :
    tensorConeSectionMap N f z ∈ (tensorObj N (coneObject f)).grading (i + -1) :=
  ((tensorDGFunctor N).functor.map (coneSection f)).2.1 i z hz

/-- The image of the graded section of the cone is compatible with the right action of `B`. -/
theorem tensorConeSectionMap_smul (N : Bimodule A B) (f : K ⟶ L) (b : B.A)
    (z : (tensorObj N K).M) :
    tensorConeSectionMap N f (MulOpposite.op b • z) =
      MulOpposite.op b • tensorConeSectionMap N f z :=
  ((tensorDGFunctor N).functor.map (coneSection f)).2.2 b z

/-- The defect of the image of the graded section from being a chain map: it is the composite of
the tensored morphism with the tensored inclusion of `L`. This is the image under the tensor
functor of `coneSection_d`, and it is the only place where compatibility of the tensor functor
with the Hom-complex differential is used. -/
theorem tensorConeSectionMap_d (N : Bimodule A B) (f : K ⟶ L) (v : (tensorObj N K).M) :
    (tensorObj N (coneObject f)).d (tensorConeSectionMap N f v) +
        tensorConeSectionMap N f ((tensorObj N K).d v) =
      (tensorModuleMap N (coneIncl f)).toFun ((tensorModuleMap N f).toFun v) := by
  have hd := (tensorDGFunctor N).functor.map_d (coneSection f)
  have hc := congrArg (tensorDGFunctor N).functor.map (coneSection_d f)
  have hcomp := (tensorDGFunctor N).functor.map_comp
    (show (0 : ℤ) + 0 = -1 + 1 by norm_num)
    (cocycleOfHom A (coneIncl f)).1 (cocycleOfHom A f).1
  have key : ((dgCategory.{u, u, u} B).d
      ((tensorDGFunctor N).functor.map (coneSection f))).1 =
      ((tensorDGFunctor N).functor.map (cocycleOfHom A (coneIncl f)).1).1 ∘ₗ
        ((tensorDGFunctor N).functor.map (cocycleOfHom A f).1).1 := by
    rw [← hd, hc, hcomp, dgCategory_comp_val]
  have h := LinearMap.congr_fun key v
  rw [dgCategory_d_val, gradedSign_neg_one] at h
  simp only [LinearMap.add_apply, LinearMap.comp_apply, neg_smul, one_smul,
    sub_neg_eq_add] at h
  exact h

/-- The comparison `cone (f ⊗_A N) ⟶ (cone f) ⊗_A N`, built from the tensored inclusion of `L`
and the image of the graded section. -/
noncomputable def tensorConeBwd (N : Bimodule A B) (f : K ⟶ L) :
    coneObject (tensorModuleMap N f) ⟶ tensorObj N (coneObject f) where
  toFun := (tensorModuleMap N (coneIncl f)).toFun.comp
      (LinearMap.fst R (tensorObj N L).M (tensorObj N K).M) +
    (tensorConeSectionMap N f).comp
      (LinearMap.snd R (tensorObj N L).M (tensorObj N K).M)
  map_smul w b := by
    change (tensorModuleMap N (coneIncl f)).toFun (MulOpposite.op b • w.1) +
        tensorConeSectionMap N f (MulOpposite.op b • w.2) =
      MulOpposite.op b •
        ((tensorModuleMap N (coneIncl f)).toFun w.1 + tensorConeSectionMap N f w.2)
    rw [(tensorModuleMap N (coneIncl f)).map_smul, tensorConeSectionMap_smul, smul_add]
  map_grading n w hw := by
    obtain ⟨hw1, hw2⟩ := (coneGrading_mem n w).mp hw
    refine (tensorObj N (coneObject f)).grading n |>.add_mem
      ((tensorModuleMap N (coneIncl f)).map_grading n w.1 hw1) ?_
    have h := tensorConeSectionMap_grading N f (n + 1) w.2 hw2
    rwa [show n + 1 + -1 = n by omega] at h
  map_d := by
    refine LinearMap.ext fun w => ?_
    have hincl : (tensorModuleMap N (coneIncl f)).toFun ((tensorObj N L).d w.1) =
        (tensorObj N (coneObject f)).d
          ((tensorModuleMap N (coneIncl f)).toFun w.1) :=
      LinearMap.congr_fun (tensorModuleMap N (coneIncl f)).map_d w.1
    have hsec := tensorConeSectionMap_d N f w.2
    change (tensorModuleMap N (coneIncl f)).toFun
          ((tensorObj N L).d w.1 + (tensorModuleMap N f).toFun w.2) +
        tensorConeSectionMap N f (-(tensorObj N K).d w.2) =
      (tensorObj N (coneObject f)).d
        ((tensorModuleMap N (coneIncl f)).toFun w.1 + tensorConeSectionMap N f w.2)
    simp only [map_add, map_neg]
    rw [hincl, ← hsec]
    abel

/-- The backward cone comparison sends `(u, v)` to the tensored inclusion of `u` plus the image
of `v` under the graded section. -/
theorem tensorConeBwd_apply (N : Bimodule A B) (f : K ⟶ L)
    (w : (coneObject (tensorModuleMap N f)).M) :
    (tensorConeBwd N f).toFun w =
      (tensorModuleMap N (coneIncl f)).toFun w.1 + tensorConeSectionMap N f w.2 := rfl

/-- The forward comparison undoes the tensored inclusion of `L`: on the first coordinate the two
comparisons are the inclusion of the cone of the tensored morphism. -/
theorem tensorConeFwd_comp_incl (N : Bimodule A B) (f : K ⟶ L) :
    ((tensorModuleMap N (coneIncl f)) ≫ tensorConeFwd N f :
        tensorObj N L ⟶ coneObject (tensorModuleMap N f)) =
      coneIncl (tensorModuleMap N f) := by
  refine tensorObj_hom_ext N L _ _ fun x y => ?_
  have h : (tensorModuleMap N (coneIncl f)).toFun ((tensorPure N L).toLinearMap x y) =
      (tensorPure N (coneObject f)).toLinearMap (x, (0 : K.M)) y :=
    tensorCompFunctor_map_pure N (coneIncl f) x y
  show (tensorConeFwd N f).toFun
      ((tensorModuleMap N (coneIncl f)).toFun ((tensorPure N L).toLinearMap x y)) =
    ((tensorPure N L).toLinearMap x y, (0 : (tensorObj N K).M))
  rw [h, tensorConeFwd_pure]
  exact Prod.ext rfl (by simp)

/-- The forward comparison on the image of the tensored inclusion of `L`. -/
theorem tensorConeFwd_incl_apply (N : Bimodule A B) (f : K ⟶ L) (u : (tensorObj N L).M) :
    (tensorConeFwd N f).toFun ((tensorModuleMap N (coneIncl f)).toFun u) =
      (coneIncl (tensorModuleMap N f)).toFun u :=
  hom_toFun_congr (tensorConeFwd_comp_incl N f) u

/-- The second direct-sum injection into the cone of the tensored morphism, with its type read
as a map into the cone. -/
noncomputable def tensorConeInr (N : Bimodule A B) (f : K ⟶ L) :
    (tensorObj N K).M →ₗ[R] (coneObject (tensorModuleMap N f)).M :=
  LinearMap.inr R (tensorObj N L).M (tensorObj N K).M

/-- The second direct-sum injection into the cone of the tensored morphism sends `v` to
`(0, v)`. -/
@[simp] theorem tensorConeInr_apply (N : Bimodule A B) (f : K ⟶ L) (v : (tensorObj N K).M) :
    tensorConeInr N f v =
      (((0 : (tensorObj N L).M), v) : (coneObject (tensorModuleMap N f)).M) := rfl

/-- The defect morphism: the difference between the forward comparison composed with the image
of the graded section and the second direct-sum injection. Neither of the two maps is a chain
map, and their failures are the same, so the difference is a homomorphism into the shift by
`-1` — whose differential carries the sign `-1`. -/
noncomputable def tensorConeDefect (N : Bimodule A B) (f : K ⟶ L) :
    tensorObj N K ⟶ shift (coneObject (tensorModuleMap N f)) (-1) where
  toFun := (tensorConeFwd N f).toFun.comp (tensorConeSectionMap N f) - tensorConeInr N f
  map_smul v b := by
    change (tensorConeFwd N f).toFun (tensorConeSectionMap N f (MulOpposite.op b • v)) -
        tensorConeInr N f (MulOpposite.op b • v) =
      MulOpposite.op b •
        ((tensorConeFwd N f).toFun (tensorConeSectionMap N f v) - tensorConeInr N f v)
    rw [tensorConeSectionMap_smul, (tensorConeFwd N f).map_smul, smul_sub,
      tensorConeInr_apply, tensorConeInr_apply]
    congr 1
    change (((0 : (tensorObj N L).M), MulOpposite.op b • v) :
        (coneObject (tensorModuleMap N f)).M) =
      ((MulOpposite.op b • (0 : (tensorObj N L).M), MulOpposite.op b • v) :
        (coneObject (tensorModuleMap N f)).M)
    rw [smul_zero]
  map_grading n v hv := by
    refine Submodule.sub_mem _ ((tensorConeFwd N f).map_grading (n + -1) _
      (tensorConeSectionMap_grading N f n v hv)) ?_
    rw [tensorConeInr_apply]
    refine (coneGrading_mem (n + -1) _).mpr
      ⟨((tensorObj N L).grading (n + -1)).zero_mem, ?_⟩
    rwa [show n + -1 + 1 = n by omega]
  map_d := by
    refine LinearMap.ext fun v => ?_
    have hA (z : (tensorObj N (coneObject f)).M) :
        (tensorConeFwd N f).toFun ((tensorObj N (coneObject f)).d z) =
          (coneObject (tensorModuleMap N f)).d ((tensorConeFwd N f).toFun z) :=
      LinearMap.congr_fun (tensorConeFwd N f).map_d z
    have hsec := tensorConeSectionMap_d N f v
    have hsplit : (tensorObj N (coneObject f)).d (tensorConeSectionMap N f v) =
        (tensorModuleMap N (coneIncl f)).toFun ((tensorModuleMap N f).toFun v) -
          tensorConeSectionMap N f ((tensorObj N K).d v) := by
      rw [← hsec]; abel
    have h1 : (coneObject (tensorModuleMap N f)).d
        ((tensorConeFwd N f).toFun (tensorConeSectionMap N f v)) =
        (coneIncl (tensorModuleMap N f)).toFun ((tensorModuleMap N f).toFun v) -
          (tensorConeFwd N f).toFun
            (tensorConeSectionMap N f ((tensorObj N K).d v)) := by
      rw [← hA, hsplit, map_sub, tensorConeFwd_incl_apply]
    have hinr : (coneObject (tensorModuleMap N f)).d (tensorConeInr N f v) =
        (coneIncl (tensorModuleMap N f)).toFun ((tensorModuleMap N f).toFun v) -
          tensorConeInr N f ((tensorObj N K).d v) := by
      refine Prod.ext ?_ ?_
      · change (tensorObj N L).d (0 : (tensorObj N L).M) + (tensorModuleMap N f).toFun v =
          (tensorModuleMap N f).toFun v - (0 : (tensorObj N L).M)
        rw [map_zero, zero_add, sub_zero]
      · change -(tensorObj N K).d v =
          (0 : (tensorObj N K).M) - (tensorObj N K).d v
        rw [zero_sub]
    have hneg : (((-1 : ℤ).negOnePow : ℤ)) = -1 := by
      rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, Int.negOnePow_neg, Int.negOnePow_one]
      rfl
    change (tensorConeFwd N f).toFun
          (tensorConeSectionMap N f ((tensorObj N K).d v)) -
        tensorConeInr N f ((tensorObj N K).d v) =
      (((-1 : ℤ).negOnePow : ℤ)) •
        (coneObject (tensorModuleMap N f)).d
          ((tensorConeFwd N f).toFun (tensorConeSectionMap N f v) - tensorConeInr N f v)
    rw [hneg, neg_one_zsmul, map_sub, h1, hinr]
    abel

/-- The forward comparison undoes the image of the graded section: the defect vanishes, because
on a pure tensor both of its summands are the same element of the cone. -/
theorem tensorConeFwd_section_apply (N : Bimodule A B) (f : K ⟶ L) (v : (tensorObj N K).M) :
    (tensorConeFwd N f).toFun (tensorConeSectionMap N f v) = tensorConeInr N f v := by
  have hz : tensorConeDefect N f =
      (0 : tensorObj N K ⟶ shift (coneObject (tensorModuleMap N f)) (-1)) := by
    refine tensorObj_hom_ext N K _ _ fun x y => ?_
    have hpure : (tensorConeFwd N f).toFun
        (tensorConeSectionMap N f ((tensorPure N K).toLinearMap x y)) =
        tensorConeInr N f ((tensorPure N K).toLinearMap x y) := by
      rw [tensorConeSectionMap_pure, tensorConeFwd_pure, tensorConeInr_apply]
      exact Prod.ext (by simp) rfl
    show (tensorConeFwd N f).toFun
        (tensorConeSectionMap N f ((tensorPure N K).toLinearMap x y)) -
        tensorConeInr N f ((tensorPure N K).toLinearMap x y) =
      (0 : tensorObj N K ⟶ shift (coneObject (tensorModuleMap N f)) (-1)).toFun
        ((tensorPure N K).toLinearMap x y)
    rw [hpure, sub_self, Hom.hom_zero_toFun]
    rfl
  have h := hom_toFun_congr hz v
  change (tensorConeFwd N f).toFun (tensorConeSectionMap N f v) -
      tensorConeInr N f v = 0 at h
  exact sub_eq_zero.mp h

/-- The two comparisons are mutually inverse on the cone of the tensored morphism. -/
theorem tensorConeBwd_fwd (N : Bimodule A B) (f : K ⟶ L) :
    (tensorConeBwd N f ≫ tensorConeFwd N f) = 𝟙 (coneObject (tensorModuleMap N f)) := by
  apply DifferentialGradedModule.Hom.ext
  refine LinearMap.ext fun w => ?_
  show (tensorConeFwd N f).toFun
      ((tensorModuleMap N (coneIncl f)).toFun w.1 + tensorConeSectionMap N f w.2) = w
  rw [map_add, tensorConeFwd_incl_apply, tensorConeFwd_section_apply, tensorConeInr_apply]
  refine Prod.ext ?_ ?_
  · show w.1 + 0 = w.1
    rw [add_zero]
  · show (0 : (tensorObj N K).M) + w.2 = w.2
    rw [zero_add]

/-- The two comparisons are mutually inverse on the tensor product of the cone. -/
theorem tensorConeFwd_bwd (N : Bimodule A B) (f : K ⟶ L) :
    (tensorConeFwd N f ≫ tensorConeBwd N f) = 𝟙 (tensorObj N (coneObject f)) := by
  refine tensorObj_hom_ext N (coneObject f) _ _ fun z y => ?_
  have hz : ((z.1, (0 : K.M)) + ((0 : L.M), z.2) : (coneObject f).M) = z := by
    refine Prod.ext ?_ ?_
    · show z.1 + 0 = z.1
      rw [add_zero]
    · show (0 : K.M) + z.2 = z.2
      rw [zero_add]
  have hincl : (tensorModuleMap N (coneIncl f)).toFun ((tensorPure N L).toLinearMap z.1 y) =
      (tensorPure N (coneObject f)).toLinearMap ((z.1, (0 : K.M)) : (coneObject f).M) y :=
    tensorCompFunctor_map_pure N (coneIncl f) z.1 y
  show (tensorConeBwd N f).toFun
      ((tensorConeFwd N f).toFun ((tensorPure N (coneObject f)).toLinearMap z y)) =
    (tensorPure N (coneObject f)).toLinearMap z y
  rw [tensorConeFwd_pure, tensorConeBwd_apply]
  show (tensorModuleMap N (coneIncl f)).toFun ((tensorPure N L).toLinearMap z.1 y) +
      tensorConeSectionMap N f ((tensorPure N K).toLinearMap z.2 y) =
    (tensorPure N (coneObject f)).toLinearMap z y
  rw [hincl, tensorConeSectionMap_pure, ← LinearMap.add_apply, ← map_add, hz]

/-- **The cone comparison.** Tensoring with `N` carries the cone of `f` to the cone of
`f ⊗_A N`. -/
noncomputable def tensorConeIso (N : Bimodule A B) (f : K ⟶ L) :
    tensorObj N (coneObject f) ≅ coneObject (tensorModuleMap N f) where
  hom := tensorConeFwd N f
  inv := tensorConeBwd N f
  hom_inv_id := tensorConeFwd_bwd N f
  inv_hom_id := tensorConeBwd_fwd N f

/-- The cone comparison is compatible with the projection to the shift: this is the third square
of the comparison of cone triangles. -/
theorem tensorConeFwd_comp_proj (N : Bimodule A B) (f : K ⟶ L) :
    (tensorConeFwd N f ≫ coneProj (tensorModuleMap N f) :
        tensorObj N (coneObject f) ⟶ shift (tensorObj N K) 1) =
      tensorModuleMap N (coneProj f) ≫ tensorShiftBack N K 1 := by
  refine tensorObj_hom_ext N (coneObject f) _ _ fun z y => ?_
  have h : (tensorModuleMap N (coneProj f)).toFun
      ((tensorPure N (coneObject f)).toLinearMap z y) =
      (tensorPure N (shift K 1)).toLinearMap z.2 y :=
    tensorCompFunctor_map_pure N (coneProj f) z y
  show (coneProj (tensorModuleMap N f)).toFun
      ((tensorConeFwd N f).toFun ((tensorPure N (coneObject f)).toLinearMap z y)) =
    (tensorShiftBack N K 1).toFun
      ((tensorModuleMap N (coneProj f)).toFun ((tensorPure N (coneObject f)).toLinearMap z y))
  rw [tensorConeFwd_pure, h, tensorShiftBack_pure]
  rfl

/-- **The cone triangle comparison.** The image of the cone triangle of `f` under the tensor
functor, as a triangle of differential graded modules, is the cone triangle of `f ⊗_A N`. -/
noncomputable def tensorConeTriangleIso (N : Bimodule A B) (f : K ⟶ L) :
    (tensorCompFunctor N).mapTriangle.obj (coneTriangleDG f) ≅
      coneTriangleDG (tensorModuleMap N f) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (tensorConeIso N f)
    (show tensorModuleMap N f ≫ 𝟙 (tensorObj N L) = 𝟙 (tensorObj N K) ≫ tensorModuleMap N f from by
      rw [Category.comp_id, Category.id_comp])
    (show tensorModuleMap N (coneIncl f) ≫ (tensorConeIso N f).hom =
        𝟙 (tensorObj N L) ≫ coneIncl (tensorModuleMap N f) from by
      rw [Category.id_comp]
      exact tensorConeFwd_comp_incl N f)
    (by exact (Category.comp_id _).trans (tensorConeFwd_comp_proj N f).symm)

end Cone

/-! ### The functor on homotopy categories -/

/-- Tensoring with `N` identifies homotopic homomorphisms: the identification is transported
from the homotopy category along the comparison of Tag 09LM. -/
theorem tensorComp_map_eq_of_homotopyRel (N : Bimodule A B)
    (x y : DifferentialGradedModule.{u, u, u} A) (f₁ f₂ : x ⟶ y)
    (h : homotopyRel A f₁ f₂) :
    (tensorCompFunctor N ⋙ toHomotopyCategory B).map f₁ =
      (tensorCompFunctor N ⋙ toHomotopyCategory B).map f₂ := by
  have hq : (toHomotopyCategory A).map f₁ = (toHomotopyCategory A).map f₂ :=
    (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel.{u, u, u} A) f₁ f₂).mpr h
  have n₁ := (tensorCompFunctor_quotient N).hom.naturality f₁
  have n₂ := (tensorCompFunctor_quotient N).hom.naturality f₂
  have hmid : (toHomotopyCategory A ⋙ tensorHomotopyFunctor N).map f₁ =
      (toHomotopyCategory A ⋙ tensorHomotopyFunctor N).map f₂ := by
    show (tensorHomotopyFunctor N).map ((toHomotopyCategory A).map f₁) =
      (tensorHomotopyFunctor N).map ((toHomotopyCategory A).map f₂)
    rw [hq]
  rw [hmid] at n₁
  exact (Iso.cancel_iso_hom_right _ _ ((tensorCompFunctor_quotient N).app y)).mp
    (n₁.trans n₂.symm)

/-- The descent of the tensor functor to the homotopy category, as a lift along the quotient. -/
noncomputable abbrev tensorQuotientLift (N : Bimodule A B) :
    HomotopyCategory.{u, u, u} A ⥤ HomotopyCategory.{u, u, u} B :=
  CategoryTheory.Quotient.lift (homotopyRel.{u, u, u} A)
    (tensorCompFunctor N ⋙ toHomotopyCategory B) (tensorComp_map_eq_of_homotopyRel N)

/-- The lift agrees with the functor of Tag 09LM on homotopy categories. -/
noncomputable def tensorQuotientLiftIso (N : Bimodule A B) :
    tensorQuotientLift N ≅ tensorHomotopyFunctor N :=
  CategoryTheory.Quotient.natIsoLift (homotopyRel.{u, u, u} A)
    (CategoryTheory.Quotient.lift.isLift (homotopyRel.{u, u, u} A)
        (tensorCompFunctor N ⋙ toHomotopyCategory B)
        (tensorComp_map_eq_of_homotopyRel N) ≪≫
      tensorCompFunctor_quotient N)

/-- The lift carries distinguished triangles to distinguished triangles: a distinguished triangle
is isomorphic to the image of a cone triangle of differential graded modules, and the tensor
functor carries that cone triangle to a cone triangle. -/
theorem tensorQuotientLift_isTriangulated (N : Bimodule A B) :
    (tensorQuotientLift N).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨K, L, f, ⟨e⟩⟩ := hT
    have chain : (tensorQuotientLift N).mapTriangle.obj (coneTriangle f) ≅
        coneTriangle (tensorModuleMap N f) :=
      (Functor.mapTriangleCompIso (toHomotopyCategory A)
            (tensorQuotientLift N)).symm.app (coneTriangleDG f) ≪≫
        (Functor.mapTriangleIso
            (CategoryTheory.Quotient.lift.isLift (homotopyRel.{u, u, u} A)
              (tensorCompFunctor N ⋙ toHomotopyCategory B)
              (tensorComp_map_eq_of_homotopyRel N))).app (coneTriangleDG f) ≪≫
        (Functor.mapTriangleCompIso (tensorCompFunctor N)
            (toHomotopyCategory B)).app (coneTriangleDG f) ≪≫
        (toHomotopyCategory B).mapTriangle.mapIso (tensorConeTriangleIso N f)
    exact isomorphic_mem_distinguishedConeTriangles (coneTriangle (tensorModuleMap N f))
      ⟨tensorObj N K, tensorObj N L, tensorModuleMap N f, ⟨Iso.refl _⟩⟩ _
      ((tensorQuotientLift N).mapTriangle.mapIso e ≪≫ chain)

end DifferentialGraded.Bimodule
