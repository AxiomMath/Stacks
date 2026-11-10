module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomB
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated

/-!
# Shift functors on sheaves of differential graded modules

Let `(C, O)` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras. For
every integer `k` there is a shift functor `[k]` on the differential graded category
`Mod^dg(A, d)` of right differential graded `A`-modules: on an object it shifts the underlying
complex of sheaves of modules and leaves the right action alone, on a homogeneous morphism it
keeps the component maps, and it satisfies `[0] = id` and `[k + l] = [k] ∘ [l]`. Moreover the
identification `Hom(L, M[k]) = Hom(L, M)[k]` of graded `Hom`-modules is compatible with the
differentials of the two `Hom` complexes.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.dgShiftFunctor`: the shift functor `[k]` on
  `Mod^dg(A, d)`, as a functor of differential graded categories.
* `SheafOfModules.DifferentialGradedModule.dgShiftHomEquiv`: the identification
  `Hom(L, M[k])^n = Hom(L, M)^{n + k}`.

## Main results

* `SheafOfModules.DifferentialGradedModule.dgShiftFunctor_complex` and
  `SheafOfModules.DifferentialGradedModule.dgShiftFunctor_complex_d`: the underlying complex of
  `M[k]` is the shift of the underlying complex of `M`, so in degree `n` it is `M^{n + k}` and
  its differential is `(-1)^k` times that of `M`.
* `SheafOfModules.DifferentialGradedModule.dgShiftFunctor_map_v` and
  `SheafOfModules.DifferentialGradedModule.dgShiftFunctor_map_v_of_degree_zero`: the components
  of `f[k]`.
* `SheafOfModules.DifferentialGradedModule.dgShiftFunctor_zero_obj`,
  `SheafOfModules.DifferentialGradedModule.dgShiftFunctor_add_obj`,
  `SheafOfModules.DifferentialGradedModule.dgShiftFunctor_add_map`: `[0] = id` and
  `[k + l] = [k] ∘ [l]`.
* `SheafOfModules.DifferentialGradedModule.dgShiftHomEquiv_d`: the identification of `Hom`
  complexes is compatible with the differentials.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj_complex`: the
  complex underlying the `k`-th translate of an object of the homotopy category is the shift of
  the complex underlying that object.

## Implementation notes

Everything here is read off the single datum
`SheafOfModules.DifferentialGradedModule.shiftAxiomB`, whose type
`SheafOfModules.DifferentialGradedModule.CanonicalShiftAxiomB` is axiom (B) of Stacks Project
Tag 0FS4 *pinned to the canonical shifts* — those whose underlying complex is the shift of the
underlying complex and whose right action is unchanged. That is exactly the shift this section
of the source defines, which is why the source's proof of tag 0FS4 says that axiom (B) was shown
in this section. This file states the content of the section in the vocabulary of right
differential graded modules and gives it its tag; it constructs nothing new.

**The sign on morphisms.** The source says that `f[k]` is given by the *same* component maps as
`f`, and then that `[k]` is a functor of differential graded *categories*. These two assertions
are incompatible unless `k` is even. Writing `L[k]^n = L^{n + k}`, `d_{L[k]} = (-1)^k d_L` and
letting `g` be the morphism with the same component maps as a homogeneous `f` of degree `n`,
```
d(g) = d_{M[k]} ∘ g - (-1)^n g ∘ d_{L[k]}
     = (-1)^k (d_M ∘ g - (-1)^n g ∘ d_L),
```
whose component maps are `(-1)^k` times those of `d(f)`; so `f ↦ g` commutes with the
differential only up to the global sign `(-1)^k`, and is a differential graded functor only for
even `k`. Multiplying the component maps by `(-1)^{k n}` repairs this and is the unique such
correction of that shape: it replaces the discrepancy `(-1)^k` by
`(-1)^{k(n + 1)} (-1)^k (-1)^{-k n} = 1`. The repo's shift takes this convention — see
`dgShiftFunctor_map_v` — and the source's literal reading is recovered on the morphisms the
source's clause 2 is about, the closed homogeneous morphisms of degree zero, where the sign is
`+1`; that is `dgShiftFunctor_map_v_of_degree_zero`.

Objects and homogeneous morphisms of `Mod^dg(A, d)` are identified with right differential graded
modules and with action-linear cochains only up to an equality of types, through
`SheafOfModules.DifferentialGradedModule.asModule`,
`SheafOfModules.DifferentialGradedModule.asObject` and
`SheafOfModules.DifferentialGradedModule.asCochain`; the heterogeneous equalities below are those
transports and say nothing about differential graded modules beyond what they say about the
underlying complexes.

## References

* [Stacks Project, Tag 0FRY](https://stacks.math.columbia.edu/tag/0FRY)
* [Stacks Project, Tag 0FS4](https://stacks.math.columbia.edu/tag/0FS4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace SheafOfModules.DifferentialGradedModule

universe u v w

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-! ### The shift functor `[k]` -/

/-- **Stacks Project, Tag 0FRY.** The `k`-th shift functor `[k]` on the differential graded
category `Mod^dg(A, d)` of right differential graded `A`-modules: a functor of differential
graded categories, so additive and linear on `Hom` modules and compatible with the differential,
the composition and the identities. -/
@[stacks 0FRY "the shift functor [k] on Mod^dg(A, d)"]
noncomputable def dgShiftFunctor (k : ℤ) :
    DGCategory.DGFunctor (dgCategoryData.{u, v, w} A).category
      (dgCategoryData.{u, v, w} A).category :=
  (shiftAxiomB.{u, v, w} A).axiomB.shiftFunctor k

/-- **Stacks Project, Tag 0FRY, clauses (1) and (2).** The complex of sheaves of modules
underlying `M[k]` is the `k`-th shift of the complex underlying `M`. -/
@[stacks 0FRY "clauses (1) and (2): the underlying complex of M[k]"]
theorem dgShiftFunctor_complex (k : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
    (asModule A ((dgShiftFunctor.{u, v, w} A k).obj (asObject A M))).complex =
      (CochainComplex.shiftFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k).obj M.complex :=
  (shiftAxiomB.{u, v, w} A).shifted_complex k M

/-- The right `A`-action on `M[k]` is that of `M`, read in the shifted degree. -/
theorem dgShiftFunctor_action (k : ℤ) (M : DifferentialGradedModule.{u, v, w} A)
    (p q : ℤ) (U : X.Cᵒᵖ) :
    HEq (((asModule A ((dgShiftFunctor.{u, v, w} A k).obj (asObject A M))).mul p q).app U)
      ((M.mul (p + k) q).app U) :=
  (shiftAxiomB.{u, v, w} A).shifted_action k M p q U

/-- **Stacks Project, Tag 0FRY, clause (1).** In degree `n` the shift `M[k]` is `M` in degree
`n + k`. -/
theorem dgShiftFunctor_complex_X (k n : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
    (asModule A ((dgShiftFunctor.{u, v, w} A k).obj (asObject A M))).complex.X n =
      M.complex.X (n + k) := by
  rw [dgShiftFunctor_complex]
  rfl

/-- **Stacks Project, Tag 0FRY, clause (2).** The differential of `M[k]` is `(-1)^k` times that
of `M`. -/
theorem dgShiftFunctor_complex_d (k p q : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
    ((CochainComplex.shiftFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k).obj M.complex).d p q =
      (k.negOnePow : ℤ) • M.complex.d (p + k) (q + k) :=
  rfl

/-! ### The action on morphisms -/

/-- **Stacks Project, Tag 0FRY.** The components of the shift `f[k]` of a homogeneous morphism
`f` of degree `n` are those of `f`, multiplied by `(-1)^{k n}`. See the implementation notes:
the sign is forced by the requirement that `[k]` be a functor of differential graded
categories, and it is `+1` in the degree the source's clause is about. -/
@[stacks 0FRY "the components of f[k]"]
theorem dgShiftFunctor_map_v (k n : ℤ) (M N : DifferentialGradedModule.{u, v, w} A)
    (f : (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) n)
    (p q : ℤ) (h : p + n = q) :
    HEq ((asCochain A ((dgShiftFunctor.{u, v, w} A k).map f)).v p q h)
      ((Int.negOnePow (k * n) : ℤ) • (asCochain A f).v (p + k) (q + k) (by omega)) :=
  (shiftAxiomB.{u, v, w} A).shifted_map k n M N f p q h

/-- **Stacks Project, Tag 0FRY.** On a homogeneous morphism of degree zero — in particular on a
morphism of `Mod(A, d)` — the shift `f[k]` has literally the same component maps as `f`, which
is the source's formulation. -/
@[stacks 0FRY "f[k] has the same component maps as f in degree zero"]
theorem dgShiftFunctor_map_v_of_degree_zero (k : ℤ)
    (M N : DifferentialGradedModule.{u, v, w} A)
    (f : (dgCategoryData.{u, v, w} A).category.Hom (asObject A M) (asObject A N) 0)
    (p q : ℤ) (h : p + 0 = q) :
    HEq ((asCochain A ((dgShiftFunctor.{u, v, w} A k).map f)).v p q h)
      ((asCochain A f).v (p + k) (q + k) (by omega)) := by
  refine (dgShiftFunctor_map_v.{u, v, w} A k 0 M N f p q h).trans (heq_of_eq ?_)
  rw [mul_zero, Int.negOnePow_zero]
  simp

/-! ### Additivity in the shift -/

/-- **Stacks Project, Tag 0FRY.** The zeroth shift is the identity on objects. -/
@[stacks 0FRY "[0] is the identity"]
theorem dgShiftFunctor_zero_obj (M : (dgCategoryData.{u, v, w} A).category.Obj) :
    (dgShiftFunctor.{u, v, w} A 0).obj M = M :=
  (shiftAxiomB.{u, v, w} A).axiomB.zero_obj M

/-- The zeroth shift is the identity on homogeneous morphisms. -/
theorem dgShiftFunctor_zero_map {M N : (dgCategoryData.{u, v, w} A).category.Obj} {n : ℤ}
    (f : (dgCategoryData.{u, v, w} A).category.Hom M N n) :
    HEq ((dgShiftFunctor.{u, v, w} A 0).map f) f :=
  (shiftAxiomB.{u, v, w} A).axiomB.zero_map f

/-- **Stacks Project, Tag 0FRY.** `[k + l] = [k] ∘ [l]` on objects. -/
@[stacks 0FRY "[k + l] = [k] ∘ [l]"]
theorem dgShiftFunctor_add_obj (k l : ℤ) (M : (dgCategoryData.{u, v, w} A).category.Obj) :
    (dgShiftFunctor.{u, v, w} A (k + l)).obj M =
      (dgShiftFunctor.{u, v, w} A k).obj ((dgShiftFunctor.{u, v, w} A l).obj M) :=
  (shiftAxiomB.{u, v, w} A).axiomB.add_obj k l M

/-- **Stacks Project, Tag 0FRY.** `[k + l] = [k] ∘ [l]` on homogeneous morphisms. -/
@[stacks 0FRY "[k + l] = [k] ∘ [l] on morphisms"]
theorem dgShiftFunctor_add_map (k l : ℤ) {M N : (dgCategoryData.{u, v, w} A).category.Obj}
    {n : ℤ} (f : (dgCategoryData.{u, v, w} A).category.Hom M N n) :
    HEq ((dgShiftFunctor.{u, v, w} A (k + l)).map f)
      ((dgShiftFunctor.{u, v, w} A k).map ((dgShiftFunctor.{u, v, w} A l).map f)) :=
  (shiftAxiomB.{u, v, w} A).axiomB.add_map k l f

/-! ### The shift of a `Hom` complex -/

/-- **Stacks Project, Tag 0FRY.** The identification `Hom(L, M[k])^n = Hom(L, M)^{n + k}`, as
modules over the global sections of the structure sheaf. -/
@[stacks 0FRY "Hom(L, M[k]) = Hom(L, M)[k]"]
noncomputable def dgShiftHomEquiv (k : ℤ) (L M : (dgCategoryData.{u, v, w} A).category.Obj)
    (n : ℤ) :
    (dgCategoryData.{u, v, w} A).category.Hom L M (n + k) ≃ₗ[(limit X.O.obj : CommRingCat.{u})]
      (dgCategoryData.{u, v, w} A).category.Hom L ((dgShiftFunctor.{u, v, w} A k).obj M) n :=
  (shiftAxiomB.{u, v, w} A).axiomB.toShift k L M n

/-- **Stacks Project, Tag 0FRY.** The identification `Hom(L, M[k]) = Hom(L, M)[k]` is compatible
with the differentials: on the right hand side the differential of a shifted complex carries the
sign `(-1)^k`. -/
@[stacks 0FRY "Hom(L, M[k]) = Hom(L, M)[k] is compatible with the differentials"]
theorem dgShiftHomEquiv_d (k : ℤ) (L M : (dgCategoryData.{u, v, w} A).category.Obj) (n : ℤ)
    (f : (dgCategoryData.{u, v, w} A).category.Hom L M (n + k)) :
    dgShiftHomEquiv.{u, v, w} A k L M (n + 1)
        ((dgCategoryData.{u, v, w} A).category.d' (by omega : (n + k) + 1 = (n + 1) + k) f) =
      (-1 : (limit X.O.obj : CommRingCat.{u})) ^ k.natAbs •
        (dgCategoryData.{u, v, w} A).category.d (dgShiftHomEquiv.{u, v, w} A k L M n f) :=
  (shiftAxiomB.{u, v, w} A).axiomB.toShift_d k L M n f

/-! ### The translations of the homotopy category -/

namespace HomotopyCategory

/-- The `k`-th translate of the class of a right differential graded module in the homotopy
category is the class of the `k`-th shift of that module. For `k = 1` this is
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj`. -/
theorem shiftFunctor_obj_eq (k : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
    (shiftFunctor (HomotopyCategory.{u, v, w} A) k).obj ((quotient A).obj M) =
      (quotient A).obj (asModule A ((dgShiftFunctor.{u, v, w} A k).obj (asObject A M))) := by
  change (quotient A).obj (asModule A
    ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K k).obj (asObject A M))) = _
  rw [(dgConeSituation A).shift.kShift_functor]
  refine congrArg (quotient A).obj (congrArg (asModule A) ?_)
  change (((dgConeSituation A).shift.shiftFunctor k).obj (asObject A M)) = _
  rw [dgConeSituation_shift]
  rfl

/-- The complex of sheaves of modules underlying the `k`-th translate of an object of the
homotopy category of right differential graded `A`-modules is the `k`-th shift of the complex
underlying that object. -/
theorem shiftFunctor_obj_complex (k : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
    ((shiftFunctor (HomotopyCategory.{u, v, w} A) k).obj ((quotient A).obj M)).as.complex =
      (CochainComplex.shiftFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k).obj M.complex := by
  rw [shiftFunctor_obj_eq]
  exact dgShiftFunctor_complex.{u, v, w} A k M

end HomotopyCategory

end SheafOfModules.DifferentialGradedModule

end
