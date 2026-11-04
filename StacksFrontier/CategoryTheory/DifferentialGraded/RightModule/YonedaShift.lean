module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.RestrictionExact
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Yoneda

/-!
# The differential graded Yoneda functor and the shift

Let `C` be a differential graded category over a commutative ring `R` carrying axiom (B), and
let `h_X = C(-, X)` be the representable right differential graded `C`-module of an object `X`.
Tag 0FQF asks of a functor of differential graded categories that it commute with the shift *on
the nose*, in the form of `DGCategory.DGFunctor.CommShiftB`. For `X ↦ h_X` that hypothesis is
`h_{X⟦n⟧} = (h_X)⟦n⟧`, and it does **not** follow from axiom (B): the degree-`i` part of the
left-hand side at an object `y` is `C.Hom y (X⟦n⟧) i`, that of the right-hand side is
`C.Hom y X (i + n)`, and axiom (B) relates the two only by the linear equivalence
`DGCategory.ShiftAxiomB.toShift`, not by an equality.

What this file does is reduce the three fields of `DGCategory.DGFunctor.CommShiftB` for the
Yoneda functor to two conditions on `C` alone:

* that the identification `toShift` of axiom (B) *is* an identity, heterogeneously; and
* that `h_{X⟦n⟧} = (h_X)⟦n⟧`.

The remaining two fields — the one about the shift of a homogeneous morphism, with its Koszul
sign, and the one about `toShift` itself — are then consequences of the laws
`DGCategory.ShiftAxiomB.toShift_comp_left` and
`DGCategory.ShiftAxiomB.toShift_comp_right` of axiom (B).

## Main definitions

* `DGCategory.ShiftAxiomB.IsStrictRepresentable`: the two conditions above.
* `DGCategory.commShiftB_yonedaDGFunctor`: the hypothesis of Tag 0FQF for `X ↦ h_X`, from them.

## Main results

* `DGCategory.ShiftAxiomB.IsStrictRepresentable.eq_toShift`: a degree-`k` morphism into `X⟦n⟧`
  is the image under `toShift` of the degree-`(k + n)` morphism into `X` it corresponds to.
* `DGCategory.ShiftAxiomB.IsStrictRepresentable.heq_map_shiftFunctor_map`: postcomposition with
  `f⟦n⟧` is, heterogeneously, the shift of postcomposition with `f`.
* `DGCategory.ShiftAxiomB.IsStrictRepresentable.heq_map_toShift`: postcomposition with
  `toShift f` is, heterogeneously, postcomposition with `f` read in the shifted target.

## Implementation notes

Both derived fields are proved pointwise through
`DGCategory.ShiftAxiomB.IsStrictRepresentable.heq_homogeneousMap`, which substitutes the two
module equalities before comparing values, so that the comparison of values is an equality of
elements of one module rather than a heterogeneous equality.

The Koszul sign `(-1)^{n p}` that the shift of a degree-`p` homogeneous morphism carries never
has to be moved across a heterogeneous equality: `toShift_comp_left` places it on the side of
the equation that lives in `C.Hom y (X⟦n⟧) k`, and the involutivity of the sign moves it to the
other side *inside that one module*, after which `toShift` is linear and absorbs it. A
heterogeneous equality `HEq u v` does not give `HEq (c • u) (c • v)`, the two scalar
multiplications being operations of two different modules, so this ordering is what makes the
proof go through at all.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public section

namespace DGCategory

universe v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-- **The shift of axiom (B) is strict on representables.** The first field says that the
identification `C.Hom x y (k + n) ≃ C.Hom x (y⟦n⟧) k` of axiom (B) is an identity, the second
that the representable module of a shifted object is the shift of the representable module.
Together they are the hypothesis of Tag 0FQF for the differential graded Yoneda functor; neither
follows from axiom (B), which asks only for a linear equivalence. -/
structure ShiftAxiomB.IsStrictRepresentable (S : ShiftAxiomB C) : Prop where
  /-- The identification of axiom (B) is a heterogeneous identity. -/
  toShift_heq : ∀ (n : ℤ) (x y : C.Obj) (k : ℤ) (f : C.Hom x y (k + n)),
    HEq (S.toShift n x y k f) f
  /-- `h_{X⟦n⟧} = (h_X)⟦n⟧`. -/
  yonedaRightModule_shift : ∀ (n : ℤ) (X : C.Obj),
    yonedaRightModule C ((S.shiftFunctor n).obj X) = RightModule.shift (yonedaRightModule C X) n

namespace ShiftAxiomB.IsStrictRepresentable

variable {S : ShiftAxiomB C} (hS : S.IsStrictRepresentable)
include hS

/-- A degree-`k` morphism into `y⟦n⟧` is the image under the identification of axiom (B) of any
degree-`(k + n)` morphism into `y` it is heterogeneously equal to. -/
theorem eq_toShift {n : ℤ} {x y : C.Obj} {k : ℤ}
    (a : C.Hom x ((S.shiftFunctor n).obj y) k) (a' : C.Hom x y (k + n)) (ha : HEq a a') :
    a = S.toShift n x y k a' :=
  eq_of_heq (ha.trans (hS.toShift_heq n x y k a').symm)

omit hS

/-- Two homogeneous morphisms between modules that are equal are heterogeneously equal as soon
as they have, heterogeneously, the same values. -/
theorem heq_homogeneousMap {M M' N N' : RightModule.{v} C} {p : ℤ}
    (hM : M = M') (hN : N = N') (φ : RightModule.HomogeneousMap M N p)
    (ψ : RightModule.HomogeneousMap M' N' p)
    (hv : ∀ (x : C.Obj) (i j : ℤ) (e : i + p = j) (a : M.obj x i) (a' : M'.obj x i),
      HEq a a' → HEq (RightModule.app φ e a) (RightModule.app ψ e a')) :
    HEq φ ψ := by
  subst hM
  subst hN
  exact heq_of_eq (RightModule.hom_ext fun x i j e a =>
    eq_of_heq (hv x i j e a a HEq.rfl))

include hS

/-- A morphism equal to the image under `toShift` of `a'` is heterogeneously equal to `a'`. -/
private theorem heq_of_eq_toShift {n : ℤ} {x y : C.Obj} {k : ℤ}
    {a : C.Hom x ((S.shiftFunctor n).obj y) k} {a' : C.Hom x y (k + n)}
    (h : a = S.toShift n x y k a') : HEq a a' :=
  (heq_of_eq h).trans (hS.toShift_heq n x y k a')

/-- **Postcomposition with `f⟦n⟧` is the shift of postcomposition with `f`.** This is the field
of `DGCategory.DGFunctor.CommShiftB` about homogeneous morphisms, for the Yoneda functor; it is
the law `DGCategory.ShiftAxiomB.toShift_comp_left` of axiom (B) read through the strictness of
the identification. -/
theorem heq_map_shiftFunctor_map (n : ℤ) {x y : C.Obj} {k : ℤ} (f : C.Hom x y k) :
    HEq (yonedaPostcomp C ((S.shiftFunctor n).map f))
      (RightModule.shiftMap (yonedaPostcomp C f) n) := by
  refine heq_homogeneousMap (hS.yonedaRightModule_shift n x) (hS.yonedaRightModule_shift n y)
    _ _ ?_
  intro z i j e a a' ha
  obtain rfl : j = k + i := by omega
  have hsign : (-1 : R) ^ (n * k).natAbs * (-1 : R) ^ (n * k).natAbs = 1 :=
    RightModule.neg_one_pow_natAbs_mul_self (n * k)
  have hcl := S.toShift_comp_left n (x := z) (y := x) (z := y) (l := i) (m := k) f a'
  rw [← hS.eq_toShift a a' ha] at hcl
  have hcl' : S.toShift n z y (k + i)
      ((-1 : R) ^ (n * k).natAbs •
        C.comp (show k + (i + n) = (k + i) + n by omega) f a') =
      C.comp (show k + i = k + i by omega) ((S.shiftFunctor n).map f) a := by
    rw [map_smul, hcl, smul_smul, hsign, one_smul]
  rw [app_yonedaPostcomp, RightModule.app_shiftMap, app_yonedaPostcomp]
  exact hS.heq_of_eq_toShift hcl'.symm

/-- **Postcomposition with `toShift f` is postcomposition with `f`, read in the shifted
target.** This is the field of `DGCategory.DGFunctor.CommShiftB` about the identifications of
axiom (B), for the Yoneda functor; it is the law
`DGCategory.ShiftAxiomB.toShift_comp_right` of axiom (B) read through the strictness of the
identification. -/
theorem heq_map_toShift (n : ℤ) (x y : C.Obj) (k : ℤ) (f : C.Hom x y (k + n)) :
    HEq (yonedaPostcomp C (S.toShift n x y k f))
      (RightModule.toShiftHom n (yonedaPostcomp C f)) := by
  refine heq_homogeneousMap rfl (hS.yonedaRightModule_shift n y) _ _ ?_
  intro z i j e a a' ha
  obtain rfl : j = k + i := by omega
  obtain rfl : a = a' := eq_of_heq ha
  have hcr := S.toShift_comp_right n (x := z) (y := x) (z := y) (l := i) (m := k) f a
  rw [app_yonedaPostcomp, RightModule.app_toShiftHom, app_yonedaPostcomp]
  exact hS.heq_of_eq_toShift hcr.symm

end ShiftAxiomB.IsStrictRepresentable

/-- **The differential graded Yoneda functor commutes with the shift**, in the form Tag 0FQF
asks for, as soon as the shift of axiom (B) is strict on representables. -/
theorem commShiftB_yonedaDGFunctor {S : ShiftAxiomB C} (hS : S.IsStrictRepresentable) :
    (yonedaDGFunctor C).CommShiftB S (rightModuleShiftAxiomB.{v} C) where
  obj n X := hS.yonedaRightModule_shift n X
  map := by
    intro n x y k f
    exact hS.heq_map_shiftFunctor_map n f
  toShift := by
    intro n x y k f
    exact hS.heq_map_toShift n x y k f

end DGCategory

end
