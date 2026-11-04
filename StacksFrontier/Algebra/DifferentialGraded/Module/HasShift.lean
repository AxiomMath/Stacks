module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Shift.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift

/-!
# The shift of differential graded modules as a `HasShift` structure

The shift functors `M ↦ M[k]` of right differential graded modules assemble into a
`HasShift (Mod_{(A,d)}) ℤ`: shifting by `0` is the identity and shifting by `a + b` is shifting
by `a` and then by `b`, with the identity of the underlying module as the comparison isomorphism
in both cases. Shifting also preserves homotopies, up to the sign `(-1)^k` on the homotopy, so
the homotopy relation is compatible with the shift and the shift descends to the homotopy
category.

## Main definitions

* `DifferentialGradedModule.shiftZeroHom`, `shiftZeroInv`, `shiftZeroIso`: the comparison with
  the identity functor.
* `DifferentialGradedModule.shiftAddHom`, `shiftAddInv`, `shiftAddIso`: the comparison of
  `M[a + b]` with `(M[a])[b]`.
* `DifferentialGradedModule.shiftMkCore`: the shift functors with their comparison
  isomorphisms, as a `CategoryTheory.ShiftMkCore`.
* `DifferentialGradedModule.instHasShift`: the resulting `HasShift` structure.

## Main results

* `DifferentialGradedModule.homotopyRelCompatibleWithShift`: the homotopy relation is compatible
  with the shift, so `CategoryTheory.Quotient` transports the shift to the homotopy category.

## Implementation notes

All four comparison homomorphisms have the identity of the underlying module as their underlying
map; only the gradings and the signs in the differentials have to be matched, which is where the
degree arithmetic and `Int.negOnePow_add` are used. The `HasShift` structure is assembled with
`CategoryTheory.hasShiftMk`, so only the three coherence identities have to be checked, and each
reduces to the identity on underlying elements by `eqToHom_shift_apply`.

The homotopy transported along the shift is `(-1)^k` times the original one; the sign is forced
by the sign in the differential of a shifted module, and it cancels against itself in the
homotopy equation because `(-1)^k (-1)^k = 1`.

## References

* [Stacks Project, Tag 09K6](https://stacks.math.columbia.edu/tag/09K6)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- The comparison `M[0] ⟶ M`, the identity on underlying modules. -/
noncomputable def shiftZeroHom (M : DifferentialGradedModule A) : shift M 0 ⟶ M where
  toFun := LinearMap.id
  map_smul := by intros; rfl
  map_grading := by intro n x hx; simpa using hx
  map_d := by ext x; simp [shift_d]

/-- The comparison `M ⟶ M[0]`, the identity on underlying modules. -/
noncomputable def shiftZeroInv (M : DifferentialGradedModule A) : M ⟶ shift M 0 where
  toFun := LinearMap.id
  map_smul := by intros; rfl
  map_grading := by intro n x hx; simpa using hx
  map_d := by ext x; simp [shift_d]

/-- The comparison `M[a + b] ⟶ (M[a])[b]`, the identity on underlying modules. -/
noncomputable def shiftAddHom (M : DifferentialGradedModule A) (a b : ℤ) :
    shift M (a + b) ⟶ shift (shift M a) b where
  toFun := LinearMap.id
  map_smul := by intros; rfl
  map_grading := by
    intro n x hx
    have hx' : x ∈ M.grading (n + (a + b)) := hx
    change x ∈ M.grading (n + b + a)
    rwa [show n + b + a = n + (a + b) from by omega]
  map_d := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, shift_d, LinearMap.smul_apply]
    rw [Int.negOnePow_add, mul_comm a.negOnePow b.negOnePow]
    simp [smul_smul]

/-- The comparison `(M[a])[b] ⟶ M[a + b]`, the identity on underlying modules. -/
noncomputable def shiftAddInv (M : DifferentialGradedModule A) (a b : ℤ) :
    shift (shift M a) b ⟶ shift M (a + b) where
  toFun := LinearMap.id
  map_smul := by intros; rfl
  map_grading := by
    intro n x hx
    have hx' : x ∈ M.grading (n + b + a) := hx
    change x ∈ M.grading (n + (a + b))
    rwa [show n + (a + b) = n + b + a from by omega]
  map_d := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, shift_d, LinearMap.smul_apply]
    rw [Int.negOnePow_add, mul_comm a.negOnePow b.negOnePow]
    simp [smul_smul]

/-- Shifting by `0` is the identity functor. -/
noncomputable def shiftZeroIso : shiftFunctor A 0 ≅ 𝟭 _ where
  hom := { app := shiftZeroHom A, naturality := by intros; apply Hom.ext; rfl }
  inv := { app := shiftZeroInv A, naturality := by intros; apply Hom.ext; rfl }
  hom_inv_id := by ext M; apply Hom.ext; rfl
  inv_hom_id := by ext M; apply Hom.ext; rfl

/-- Shifting by `a + b` is shifting by `a` and then by `b`. -/
noncomputable def shiftAddIso (a b : ℤ) :
    shiftFunctor A (a + b) ≅ shiftFunctor A a ⋙ shiftFunctor A b where
  hom := { app := fun M => shiftAddHom A M a b, naturality := by intros; apply Hom.ext; rfl }
  inv := { app := fun M => shiftAddInv A M a b, naturality := by intros; apply Hom.ext; rfl }
  hom_inv_id := by ext M; apply Hom.ext; rfl
  inv_hom_id := by ext M; apply Hom.ext; rfl

private theorem eqToHom_toFun {M N : DifferentialGradedModule A} (h : M = N) (x : M.M) :
    (eqToHom h).toFun x = cast (congrArg DifferentialGradedModule.M h) x := by
  cases h
  rfl

private theorem eqToHom_shift_apply (X : DifferentialGradedModule A) (a b : ℤ)
    (h : shift X a = shift X b) (x : X.M) : (eqToHom h).toFun x = x := by
  rw [eqToHom_toFun]
  have he : congrArg DifferentialGradedModule.M h = (rfl : X.M = X.M) := Subsingleton.elim _ _
  rw [he]
  rfl

/-- The shift functors on differential graded modules, together with the comparison isomorphisms
making them an action of the additive monoid `ℤ`. The core is named rather than inlined into
`DifferentialGradedModule.instHasShift` so that clients can rewrite with
`CategoryTheory.ShiftMkCore.shiftFunctorAdd_eq` for it. -/
@[implicit_reducible]
noncomputable def shiftMkCore : ShiftMkCore (DifferentialGradedModule.{u, v, w} A) ℤ where
  F := shiftFunctor A
  zero := shiftZeroIso A
  add := shiftAddIso A
  assoc_hom_app := by
    intro m₁ m₂ m₃ X
    apply Hom.ext
    ext x
    simp [shiftAddIso, shiftAddHom, Hom.comp_toFun_apply, eqToHom_shift_apply]
  zero_add_hom_app := by
    intro n X
    apply Hom.ext
    ext x
    simp [shiftAddIso, shiftAddHom, shiftZeroIso, shiftZeroInv, Hom.comp_toFun_apply,
      eqToHom_shift_apply]
  add_zero_hom_app := by
    intro n X
    apply Hom.ext
    ext x
    simp [shiftAddIso, shiftAddHom, shiftZeroIso, shiftZeroInv, Hom.comp_toFun_apply,
      eqToHom_shift_apply]

/-- The shift functors make the category of right differential graded modules a category with a
`ℤ`-shift. -/
noncomputable instance instHasShift : HasShift (DifferentialGradedModule.{u, v, w} A) ℤ :=
  hasShiftMk _ _ (shiftMkCore.{u, v, w} A)

/-- The shift functor supplied by the `HasShift` structure is the shift functor by that
integer. -/
theorem shiftFunctor_eq_shiftFunctor (k : ℤ) :
    CategoryTheory.shiftFunctor (DifferentialGradedModule A) k = shiftFunctor A k :=
  ShiftMkCore.shiftFunctor_eq _ k

/-- Shifting a homomorphism leaves its underlying linear map unchanged. -/
@[simp] theorem shiftFunctor_int_map_toFun (k : ℤ) {M N : DifferentialGradedModule A}
    (f : M ⟶ N) :
    ((CategoryTheory.shiftFunctor (DifferentialGradedModule A) k).map f).toFun = f.toFun := rfl

/-- Every shift functor on differential graded modules is additive: it leaves the underlying
linear map of a homomorphism unchanged, and addition of homomorphisms is addition of those
linear maps. -/
instance instShiftFunctorAdditive (k : ℤ) :
    (CategoryTheory.shiftFunctor (DifferentialGradedModule A) k).Additive where
  map_add := by intros; apply Hom.ext; rfl

/-- The shift of a homotopy, with the sign `(-1)^k` forced by the differential of a shifted
module. -/
private def shiftHomotopy {M N : DifferentialGradedModule A} {f g : Hom M N}
    (h : Homotopy f g) (k : ℤ) : Homotopy (shiftMap f k) (shiftMap g k) where
  toLinearMap := k.negOnePow • h.toLinearMap
  map_grading := by
    intro n x hx
    change (k.negOnePow • h.toLinearMap) x ∈ N.grading (n - 1 + k)
    rw [LinearMap.smul_apply, Units.smul_def]
    have hh := h.map_grading (n + k) x hx
    convert zsmul_mem hh _ using 1; congr 1; omega
  homotopy_eq := by
    intro x
    have hh := h.homotopy_eq x
    change f.toFun x - g.toFun x =
      (k.negOnePow • N.d) ((k.negOnePow • h.toLinearMap) x) +
        (k.negOnePow • h.toLinearMap) ((k.negOnePow • M.d) x)
    simp only [LinearMap.smul_apply, Units.smul_def, map_zsmul, smul_smul]
    have hk : (k.negOnePow : ℤ) * (k.negOnePow : ℤ) = 1 :=
      congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_mul_self k.negOnePow)
    simp only [hk, one_smul]
    exact hh

/-- Homotopy is compatible with the shift, so the shift descends to the homotopy category. -/
instance homotopyRelCompatibleWithShift : (homotopyRel A).IsCompatibleWithShift ℤ where
  condition := by
    intro k M N f g ⟨h⟩
    exact ⟨shiftHomotopy A h k⟩

end DifferentialGradedModule
