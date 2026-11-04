module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveLifting

/-!
# Flatness and K-flatness of an arbitrary shift of a differential graded module

Let `X` be a ringed site, let `A` be a sheaf of differential graded algebras on it and let `M` be
a right differential graded `A`-module. For every integer `k` the shift `M[k]` by the shift
functor `[k]` on `Mod^dg(A, d)` is the degree `k` shift of `M` in the sense of
`SheafOfModules.RelativeTensor.IsDifferentialGradedShift`: degree `n` of `M[k]` is degree
`n + k` of `M`, the right action is unchanged and the differential acquires the sign `(-1)^k`.
Consequently `M[k]` is flat as a graded module as soon as `M` is, and is K-flat as soon as `M`
is.

## Main results

* `SheafOfModules.DifferentialGradedModule.isGradedShift_translate` and
  `SheafOfModules.DifferentialGradedModule.isDifferentialGradedShift_translate`: the translation
  `M[k]` is the degree `k` shift of `M`.
* `SheafOfModules.DifferentialGradedModule.isGradedFlat_translate` and
  `SheafOfModules.DifferentialGradedModule.isKFlat_translate`: `M[k]` is flat as a graded
  module, respectively K-flat, as soon as `M` is.
* `SheafOfModules.DifferentialGradedModule.isGradedFlat_dgShiftFunctor_obj` and
  `SheafOfModules.DifferentialGradedModule.isKFlat_dgShiftFunctor_obj`: the same statements for
  the image of `M` under the shift functor `[k]` on the differential graded category
  `Mod^dg(A, d)`.

## Implementation notes

The translation is `SheafOfModules.DifferentialGradedModule.translate`, which is the object part
of the shift functor `SheafOfModules.DifferentialGradedModule.dgShiftFunctor` read as a right
differential graded module; nothing new is constructed here. What is proved is that the two data
`SheafOfModules.DifferentialGradedModule.translate_complex` and the field `shifted_action` of
`SheafOfModules.DifferentialGradedModule.CanonicalShiftAxiomB` assemble into a degree shift in
the sense of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedShiftFlat.lean`,
whose consequences for the relative tensor product are then available.

The relative tensor product is formed over the sheaf of commutative rings `X.O`, whose underlying
sheaf of rings is the structure sheaf `X.ringSheaf` of the ringed site; the sheaf-of-commutative-
rings argument of the relative tensor product is therefore given explicitly as `X.O` in every
statement below, since it cannot be recovered from `X.ringSheaf` by unification. For the same
reason the sheaf-composition hypothesis of the relative tensor product is taken as an instance
argument rather than read off
`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`, which proves it for every ringed
site: the instance has to be available while the sheaf of commutative rings is still being
determined. The homogeneous pieces of the algebra and of the modules live in one universe, which
is what the relative tensor product requires.

## References

* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FRY](https://stacks.math.columbia.edu/tag/0FRY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (A : DifferentialGradedAlgebra.{u, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}] in
/-- Degree `n` of the translation `M[k]` is degree `n + k` of `M`. -/
theorem translate_piece_eq (k : ℤ) (M : DifferentialGradedModule.{u, w, w} A) {n p : ℤ}
    (h : n + k = p) :
    (GradedModule.ofDifferentialGraded (translate A k M)).piece n =
      (GradedModule.ofDifferentialGraded M).piece p :=
  (congrArg
    (fun T : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ↦
      T.X n)
    (translate_complex k M)).trans (congrArg M.complex.X h)

/-- **The translation `M[k]` is the degree `k` shift of `M` as a right graded module**: the
identification of `(M[k])^n` with `M^{n + k}` carries the right action. -/
noncomputable def isGradedShift_translate (k : ℤ) (M : DifferentialGradedModule.{u, w, w} A) :
    RelativeTensor.IsGradedShift (Osharp := X.O) k
      (GradedModule.ofDifferentialGraded (translate A k M))
      (GradedModule.ofDifferentialGraded M) where
  e h := eqToIso (translate_piece_eq A k M h)
  e_smul {n i p} h U x y := by
    have hβ : HEq (((translate A k M).mul n i).app U) ((M.mul p i).app U) := by
      subst h
      exact (shiftAxiomB A).shifted_action k M n i U
    exact SheafOfModules.ShiftFlat.bilinear_transport (translate_piece_eq A k M h)
      (translate_piece_eq A k M (show n + i + k = p + i by omega))
      ((translate A k M).mul n i) (M.mul p i) U hβ x y

/-- **The translation `M[k]` is the degree `k` shift of `M` as a differential graded module**:
the identification of `(M[k])^n` with `M^{n + k}` carries the right action, and carries the
differential of `M[k]` to `(-1)^k` times that of `M`. -/
noncomputable def isDifferentialGradedShift_translate (k : ℤ)
    (M : DifferentialGradedModule.{u, w, w} A) :
    RelativeTensor.IsDifferentialGradedShift (Osharp := X.O) k (translate A k M) M where
  toIsGradedShift := isGradedShift_translate A k M
  e_d {n p} h U x := by
    subst h
    exact SheafOfModules.ShiftFlat.shifted_d_val_app k (translate_complex k M) n (n + 1)
      (n + k) (n + k + 1) rfl rfl (by omega) U x

/-- **The translation `M[k]` of a right differential graded module whose underlying right graded
module is flat has flat underlying right graded module.** -/
theorem isGradedFlat_translate (k : ℤ) (M : DifferentialGradedModule.{u, w, w} A)
    (hM : RelativeTensor.IsGradedFlat (Osharp := X.O)
      (GradedModule.ofDifferentialGraded M)) :
    RelativeTensor.IsGradedFlat (Osharp := X.O)
      (GradedModule.ofDifferentialGraded (translate A k M)) :=
  (isGradedShift_translate A k M).isGradedFlat hM

/-- **The translation `M[k]` of a K-flat right differential graded module is K-flat.** -/
theorem isKFlat_translate (k : ℤ) (M : DifferentialGradedModule.{u, w, w} A)
    (hM : RelativeTensor.IsKFlat (Osharp := X.O) M) :
    RelativeTensor.IsKFlat (Osharp := X.O) (translate A k M) :=
  (isDifferentialGradedShift_translate A k M).isKFlat hM

/-- **The shift `M[k]` of a right differential graded module whose underlying right graded module
is flat has flat underlying right graded module.** -/
theorem isGradedFlat_dgShiftFunctor_obj (k : ℤ) (M : DifferentialGradedModule.{u, w, w} A)
    (hM : RelativeTensor.IsGradedFlat (Osharp := X.O)
      (GradedModule.ofDifferentialGraded M)) :
    RelativeTensor.IsGradedFlat (Osharp := X.O) (GradedModule.ofDifferentialGraded
      (asModule A ((dgShiftFunctor.{u, w, w} A k).obj (asObject A M)))) :=
  isGradedFlat_translate A k M hM

/-- **The shift `M[k]` of a K-flat right differential graded module is K-flat.** -/
theorem isKFlat_dgShiftFunctor_obj (k : ℤ) (M : DifferentialGradedModule.{u, w, w} A)
    (hM : RelativeTensor.IsKFlat (Osharp := X.O) M) :
    RelativeTensor.IsKFlat (Osharp := X.O)
      (asModule A ((dgShiftFunctor.{u, w, w} A k).obj (asObject A M))) :=
  isKFlat_translate A k M hM

end SheafOfModules.DifferentialGradedModule

end
