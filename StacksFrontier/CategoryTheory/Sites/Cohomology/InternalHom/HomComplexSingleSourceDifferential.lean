module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSingleSource

/-!
# The internal Hom complex out of a single complex, degreewise

Let `(C, O)` be a ringed site, `A` a sheaf of `O`-modules and `L` a complex of `O`-modules.
`AlgebraicGeometry.RingedSite.homComponentIso` identifies the degree-`n` term of the internal
Hom complex `SheafHom^•(A[0], L)` with the internal Hom sheaf `ℰom(A, L^n)`.  This file records
what that identification does to the differential: the differential of `SheafHom^•(A[0], L)`
becomes postcomposition with the differential of `L`, with no sign, because the Leibniz rule's
other term involves the differential of `A[0]`, which vanishes.

## Main definitions

* `AlgebraicGeometry.RingedSite.homComponentIsoOfEq`: the identification
  `SheafHom^•(E, F)^n ≅ ℰom(E^k, F^q)` for a source concentrated in degree `k`, with the target
  index `q = k + n` given explicitly rather than as the sum.

## Main results

* `AlgebraicGeometry.RingedSite.applyHomSectionOver_homComponentIsoOfEq_inv`: the Hom section
  attached to a local morphism evaluates to that morphism.  This pins the identification down.
* `AlgebraicGeometry.RingedSite.applyHomSectionOver_eq_zero_of_isZero`: a Hom section evaluates
  to zero on a degree in which the source complex vanishes.
* `AlgebraicGeometry.RingedSite.internalHomPost_val_app_apply`: postcomposition on the internal
  Hom sheaf acts on sections by postcomposition.

## Implementation notes

The target index is kept free because `(0 : ℤ) + n` and `n` are equal but not definitionally so,
and the internal Hom complex out of a complex concentrated in degree zero has to be compared, in
degree `n`, with the degree-`n` term of the target.  `homComponentIsoOfEq` is therefore
`homComponentIso` with that index substituted, and its characterising property is proved by
substituting it back.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
variable {E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Postcomposition on the internal Hom sheaf acts on a local section — a morphism of
restrictions — by postcomposition with the restriction of the inducing morphism. -/
theorem internalHomPost_val_app_apply
    {A B G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : B ⟶ G)
    (U V : X.C) (i : V ⟶ U) (ξ : (internalHomSheaf X A B).val.obj (op U))
    (x : A.val.obj (op V)) :
    PresheafOfModules.Hom.app ((internalHomPost X (A := A) g).val.app (op U) ξ)
        (op (Over.mk i)) x =
      (g.val.app (op V)) (PresheafOfModules.Hom.app ξ (op (Over.mk i)) x) :=
  rfl

/-- Equal morphisms of sheaves of modules act equally on sections. -/
private theorem val_app_apply_congr
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} {f g : M ⟶ N}
    (h : f = g) (U : X.C) (x : M.val.obj (op U)) : f.val.app (op U) x = g.val.app (op U) x := by
  rw [h]

/-- A section of a sheaf of modules which is a zero object is zero. -/
theorem eq_zero_of_isZero
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hM : IsZero M) (V : X.C)
    (x : M.val.obj (op V)) : x = 0 :=
  (val_app_apply_congr X (hM.eq_of_src (𝟙 M) 0) V x).trans
    (Stacks.SheafOfModules.zero_val_app_apply _ _)

/-- Evaluating a Hom section on a degree in which the source complex vanishes gives zero. -/
theorem applyHomSectionOver_eq_zero_of_isZero (U V : X.C) (i : V ⟶ U) (n p q : ℤ)
    (hpq : p + n = q) (hE : IsZero (E.X p))
    (s : (((sheafHomComplex X E F)).obj.X n).val.obj (op U)) (x : (E.X p).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X E F) U V i n p q hpq s x = 0 := by
  rw [eq_zero_of_isZero X hE V x]
  exact map_zero _

/-- The degree-`n` term of the internal Hom complex out of a source concentrated in degree `k`
is the internal Hom sheaf from that term into the degree-`q` term of the target, for `q` the sum
`k + n` spelled explicitly. -/
def homComponentIsoOfEq (k n q : ℤ) (hq : k + n = q)
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) :
    (sheafHomComplex X E F).obj.X n ≅ internalHomSheaf X (E.X k) (F.X q) := by
  subst hq
  exact homComponentIso X k n hE

/-- **The Hom section attached to a local morphism evaluates to that morphism.** This is the
characterising property of `AlgebraicGeometry.RingedSite.homComponentIsoOfEq`. -/
theorem applyHomSectionOver_homComponentIsoOfEq_inv (k n q : ℤ) (hq : k + n = q)
    (hE : ∀ p, p ≠ k → IsZero (E.X p)) (U V : X.C) (i : V ⟶ U)
    (ξ : (internalHomSheaf X (E.X k) (F.X q)).val.obj (op U))
    (x : (E.X k).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X E F) U V i n k q hq
        ((homComponentIsoOfEq X k n q hq hE).inv.val.app (op U) ξ) x =
      PresheafOfModules.Hom.app ξ (op (Over.mk i)) x := by
  subst hq
  have h := val_app_apply_congr X (homComponentIsoOfEq X k n (k + n) rfl hE).inv_hom_id U ξ
  exact congrArg (fun t => PresheafOfModules.Hom.app t (op (Over.mk i)) x) h

/-- **The differential of the internal Hom complex out of a complex concentrated in degree zero
is postcomposition with the differential of the target**, with no sign: the other term of the
Leibniz rule evaluates the Hom section on the differential of the source, which vanishes. -/
theorem applyHomSectionOver_differential_sgl
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U V : X.C) (i : V ⟶ U)
    (n q q' : ℤ) (hq : 0 + n = q) (hqq' : q + 1 = q')
    (f : ((sheafHomComplex X (sgl X A) L).obj.X n).val.obj (op U))
    (x : ((sgl X A).X 0).val.obj (op V)) :
    applyHomSectionOver X (sheafHomComplex X (sgl X A) L) U V i (n + 1) 0 q' (by omega)
        (((sheafHomComplex X (sgl X A) L).obj.d n (n + 1)).val.app (op U) f) x =
      (L.d q q').val.app (op V)
        (applyHomSectionOver X (sheafHomComplex X (sgl X A) L) U V i n 0 q hq f x) := by
  rw [applyHomSectionOver_differential X (sheafHomComplex X (sgl X A) L) U V i n 0 q q' hq hqq'
      f x,
    applyHomSectionOver_eq_zero_of_isZero X U V i n (0 + 1) q' (by omega)
      (isZero_sgl_X X A (0 + 1) (by omega)) f _,
    smul_zero, add_zero]

end AlgebraicGeometry.RingedSite

end
