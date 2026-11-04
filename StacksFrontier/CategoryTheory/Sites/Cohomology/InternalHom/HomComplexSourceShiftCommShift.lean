module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexShift

/-! # The internal Hom complex commutes with the shift in its source

Let `(C, O)` be a ringed site and let `I` be a complex of `O`-modules. This file assembles the
source-shift identification
`AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso` into the commutation datum of

`SheafHom(-, I) : (CochainComplex O-Mod ℤ)ᵒᵖ ⥤ CochainComplex O-Mod ℤ`

with the opposite shift of `CategoryTheory.Pretriangulated.Opposite`.

## Main definitions

* `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso'`: the source-shift identification with
  the index of the outer shift in general position, `SheafHom(K, M)[c] ≅ SheafHom(K[b], M)` for
  `b + c = 0`.
* `AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso`: the commutation datum.
* `AlgebraicGeometry.RingedSite.commShift_sheafHomComplexFlip`: the
  `CategoryTheory.Functor.CommShift ℤ` built from that datum and its two coherence equations,
  which are taken as hypotheses.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomSourceUnshiftIso'_hom_naturality`: the datum is natural
  in both complexes.

## What is left open, and what it is

The datum and its naturality are proved. The two coherence equations are not, and
`commShift_sheafHomComplexFlip` carries them as the hypotheses `hzero` and `hadd`. Together with
`AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSheafHomContravariantCommShift`,
those two equations are all that stands between this development and a
`CategoryTheory.Functor.CommShift ℤ` on the contravariant derived internal Hom
`RSheafHom(-, M) : D(O)ᵒᵖ ⥤ D(O)`.

Both are identities between morphisms of complexes of `O`-modules, so each reduces, by
`AlgebraicGeometry.RingedSite.sheafHom_ext` and the characterisation
`AlgebraicGeometry.RingedSite.sectionsEquiv_sourceShiftHom`, to an identity between homogeneous
components of cochains, where `AlgebraicGeometry.RingedSite.cochainSourceShift_v` computes the
left-hand side as the sign `(-1)^(b n' + b(b-1)/2)` times a reindexing. For `hadd` the sign
bookkeeping comes out: shifting the source by `a` and then by `b` carries the total sign
`a(n + a) + a(a-1)/2 + b(n + a + b) + b(b-1)/2`, while shifting by `a + b` at once carries
`(a+b)(n+a+b) + (a+b)(a+b-1)/2`, and the two differ by
`ab + ((a+b)(a+b-1)/2 - a(a-1)/2 - b(b-1)/2) = ab + ab = 2ab`, which is even. So no sign
obstruction stands in the way; what is left is the bookkeeping itself, together with the
components of `CochainComplex.shiftFunctorZero` and `CochainComplex.shiftFunctorAdd` and those
of their counterparts on the opposite category, Mathlib's
`CategoryTheory.Pretriangulated.Opposite.shiftFunctorZero_op_hom_app` and
`shiftFunctorAdd'_op_hom_app`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u})

section

variable {K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The source-shift identification of internal Hom complexes with the index of the outer shift
in general position: `SheafHom(K, M)[c] ≅ SheafHom(K[b], M)` whenever `b + c = 0`. The
reindexing `c = -b` is performed once here, so that the opposite shift — which presents
`(op K)[n]` as `op (K[-n])` and therefore always asks for the outer index `n` rather than
`-(-n)` — never meets it. -/
def sheafHomSourceShiftIso' (b c : ℤ) (h : b + c = 0) :
    ((sheafHomComplex X K M).obj)⟦c⟧ ≅ (sheafHomComplex X (K⟦b⟧) M).obj :=
  eqToIso (by rw [show c = -b from by omega]) ≪≫ sheafHomSourceShiftIso X b

/-- At `c = -b` the general-position identification is
`AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso`. -/
theorem sheafHomSourceShiftIso'_eq (b : ℤ) :
    sheafHomSourceShiftIso' X (K := K) (M := M) b (-b) (by omega) =
      sheafHomSourceShiftIso X b := by
  ext
  simp only [sheafHomSourceShiftIso', Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.id_comp]

/-- `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso'` is natural in both complexes. -/
theorem sheafHomSourceShiftIso'_hom_naturality (b c : ℤ) (h : b + c = 0)
    {K' M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (g : M ⟶ M') :
    (sheafHomSourceShiftIso' X (K := K) (M := M) b c h).hom ≫
        homMap X ((CategoryTheory.shiftFunctor _ b).map k) g =
      (CategoryTheory.shiftFunctor _ c).map (homMap X k g) ≫
        (sheafHomSourceShiftIso' X (K := K') (M := M') b c h).hom := by
  obtain rfl : c = -b := by omega
  rw [sheafHomSourceShiftIso'_eq, sheafHomSourceShiftIso'_eq]
  exact sheafHomSourceShiftIso_hom_naturality X b k g

/-- `AlgebraicGeometry.RingedSite.sheafHomSourceShiftIso'` read in the direction the commutation
datum of a `CategoryTheory.Functor.CommShift` wants: `SheafHom(K[b], M) ≅ SheafHom(K, M)[c]`
whenever `b + c = 0`. -/
def sheafHomSourceUnshiftIso' (b c : ℤ) (h : b + c = 0) :
    (sheafHomComplex X (K⟦b⟧) M).obj ≅ ((sheafHomComplex X K M).obj)⟦c⟧ :=
  (sheafHomSourceShiftIso' X (K := K) (M := M) b c h).symm

/-- `AlgebraicGeometry.RingedSite.sheafHomSourceUnshiftIso'` is natural in both complexes. -/
theorem sheafHomSourceUnshiftIso'_hom_naturality (b c : ℤ) (h : b + c = 0)
    {K' M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (g : M ⟶ M') :
    homMap X ((CategoryTheory.shiftFunctor _ b).map k) g ≫
        (sheafHomSourceUnshiftIso' X (K := K') (M := M') b c h).hom =
      (sheafHomSourceUnshiftIso' X (K := K) (M := M) b c h).hom ≫
        (CategoryTheory.shiftFunctor _ c).map (homMap X k g) := by
  rw [sheafHomSourceUnshiftIso', sheafHomSourceUnshiftIso', Iso.symm_hom, Iso.symm_hom,
    Iso.comp_inv_eq, Category.assoc,
    ← sheafHomSourceShiftIso'_hom_naturality X b c h k g, Iso.inv_hom_id_assoc]

end

/-- **The commutation datum of the contravariant internal Hom complex with the shift.** Its
component at `op K` is `SheafHom(K[-n], I) ≅ SheafHom(K, I)[n]`, because the opposite shift of
`CategoryTheory.Pretriangulated.Opposite` presents `(op K)[n]` as `op (K[-n])`. -/
def sheafHomOpCommShiftIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) :
    CategoryTheory.shiftFunctor
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ n ⋙
        (sheafHomComplexBifunctor X).flip.obj I ≅
      (sheafHomComplexBifunctor X).flip.obj I ⋙
        CategoryTheory.shiftFunctor
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) n :=
  NatIso.ofComponents
    (fun K => sheafHomSourceUnshiftIso' X (K := K.unop) (M := I) (-n) n (by omega))
    (fun {K _} f =>
      sheafHomSourceUnshiftIso'_hom_naturality X (K := K.unop) (M := I) (-n) n (by omega)
        f.unop (𝟙 I))

/-- **The contravariant internal Hom complex commutes with the shift**, given the two coherence
equations for the datum `AlgebraicGeometry.RingedSite.sheafHomOpCommShiftIso`.

This is the shape in which the residual is consumed: fed to
`AlgebraicGeometry.RingedSite.commShift_derivedSheafHomFlip` it produces a
`CategoryTheory.Functor.CommShift ℤ` on `RSheafHom(-, M) : D(O)ᵒᵖ ⥤ D(O)` for every object `M`
of `D(O)`. Both hypotheses are equations between morphisms of complexes of `O`-modules; neither
mentions a derived category. -/
@[instance_reducible]
def commShift_sheafHomComplexFlip
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hzero : sheafHomOpCommShiftIso X I 0 =
      Functor.CommShift.isoZero ((sheafHomComplexBifunctor X).flip.obj I) ℤ)
    (hadd : ∀ a b : ℤ, sheafHomOpCommShiftIso X I (a + b) =
      Functor.CommShift.isoAdd (sheafHomOpCommShiftIso X I a) (sheafHomOpCommShiftIso X I b)) :
    ((sheafHomComplexBifunctor X).flip.obj I).CommShift ℤ where
  commShiftIso n := sheafHomOpCommShiftIso X I n
  commShiftIso_zero := hzero
  commShiftIso_add := hadd

end AlgebraicGeometry.RingedSite

end
