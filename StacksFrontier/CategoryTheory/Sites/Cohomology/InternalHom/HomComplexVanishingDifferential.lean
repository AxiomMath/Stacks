module

public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSectionsSums

/-!
# When the internal Hom complex has vanishing differential

Let `(C, O)` be a ringed site and let `K`, `L` be complexes of `O`-modules. The differential of
the internal Hom complex `SheafHom^•(K, L)` obeys the Leibniz rule

`d(f) = d_L ∘ f + (-1)^{n+1} f ∘ d_K`

on local sections. So if `L` has vanishing differential, the differential of the Hom complex is
the second term alone, and it vanishes identically exactly when every local section of the Hom
complex annihilates every section in the image of the differential of `K`. When moreover `L` is
concentrated in degree zero, all but one of those conditions is vacuous, because the Hom complex
has only one nonvanishing component in each degree.

That is the situation of a Koszul complex mapped into the quotient of the structure sheaf by the
ideal the Koszul complex is built from: the differential of the Koszul complex is contraction by
sections of the ideal, which act as zero on the quotient.

## Main results

* `AlgebraicGeometry.RingedSite.homSection_eq_zero`: a section of the internal Hom complex
  vanishes as soon as all its evaluations do.
* `AlgebraicGeometry.RingedSite.SheafHomComplex.d_eq_zero`: **the differential of the internal
  Hom complex vanishes** when the differential of the target does and every evaluation of a Hom
  section on a section in the image of the differential of the source vanishes.
* `AlgebraicGeometry.RingedSite.SheafHomComplex.d_eq_zero_of_single`: the same for a target
  concentrated in degree zero, where only the evaluations landing in degree zero have to be
  considered.

## Implementation notes

The complex underlying a realization of the internal Hom is opaque: neither its terms nor its
differential can be unfolded, and the only handle on either is the identification of its
sections with the ordinary Hom complex of the restricted complexes. So the differential is
reached through `AlgebraicGeometry.RingedSite.applyHomSectionOver_differential`, the Leibniz
rule on evaluations, and a morphism out of a term of the Hom complex is shown to vanish through
`AlgebraicGeometry.RingedSite.homSection_ext`, which says that a section is determined by its
evaluations.

For a target concentrated in degree zero the reduction is by cases on the target degree: the
term of the Hom complex in degree `n` has a single nonvanishing component, the one evaluating a
degree-`(-n)` section of the source, and in every other component the value lands in a zero
object, where `Stacks.SheafOfModules.section_eq_zero_of_isZero` applies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open CochainComplex.HomComplex

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The zero morphism of sheaves of modules acts as zero on sections. -/
theorem zero_val_app_apply {A B : _root_.SheafOfModules.{w} R} (W : Cᵒᵖ) (x : A.val.obj W) :
    (_root_.SheafOfModules.Hom.val (0 : A ⟶ B)).app W x = 0 := by
  with_unfolding_all rfl

/-- **Every section of a zero object vanishes.** This is the converse of
`Stacks.SheafOfModules.isZero_of_forall_section_eq_zero`: the identity of a zero object is the
zero morphism, and both act on a section as themselves. -/
theorem section_eq_zero_of_isZero {M : _root_.SheafOfModules.{w} R} (h : IsZero M) (W : Cᵒᵖ)
    (y : M.val.obj W) : y = 0 := by
  have h1 : (_root_.SheafOfModules.Hom.val (𝟙 M)).app W y =
      (_root_.SheafOfModules.Hom.val (0 : M ⟶ M)).app W y := by
    rw [h.eq_of_src (𝟙 M) 0]
  rw [zero_val_app_apply] at h1
  simpa using h1

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (H : SheafHomComplex X K L)

/-- **A section of the internal Hom complex vanishes as soon as all its evaluations do.** -/
theorem homSection_eq_zero (U : X.C) (n : ℤ) {f : (H.obj.X n).val.obj (op U)}
    (h : ∀ (p q : ℤ) (hpq : p + n = q) (V : X.C) (i : V ⟶ U) (x : (K.X p).val.obj (op V)),
      applyHomSectionOver X H U V i n p q hpq f x = 0) : f = 0 :=
  homSection_ext X H U n fun p q hpq V i x =>
    (h p q hpq V i x).trans (applyHomSectionOver_zero_left X H U V i n p q hpq x).symm

namespace SheafHomComplex

/-- **The differential of the internal Hom complex vanishes** when the differential of the
target vanishes and every evaluation of a section of the Hom complex on a section in the image
of the differential of the source vanishes. By the Leibniz rule those two are exactly the two
summands of the differential. -/
theorem d_eq_zero (hL : ∀ q q' : ℤ, L.d q q' = 0)
    (hd : ∀ (U V : X.C) (i : V ⟶ U) (n p q : ℤ) (hpq : p + 1 + n = q)
      (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)),
      applyHomSectionOver X H U V i n (p + 1) q hpq f
        ((K.d p (p + 1)).val.app (op V) x) = 0)
    (n : ℤ) : H.obj.d n (n + 1) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext
    (LinearMap.ext fun f => ?_))
  obtain ⟨U⟩ := W
  refine homSection_eq_zero X H U (n + 1) fun p q hpq V i x => ?_
  obtain rfl : q = p + n + 1 := by omega
  refine Eq.trans (applyHomSectionOver_differential X H U V i n p (p + n) (p + n + 1)
    rfl rfl f x) ?_
  rw [hd U V i n p (p + n + 1) (by omega) f x, smul_zero, add_zero, hL]
  exact Stacks.SheafOfModules.zero_val_app_apply _ _

/-- **The differential of the internal Hom complex into a complex concentrated in degree zero
vanishes** when every evaluation of a Hom section on a section in the image of the differential
of the source *which lands in degree zero* vanishes. The other evaluations land in zero objects,
so nothing has to be assumed about them. -/
theorem d_eq_zero_of_single (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (H : SheafHomComplex X K
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0).obj N))
    (hd : ∀ (U V : X.C) (i : V ⟶ U) (n p : ℤ) (hp : p + 1 + n = 0)
      (f : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)),
      applyHomSectionOver X H U V i n (p + 1) 0 (by omega) f
        ((K.d p (p + 1)).val.app (op V) x) = 0)
    (n : ℤ) : H.obj.d n (n + 1) = 0 := by
  refine d_eq_zero X H (fun q q' => HomologicalComplex.single_obj_d _ 0 N q q')
    (fun U V i m p q hpq f x => ?_) n
  by_cases hq : q = 0
  · subst hq
    exact hd U V i m p hpq f x
  · exact Stacks.SheafOfModules.section_eq_zero_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N q hq) (op V) _

end SheafHomComplex

end AlgebraicGeometry.RingedSite

end
