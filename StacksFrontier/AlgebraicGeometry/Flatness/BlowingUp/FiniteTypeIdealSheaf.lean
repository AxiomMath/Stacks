module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type quasi-coherent ideal sheaves and finitely presented closed subschemes

A quasi-coherent sheaf of ideals on a scheme is of finite type when its ideal on every affine
open is finitely generated (`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`). This file
records two things about that condition.

First, it is stable under the two operations on ideal sheaves that the theory of blowups
uses: the product and the sum of two finite type ideal sheaves are again of finite type.

Second, it is exactly the condition for the associated closed subscheme to be of finite
presentation over the ambient scheme: a closed immersion is of finite presentation if and only
if the ideal sheaf data it cuts out is of finite type. A closed immersion is automatically
affine, hence quasi-compact and quasi-separated, so only the local condition is at stake, and
on an affine open it is the statement that a surjection of rings is of finite presentation
exactly when its kernel is finitely generated.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType.mul` and
  `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType.sup`: the product and the sum of two
  finite type ideal sheaves are of finite type.
* `AlgebraicGeometry.isFiniteType_ker_of_finitePresentation`: the ideal sheaf cut out by a
  closed immersion of finite presentation is of finite type.
* `AlgebraicGeometry.locallyOfFinitePresentation_of_isFiniteType_ker`: the converse local
  statement.
* `AlgebraicGeometry.finitePresentation_subschemeι_iff_isFiniteType`: the resulting
  equivalence, for the closed subscheme attached to an ideal sheaf.
* `AlgebraicGeometry.finitePresentation_comap_subschemeι`: the closed subscheme attached to the
  inverse image of an ideal sheaf is again of finite presentation.

## Implementation notes

This is the statement of [Stacks, Tag 01TV] in the `Scheme.IdealSheafData` idiom, which is the
one the blowup API is written in;
`AlgebraicGeometry.finitePresentation_iff_isFiniteType_idealSheaf` states the same tag for the
kernel regarded as a `SheafOfModules` and asks for `SheafOfModules.IsFiniteType`. The two
predicates are about different objects — an assignment of ideals to affine opens versus a sheaf
of modules — so neither statement is an instance of the other, and the proof here is the direct
affine-local one rather than a transport along an identification of the two.

No `@[stacks]` attribute appears here: Tag 01TV is already carried by
`AlgebraicGeometry.finitePresentation_iff_isFiniteType_idealSheaf`.

## References

* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 0C3E](https://stacks.math.columbia.edu/tag/0C3E)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The product of two finite type quasi-coherent ideal sheaves is of finite type. -/
theorem Scheme.IdealSheafData.IsFiniteType.mul {X : Scheme.{u}} {I J : X.IdealSheafData}
    (hI : I.IsFiniteType) (hJ : J.IsFiniteType) : (I * J).IsFiniteType := by
  intro U
  simpa only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply] using (hI U).mul (hJ U)

/-- The sum of two finite type quasi-coherent ideal sheaves is of finite type. -/
theorem Scheme.IdealSheafData.IsFiniteType.sup {X : Scheme.{u}} {I J : X.IdealSheafData}
    (hI : I.IsFiniteType) (hJ : J.IsFiniteType) : (I ⊔ J).IsFiniteType := fun U =>
  Submodule.FG.sup (hI U) (hJ U)

/-- On an affine open, the ideal cut out by a closed immersion of finite presentation is
finitely generated: it is the kernel of a surjective ring map of finite presentation. -/
theorem fg_ker_ideal_of_finitePresentation {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hfp : FinitePresentation i) (U : X.affineOpens) :
    (i.ker.ideal U).FG := by
  rw [i.ker_apply U]
  have hsurj : Function.Surjective (i.app U.1).hom := i.app_surjective U.1 U.2
  have : (i.app U.1).hom.FinitePresentation := by
    rw [← Scheme.Hom.appLE_eq_app]
    exact hfp.1.finitePresentation_appLE U.2 (U.2.preimage i) le_rfl
  algebraize [(i.app U.1).hom]
  exact Algebra.FinitePresentation.ker_fG_of_surjective
    (Algebra.ofId Γ(X, U.1) Γ(Z, i ⁻¹ᵁ U.1)) hsurj

/-- The ideal sheaf cut out by a closed immersion of finite presentation is of finite type. -/
theorem isFiniteType_ker_of_finitePresentation {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hfp : FinitePresentation i) : i.ker.IsFiniteType :=
  fg_ker_ideal_of_finitePresentation i hfp

/-- Conjugating a ring map between sections by the isomorphisms with the global sections of the
open subschemes does not change whether it is of finite presentation. -/
private theorem finitePresentation_topIso_comp_comp_topIso_inv_iff {X Z : Scheme.{u}}
    {U : X.Opens} {W : Z.Opens} (f : Γ(X, U) ⟶ Γ(Z, W)) :
    (U.topIso.hom ≫ f ≫ W.topIso.inv).hom.FinitePresentation ↔ f.hom.FinitePresentation := by
  rw [← Category.assoc]
  exact (RingHom.finitePresentation_respectsIso.cancel_right_isIso _ _).trans
    (RingHom.finitePresentation_respectsIso.cancel_left_isIso _ _)

/-- If a morphism induces a ring map of finite presentation on a pair of affine opens, its
restriction between them is locally of finite presentation. -/
theorem locallyOfFinitePresentation_resLE_of_finitePresentation_appLE {X Z : Scheme.{u}}
    (i : Z ⟶ X) {U : X.Opens} {W : Z.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (h : W ≤ i ⁻¹ᵁ U) (hfp : (i.appLE U W h).hom.FinitePresentation) :
    LocallyOfFinitePresentation (i.resLE U W h) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have h2 : (U.topIso.hom ≫ i.appLE U W h ≫ W.topIso.inv).hom.FinitePresentation :=
    (finitePresentation_topIso_comp_comp_topIso_inv_iff _).2 hfp
  simpa [Scheme.Hom.appTop, Scheme.Hom.appLE_eq_app] using h2

/-- A closed immersion whose ideal sheaf is of finite type is locally of finite presentation:
on affine opens it is a surjection with finitely generated kernel. -/
theorem locallyOfFinitePresentation_of_isFiniteType_ker {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hI : i.ker.IsFiniteType) : LocallyOfFinitePresentation i := by
  refine ⟨fun U hU {V} hV hVU => ?_⟩
  let W := i ⁻¹ᵁ U
  have hfp : (i.appLE U W le_rfl).hom.FinitePresentation := by
    rw [Scheme.Hom.appLE_eq_app]
    exact RingHom.FinitePresentation.of_surjective _ (i.app_surjective U hU)
      (by simpa using hI ⟨U, hU⟩)
  have : LocallyOfFinitePresentation (i.resLE U W le_rfl) :=
    locallyOfFinitePresentation_resLE_of_finitePresentation_appLE i hU (hU.preimage i) le_rfl hfp
  have hcomp : Z.homOfLE hVU ≫ i.resLE U W le_rfl = i.resLE U V hVU := by simp [W]
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have htop := Scheme.Hom.finitePresentation_appTop (Z.homOfLE hVU ≫ i.resLE U W le_rfl)
  rw [hcomp, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at htop
  exact (finitePresentation_topIso_comp_comp_topIso_inv_iff _).1 (by simpa using htop)

/-- **[Stacks, Tag 01TV] in the ideal sheaf data idiom.** The closed subscheme cut out by a
quasi-coherent sheaf of ideals is of finite presentation over the ambient scheme if and only if
that sheaf of ideals is of finite type. -/
@[ega "IV 8.6.1"]
theorem finitePresentation_subschemeι_iff_isFiniteType {X : Scheme.{u}}
    (I : X.IdealSheafData) : FinitePresentation I.subschemeι ↔ I.IsFiniteType := by
  refine ⟨fun hI U => ?_, fun hI => ⟨?_, inferInstance, inferInstance⟩⟩
  · rw [← I.ker_subschemeι]
    exact fg_ker_ideal_of_finitePresentation I.subschemeι hI U
  · refine locallyOfFinitePresentation_of_isFiniteType_ker I.subschemeι fun U => ?_
    rw [I.ker_subschemeι]
    exact hI U

/-- The closed subscheme cut out by the inverse image of an ideal sheaf of finite presentation
is again of finite presentation: it is the base change of the original one. -/
theorem finitePresentation_comap_subschemeι {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) (hI : FinitePresentation I.subschemeι) :
    FinitePresentation (I.comap f).subschemeι := by
  have : LocallyOfFinitePresentation I.subschemeι := hI.1
  have : QuasiCompact I.subschemeι := hI.2.1
  have : QuasiSeparated I.subschemeι := hI.2.2
  refine ⟨?_, ?_, ?_⟩ <;> rw [← I.comapIso_hom_fst] <;> infer_instance

end AlgebraicGeometry

end
