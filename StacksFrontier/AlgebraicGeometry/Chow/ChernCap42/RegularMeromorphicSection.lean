module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSection
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSheafComparison.Stalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators
public import StacksFrontier.AlgebraicGeometry.Meromorphic.TotalQuotientSheafStalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regularity of a meromorphic section with nowhere vanishing germs

Let `X` be an integral scheme and let `L` be an `𝒪_X`-module. A meromorphic section of `L` is a
global section `σ` of the sheaf `𝒦_X(L)`, and it is *regular* in the sense of
[Stacks, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX) when multiplication by it embeds
the sheaf `𝒦_X` of meromorphic functions in `𝒦_X(L)`. This file proves that on an integral
scheme a meromorphic section whose germ is nonzero at every point is regular.

## Main results

* `Stacks.ChernCap42.isUnit_of_ne_zero_stalk_totalQuotientSheaf` — on an integral scheme every
  nonzero germ of a meromorphic function is a unit.
* `Stacks.ChernCap42.isRegularMeromorphicSection_of_germ_ne_zero` — a meromorphic section with
  nowhere vanishing germs is regular.
* `Stacks.ChernCap42.isRegularMeromorphicSection_of_ne_zero` — the canonical meromorphic image
  of a nonzero global section of an invertible module on an integral scheme is a regular
  meromorphic section.

## References

* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.ChernCap42

/-- On an integral scheme every nonzero germ of a meromorphic function is a unit. -/
@[ega "IV 20.1.8" "special case"]
theorem isUnit_of_ne_zero_stalk_totalQuotientSheaf (X : Scheme.{u}) [IsIntegral X] (x : X)
    {r : ↑(X.totalQuotientSheaf.presheaf.stalk x)} (hr : r ≠ 0) : IsUnit r := by
  let _ : Algebra ↑(X.presheaf.stalk x) ↑(X.totalQuotientSheaf.presheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      X.toTotalQuotientSheaf.hom).hom.toAlgebra
  have _ : IsFractionRing ↑(X.presheaf.stalk x) ↑(X.totalQuotientSheaf.presheaf.stalk x) :=
    stalk_totalQuotientSheaf_isFractionRing_of_weaklyAssociated X
      (le_of_eq (weaklyAssociatedPointsOfScheme_eq_genericPoints X))
      (fun U _ => Stacks.Divisors.finite_irreducibleComponents_opens X U) x
  obtain ⟨b, hb⟩ :=
    (@Field.toIsField _ (IsFractionRing.toField ↑(X.presheaf.stalk x))).mul_inv_cancel hr
  exact IsUnit.of_mul_eq_one b hb

/-- Multiplication by a meromorphic section acts on the sections over an open set as the scalar
action of the sheaf of meromorphic functions. -/
private theorem unitHomEquiv_symm_val_app_apply {X : Scheme.{u}} (L : X.Modules)
    (σ : AlgebraicGeometry.MeromorphicSection X.sheaf L) (V : (Opens X)ᵒᵖ)
    (z : ↑((Stacks.Sheaves.Differentials.ringSheaf (totalQuotientSheaf X.sheaf)).obj.obj V)) :
    (((AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm σ).val.app V).hom z =
      z • σ.eval V := rfl

/-- On an integral scheme a meromorphic section with nowhere vanishing germs is regular. -/
theorem isRegularMeromorphicSection_of_germ_ne_zero (X : Scheme.{u}) [IsIntegral X]
    (L : X.Modules) (σ : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hσ : ∀ x : X, Stacks.ModuleStalk.germ
      (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val ⊤ x trivial
        (σ.eval (op ⊤)) ≠ 0) :
    AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L σ := by
  refine CategoryTheory.SheafOfModules.mono_of_forall_app_injective _ fun V z z' hzz' => ?_
  have hz := (unitHomEquiv_symm_val_app_apply L σ V z).symm.trans
    (hzz'.trans (unitHomEquiv_symm_val_app_apply L σ V z'))
  refine TopCat.Presheaf.section_ext X.totalQuotientSheaf V.unop z z' fun x hx => ?_
  have hsec : Stacks.ModuleStalk.res
      (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val (le_top (a := V.unop))
        (σ.eval (op ⊤)) = σ.eval V :=
    PresheafOfModules.sections_property σ (homOfLE (le_top (a := V.unop))).op
  have hres : Stacks.ModuleStalk.germ
      (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val V.unop x hx (σ.eval V) =
      Stacks.ModuleStalk.germ
        (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val ⊤ x trivial
          (σ.eval (op ⊤)) := by
    rw [← hsec]
    exact Stacks.ModuleStalk.germ_res _ le_top hx _
  have hgs : ∀ w : ↑((Stacks.Sheaves.Differentials.ringSheaf (totalQuotientSheaf X.sheaf)).obj.obj
    V),
      Stacks.ModuleStalk.germ (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val
          V.unop x hx (w • σ.eval V) =
        X.totalQuotientSheaf.presheaf.germ V.unop x hx w •
          Stacks.ModuleStalk.germ (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val
            V.unop x hx (σ.eval V) :=
    fun w => Stacks.ModuleStalk.presheafGerm_smul _ hx w _
  have hgerm := congrArg
    (Stacks.ModuleStalk.germ
      (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val V.unop x hx) hz
  rw [hgs z, hgs z', hres] at hgerm
  by_contra hne
  refine hσ x (((isUnit_of_ne_zero_stalk_totalQuotientSheaf X x (sub_ne_zero.mpr hne)).smul_eq_zero
    (M := ↑((Stacks.ModuleStalk.presheafOn
      (AlgebraicGeometry.meromorphicSectionSheaf X.sheaf L).val).stalk x))).mp ?_)
  rw [sub_smul, hgerm, sub_self]

/-- On an integral scheme the canonical meromorphic image of a nonzero global section of an
invertible module is a regular meromorphic section. -/
theorem isRegularMeromorphicSection_of_ne_zero (X : Scheme.{u}) [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L
      (meromorphicSectionOfSection L s) :=
  isRegularMeromorphicSection_of_germ_ne_zero X L (meromorphicSectionOfSection L s)
    fun x => germ_meromorphicSectionOfSection_ne_zero L s hs x ⊤ trivial

end Stacks.ChernCap42

end
