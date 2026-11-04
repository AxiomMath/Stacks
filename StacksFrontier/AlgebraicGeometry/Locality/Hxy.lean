module

public import StacksFrontier.AlgebraicGeometry.Locality.Model
public import StacksFrontier.AlgebraicGeometry.Generators.Basic

/-!
# The engine's affine-model comparison `hxy`, for an arbitrary immersion

`Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply` takes two hypotheses
about the affine model: `hax`, naming the model's section by an element of the ideal, and `hxy`,
saying that the section `y` of the ideal sheaf of `j ∣_ V` and the model's section have the same
image in the structure sheaf up to the comorphism of
`AlgebraicGeometry.IsAffineOpen.isoSpec`. `StacksFrontier.AlgebraicGeometry.Locality.Model`
removes `hax`; this file removes `hxy`, for **any** morphism of schemes and any affine open.

## Main results

* `Stacks.Tag08S2Locality.hxy_of_image`: for a morphism `i : Z ⟶ X`, an affine open `V` of `X` and
  a section `x₀` of the ideal sheaf of `i` over `V` whose image in the structure sheaf is `a`, the
  section `Stacks.Conormal.Tag01R3Generators.restrictIdealSectionTop i V x₀` of the ideal sheaf of
  `i ∣_ V` satisfies the engine's `hxy` at `a`.
* `Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_image`: the generator formula
  for `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` with **only one
  hypothesis left** — `hy`, which compares the quotient generator's section at the coborder
  factorization with `x₀` through the structure sheaf.

## Route

Both halves were already in the tree and nothing new is proved about ideal sheaves:

* `Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop` computes the image in the
  structure sheaf of the transported section, for an arbitrary morphism — it is
  `AlgebraicGeometry.Scheme.Opens.topIso` of the image of `x₀`;
* `AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop` says the comorphism on the right-hand side
  of `hxy` is `(AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, V)).hom` followed by that same `topIso`, so
  the `ΓSpecIso` cancels against the `(Scheme.ΓSpecIso Γ(X, V)).inv` that `hax` introduced and the
  two sides are the same `topIso` image.

`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit_val_app_apply` is what makes the
right-hand side a comorphism on sections at all, and it holds by `rfl` in Mathlib.

## What is not done

* **No clause of [Stacks, Tag 01R3] or [Stacks, Tag 08S2] is discharged and no `stacks` attribute
  is attached.** `conormalAffineSectionsIsoCotangent_apply_of_image` still carries `hy`, and
  carries it at the *generic* immersion; it is not verified at the diagonal.
* **`hy` at the diagonal is the remaining sheaf-side step for [Stacks, Tag 08S2].** With
  `i = pullback.diagonal f` and `V = Stacks.LeibnizDerivation.ambientChart f U` the open
  `i.coborderRange.ι ⁻¹ᵁ V` is `Stacks.LeibnizDerivation.chart f U` by `rfl`
  (`coborderRange_ι_preimage_ambientChart`) and `y₀` is
  `Stacks.LeibnizDerivation.deltaIdealSection f U b`, whose image in the structure sheaf is
  `Stacks.LeibnizDerivation.deltaAt f U b` by `ι_deltaIdealSection`; so `hy` there is an identity
  between two restriction-and-comorphism images of that one section, with
  `image_restrictIdealSectionTop` available on both sides.
* **Nothing about the module-structure step**
  (`Stacks.LeibnizDerivation.surjective_diagRes_appTop`) or
  `Stacks.LeibnizDerivation.existsUnique_affineConormalIsoKaehler_iff_isIso`.

## Universe situation

A single universe `u`, as in the tagged statements.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag08S2Locality

/-- **The engine's affine-model comparison `hxy`, for an arbitrary morphism of schemes.** If a
section `x₀` of the ideal sheaf of `i` over an affine open `V` has image `a` in the structure
sheaf, then the section of the ideal sheaf of `i ∣_ V` obtained from it by
`Stacks.Conormal.Tag01R3Generators.restrictIdealSectionTop` has the same image in the structure
sheaf as the affine model's section named by `a`, up to the comorphism of
`AlgebraicGeometry.IsAffineOpen.isoSpec`.

See the module docstring: the left side is `topIso` of `a` by
`Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop`, and so is the right side by
`AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop`, the two `ΓSpecIso`s cancelling. -/
theorem hxy_of_image {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(X, V)) (a : I)
    (x₀ : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (.op V))
    (hx₀ : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.toLRSHom.toShHom))).val.app (.op V)).hom x₀ = (a : Γ(X, V))) :
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (i ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom
        (Stacks.Conormal.Tag01R3Generators.restrictIdealSectionTop i V x₀) =
      ((SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom hV.isoSpec.hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
        ((Scheme.ΓSpecIso Γ(X, V)).inv (a : Γ(X, V))) := by
  refine Eq.trans (Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop i V x₀) ?_
  rw [hx₀]
  have h2 : ((SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom hV.isoSpec.hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
      ((Scheme.ΓSpecIso Γ(X, V)).inv (a : Γ(X, V))) =
      (hV.isoSpec.hom.appTop).hom ((Scheme.ΓSpecIso Γ(X, V)).inv (a : Γ(X, V))) := rfl
  rw [h2, IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply]
  exact congrArg V.topIso.inv.hom
    ((Scheme.ΓSpecIso Γ(X, V)).inv_hom_id_apply (a : Γ(X, V))).symm

/-- **The generator formula for
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent`, with the affine model
eliminated.** Only `hy` is left: the comparison, through the structure sheaf, of the section `y₀`
of the ideal sheaf of the coborder factorization with the section `x₀` of the ideal sheaf of `i`
over `V`.

This is the shape [Stacks, Tag 08S2] consumes, through
`StacksDraft.AlgebraicGeometry.F3.DiagonalQuotientPresentation.Basic`. `hc` is
`hc_conormalSheafRestrictIsoOfLe`, `hax` is `exists_idealSheafSection` and `hxy` is
`hxy_of_image`; what remains for Tag 08S2 is `hy` at the diagonal and the module-structure step,
as the module docstring records. -/
theorem conormalAffineSectionsIsoCotangent_apply_of_image {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (hVeq : i ⁻¹ᵁ V = i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V))
    (a : I)
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
      (.op (i.coborderRange.ι ⁻¹ᵁ V)))
    (x₀ : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (.op V))
    (hx₀ : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.toLRSHom.toShHom))).val.app (.op V)).hom x₀ = (a : Γ(X, V)))
    (hy : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (i.liftCoborder ∣_ (i.coborderRange.ι ⁻¹ᵁ V)).toLRSHom.toShHom))).val.app
            (.op ⊤)).hom
          (((Stacks.Conormal.Restriction.restrictIdealSheafIso' i.liftCoborder
              (i.coborderRange.ι ⁻¹ᵁ V)).hom.val.app (.op ⊤)).hom
            (((Stacks.ClosedImmersion.idealSheaf
              i.liftCoborder.toLRSHom.toShHom).val.map
              (homOfLE (Scheme.Opens.ι_image_top
                (i.coborderRange.ι ⁻¹ᵁ V)).le).op).hom y₀)) =
        ((SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (Scheme.Opens.isoOfLE
              (Stacks.Conormal.AffineCotangent.le_coborderRange_of_isoSpecQuotient
                i V hV I e he)).hom.toLRSHom.toShHom)).val.app
            (.op ⊤)).hom
          (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (i ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom
            (Stacks.Conormal.Tag01R3Generators.restrictIdealSectionTop i V x₀))) :
    (Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent
          i V hV I e he).hom.hom
        (((Stacks.Conormal.conormalSheaf i).val.map (eqToHom hVeq).op).hom
          (((Stacks.Conormal.conormalQuotientMap i i.coborderRange i.liftCoborder
            i.liftCoborder_ι).val.app (.op (i.coborderRange.ι ⁻¹ᵁ V))).hom y₀)) =
      I.toCotangent a :=
  conormalAffineSectionsIsoCotangent_apply_of_mem i V hV I e he hVeq a y₀
    (Stacks.Conormal.Tag01R3Generators.restrictIdealSectionTop i V x₀) hy
    (hxy_of_image i V hV I a x₀ hx₀)

end Stacks.Tag08S2Locality

end
