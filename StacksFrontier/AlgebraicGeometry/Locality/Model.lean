module

public import StacksFrontier.AlgebraicGeometry.Locality.Sections
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.AffineModel

/-!
# Naming the affine model's section by an ideal element

`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` is stated as "for every `a : I` and
every section `x` of the affine model's ideal sheaf over `⊤` whose image in the structure sheaf is
`(AlgebraicGeometry.Scheme.ΓSpecIso R).inv a`, …", and
`Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply` inherits both `x` and
that hypothesis `hax`. This file produces `x` from `a`, and so removes the pair from the two
generator formulas of
`StacksFrontier.AlgebraicGeometry.Locality.Sections`.

## Main results

* `Stacks.Tag08S2Locality.exists_idealSheafSection`: for every `a : I` there is a section of the
  ideal sheaf of `Spec (R ⧸ I) ⟶ Spec R` over `⊤` whose image in the structure sheaf is
  `(Scheme.ΓSpecIso R).inv a`.
* `Stacks.Tag08S2Locality.pushforwardConormalSectionsIsoCotangent_apply_of_mem` and
  `Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_mem`: the two generator
  formulas with `x` and `hax` eliminated. What is left of the affine-model bookkeeping is a single
  hypothesis naming the image of `y` in the structure sheaf by the ideal element `a`.

## Implementation notes

Such an `x` is also produced from `a` by a general criterion,
`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff`,
which for *any* morphism of schemes says a section `r` of the structure sheaf over `O` is the
image of a section of the ideal sheaf exactly when `f.app O r = 0` —
`Stacks.LeibnizDerivation.idealSection` and `ι_idealSection` are the bundled form, used at the
diagonal. What is stated here is its instance at the affine model.

The proof below does not use that criterion: the affine model's
ideal sheaf *is* `I^~` by
`Stacks.ClosedImmersion.IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom`, compatibly with
the two inclusions into `𝒪_{Spec R}`, so the section is the image of `a` under
`AlgebraicGeometry.tilde.toOpen` and the compatibility is the whole computation
(`AlgebraicGeometry.tilde.toOpen_map_app`, with `toOpen` at `⊤` on `R` being
`(Scheme.ΓSpecIso R).inv` by `rfl`).

## What is not done

* **No clause of [Stacks, Tag 01R3] or [Stacks, Tag 08S2] is discharged, and no `stacks`
  attribute is attached.** The remaining hypothesis of each generator formula, `hxy`, is
  unverified at any concrete immersion; at the diagonal of a morphism of schemes it is a
  computation in the structure sheaf alone, between
  `Stacks.LeibnizDerivation.ι_deltaIdealSection` on one side and
  `Stacks.Conormal.AffineShape.appLE_eq_ΓSpecIso_inv` on the other.
* **Nothing about the module-structure step**
  (`Stacks.LeibnizDerivation.surjective_diagRes_appTop`) or about
  `Stacks.LeibnizDerivation.existsUnique_affineConormalIsoKaehler_iff_isIso`.

## Universe situation

A single universe `u`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace Stacks.Tag08S2Locality

/-- **The affine model's ideal-sheaf section named by an element of the ideal.** For an ideal `I`
of a commutative ring `R` and `a : I`, there is a global section of the ideal sheaf of
`Spec (R ⧸ I) ⟶ Spec R` whose image in the structure sheaf is `(Scheme.ΓSpecIso R).inv a`.

This is the hypothesis `hax` of
`Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply` made satisfiable. The
section is `AlgebraicGeometry.tilde.toOpen` of `a`, carried along the identification of the ideal
sheaf with `I^~`; the compatibility clause of
`Stacks.ClosedImmersion.IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom` is read on global
sections and `AlgebraicGeometry.tilde.toOpen_map_app` finishes it, `toOpen` at `⊤` on the module
`R` being `(Scheme.ΓSpecIso R).inv` by `rfl`
(`Stacks.Conormal.AffineModel.toOpen_top_eq_ΓSpecIso_inv`). -/
theorem exists_idealSheafSection (R : CommRingCat.{u}) (I : Ideal R) (a : I) :
    ∃ x : (Stacks.ClosedImmersion.idealSheaf
        (Spec.map (quotHom I)).toLRSHom.toShHom).val.obj (.op ⊤),
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (Spec.map (quotHom I)).toLRSHom.toShHom))).val.app (.op ⊤)).hom x =
        (Scheme.ΓSpecIso R).inv (a : R) := by
  obtain ⟨e, he⟩ := exists_tilde_iso_kernel_quotUnitHom I
  refine ⟨(e.hom.val.app (.op ⊤)).hom (tilde.toOpen (ModuleCat.of R I) ⊤ a), ?_⟩
  refine Eq.trans (ConcreteCategory.congr_hom (congr($(he).val.app (.op ⊤)))
    ((tilde.toOpen (ModuleCat.of R I) ⊤).hom a)) ?_
  exact congr($(tilde.toOpen_map_app (ModuleCat.ofHom (Submodule.subtype I)) ⊤).hom a)

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- `pushforwardConormalSectionsIsoCotangent_apply` with the affine model's section eliminated by
`exists_idealSheafSection`: the only affine-model datum left is the naming of the image of the
section of the ideal sheaf of `i' ∣_ V` by `a : I`. -/
theorem pushforwardConormalSectionsIsoCotangent_apply_of_mem
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(U.toScheme, V))
    (e : Limits.pullback i' V.ι ≅ Spec (.of (Γ(U.toScheme, V) ⧸ I)))
    (he : Limits.pullback.snd i' V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I)
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op V))
    (hxy : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (i' ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom
            (((Stacks.Conormal.Restriction.restrictIdealSheafIso' i' V).hom.val.app
                (.op ⊤)).hom
              (((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
                (homOfLE (Scheme.Opens.ι_image_top V).le).op).hom y₀)) =
          ((SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom hV.isoSpec.hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
            ((Scheme.ΓSpecIso Γ(U.toScheme, V)).inv (a : Γ(U.toScheme, V)))) :
    (Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent
          i U i' hfac V hV I e he).hom.hom
        (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op V)).hom y₀) =
      I.toCotangent a := by
  obtain ⟨x, hax⟩ := exists_idealSheafSection Γ(U.toScheme, V) I a
  exact pushforwardConormalSectionsIsoCotangent_apply i U i' hfac V hV I e he a x y₀
    (hxy.trans (congrArg _ hax.symm)) hax

/-- `conormalAffineSectionsIsoCotangent_apply` with the affine model's section eliminated by
`exists_idealSheafSection`. This is the shape
`StacksFrontier.AlgebraicGeometry.DiagonalQuotientPresentation.Basic` needs at the diagonal: the
two remaining hypotheses are both statements in the structure sheaf about the section of the ideal
sheaf of `i ∣_ V` that the quotient generator of `y₀` is carried to. -/
theorem conormalAffineSectionsIsoCotangent_apply_of_mem
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (hVeq : i ⁻¹ᵁ V = i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V))
    (a : I)
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
      (.op (i.coborderRange.ι ⁻¹ᵁ V)))
    (y : (Stacks.ClosedImmersion.idealSheaf (i ∣_ V).toLRSHom.toShHom).val.obj (.op ⊤))
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
            (i ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom y))
    (hxy : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (i ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom y =
          ((SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom hV.isoSpec.hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
            ((Scheme.ΓSpecIso Γ(X, V)).inv (a : Γ(X, V)))) :
    (Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent
          i V hV I e he).hom.hom
        (((Stacks.Conormal.conormalSheaf i).val.map (eqToHom hVeq).op).hom
          (((Stacks.Conormal.conormalQuotientMap i i.coborderRange i.liftCoborder
            i.liftCoborder_ι).val.app (.op (i.coborderRange.ι ⁻¹ᵁ V))).hom y₀)) =
      I.toCotangent a := by
  obtain ⟨x, hax⟩ := exists_idealSheafSection Γ(X, V) I a
  exact conormalAffineSectionsIsoCotangent_apply i V hV I e he hVeq a x y₀ y hy
    (hxy.trans (congrArg _ hax.symm)) hax

end Stacks.Tag08S2Locality

end
