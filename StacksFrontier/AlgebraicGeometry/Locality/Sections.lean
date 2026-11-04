module

public import StacksFrontier.AlgebraicGeometry.Locality.Basic

/-!
# The part (2) identification of [Stacks, Tag 01R3] on a quotient generator, at both shapes

`StacksFrontier.AlgebraicGeometry.Locality.Basic` discharges the hypothesis `hc` of
`Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply` at both shapes of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)'s part (2). This file feeds each of
them to the engine, so that the two identifications

* `Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent` and
* `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent`

each carry a formula on the generators of [Stacks, Tag 01R3]: the quotient generator
`Stacks.Conormal.conormalQuotientMap` of a section `y₀` of the ideal sheaf of the factorization
goes to `Ideal.toCotangent a`, for the ambient ideal element `a` naming `y₀`.

## Main results

* `Stacks.Tag08S2Locality.pushforwardConormalSectionsIsoCotangent_apply`: the generator formula at
  an affine open of the *factorization's target*.
* `Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply`: the generator formula at an
  affine open of the *ambient scheme* — the shape
  `StacksFrontier.AlgebraicGeometry.DiagonalQuotientPresentation.Basic` instantiates at the
  diagonal of a morphism of schemes.

Both are the engine's `affineSectionsIsoCotangent_apply` with its `hc` argument supplied, and
nothing else; the remaining hypotheses `hxy` and `hax` are the engine's own, and they are the
affine-model bookkeeping described below.

## What is not done, precisely

Two of the engine's arguments are *not* discharged here:

1. **The affine model's section `x` is still an argument, with `hax` as its characterization.**
   `StacksFrontier.AlgebraicGeometry.Locality.Model` removes both: `x` exists for every
   `a : I`, by the general criterion
   `Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff` or directly from
   `Stacks.ClosedImmersion.IdealSheafAffine.exists_tilde_iso_kernel_quotUnitHom`. Use the
   `_of_mem` forms there in preference to the two theorems below.
2. **`hxy` is unverified at any concrete immersion.** It says the section `y` of the ideal sheaf of
   `i ∣_ V` and the affine model's `x` have the same image in the structure sheaf, up to the
   comorphism of `AlgebraicGeometry.IsAffineOpen.isoSpec`. At the diagonal, with
   `a = p₂^♯ b − p₁^♯ b`, that is a computation on the structure sheaf only;
   `Stacks.Conormal.AffineShape.appLE_eq_ΓSpecIso_inv` is the lemma routing
   `(Scheme.ΓSpecIso Γ(X, V)).inv` through `Spec` for it, and
   `Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι` together with
   `Stacks.LeibnizDerivation.ι_deltaIdealSection` are the two ends it has to meet. This is the
   whole frontier of [Stacks, Tag 08S2] that remains on the sheaf side.

Beyond those, [Stacks, Tag 08S2] needs the module-structure step
(`Stacks.LeibnizDerivation.surjective_diagRes_appTop`) and then
`Stacks.LeibnizDerivation.existsUnique_affineConormalIsoKaehler_iff_isIso`.

**No `stacks` attribute is attached.** The part (2) assertions of [Stacks, Tag 01R3] are the
projection of a subtype quantified over *all* closed-immersion factorizations and all opens; the
formulas here are at one factorization and one open at a time, and nothing says two factorizations
give the same answer. No clause of [Stacks, Tag 08S2] is stated.

## Universe situation

A single universe `u`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag08S2Locality

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **The generator formula for
`Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent`.** For an immersion
`i : Z ⟶ X`, a closed-immersion factorization `i' : Z ⟶ U` of it, and the part (2) presentation
data at an affine open `V` of `U`, the identification of the sections over `V` of `i' _* C(i)`
with `I.Cotangent` carries the quotient generator of a section `y₀` of the ideal sheaf of `i'`
over `V` to `I.toCotangent a`, where `a ∈ I` names the affine model's matching section `x`.

This is `Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply` with its `hc`
argument supplied by `hc_conormalSheafRestrictIso`; `hxy` and `hax` are the engine's own
hypotheses, and the module docstring says which of them remain open. -/
theorem pushforwardConormalSectionsIsoCotangent_apply
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(U.toScheme, V))
    (e : Limits.pullback i' V.ι ≅ Spec (.of (Γ(U.toScheme, V) ⧸ I)))
    (he : Limits.pullback.snd i' V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I)
    (x : Γ(Stacks.ClosedImmersion.idealSheaf
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom, ⊤))
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op V))
    (hxy : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (i' ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom
            (((Stacks.Conormal.Restriction.restrictIdealSheafIso' i' V).hom.val.app
                (.op ⊤)).hom
              (((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
                (homOfLE (Scheme.Opens.ι_image_top V).le).op).hom y₀)) =
          ((SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom hV.isoSpec.hom.toLRSHom.toShHom)).val.app (.op ⊤)).hom
            (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
                )).val.app (.op ⊤)).hom x))
    (hax : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
            )).val.app (.op ⊤)).hom x =
      (Scheme.ΓSpecIso Γ(U.toScheme, V)).inv (a : Γ(U.toScheme, V))) :
    (Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent
          i U i' hfac V hV I e he).hom.hom
        (((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op V)).hom y₀) =
      I.toCotangent a :=
  Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply
    i' (Stacks.Conormal.conormalSheaf i) V hV I e he
    (Stacks.Conormal.Locality.conormalSheafRestrictIso i U i' hfac V) a x _ _ hxy hax
    (hc_conormalSheafRestrictIso i U i' hfac V y₀)

/-- **The generator formula for
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent`.** For an immersion
`i : Z ⟶ X` and the part (2) presentation data at an affine open `V` of the *ambient* scheme, the
identification of the sections over `V` of `i _* C(i)` with `I.Cotangent` carries the quotient
generator, taken at the defining coborder factorization over the open
`i.coborderRange.ι ⁻¹ᵁ V`, to `I.toCotangent a`.

This is the shape `StacksFrontier.AlgebraicGeometry.DiagonalQuotientPresentation.Basic`
instantiates at the diagonal of a morphism of schemes, and whose missing generator formula that
file's "What is not done" section names as the missing ingredient for [Stacks, Tag 08S2]. The
hypothesis `hy` pins down the section of the ideal sheaf of `i ∣_ V` that the generator is carried
to, through its image in the structure sheaf; `hxy` and `hax` are the engine's own, as above. -/
theorem conormalAffineSectionsIsoCotangent_apply
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (hVeq : i ⁻¹ᵁ V = i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V))
    (a : I)
    (x : Γ(Stacks.ClosedImmersion.idealSheaf
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom, ⊤))
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
            (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
                )).val.app (.op ⊤)).hom x))
    (hax : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)
            )).val.app (.op ⊤)).hom x =
      (Scheme.ΓSpecIso Γ(X, V)).inv (a : Γ(X, V))) :
    (Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent
          i V hV I e he).hom.hom
        (((Stacks.Conormal.conormalSheaf i).val.map (eqToHom hVeq).op).hom
          (((Stacks.Conormal.conormalQuotientMap i i.coborderRange i.liftCoborder
            i.liftCoborder_ι).val.app (.op (i.coborderRange.ι ⁻¹ᵁ V))).hom y₀)) =
      I.toCotangent a :=
  Stacks.Conormal.CotangentAppIsoGenerator.affineSectionsIsoCotangent_apply
    i (Stacks.Conormal.conormalSheaf i) V hV I e he
    (Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe i i.coborderRange i.liftCoborder
      i.liftCoborder_ι V
      (Stacks.Conormal.AffineCotangent.le_coborderRange_of_isoSpecQuotient i V hV I e he))
    a x y _ hxy hax
    (hc_conormalSheafRestrictIsoOfLe i i.coborderRange i.liftCoborder i.liftCoborder_ι V
      (Stacks.Conormal.AffineCotangent.le_coborderRange_of_isoSpecQuotient i V hV I e he)
      hVeq y₀ y hy)

end Stacks.Tag08S2Locality

end
