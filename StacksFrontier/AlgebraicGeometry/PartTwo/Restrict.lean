module

public import StacksFrontier.AlgebraicGeometry.PartTwo.Generators

/-!
# [Stacks, Tag 01R3], part (2): compatibility with restriction

This file closes the last part (2) label of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3): the affine identifications of
`StacksFrontier.AlgebraicGeometry.PartTwo.Generators` commute with restriction of the
ambient affine open.

## Route

The generator formula
`Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_inv_toCotangent` holds at *every*
closed-immersion factorization and every open of it, so it can be read at the coborder
factorization over the **smaller** open `i.coborderRange.ι ⁻¹ᵁ V` while the presentation data is
the one over `U`. That is the whole content: one section of the coborder ideal sheaf serves both
presentations.

Concretely, let `y` be the coborder section named by the restriction of `x : I` to `V`, produced
by `Stacks.Tag01R3PartTwo.exists_coborderSection` from the `V`-presentation. Then

* `AlgebraicGeometry.Scheme.Hom.map_appLE` says `y` is *also* named by `x` itself over `U` — the
  two `appLE`s differ by exactly the restriction `Γ(X, U) ⟶ Γ(X, V)` that `x` is restricted
  along. So no second section is needed, and
  `Stacks.Conormal.Locality.idealSheaf_section_injective` is not needed either.
* The generator formula at the `U`-presentation therefore sends the class of `x` to the quotient
  generator of `y`, and the generator formula at the `V`-presentation — in the form
  `Stacks.Tag01R3PartTwo.conormalAffineSectionsIsoCotangent_toCotangent` — sends that same
  quotient generator to the class of the restriction of `x`.
* The two restriction maps in between are collapsed by
  `Stacks.Conormal.Tag01R3Generators.pushforward_res` (a restriction map of a direct image is a
  restriction map of the module, between the preimage opens) and
  `Stacks.Conormal.Tag01R3Generators.res_comp`.

No affineness of `U` or `V` beyond that of the statement is used, and no hypothesis is added.

## Main results

* `Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_restrict`:
  **the statement of Tag 01R3 (part 2)**, carrying the `stacks` attribute.

## Universe situation

A single universe `u`, as in the related statements of Tag 01R3.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag01R3PartTwo

/-- **[Stacks, Tag 01R3], part (2): compatibility with restriction.** The affine identifications
commute with restriction: the class of an ideal section restricts to the class of its
restriction.

This is the generator-level naturality needed to use the affine formula to characterize
morphisms of conormal sheaves. See the module docstring for the route; the point is that
`affineConormalIsoCotangent_inv_toCotangent` is available at the coborder factorization over the
*smaller* open, so one section of the coborder ideal sheaf serves both presentations. -/
@[stacks 01R3 "part (2): compatibility with restriction"]
theorem affineConormalIsoCotangent_restrict {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U V : X.Opens) (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (I : Ideal Γ(X, U)) (J : Ideal Γ(X, V))
    (eU : Limits.pullback i U.ι ≅ Spec (.of (Γ(X, U) ⧸ I)))
    (heU : Limits.pullback.snd i U.ι ≫ hU.isoSpec.hom =
      eU.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (eV : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ J)))
    (heV : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      eV.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (x : I)
    (hx : (X.presheaf.map (homOfLE hVU).op).hom (x : Γ(X, U)) ∈ J) :
    (Stacks.Conormal.affineConormalIsoCotangent i V hV J eV heV).hom.hom
      (((modulePushforward i.toLRSHom.toShHom).obj
        (Stacks.Conormal.conormalSheaf i)).val.map (homOfLE hVU).op
          ((Stacks.Conormal.affineConormalIsoCotangent i U hU I eU heU).inv.hom
            (I.toCotangent x))) =
      J.toCotangent
        ⟨(X.presheaf.map (homOfLE hVU).op).hom (x : Γ(X, U)), hx⟩ := by
  rw [Stacks.Conormal.affineConormalIsoCotangent_eq_conormalAffineSectionsIsoCotangent
    i V hV J eV heV]
  have hWU : i.coborderRange.ι ⁻¹ᵁ V ≤ i.coborderRange.ι ⁻¹ᵁ U :=
    i.coborderRange.ι.preimage_mono hVU
  obtain ⟨y, hy⟩ := exists_coborderSection i V hV J eV heV
    (⟨(X.presheaf.map (homOfLE hVU).op).hom (x : Γ(X, U)), hx⟩ : J)
  have hyU : (i.coborderRange.ι.appLE U (i.coborderRange.ι ⁻¹ᵁ V) hWU).hom (x : Γ(X, U)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
          (.op (i.coborderRange.ι ⁻¹ᵁ V)) y :=
    (congr($(Scheme.Hom.map_appLE i.coborderRange.ι (U := V)
      (V := i.coborderRange.ι ⁻¹ᵁ V) le_rfl (homOfLE hVU).op) (x : Γ(X, U)))).symm.trans hy
  have hgen := affineConormalIsoCotangent_inv_toCotangent i U hU I eU heU
    i.coborderRange i.liftCoborder i.liftCoborder_ι (i.coborderRange.ι ⁻¹ᵁ V) hWU x y hyU
  refine Eq.trans (congrArg
    (fun z => (Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent
      i V hV J eV heV).hom.hom z) ?_)
    (conormalAffineSectionsIsoCotangent_toCotangent i V hV J eV heV
      (⟨(X.presheaf.map (homOfLE hVU).op).hom (x : Γ(X, U)), hx⟩ : J) y hy)
  refine Eq.trans (Stacks.Conormal.Tag01R3Generators.pushforward_res i
    (Stacks.Conormal.conormalSheaf i) (homOfLE hVU) (homOfLE (i.preimage_mono hVU)) _) ?_
  refine Eq.trans (Stacks.Conormal.Tag01R3Generators.res_comp
    (Stacks.Conormal.conormalSheaf i)
    (homOfLE (show i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V) ≤ i ⁻¹ᵁ U from
      (le_of_eq (preimage_eq_liftCoborder_preimage i V).symm).trans (i.preimage_mono hVU)))
    (eqToHom (preimage_eq_liftCoborder_preimage i V))
    (homOfLE (i.preimage_mono hVU)) _).symm ?_
  exact congrArg (fun z => ((Stacks.Conormal.conormalSheaf i).val.map
    (eqToHom (preimage_eq_liftCoborder_preimage i V)).op).hom z) hgen

end Stacks.Tag01R3PartTwo

end
