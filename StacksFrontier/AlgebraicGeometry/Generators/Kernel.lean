module

public import StacksFrontier.AlgebraicGeometry.Generators.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Factorization
public import StacksFrontier.AlgebraicGeometry.DiagonalQuotientPresentation.Basic

/-!
# The affine kernel label of [Stacks, Tag 01R3], part (1)

This file closes the part (1) label "quotient by the ideal square" of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3): on an affine open `V` of a
closed-immersion factorization `i' : Z ⟶ U` of an immersion `i : Z ⟶ X`, a section `x` of the
ideal sheaf of `i'` is killed by `Stacks.Conormal.conormalQuotientMap` exactly when its image in
the structure sheaf lies in the square of `i'.ker.ideal ⟨V, hV⟩`.

## Route

With the affine quotient formula of
`StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Factorization` in hand this is three steps.

1. **A presentation exists.** `Stacks.DiagonalPresentation.exists_presentation`
   (`StacksDraft.AlgebraicGeometry.F3.DiagonalQuotientPresentation.Basic`) produces presentation
   data `(I, e, he)` over any affine open across which the morphism restricts to a closed
   immersion, from `AlgebraicGeometry.IsClosedImmersion.Spec_iff`. The tagged statement, however,
   names its ideal `i'.ker.ideal ⟨V, hV⟩`, and `Spec_iff` does not say which ideal it produced.
2. **The presentation's ideal is that one.** `Stacks.DiagonalPresentation.presentation_ideal_eq`
   pins it as `RingHom.ker` of the presented comorphism on global sections;
   `presentationIdeal_eq_ker_app` below strips the three isomorphisms off that comorphism,
   leaving `RingHom.ker (i'.app V).hom`, and Mathlib's `AlgebraicGeometry.Scheme.Hom.ker_apply`
   is exactly that for a quasi-compact morphism. The general form of this computation was
   missing: `DiagonalQuotientPresentation` carries it only at the diagonal, where an extra
   presheaf restriction map intervenes.
3. **The formula.** `Stacks.Conormal.pushforwardConormalIsoCotangent_apply` turns the quotient
   generator into `I.toCotangent` of the ambient section, `Ideal.toCotangent_eq_zero` turns
   vanishing there into membership of `I ^ 2`, and the identification is an isomorphism, hence
   injective.

## Main results

* `Stacks.Conormal.Tag01R3Generators.ΓSpecIso_inv_comp_appTop_eq'` and
  `presentationIdeal_eq_ker_app`: the presented comorphism is `i'.app V` up to three
  isomorphisms, so the presentation's ideal is `RingHom.ker (i'.app V).hom`. These are the
  general forms of `Stacks.DiagonalPresentation.ΓSpecIso_inv_comp_appTop_eq` and
  `presentationIdeal_eq_ker_diagAppLE`, which are stated only at the diagonal.
* `Stacks.Conormal.Tag01R3Generators.conormalQuotientMap_kernel`: **the tagged statement**,
  carrying the `stacks` attribute.

## Universe situation

A single universe `u`, as in the tagged statements.

## What is not done

* **No part (2) label.** See the "What is not done" section of
  `StacksFrontier.AlgebraicGeometry.Generators.Basic`.
* **Nothing global about the ideal square.** The statement is affine-local, as the tag's is; no
  sheaf-level kernel object is constructed.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.Tag01R3Generators

open Stacks.Conormal.AffineCotangent

/-- **The comorphism presented by `AlgebraicGeometry.IsClosedImmersion.Spec_iff` over an affine
open, with its three isomorphisms exposed.** For any morphism of schemes `i : Z ⟶ X` and any
affine open `V` of `X`, the comorphism of `pullback.snd i V.ι ≫ hV.isoSpec.hom` on global
sections, read through `AlgebraicGeometry.Scheme.ΓSpecIso`, is `i.app V` followed by the
`topIso` of `i ⁻¹ᵁ V` and the comorphism of `AlgebraicGeometry.pullbackRestrictIsoRestrict`.

`AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop` cancels the `ΓSpecIso` against the affine
identification, `AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict` replaces the
second projection by `i ∣_ V`, and `AlgebraicGeometry.Scheme.Hom.resLE_app_top` computes that
restriction's comorphism as an `appLE`, which is `i.app V` because the source open is the full
preimage.

This is the general form of `Stacks.DiagonalPresentation.ΓSpecIso_inv_comp_appTop_eq`, which is
stated only at the diagonal and over a chart; there the source open is not the full preimage, so
a presheaf restriction map survives that is absent here. -/
theorem ΓSpecIso_inv_comp_appTop_eq' {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) :
    (Scheme.ΓSpecIso Γ(X, V)).inv ≫
        (Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom).appTop =
      i.app V ≫ ((i ⁻¹ᵁ V).topIso.inv ≫ (pullbackRestrictIsoRestrict i V).hom.appTop) := by
  rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, Category.assoc,
    Iso.inv_hom_id_assoc, ← pullbackRestrictIsoRestrict_hom_morphismRestrict i V,
    Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.Hom.resLE_eq_morphismRestrict i (U := V), Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, Scheme.Hom.appLE_eq_app, Category.assoc]

/-- **The ideal of any presentation over an affine open is the kernel of the morphism's map on
sections there.** `ΓSpecIso_inv_comp_appTop_eq'` exhibits the presented comorphism as `i.app V`
followed by two isomorphisms, so `RingHom.ker_comp_of_injective` leaves exactly
`RingHom.ker (i.app V).hom`.

Together with `Stacks.DiagonalPresentation.presentation_ideal_eq` this names the ideal of every
presentation, and with Mathlib's `AlgebraicGeometry.Scheme.Hom.ker_apply` it identifies it with
`i.ker.ideal ⟨V, hV⟩` whenever `i` is quasi-compact. -/
theorem presentationIdeal_eq_ker_app {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) :
    RingHom.ker ((Scheme.ΓSpecIso Γ(X, V)).inv ≫
        (Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom).appTop).hom =
      RingHom.ker (i.app V).hom := by
  have hpb := Stacks.DiagonalPresentation.isIso_appTop_of_iso (pullbackRestrictIsoRestrict i V)
  rw [ΓSpecIso_inv_comp_appTop_eq' i V hV, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso
      ((i ⁻¹ᵁ V).topIso.inv ≫ (pullbackRestrictIsoRestrict i V).hom.appTop)).1]

/-- **[Stacks, Tag 01R3], part (1): the quotient is by the square of the ideal.** On an affine
open `V` of a closed-immersion factorization `i' : Z ⟶ U` of an immersion `i : Z ⟶ X`, a section
`x` of the ideal sheaf of `i'` over `V` is killed by `Stacks.Conormal.conormalQuotientMap`
exactly when its image in the structure sheaf lies in `(i'.ker.ideal ⟨V, hV⟩) ^ 2`.

The statement involves no presentation data; one is produced inside the proof by
`Stacks.DiagonalPresentation.exists_presentation` and its ideal identified with
`i'.ker.ideal ⟨V, hV⟩` by `presentationIdeal_eq_ker_app`. The vanishing is then transported
across `Stacks.Conormal.pushforwardConormalIsoCotangent` by
`Stacks.Conormal.pushforwardConormalIsoCotangent_apply` and read off by
`Ideal.toCotangent_eq_zero`. -/
@[stacks 01R3 "part (1): quotient by the ideal square"]
theorem conormalQuotientMap_kernel {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V)
    (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op V)) :
    (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op V) x = 0 ↔
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op V) x ∈
          (i'.ker.ideal ⟨V, hV⟩) ^ 2 := by
  obtain ⟨I, e, he⟩ := Stacks.DiagonalPresentation.exists_presentation i' V hV
  have hI : I = i'.ker.ideal ⟨V, hV⟩ :=
    ((Stacks.DiagonalPresentation.presentation_ideal_eq i' V hV I e he).symm.trans
      (presentationIdeal_eq_ker_app i' V hV)).trans (i'.ker_apply ⟨V, hV⟩).symm
  have hxI : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op V) x ∈ I := by
    rw [hI]
    exact (Sections.exists_idealSheaf_section_iff_mem_ker_ideal i' V hV _).1 ⟨x, rfl⟩
  have key :=
    Stacks.Conormal.pushforwardConormalIsoCotangent_apply i U i' hfac V hV I e he x hxI
  rw [← hI]
  have : IsIso (Stacks.Conormal.pushforwardConormalIsoCotangent
    i U i' hfac V hV I e he).hom := Iso.isIso_hom _
  refine Iff.trans (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Stacks.Conormal.pushforwardConormalIsoCotangent i U i' hfac V hV I e he).hom).1).symm ?_
  refine Iff.trans (Iff.of_eq (congrArg (fun w => w = 0) key)) ?_
  exact Ideal.toCotangent_eq_zero I ⟨_, hxI⟩

end Stacks.Conormal.Tag01R3Generators

end
