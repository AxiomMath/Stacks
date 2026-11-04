module

public import StacksFrontier.AlgebraicGeometry.Locality.Hxy
public import StacksFrontier.AlgebraicGeometry.ConormalOpenFactorizations.Compatibility
public import StacksFrontier.AlgebraicGeometry.Generators.Kernel

/-!
# The inputs of [Stacks, Tag 01R3] part (2), at the coborder factorization

`StacksFrontier.AlgebraicGeometry.Locality.Hxy` reduces the part (2) generator formula of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) — the formula for
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` — to a single hypothesis
`hy`, a comparison in the structure sheaf between the section of the coborder ideal sheaf
carrying the quotient generator and a section of the ideal sheaf of `i` over `V`. This file
discharges `hy`, and with it every remaining hypothesis of that formula.

## Route

Three ingredients, two of which are bookkeeping and one of which was genuinely owed.

1. **The presentation's ideal is the kernel of `i.app V`.** This is
   `Stacks.Conormal.Tag01R3Generators.presentationIdeal_eq_ker_app` composed with
   `Stacks.DiagonalPresentation.presentation_ideal_eq`; both hold for an arbitrary morphism of
   schemes. So `a : I` restricts to zero on the fibre, and
   `Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff` then produces both
   sections the formula needs: one of the ideal sheaf of `i` over `V`, and one of the ideal sheaf
   of `i.liftCoborder` over `i.coborderRange.ι ⁻¹ᵁ V`.
2. **The image of a transported ideal-sheaf section.** `image_restrictIso'` below is the general
   form of the computation inside
   `Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop`: the image in the structure
   sheaf of a restricted section carried across
   `Stacks.Conormal.Restriction.restrictIdealSheafIso'` is the image of the section, restricted
   and read through `AlgebraicGeometry.Scheme.Hom.appIso`.
3. **The one new identity: the two routes from `Γ(X, V)` to `Γ((C.ι ⁻¹ᵁ V).toScheme, ⊤)` agree**
   (`appIso_res_appLE_eq_isoOfLE_appTop`), for `V ≤ C` opens of `X`. One route restricts along
   `C.ι` and then down to the top open of `C.ι ⁻¹ᵁ V`; the other is `topIso` followed by the
   comorphism of `AlgebraicGeometry.Scheme.Opens.isoOfLE`. Both are
   `AlgebraicGeometry.Scheme.Hom.appLE` of the *same* morphism `(C.ι ⁻¹ᵁ V).toScheme ⟶ X`, by
   `AlgebraicGeometry.Scheme.Opens.isoOfLE_hom_ι`, so
   `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` on each side and
   `Stacks.DiagonalConormal.appLE_congr` between them finish it. The passage from
   `appLE` to the spellings the hypothesis is stated in is
   `AlgebraicGeometry.Scheme.Opens.ι_appLE` on two factors and
   `AlgebraicGeometry.Scheme.Hom.appLE_eq_app` on the third.

## Main results

* `Stacks.Tag01R3PartTwo.mem_ker_app_of_mem`: an element of the presentation's ideal restricts to
  zero on the fibre.
* `Stacks.Tag01R3PartTwo.exists_idealSection` and
  `Stacks.Tag01R3PartTwo.exists_coborderSection`: the two sections named by `a : I`.
* `Stacks.Tag01R3PartTwo.appIso_res_appLE_eq_isoOfLE_appTop`: the structure-sheaf identity.
* `Stacks.Tag01R3PartTwo.hy_of_names`: the engine's `hy`, from the two naming hypotheses.
* `Stacks.Tag01R3PartTwo.conormalAffineSectionsIsoCotangent_toCotangent`: **the part (2) generator
  formula at the coborder factorization with every hypothesis discharged.** Only the presentation
  data `(I, e, he)` of the tagged statement and a section of the coborder ideal sheaf named by `a : I` remain.

## Universe situation

A single universe `u`, as in the tagged statements.

## What is not done here

No `stacks` attribute is attached in this file; the part (2) labels of the tag are stated in
`StacksFrontier.AlgebraicGeometry.PartTwo.Generators`, which quantifies this formula over
all closed-immersion factorizations using
`Stacks.Conormal.OpenFactorizations.generator_eq_of_two_factorizations`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag01R3PartTwo

/-- **An element of a presentation's ideal restricts to zero on the fibre.**
`Stacks.DiagonalPresentation.presentation_ideal_eq` identifies `I` with the kernel of the
comorphism `AlgebraicGeometry.IsClosedImmersion.Spec_iff` presents, and
`Stacks.Conormal.Tag01R3Generators.presentationIdeal_eq_ker_app` strips the three isomorphisms off
that comorphism, leaving `RingHom.ker (i.app V).hom`. Both hold for an arbitrary morphism of
schemes. -/
theorem mem_ker_app_of_mem {Z X : Scheme.{u}} (i : Z ⟶ X)
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I) : (i.app V).hom (a : Γ(X, V)) = 0 :=
  ((Stacks.DiagonalPresentation.presentation_ideal_eq i V hV I e he).symm.trans
    (Stacks.Conormal.Tag01R3Generators.presentationIdeal_eq_ker_app i V hV)) ▸ a.2

/-- **The image in the structure sheaf of a restricted ideal-sheaf section carried across
`Stacks.Conormal.Restriction.restrictIdealSheafIso'`.** It is the image of the section, restricted
to the image open and read through `AlgebraicGeometry.Scheme.Hom.appIso`.

This is the general form of the computation inside
`Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop`, which is the instance at
`W = ⊤` composed with the move along `AlgebraicGeometry.Scheme.Opens.ι_preimage_self`. -/
theorem image_restrictIso' {A B : Scheme.{u}} (f : A ⟶ B) (O : B.Opens)
    (W : O.toScheme.Opens) (h : O.ι ''ᵁ W ≤ O)
    (y : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op O)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (f ∣_ O).toLRSHom.toShHom))).val.app (.op W)
        ((Stacks.Conormal.Restriction.restrictIdealSheafIso' f O).hom.val.app (.op W)
          ((Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.map
            (homOfLE h).op y)) =
      (O.ι.appIso W).hom ((B.presheaf.map (homOfLE h).op).hom
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom f.toLRSHom.toShHom))).val.app (.op O) y)) := by
  refine Eq.trans (Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι f O W _) ?_
  refine congrArg (O.ι.appIso W).hom ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom f.toLRSHom.toShHom))).val (homOfLE h).op y) ?_
  exact Stacks.Conormal.Locality.unitModule_val_map h _

/-- **The two routes from `Γ(X, V)` to the global sections of `C.ι ⁻¹ᵁ V` agree**, for opens
`V ≤ C` of `X`: restricting along `C.ι` and then to the top open of `C.ι ⁻¹ᵁ V` is `topIso`
followed by the comorphism of `AlgebraicGeometry.Scheme.Opens.isoOfLE`.

Both are `AlgebraicGeometry.Scheme.Hom.appLE` of the same morphism
`(C.ι ⁻¹ᵁ V).toScheme ⟶ X`: the two factorizations `(C.ι ⁻¹ᵁ V).ι ≫ C.ι` and
`(Scheme.Opens.isoOfLE hle).hom ≫ V.ι` of it are identified by
`AlgebraicGeometry.Scheme.Opens.isoOfLE_hom_ι`. So this is
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` twice and
`Stacks.DiagonalConormal.appLE_congr` once, with
`AlgebraicGeometry.Scheme.Opens.ι_appLE` converting the two open-immersion factors into
restriction maps and `AlgebraicGeometry.Scheme.Hom.appLE_eq_app` the third into `appTop`. -/
theorem appIso_res_appLE_eq_isoOfLE_appTop {X : Scheme.{u}} (C V : X.Opens) (hle : V ≤ C)
    (a : Γ(X, V)) :
    (((C.ι ⁻¹ᵁ V).ι.appIso ⊤).hom
        ((C.toScheme.presheaf.map
            (homOfLE (Scheme.Opens.ι_image_top (C.ι ⁻¹ᵁ V)).le).op).hom
          ((C.ι.appLE V (C.ι ⁻¹ᵁ V) le_rfl).hom a))) =
      ((Scheme.Opens.isoOfLE hle).hom.appTop).hom (V.topIso.inv.hom a) := by
  have hcomp : (Scheme.Opens.isoOfLE hle).hom ≫ V.ι = (C.ι ⁻¹ᵁ V).ι ≫ C.ι :=
    Scheme.Opens.isoOfLE_hom_ι hle
  have hA : (C.ι ⁻¹ᵁ V).ι.appLE (C.ι ⁻¹ᵁ V) ⊤
        (le_of_eq (C.ι ⁻¹ᵁ V).ι_preimage_self.symm) =
      C.toScheme.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (C.ι ⁻¹ᵁ V)).le).op := by
    rw [Scheme.Opens.ι_appLE]
  have hB : V.ι.appLE V ⊤ (le_of_eq V.ι_preimage_self.symm) = V.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact congrArg X.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have hC : (Scheme.Opens.isoOfLE hle).hom.appLE ⊤ ⊤ le_rfl =
      (Scheme.Opens.isoOfLE hle).hom.appTop :=
    Scheme.Hom.appLE_eq_app _
  have hring : C.ι.appLE V (C.ι ⁻¹ᵁ V) le_rfl ≫
        (C.ι ⁻¹ᵁ V).ι.appLE (C.ι ⁻¹ᵁ V) ⊤
          (le_of_eq (C.ι ⁻¹ᵁ V).ι_preimage_self.symm) =
      V.ι.appLE V ⊤ (le_of_eq V.ι_preimage_self.symm) ≫
        (Scheme.Opens.isoOfLE hle).hom.appLE ⊤ ⊤ le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE (C.ι ⁻¹ᵁ V).ι C.ι V (C.ι ⁻¹ᵁ V) ⊤ le_rfl
        (le_of_eq (C.ι ⁻¹ᵁ V).ι_preimage_self.symm),
      Scheme.Hom.appLE_comp_appLE (Scheme.Opens.isoOfLE hle).hom V.ι V ⊤ ⊤
        (le_of_eq V.ι_preimage_self.symm) le_rfl]
    exact (Stacks.DiagonalConormal.appLE_congr hcomp V ⊤ _ _).symm
  have h1 := congr($(hring) a)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h1
  rw [Scheme.Opens.ι_appIso]
  exact (congr($(hA) ((C.ι.appLE V (C.ι ⁻¹ᵁ V) le_rfl).hom a))).symm.trans
    (h1.trans ((congr($(hC)
        ((V.ι.appLE V ⊤ (le_of_eq V.ι_preimage_self.symm)).hom a))).trans
      (congrArg (fun z => ((Scheme.Opens.isoOfLE hle).hom.appTop).hom z)
        (congr($(hB) a)))))

/-- `i ⁻¹ᵁ V` is the preimage along the coborder factorization of `i.coborderRange.ι ⁻¹ᵁ V`. -/
theorem preimage_eq_liftCoborder_preimage {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) : i ⁻¹ᵁ V = i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, i.liftCoborder_ι]

/-- **A section of the ideal sheaf of `i` over `V` named by `a : I`.** By `mem_ker_app_of_mem` the
element `a` is killed by `i.app V`, which is exactly the criterion
`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff`. -/
theorem exists_idealSection {Z X : Scheme.{u}} (i : Z ⟶ X)
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I) :
    ∃ x₀ : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (.op V),
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.toLRSHom.toShHom))).val.app (.op V)).hom x₀ = (a : Γ(X, V)) :=
  (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff i V _).mpr
    (mem_ker_app_of_mem i V hV I e he a)

/-- **A section of the coborder ideal sheaf over `i.coborderRange.ι ⁻¹ᵁ V` named by `a : I`.**
`Stacks.Conormal.OpenFactorizations.app_appLE_comp` reads the vanishing of `a` on that open as the
vanishing of `a` on `i ⁻¹ᵁ V`, which is `mem_ker_app_of_mem`. -/
theorem exists_coborderSection {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I) :
    ∃ y₀ : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
        (.op (i.coborderRange.ι ⁻¹ᵁ V)),
      (i.coborderRange.ι.appLE V (i.coborderRange.ι ⁻¹ᵁ V) le_rfl).hom (a : Γ(X, V)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
          (.op (i.coborderRange.ι ⁻¹ᵁ V)) y₀ := by
  have hSV : i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V) ≤ i ⁻¹ᵁ V :=
    le_of_eq (preimage_eq_liftCoborder_preimage i V).symm
  have hvan : (i.liftCoborder.app (i.coborderRange.ι ⁻¹ᵁ V)).hom
      ((i.coborderRange.ι.appLE V (i.coborderRange.ι ⁻¹ᵁ V) le_rfl).hom (a : Γ(X, V))) = 0 := by
    rw [Stacks.Conormal.OpenFactorizations.app_appLE_comp i.liftCoborder i.coborderRange.ι i
      i.liftCoborder_ι V (i.coborderRange.ι ⁻¹ᵁ V) le_rfl hSV (a : Γ(X, V))]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, mem_ker_app_of_mem i V hV I e he a, map_zero]
  obtain ⟨y₀, hy₀⟩ :=
    (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff i.liftCoborder
      (i.coborderRange.ι ⁻¹ᵁ V) _).mpr hvan
  exact ⟨y₀, hy₀.symm⟩

/-- **The engine's remaining hypothesis `hy`, discharged from the two naming hypotheses.** If a
section `y₀` of the coborder ideal sheaf over `i.coborderRange.ι ⁻¹ᵁ V` and a section `x₀` of the
ideal sheaf of `i` over `V` are both named by `a : I`, then they agree in the structure sheaf in
the sense `Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_image` asks for.

`image_restrictIso'` computes the left-hand side,
`Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop` the right-hand side, and
`appIso_res_appLE_eq_isoOfLE_appTop` identifies the two results. -/
theorem hy_of_names {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I)
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
      (.op (i.coborderRange.ι ⁻¹ᵁ V)))
    (x₀ : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (.op V))
    (hy₀ : (i.coborderRange.ι.appLE V (i.coborderRange.ι ⁻¹ᵁ V) le_rfl).hom (a : Γ(X, V)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
          (.op (i.coborderRange.ι ⁻¹ᵁ V)) y₀)
    (hx₀ : ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.toLRSHom.toShHom))).val.app (.op V)).hom x₀ = (a : Γ(X, V))) :
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
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
            (Stacks.Conormal.Tag01R3Generators.restrictIdealSectionTop i V x₀)) := by
  have hle := Stacks.Conormal.AffineCotangent.le_coborderRange_of_isoSpecQuotient i V hV I e he
  refine Eq.trans (image_restrictIso' i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ V) ⊤
    (Scheme.Opens.ι_image_top (i.coborderRange.ι ⁻¹ᵁ V)).le y₀) ?_
  rw [← hy₀]
  refine Eq.trans (appIso_res_appLE_eq_isoOfLE_appTop i.coborderRange V hle (a : Γ(X, V))) ?_
  refine congrArg (fun z => ((Scheme.Opens.isoOfLE hle).hom.appTop).hom z) ?_
  refine Eq.trans ?_ (Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop
    i V x₀).symm
  exact congrArg V.topIso.inv.hom hx₀.symm

/-- **The part (2) generator formula at the coborder factorization, with every hypothesis of the
engine discharged.** For the presentation data of the tagged statement over an affine open `V` of the ambient
scheme and a section `y₀` of the coborder ideal sheaf over `i.coborderRange.ι ⁻¹ᵁ V` named by
`a : I`, the identification
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` carries the quotient
generator of `y₀` to `I.toCotangent a`.

This is `Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_image` with its `hy`
supplied by `hy_of_names` and its `x₀` by `exists_idealSection`. -/
theorem conormalAffineSectionsIsoCotangent_toCotangent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (a : I)
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
      (.op (i.coborderRange.ι ⁻¹ᵁ V)))
    (hy₀ : (i.coborderRange.ι.appLE V (i.coborderRange.ι ⁻¹ᵁ V) le_rfl).hom (a : Γ(X, V)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
          (.op (i.coborderRange.ι ⁻¹ᵁ V)) y₀) :
    (Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent i V hV I e he).hom.hom
        (((Stacks.Conormal.conormalSheaf i).val.map
            (eqToHom (preimage_eq_liftCoborder_preimage i V)).op).hom
          (((Stacks.Conormal.conormalQuotientMap i i.coborderRange i.liftCoborder
            i.liftCoborder_ι).val.app (.op (i.coborderRange.ι ⁻¹ᵁ V))).hom y₀)) =
      I.toCotangent a := by
  obtain ⟨x₀, hx₀⟩ := exists_idealSection i V hV I e he a
  exact Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_image i V hV I e he
    (preimage_eq_liftCoborder_preimage i V) a y₀ x₀ hx₀
    (hy_of_names i V hV I e he a y₀ x₀ hy₀ hx₀)

end Stacks.Tag01R3PartTwo

end
