module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationConormalTrack
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafHomAction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionDifference
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Simple transitivity of the action on the sheaf of infinitesimal deformations

[Stacks Project, Tag 04FJ] asserts that `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` acts on the sheaf
of [Stacks Project, Tag 04FI], simply transitively over any open carrying a section. The action
is `Stacks.Thickenings.exists_addAction_compatibleLifts` in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafHomAction.lean`. This
file proves the **transitivity** clause,
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq`: over an open `V` of `X'` carrying a
lift, any two lifts differ by exactly one section of the sheaf of homomorphisms. Both clauses are
unrestricted — nothing is affine, and `V` is an arbitrary open.

The transitivity clause is the unrestricted [Stacks Project, Tag 04FG]
(`Stacks.Thickenings.exists_isDerivationAction`) read for the restricted thickening `i ∣_ V`,
together with the uniqueness half of [Stacks Project, Tag 02H5]
(`Stacks.Thickenings.eq_of_isDerivationAction`) and the characterisation of the moved lift of
[Stacks Project, Tag 0CK1]. Those are stated in the library's *other* conormal track, so what the
proof has to supply is the identification of the two tracks' moved lifts,
`Stacks.Thickenings.homSectionAct_eq_derivationActionSheaf`. The translation of the **datum** is
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationConormalTrack.lean`; this
file supplies the translation of the **inclusion**: the conormal sheaf of a first-order
thickening sits inside the ambient structure sheaf by
`Stacks.Thickenings.firstOrderImmersionConormalSheafι`, the deformation sheaf's perturbation
`Stacks.Thickenings.homSectionValue` uses that inclusion for `i`, and the derivation
`Stacks.Thickenings.derivationSectionι` of the conormal track uses it for `i ∣_ V`. The two agree
across `Stacks.Thickenings.restrictConormalModulesIso`, which is
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_restrict`.

## Main results

* `Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq`: **the transitivity clause of
  [Stacks Project, Tag 04FJ] for arbitrary schemes**, which carries the attribute.
* `Stacks.Thickenings.homSectionAct_eq_derivationActionSheaf`: the lift `θ ⬝ b` of the
  deformation sheaf is the lift `θ ⬝ b` of the derivation track.
* `Stacks.Thickenings.deformationHomSections_ext`: a section of the sheaf of homomorphisms is
  determined by the lift it produces — the uniqueness half.
* `Stacks.Thickenings.derivationSectionι_eq_conormalSection`: the two perturbations agree on
  sections. This is the comparison the identification of the lifts rests on.
* `Stacks.Thickenings.restrictConormalModulesIso_hom_val_app`: the restriction comparison of
  conormal sheaves, read on sections, is the transpose of the canonical map of
  [Stacks Project, Tag 01R4] of the restriction square.
* `Stacks.Thickenings.firstOrderImmersionConormalSheafι_restrict` and
  `Stacks.Thickenings.firstOrderImmersionConormalSheafι_restrict_le`: **the inclusion
  `𝒞 ⟶ 𝒪` of a first-order thickening is compatible with restriction to an open of the ambient
  scheme.** This is the input the conormal-track bridge leaves open.
* `Stacks.Thickenings.restrictDerivationDatumEquiv_hom_comp` and
  `Stacks.Thickenings.restrictDerivationDatumEquiv_app_hom`: the translated datum precomposed
  with the comparison of the two readings of `a^*Ω_{Y/S}` over `i⁻¹V`; stated with the forward
  components only, which is what makes it usable.
* `Stacks.Thickenings.preimage_ι_preimage_eq`,
  `Stacks.Thickenings.preimage_morphismRestrict_image`,
  `Stacks.Thickenings.preimage_lift_eq`, `Stacks.Thickenings.preimage_image_lift_eq` and
  `Stacks.Thickenings.image_preimage_lift_le`: the identifications of the opens of `i⁻¹V` the two
  tracks evaluate their data on — `(ι ≫ a)⁻¹j⁻¹W` on one side, the part cut out by
  `Stacks.Thickenings.liftOpen` on the other.
* `Stacks.Thickenings.morphismRestrict_app_eq_zero`,
  `Stacks.Thickenings.conormalSection_eq_val_app`,
  `Stacks.Thickenings.module_val_map_apply_eq`,
  `Stacks.Thickenings.presheaf_map_apply_eq` and
  `Stacks.Thickenings.module_presheaf_map_apply`: the bookkeeping the comparison needs.

## Implementation notes

The compatibility of the inclusion is proved on conormal **classes**. For a first-order
thickening every conormal section over the part of `X` cut out by an open `U` of `X'` is the
class of a section of `𝒪_{X'}` over `U`
(`Stacks.Thickenings.conormalClass_firstOrderImmersionConormalSheafι`, which rests on the
quotient map `ℐ ⟶ i_*𝒞` being an isomorphism); the canonical map of [Stacks Project, Tag 01R4]
carries classes to classes
(`Stacks.Conormal.conormalClass_immersionConormalSheafMap_app`); the ambient and cut-out opens of
a class move by `Stacks.Conormal.conormalClass_congr_open` and
`Stacks.Conormal.conormalClass_restrict_target`; and the inclusion undoes the class
(`Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass`). So no affine chart is
chosen and no cover is used.

The statement of the inclusion compatibility is arranged so that the two sides are sections over
the *same* open of `X'`: the open of `V` is an arbitrary `O` and the open of `X'` is its image
`V.ι ''ᵁ O`, whose sections are the sections of `𝒪_V` over `O` on the nose. Presenting the open
of `X'` first and `O` as its preimage instead would put the two sides in two modules that are
equal only propositionally. The enlargement of the open that the comparison then needs is made by
**naturality** of `Stacks.Thickenings.restrictConormalModulesIso`
(`Stacks.Thickenings.firstOrderImmersionConormalSheafι_restrict_le`) and not by transporting the
statement along the equality of opens: the transport is a term the kernel does not reduce in
reasonable time.

Several of the comparisons are proved over an **opaque** abbreviation of a large term:
`Stacks.Thickenings.restrictDerivationDatumEquiv_app_hom` and
`Stacks.Thickenings.derivationSectionι_eq_conormalSection` reason about variables standing for
morphisms of sheaves of modules rather than about the morphisms themselves, and the step reading
an equality of derivations on a universal differential is factored through a lemma stated over
two arbitrary morphisms. The mathematics is the same; what changes is that the unifier compares
variables rather than the unfoldings of
`Scheme.Modules.pullbackPushforwardAdjunction` and of the two conormal tracks' isomorphisms,
which exhausts its recursion depth.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction Opposite TopologicalSpace
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

/-! ### The conormal inclusion of a restricted thickening -/

section ConormalInclusion

variable {X X' : Scheme.{u}} {i : X ⟶ X'}

/-- Two restriction maps of a sheaf of modules between the same two opens agree: the category of
opens is thin. -/
theorem module_val_map_apply_eq {Z : Scheme.{u}} (M : Z.Modules) {A B : (Z.Opens)ᵒᵖ}
    (u v : A ⟶ B) (x : M.val.obj A) : M.val.map u x = M.val.map v x := by
  rw [Subsingleton.elim u v]

/-- Two restriction maps of the structure sheaf between the same two opens agree, on sections. -/
theorem presheaf_map_apply_eq {Z : Scheme.{u}} {A B : (Z.Opens)ᵒᵖ} (u v : A ⟶ B)
    (x : Z.presheaf.obj A) : (Z.presheaf.map u).hom x = (Z.presheaf.map v).hom x := by
  rw [presheaf_map_eq u v]

/-- A restriction map of the restriction of a sheaf of modules to an open subscheme is a
restriction map of the sheaf itself. -/
theorem restrict_val_map_apply {Z : Scheme.{u}} (M : Z.Modules) (U : Z.Opens)
    {D D' : U.toScheme.Opens} (h : D ≤ D') (x : (M.restrict U.ι).val.obj (op D')) :
    (M.restrict U.ι).val.map (homOfLE h).op x
      = M.val.map (homOfLE (U.ι.image_mono h)).op x :=
  module_val_map_apply_eq M (U.ι.opensFunctor.map (homOfLE h)).op
    (homOfLE (U.ι.image_mono h)).op x

/-- **The restriction comparison of conormal sheaves, on sections, is the transpose of the map of
[Stacks Project, Tag 01R4] of the restriction square.** -/
theorem restrictConormalModulesIso_hom_val_app [IsImmersion i] (V : X'.Opens) (U' : X.Opens)
    (m : (conormalModules i).val.obj (op U')) :
    (restrictConormalModulesIso i V).hom.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ U'))
        ((conormalModules i).val.map
          (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le U')).op m)
      = (((Scheme.Modules.pullbackPushforwardAdjunction (i ⁻¹ᵁ V).ι).homEquiv
            (conormalModules i) (conormalModules (i ∣_ V))
            (immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
              (toShHom_square (morphismRestrict_ι i V)))).val.app (op U')) m := by
  have hD : (restrictConormalModulesIso i V).hom =
      ((Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ V).ι).app (conormalModules i)).hom ≫
        (pullbackConormalModulesIso i V).hom :=
    Iso.trans_hom _ _
  have hA := homEquiv_val_app_apply (i ⁻¹ᵁ V).ι
    (immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
      (toShHom_square (morphismRestrict_ι i V))) U' m
  have hB := Stacks.Smooth.restrictFunctorIsoPullback_app_map (i ⁻¹ᵁ V) (conormalModules i) U' m
  have hC := comp_val_app_apply
    (((Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ V).ι).app (conormalModules i)).hom)
    (pullbackConormalModulesIso i V).hom ((i ⁻¹ᵁ V).ι ⁻¹ᵁ U')
    ((conormalModules i).val.map (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le U')).op m)
  have hB' : (((Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ V).ι).app
        (conormalModules i)).hom.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ U')))
        ((conormalModules i).val.map
          (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le U')).op m)
      = (((Scheme.Modules.pullbackPushforwardAdjunction (i ⁻¹ᵁ V).ι).unit.app
          (conormalModules i)).val.app (op U')) m := hB
  rw [hD, hC, hB', pullbackConormalModulesIso_hom]
  exact hA.symm

/-- **The two spellings of the part of `i⁻¹V` cut out by an open of `X'`.** -/
theorem preimage_ι_preimage_eq (i : X ⟶ X') (V U : X'.Opens) :
    (i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ U) = (i ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]

/-- **The part of `i⁻¹V` cut out by the image of an open of `V`.** -/
theorem preimage_morphismRestrict_image (i : X ⟶ X') (V : X'.Opens) (O : V.toScheme.Opens) :
    (i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ O)) = (i ∣_ V) ⁻¹ᵁ O := by
  rw [preimage_ι_preimage_eq, V.ι.preimage_image_eq]

/-- **The comorphism of `i ∣_ V` kills a section of `𝒪_{X'}` killed by the comorphism of `i`.** -/
theorem morphismRestrict_app_eq_zero [IsImmersion i] (V : X'.Opens) (O : V.toScheme.Opens)
    (r : Γ(X', V.ι ''ᵁ O)) (hr : (i.app (V.ι ''ᵁ O)).hom r = 0) :
    ((i ∣_ V).app O).hom r = 0 := by
  refine Eq.trans (congrArg (fun φ : Γ(X', V.ι ''ᵁ O) ⟶
      Γ(X, (i ⁻¹ᵁ V).ι ''ᵁ ((i ∣_ V) ⁻¹ᵁ O)) => φ.hom r) (morphismRestrict_app' i V O)) ?_
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hr, map_zero]
  rfl

/-- **The inclusion `𝒞 ⟶ 𝒪` of the conormal sheaf of a first-order thickening is compatible with
restriction to an open of the ambient scheme.** Reading a conormal section of `i` over the part of
`X` cut out by the image of an open `O` of `V` as a conormal section of the restricted thickening
`i ∣_ V`, along `Stacks.Thickenings.restrictConormalModulesIso`, and then including it into
`𝒪_V` over `O`, is including it into `𝒪_{X'}`. The two sides are sections over the same open of
`X'`, since the sections of `𝒪_V` over `O` are the sections of `𝒪_{X'}` over `V.ι ''ᵁ O`.

This is the one input to the conormal-track bridge that is about the inclusion rather than about
the datum. Every conormal section of a first-order thickening is a conormal class
(`Stacks.Thickenings.conormalClass_firstOrderImmersionConormalSheafι`), the map of
[Stacks Project, Tag 01R4] of the restriction square carries classes to classes
(`Stacks.Conormal.conormalClass_immersionConormalSheafMap_app`), the ambient and cut-out opens of
a class move by `Stacks.Conormal.conormalClass_congr_open` and
`Stacks.Conormal.conormalClass_restrict_target`, and the inclusion undoes the class
(`Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass`). -/
theorem firstOrderImmersionConormalSheafι_restrict [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (V : X'.Opens) (O : V.toScheme.Opens)
    (m : (conormalModules i).val.obj (op (i ⁻¹ᵁ (V.ι ''ᵁ O)))) :
    (firstOrderImmersionConormalSheafι (i ∣_ V)
          (ker_pow_morphismRestrict_eq_bot i hsq V)).val.app (op O)
        ((conormalModules (i ∣_ V)).val.map
          (homOfLE (preimage_morphismRestrict_image i V O).ge).op
          ((restrictConormalModulesIso i V).hom.val.app
            (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ O))))
            ((conormalModules i).val.map
              (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ O)))).op m)))
      = (firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m := by
  have hr : (i.app (V.ι ''ᵁ O)).hom
      ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m) = 0 :=
    app_firstOrderImmersionConormalSheafι_eq_zero i hsq (V.ι ''ᵁ O) m
  have hm := conormalClass_firstOrderImmersionConormalSheafι i hsq (V.ι ''ᵁ O) m hr
  have hstep := restrictConormalModulesIso_hom_val_app V (i ⁻¹ᵁ (V.ι ''ᵁ O)) m
  have hclass := Stacks.Conormal.conormalClass_immersionConormalSheafMap_app (i ∣_ V) i
    (i ⁻¹ᵁ V).ι V.ι (morphismRestrict_ι i V) (V.ι ''ᵁ O) (i ⁻¹ᵁ (V.ι ''ᵁ O)) le_rfl
    (preimage_ι_preimage_eq i V (V.ι ''ᵁ O)).le
    ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m) hr
  have hr' : ((i ∣_ V).app O).hom
      ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m) = 0 :=
    morphismRestrict_app_eq_zero V O _ hr
  have hrr' : ((V.toScheme).presheaf.map
        (homOfLE (V.ι.preimage_image_eq O).ge).op).hom
        ((V.ι.app (V.ι ''ᵁ O)).hom
          ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m))
      = (firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m := by
    refine Eq.trans (CommRingCat.comp_apply (V.ι.app (V.ι ''ᵁ O))
      ((V.toScheme).presheaf.map (homOfLE (V.ι.preimage_image_eq O).ge).op)
      ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m)).symm ?_
    rw [show (V.ι.app (V.ι ''ᵁ O)) ≫
          (V.toScheme).presheaf.map (homOfLE (V.ι.preimage_image_eq O).ge).op
        = V.ι.appLE (V.ι ''ᵁ O) O (V.ι.preimage_image_eq O).ge from rfl,
      Scheme.Opens.ι_appLE]
    exact presheaf_map_self _ _
  have hcongr := Stacks.Conormal.conormalClass_congr_open (i ∣_ V) (V.ι ⁻¹ᵁ (V.ι ''ᵁ O)) O
    (V.ι.preimage_image_eq O) (preimage_ι_preimage_eq i V (V.ι ''ᵁ O)).le
    ((preimage_ι_preimage_eq i V (V.ι ''ᵁ O)).le.trans
      ((i ∣_ V).preimage_mono (V.ι.preimage_image_eq O).le))
    ((V.ι.app (V.ι ''ᵁ O)).hom
      ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m))
    ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m)
    (Stacks.Conormal.app_app_eq_zero_of_square (morphismRestrict_ι i V) (V.ι ''ᵁ O) _ hr)
    hr' hrr'
  have htgt := Stacks.Conormal.conormalClass_restrict_target (i ∣_ V) O
    ((preimage_ι_preimage_eq i V (V.ι ''ᵁ O)).le.trans
      ((i ∣_ V).preimage_mono (V.ι.preimage_image_eq O).le))
    (le_refl ((i ∣_ V) ⁻¹ᵁ O)) (preimage_morphismRestrict_image i V O).ge
    ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m) hr'
  have hfin := Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass (i ∣_ V)
    (ker_pow_morphismRestrict_eq_bot i hsq V) O
    ((firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m) hr'
  rw [hm] at hclass
  have hcomb := (hstep.trans hclass).trans hcongr
  rw [hcomb]
  refine Eq.trans (congrArg (fun z : (conormalModules (i ∣_ V)).val.obj (op ((i ∣_ V) ⁻¹ᵁ O)) =>
      ((firstOrderImmersionConormalSheafι (i ∣_ V)
            (ker_pow_morphismRestrict_eq_bot i hsq V)).val.app (op O)).hom z) htgt) ?_
  exact hfin

end ConormalInclusion

/-! ### The derivation datum through the bridge -/

section Datum

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}

/-- **The translated datum precomposed with the comparison of the two readings of `a^*Ω_{Y/S}`
over `i⁻¹V`.** -/
theorem restrictDerivationDatumEquiv_hom_comp [IsImmersion i] (V : X'.Opens) (p : Y ⟶ S)
    (θr : (Stacks.Smooth.pullbackCotangentSheaf p a).restrict (i ⁻¹ᵁ V).ι ⟶
      (conormalModules i).restrict (i ⁻¹ᵁ V).ι) :
    (Stacks.Smooth.restrictPullbackCotangentSheafIso p a (i ⁻¹ᵁ V)).hom ≫
        restrictDerivationDatumEquiv i a p V θr
      = θr ≫ (restrictConormalModulesIso i V).hom := by
  rw [restrictDerivationDatumEquiv, Iso.homCongr_apply]
  exact Iso.hom_inv_id_assoc _ _

/-- `Stacks.Thickenings.restrictDerivationDatumEquiv_hom_comp` on sections, in the
`AlgebraicGeometry.Scheme.Modules.Hom.app` reading. -/
theorem restrictDerivationDatumEquiv_app_hom [IsImmersion i] (V : X'.Opens) (p : Y ⟶ S)
    (θr : (Stacks.Smooth.pullbackCotangentSheaf p a).restrict (i ⁻¹ᵁ V).ι ⟶
      (conormalModules i).restrict (i ⁻¹ᵁ V).ι) (D : (i ⁻¹ᵁ V).toScheme.Opens)
    (w : Γ((Stacks.Smooth.pullbackCotangentSheaf p a).restrict (i ⁻¹ᵁ V).ι, D)) :
    ((restrictDerivationDatumEquiv i a p V θr).app D)
        (((Stacks.Smooth.restrictPullbackCotangentSheafIso p a (i ⁻¹ᵁ V)).hom.app D) w)
      = ((restrictConormalModulesIso i V).hom.app D) ((θr.app D) w) := by
  obtain ⟨E, hE⟩ : ∃ E : (Stacks.Smooth.pullbackCotangentSheaf p a).restrict (i ⁻¹ᵁ V).ι ⟶
      Stacks.Smooth.pullbackCotangentSheaf p ((i ⁻¹ᵁ V).ι ≫ a),
      (Stacks.Smooth.restrictPullbackCotangentSheafIso p a (i ⁻¹ᵁ V)).hom = E := ⟨_, rfl⟩
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Stacks.Smooth.pullbackCotangentSheaf p ((i ⁻¹ᵁ V).ι ≫ a) ⟶
      conormalModules (i ∣_ V), restrictDerivationDatumEquiv i a p V θr = Θ := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (conormalModules i).restrict (i ⁻¹ᵁ V).ι ⟶ conormalModules (i ∣_ V),
      (restrictConormalModulesIso i V).hom = F := ⟨_, rfl⟩
  have h2 : E ≫ Θ = θr ≫ F := by
    rw [← hE, ← hΘ, ← hF]
    exact restrictDerivationDatumEquiv_hom_comp V p θr
  rw [hE, hΘ, hF]
  have h3 := congrArg (fun φ : (Stacks.Smooth.pullbackCotangentSheaf p a).restrict (i ⁻¹ᵁ V).ι ⟶
    conormalModules (i ∣_ V) => (φ.app D) w) h2
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using h3

end Datum

/-! ### The two perturbations agree -/

section Perturbation

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] {V : X'.Opens} {b : V.toScheme ⟶ Y'}

omit [IsClosedImmersion i] in
/-- The part of `i⁻¹V` over which a lift reads a section of `𝒪_{Y'}` over `W`. -/
theorem preimage_lift_eq {a : X ⟶ Y} (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j) (W : Y'.Opens) :
    (i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W) = ((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, cb, Scheme.Hom.comp_preimage]

omit [IsClosedImmersion i] in
/-- The same open, read as the part of `i⁻¹V` cut out by `Stacks.Thickenings.liftOpen`. -/
theorem preimage_image_lift_eq {a : X ⟶ Y} (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (W : Y'.Opens) :
    (i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ (b ⁻¹ᵁ W))) = ((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W) :=
  (preimage_morphismRestrict_image i V (b ⁻¹ᵁ W)).trans (preimage_lift_eq cb W)

omit [IsClosedImmersion i] in
/-- The image of that open in `X` is the part of `X` cut out by
`Stacks.Thickenings.liftOpen`. -/
theorem image_preimage_lift_le {a : X ⟶ Y} (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (W : Y'.Opens) :
    (i ⁻¹ᵁ V).ι ''ᵁ (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)) ≤ i ⁻¹ᵁ (liftOpen V b W) := by
  rw [← preimage_image_lift_eq cb W]
  exact (i ⁻¹ᵁ V).ι.image_preimage_le _

/-- A restriction map of a sheaf of modules on a scheme, read at the two levels. -/
theorem module_presheaf_map_apply {Z : Scheme.{u}} (M : Z.Modules) {A B : (Z.Opens)ᵒᵖ}
    (u : A ⟶ B) (x : M.val.obj A) : (M.presheaf.map u).hom x = M.val.map u x := rfl

/-- `Stacks.Thickenings.conormalSection` is the inclusion read on sections. -/
theorem conormalSection_eq_val_app (hsq : i.ker ^ 2 = ⊥) (E : X'.Opens)
    (s : (conormalModules i).val.obj (op (i ⁻¹ᵁ E))) :
    conormalSection hsq E s = (firstOrderImmersionConormalSheafι i hsq).val.app (op E) s := rfl

/-- **`Stacks.Thickenings.firstOrderImmersionConormalSheafι_restrict` with the open of `i⁻¹V`
enlarged.** The open is moved by naturality of
`Stacks.Thickenings.restrictConormalModulesIso`, never by a transport along an equality of
opens. -/
theorem firstOrderImmersionConormalSheafι_restrict_le (hsq : i.ker ^ 2 = ⊥)
    (V : X'.Opens) (O : V.toScheme.Opens) {D : (i ⁻¹ᵁ V).toScheme.Opens}
    (hDD' : D ≤ (i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ O)))
    (hDO : (i ∣_ V) ⁻¹ᵁ O ≤ D) (hEq : (i ⁻¹ᵁ V).ι ''ᵁ D ≤ i ⁻¹ᵁ (V.ι ''ᵁ O))
    (m : (conormalModules i).val.obj (op (i ⁻¹ᵁ (V.ι ''ᵁ O)))) :
    (firstOrderImmersionConormalSheafι (i ∣_ V)
          (ker_pow_morphismRestrict_eq_bot i hsq V)).val.app (op O)
        ((conormalModules (i ∣_ V)).val.map (homOfLE hDO).op
          ((restrictConormalModulesIso i V).hom.val.app (op D)
            ((conormalModules i).val.map (homOfLE hEq).op m)))
      = (firstOrderImmersionConormalSheafι i hsq).val.app (op (V.ι ''ᵁ O)) m := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (conormalModules i).restrict (i ⁻¹ᵁ V).ι ⟶ conormalModules (i ∣_ V),
      (restrictConormalModulesIso i V).hom = Φ := ⟨_, rfl⟩
  have hB := firstOrderImmersionConormalSheafι_restrict hsq V O m
  rw [hΦ] at hB ⊢
  refine Eq.trans ?_ hB
  have hnat := PresheafOfModules.naturality_apply Φ.val (homOfLE hDD').op
    ((conormalModules i).val.map
      (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ O)))).op m)
  have hsrc := module_map_map
    (M := conormalModules i)
    (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ O)))).op
    (homOfLE ((i ⁻¹ᵁ V).ι.image_mono hDD')).op (homOfLE hEq).op m
  have htgt := module_map_map (M := conormalModules (i ∣_ V)) (homOfLE hDD').op
    (homOfLE hDO).op (homOfLE (hDO.trans hDD')).op
    (Φ.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ O))))
      ((conormalModules i).val.map
        (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ O)))).op m))
  have hnat2 : Φ.val.app (op D)
        ((conormalModules i).val.map (homOfLE ((i ⁻¹ᵁ V).ι.image_mono hDD')).op
          ((conormalModules i).val.map
            (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ O)))).op m))
      = (conormalModules (i ∣_ V)).val.map (homOfLE hDD').op
          (Φ.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ O))))
            ((conormalModules i).val.map
              (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ O)))).op m)) := hnat
  have step1 : Φ.val.app (op D) ((conormalModules i).val.map (homOfLE hEq).op m)
      = (conormalModules (i ∣_ V)).val.map (homOfLE hDD').op
          (Φ.val.app (op ((i ⁻¹ᵁ V).ι ⁻¹ᵁ (i ⁻¹ᵁ (V.ι ''ᵁ O))))
            ((conormalModules i).val.map
              (homOfLE ((i ⁻¹ᵁ V).ι.image_preimage_le (i ⁻¹ᵁ (V.ι ''ᵁ O)))).op m)) :=
    (congrArg (fun z : (conormalModules i).val.obj (op ((i ⁻¹ᵁ V).ι ''ᵁ D)) =>
      Φ.val.app (op D) z) hsrc.symm).trans hnat2
  refine congrArg (fun z : (conormalModules (i ∣_ V)).val.obj (op ((i ∣_ V) ⁻¹ᵁ O)) =>
      (firstOrderImmersionConormalSheafι (i ∣_ V)
        (ker_pow_morphismRestrict_eq_bot i hsq V)).val.app (op O) z) ?_
  refine Eq.trans (congrArg (fun z : (conormalModules (i ∣_ V)).val.obj (op D) =>
      (conormalModules (i ∣_ V)).val.map (homOfLE hDO).op z) step1) ?_
  exact htgt

/-- **The translated datum, evaluated on the pulled-back universal differential.** The datum the
conormal-track bridge produces from a section `θ` of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` takes,
on the pulled-back universal differential of a section of `𝒪_Y`, the value `θ` itself takes,
carried across `Stacks.Thickenings.restrictConormalModulesIso`. -/
theorem restrictDerivationDatum_app_pullbackD [IsImmersion j] (pY' : Y' ⟶ S) (V : X'.Opens)
    (θ : deformationHomSections i a (j ≫ pY') V) (W : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ W)) :
    ((restrictDerivationDatumEquiv i a (j ≫ pY') V
          (Stacks.Modules.overHomEquivRestrictHom _ _ _ θ)).app
        (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)))
        (Stacks.Smooth.pullbackD (j ≫ pY') ((i ⁻¹ᵁ V).ι ≫ a) (j ⁻¹ᵁ W) le_rfl y)
      = ((restrictConormalModulesIso i V).hom.app (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)))
          (θ.app ((i ⁻¹ᵁ V).ι_image_le (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)))
            (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
              ((i ⁻¹ᵁ V).ι.image_preimage_le (a ⁻¹ᵁ (j ⁻¹ᵁ W))) y)) := by
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ pY') ((i ⁻¹ᵁ V).ι ≫ a) ⟶
      conormalModules (i ∣_ V),
      restrictDerivationDatumEquiv i a (j ≫ pY') V
        (Stacks.Modules.overHomEquivRestrictHom _ _ _ θ) = Θ := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (conormalModules i).restrict (i ⁻¹ᵁ V).ι ⟶ conormalModules (i ∣_ V),
      (restrictConormalModulesIso i V).hom = Φ := ⟨_, rfl⟩
  have hdat := restrictDerivationDatumEquiv_app_hom V (j ≫ pY')
    (Stacks.Modules.overHomEquivRestrictHom _ _ _ θ) (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W))
    (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
      ((i ⁻¹ᵁ V).ι.image_preimage_le (a ⁻¹ᵁ (j ⁻¹ᵁ W))) y)
  have hover := Stacks.Modules.overHomEquivRestrictHom_val_app
    (Stacks.Smooth.pullbackCotangentSheaf (j ≫ pY') a) (conormalModules i) (i ⁻¹ᵁ V) θ
    (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W))
    (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
      ((i ⁻¹ᵁ V).ι.image_preimage_le (a ⁻¹ᵁ (j ⁻¹ᵁ W))) y)
  rw [hΘ, hΦ] at hdat
  rw [hΘ, hΦ]
  refine Eq.trans (congrArg
    (fun z : Γ(Stacks.Smooth.pullbackCotangentSheaf (j ≫ pY') ((i ⁻¹ᵁ V).ι ≫ a),
        ((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)) =>
      (Θ.app (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W))) z)
    (Stacks.Smooth.restrictPullbackCotangentSheafIso_pullbackD (j ≫ pY') a (i ⁻¹ᵁ V)
      ((i ⁻¹ᵁ V).ι.image_preimage_le (a ⁻¹ᵁ (j ⁻¹ᵁ W))) le_rfl y).symm) ?_
  refine hdat.trans ?_
  exact congrArg
    (fun z : Γ((conormalModules i).restrict (i ⁻¹ᵁ V).ι, ((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)) =>
      (Φ.app (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W))) z) hover

/-- **The derivation of Equation [Stacks Project, Tag 04BV] attached to the translated datum is
the perturbation of the deformation sheaf.** For a section `θ` of
`SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` over the part of `X` cut out by `V`, the derivation
`Stacks.Thickenings.derivationSectionι` of the datum the conormal-track bridge produces from `θ`
is `θ` applied to the pulled-back universal differential and included into `𝒪_{X'}` — which is
`Stacks.Thickenings.homSectionValue` read on an arbitrary section of `𝒪_Y`. -/
theorem derivationSectionι_eq_conormalSection [IsImmersion j] (hsq : i.ker ^ 2 = ⊥)
    (pY' : Y' ⟶ S) (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (θ : deformationHomSections i a (j ≫ pY') V) (W : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ W)) :
    derivationSectionι (ker_pow_morphismRestrict_eq_bot i hsq V) pY' cb
        (derivationDatumOfCotangent (restrictDerivationDatumEquiv i a (j ≫ pY') V
          (Stacks.Modules.overHomEquivRestrictHom _ _ _ θ))) W y
      = conormalSection hsq (liftOpen V b W)
          (θ.app (preimage_liftOpen_le i V b W)
            (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
              (preimage_liftOpen_le_preimage cb W) y)) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (conormalModules i).restrict (i ⁻¹ᵁ V).ι ⟶ conormalModules (i ∣_ V),
      (restrictConormalModulesIso i V).hom = Φ := ⟨_, rfl⟩
  have hbr := derivationSectionι_derivationDatumOfCotangent
    (ker_pow_morphismRestrict_eq_bot i hsq V) pY' cb
    (restrictDerivationDatumEquiv i a (j ≫ pY') V
      (Stacks.Modules.overHomEquivRestrictHom _ _ _ θ)) W y
  have hdv := restrictDerivationDatum_app_pullbackD pY' V θ W y
  have hmpd := Stacks.Smooth.map_pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
    (preimage_liftOpen_le_preimage cb W)
    ((i ⁻¹ᵁ V).ι.image_preimage_le (a ⁻¹ᵁ (j ⁻¹ᵁ W))) (image_preimage_lift_le cb W) y
  have hnatθ := moduleHomSections.map_app θ (preimage_liftOpen_le i V b W)
    (image_preimage_lift_le cb W)
    (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W) (preimage_liftOpen_le_preimage cb W) y)
  have hmpd' : (Stacks.Smooth.pullbackCotangentSheaf (j ≫ pY') a).val.map
        (homOfLE (image_preimage_lift_le cb W)).op
        (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W) (preimage_liftOpen_le_preimage cb W) y)
      = Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
          ((i ⁻¹ᵁ V).ι.image_preimage_le (a ⁻¹ᵁ (j ⁻¹ᵁ W))) y := hmpd
  have hnatθ' : θ.app ((i ⁻¹ᵁ V).ι_image_le (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)))
        (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
          ((i ⁻¹ᵁ V).ι.image_preimage_le (a ⁻¹ᵁ (j ⁻¹ᵁ W))) y)
      = (conormalModules i).val.map (homOfLE (image_preimage_lift_le cb W)).op
          (θ.app (preimage_liftOpen_le i V b W)
            (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W)
              (preimage_liftOpen_le_preimage cb W) y)) :=
    (congrArg (fun z : (Stacks.Smooth.pullbackCotangentSheaf (j ≫ pY') a).val.obj
        (op ((i ⁻¹ᵁ V).ι ''ᵁ (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)))) =>
      θ.app ((i ⁻¹ᵁ V).ι_image_le (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W))) z) hmpd').symm.trans hnatθ
  have hBle := firstOrderImmersionConormalSheafι_restrict_le hsq V (b ⁻¹ᵁ W)
    (preimage_image_lift_eq cb W).ge (preimage_lift_eq cb W).le (image_preimage_lift_le cb W)
    (θ.app (preimage_liftOpen_le i V b W)
      (Stacks.Smooth.pullbackD (j ≫ pY') a (j ⁻¹ᵁ W) (preimage_liftOpen_le_preimage cb W) y))
  rw [hΦ] at hdv hBle
  refine hbr.trans ?_
  refine Eq.trans (congrArg (fun z : (conormalModules (i ∣_ V)).val.obj
      (op (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W))) =>
    conormalSectionι (ker_pow_morphismRestrict_eq_bot i hsq V) cb W z) hdv) ?_
  refine Eq.trans (congrArg (fun z : (conormalModules i).val.obj
      (op ((i ⁻¹ᵁ V).ι ''ᵁ (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W)))) =>
    conormalSectionι (ker_pow_morphismRestrict_eq_bot i hsq V) cb W
      (Φ.val.app (op (((i ⁻¹ᵁ V).ι ≫ a) ⁻¹ᵁ (j ⁻¹ᵁ W))) z)) hnatθ') ?_
  refine Eq.trans ?_ hBle
  exact congrArg (fun z : (conormalModules (i ∣_ V)).val.obj (op ((i ∣_ V) ⁻¹ᵁ (b ⁻¹ᵁ W))) =>
      (firstOrderImmersionConormalSheafι (i ∣_ V)
        (ker_pow_morphismRestrict_eq_bot i hsq V)).val.app (op (b ⁻¹ᵁ W)) z)
    (module_val_map_apply_eq (conormalModules (i ∣_ V)) (eqToHom (preimage_square cb W)).op
      (homOfLE (preimage_lift_eq cb W).le).op _)

end Perturbation

/-! ### Simple transitivity -/

section Transitivity

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
  [IsClosedImmersion i] [IsImmersion j] {V : X'.Opens} {b : V.toScheme ⟶ Y'}

/-- **The lift `θ ⬝ b` of the deformation sheaf is the lift `θ ⬝ b` of the derivation track.**
Both are the perturbation of `b` by the same derivation, by
`Stacks.Thickenings.derivationSectionι_eq_conormalSection`. -/
theorem homSectionAct_eq_derivationActionSheaf (hsq : i.ker ^ 2 = ⊥) (pY' : Y' ⟶ S)
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (θ : deformationHomSections i a (j ≫ pY') V) :
    homSectionAct hsq pY' cb θ
      = derivationActionSheaf (ker_pow_morphismRestrict_eq_bot i hsq V) pY' cb
          (derivationDatumOfCotangent (restrictDerivationDatumEquiv i a (j ≫ pY') V
            (Stacks.Modules.overHomEquivRestrictHom _ _ _ θ))) := by
  refine Scheme.Hom.ext rfl (fun W ↦ CommRingCat.hom_ext (RingHom.ext fun s ↦ ?_))
  refine (CommRingCat.comp_apply _ _ s).trans ((presheaf_map_self _ _).trans ?_)
  rw [homSectionAct_app, derivationActionSheaf_app,
    derivationSectionι_eq_conormalSection hsq pY' cb θ W ((j.app W).hom s)]
  rfl

/-- **The difference derivation of [Stacks Project, Tag 04FG] depends only on the pair of
lifts**: everything else it is given is a proposition. Stated over an arbitrary pair, so that the
substitution happens on small terms. -/
private theorem differenceDerivation_congr_lift {T T' : Scheme.{u}} {k : T ⟶ T'}
    [IsClosedImmersion k] {aa : T ⟶ Y} {b' : T' ⟶ Y'} (q : Y' ⟶ S) (hk : k.ker ^ 2 = ⊥)
    {L₁ L₂ : T' ⟶ Y'} (hL : L₁ = L₂)
    (hq₁ : b' ≫ q = L₁ ≫ q) (c₁ : k ≫ L₁ = aa ≫ j) (cb : k ≫ b' = aa ≫ j)
    (hC₁ : immersionConormalSheafMap k j aa L₁ (toShHom_square c₁) =
      immersionConormalSheafMap k j aa b' (toShHom_square cb))
    (hq₂ : b' ≫ q = L₂ ≫ q) (c₂ : k ≫ L₂ = aa ≫ j)
    (hC₂ : immersionConormalSheafMap k j aa L₂ (toShHom_square c₂) =
      immersionConormalSheafMap k j aa b' (toShHom_square cb)) :
    differenceDerivation q hk hq₁ c₁ cb hC₁ = differenceDerivation q hk hq₂ c₂ cb hC₂ := by
  subst hL
  rfl

/-- **Two morphisms whose postcompositions with a derivation agree, agree on the differentials.**
Stated over arbitrary `F₁`, `F₂` so that the defeq check happens on variables: at the point of use
the two morphisms are large terms. -/
private theorem derivation_postcomp_congr_app {Y₁ S₁ : Scheme.{u}} {q : Y₁ ⟶ S₁}
    {M N : Y₁.Modules} (Dv : SheafOfModules.SheafDerivation (inverseImageStructureMap q) M)
    {F₁ F₂ : M ⟶ N} (h : Dv.postcomp F₁.val = Dv.postcomp F₂.val) (W : Y₁.Opens) (s : Γ(Y₁, W)) :
    (F₁.val.app (op W)).hom (Dv.d s) = (F₂.val.app (op W)).hom (Dv.d s) :=
  PresheafOfModulesOfCommRing.Derivation.congr_d h s

/-- **A derivation datum is determined by the lift `θ ⬝ b` it produces.** -/
private theorem derivationDatum_eq_of_derivationActionSheaf_eq {T T' : Scheme.{u}} {k : T ⟶ T'}
    [IsClosedImmersion k] {aa : T ⟶ Y} {b' : T' ⟶ Y'} (q : Y' ⟶ S) (hk : k.ker ^ 2 = ⊥)
    (cb : k ≫ b' = aa ≫ j)
    {ψ₁ ψ₂ : (Scheme.Modules.pullback aa).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
      conormalModules k}
    (h : derivationActionSheaf hk q cb ψ₁ = derivationActionSheaf hk q cb ψ₂) : ψ₁ = ψ₂ := by
  have hDD : derivationActionDifferenceDerivation hk q cb ψ₁
      = derivationActionDifferenceDerivation hk q cb ψ₂ :=
    differenceDerivation_congr_lift q hk h _ _ cb _ _ _ _
  rw [derivationActionDifferenceDerivation_eq, derivationActionDifferenceDerivation_eq] at hDD
  exact pullback_relativeDifferentials_hom_ext aa (j ≫ q)
    (fun W s ↦ derivation_postcomp_congr_app _ hDD W s)

/-- **A section of `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` is determined by the lift it
produces.**

The two lifts are `θ ⬝ b` in the derivation track as well
(`Stacks.Thickenings.homSectionAct_eq_derivationActionSheaf`), so the difference derivations of
[Stacks Project, Tag 04FG] attached to the two pairs agree; by [Stacks Project, Tag 0CK1]
(`Stacks.Thickenings.derivationActionDifferenceDerivation_eq`) those are `d_{Y/S}` followed by
the two data — which is more than the comorphisms give, since it is an equality of derivations on
*every* section of `𝒪_Y` and not only on the image of `j^♯` — and a datum is determined by that
(`Stacks.Thickenings.pullback_relativeDifferentials_hom_ext`). The three translations of the
conormal-track bridge are bijections, so the data themselves agree. -/
@[ega "IV 16.5.14" "partial"]
theorem deformationHomSections_ext (hsq : i.ker ^ 2 = ⊥) (pY' : Y' ⟶ S)
    (cb : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    {θ η : deformationHomSections i a (j ≫ pY') V}
    (h : homSectionAct hsq pY' cb θ = homSectionAct hsq pY' cb η) : θ = η := by
  have hψ := derivationDatum_eq_of_derivationActionSheaf_eq pY'
    (ker_pow_morphismRestrict_eq_bot i hsq V) cb
    ((homSectionAct_eq_derivationActionSheaf hsq pY' cb θ).symm.trans
      (h.trans (homSectionAct_eq_derivationActionSheaf hsq pY' cb η)))
  exact (Stacks.Modules.overHomEquivRestrictHom _ _ _).injective
    ((restrictDerivationDatumEquiv i a (j ≫ pY') V).injective
      ((derivationDatumEquiv ((i ⁻¹ᵁ V).ι ≫ a) (j ≫ pY')
        (conormalModules (i ∣_ V))).injective hψ))

end Transitivity

/-! ### The transitivity clause of Tag 04FJ -/

section Statement

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'}
  [IsClosedImmersion i] [IsImmersion j]

/-- **[Stacks Project, Tag 04FJ], the transitivity clause, for arbitrary schemes.** Let `S` be a
scheme, let `i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` be an immersion, let
`a : X ⟶ Y` be a morphism and let `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` be a map of `𝒪_X`-modules. Over an
open `V` of `X'` **carrying a lift**, the action of
`SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` of `Stacks.Thickenings.compatibleLiftsVAdd` on the lifts of
[Stacks Project, Tag 04FI] is **simply transitive**: for any two lifts `b₀`, `c₀` over `V` there
is exactly one section carrying `b₀` to `c₀`.

No affineness is assumed, of `S`, `X'`, `Y'` or `V`.

Existence is the unrestricted [Stacks Project, Tag 04FG] read for the restricted thickening
`i ∣_ V` and transported to the deformation sheaf's conormal track
(`Stacks.Thickenings.exists_isDerivationAction_over`), followed by the uniqueness half of
[Stacks Project, Tag 02H5] (`Stacks.Thickenings.eq_of_isDerivationAction`) identifying the lift it
produces with `θ ⬝ b₀` (`Stacks.Thickenings.homSectionAct_eq_derivationActionSheaf`). Uniqueness of
the section is `Stacks.Thickenings.deformationHomSections_ext`. -/
@[stacks 04FJ "simple transitivity over an open carrying a lift, for arbitrary schemes",
  ega "IV 16.5.14" "more general"]
theorem existsUnique_compatibleLiftsVAdd_eq (hsq : i.ker ^ 2 = ⊥) (pX' : X' ⟶ S) (pY' : Y' ⟶ S)
    (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) (b₀ c₀ : compatibleLifts pX' pY' a A V) :
    ∃! θ : deformationHomSections i a (j ≫ pY') V,
      compatibleLiftsVAdd hsq pX' pY' a A V θ b₀ = c₀ := by
  obtain ⟨θ, hθ⟩ := exists_isDerivationAction_over hsq pY' V
    (c₀.2.1.trans b₀.2.1.symm) b₀.2.2.choose c₀.2.2.choose
    (b₀.2.2.choose_spec.trans c₀.2.2.choose_spec.symm)
  have heq : c₀.1 = derivationActionSheaf (ker_pow_morphismRestrict_eq_bot i hsq V) pY'
      b₀.2.2.choose (derivationDatumOfCotangent (restrictDerivationDatumEquiv i a (j ≫ pY') V
        (Stacks.Modules.overHomEquivRestrictHom _ _ _ θ))) :=
    eq_of_isDerivationAction (ker_pow_morphismRestrict_eq_bot i hsq V) pY' b₀.2.2.choose
      c₀.2.2.choose (derivationActionSheaf_comm _ pY' b₀.2.2.choose _) hθ
      (isDerivationAction_derivationActionSheaf _ pY' b₀.2.2.choose _)
  have hact : homSectionAct hsq pY' b₀.2.2.choose θ = c₀.1 :=
    (homSectionAct_eq_derivationActionSheaf hsq pY' b₀.2.2.choose θ).trans heq.symm
  exact ⟨θ, Subtype.ext hact, fun η hη ↦ deformationHomSections_ext hsq pY' b₀.2.2.choose
    ((congrArg Subtype.val hη).trans hact.symm)⟩

end Statement

end Stacks.Thickenings

end
