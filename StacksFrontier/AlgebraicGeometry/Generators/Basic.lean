module

public import StacksFrontier.AlgebraicGeometry.CotangentAppIsoGenerator.Engine
public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Sections

/-!
# The part (1) shape of the generator engine of [Stacks, Tag 01R3]

On an affine open `V` of a closed-immersion factorization `i' : Z ⟶ U` of an immersion
`i : Z ⟶ X`, the identification of `Γ(i'_* C_{Z/X}, V)` with `I.Cotangent` carries the quotient
generator attached to a section `x` of the ideal sheaf of `i'` to the class of `x`'s image in the
structure sheaf; that is the part (1) label "canonical affine quotient formula" of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3), proved as
`Stacks.Conormal.pushforwardConormalIsoCotangent_apply`.

This file carries what the generator machinery needs at that shape: the hypothesis `hc` of the
engine, and the sections and restriction maps the formula is read through.

## The transports

`StacksFrontier.AlgebraicGeometry.CotangentAppIsoGenerator.Engine` proves the generator formula
for the engine — `affineSectionsIsoCotangent_apply` — *taking as a hypothesis* `hc`, a
characterization of the locality comparison fed into it, and leaves `hc` open at both shapes of
[Stacks, Tag 01R3]. At the shape used by
`Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent` the comparison is
`Stacks.Conormal.Locality.conormalSheafRestrictIso`, whose generator formula
`Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app` has exactly the right
content but stated over the two opens `(i' ⁻¹ᵁ V).ι ⁻¹ᵁ (i' ⁻¹ᵁ V)` and `V.ι ⁻¹ᵁ V`, each of
which is `⊤` but **not definitionally** — whereas `hc` is stated over `⊤`, because the engine
reads a direct image on sections there (see the first of the four tooling facts in that file's
module docstring). Two transports are therefore needed, plus an identification of
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`'s restriction map with the
restriction map appearing in that formula.

**The transports are free because `X.Opens` is a poset, so its hom-sets are subsingletons.**
Every map in sight between sections over two opens is a presheaf restriction map along *the*
morphism of opens, so any two such maps with the same source and target agree, and composites
collapse by functoriality. The `res_*` lemmas below are that
observation; `inner_eq` and `hc_part_one` are then bookkeeping, and no new mathematics about the
conormal sheaf is used.

## Main results

* `Stacks.Conormal.Tag01R3Generators.hc_part_one`: **the hypothesis `hc` of the engine,
  discharged at the part (1) shape.** The locality comparison of a closed-immersion
  factorization carries the restriction to the top open of the quotient generator attached to a
  section `x` of the ideal sheaf of `i'` over `V` to the unit generator attached to
  `restrictIdealSectionTop i' V x`. No affineness, Noetherian or finiteness hypothesis appears,
  and the factorization is arbitrary.
* `Stacks.Conormal.Tag01R3Generators.exists_model_section`: the section of the affine model's
  ideal sheaf named by an element of the ideal. Its existence is
  `Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff` at the vanishing
  `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality` provides.
* `Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop`: the image in the structure
  sheaf of the transported section is the image of `x`, carried by
  `AlgebraicGeometry.Scheme.Opens.topIso`. This is what matches the naming of a generator
  by a ring element in [Stacks, Tag 01R3] with the affine model's.
* `res_eq`, `res_self`, `res_comp`, `res_injective`, `restrict_res`, `pushforward_res`,
  `sres_eq`, `sres_comp`: the restriction-map calculus described above.

## Universe situation

A single universe `u`.

## What is not done

* **No labelled assertion is discharged here.** [Stacks, Tag 01R3] has twelve labels; the part (1)
  "canonical affine quotient formula" they serve is proved in
  `StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Factorization`.
* **Nothing about part (2).** The part (2) identification is the projection of a
  generator-carrying subtype, and its comparison is
  `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe` rather than
  `Stacks.Conormal.Locality.conormalSheafRestrictIso`; the extra factor
  `Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget` still has no
  elementwise description, so `hc` is not discharged at that shape. What `hc_part_one` *does*
  settle is the harder half: the transport pattern that the part (2) shape needs as well.
* **Nothing about the square of the ideal or epimorphy of the quotient map.** The part (1) labels
  "sheaf quotient map is epimorphic" and "quotient by the ideal square" are untouched; the latter
  would follow from this file's formula together with `Ideal.toCotangent_eq_zero` as soon as a
  presentation `(I, e, he)` is *produced* at `I = i'.ker.ideal ⟨V, hV⟩`, which nothing here does.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.AffinePushforward

universe u

namespace Stacks.Conormal.Tag01R3Generators

open Stacks.Conormal.AffineCotangent

/-! ### The restriction-map calculus

`X.Opens` is a poset, so there is at most one morphism between two opens and any two presheaf
restriction maps with the same source and target agree. These four lemmas are that observation
for a sheaf of modules; everything in this file that moves a section between two opens that are
*equal but not definitionally equal* is one of them. -/

section Res

variable {Y : Scheme.{u}} (P : Y.Modules)

/-- Two restriction maps of a sheaf of modules between the same two opens agree: the hom-sets of
`Y.Opens` are subsingletons. -/
theorem res_eq {W₁ W₂ : Y.Opens} (g g' : W₂ ⟶ W₁) (t : P.val.obj (.op W₁)) :
    P.val.map g.op t = P.val.map g'.op t :=
  P.val.congr_map_apply (by rw [Subsingleton.elim g g']) t

/-- A restriction map from an open to itself is the identity. -/
theorem res_self {W : Y.Opens} (g : W ⟶ W) (t : P.val.obj (.op W)) :
    P.val.map g.op t = t := by
  rw [P.val.congr_map_apply (Subsingleton.elim g.op (𝟙 (Opposite.op W))) t, P.val.map_id]
  simp
  rfl

/-- Two restriction maps in succession are one restriction map. -/
theorem res_comp {W₁ W₂ W₃ : Y.Opens} (g : W₂ ⟶ W₁) (g' : W₃ ⟶ W₂) (g'' : W₃ ⟶ W₁)
    (t : P.val.obj (.op W₁)) :
    P.val.map g'.op (P.val.map g.op t) = P.val.map g''.op t :=
  (P.val.map_comp_apply g.op g'.op t).symm.trans
    (P.val.congr_map_apply (Subsingleton.elim _ _) t)

/-- A restriction map between two opens that admit morphisms both ways — in particular between
two opens that are equal — is injective on sections. -/
theorem res_injective {W₁ W₂ : Y.Opens} (g : W₂ ⟶ W₁) (g' : W₁ ⟶ W₂)
    {t t' : P.val.obj (.op W₁)}
    (hh : P.val.map g.op t = P.val.map g.op t') : t = t' :=
  ((res_comp P g g' (𝟙 W₁) t).trans (res_self P _ t)).symm.trans
    ((congrArg (P.val.map g'.op) hh).trans
      ((res_comp P g g' (𝟙 W₁) t').trans (res_self P _ t')))

end Res

/-- A restriction map of the restriction of a module to an open subscheme is a restriction map of
the module, between the image opens. -/
theorem restrict_res {Y : Scheme.{u}} (O : Y.Opens) (N : Y.Modules)
    {W₁ W₂ : O.toScheme.Opens} (g : W₂ ⟶ W₁) (g' : O.ι ''ᵁ W₂ ⟶ O.ι ''ᵁ W₁)
    (t : N.val.obj (.op (O.ι ''ᵁ W₁))) :
    ((Scheme.Modules.restrictFunctor O.ι).obj N).val.map g.op t = N.val.map g'.op t :=
  res_eq N (O.ι.opensFunctor.map g) g' t

/-- A restriction map of a direct image is a restriction map of the module, between the preimage
opens. -/
theorem pushforward_res {A B : Scheme.{u}} (f : A ⟶ B) (N : A.Modules) {W₁ W₂ : B.Opens}
    (g : W₂ ⟶ W₁) (g' : f ⁻¹ᵁ W₂ ⟶ f ⁻¹ᵁ W₁) (t : N.val.obj (.op (f ⁻¹ᵁ W₁))) :
    ((Scheme.Modules.pushforward f).obj N).val.map g.op t = N.val.map g'.op t :=
  res_eq N ((Opens.map f.base).map g) g' t

/-- Two restriction maps of the structure sheaf between the same two opens agree. -/
theorem sres_eq {Y : Scheme.{u}} {W₁ W₂ : Y.Opens} (g g' : W₂ ⟶ W₁) (t : Γ(Y, W₁)) :
    (Y.presheaf.map g.op).hom t = (Y.presheaf.map g'.op).hom t := by
  rw [Subsingleton.elim g g']

/-- Two restriction maps of the structure sheaf in succession are one restriction map. -/
theorem sres_comp {Y : Scheme.{u}} {W₁ W₂ W₃ : Y.Opens} (g : W₂ ⟶ W₁) (g' : W₃ ⟶ W₂)
    (g'' : W₃ ⟶ W₁) (t : Γ(Y, W₁)) :
    (Y.presheaf.map g'.op).hom ((Y.presheaf.map g.op).hom t) =
      (Y.presheaf.map g''.op).hom t := by
  have h : Y.presheaf.map g.op ≫ Y.presheaf.map g'.op = Y.presheaf.map g''.op := by
    rw [← Y.presheaf.map_comp, Subsingleton.elim (g.op ≫ g'.op) g''.op]
  exact congr($(h).hom t)

/-! ### The section of the restricted ideal sheaf named by a section of the ideal sheaf -/

/-- The section of the restriction to `V` of the ideal sheaf of `f` that a section `x` of the
ideal sheaf over `V` becomes, read as a section of the ideal sheaf of `f ∣_ V` over `V.ι ⁻¹ᵁ V`.
This is the section appearing on the right of
`Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app`. -/
noncomputable abbrev zSec {A B : Scheme.{u}} (f : A ⟶ B) (V : B.Opens)
    (x : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op V)) :
    (Stacks.ClosedImmersion.idealSheaf (f ∣_ V).toLRSHom.toShHom).val.obj
      (.op (V.ι ⁻¹ᵁ V)) :=
  (Restriction.restrictIdealSheafIso' f V).hom.val.app (.op (V.ι ⁻¹ᵁ V))
    ((Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.map
      (homOfLE (V.ι.image_preimage_le V)).op x)

/-- `zSec` moved to the top open along `AlgebraicGeometry.Scheme.Opens.ι_preimage_self`. This is
the section of the ideal sheaf of `f ∣_ V` that the engine's hypothesis `hc` is stated at. -/
noncomputable def restrictIdealSectionTop {A B : Scheme.{u}} (f : A ⟶ B) (V : B.Opens)
    (x : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op V)) :
    (Stacks.ClosedImmersion.idealSheaf (f ∣_ V).toLRSHom.toShHom).val.obj
      (.op (⊤ : V.toScheme.Opens)) :=
  (Stacks.ClosedImmersion.idealSheaf (f ∣_ V).toLRSHom.toShHom).val.map
      (eqToHom V.ι_preimage_self.symm).op (zSec f V x)

/-- **The image in the structure sheaf of `restrictIdealSectionTop`.** It is the image of `x`,
carried by `AlgebraicGeometry.Scheme.Opens.topIso`.

Four steps, each one of the restriction-map lemmas or an existing characterization: naturality of
`CategoryTheory.Limits.kernel.ι`, then
`Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι` for the comparison of the two ideal
sheaves, then naturality of `kernel.ι` again, and finally the collapse of the three remaining
restriction maps of the structure sheaf into the one that `topIso` is.
`AlgebraicGeometry.Scheme.Opens.ι_appIso` being `Iso.refl` is what makes the middle step a
restriction map rather than a transport. -/
theorem image_restrictIdealSectionTop {A B : Scheme.{u}} (f : A ⟶ B) (V : B.Opens)
    (x : (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom).val.obj (.op V)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (f ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)
        (restrictIdealSectionTop f V x) =
      V.topIso.inv.hom ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom f.toLRSHom.toShHom))).val.app (.op V) x) := by
  refine Eq.trans (PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom (f ∣_ V).toLRSHom.toShHom))).val
    (eqToHom V.ι_preimage_self.symm).op (zSec f V x)) ?_
  refine Eq.trans (res_eq (SheafOfModules.unit
      (structureSheafRing V.toScheme.toLocallyRingedSpace.toRingedSpace))
    (eqToHom V.ι_preimage_self.symm) (homOfLE (le_of_eq V.ι_preimage_self.symm)) _) ?_
  refine Eq.trans (Locality.unitModule_val_map (le_of_eq V.ι_preimage_self.symm) _) ?_
  refine Eq.trans (congrArg (V.toScheme.presheaf.map
      (homOfLE (le_of_eq V.ι_preimage_self.symm)).op).hom
    (Locality.restrictIdealSheafIso'_app_ι f V (V.ι ⁻¹ᵁ V) _)) ?_
  refine Eq.trans (congrArg (V.toScheme.presheaf.map
      (homOfLE (le_of_eq V.ι_preimage_self.symm)).op).hom
    (congrArg (V.ι.appIso (V.ι ⁻¹ᵁ V)).hom
      (PresheafOfModules.naturality_apply
        (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom f.toLRSHom.toShHom))).val
        (homOfLE (V.ι.image_preimage_le V)).op x))) ?_
  rw [Scheme.Opens.ι_appIso]
  refine Eq.trans (congrArg (V.toScheme.presheaf.map
      (homOfLE (le_of_eq V.ι_preimage_self.symm)).op).hom
    (Locality.unitModule_val_map (V.ι.image_preimage_le V) _)) ?_
  rw [Scheme.Opens.topIso_inv]
  exact sres_comp (Y := B) _ _ _ _

/-! ### The section of the affine model's ideal sheaf named by an element of the ideal -/

/-- **An element of `I` names a global section of the ideal sheaf of
`Spec (R ⧸ I) ⟶ Spec R`.** This is the datum `x` of
`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent`'s generator formula, produced rather
than hypothesised.

The section exists by
`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff`, whose hypothesis is
that `(Spec.map (Ideal.Quotient.mk I)).app ⊤` kills `(Scheme.ΓSpecIso R).inv a`; by
`AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality` that image is
`(Scheme.ΓSpecIso (R ⧸ I)).inv` of the class of `a`, which is zero. -/
theorem exists_model_section {R : CommRingCat.{u}} (I : Ideal R) (a : I) :
    ∃ xm : (Stacks.ClosedImmersion.idealSheaf
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom).val.obj
          (.op (⊤ : (Spec R).Opens)),
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom))).val.app
            (.op ⊤) xm = (Scheme.ΓSpecIso R).inv (a : R) := by
  refine (Sections.exists_idealSheaf_section_iff
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⊤ _).mpr ?_
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have h2 : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).app ⊤).hom
      ((Scheme.ΓSpecIso R).inv (a : R)) =
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv (Ideal.Quotient.mk I (a : R)) :=
    (congr($(h).hom (a : R))).symm
  rw [h2, show Ideal.Quotient.mk I (a : R) = 0 from (Ideal.Quotient.eq_zero_iff_mem).2 a.2]
  exact map_zero _

/-! ### The engine's hypothesis `hc`, at the part (1) shape -/

section Inner

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
  (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
  (V : U.toScheme.Opens)
  (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op V))

/-- The quotient generator attached to `x`, moved to the top open of `V.toScheme`: the section of
the restriction to `V` of `i'_* C_{Z/X}` that the engine's hypothesis `hc` is stated at. -/
noncomputable abbrev mSec :
    ((Scheme.Modules.pushforward i').obj (Stacks.Conormal.conormalSheaf i)).val.obj
      (.op (V.ι ''ᵁ (⊤ : V.toScheme.Opens))) :=
  ((Scheme.Modules.pushforward i').obj (Stacks.Conormal.conormalSheaf i)).val.map
    (eqToHom V.ι_image_top).op
      ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op V) x)

/-- **`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` against the restriction
map of the locality formula.** Both carry the quotient generator attached to `x` over `V`
to its restriction to the top open; they are a composite of two restriction maps of
`Stacks.Conormal.conormalSheaf i` and a single one, so they agree by `res_comp`.

`Stacks.Conormal.Restriction.restrictPushforwardIso_hom_app` identifies the comparison with a
restriction map, which is what makes this a calculation in the poset `Z.Opens` rather than a
statement about the comparison. -/
theorem inner_eq :
    ((Scheme.Modules.restrictFunctor (i' ⁻¹ᵁ V).ι).obj
          (Stacks.Conormal.conormalSheaf i)).val.map
        (eqToHom ((i' ⁻¹ᵁ V).ι_preimage_self)).op
        (((restrictPushforwardIso i' V).app (Stacks.Conormal.conormalSheaf i)).hom.val.app
          (.op ⊤) (mSec i U i' hfac V x)) =
      (Stacks.Conormal.conormalSheaf i).val.map
        (homOfLE ((i' ⁻¹ᵁ V).ι.image_preimage_le (i' ⁻¹ᵁ V))).op
          ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op V) x) := by
  refine Eq.trans (restrict_res (i' ⁻¹ᵁ V) (Stacks.Conormal.conormalSheaf i) _
    (homOfLE ((i' ⁻¹ᵁ V).ι.image_mono le_top)) _) ?_
  have h := (Restriction.restrictPushforwardIso_hom_app i' V (Stacks.Conormal.conormalSheaf i) ⊤
      (mSec i U i' hfac V x)).trans <|
    (congrArg ((Stacks.Conormal.conormalSheaf i).val.map
      (eqToHom (image_morphismRestrict_preimage i' V ⊤)).op).hom
      (pushforward_res i' (Stacks.Conormal.conormalSheaf i) (eqToHom V.ι_image_top)
        (homOfLE (i'.preimage_mono (le_of_eq V.ι_image_top))) _)).trans
      (res_comp (Stacks.Conormal.conormalSheaf i) _ _
        (eqToHom (image_morphismRestrict_preimage i' V ⊤) ≫
          homOfLE (i'.preimage_mono (le_of_eq V.ι_image_top))) _)
  refine Eq.trans (congrArg (fun z => (Stacks.Conormal.conormalSheaf i).val.map
      (homOfLE ((i' ⁻¹ᵁ V).ι.image_mono (le_top (a := (i' ⁻¹ᵁ V).ι ⁻¹ᵁ (i' ⁻¹ᵁ V))))).op z) h) ?_
  exact res_comp (Stacks.Conormal.conormalSheaf i) _ _ _ _

/-- **The engine's hypothesis `hc`, at the part (1) shape of [Stacks, Tag 01R3].** For an
immersion `i : Z ⟶ X`, *any* closed-immersion factorization `i' : Z ⟶ U` of it and any open `V`
of `U`, the locality comparison `Stacks.Conormal.Locality.conormalSheafRestrictIso` carries the
quotient generator attached to a section `x` of the ideal sheaf of `i'` over `V` — restricted to
the top open along `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` — to the
unit generator attached to `restrictIdealSectionTop i' V x`.

This is the one further argument that
`StacksFrontier.AlgebraicGeometry.CotangentAppIsoGenerator.Engine` says
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` needs, at the shape
`pushforwardConormalSectionsIsoCotangent` feeds in. It is
`Stacks.Conormal.Locality.conormalSheafRestrictIso_unit_app` transported from the opens
`(i' ⁻¹ᵁ V).ι ⁻¹ᵁ (i' ⁻¹ᵁ V)` and `V.ι ⁻¹ᵁ V` to the top opens: the left-hand side by naturality
of the comparison together with `inner_eq`, the right-hand side by naturality of the unit
together with `res_comp`, and the two transports are cancelled by `res_injective`.

No affineness, Noetherian or finiteness hypothesis appears, and nothing is special to the
coborder factorization. -/
theorem hc_part_one :
    ((Locality.conormalSheafRestrictIso i U i' hfac V).hom.val.app (.op ⊤)).hom
        ((((restrictPushforwardIso i' V).app (Stacks.Conormal.conormalSheaf i)).hom.val.app
            (.op ⊤)).hom
          ((((Scheme.Modules.pushforward i').obj (Stacks.Conormal.conormalSheaf i)).val.map
            (eqToHom V.ι_image_top).op).hom
              ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op V) x))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (i' ∣_ V)).unit.app
        (Stacks.ClosedImmersion.idealSheaf (i' ∣_ V).toLRSHom.toShHom)).val.app (.op ⊤)).hom
          (restrictIdealSectionTop i' V x) := by
  have K := Locality.conormalSheafRestrictIso_unit_app i U i' hfac V x
  refine res_injective
    ((Scheme.Modules.pullback (i' ∣_ V)).obj
      (Stacks.ClosedImmersion.idealSheaf (i' ∣_ V).toLRSHom.toShHom))
    (eqToHom ((i' ⁻¹ᵁ V).ι_preimage_self)) (eqToHom ((i' ⁻¹ᵁ V).ι_preimage_self).symm) ?_
  refine Eq.trans ?_ (K.trans ?_)
  · refine Eq.trans (PresheafOfModules.naturality_apply
      (Locality.conormalSheafRestrictIso i U i' hfac V).hom.val
      (eqToHom ((i' ⁻¹ᵁ V).ι_preimage_self)).op
      (((restrictPushforwardIso i' V).app (Stacks.Conormal.conormalSheaf i)).hom.val.app
        (.op ⊤) (mSec i U i' hfac V x))).symm ?_
    exact congrArg (fun z => (Locality.conormalSheafRestrictIso i U i' hfac V).hom.val.app
      (.op ((i' ⁻¹ᵁ V).ι ⁻¹ᵁ (i' ⁻¹ᵁ V))) z) (inner_eq i U i' hfac V x)
  · refine Eq.trans (res_comp
      ((Scheme.Modules.pullback (i' ∣_ V)).obj
        (Stacks.ClosedImmersion.idealSheaf (i' ∣_ V).toLRSHom.toShHom))
      (homOfLE ((i' ∣_ V).preimage_mono (le_of_eq V.ι_preimage_self.symm)))
      (eqToHom ((i' ⁻¹ᵁ V).ι_preimage_self))
      (eqToHom (Locality.preimage_ι_preimage_eq i' V))
      (((Scheme.Modules.pullbackPushforwardAdjunction (i' ∣_ V)).unit.app
        (Stacks.ClosedImmersion.idealSheaf (i' ∣_ V).toLRSHom.toShHom)).val.app
          (.op (V.ι ⁻¹ᵁ V)) (zSec i' V x))).symm ?_
    refine congrArg (fun z => ((Scheme.Modules.pullback (i' ∣_ V)).obj
      (Stacks.ClosedImmersion.idealSheaf (i' ∣_ V).toLRSHom.toShHom)).val.map
      (eqToHom ((i' ⁻¹ᵁ V).ι_preimage_self)).op z) ?_
    exact ((PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction (i' ∣_ V)).unit.app
        (Stacks.ClosedImmersion.idealSheaf (i' ∣_ V).toLRSHom.toShHom)).val
      (eqToHom V.ι_preimage_self.symm).op (zSec i' V x)).trans
      (pushforward_res (i' ∣_ V)
        ((Scheme.Modules.pullback (i' ∣_ V)).obj
          (Stacks.ClosedImmersion.idealSheaf (i' ∣_ V).toLRSHom.toShHom))
        (eqToHom V.ι_preimage_self.symm)
        (homOfLE ((i' ∣_ V).preimage_mono (le_of_eq V.ι_preimage_self.symm))) _)).symm

end Inner

end Stacks.Conormal.Tag01R3Generators

end
