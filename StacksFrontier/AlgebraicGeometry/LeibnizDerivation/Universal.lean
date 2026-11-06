module

public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Basic
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Vanishing

/-!
# The canonical morphism `Ω_{X/S} ⟶ C_Δ` of [Stacks, Tag 08S2]

`StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Basic` proved the four derivation axioms
for the conormal class `Stacks.LeibnizDerivation.cls` of `p₂^♯ b - p₁^♯ b`. This file assembles
them into a derivation, feeds it to the universal property of the sheaf of relative
differentials, and proves that the resulting morphism satisfies the generator formula of
[Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2) at *every* open of the coborder
neighbourhood of the diagonal admitting the tag's two containments — not only at the canonical
chart the derivation is built from.

The passage from the tag's arbitrary auxiliary open `V` to the canonical chart is a
*restriction*: `le_chart_preimage_self` says `V ≤ chart f (Δ.liftCoborder ⁻¹ᵁ V)`, and the two
have the same preimage, so the restriction map of the conormal sheaf involved is the same
morphism of opens on both sides. No independence-of-the-auxiliary-open statement is used, and
neither is the statement that the quotient map kills the square of the ideal.

## Main definitions

* `Stacks.LeibnizDerivation.comorphismDerivation`: the derivation of `𝒪_X` along the comorphism
  of `f` with values in the conormal sheaf of the diagonal, built from `cls_add`, `cls_mul`,
  `cls_restrict` and `cls_app_eq_zero`.
* `Stacks.LeibnizDerivation.structuralDerivation`: the same, read along the structural map
  `f⁻¹𝒪_S ⟶ 𝒪_X`, which is the form the universal property consumes.
* `Stacks.LeibnizDerivation.toConormal`: **the canonical morphism
  `Ω_{X/S} ⟶ C_Δ`.**

## Main results

* `Stacks.LeibnizDerivation.toConormal_d`: `toConormal` sends `d b` to `cls f U b`.
* `Stacks.LeibnizDerivation.eq_toConormal`: it is the unique morphism with that property.
* `Stacks.LeibnizDerivation.toConormal_d_eq_quotientMap`: **the generator formula of
  [Stacks, Tag 08S2]** — `toConormal` sends `d b` to the image of `p₂^♯ b - p₁^♯ b` under
  `Stacks.Conormal.conormalQuotientMap`, in the tag's own spelling of the hypotheses.

## Route

`Stacks.AlgebraicGeometry.AffineDifferentialsIso.toStructuralDerivation`
(`StacksFrontier/AlgebraicGeometry/AffineDifferentialsIso/Vanishing.lean`) converts a derivation
along the comorphism into one along the structural map; the underlying additive maps and the
Leibniz and restriction data are unchanged, and only the vanishing condition is transported.
`AlgebraicGeometry.SheafOfModules.universalDerivation_isUniversal`
(`StacksFrontier/Topology/Sheaves/Modules/Differentials.lean`, tag 08RM) then gives the morphism
and its uniqueness.

The generator formula is `Stacks.Conormal.Locality.conormalQuotientMap_restrict` applied to
`le_chart_preimage_self`, with the two sections of the ideal sheaf matched by
`Stacks.Conormal.Locality.idealSheaf_section_injective`: the restriction of the canonical ideal
section to `V` has the same image in the structure sheaf as the tag's `x`, which is
`Stacks.DiagonalDerivation.diagonalDelta_eq`.

## What is not done

**`toConormal` is not shown to be an isomorphism.** That is the remaining content of
[Stacks, Tag 08S2] and it is a separate, affine-local matter: the two named missing statements
are an affine comparison

  `Stacks.LeibnizDerivation.affineConormalIsoKaehler`, giving, for an affine open `U ≤ f ⁻¹ᵁ V`
  with `V` an affine open of `S`, an isomorphism
  `(Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) ≅`
  `CommRingCat.KaehlerDifferential (f.appLE V U hUV)` carrying `cls f U b` to
  `CommRingCat.KaehlerDifferential.d b`,

and then

  `Stacks.LeibnizDerivation.isIso_toConormal`, that `toConormal f` is an isomorphism,

both intended for `StacksFrontier/AlgebraicGeometry/LeibnizDerivation/Affine.lean`. The second
follows from the first together with
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso` (tag
01UT, proved) and
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict` (proved). The first is the
open one: its sheaf-level half is
`Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel` and its ring-level half is
`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` together with
`Stacks.DiagonalConormal.kaehlerDifferential_eq_cotangent` and
`Stacks.DiagonalConormal.toCotangent_one_tmul_sub_tmul_one`, but no generator formula is
available for the first of those, and the comparison of the two scalar actions that its own
module docstring records as missing is exactly what carrying `cls` across it needs.

## Vocabulary

The module of relative differentials and the universal relative derivation of Stacks Tag 01US are
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and
`AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation`
(`StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative`); the conormal sheaf of Stacks
Tag 01R2 is `Stacks.Conormal.conormalSheaf` and the quotient map of Stacks Tag 01R3 is
`Stacks.Conormal.conormalQuotientMap`; the ideal sheaf of Stacks Tag 01C2 is
`Stacks.ClosedImmersion.idealSheaf`.

No `stacks` attribute is attached. Under the covering-set rule the bare label of
[Stacks, Tag 08S2] is carried by the comparison *isomorphism*, which is not constructed here,
and its "canonical quotient formula" label is carried by a statement about that isomorphism's
hom; `toConormal_d_eq_quotientMap` is that statement for the canonical morphism, which is not
the same assertion.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.LeibnizDerivation

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `cls` vanishes on the image of `Γ(S, V)` in `Γ(X, f ⁻¹ᵁ V)`. -/
theorem cls_app_eq_zero (V : S.Opens) (a : Γ(S, V)) :
    cls f (f ⁻¹ᵁ V) ((f.app V).hom a) = 0 := by
  refine Eq.trans (congrArg (cls f (f ⁻¹ᵁ V)) (congr($(Scheme.Hom.app_eq_appLE f) a))) ?_
  exact cls_appLE_eq_zero f V (f ⁻¹ᵁ V) le_rfl a

/-- **The canonical derivation of [Stacks, Tag 08S2], along the comorphism of `f`.** Its value
on a section `b` of `𝒪_X` over `U` is the conormal class of `p₂^♯ b - p₁^♯ b`, formed over the
canonical open `chart f U`. The four axioms are `cls_add`, `cls_mul`, `cls_restrict` and
`cls_app_eq_zero`. -/
noncomputable def comorphismDerivation :
    PresheafOfModulesOfCommRing.Derivation
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val f.c where
  d {W} := AddMonoidHom.mk' (cls f W.unop) (cls_add f W.unop)
  d_mul {_} a b := cls_mul f _ a b
  d_map {_ _} g x := (cls_restrict f g.unop.le x).symm
  d_app {W} a := cls_app_eq_zero f W.unop a

/-- The underlying map of `comorphismDerivation` is `cls`. -/
theorem comorphismDerivation_d (U : X.Opens) (b : Γ(X, U)) :
    (comorphismDerivation f).d (X := .op U) b = cls f U b :=
  rfl

/-- **The canonical derivation of [Stacks, Tag 08S2], along the structural map
`f⁻¹𝒪_S ⟶ 𝒪_X`.** This is the single input that the universal property of the sheaf of
relative differentials consumes;
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.toStructuralDerivation` transports the
vanishing condition. -/
noncomputable def structuralDerivation :
    SheafOfModules.SheafDerivation (inverseImageStructureMap f)
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) :=
  Stacks.AlgebraicGeometry.AffineDifferentialsIso.toStructuralDerivation f
    (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) (comorphismDerivation f)

/-- The underlying map of `structuralDerivation` is `cls`. -/
theorem structuralDerivation_d (U : X.Opens) (b : Γ(X, U)) :
    (structuralDerivation f).d (X := .op U) b = cls f U b :=
  rfl

/-- The universal property of the relative differentials, applied to the canonical
derivation. -/
theorem existsUnique_toConormal :
    ∃! g : Scheme.Hom.relativeDifferentials f ⟶
        Stacks.Conormal.conormalSheaf (pullback.diagonal f),
      ((Scheme.Hom.universalRelativeDerivation f).postcomp g.val :
          SheafOfModules.SheafDerivation (inverseImageStructureMap f)
            (Stacks.Conormal.conormalSheaf (pullback.diagonal f))) =
        structuralDerivation f :=
  SheafOfModules.universalDerivation_isUniversal (inverseImageStructureMap f)
    (Stacks.Conormal.conormalSheaf (pullback.diagonal f)) (structuralDerivation f)

/-- **The canonical morphism `Ω_{X/S} ⟶ C_Δ` of [Stacks, Tag 08S2].** -/
noncomputable def toConormal :
    Scheme.Hom.relativeDifferentials f ⟶
      Stacks.Conormal.conormalSheaf (pullback.diagonal f) :=
  (existsUnique_toConormal f).choose

/-- **The defining property of `toConormal`:** it sends `d b` to the conormal class of
`p₂^♯ b - p₁^♯ b`. -/
theorem toConormal_d (U : X.Opens) (b : Γ(X, U)) :
    ((toConormal f).val.app (.op U)).hom
        ((Scheme.Hom.universalRelativeDerivation f).d b) = cls f U b :=
  PresheafOfModulesOfCommRing.Derivation.congr_d (existsUnique_toConormal f).choose_spec.1 b

/-- **`toConormal` is the unique morphism with that property.** -/
theorem eq_toConormal
    (g : Scheme.Hom.relativeDifferentials f ⟶
      Stacks.Conormal.conormalSheaf (pullback.diagonal f))
    (hg : ∀ (U : X.Opens) (b : Γ(X, U)), ((g.val.app (.op U)).hom)
      ((Scheme.Hom.universalRelativeDerivation f).d b) = cls f U b) :
    g = toConormal f :=
  (existsUnique_toConormal f).choose_spec.2 g
    (PresheafOfModulesOfCommRing.Derivation.ext
      (funext fun W => AddMonoidHom.ext fun b => hg W.unop b))

/-! ### The generator formula of [Stacks, Tag 08S2] -/

section Generator

variable (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
  (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
    (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
  (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
    (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))

/-- **Every open admitted by [Stacks, Tag 08S2] is contained in the canonical chart over its
own preimage.** This is what replaces an independence-of-the-auxiliary-open statement: the
tag's arbitrary `V` is compared with `chart f (Δ.liftCoborder ⁻¹ᵁ V)` by a *restriction*, not
by a choice. -/
theorem le_chart_preimage_self
    (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    V ≤ chart f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) :=
  le_chart f _ V h₁ h₂

/-- Restricting `p₂^♯ b - p₁^♯ b` from the canonical chart to the tag's open `V` gives the
tag's own expression. -/
theorem deltaAt_restrict_self (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V)) :
    (((pullback.diagonal f).coborderRange.toScheme.presheaf.map
        (homOfLE (le_chart_preimage_self f V h₁ h₂)).op).hom)
      (deltaAt f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) b) =
      ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b := by
  refine Eq.trans (Stacks.DiagonalDerivation.delta_restrict
    ((pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f)
    ((pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f)
    ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V)
    (chart f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (chart_le_fst f _) (chart_le_snd f _)
    ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) le_rfl V
    (le_chart_preimage_self f V h₁ h₂)
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₁)
    (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₂) b) ?_
  refine Eq.trans (congrArg
    (Stacks.DiagonalDerivation.delta _ _ _ _
      (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₁)
      (Stacks.DiagonalConormal.le_preimage_opensι_comp _ _ h₂))
    (Stacks.DiagonalConormal.presheaf_map_self _ le_rfl b)) ?_
  exact Stacks.DiagonalDerivation.diagonalDelta_eq f V h₁ h₂ b

/-- **The section of the ideal sheaf named by [Stacks, Tag 08S2] is the restriction of the
canonical one.** The tag's hypothesis `hx` determines `x`, the inclusion of the ideal sheaf
being a monomorphism. -/
theorem deltaIdealSection_restrict_self
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V) x =
      ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b) :
    (Stacks.ClosedImmersion.idealSheaf
          (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (le_chart_preimage_self f V h₁ h₂)).op
      (deltaIdealSection f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) b) = x := by
  refine Stacks.Conormal.Locality.idealSheaf_section_injective
    (pullback.diagonal f).liftCoborder V ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val
    (homOfLE (le_chart_preimage_self f V h₁ h₂)).op
    (deltaIdealSection f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) b)) ?_
  refine Eq.trans (Stacks.Conormal.Locality.unitModule_val_map
    (le_chart_preimage_self f V h₁ h₂) _) ?_
  refine Eq.trans (congrArg
    (((pullback.diagonal f).coborderRange.toScheme.presheaf.map
      (homOfLE (le_chart_preimage_self f V h₁ h₂)).op).hom)
    (idealValue_deltaIdealSection f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) b)) ?_
  exact (deltaAt_restrict_self f V h₁ h₂ b).trans hx.symm

/-- **The generator formula of [Stacks, Tag 08S2].** The canonical morphism sends `d b` to the
image of `p₂^♯ b - p₁^♯ b` under the canonical quotient map from the ideal sheaf of the
diagonal to its conormal sheaf, read on *any* open `V` of the coborder neighbourhood admitting
the tag's two containments.

The comparison with the canonical chart is a restriction, by `le_chart_preimage_self`, and the
two restriction maps of the conormal sheaf involved are the same morphism of opens. -/
theorem toConormal_d_eq_quotientMap
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V) x =
      ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b) :
    ((toConormal f).val.app (.op ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))).hom
        ((Scheme.Hom.universalRelativeDerivation f).d b) =
      (Stacks.Conormal.conormalQuotientMap (pullback.diagonal f)
        (pullback.diagonal f).coborderRange (pullback.diagonal f).liftCoborder
        (pullback.diagonal f).liftCoborder_ι).val.app (.op V) x := by
  refine Eq.trans (toConormal_d f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) b) ?_
  refine Eq.trans (cls_eq f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) b) ?_
  refine Eq.trans ?_ (congrArg
    (quotientApp f V) (deltaIdealSection_restrict_self f V h₁ h₂ b x hx))
  exact Stacks.Conormal.Locality.conormalQuotientMap_restrict (pullback.diagonal f)
    (pullback.diagonal f).coborderRange (pullback.diagonal f).liftCoborder
    (pullback.diagonal f).liftCoborder_ι (le_chart_preimage_self f V h₁ h₂)
    (deltaIdealSection f ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V) b)

end Generator

end Stacks.LeibnizDerivation

end
