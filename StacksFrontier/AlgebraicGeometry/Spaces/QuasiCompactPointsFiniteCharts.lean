module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres

/-!
# Condition (4) implies condition (3) of Stacks 03JV

Let `F` be a presheaf on the big fppf site of a scheme `S` and let `x` be a point of `|F|`
which is the class of a field-valued point `p` whose presenting morphism `Spec(k) ⟶ F` is a
quasi-compact monomorphism — condition (4) of Stacks 03JV. This file proves condition (3):
the same monomorphism has the property that its base change `Spec(k) ×_F U ⟶ Spec(k)` along
every étale chart `φ : h_U ⟶ F` with affine source is a finite morphism.

## Main results

* `AlgebraicGeometry.Space.isFinite_pullback_fst_fieldMorphism_of_isQuasiCompact`: for a
  field-valued point whose presenting morphism is quasi-compact in the sense of Stacks 03HE
  and an étale chart with quasi-compact source, the projection
  `Spec(k) ×_F U ⟶ Spec(k)` is a finite morphism of algebraic spaces.
* In the namespace `AlgebraicGeometry.Space`,
  `HasQuasiCompactMonomorphicFieldRepresentative.hasMonomorphicFieldRepresentativeWithFiniteCharts`
  is Stacks 03JV, condition (4) implies condition (3).

## Implementation notes

The source's argument is followed: the fibre product `Spec(k) ×_F U` is étale over `Spec(k)`
because the chart is étale, and it is quasi-compact because `Spec(k) ⟶ F` is, so it is a
finite disjoint union of spectra of finite separable extensions of `k` and in particular
finite over `k`. Only one departure is made, and it shortens the argument considerably: the
decomposition of Stacks 03PC is not used. An étale morphism is locally quasi-finite by Stacks
03II, a morphism out of a quasi-compact scheme into a one-point scheme is quasi-compact, and
`Spec(k)` is Artinian, so Mathlib's `AlgebraicGeometry.IsFinite.of_locallyQuasiFinite`
applies directly; that composite is
`AlgebraicGeometry.isFinite_of_etale_of_finite`, which the repository already has.

The monomorphism half of condition (4) is *not* used. Accordingly the per-chart result is
stated for an arbitrary quasi-compact field-valued representative, and the monomorphism is
carried through condition (3) untouched, exactly as condition (4) supplies it.

The quasi-compact étale fibre product itself is built once, by
`AlgebraicGeometry.Space.finite_rep_pullback_fieldMorphism_of_isQuasiCompact`, and is shared
with `AlgebraicGeometry.Space.finite_setFibre_of_isQuasiCompact_fieldMorphism`, the chart-fibre
half of condition (1); the two consumers differ only in what they extract from it, finiteness
of the point set there and finiteness of the morphism here.

No algebraicity hypothesis on `F` appears. Representability of the fibre product comes from
étaleness of the chart alone, through
`AlgebraicGeometry.Space.presheaf_etale_of_isEtale`, and quasi-compactness of
`Spec(k) ⟶ F` is tested on the representable — hence automatically algebraic — space `h_U`.
The implication is therefore unconditional, which is why it carries the tag.

Both the `IsFinite` of Stacks 03ZP for morphisms of algebraic spaces and Mathlib's
`AlgebraicGeometry.IsFinite` for morphisms of schemes occur below; the latter is written
`_root_.AlgebraicGeometry.IsFinite`, since inside `AlgebraicGeometry.Space` the bare name is
the former.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_quasiCompactPointsFiniteCharts
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The base change of a quasi-compact field-valued representative to a chart -/

/-- **The chart half of condition (3) of Stacks 03JV.** Let `p` be a field-valued point of a
presheaf `F` on the big fppf site of `S` whose presenting morphism `Spec(k) ⟶ F` is
quasi-compact in the sense of Stacks 03HE, and let `φ : h_U ⟶ F` be étale with `U` of
quasi-compact underlying scheme. Then the projection `Spec(k) ×_F U ⟶ Spec(k)` is a finite
morphism of algebraic spaces in the sense of Stacks 03ZP.

Étaleness of the chart makes the fibre product the Yoneda image of an object of the site which
is étale over `Spec(k)`; quasi-compactness of `Spec(k) ⟶ F`, tested on the quasi-compact
algebraic space `h_U`, makes that object quasi-compact. A quasi-compact scheme étale over a
scheme with at most one point has finitely many points, and an étale morphism with finitely
many points to the spectrum of a field is finite, so the representing morphism of schemes is
finite and the identification of the two pullbacks transports that to the projection. -/
theorem isFinite_pullback_fst_fieldMorphism_of_isQuasiCompact
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS F)
    (hp : IsQuasiCompact B S hS (fieldMorphism B S hS F p))
    {U : BigFppfOver B S hS} (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    {φ : yoneda.obj U ⟶ F} (hφ : IsEtale B S hS φ) :
    IsFinite B S hS (pullback.fst (fieldMorphism B S hS F p) φ) := by
  have hφp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ := presheaf_etale_of_isEtale B S hS hφ
  have sqW := hφp.rep.isPullback (fieldMorphism B S hS F p)
  have hWet : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (hφp.rep.snd (fieldMorphism B S hS F p))) :=
    hφp.property_snd _
  have hfin := finite_rep_pullback_fieldMorphism_of_isQuasiCompact B S hS p hp hU hφp
  have hmap : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      (hφp.rep.snd (fieldMorphism B S hS F p))) :=
    isFinite_of_etale_of_finite p.carrier ((BigFppfOver.toScheme B S hS).map
      (hφp.rep.snd (fieldMorphism B S hS F p)))
  refine isFinite_of_isFinite_map_of_iso B S hS
    (pullback.fst (fieldMorphism B S hS F p) φ)
    (hφp.rep.snd (fieldMorphism B S hS F p))
    ((IsPullback.of_hasPullback (fieldMorphism B S hS F p) φ).isoIsPullback _ _ sqW.flip)
    (Iso.refl _) ?_ hmap
  exact (Category.comp_id (pullback.fst (fieldMorphism B S hS F p) φ)).trans
    ((IsPullback.of_hasPullback (fieldMorphism B S hS F p) φ).isoIsPullback_hom_fst _ _
      sqW.flip).symm

/-! ### Condition (4) implies condition (3) -/

namespace HasQuasiCompactMonomorphicFieldRepresentative

/-- **Stacks 03JV, condition (4) implies condition (3).** If a point `x` of a presheaf `F` on
the big fppf site of `S` is the class of a field-valued point whose presenting morphism
`Spec(k) ⟶ F` is a quasi-compact monomorphism, then that same monomorphism presents `x` and
has finite base change to every affine étale chart of `F`.

The representative, the equality of classes and the monomorphism are carried over unchanged;
the only content is the finiteness of the base change, which is
`AlgebraicGeometry.Space.isFinite_pullback_fst_fieldMorphism_of_isQuasiCompact` applied to the
affine — hence quasi-compact — chart. -/
@[stacks 03JV "part (4) implies part (3)"]
theorem hasMonomorphicFieldRepresentativeWithFiniteCharts
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {x : points B S hS F}
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS F x) :
    HasMonomorphicFieldRepresentativeWithFiniteCharts B S hS F x := by
  obtain ⟨p, hpx, hmono, hqc⟩ := h
  refine ⟨p, hpx, hmono, ?_⟩
  intro U hUaff φ hφ
  have hUcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    have := hUaff
    inferInstance
  exact isFinite_pullback_fst_fieldMorphism_of_isQuasiCompact B S hS p hqc hUcpt hφ

end HasQuasiCompactMonomorphicFieldRepresentative

end AlgebraicGeometry.Space

end
