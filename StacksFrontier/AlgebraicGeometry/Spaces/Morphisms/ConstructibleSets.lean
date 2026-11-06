module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Nagata
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.GeneralDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.Nagata.Universes

/-!
# Constructible sets, Nagata algebraic spaces and the dimension formula

Three permanence sections of the chapter on morphisms of algebraic spaces.

*Constructible sets.* Étale-local constructibility of a subset of the points of an algebraic
space over `S` (`AlgebraicGeometry.Space.IsEtaleLocallyConstructible`, Stacks 0ECU) is stable
under inverse image along an arbitrary morphism, and — this is Chevalley's theorem for
algebraic spaces — under image along a quasi-compact morphism locally of finite presentation.

*Nagata spaces.* An algebraic space over `S` is *Nagata* when the scheme property
`IsNagataScheme` holds étale-locally on it, that is when
`AlgebraicGeometry.Space.HasEtaleLocalProperty` holds for it (Stacks 03E6). Being Nagata
passes from the target of a morphism locally of finite type to its source, which specialises
to the five classes of Nagata algebraic spaces the source lists.

*The dimension formula.* For a morphism `f : X ⟶ Y` of algebraic spaces over `S` which is
locally of finite type and has locally Noetherian target, the dimension of the local ring of
`X` at a point `x` is bounded by the dimension of the local ring of `Y` at the image of `x`
plus the largest transcendence degree of `f` at a codimension-zero point of `X` specializing to
`x`, minus the transcendence degree of `f` at `x`; and the dimension of `X` is bounded by the
dimension of `Y` plus the supremum of those transcendence degrees over all codimension-zero
points of `X`.

## Main definitions

* `AlgebraicGeometry.Space.residueFieldTranscendenceDegreeAt` is the transcendence degree of
  the residue-field extension of a morphism of algebraic spaces at a point, as a number rather
  than as the chartwise predicate of Stacks 04NM.
* `AlgebraicGeometry.Space.genericResidueFieldTranscendenceDegreeAt` is the supremum of those
  degrees over the codimension-zero points specializing to a given point.

## Main results

* `AlgebraicGeometry.Space.isEtaleLocallyConstructible_preimage`: **Stacks 0ECW**.
* `AlgebraicGeometry.Space.isEtaleLocallyConstructible_image`: **Stacks 0ECX**, Chevalley's
  theorem for algebraic spaces.
* `AlgebraicGeometry.Space.isNagata_of_isLocallyOfFiniteType`: **Stacks 0BAU**.
* `AlgebraicGeometry.Space.isNagata_of_isLocallyOfFiniteType_over_nagataScheme` and its four
  specialisations `..._over_field`, `..._over_completeLocalRing`, `..._over_int` and
  `..._over_dedekindDomain`: **Stacks 0BAV**.
* `AlgebraicGeometry.Space.localRingDimension_add_residueFieldTranscendenceDegree_le`,
  `AlgebraicGeometry.Space.finite_zeroDimensionalSpecializations` and
  `AlgebraicGeometry.Space.exists_genericResidueFieldTranscendenceDegreeAt_eq`: **Stacks 0BAX**.
* `AlgebraicGeometry.Space.dimension_le_add_iSup_residueFieldTranscendenceDegree`:
  **Stacks 0BAY**.

## Implementation notes

Both constructibility statements are reduced to the corresponding statement for schemes by
clause (1) of Stacks 03BX, `AlgebraicGeometry.Space.schemePointsHomeomorph`: the points of a
represented presheaf are homeomorphic to the points of the representing scheme, so a
condition on an étale chart is a condition on a subset of a scheme. For the inverse image the
chart of the target is lifted to one of the source by Stacks 02X1 and the statement is
Stacks 054I; the conclusion is then read off that single surjective chart by Stacks 0ECT. For
the image the test chart is taken affine, again by Stacks 0ECT, the base change of `f` along
it is covered by an affine scheme because `f` is quasi-compact (Stacks 03H6), and the induced
morphism of affine schemes is of finite presentation, so Chevalley's theorem for schemes
applies. That the image of the chart of the base change is the whole of the preimage of the
image is Stacks 03H4.

Being Nagata is a *smooth*-local property of schemes (Stacks 036E,
`AlgebraicGeometry.isNagataScheme_isLocal_smooth`); the étale locality which
`AlgebraicGeometry.Space.HasEtaleLocalProperty` asks for follows because an étale morphism is
smooth. Stacks 0BAU is then the same chart-lifting argument as Stacks 04ZK, with the Nagata
property of the source of a locally finite type morphism of schemes (Stacks 035A,
`AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType`) in place of Noetherianity.

The base of the four special cases of Stacks 0BAV is an object of the big fppf site whose
underlying scheme is isomorphic to the spectrum of the relevant ring; "over `ℤ`" is read, as
in `StacksFrontier/AlgebraicGeometry/Morphisms/FiniteType/UniversallyCatenaryExamples.lean`, as
"over the terminal scheme of the ambient universe", which is `Spec (ULift ℤ)`. The four ring
classes are Nagata rings by `IsNagataRing.of_field`,
`IsNagataRing.of_isPrecomplete_maximalIdeal`, `Int.isNagataRing` together with
`IsNagataRing.of_finiteType`, and `IsNagataRing.of_isDedekindDomain_of_charZero`. Only the
passage from a Nagata ring to a Nagata scheme is needed on top of those, and the private
`isNagataScheme_of_iso_spec` below supplies it; `AlgebraicGeometry.isNagataScheme_spec_of_field`
in `StacksFrontier/AlgebraicGeometry/NagataNormalization/FiniteType.lean` is its special case for
a field, and is where a general form would belong.

The transcendence degree at a point of a morphism of algebraic spaces is defined in Stacks 04NM
as a predicate tested on étale charts, `AlgebraicGeometry.Space.HasTranscendenceDegreeAt`; since
the dimension formula does arithmetic with it, it is converted here into a number by taking the
supremum of the values the predicate holds at, exactly as Stacks 04NA turns the chartwise local
dimension into `AlgebraicGeometry.Space.localRingDimension`. The predicate holds at exactly one
value for a morphism of algebraic spaces, which is
`AlgebraicGeometry.Space.residueFieldTranscendenceDegreeAt_eq_iff`: it holds at the numerical
residue-field degree of the chart morphism by Stacks 04NK, hence on every chart by Stacks 04NC,
and no two values can both satisfy it because the germ-level degree is unique.

Both inequalities are read on a single pointed étale chart of Stacks 04NC: there the two local
dimensions are the Krull dimensions of the two chart stalks by Stacks 0BAM, the transcendence
degrees are those of the chart morphism of schemes by Stacks 04NK, and the inequality is the
dimension formula for schemes, Stacks 0BAE. The one point needing care is that the generic
points of the chart through the chart point do not exhaust the codimension-zero points of `X`
specializing to `x`, only enough of them: each of them maps to such a point by Stacks 0BAQ and
Stacks 0A4H, which bounds the chart's maximum by the one in the statement, and that is the
direction the inequality needs.

Stacks 0BAX asserts that its maximum really is a maximum. That is the content of
`AlgebraicGeometry.Space.finite_zeroDimensionalSpecializations` and
`AlgebraicGeometry.Space.exists_genericResidueFieldTranscendenceDegreeAt_eq`: the source of a
locally finite type morphism with locally Noetherian target is locally Noetherian by
Stacks 04ZK, hence has locally finite irreducible components by Stacks 0GMB, hence every
quasi-compact algebraic space étale over it has finitely many codimension-zero points by
Stacks 0BB1; an affine étale chart through `x` is such a space, and its image on points is open
by Stacks 03BX, so it already contains every point specializing to `x`. The affine étale chart
is `AlgebraicGeometry.Space.exists_affine_etale_chart_of_point`, which carries no decency
hypothesis despite the module it is stated in.

## References

* [Stacks Project, Tag 0ECW](https://stacks.math.columbia.edu/tag/0ECW)
* [Stacks Project, Tag 0ECX](https://stacks.math.columbia.edu/tag/0ECX)
* [Stacks Project, Tag 0BAU](https://stacks.math.columbia.edu/tag/0BAU)
* [Stacks Project, Tag 0BAV](https://stacks.math.columbia.edu/tag/0BAV)
* [Stacks Project, Tag 0BAX](https://stacks.math.columbia.edu/tag/0BAX)
* [Stacks Project, Tag 0BAY](https://stacks.math.columbia.edu/tag/0BAY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_constructibleSets
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Constructible sets -/

/-- **Stacks 0ECW.** The inverse image of an étale-locally constructible subset of the points
of an algebraic space over `S` under a morphism of algebraic spaces is étale locally
constructible.

A surjective étale chart `q : h_V ⟶ Y` of the target lifts by Stacks 02X1 to a surjective
étale chart `p : h_U ⟶ X` of the source together with a morphism `α : U ⟶ V` of the site over
`f`. Read through the homeomorphisms of Stacks 03BX, the inverse image of `E` on `U` is the
inverse image along the scheme morphism underlying `α` of the inverse image of `E` on `V`, so
it is locally constructible by Stacks 054I; one surjective chart suffices by Stacks 0ECT. -/
@[stacks 0ECW]
theorem isEtaleLocallyConstructible_preimage
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (E : Set (points B S hS Y)) (hE : IsEtaleLocallyConstructible B S hS Y E) :
    IsEtaleLocallyConstructible B S hS X (pointsMap B S hS X f ⁻¹' E) := by
  obtain ⟨V, q, hq_surjective, hq_etale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hp_surjective, hp_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hq_surjective hq_etale
  refine (forall_etale_iff_exists_surjective_etale B S hS X _ hX).2
    ⟨U, p, (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hp_surjective,
      isEtale_of_presheaf_etale B S hS hp_etale, ?_⟩
  have hsets : (schemePointsHomeomorph B S hS U).symm ⁻¹'
      (pointsMap B S hS (yoneda.obj U) p ⁻¹' (pointsMap B S hS X f ⁻¹' E)) =
        (BigFppfOver.toScheme B S hS).map α ⁻¹'
          ((schemePointsHomeomorph B S hS V).symm ⁻¹'
            (pointsMap B S hS (yoneda.obj V) q ⁻¹' E)) := by
    ext x
    show pointsMap B S hS X f (pointsMap B S hS (yoneda.obj U) p
      ((schemePointsHomeomorph B S hS U).symm x)) ∈ E ↔ _
    rw [← pointsMap_comp_apply, hcomm, pointsMap_comp_apply,
      schemePointsHomeomorph_symm_naturality]
    rfl
  refine ((schemePointsHomeomorph B S hS U).symm.isLocallyConstructible_preimage_iff _).mp ?_
  rw [hsets]
  exact isLocallyConstructible_preimage _
    (((schemePointsHomeomorph B S hS V).symm.isLocallyConstructible_preimage_iff _).mpr
      (hE V q (isEtale_of_presheaf_etale B S hS hq_etale)))

/-- **Stacks 0ECX, Chevalley's theorem for algebraic spaces.** The image of an étale-locally
constructible subset of the points of an algebraic space over `S` under a quasi-compact
morphism locally of finite presentation is étale locally constructible.

By Stacks 0ECT it is enough to test the image on an affine étale chart `g : h_V ⟶ Y`. The
base change `h_V ×_Y X` is a quasi-compact algebraic space because `g` has quasi-compact
source and `f` is quasi-compact, so it has an affine surjective étale chart `t : h_T ⟶
h_V ×_Y X` by Stacks 03H6. The chart `T` sits over `V` by a morphism `q` of the site and over
`X` by an étale chart, so the inverse image of `E` on `T` is constructible, and `q` is a
morphism of affine schemes which is locally of finite presentation because `f` is; Chevalley's
theorem for schemes therefore makes its image constructible. That image is the inverse image
of the image of `E` under `g`, which is where Stacks 03H4 and surjectivity of `t` on points
are used. -/
@[stacks 0ECX, ega "IV 1.8.4", ega "IV 1.8.4.1", ega "IV 9.5.1", sga "1 IV 6.2"]
theorem isEtaleLocallyConstructible_image
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (E : Set (points B S hS X)) (hE : IsEtaleLocallyConstructible B S hS X E) :
    IsEtaleLocallyConstructible B S hS Y (pointsMap B S hS X f '' E) := by
  refine (forall_etale_iff_forall_affine_etale B S hS Y _).2 fun V hV g hg ↦ ?_
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
  -- The base change of `f` along the affine chart `g`, as an algebraic space over `S`.
  let Vsp : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ysp : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let gsp : Vsp ⟶ Ysp := ObjectProperty.homMk g
  let fsp : Xsp ⟶ Ysp := ObjectProperty.homMk f
  let W := AlgebraicSpaces.fiberProduct B S hS gsp fsp
  let p₁ : W ⟶ Vsp := ObjectProperty.homMk (pullback.fst g f)
  let p₂ : W ⟶ Xsp := ObjectProperty.homMk (pullback.snd g f)
  have sq : IsPullback p₁ p₂ gsp fsp := AlgebraicSpaces.isPullback_fiberProduct B S hS gsp fsp
  have hWqc : IsQuasiCompactSpace B S hS W.1 :=
    hf (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) g
  obtain ⟨T, t, hT, htSurj, htEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS W.1 W.property).mp hWqc
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  -- `T` sits over `V` by a morphism of the site and over `X` by an étale chart.
  let q : T ⟶ V := yonedaEquiv (t ≫ p₁.hom)
  have hqmap : yoneda.map q = t ≫ p₁.hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map]
  have hp₂Etale : IsEtale B S hS p₂.hom := isEtale_of_isPullback B S hS p₁ p₂ gsp fsp sq hg
  have hTXEtale : IsEtale B S hS (t ≫ p₂.hom) := isEtale_comp B S hS htEtale hp₂Etale
  have hsqhom : p₁.hom ≫ g = p₂.hom ≫ f := by
    show (p₁ ≫ gsp).hom = (p₂ ≫ fsp).hom
    rw [sq.w]
  have hcomm : yoneda.map q ≫ g = (t ≫ p₂.hom) ≫ f := by
    rw [hqmap, Category.assoc, Category.assoc, hsqhom]
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) :=
    hfp T V (t ≫ p₂.hom) g q
      ((isEtale_iff_presheaf_of_yoneda B S hS (t ≫ p₂.hom)).1 hTXEtale)
      ((isEtale_iff_presheaf_of_yoneda B S hS g).1 hg) hcomm
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map q) := by
    have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map q) :=
      inferInstance
    infer_instance
  -- Chevalley for schemes, applied to the inverse image of `E` on `T`.
  have hET : IsConstructible ((schemePointsHomeomorph B S hS T).symm ⁻¹'
      (pointsMap B S hS (yoneda.obj T) (t ≫ p₂.hom) ⁻¹' E)) :=
    ((schemePointsHomeomorph B S hS T).symm.isConstructible_preimage_iff _).mpr
      ((forall_etale_iff_forall_affine_etale B S hS X E).mp hE T hT (t ≫ p₂.hom) hTXEtale)
  have himage := ((BigFppfOver.toScheme B S hS).map q).isConstructible_image hET
  -- The image on `V` is the inverse image under `g` of the image of `E` under `f`.
  have hsets : (BigFppfOver.toScheme B S hS).map q ''
      ((schemePointsHomeomorph B S hS T).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj T) (t ≫ p₂.hom) ⁻¹' E)) =
      (schemePointsHomeomorph B S hS V).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj V) g ⁻¹' (pointsMap B S hS X f '' E)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨pointsMap B S hS (yoneda.obj T) (t ≫ p₂.hom)
        ((schemePointsHomeomorph B S hS T).symm x), hx, ?_⟩
      rw [← pointsMap_comp_apply, ← hcomm, pointsMap_comp_apply,
        schemePointsHomeomorph_symm_naturality]
    · rintro ⟨z, hz, hzy⟩
      obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback B S hS sq
        ((schemePointsHomeomorph B S hS V).symm y) z hzy.symm
      obtain ⟨x, hx⟩ :=
        (surjective_iff_surjective_pointsMap B S hS W.1 W.property T t).mp htSurj w
      refine ⟨(schemePointsHomeomorph B S hS T) x, ?_, ?_⟩
      · show pointsMap B S hS (yoneda.obj T) (t ≫ p₂.hom)
          ((schemePointsHomeomorph B S hS T).symm
            ((schemePointsHomeomorph B S hS T) x)) ∈ E
        rwa [Homeomorph.symm_apply_apply, pointsMap_comp_apply, hx, hw₂]
      · apply (schemePointsHomeomorph B S hS V).symm.injective
        rw [← schemePointsHomeomorph_symm_naturality, Homeomorph.symm_apply_apply, hqmap,
          pointsMap_comp_apply, hx, hw₁]
  rw [hsets] at himage
  exact ((schemePointsHomeomorph B S hS V).symm.isConstructible_preimage_iff _).mp himage

/-! ### Nagata spaces -/

/-- **Stacks 0BAU.** A morphism of algebraic spaces over `S` which is locally of finite type
and whose target is Nagata has Nagata source.

A surjective étale chart `q : h_V ⟶ Y` witnessing that the target is Nagata lifts, by
Stacks 02X1, to a surjective étale chart `p : h_U ⟶ X` of the source and a morphism
`α : U ⟶ V` of the site making the square commute. Local finite type of the morphism tests
exactly such squares, so the scheme morphism underlying `α` is locally of finite type with
Nagata target, whence `U` is Nagata by Stacks 035A and `p` is the required chart. -/
@[stacks 0BAU]
theorem isNagata_of_isLocallyOfFiniteType
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsNagataScheme T)) :
    HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsNagataScheme T) := by
  obtain ⟨V, q, hq_surjective, hq_etale, hV⟩ := hN
  obtain ⟨U, p, α, hcomm, hp_surjective, hp_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hq_surjective hq_etale
  have := hf U V p q α hp_etale hq_etale hcomm.symm
  exact ⟨U, p, hp_surjective, hp_etale,
    isNagataScheme_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) hV⟩

/-- A scheme isomorphic to the spectrum of a Nagata ring is a Nagata scheme: an isomorphism is
locally of finite type, so Stacks 035A applies.

`AlgebraicGeometry.isNagataScheme_spec_of_field` is the case of a field. -/
private theorem isNagataScheme_of_iso_spec {R : Type u} [CommRing R] {Z : Scheme.{u}}
    (e : Z ≅ Spec (.of R)) (hR : IsNagataRing R) : IsNagataScheme Z :=
  isNagataScheme_of_locallyOfFiniteType e.hom (fun _ =>
    ⟨⟨⊤, isAffineOpen_top _⟩, Set.mem_univ _,
      CommRing.isNagataRing_propertyIsLocal.of_ringEquiv
        (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv hR⟩)

variable (X) in
/-- **Stacks 0BAV, part (1).** An algebraic space over `S` locally of finite type over a
Nagata scheme is Nagata. -/
@[stacks 0BAV "part (1): over a Nagata scheme"]
theorem isNagata_of_isLocallyOfFiniteType_over_nagataScheme (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (hT : IsNagataScheme ((BigFppfOver.toScheme B S hS).obj T))
    (f : X ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS f) :
    HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsNagataScheme Z) :=
  isNagata_of_isLocallyOfFiniteType B S hS hX (isAlgebraicSpace_yoneda B S hS T) f hf
    ((exists_atlas_iff_of_representable B S hS (yoneda.obj T)
      (fun Z : Scheme.{u} => IsNagataScheme Z) T (Iso.refl _)).2 hT)

variable (X) in
/-- **Stacks 0BAV, part (2).** An algebraic space over `S` locally of finite type over a field
is Nagata. -/
@[stacks 0BAV "part (2): over a field"]
theorem isNagata_of_isLocallyOfFiniteType_over_field (hX : IsAlgebraicSpace B S hS X)
    (k : Type u) [Field k] (T : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k))
    (f : X ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS f) :
    HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsNagataScheme Z) :=
  isNagata_of_isLocallyOfFiniteType_over_nagataScheme B S hS X hX T
    (isNagataScheme_of_iso_spec e IsNagataRing.of_field) f hf

variable (X) in
/-- **Stacks 0BAV, part (3).** An algebraic space over `S` locally of finite type over a
Noetherian complete local ring is Nagata. Completeness is
`IsPrecomplete (IsLocalRing.maximalIdeal R) R`, as in Stacks 032W. -/
@[stacks 0BAV "part (3): over a Noetherian complete local ring"]
theorem isNagata_of_isLocallyOfFiniteType_over_completeLocalRing (hX : IsAlgebraicSpace B S hS X)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (IsLocalRing.maximalIdeal R) R] (T : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of R))
    (f : X ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS f) :
    HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsNagataScheme Z) :=
  isNagata_of_isLocallyOfFiniteType_over_nagataScheme B S hS X hX T
    (isNagataScheme_of_iso_spec e IsNagataRing.of_isPrecomplete_maximalIdeal) f hf

variable (X) in
/-- **Stacks 0BAV, part (4).** An algebraic space over `S` locally of finite type over the
integers is Nagata. "Over the integers" is read as "over the terminal scheme of the ambient
universe", which is the spectrum of `ULift ℤ`. -/
@[stacks 0BAV "part (4): over the integers"]
theorem isNagata_of_isLocallyOfFiniteType_over_int (hX : IsAlgebraicSpace B S hS X)
    (T : BigFppfOver B S hS) (hT : IsTerminal ((BigFppfOver.toScheme B S hS).obj T))
    (f : X ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS f) :
    HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsNagataScheme Z) :=
  have : Algebra.FiniteType ℤ (ULift.{u} ℤ) := Module.Finite.finiteType _
  isNagata_of_isLocallyOfFiniteType_over_nagataScheme B S hS X hX T
    (isNagataScheme_of_iso_spec (hT.uniqueUpToIso specULiftZIsTerminal)
      (IsNagataRing.of_finiteType (A := ℤ) Int.isNagataRing)) f hf

variable (X) in
/-- **Stacks 0BAV, part (5).** An algebraic space over `S` locally of finite type over a
Dedekind domain of characteristic zero is Nagata. -/
@[stacks 0BAV "part (5): over a Dedekind domain of characteristic zero"]
theorem isNagata_of_isLocallyOfFiniteType_over_dedekindDomain (hX : IsAlgebraicSpace B S hS X)
    (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero R] (T : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of R))
    (f : X ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS f) :
    HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsNagataScheme Z) :=
  isNagata_of_isLocallyOfFiniteType_over_nagataScheme B S hS X hX T
    (isNagataScheme_of_iso_spec e IsNagataRing.of_isDedekindDomain_of_charZero) f hf

/-! ### The dimension formula -/

/-- The germ property of Stacks 04NK at the germ of a morphism of schemes, phrased with the
numerical residue-field transcendence degree used by the dimension formula for schemes. -/
private theorem hasResidueFieldTranscendenceDegree_ofSchemeHom_iff_eq {U V : Scheme.{u}}
    (r : ℕ∞) (g : U ⟶ V) (u : U) :
    MorphismOfGerms.HasResidueFieldTranscendenceDegree r (MorphismOfGerms.ofSchemeHom g u) ↔
      residueFieldTranscendenceDegree g u = r :=
  MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff g u r

/-- The transcendence degree of the residue-field extension of a morphism of algebraic spaces
over `S` at a point of its source, as an element of `ℕ∞`.

This reads the chartwise predicate `AlgebraicGeometry.Space.HasTranscendenceDegreeAt` of
Stacks 04NM as a number; for a morphism of algebraic spaces exactly one value satisfies that
predicate, which is `AlgebraicGeometry.Space.residueFieldTranscendenceDegreeAt_eq_iff`. -/
noncomputable def residueFieldTranscendenceDegreeAt (f : X ⟶ Y) (x : points B S hS X) : ℕ∞ :=
  sSup {r : ℕ∞ | HasTranscendenceDegreeAt B S hS f x r}

/-- The numerical residue-field transcendence degree at a point of a morphism of algebraic
spaces over `S` is the unique value at which the chartwise predicate of Stacks 04NM holds: it
holds at the residue-field degree of the morphism of charts by Stacks 04NK, hence on every
chart by Stacks 04NC, and two values at which it holds agree because the germ-level degree is
unique. -/
theorem residueFieldTranscendenceDegreeAt_eq_iff (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (x : points B S hS X) (r : ℕ∞) :
    residueFieldTranscendenceDegreeAt B S hS f x = r ↔
      HasTranscendenceDegreeAt B S hS f x r := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hX hY f x
  set r₀ := residueFieldTranscendenceDegree ((BigFppfOver.toScheme B S hS).map c.h)
    (c.sourcePoint B S hS) with hr₀
  have hchart : MorphismOfGerms.HasResidueFieldTranscendenceDegree r₀
      (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map c.h)
        (c.sourcePoint B S hS)) :=
    (hasResidueFieldTranscendenceDegree_ofSchemeHom_iff_eq r₀ _ _).2 hr₀.symm
  have hevery : HasTranscendenceDegreeAt B S hS f x r₀ :=
    (holdsOnEveryEtaleChartAtPoint_iff_some B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r₀)
      (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r₀)
      hX hY f x).mpr ⟨c, hchart⟩
  have hunique (t : ℕ∞) (ht : HasTranscendenceDegreeAt B S hS f x t) : t = r₀ :=
    MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique (ht c) hchart
  rw [residueFieldTranscendenceDegreeAt,
    show {t : ℕ∞ | HasTranscendenceDegreeAt B S hS f x t} = {r₀} from
      Set.ext fun t => ⟨hunique t, fun ht => ht ▸ hevery⟩,
    sSup_singleton]
  exact ⟨fun h => h ▸ hevery, fun h => (hunique r h).symm⟩

/-- The supremum of the residue-field transcendence degrees of a morphism of algebraic spaces
over `S` at the codimension-zero points of its source specializing to a given point.

This is the quantity written `E` in Stacks 0BAX; it really is a maximum, by
`AlgebraicGeometry.Space.finite_zeroDimensionalSpecializations` and
`AlgebraicGeometry.Space.exists_genericResidueFieldTranscendenceDegreeAt_eq`. -/
noncomputable def genericResidueFieldTranscendenceDegreeAt (f : X ⟶ Y)
    (x : points B S hS X) : ℕ∞ :=
  ⨆ ξ : {ξ : points B S hS X // x ∈ closure {ξ} ∧ localRingDimension B S hS ξ = 0},
    residueFieldTranscendenceDegreeAt B S hS f ξ.1

/-- **Stacks 0BAX, finiteness of the family entering the maximum.** Under the hypotheses of the
dimension formula only finitely many codimension-zero points of the source specialize to a
given point.

The source is locally Noetherian by Stacks 04ZK, hence has locally finite irreducible
components by Stacks 0GMB, so every quasi-compact algebraic space étale over it has finitely
many codimension-zero points by Stacks 0BB1. An affine étale chart through the point is such a
space, its image on points is open by Stacks 03BX and therefore contains every point
specializing to the given one, and codimension zero is étale-invariant by Stacks 0A4H. -/
@[stacks 0BAX "finiteness of the family entering the maximum", ega "IV 13.2.6" "more general"]
theorem finite_zeroDimensionalSpecializations (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X) :
    {ξ : points B S hS X | x ∈ closure {ξ} ∧ localRingDimension B S hS ξ = 0}.Finite := by
  obtain ⟨T, g, y, hTaff, hg, hy⟩ := exists_affine_etale_chart_of_point B S hS X hX x
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hgE : IsEtale B S hS g := (isEtale_iff_presheaf_of_yoneda B S hS g).mpr hg
  have hqc : IsQuasiCompactSpace B S hS (yoneda.obj T) := by
    let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
    exact isQuasiCompactSpace_yoneda_obj B S hS
      (Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj T))
  have hzero :=
    (hasLocallyFiniteIrreducibleComponents_iff_finite_codimensionZeroPoints B S hS).mp
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS X hX
        (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hX hY f hf hNoeth))
      (yoneda.obj T) hT hqc g hgE
  have hopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj T) g)) := by
    simpa [Set.image_univ] using
      isOpenMap_pointsMap_of_etale B S hS hX T g hg Set.univ isOpen_univ
  refine (hzero.image (pointsMap B S hS (yoneda.obj T) g)).subset ?_
  rintro ξ ⟨hξ, hξdim⟩
  obtain ⟨η, rfl⟩ := specializes_iff_forall_open.mp (specializes_iff_mem_closure.mpr hξ)
    _ hopen ⟨y, hy⟩
  refine ⟨η, ?_, rfl⟩
  simpa [hξdim] using (localRingDimension_pointsMap_of_etale B S hS hT hX g hgE η).symm

/-- The image on points, under an étale chart `a`, of a generic point of the chart is a
codimension-zero point of the space, specializing to the image of any point it specializes to. -/
private theorem pointsMap_symm_mem_closure_and_localRingDimension_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : IsEtale B S hS a) (η : (BigFppfOver.toScheme B S hS).obj U)
    (hηgen : η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U))
    (y : points B S hS (yoneda.obj U)) (hηy : η ⤳ pointsToScheme B S hS U y) :
    pointsMap B S hS (yoneda.obj U) a y ∈
        closure {pointsMap B S hS (yoneda.obj U) a ((schemePointsHomeomorph B S hS U).symm η)} ∧
      localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj U) a ((schemePointsHomeomorph B S hS U).symm η)) = 0 := by
  have hyη : pointsToScheme B S hS U ((schemePointsHomeomorph B S hS U).symm η) = η :=
    (schemePointsHomeomorph B S hS U).apply_symm_apply η
  have hsy : (schemePointsHomeomorph B S hS U).symm (pointsToScheme B S hS U y) = y := by
    rw [← schemePointsHomeomorph_apply, Homeomorph.symm_apply_apply]
  have hspec := hηy.map (schemePointsHomeomorph B S hS U).symm.continuous
  rw [hsy] at hspec
  refine ⟨specializes_iff_mem_closure.mp (hspec.map (continuous_pointsMap B S hS a)), ?_⟩
  refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).2
    ⟨U, a, η, ha, ?_, hηgen⟩
  have hcp := chartPoint_pointsToScheme B S hS U a ((schemePointsHomeomorph B S hS U).symm η)
  rwa [hyη] at hcp

/-- **Stacks 0BAX, attainment of the maximum.** Under the hypotheses of the dimension formula
the supremum defining the correction term is attained, so it is a maximum.

The family is finite by `AlgebraicGeometry.Space.finite_zeroDimensionalSpecializations`, and it
is nonempty because the generic point of an irreducible component of an étale chart through the
chosen point maps to a codimension-zero point specializing to it (Stacks 0BAQ). -/
@[stacks 0BAX "attainment of the maximum"]
theorem exists_genericResidueFieldTranscendenceDegreeAt_eq (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X) :
    ∃ ξ : {ξ : points B S hS X // x ∈ closure {ξ} ∧ localRingDimension B S hS ξ = 0},
      genericResidueFieldTranscendenceDegreeAt B S hS f x =
        residueFieldTranscendenceDegreeAt B S hS f ξ.1 := by
  obtain ⟨U, a, y, -, ha, hy⟩ := exists_affine_etale_chart_of_point B S hS X hX x
  obtain ⟨η, hηgen, hηy⟩ : ∃ η : (BigFppfOver.toScheme B S hS).obj U,
      η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) ∧
        η ⤳ pointsToScheme B S hS U y := by
    refine ⟨genericPoints.ofComponent ⟨irreducibleComponent (pointsToScheme B S hS U y),
      irreducibleComponent_mem_irreducibleComponents _⟩, (genericPoints.ofComponent _).2, ?_⟩
    exact (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent
  obtain ⟨hξx, hξdim⟩ := pointsMap_symm_mem_closure_and_localRingDimension_eq_zero B S hS hX U a
    ((isEtale_iff_presheaf_of_yoneda B S hS a).mpr ha) η hηgen y hηy
  rw [hy] at hξx
  have _ : Finite {ξ : points B S hS X //
      x ∈ closure {ξ} ∧ localRingDimension B S hS ξ = 0} :=
    (finite_zeroDimensionalSpecializations B S hS f hX hY hNoeth hf x).to_subtype
  have _ : Nonempty {ξ : points B S hS X //
      x ∈ closure {ξ} ∧ localRingDimension B S hS ξ = 0} :=
    ⟨⟨_, hξx, hξdim⟩⟩
  obtain ⟨z, hz⟩ := Finite.ciSup_mem (fun z : {ξ : points B S hS X //
      x ∈ closure {ξ} ∧ localRingDimension B S hS ξ = 0} =>
    residueFieldTranscendenceDegreeAt B S hS f z.1)
  exact ⟨z, hz.symm⟩

/-- The numerical residue-field transcendence degree of a morphism of algebraic spaces at the
image of a point of an étale chart is the numerical residue-field transcendence degree of the
induced morphism of charts at that point. -/
private theorem residueFieldTranscendenceDegreeAt_chart (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f) (z : points B S hS (yoneda.obj U)) :
    residueFieldTranscendenceDegreeAt B S hS f (pointsMap B S hS (yoneda.obj U) a z) =
      residueFieldTranscendenceDegree ((BigFppfOver.toScheme B S hS).map h)
        (pointsToScheme B S hS U z) := by
  obtain ⟨q, hq⟩ := Quot.exists_rep z
  subst hq
  let c : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a (q.class B S hS (yoneda.obj U))) :=
    { U := U
      V := V
      a := a
      b := b
      h := h
      a_etale := ha
      b_etale := hb
      comm := hcomm
      representative := q
      point := IsLocalRing.closedPoint q.carrier
      maps_to := rfl }
  exact ((hasResidueFieldTranscendenceDegree_ofSchemeHom_iff_eq _ _ _).1
    ((residueFieldTranscendenceDegreeAt_eq_iff B S hS f hX hY _ _).1 rfl c)).symm

/-- **Stacks 0BAX, the dimension inequality.** For a morphism of algebraic spaces over `S`
locally of finite type with locally Noetherian target, the dimension of the local ring at a
point plus the residue-field transcendence degree there is at most the dimension of the local
ring at the image point plus the largest residue-field transcendence degree at a
codimension-zero point specializing to the given one.

Everything is read on one pointed étale chart of Stacks 04NC: the two local dimensions are the
Krull dimensions of the two chart stalks by Stacks 0BAM, the two residue-field degrees are
those of the morphism of charts by Stacks 04NK, and the inequality between them is the
dimension formula for schemes, Stacks 0BAE. The chart's own maximum is bounded by the one in
the statement because each generic point of the chart through the chart point maps to a
codimension-zero point of the source specializing to the given one, by Stacks 0BAQ and
Stacks 0A4H. -/
@[stacks 0BAX "dimension inequality", ega "IV 5.6.5" "more general"]
theorem localRingDimension_add_residueFieldTranscendenceDegree_le (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X) :
    (localRingDimension B S hS x : WithBot ℕ∞) +
        (residueFieldTranscendenceDegreeAt B S hS f x : WithBot ℕ∞) ≤
      (localRingDimension B S hS (pointsMap B S hS X f x) : WithBot ℕ∞) +
        (genericResidueFieldTranscendenceDegreeAt B S hS f x : WithBot ℕ∞) := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hX hY f x
  have hpt : (IsLocalRing.closedPoint c.representative.carrier :
      Spec (CommRingCat.of c.representative.carrier)) = c.point := Subsingleton.elim _ _
  have hsource : pointsToScheme B S hS c.U (c.representative.class B S hS (yoneda.obj c.U)) =
      c.sourcePoint B S hS :=
    congrArg ((BigFppfOver.toScheme B S hS).map c.representative.value) hpt
  -- the two local dimensions, read on the chart
  have hdimX : (localRingDimension B S hS x : WithBot ℕ∞) =
      ringKrullDim (((BigFppfOver.toScheme B S hS).obj c.U).presheaf.stalk
        (c.sourcePoint B S hS)) := by
    refine localRingDimension_eq_of_chartPoint B S hS hX c.U c.a c.a_etale _ x ?_
    have hcp := chartPoint_pointsToScheme B S hS c.U c.a
      (c.representative.class B S hS (yoneda.obj c.U))
    rwa [hsource, c.maps_to] at hcp
  have hdimY : (localRingDimension B S hS (pointsMap B S hS X f x) : WithBot ℕ∞) =
      ringKrullDim (((BigFppfOver.toScheme B S hS).obj c.V).presheaf.stalk
        ((BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS))) := by
    refine localRingDimension_eq_of_chartPoint B S hS hY c.V c.b c.b_etale _ _ ?_
    have hcp := chartPoint_pointsToScheme B S hS c.V c.b
      (pointsMap B S hS (yoneda.obj c.U) (yoneda.map c.h)
        (c.representative.class B S hS (yoneda.obj c.U)))
    rwa [pointsToScheme_pointsMap, hsource, ← pointsMap_comp_apply, c.comm,
      pointsMap_comp_apply, c.maps_to] at hcp
  -- the hypotheses of the dimension formula on the chart
  have hNoethV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj c.V) :=
    (exists_atlas_iff_forall_etale B S hS Y
      (fun W : Scheme.{u} => IsLocallyNoetherian W) hY).mp hNoeth c.V c.b c.b_etale
  have hLft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) :=
    hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  -- the two residue-field degrees, read on the chart
  have hdegx := residueFieldTranscendenceDegreeAt_chart B S hS f hX hY c.U c.V c.a c.b c.h
    c.a_etale c.b_etale c.comm (c.representative.class B S hS (yoneda.obj c.U))
  rw [c.maps_to, hsource] at hdegx
  have hgeneric : _root_.AlgebraicGeometry.genericResidueFieldTranscendenceDegreeAt
      ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) ≤
      genericResidueFieldTranscendenceDegreeAt B S hS f x := by
    unfold _root_.AlgebraicGeometry.genericResidueFieldTranscendenceDegreeAt
      genericResidueFieldTranscendenceDegreeAt
    refine iSup_le ?_
    rintro ⟨⟨ηpt, hηgen⟩, hηspec⟩
    have hyη : pointsToScheme B S hS c.U
        ((schemePointsHomeomorph B S hS c.U).symm ηpt) = ηpt :=
      (schemePointsHomeomorph B S hS c.U).apply_symm_apply ηpt
    obtain ⟨hξx, hξdim⟩ := pointsMap_symm_mem_closure_and_localRingDimension_eq_zero B S hS hX
      c.U c.a ((isEtale_iff_presheaf_of_yoneda B S hS c.a).mpr c.a_etale) ηpt hηgen _
      (hsource ▸ specializes_iff_mem_closure.mpr hηspec)
    rw [c.maps_to] at hξx
    have hdeg := residueFieldTranscendenceDegreeAt_chart B S hS f hX hY c.U c.V c.a c.b c.h
      c.a_etale c.b_etale c.comm ((schemePointsHomeomorph B S hS c.U).symm ηpt)
    rw [hyη] at hdeg
    rw [← hdeg]
    exact le_iSup_of_le ⟨_, hξx, hξdim⟩ le_rfl
  calc (localRingDimension B S hS x : WithBot ℕ∞) +
        (residueFieldTranscendenceDegreeAt B S hS f x : WithBot ℕ∞)
      = ringKrullDim (((BigFppfOver.toScheme B S hS).obj c.U).presheaf.stalk
            (c.sourcePoint B S hS)) +
          (residueFieldTranscendenceDegree ((BigFppfOver.toScheme B S hS).map c.h)
            (c.sourcePoint B S hS) : WithBot ℕ∞) := by rw [hdimX, hdegx]
    _ ≤ ringKrullDim (((BigFppfOver.toScheme B S hS).obj c.V).presheaf.stalk
            ((BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS))) +
          (_root_.AlgebraicGeometry.genericResidueFieldTranscendenceDegreeAt
            ((BigFppfOver.toScheme B S hS).map c.h)
            (c.sourcePoint B S hS) : WithBot ℕ∞) :=
      ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le _ _
    _ ≤ _ := add_le_add hdimY.symm.le (WithBot.coe_le_coe.mpr hgeneric)

/-- **Stacks 0BAY.** For a morphism of algebraic spaces over `S` locally of finite type with
locally Noetherian target, the dimension of the source is at most the dimension of the target
plus the supremum of the residue-field transcendence degrees at the codimension-zero points of
the source.

Both dimensions are suprema of local-ring dimensions by Stacks 0BAN, and at each point the
pointwise inequality is Stacks 0BAX, whose correction term is attained at a codimension-zero
point and so is bounded by the supremum over all of them. -/
@[stacks 0BAY]
theorem dimension_le_add_iSup_residueFieldTranscendenceDegree (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hf : IsLocallyOfFiniteType B S hS f) :
    dimension B S hS X hX ≤ dimension B S hS Y hY +
      ((⨆ ξ : {ξ : points B S hS X // localRingDimension B S hS ξ = 0},
        residueFieldTranscendenceDegreeAt B S hS f ξ.1 : ℕ∞) : WithBot ℕ∞) := by
  have hgeneric (z : points B S hS X) :
      (genericResidueFieldTranscendenceDegreeAt B S hS f z : WithBot ℕ∞) ≤
        ((⨆ ξ : {ξ : points B S hS X // localRingDimension B S hS ξ = 0},
          residueFieldTranscendenceDegreeAt B S hS f ξ.1 : ℕ∞) : WithBot ℕ∞) := by
    obtain ⟨ξ, hξ⟩ :=
      exists_genericResidueFieldTranscendenceDegreeAt_eq B S hS f hX hY hNoeth hf z
    rw [hξ]
    exact WithBot.coe_le_coe.mpr (le_iSup_of_le ⟨ξ.1, ξ.2.2⟩ le_rfl)
  rw [dimension_eq_iSup_localRingDimension B S hS X hX]
  refine iSup_le fun z => ?_
  calc (localRingDimension B S hS z : WithBot ℕ∞)
      ≤ (localRingDimension B S hS z : WithBot ℕ∞) +
          (residueFieldTranscendenceDegreeAt B S hS f z : WithBot ℕ∞) :=
        le_add_of_nonneg_right (by simp)
    _ ≤ (localRingDimension B S hS (pointsMap B S hS X f z) : WithBot ℕ∞) +
          (genericResidueFieldTranscendenceDegreeAt B S hS f z : WithBot ℕ∞) :=
        localRingDimension_add_residueFieldTranscendenceDegree_le B S hS f hX hY hNoeth hf z
    _ ≤ _ := add_le_add (by
        rw [dimension_eq_iSup_localRingDimension B S hS Y hY]
        exact le_iSup_of_le (pointsMap B S hS X f z) le_rfl) (hgeneric z)

end AlgebraicGeometry.Space

end
