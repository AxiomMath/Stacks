module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSliceChartZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedAtChart
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingRegularSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalSourceLemmaUnramified

/-!
# The slice of Stacks 06MD as a zero locus on the open subspace, and its chart read on the space

Three steps of the chart construction of **Stacks 06N3**, all of them independent of the
identification of the fibre of the slice.

The slice **Stacks 06MD** delivers is `V(c₁, …, c_r) ∩ V` for an *open* subspace `V ⊆ U`, i.e.
`AlgebraicGeometry.Stack.zeroLocusOnOpen`, which is a closed subspace of `V` and only a locally
closed subspace of `U`. The first result below records that it is, on the nose, the zero locus of
the *restricted* functions on the algebraic space `V`:

`V(c₁, …, c_r) ∩ V = V(ι^*c₁, …, ι^*c_r)` inside `V`,

so every statement about `AlgebraicGeometry.Space.vanishingSubfunctor` — in particular
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_chartBaseChange`, which identifies the
base change of a zero locus along a chart — is available for it, read at the algebraic space `V`
rather than at `U`.

The second records the point: a point of an affine étale chart of `X` at which no section of the
defining ideal of a closed subspace `Z ⊆ X` is invertible is in the image of the base changed
closed immersion `Z ×_X W ⟶ W`, so the chart of `Z` carries a point over it.

The third carries the unramifiedness of such a chart over `Spec k` from the morphism of *schemes*
that `AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field`
delivers to `AlgebraicGeometry.Space.IsUnramifiedAt` of the structure morphism of the closed
subspace, read on the algebraic space. That is the chart-independent form: having it, the same
condition may be read back on *any* étale chart of the subspace, by
`AlgebraicGeometry.Space.isUnramifiedAt_chartPoint_iff`, which is an equivalence.

## Main results

* `AlgebraicGeometry.Stack.vanishingSubfunctor_globalFunctionsMap_ι_eq_zeroLocusOnOpen`: the
  slice of Stacks 06MD is the zero locus of the restricted functions on the open subspace.
* `AlgebraicGeometry.Space.exists_chartBaseChangeHom_eq_of_forall_germ_mem_maximalIdeal`: the
  chart of a closed subspace carries a point over a point of the ambient chart at which the
  defining ideal is not invertible.
* `AlgebraicGeometry.Space.pointsMap_ι_pointsMap_chartBaseChangeToSubspace`: the point of `|Z|`
  carried by a point of the chart `Z ×_X W` lies over the point of `|X|` carried by its image
  in the chart `W`.
* `AlgebraicGeometry.Space.mem_range_pointsMap_ι_of_mem_range_pointsMap_ι_chartBaseChangeHom`:
  the membership hypothesis of the assembled statement below, discharged when the open subspace
  of the closed subspace is the inverse image of a subspace of the ambient space.
* `AlgebraicGeometry.Space.exists_chartBaseChangeHom_eq_and_mem_range_pointsMap_ι`: the two
  previous results joined — one point of the chart of the closed subspace lying over a
  prescribed point of the ambient chart *and* satisfying that membership.
* `AlgebraicGeometry.Space.isUnramifiedAt_chartBaseChangeToSubspace_of_unramifiedAt`: the
  structure morphism of a closed subspace over `Spec k` is unramified, in the sense of
  **Stacks 03ZH**, part (2), at the point of the subspace carried by a point of the chart
  `Z ×_X W` at which the morphism of schemes is unramified.
* `AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange`:
  the three steps joined — an **open** subspace of the closed subspace carries an affine étale
  chart with a point at which the morphism of schemes to the represented base is unramified,
  given a point of the chart of the closed subspace lying over it at which that morphism of
  schemes is unramified.
* `AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal`:
  the same with **no point-set hypothesis left** — at the configuration in which the open
  subspace of the closed subspace is the inverse image of an open subspace of the ambient space,
  the membership is discharged from the point of the ambient chart the slicing datum already
  names.

## What the finite type point assembly needs

The three results here are the part of that assembly which does *not* depend on identifying the
fibre of the slice. The identification itself is **not** a matter of instantiating
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_chartBaseChange` at the algebraic space
`U` of **Stacks 06MD**, and the obstruction is the open subspace `V` that lemma returns:

* the slice is `V(c₁, …, c_r) ∩ V`, a closed subspace of `V` and only a **locally closed**
  subspace of `U`, so it is not `AlgebraicGeometry.Space.vanishingSubfunctor` of anything on `U`
  and `AlgebraicGeometry.Space.chartBaseChangeToSubspace`, which takes a
  `AlgebraicGeometry.Space.ClosedSubspaces` of the ambient space, does not reach it from `U`;
* the first result below removes that obstruction one level down: the slice *is* the zero locus
  of the restricted functions on the algebraic space `V`, so the identification is available
  with `V` in the role of `U`, and the closed subspace in play is then a closed subspace of an
  algebraic space `P` representing `V ×_𝒳 Spec k` — **not** of the algebraic space `Fsp`
  representing `F = U ×_𝒳 Spec k`;
* what is then missing is the match of the two fibres. The slicing sequence, its germ clause and
  the closed point of **Stacks 056U** are all produced on an *affine étale chart of* `Fsp`
  (`AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`
  and
  `Space.exists_affine_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable`),
  because `V` is only produced afterwards, out of that sequence; whereas the unramifiedness that
  **Stacks 06N2** reads has to be checked on a chart of `P`. Bridging the two is what remains:
  either the identification of `P` with the open subspace `p⁻¹V ⊆ Fsp` — available in principle
  from `AlgebraicGeometry.Stack.exists_iso_representingMap_restrictionInnerSquare_fst`, which
  needs no closedness of the subfunctor and so applies to the open subspace `V` itself — together
  with the restriction of an affine chart to an affine open inside it, or the passage through the
  chart-independent condition on the algebraic space, for which the third result below is the
  first half and a transport of `AlgebraicGeometry.Space.IsUnramifiedAt` along the inclusion of
  an open subspace of the source the second.

The second half of that second route is **not** owed: the transport is
`AlgebraicGeometry.Space.isUnramifiedAt_iff_of_isOpenSubspace` of
`StacksFrontier/AlgebraicGeometry/Stacks/LocalSourceLemmaUnramified.lean`, an *equivalence* between
`AlgebraicGeometry.Space.IsUnramifiedAt` of a morphism at a point of an open subspace of its
source and `AlgebraicGeometry.Space.IsUnramifiedAt` of its restriction to that open subspace, for
an arbitrary morphism of algebraic spaces and an arbitrary open subfunctor. It is already in the
import closure of this file, so no import is owed for it either. The open subspace it is applied
along is not `V`: it is the fibre of the slice sitting inside the **closed** subspace
`V(g^*c₁, …, g^*c_r) ⊆ Fsp`. That zero locus *is* closed in `Fsp`, so the third result below
applies to it at the chart of `Fsp` which the slicing sequence already lives on; the fibre of the
slice is its intersection with `p⁻¹V`, hence an open subspace of it; and the transport carries
the conclusion from the one to the other. Taking the third result at `P` instead needs no
transport but does need the chart of `Fsp` restricted to `p⁻¹V` and the scheme-level
unramifiedness carried to that restriction, which is why this is the cheaper of the two.
The three steps are joined into one statement,
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange`,
which assumes nothing beyond the configuration and one point-set hypothesis, and that hypothesis
is **not** an identity: the maps
`|Z ×_X W| ∋ z ↦ |Z|` and `|G| ∋ w ↦ |Z|` are not two spellings of one point. With `z`
and `w` unrelated the two images are unrelated, and nothing in the configuration `G ⊆ Z ⊆ X`
makes the chart of `Z` factor through the open subspace `G`: the chart is the base change of a
chart of the *ambient* space `X`, which is chosen before `G` is cut out, so its range meets the
complement of `G` in general. What the assembly actually needs is the *membership*
`|Z ×_X W| z ∈ |G|`, which is a condition on `z` — exactly the chase through the closed point of
**Stacks 06FX**, the open `V` of **Stacks 06MD** and the open `V'` of **Stacks 06N2** — and the
point `w` is then produced by that membership rather than matched against it.

That membership is **supplied**, and the chase it is supplied by lands in the first of the
three transfers of the condition — `AlgebraicGeometry.Space.range_pointsMap_ι_preimage`,
the equality of point sets `|f⁻¹O| = |f|⁻¹|O|` for an arbitrary morphism and an arbitrary
subspace — read twice:

* once at the closed immersion `Z ⟶ X`, which is
  `AlgebraicGeometry.Space.mem_range_pointsMap_ι_of_mem_range_pointsMap_ι_chartBaseChangeHom`
  below. At the configuration of **Stacks 06N3** the open subspace `G ⊆ Z` *is* an inverse
  image: with `X` an algebraic space `Fsp` representing `F = U ×_𝒳 Spec k`, `Z` the closed
  subspace `V(g^*c₁, …, g^*c_r) ⊆ Fsp` and `V ⊆ U` the open subspace of **Stacks 06MD** and
  **Stacks 06N2**, the fibre of the slice is `Z ∩ p⁻¹V`, the inverse image along `Z ⟶ Fsp` of
  the open subspace `p⁻¹V ⊆ Fsp`. So the transfer turns the membership into one about the point
  of `|Fsp|` carried by the point of the *ambient* chart, which
  `AlgebraicGeometry.Space.pointsMap_ι_pointsMap_chartBaseChangeToSubspace` identifies;
* once at the projection `p : Fsp ⟶ U`, which turns that in turn into the membership of the
  image in `|U|` of the point of the ambient chart in the point set of `V` — and *that* is the
  first conjunct of
  `Stack.exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`,
  the theorem tagged `@[stacks 06MD]`, whose statement
  already reads it at the level of algebraic spaces,
  at the image of the geometric point of the slicing datum. That second reading is a bare
  instantiation of the transfer and is not wrapped here.

The other two transfers are *not* where the chase lands.
`AlgebraicGeometry.Space.exists_opens_mem_iff_mem_range_pointsMap_ι` would route the condition
through a germ computation on the affine chart, which is not how the open subspace arrives — it
arrives as an inverse image, with no equation for the open of the chart scheme cutting it out.
`AlgebraicGeometry.Space.mem_range_pointsMap_ι_of_range_le` is the cheapest of the three, but its
side condition `CategoryTheory.Subfunctor.range (chartBaseChangeToSubspace …) ≤ G` is **not
available in this configuration and would itself have to be chased**: it says the whole chart of
`Z` factors through `G`, and the chart is the base change of a chart of the ambient space `X`
chosen before `G` is cut out, so its range meets the complement of `G` in general. It becomes
available only after the ambient chart has been shrunk to the inverse image of `p⁻¹V` — which is
exactly the step that identifying the two points would silently skip. Nothing below needs it.

Both instantiations of the first transfer use it as stated, with no massaging; the one at
`Z ⟶ X` takes `Z.2.1`, `X.2` and the algebraic-space witness of the subspace of `X` for its
three algebraic-space arguments. This file imports
`StacksFrontier/AlgebraicGeometry/Spaces/Properness/ProperClosedSubsetBaseChange.lean` for it.
`AlgebraicGeometry.Space.mem_range_pointsMap_ι_of_range_le` lives in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/DenseWitnessedAgreement.lean`, which is not in
this file's closure and is not needed.

So the unramifiedness half of the chart at a finite type point assumes nothing beyond the
configuration:
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal`
takes the point of the ambient affine chart, the germ clause of the slicing sequence at it, the
scheme-level unramifiedness at the points of the chart of `Z` over it, and the membership of its
point of `|Fsp|` in the inverse image of the open subspace — and no point-set hypothesis about
the chart of `Z`. What that does **not** do — the
identification of the fibre of the slice at `U := V` described above, and the remaining steps of
the assembly — is done elsewhere. The fibre identification is
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList` of
`StacksFrontier.AlgebraicGeometry.Spaces.FibreSliceChartZeroScheme`, read at the chart by
`StacksFrontier.AlgebraicGeometry.Stacks.ChartSliceUnramifiedFieldPoint` and carried to the fibre
hypothesis of **Stacks 06N2** by
`StacksFrontier.AlgebraicGeometry.Stacks.SliceFibreSubspaceComparison`; and the
assembly is complete,
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.AbsolutelyDMEtaleChartAssembly` stating **Stacks 06N3**
with no hypothesis at all. The reading of the membership conclusion of **Stacks 06N2** costs neither
the bijectivity of `AlgebraicGeometry.Stack.spacePointMap` nor a comparison of
`AlgebraicGeometry.Stack.fibreProjection` on points with
`AlgebraicGeometry.Stack.fibreSpaceProjection`:
`AlgebraicGeometry.Stack.exists_isOpenSubspace_isEtale_mem_range_pointsMap` of
`StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartStackPointMembership` reads the membership
off the singleton range of the field-valued point instead. No `@[stacks 06N3]` attribute is
claimed by anything in this file.

## Implementation notes

The point of the chart of the subspace is produced through
`AlgebraicGeometry.Space.exists_iso_subscheme_ofIdealTop_definingIdealAt`, which presents the
chart as the closed subscheme cut out by the defining ideal: the point lies on the support of that
ideal sheaf, hence in the range of the closed immersion of the subscheme, and the isomorphism
carries the preimage back. Affineness of the chart is needed only for that presentation.

The square of étale charts feeding `AlgebraicGeometry.Space.isUnramifiedAt_chartPoint_iff` is the
one the representability datum of the closed immersion already carries: its cartesian square gives
the commuting triangle over `Z ⟶ X ⟶ yoneda.obj T`, and the chart on the right is the identity
chart of the represented target, `AlgebraicGeometry.Space.isEtaleChart_id`. So no chart has to be
chosen and no point is transported.

No `@[stacks]` attribute is claimed: these are steps of the proof of **Stacks 06N3**, which is no
tag of its own, and whose registration sits on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack`.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u w

namespace AlgebraicGeometry

/-- **A point at which no section of an ideal of global functions is invertible lies on the zero
scheme of that ideal.** The germs of the sections generate an ideal contained in the maximal
ideal of the local ring, so no section is invertible at the point, which is membership of the
zero locus. This is the ideal form of
`AlgebraicGeometry.mem_support_ofIdealTop_of_germ_mem_maximalIdeal`. -/
theorem mem_support_ofIdealTop_of_forall_germ_mem_maximalIdeal {Xs : Scheme.{u}} (x : Xs)
    (I : Ideal Γ(Xs, ⊤))
    (h : ∀ s ∈ I, Xs.presheaf.germ ⊤ x trivial s ∈ maximalIdeal (Xs.presheaf.stalk x)) :
    x ∈ (Scheme.IdealSheafData.ofIdealTop I).support := by
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_ofIdealTop,
    Scheme.mem_zeroLocus_iff]
  intro s hs hx
  exact (IsLocalRing.mem_maximalIdeal _).mp (h s hs) ((Xs.mem_basicOpen_top s x).mp hx)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A point of the chart of a closed subspace over a point of the ambient chart -/

/-- **The chart of a closed subspace carries a point over a point of the ambient chart at which
the defining ideal is not invertible.** Let `Z ⊆ X` be a closed subspace of an algebraic space
over `S`, let `W` be an **affine** étale chart of `X`, let `I` be an ideal of global regular
functions on the chart equal to the defining ideal of `Z` there, and let `w` be a point of the
chart scheme at which the germ of every section of `I` lies in the maximal ideal. Then there is a
point of the chart `Z ×_X W` of `Z` lying over `w`.

The ideal is taken as a parameter together with the equality, rather than being the defining ideal
itself, so that a consumer which knows it under another name — the ideal of a slicing sequence,
which is what
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList` supplies
— may use it with no transport of a dependent type.

The chart of `Z` is the closed subscheme of `W` cut out by `I`, by
`AlgebraicGeometry.Space.exists_iso_zeroScheme_chartBaseChange_of_definingIdealAt_eq`, and `w`
lies on its support by
`AlgebraicGeometry.mem_support_ofIdealTop_of_forall_germ_mem_maximalIdeal`, hence in the range of
its closed immersion; the isomorphism carries the preimage back. -/
theorem exists_chartBaseChangeHom_eq_of_forall_germ_mem_maximalIdeal (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    (hW : IsAffine (chartScheme W)) (I : Ideal Γ(chartScheme W, ⊤))
    (hI : definingIdealAt B S hS X Z (op W) = I) (w : chartScheme W)
    (h : ∀ s ∈ I, (chartScheme W).presheaf.germ ⊤ w trivial s ∈
      maximalIdeal ((chartScheme W).presheaf.stalk w)) :
    ∃ z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom),
      chartBaseChangeHom B S hS X Z W z = w := by
  obtain ⟨e, he⟩ :=
    exists_iso_zeroScheme_chartBaseChange_of_definingIdealAt_eq B S hS Z W hW I hI
  obtain ⟨z', hz'⟩ : w ∈ Set.range (Scheme.IdealSheafData.ofIdealTop I).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact mem_support_ofIdealTop_of_forall_germ_mem_maximalIdeal w I h
  have hcancel : ∀ y, (e.inv ≫ e.hom ≫ (Scheme.IdealSheafData.ofIdealTop I).subschemeι).base y =
      (Scheme.IdealSheafData.ofIdealTop I).subschemeι.base y := fun y => by
    rw [Iso.inv_hom_id_assoc]
  have hfac : ∀ y, (e.inv ≫ e.hom ≫ (Scheme.IdealSheafData.ofIdealTop I).subschemeι).base y =
      chartBaseChangeHom B S hS X Z W (e.inv.base y) := fun y => by
    rw [he]
    rfl
  exact ⟨e.inv.base z', ((hfac z').symm.trans (hcancel z')).trans hz'⟩

/-! ### The chart point of a closed subspace in an inverse image of a subspace of the ambient -/

/-- **The point of `|Z|` carried by a point of the chart `Z ×_X W` lies over the point of `|X|`
carried by its image in the chart `W`.** For a closed subspace `Z ⊆ X` of an algebraic space over
`S` and an étale chart `W` of `X`, the square

`Z ×_X W ⟶ Z`, `Z ×_X W ⟶ W`, `Z ⟶ X`, `W ⟶ X`

of the representability datum of the closed immersion commutes, so the point of `|X|` below the
point of `|Z|` determined by a point `z` of the chart scheme of `Z ×_X W` is the one determined by
the point `AlgebraicGeometry.Space.chartBaseChangeHom … z` of the chart scheme of `W`. Both sides
are `AlgebraicGeometry.Space.chartSchemeToPoints` of the respective charts, by
`AlgebraicGeometry.Space.chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm`; they are
written out here in the form in which the hypothesis `hmem` of
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange`
states its left-hand side, so that no rewriting is needed at that interface. -/
theorem pointsMap_ι_pointsMap_chartBaseChangeToSubspace (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    (z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom)) :
    pointsMap B S hS Z.1.toFunctor Z.1.ι
        (pointsMap B S hS (yoneda.obj (Z.2.2.rep.pullback W.1.hom))
          (chartBaseChangeToSubspace B S hS X Z W)
          ((pointsEquivScheme B S hS (Z.2.2.rep.pullback W.1.hom)).symm z)) =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W)).symm
          (chartBaseChangeHom B S hS X Z W z)) := by
  have hnat : pointsMap B S hS (yoneda.obj (Z.2.2.rep.pullback W.1.hom))
        (yoneda.map (Z.2.2.rep.snd W.1.hom))
        ((pointsEquivScheme B S hS (Z.2.2.rep.pullback W.1.hom)).symm z) =
      (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W)).symm
        (chartBaseChangeHom B S hS X Z W z) :=
    (Equiv.eq_symm_apply _).2 (by
      rw [pointsEquivScheme_pointsMap_yoneda, Equiv.apply_symm_apply])
  rw [← pointsMap_comp_apply, (Z.2.2.rep.isPullback W.1.hom).w, pointsMap_comp_apply, hnat]
  -- the site object of the chart under two spellings, `W.obj.left` and the image of `W` under
  -- `AlgebraicGeometry.Space.SmallEtale.toOver`
  congr 1

/-- **The membership hypothesis of the finite-type-point chart, discharged at an inverse image.**
Let `Z ⊆ X` be a closed subspace of an algebraic space over `S`, let `W` be an étale chart of `X`,
let `O ⊆ X` be a subspace of the *ambient* space and let `G ⊆ Z` be its inverse image in `Z`. If
the point of `|X|` carried by the image in the chart `W` of a point `z` of the chart scheme of
`Z ×_X W` lies in the point set of `O`, then the point of `|Z|` carried by `z` lies in the point
set of `G` — which is the hypothesis `hmem` of
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange`.

This is the form the point-set chase of **Stacks 06N3** arrives in: there `X` is an algebraic
space `Fsp` representing the fibre `F = U ×_𝒳 Spec k`, `Z` is the closed subspace
`V(g^*c₁, …, g^*c_r) ⊆ Fsp` cut out by the pulled-back slicing sequence, `O` is the inverse image
`p⁻¹V ⊆ Fsp` of the open subspace `V ⊆ U` which **Stacks 06MD** and **Stacks 06N2** return along
the projection `p : Fsp ⟶ U`, and `G = Z ∩ p⁻¹V` is the fibre of the slice. The hypothesis is then
the membership of the image in `|U|` of the closed point of **Stacks 056U** in the point set of
`V`, after one further application of
`AlgebraicGeometry.Space.range_pointsMap_ι_preimage` at `p` — the same transfer used here at
`Z ⟶ X`, which is why `O` is left an arbitrary subspace and the inverse image is a hypothesis:
the two preimages compose by instantiating the one transfer twice.

The inclusion `G ⟶ Z` is *not* the one through which the chart of `Z` factors, and the chase is
not an identity; see the implementation notes of
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange`.
-/
theorem mem_range_pointsMap_ι_of_mem_range_pointsMap_ι_chartBaseChangeHom
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    (O : Subfunctor X.1) (hO : IsAlgebraicSpace B S hS O.toFunctor)
    (G : Subfunctor Z.1.toFunctor) (hG : G = O.preimage Z.1.ι)
    (z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom))
    (hz : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W)).symm
          (chartBaseChangeHom B S hS X Z W z)) ∈
      Set.range (pointsMap B S hS O.toFunctor O.ι)) :
    pointsMap B S hS (yoneda.obj (Z.2.2.rep.pullback W.1.hom))
        (chartBaseChangeToSubspace B S hS X Z W)
        ((pointsEquivScheme B S hS (Z.2.2.rep.pullback W.1.hom)).symm z) ∈
      Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  subst hG
  rwa [range_pointsMap_ι_preimage B S hS Z.2.1 X.2 Z.1.ι O hO, Set.mem_preimage,
    pointsMap_ι_pointsMap_chartBaseChangeToSubspace]

/-- **A point of the chart of a closed subspace over a prescribed point of the ambient chart, with
the membership hypothesis of the finite-type-point chart already discharged at it.** The
conclusion of
`AlgebraicGeometry.Space.exists_chartBaseChangeHom_eq_of_forall_germ_mem_maximalIdeal` together
with the conclusion of
`AlgebraicGeometry.Space.mem_range_pointsMap_ι_of_mem_range_pointsMap_ι_chartBaseChangeHom` at
the point it produces: given a point `w` of an **affine** étale chart `W` of `X` at which no
section of the defining ideal of `Z` is invertible, and given that the point of `|X|` carried by
`w` lies in the point set of a subspace `O ⊆ X` whose inverse image in `Z` is `G`, the chart
`Z ×_X W` carries a point over `w` whose point of `|Z|` lies in the point set of `G`.

This is what the chart construction of **Stacks 06N3** consumes: *one* point of the chart of the
slice which both lies over the closed point of **Stacks 056U** — so that the scheme-level
unramifiedness read off the germ clause there is available at it, by
`AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field`,
whose hypotheses are all at the image point — and satisfies the membership hypothesis of
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange`.
-/
theorem exists_chartBaseChangeHom_eq_and_mem_range_pointsMap_ι (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    (hW : IsAffine (chartScheme W)) (I : Ideal Γ(chartScheme W, ⊤))
    (hI : definingIdealAt B S hS X Z (op W) = I) (w : chartScheme W)
    (h : ∀ s ∈ I, (chartScheme W).presheaf.germ ⊤ w trivial s ∈
      maximalIdeal ((chartScheme W).presheaf.stalk w))
    (O : Subfunctor X.1) (hO : IsAlgebraicSpace B S hS O.toFunctor)
    (hw : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W)).symm w) ∈
      Set.range (pointsMap B S hS O.toFunctor O.ι))
    (G : Subfunctor Z.1.toFunctor) (hG : G = O.preimage Z.1.ι) :
    ∃ z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom),
      chartBaseChangeHom B S hS X Z W z = w ∧
        pointsMap B S hS (yoneda.obj (Z.2.2.rep.pullback W.1.hom))
            (chartBaseChangeToSubspace B S hS X Z W)
            ((pointsEquivScheme B S hS (Z.2.2.rep.pullback W.1.hom)).symm z) ∈
          Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  obtain ⟨z, hz⟩ :=
    exists_chartBaseChangeHom_eq_of_forall_germ_mem_maximalIdeal B S hS X Z W hW I hI w h
  exact ⟨z, hz, mem_range_pointsMap_ι_of_mem_range_pointsMap_ι_chartBaseChangeHom B S hS X Z W
    O hO G hG z (hz ▸ hw)⟩

/-! ### Unramifiedness of the chart of a closed subspace, read on the algebraic space -/

/-- **Unramifiedness of the chart of a closed subspace over a represented base, read on the
algebraic space.** Let `Z ⊆ X` be a closed subspace of an algebraic space over `S`, let
`ξ : X ⟶ yoneda.obj T` be a morphism to a represented algebraic space, let `W` be an étale chart
of `X` and let `β : W.obj.left ⟶ T` be a morphism of the site under it. If the morphism of
schemes `Z ×_X W ⟶ T` is unramified at a point `z` of `Z ×_X W` in the sense of **Stacks 02G4**,
then the composite `Z ⟶ X ⟶ yoneda.obj T` is unramified at the image of `z` in `|Z|`, in the sense
of **Stacks 03ZH**, part (2).

The square of étale charts is the cartesian square of the representability datum of the closed
immersion: `Z ×_X W ⟶ Z` is an étale chart by
`AlgebraicGeometry.Space.isEtale_chartBaseChangeToSubspace`, the identity chart of `yoneda.obj T`
is one by `AlgebraicGeometry.Space.isEtaleChart_id`, and the morphism of the site between them is
`Z.2.2.rep.snd W.obj.hom ≫ β`. `AlgebraicGeometry.Space.isUnramifiedAt_chartPoint_iff` is an
equivalence, so having the condition on the algebraic space it may be read back on any other
étale chart of `Z`. -/
theorem isUnramifiedAt_chartBaseChangeToSubspace_of_unramifiedAt (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) {T : BigFppfOver B S hS}
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T)) (ξ : X.1 ⟶ yoneda.obj T)
    (W : SmallEtale B S hS X.1) (β : W.obj.left ⟶ T)
    (hβ : W.obj.hom ≫ ξ = yoneda.map β)
    (z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom))
    (hz : _root_.AlgebraicGeometry.UnramifiedAt
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd W.1.hom ≫ β)) z) :
    IsUnramifiedAt B S hS (Z.1.ι ≫ ξ)
      (pointsMap B S hS (yoneda.obj (Z.2.2.rep.pullback W.1.hom))
        (chartBaseChangeToSubspace B S hS X Z W)
        ((pointsEquivScheme B S hS (Z.2.2.rep.pullback W.1.hom)).symm z)) := by
  have hcomm : chartBaseChangeToSubspace B S hS X Z W ≫ Z.1.ι ≫ ξ =
      yoneda.map (Z.2.2.rep.snd W.1.hom ≫ β) ≫ (idChart B S hS T).obj.hom := by
    rw [← Category.assoc, (Z.2.2.rep.isPullback W.1.hom).w, Category.assoc, hβ,
      ← Functor.map_comp]
    exact (Category.comp_id _).symm
  exact (isUnramifiedAt_chartPoint_iff B S hS Z.2.1 hT (Z.1.ι ≫ ξ)
    (Z.2.2.rep.pullback W.1.hom) T (chartBaseChangeToSubspace B S hS X Z W)
    (idChart B S hS T).obj.hom (Z.2.2.rep.snd W.1.hom ≫ β)
    ((isEtale_iff_presheaf_of_yoneda B S hS (chartBaseChangeToSubspace B S hS X Z W)).1
      (isEtale_chartBaseChangeToSubspace B S hS X Z W))
    (idChart B S hS T).property hcomm z).2 hz

/-! ### The three steps joined: an affine étale chart of an open subspace of the closed subspace -/

/-- **The unramifiedness half of the finite-type-point chart, assembled.** Let `Z ⊆ X` be a
closed subspace of an algebraic space over `S`, let `ξ : X ⟶ yoneda.obj T` be a morphism to a
represented algebraic space, let `Wc` be an étale chart of `X` with `β : Wc ⟶ T` under `ξ`, and
let `G ⊆ Z` be an *open* subspace of the closed subspace. Let `z` be a point of the chart scheme
`Z ×_X Wc` at which the morphism of schemes `Z ×_X Wc ⟶ T` is unramified in the sense of
**Stacks 02G4**, and assume the point of `|Z|` it determines lies in the point set of `G`. Then
`G` carries an **affine** étale chart `a : A ⟶ G` and a point `v` of its scheme, together with a
morphism `h : A ⟶ T` of the site realising `a ≫ G ⟶ Z ⟶ yoneda.obj T`, at which the morphism of
schemes `A ⟶ T` is unramified.

This is the closed-then-open form of the configuration: the zero locus of the pulled-back
functions is closed in the ambient chart-carrying space, and the fibre of the slice is an *open*
subspace of it, so the three steps compose as

* `AlgebraicGeometry.Space.isUnramifiedAt_chartBaseChangeToSubspace_of_unramifiedAt` at the
  closed subspace, which puts the scheme-level condition on the algebraic space `Z`;
* `AlgebraicGeometry.Space.isUnramifiedAt_iff_of_isOpenSubspace`, an equivalence, which carries
  it along the inclusion of the open subspace `G`;
* `AlgebraicGeometry.Space.exists_affine_etale_chart_at_point` and
  `AlgebraicGeometry.Space.isUnramifiedAt_pointsMap_chart_iff`, which read it back on an affine
  étale chart of `G`, the target chart being the identity chart of `yoneda.obj T` so that no
  square has to be chosen and full faithfulness of the Yoneda embedding supplies `h`.

The hypothesis `hmem` is where the point-set content sits, and it is a genuine hypothesis rather
than an identity: the two spellings of the point — the image of `z` under the chart of `Z`, and
the image under `G.ι` of a point of `G` — agree only once `z` is known to lie over `G`, and
nothing in the configuration `G ⊆ Z ⊆ X` forces that. Three results of the library discharge it,
each from a different kind of input: `AlgebraicGeometry.Space.range_pointsMap_ι_preimage`
rewrites it as membership of the point of the chart in the point set of
`CategoryTheory.Subfunctor.preimage` of `G`;
`AlgebraicGeometry.Space.exists_opens_mem_iff_mem_range_pointsMap_ι` rewrites it as membership of
the underlying scheme point in an open of the chart scheme; and
`AlgebraicGeometry.Space.mem_range_pointsMap_ι_of_range_le` discharges it outright when the chart
of `Z` factors through `G`, i.e. after the chart has been shrunk. At the configuration of
**Stacks 06N3** it is the first of the three that applies, and
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal`
is this statement with the hypothesis discharged that way. -/
theorem exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    {T : BigFppfOver B S hS} (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
    (ξ : X.1 ⟶ yoneda.obj T) (Wc : SmallEtale B S hS X.1) (β : Wc.obj.left ⟶ T)
    (hβ : Wc.obj.hom ≫ ξ = yoneda.map β)
    (G : Subfunctor Z.1.toFunctor) (hG : IsOpenSubspace B S hS G)
    (z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback Wc.1.hom))
    (hz : _root_.AlgebraicGeometry.UnramifiedAt
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd Wc.1.hom ≫ β)) z)
    (hmem : pointsMap B S hS (yoneda.obj (Z.2.2.rep.pullback Wc.1.hom))
        (chartBaseChangeToSubspace B S hS X Z Wc)
        ((pointsEquivScheme B S hS (Z.2.2.rep.pullback Wc.1.hom)).symm z) ∈
      Set.range (pointsMap B S hS G.toFunctor G.ι)) :
    ∃ (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ G.toFunctor) (h : A ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      a ≫ G.ι ≫ Z.1.ι ≫ ξ = yoneda.map h ∧
      ∃ v : (BigFppfOver.toScheme B S hS).obj A,
        _root_.AlgebraicGeometry.UnramifiedAt ((BigFppfOver.toScheme B S hS).map h) v := by
  obtain ⟨w, hw⟩ := hmem
  have h₁ : IsUnramifiedAt B S hS (Z.1.ι ≫ ξ) (pointsMap B S hS G.toFunctor G.ι w) := by
    rw [hw]
    exact isUnramifiedAt_chartBaseChangeToSubspace_of_unramifiedAt B S hS X Z hT ξ Wc β hβ z hz
  have h₂ : IsUnramifiedAt B S hS (G.ι ≫ Z.1.ι ≫ ξ) w :=
    (isUnramifiedAt_iff_of_isOpenSubspace B S hS Z.2.1 hT G hG (Z.1.ι ≫ ξ) w).1 h₁
  obtain ⟨A, a, hAaffine, haEtale, u, hu⟩ :=
    exists_affine_etale_chart_at_point B S hS G.toFunctor hG.1 w
  have hfac : a ≫ G.ι ≫ Z.1.ι ≫ ξ = yoneda.map (yoneda.preimage (a ≫ G.ι ≫ Z.1.ι ≫ ξ)) :=
    (yoneda.map_preimage _).symm
  refine ⟨A, a, yoneda.preimage (a ≫ G.ι ≫ Z.1.ι ≫ ξ), hAaffine, haEtale, hfac,
    pointsToScheme B S hS A u, ?_⟩
  refine (isUnramifiedAt_pointsMap_chart_iff B S hS hG.1 hT (G.ι ≫ Z.1.ι ≫ ξ) A T a
    (idChart B S hS T).obj.hom (yoneda.preimage (a ≫ G.ι ≫ Z.1.ι ≫ ξ)) haEtale
    (idChart B S hS T).property (hfac.trans (Category.comp_id _).symm) u).1 ?_
  rwa [hu]

/-- **The unramifiedness half of the finite-type-point chart with no point-set hypothesis left.**
The same conclusion as
`AlgebraicGeometry.Space.exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange`,
at the configuration in which the open subspace `G ⊆ Z` is the inverse image in `Z` of an open
subspace `O ⊆ X` of the *ambient* space, with the membership hypothesis discharged from the
geometric datum it is a consequence of: a point `w` of an **affine** étale chart `Wc` of `X` at
which no section of the defining ideal of `Z` is invertible and whose point of `|X|` lies in the
point set of `O`.

The unramifiedness is assumed at every point of the chart `Z ×_X Wc` over `w`, which is the form
in which it is available: the criterion of **Stacks 02GF** read on the chart,
`AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field`,
states all of its hypotheses at the image in `Wc` of the point of the chart of `Z`, so one
application of it discharges the clause for every such point at once.

At the configuration of **Stacks 06N3**, `X` is an algebraic space `Fsp` representing the fibre
`F = U ×_𝒳 Spec k`, `Z` is `V(g^*c₁, …, g^*c_r) ⊆ Fsp`, `O` is `p⁻¹V` for the open subspace
`V ⊆ U` of **Stacks 06MD** and **Stacks 06N2** and `w` is the closed point of **Stacks 056U** on
an affine étale chart of `Fsp`; the one remaining input, the membership of the point of `|Fsp|`
carried by `w` in the point set of `p⁻¹V`, is the membership of its image in `|U|` in the point
set of `V` — the conclusion of
`Stack.exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`
— through `AlgebraicGeometry.Space.range_pointsMap_ι_preimage` at `p`. -/
theorem exists_affine_etale_chart_unramifiedAt_of_forall_germ_mem_maximalIdeal
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    {T : BigFppfOver B S hS} (hT : IsAlgebraicSpace B S hS (yoneda.obj T))
    (ξ : X.1 ⟶ yoneda.obj T) (Wc : SmallEtale B S hS X.1) (β : Wc.obj.left ⟶ T)
    (hβ : Wc.obj.hom ≫ ξ = yoneda.map β) (hWc : IsAffine (chartScheme Wc))
    (I : Ideal Γ(chartScheme Wc, ⊤)) (hI : definingIdealAt B S hS X Z (op Wc) = I)
    (w : chartScheme Wc)
    (hgerm : ∀ s ∈ I, (chartScheme Wc).presheaf.germ ⊤ w trivial s ∈
      maximalIdeal ((chartScheme Wc).presheaf.stalk w))
    (hunr : ∀ z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback Wc.1.hom),
      chartBaseChangeHom B S hS X Z Wc z = w →
        _root_.AlgebraicGeometry.UnramifiedAt
          ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd Wc.1.hom ≫ β)) z)
    (O : Subfunctor X.1) (hO : IsOpenSubspace B S hS O)
    (hw : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj Wc)) Wc.1.hom
        ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj Wc)).symm w) ∈
      Set.range (pointsMap B S hS O.toFunctor O.ι))
    (G : Subfunctor Z.1.toFunctor) (hG : G = O.preimage Z.1.ι) :
    ∃ (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ G.toFunctor) (h : A ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      a ≫ G.ι ≫ Z.1.ι ≫ ξ = yoneda.map h ∧
      ∃ v : (BigFppfOver.toScheme B S hS).obj A,
        _root_.AlgebraicGeometry.UnramifiedAt ((BigFppfOver.toScheme B S hS).map h) v := by
  obtain ⟨z, hzw, hmem⟩ := exists_chartBaseChangeHom_eq_and_mem_range_pointsMap_ι B S hS X Z Wc
    hWc I hI w hgerm O hO.1 hw G hG
  exact exists_affine_etale_chart_unramifiedAt_of_unramifiedAt_chartBaseChange B S hS X Z hT ξ
    Wc β hβ G (hG ▸ isOpenSubspace_preimage B S hS Z.1.ι O X.2 Z.2.1 hO) z (hunr z hzw) hmem

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  {r : ℕ}
  (c : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)

/-- **The slice of Stacks 06MD is the zero locus of the restricted functions on the open
subspace.** For an open subspace `V ⊆ U` of an algebraic space over `S` and global regular
functions `c₁, …, c_r` on `U`,

`V(ι^*c₁, …, ι^*c_r) = V(c₁, …, c_r) ∩ V`

as subfunctors of `V`, where `ι : V ⟶ U` is the inclusion. So the slice `Stacks 06MD` returns is
itself a zero locus of finitely many global regular functions on an algebraic space, namely on
`V`, and every statement about `AlgebraicGeometry.Space.vanishingSubfunctor` applies to it at that
algebraic space.

This is `AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage` — the zero
locus of pulled-back functions is the inverse image of the zero locus, with no hypothesis on the
morphism — read at the open immersion `ι`, `AlgebraicGeometry.Stack.zeroLocusOnOpen` being by
definition that inverse image. -/
theorem vanishingSubfunctor_globalFunctionsMap_ι_eq_zeroLocusOnOpen (V : Subfunctor U)
    (hV : Space.IsOpenSubspace B S hS V) :
    Space.vanishingSubfunctor B S hS ⟨V.toFunctor, hV.1⟩
        (fun i => Space.globalFunctionsMap B S hS
          (ObjectProperty.homMk V.ι : (⟨V.toFunctor, hV.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩)
          (c i)) =
      zeroLocusOnOpen B S hS U hU c V :=
  Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage B S hS _ c

end Stack

end AlgebraicGeometry

end
