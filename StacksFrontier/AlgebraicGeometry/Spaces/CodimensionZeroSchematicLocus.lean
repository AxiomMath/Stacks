module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Topology.LocallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.Topology.Sober.SurjectionComponents

/-!
# Codimension-zero points of an algebraic space lie in the schematic locus

Let `X` be an algebraic space over a scheme `S` which satisfies

* (b) every quasi-compact open of every étale scheme chart of `X` has finitely many
  irreducible components, the condition of Stacks 0BB1
  (`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents`), and
* (c) every point of codimension `0` of `X` is represented by a monomorphism from the
  spectrum of a field (`AlgebraicGeometry.Space.HasMonomorphicCodimensionZeroPoints`).

Then `X` is reasonable by Stacks 0BB8, hence decent, hence it has a dense open subspace which
is a scheme by Stacks 086U; and every point of codimension `0` lies in that subspace, so in
particular in the schematic locus of Stacks 03JH.  This is the assertion of Stacks 0ENA that
the set `X⁰` of codimension-zero points of `X` is contained in the schematic locus — the
assertion which makes the local rings `𝒪_{X, η}` and the canonical morphisms
`j_η : Spec(𝒪_{X, η}) ⟶ X` of `X⁰` well defined.

Those local rings and morphisms are constructed here as well, from a *presentation* of the
schematic locus containing `X⁰`: a representable dense open subspace whose point set contains
every codimension-zero point, which is exactly what the two hypotheses produce.

## Main definitions

* `AlgebraicGeometry.Space.CodimensionZeroPresentation` is a representable dense open subspace
  of `X` whose point set contains every point of codimension `0`, together with a chosen
  scheme representing it.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.stalk` is the local ring `𝒪_{X, η}` at a
  point `η` of codimension `0`, computed on that scheme, and
  `AlgebraicGeometry.Space.CodimensionZeroPresentation.specStalk` is the spectrum of that local
  ring as an object of the big fppf site over `S`.
* `AlgebraicGeometry.Space.CodimensionZeroPresentation.fromSpecStalk` is the canonical morphism
  `j_η : Spec(𝒪_{X, η}) ⟶ X`.

## Main results

All of these live in the namespace `AlgebraicGeometry.Space`, and are named here without that
prefix because two of the names are too long to qualify on one line.

* `isReasonableSpace_of_hasLocallyFiniteIrreducibleComponents` and
  `isDecentSpace_of_hasLocallyFiniteIrreducibleComponents`: under (b) and (c) the space is
  reasonable, hence decent.
* `codimensionZeroPoints_eq_genericPoints_of_hasLocallyFiniteIrreducibleComponents`: under (b)
  and (c) the points of codimension `0` are exactly the generic points of the irreducible
  components of `|X|`.
* `mem_range_pointsMap_ι_of_localRingDimension_eq_zero`: a point of codimension `0` lies over
  every dense open subspace, once (b) holds.
* `locallyFinite_codimensionZeroPoints_of_hasLocallyFiniteIrreducibleComponents`: under (b)
  the set `X⁰` is locally finite in `|X|`, which is what makes the direct sum of Stacks 0ENA
  agree with the product.
* `exists_codimensionZeroPresentation` and
  `codimensionZero_mem_schematicLocus_of_hasLocallyFiniteIrreducibleComponents` are the
  assertion of Stacks 0ENA that `X⁰` is contained in the schematic locus.

## Implementation notes

The containment of `X⁰` in a dense open subspace is obtained chartwise rather than from the
local finiteness of `X⁰` in `|X|`: a point of codimension `0` is covered by an *affine* étale
chart, hypothesis (b) makes the irreducible components of that chart finite in number, and
`AlgebraicGeometry.Space.mem_range_pointsMap_ι_of_mem_genericPoints` then places the point over
the dense open subspace.  Hypothesis (a) of Stacks 0ENA — that every weakly associated point of
`X` has codimension `0` — is not used anywhere in this file.

The local ring at `η` is the Zariski stalk of the chosen representing scheme at a point above
`η`, which is what Stacks means by `𝒪_{X, η}` for `η` in the schematic locus, and `j_η` is
`AlgebraicGeometry.Scheme.fromSpecStalk` there, composed with the presentation and the
inclusion of the subspace.  That the spectrum of the stalk is small enough to be an object of
the site is the only size bookkeeping involved; it is
`AlgebraicGeometry.Space.contains_Spec_stalk`.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BB8](https://stacks.math.columbia.edu/tag/0BB8)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Decency from the two hypotheses -/

/-- A space with finitely many irreducible components on its universal open has finitely many
irreducible components. -/
private theorem finite_irreducibleComponents_of_univ (Y : Type*) [TopologicalSpace Y]
    (h : (irreducibleComponents (⊤ : Opens Y)).Finite) :
    (irreducibleComponents Y).Finite :=
  (ncard_irreducibleComponents_le_of_surjective (Homeomorph.Set.univ Y)
    (Homeomorph.Set.univ Y).continuous (Homeomorph.Set.univ Y).surjective h).1

/-- A quasi-compact étale scheme chart of a space satisfying the condition of Stacks 0BB1 has
finitely many irreducible components. -/
theorem finite_irreducibleComponents_chart_of_hasLocallyFiniteIrreducibleComponents
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (ha : IsEtale B S hS a)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)] :
    (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)).Finite :=
  finite_irreducibleComponents_of_univ _ (hfin U a ha ⊤ (by
    simpa using (isCompact_univ :
      IsCompact (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj U)))))

/-- **An algebraic space satisfying hypotheses (b) and (c) of Stacks 0ENA is reasonable.**

The two hypotheses of Stacks 0BB8 are the condition of Stacks 0BB1, read on the quasi-compact
étale scheme charts, and the existence of monomorphic field-valued representatives at the
points of codimension `0`. -/
theorem isReasonableSpace_of_hasLocallyFiniteIrreducibleComponents
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X) :
    IsReasonableSpace B S hS X :=
  isReasonableSpace_of_finite_irreducibleComponents_of_mono B S hS X hX
    (fun U _hU f hf =>
      finite_irreducibleComponents_chart_of_hasLocallyFiniteIrreducibleComponents B S hS hfin U f
        (isEtale_of_presheaf_etale B S hS hf))
    (fun x hx => hmono x hx)

/-- **An algebraic space satisfying hypotheses (b) and (c) of Stacks 0ENA is decent.** -/
theorem isDecentSpace_of_hasLocallyFiniteIrreducibleComponents
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X) :
    IsDecentSpace B S hS X :=
  isDecentSpace_of_isReasonableSpace B S hS hX
    (isReasonableSpace_of_hasLocallyFiniteIrreducibleComponents B S hS hX hfin hmono)

/-- **`X⁰` is the set of generic points of the irreducible components of `|X|`.** Under
hypotheses (b) and (c) of Stacks 0ENA the space is decent, and Stacks 0ABV identifies the
points of codimension `0` of a decent algebraic space with those generic points. -/
theorem codimensionZeroPoints_eq_genericPoints_of_hasLocallyFiniteIrreducibleComponents
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X) :
    {x : points B S hS X | localRingDimension B S hS x = 0} =
      genericPoints (points B S hS X) := by
  have hdec := isDecentSpace_of_hasLocallyFiniteIrreducibleComponents B S hS hX hfin hmono
  exact Set.ext fun x =>
    ⟨fun hx => mem_genericPoints_of_localRingDimension_eq_zero B S hS hX hdec hx,
      fun hx => localRingDimension_eq_zero_of_mem_genericPoints B S hS hX hdec hx⟩

/-! ### Codimension-zero points lie over every dense open subspace -/

/-- **A point of codimension `0` lies over every dense open subspace**, as soon as every
quasi-compact open of every étale scheme chart has finitely many irreducible components.

An affine étale chart through the point has finitely many irreducible components by that
hypothesis, and the point of the chart above a point of codimension `0` is a generic point of
one of them by Stacks 0BAQ; such a point lies over every dense open subspace. -/
@[sga "3 VIB 5.4.1" "more general"]
theorem mem_range_pointsMap_ι_of_localRingDimension_eq_zero
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    {G : Subfunctor X} (hG : IsOpenSubspace B S hS G)
    (hdense : DenseRange (pointsMap B S hS G.toFunctor G.ι))
    (x : points B S hS X) (hx : localRingDimension B S hS x = 0) :
    x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) := by
  obtain ⟨W, b, hWaff, hbEt, w, hw⟩ := exists_affine_etale_chart_at_point B S hS X hX x
  have hb : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hbEt
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) := inferInstance
  have hfinW : (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj W)).Finite :=
    finite_irreducibleComponents_chart_of_hasLocallyFiniteIrreducibleComponents B S hS hfin W b hb
  have hcp : ChartPoint B S hS W b (pointsToScheme B S hS W w) x :=
    hw ▸ chartPoint_pointsToScheme B S hS W b w
  have hp : pointsToScheme B S hS W w ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj W) :=
    (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX x).mp hx W b _ hb hcp
  have hmem := mem_range_pointsMap_ι_of_mem_genericPoints B S hS hX hG hdense W b hb hfinW w hp
  rwa [hw] at hmem

/-- **`X⁰` is locally finite in `|X|`**, as soon as every quasi-compact open of every étale
scheme chart has finitely many irreducible components.

This is the assertion of the proof of Stacks 0ENA that makes the direct sum over `X⁰` agree
with the product.  An affine étale chart through a given point is a quasi-compact algebraic
space étale over `X`, so it has finitely many points of codimension `0` by condition (3) of
Stacks 0BB1; its open image on points is therefore a neighbourhood of the given point meeting
only finitely many points of codimension `0`, because codimension is an étale invariant
(Stacks 0A4H). -/
theorem locallyFinite_codimensionZeroPoints_of_hasLocallyFiniteIrreducibleComponents
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X) :
    LocallyFinite (fun η : {x : points B S hS X // localRingDimension B S hS x = 0} =>
      ({η.1} : Set (points B S hS X))) := by
  intro x
  obtain ⟨W, b, hWaff, hbEt, w, hw⟩ := exists_affine_etale_chart_at_point B S hS X hX x
  have hb : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hbEt
  have hW : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  have hfinW : {y : points B S hS (yoneda.obj W) | localRingDimension B S hS y = 0}.Finite :=
    (hasLocallyFiniteIrreducibleComponents_iff_finite_codimensionZeroPoints B S hS).mp hfin
      (yoneda.obj W) hW (isQuasiCompactSpace_yoneda_of_isAffine B S hS W hWaff) b hb
  have hRopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj W) b)) :=
    isOpen_range_pointsMap_of_isEtale B S hS b hW hX hb
  have hkey : (Set.range (pointsMap B S hS (yoneda.obj W) b) ∩
      {z : points B S hS X | localRingDimension B S hS z = 0}).Finite := by
    refine (hfinW.image (pointsMap B S hS (yoneda.obj W) b)).subset ?_
    rintro z ⟨⟨y, rfl⟩, hz⟩
    exact ⟨y, (localRingDimension_pointsMap_of_etale B S hS hW hX b hb y).symm.trans hz, rfl⟩
  refine ⟨Set.range (pointsMap B S hS (yoneda.obj W) b), hRopen.mem_nhds ⟨w, hw⟩,
    (hkey.preimage (Subtype.val_injective.injOn)).subset ?_⟩
  rintro η ⟨z, hz, hzR⟩
  rw [Set.mem_singleton_iff] at hz
  exact ⟨hz ▸ hzR, η.2⟩

/-! ### The presentation of the schematic locus at the codimension-zero points -/

/-- **A presentation of the schematic locus at the points of codimension `0`.** A dense open
subspace of `X` which is a scheme and whose point set contains every point of codimension `0`,
together with a chosen object of the site representing it.

This is the data Stacks 0ENA needs in order for the local rings `𝒪_{X, η}` and the canonical
morphisms `j_η : Spec(𝒪_{X, η}) ⟶ X` at the points `η ∈ X⁰` to be defined. -/
structure CodimensionZeroPresentation (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The dense open subspace. -/
  sub : Subfunctor X
  /-- It is an open subspace. -/
  isOpenSubspace : IsOpenSubspace B S hS sub
  /-- An object of the site representing it. -/
  scheme : BigFppfOver B S hS
  /-- The representing isomorphism. -/
  iso : yoneda.obj scheme ≅ sub.toFunctor
  /-- Its point set is dense. -/
  denseRange : DenseRange (pointsMap B S hS sub.toFunctor sub.ι)
  /-- Its point set contains every point of codimension `0`. -/
  mem_range : ∀ x : points B S hS X, localRingDimension B S hS x = 0 →
    x ∈ Set.range (pointsMap B S hS sub.toFunctor sub.ι)

namespace CodimensionZeroPresentation

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : CodimensionZeroPresentation B S hS X)

/-- The étale chart of `X` presenting the dense open subspace. -/
noncomputable abbrev chart : yoneda.obj P.scheme ⟶ X := P.iso.hom ≫ P.sub.ι

/-- The scheme presenting the dense open subspace. -/
noncomputable abbrev schemeObj : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj P.scheme

variable {x : points B S hS X} (hx : localRingDimension B S hS x = 0)

/-- A point of the presenting chart above a given point of codimension `0`. -/
noncomputable def chartPointAt : points B S hS (yoneda.obj P.scheme) :=
  pointsMap B S hS P.sub.toFunctor P.iso.inv (Set.mem_range.mp (P.mem_range x hx)).choose

/-- The chosen point of the presenting chart does lie above the given point. -/
theorem pointsMap_chart_chartPointAt :
    pointsMap B S hS (yoneda.obj P.scheme) P.chart (P.chartPointAt hx) = x := by
  set w := (Set.mem_range.mp (P.mem_range x hx)).choose with hwdef
  have h : pointsMap B S hS P.sub.toFunctor P.sub.ι w = x :=
    (Set.mem_range.mp (P.mem_range x hx)).choose_spec
  have hback : pointsMap B S hS (yoneda.obj P.scheme) P.iso.hom
      (pointsMap B S hS P.sub.toFunctor P.iso.inv w) = w := by
    rw [← pointsMap_comp_apply B S hS P.iso.inv P.iso.hom w, P.iso.inv_hom_id, pointsMap_id,
      id_eq]
  rw [chartPointAt, ← hwdef,
    pointsMap_comp_apply B S hS P.iso.hom P.sub.ι
      (pointsMap B S hS P.sub.toFunctor P.iso.inv w), hback]
  exact h

/-- The point of the presenting scheme above a given point of codimension `0`. -/
noncomputable def schemePointAt : P.schemeObj :=
  pointsToScheme B S hS P.scheme (P.chartPointAt hx)

/-- **The local ring `𝒪_{X, η}` at a point of codimension `0`**, computed as the Zariski stalk
of the presenting scheme at the chosen point above it. -/
noncomputable def stalk : CommRingCat.{u} :=
  P.schemeObj.presheaf.stalk (P.schemePointAt hx)

/-! ### The spectrum of the local ring as an object of the site -/

variable (B S hS)

/-- **The spectrum of a stalk of an object of the site is again an object of the site.** -/
theorem contains_Spec_stalk (U : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj U) :
    B.Contains (Spec (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk z)) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ U.left.property
    ((Scheme.mk_stalk_le_size _ z).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0))

variable {B S hS}

/-- **The spectrum of the local ring `𝒪_{X, η}`**, as an object of the big fppf site over
`S`. -/
noncomputable def specStalk : BigFppfOver B S hS :=
  Over.mk ((B.inclusion.preimage (P.schemeObj.fromSpecStalk (P.schemePointAt hx)) :
    B.obj (contains_Spec_stalk B S hS P.scheme (P.schemePointAt hx)) ⟶ P.scheme.left) ≫
      P.scheme.hom)

/-- The canonical morphism from the spectrum of the local ring at a point of codimension `0`
to the scheme presenting the dense open subspace. -/
noncomputable def specStalkToScheme : P.specStalk hx ⟶ P.scheme :=
  Over.homMk (B.inclusion.preimage (P.schemeObj.fromSpecStalk (P.schemePointAt hx))) rfl

/-- The underlying morphism of schemes of
`AlgebraicGeometry.Space.CodimensionZeroPresentation.specStalkToScheme` is
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
theorem toScheme_map_specStalkToScheme :
    (BigFppfOver.toScheme B S hS).map (P.specStalkToScheme hx) =
      P.schemeObj.fromSpecStalk (P.schemePointAt hx) :=
  B.inclusion.map_preimage _

/-- **The canonical morphism `j_η : Spec(𝒪_{X, η}) ⟶ X`** at a point `η` of codimension `0`:
the spectrum of the local ring maps to the scheme presenting the dense open subspace, which
maps to `X`. -/
noncomputable def fromSpecStalk : yoneda.obj (P.specStalk hx) ⟶ X :=
  yoneda.map (P.specStalkToScheme hx) ≫ P.chart

/-- The spectrum `Spec(𝒪_{X, η})` of the local ring at a point of codimension `0`, as an
algebraic space. -/
noncomputable def specStalkSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (P.specStalk hx), isAlgebraicSpace_yoneda B S hS (P.specStalk hx)⟩

/-- The canonical morphism `j_η : Spec(𝒪_{X, η}) ⟶ X` at a point of codimension `0`, as a
morphism of algebraic spaces. -/
noncomputable def genericMorphism (hX : IsAlgebraicSpace B S hS X) :
    P.specStalkSpace hx ⟶ (⟨X, hX⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk (P.fromSpecStalk hx)

end CodimensionZeroPresentation

/-! ### Stacks 0ENA: `X⁰` is contained in the schematic locus -/

/-- **Stacks 0ENA, the assertion that the construction makes sense.** Let `X` be an algebraic
space over a scheme `S` satisfying hypotheses (b) and (c) of Stacks 0ENA — the equivalent
conditions of Stacks 0BB1, and representability of every codimension-zero point by a
monomorphism from the spectrum of a field.  Then `X` has a dense open subspace which is a
scheme and whose point set contains the whole of `X⁰`.

Consequently the local rings `𝒪_{X, η}` and the canonical morphisms
`j_η : Spec(𝒪_{X, η}) ⟶ X` for `η ∈ X⁰` are defined; they are
`AlgebraicGeometry.Space.CodimensionZeroPresentation.stalk` and
`AlgebraicGeometry.Space.CodimensionZeroPresentation.fromSpecStalk`. -/
@[stacks 0ENA "the assertion of the statement that the construction makes sense: the set of
codimension-zero points is contained in the schematic locus, so that the local rings and the
morphisms j_η are defined"]
theorem exists_codimensionZeroPresentation
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X) :
    Nonempty (CodimensionZeroPresentation B S hS X) := by
  obtain ⟨G, hGopen, hGrep, hGdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hX
      (isDecentSpace_of_hasLocallyFiniteIrreducibleComponents B S hS hX hfin hmono)
  have _ : G.toFunctor.IsRepresentable := hGrep
  exact ⟨{ sub := G
           isOpenSubspace := hGopen
           scheme := G.toFunctor.reprX
           iso := G.toFunctor.reprW
           denseRange := hGdense
           mem_range := fun x hx =>
             mem_range_pointsMap_ι_of_localRingDimension_eq_zero B S hS hX hfin hGopen hGdense
               x hx }⟩

/-- **Stacks 0ENA, the assertion that the construction makes sense**, stated with the
schematic locus of Stacks 03JH: under hypotheses (b) and (c) of Stacks 0ENA every point of
codimension `0` of `X` lies in the schematic locus.

The dense open subspace of `AlgebraicGeometry.Space.exists_codimensionZeroPresentation` is a
representable open subspace, hence contained in the schematic locus. -/
@[stacks 0ENA "the assertion of the statement that the construction makes sense, read on the
schematic locus of Tag 03JH"]
theorem codimensionZero_mem_schematicLocus_of_hasLocallyFiniteIrreducibleComponents
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X)
    (x : points B S hS X) (hx : localRingDimension B S hS x = 0) :
    x ∈ Set.range (pointsMap B S hS (schematicLocus B S hS X).toFunctor
      (schematicLocus B S hS X).ι) := by
  obtain ⟨P⟩ := exists_codimensionZeroPresentation B S hS hX hfin hmono
  exact range_pointsMap_ι_le_schematicLocus B S hS P.sub P.isOpenSubspace
    (Functor.IsRepresentable.mk' P.iso) (P.mem_range x hx)

end AlgebraicGeometry.Space

end
