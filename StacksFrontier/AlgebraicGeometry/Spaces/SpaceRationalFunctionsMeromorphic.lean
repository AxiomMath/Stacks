module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Local
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart

/-!
# The rational functions of an algebraic space are its meromorphic functions

Let `X` be an algebraic space over a scheme `S` satisfying the three hypotheses of Stacks 0ENA:
every weakly associated point of `X` has codimension `0`, the irreducible components of `X` are
locally finite, and every codimension-zero point of `X` is representable by a monomorphism from
the spectrum of a field.  The canonical ring homomorphism

`R(X) ⟶ Γ(X, 𝒦_X)`

from the rational functions of Stacks 0EMP to the meromorphic functions was built, and shown to
be injective, in `StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart`.  This file
proves it **surjective**, so that `R(X) = Γ(X, 𝒦_X)`.

Write `Y` for the scheme of the chart presenting the schematic locus of `X` at its
codimension-zero points.  A meromorphic function `m` is a fraction over every affine open `V` of
`Y`: over the étale chart cut out by `V` the ring `𝒦_X` is the total ring of fractions of `𝒪_X`,
so `m = p / q` there with `q` a nonzerodivisor.  On the basic open `Y_q` the denominator is
invertible, so `m` is *regular* on `Y_q`, and `q` being a nonzerodivisor on an affine open forces
`Y_q` to contain every generic point of `Y` lying in `V`.  The union `Ω` of these basic opens
therefore contains all of `genericPoints Y` and is dense, the local regular functions agree on
overlaps because regular functions inject into meromorphic ones, and gluing them produces a
regular function on `Ω` whose associated rational function is carried to `m`.

## Main results

* `AlgebraicGeometry.mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints`: on an affine
  open of a scheme whose weakly associated points are generic points and whose quasi-compact
  opens have finitely many irreducible components, a nonzerodivisor is invertible at every
  generic point of the ambient scheme lying in that open.
* `AlgebraicGeometry.Space.eq_of_openChartHomOfLE_restriction_eq`: a sheaf on the small étale
  site is separated for an arbitrary family of Zariski opens covering a Zariski open of a chart.
* `AlgebraicGeometry.Space.surjective_rationalToMeromorphic`: the canonical map from the
  rational functions to the meromorphic functions is surjective.
* `AlgebraicGeometry.Space.exists_ringEquiv_rationalFunctions_meromorphicFunction`: **the third
  conclusion of Stacks 0ENA**, `R(X) = Γ(X, 𝒦_X)`.

## Implementation notes

The regular functions on the étale chart cut out by a Zariski open `O` of the chart scheme are
the sections of the structure sheaf of that scheme over `O`, by
`AlgebraicGeometry.Space.openChartGlobalSectionsIso`; that comparison is packaged here as the
ring isomorphism `AlgebraicGeometry.Space.schematicSection`, because the construction has to
multiply sections and to transport both units and nonzerodivisors across it.  Its compatibility
with restriction, `AlgebraicGeometry.Space.schematicSection_map`, is the only place where the
two descriptions are compared; all four maps involved are restriction maps of the structure
sheaf of the chart scheme between fixed opens, once
`AlgebraicGeometry.Scheme.homOfLE_appTop` has identified the pullback along an inclusion of
opens, so the comparison is the equality of two composites in a thin category.  The intermediate
object of one of those composites is, however, only definitionally the one written in the other
description, so that composite has to be restated by `show` before
`CategoryTheory.Functor.map_comp` will contract it: the rewriting tactics do not see through the
two descriptions of the same ring.

The gluing is performed on the chart scheme with `TopCat.Sheaf.existsUnique_gluing` rather than
on the small étale site: the covering family is a family of Zariski opens of one scheme, where
compatibility is the pairwise condition on intersections, whereas the étale sheaf condition
would ask for descent data along a whole sieve.  Transporting the glued section back to the
chart then needs separatedness of `𝒦_X` for an *arbitrary* open cover of a Zariski-open chart,
which is `AlgebraicGeometry.Space.eq_of_openChartHomOfLE_restriction_eq`; the covering sieve
comes from the input of
`AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology`, namely
`AlgebraicGeometry.Space.SmallEtale.ofArrows_mem_topology`, applied to the inclusions
`AlgebraicGeometry.Space.openChartHomOfLE` rather than to the inclusions into the ambient chart.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-! ### Nonzerodivisors are invertible at the generic points of an affine open -/

/-- **A nonzerodivisor on an affine open is invertible at every generic point lying in it.**

Let `Z` be a scheme whose weakly associated points are generic points of irreducible components
and whose quasi-compact opens have finitely many irreducible components, and let `V` be an affine
open of `Z`.  The product of the local rings of `Z` at the generic points lying in `V` is the
total ring of fractions of `Γ(Z, V)` by the affine case of Stacks 0EMF, so a nonzerodivisor `q`
becomes a unit there; a unit of a product has unit components, and the component at a generic
point `y ∈ V` is the germ of `q` at `y`. -/
@[ega "IV 20.1.3.1" "partial"]
theorem mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints {Z : Scheme.{u}}
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints Z ⊆ genericPoints Z)
    (hfinite : ∀ V : Z.Opens, IsCompact (V : Set Z) → (irreducibleComponents V).Finite)
    {V : Z.Opens} (hV : IsAffineOpen V) {q : Γ(Z, V)} (hq : q ∈ nonZeroDivisors Γ(Z, V))
    {y : Z} (hy : y ∈ genericPoints Z) (hyV : y ∈ V) :
    y ∈ Z.basicOpen q := by
  let : ∀ η : {η : genericPoints Z // η.1 ∈ V}, Algebra Γ(Z, V) (Z.presheaf.stalk η.1.1) :=
    fun η => Z.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  have := isLocalization_pi_stalk_genericPoints hass hfinite hV
  have hunit : IsUnit (algebraMap Γ(Z, V)
      (∀ η : {η : genericPoints Z // η.1 ∈ V}, Z.presheaf.stalk η.1.1) q) :=
    IsLocalization.map_units _ (⟨q, hq⟩ : nonZeroDivisors Γ(Z, V))
  rw [Scheme.mem_basicOpen Z q y hyV]
  have h := Pi.isUnit_iff.mp hunit ⟨⟨y, hy⟩, hyV⟩
  rwa [Pi.algebraMap_apply,
    TopCat.Presheaf.stalk_open_algebraMap Z.presheaf (⟨y, hyV⟩ : V)] at h

/-- An open subset of a scheme containing every generic point is dense: the generic points are
dense by `genericPoints.closure`. -/
theorem dense_of_genericPoints_subset {Z : Scheme.{u}} {Ω : Z.Opens}
    (h : genericPoints Z ⊆ (Ω : Set Z)) : Dense (Ω : Set Z) :=
  (dense_iff_closure_eq.mpr genericPoints.closure).mono h

namespace Space

attribute [local instance] pointTopology

/-! ### Separatedness for a family of opens covering a Zariski-open chart -/

section Cover

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **A family of Zariski opens covering a Zariski open of a chart induces a covering sieve of
the chart that open cuts out.**

The morphisms of charts induced by the inclusions of opens have the inclusions of open
subschemes as underlying morphisms of schemes, by
`AlgebraicGeometry.Space.toScheme_map_toOver_map_openChartHomOfLE`, so they are étale and
jointly surjective.  This is the analogue, for the inclusions
`AlgebraicGeometry.Space.openChartHomOfLE`, of
`AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology`. -/
theorem ofArrows_openChartHomOfLE_mem_topology (A : SmallEtale B S hS F)
    {Ω : (chartScheme A).Opens} {ι : Type*} (O : ι → (chartScheme A).Opens)
    (hle : ∀ i, O i ≤ Ω) (hΩ : Ω ≤ ⨆ i, O i) :
    Sieve.ofArrows (fun i => openChart B S hS F A (O i))
        (fun i => openChartHomOfLE B S hS F A (hle i)) ∈
      SmallEtale.topology B S hS F (openChart B S hS F A Ω) := by
  refine SmallEtale.ofArrows_mem_topology B S hS F _ _ ?_
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
  refine ⟨fun x => ?_, fun i => etale_toScheme_toOver_map B S hS F _⟩
  let x' : (Ω : (chartScheme A).Opens).toScheme := x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hΩ x'.2)
  have hmem : x' ∈ Set.range ((chartScheme A).homOfLE (hle i)) :=
    ⟨⟨x'.1, hi⟩, Subtype.ext (Scheme.homOfLE_apply (hle i) ⟨x'.1, hi⟩)⟩
  exact ⟨i, hmem⟩

/-- **A sheaf of commutative rings on the small étale site is separated for an arbitrary family
of Zariski opens covering a Zariski open of a chart.**  Two sections over the chart cut out by
`Ω` whose restrictions to the charts cut out by the members of a cover of `Ω` agree are equal.

This is `AlgebraicGeometry.Space.eq_of_openChart_restriction_eq_commRingCat` with the family of
all affine opens of a chart replaced by an arbitrary open cover of a Zariski open. -/
theorem eq_of_openChartHomOfLE_restriction_eq (G : (SmallEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{v})
    (hG : Presheaf.IsSheaf (SmallEtale.topology B S hS F) G) (A : SmallEtale B S hS F)
    {Ω : (chartScheme A).Opens} {ι : Type*} (O : ι → (chartScheme A).Opens)
    (hle : ∀ i, O i ≤ Ω) (hΩ : Ω ≤ ⨆ i, O i)
    {a b : G.obj (op (openChart B S hS F A Ω))}
    (h : ∀ i, (G.map (openChartHomOfLE B S hS F A (hle i)).op).hom a =
      (G.map (openChartHomOfLE B S hS F A (hle i)).op).hom b) :
    a = b := by
  refine hG.isSeparated (openChart B S hS F A Ω) _
    (ofArrows_openChartHomOfLE_mem_topology B S hS F A O hle hΩ) a b ?_
  intro V f hf
  obtain ⟨i, g, rfl⟩ := Sieve.ofArrows.exists hf
  simp only [op_comp, G.map_comp, CommRingCat.comp_apply, h i]

/-! ### Regular functions on a Zariski-open chart and restriction -/

/-- **The comparison between the regular functions on a Zariski-open chart and the sections of
the structure sheaf of the chart scheme is compatible with restriction.**

Pullback along `AlgebraicGeometry.Space.openChartHomOfLE` is, on global sections, pullback along
the inclusion of open subschemes, which `AlgebraicGeometry.Scheme.homOfLE_appTop` identifies
with a restriction map of the chart scheme; all four maps involved are then restriction maps of
that one presheaf, and both composites are restrictions between the same two opens. -/
theorem openChartGlobalSectionsIso_inv_comp (A : SmallEtale B S hS F)
    {O O' : (chartScheme A).Opens} (h : O ≤ O') :
    (openChartGlobalSectionsIso A O').inv ≫
        (structurePresheaf B S hS F).map (openChartHomOfLE B S hS F A h).op =
      (chartScheme A).presheaf.map (homOfLE h).op ≫ (openChartGlobalSectionsIso A O).inv := by
  have e : (structurePresheaf B S hS F).map (openChartHomOfLE B S hS F A h).op =
      ((chartScheme A).homOfLE h).appTop := rfl
  have e' : openChartGlobalSectionsIso A O = O.topIso := rfl
  have e'' : openChartGlobalSectionsIso A O' = O'.topIso := rfl
  rw [e, e', e'', Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv]
  show (chartScheme A).presheaf.map (eqToHom O'.ι_image_top).op ≫
      (chartScheme A).presheaf.map
        (homOfLE ((chartScheme A).ι_image_homOfLE_le_ι_image h ⊤)).op =
    (chartScheme A).presheaf.map (homOfLE h).op ≫
      (chartScheme A).presheaf.map (eqToHom O.ι_image_top).op
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end Cover

/-! ### Surjectivity of the comparison -/

section Surjective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (P : CodimensionZeroPresentation B S hS X.1)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

/-- The scheme of the chart presenting the schematic locus at the codimension-zero points. -/
noncomputable abbrev schematicChartScheme : Scheme.{u} :=
  chartScheme P.schematicChart

/-- The étale chart of `X` cut out by a Zariski open of
`AlgebraicGeometry.Space.schematicChartScheme`. -/
noncomputable abbrev schematicOpenChart (O : (schematicChartScheme P).Opens) :
    SmallEtale B S hS X.1 :=
  openChart B S hS X.1 P.schematicChart O

/-- **The regular functions on a Zariski-open chart of the schematic chart are the sections of
the structure sheaf of its scheme over that open**, as rings.  This is
`AlgebraicGeometry.Space.openChartGlobalSectionsIso` read as a ring isomorphism, in the
direction that produces a regular function on the chart. -/
noncomputable def schematicSection (O : (schematicChartScheme P).Opens) :
    Γ(schematicChartScheme P, O) ≃+*
      (structurePresheaf B S hS X.1).obj (op (schematicOpenChart P O)) :=
  (openChartGlobalSectionsIso P.schematicChart O).commRingCatIsoToRingEquiv.symm

/-- `AlgebraicGeometry.Space.schematicSection` is compatible with restriction to a smaller
Zariski open. -/
theorem schematicSection_map {O O' : (schematicChartScheme P).Opens} (h : O ≤ O')
    (s : Γ(schematicChartScheme P, O')) :
    ((structurePresheaf B S hS X.1).map
          (openChartHomOfLE B S hS X.1 P.schematicChart h).op).hom (schematicSection P O' s) =
      schematicSection P O (((schematicChartScheme P).presheaf.map (homOfLE h).op).hom s) :=
  ConcreteCategory.congr_hom
    (openChartGlobalSectionsIso_inv_comp B S hS X.1 P.schematicChart h) s

/-- **A fraction whose denominator has become invertible on a chart is a regular function there
whose image in the meromorphic functions is the given meromorphic section.**

Stated for an arbitrary section `m` of `𝒦_X` over the chart rather than for the value of a
global meromorphic function: the computation is multiplication in `𝒦_X(U)` and nothing about `m`
beyond the equation `m · b = a` enters, and the chartwise form is what reads the coefficient of
a meromorphic *section* as a regular function. -/
theorem chartToMeromorphic_mul_eq_section (U : SmallEtale B S hS X.1)
    (m : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U))
    {a b c : (structurePresheaf B S hS X.1).obj (op U)} (hbc : b * c = 1)
    (h : m * chartToMeromorphic U b = chartToMeromorphic U a) :
    chartToMeromorphic U (a * c) = m := by
  rw [map_mul, ← h, mul_assoc, ← map_mul, hbc, map_one, mul_one]

/-- **A fraction whose denominator has become invertible on a chart is a regular function there
whose image in the meromorphic functions is the given meromorphic function.**  This reads
`AlgebraicGeometry.Space.chartToMeromorphic_mul_eq_section` at the value over the chart of a
global meromorphic function. -/
theorem chartToMeromorphic_mul_eq_val (m : MeromorphicFunction B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1)
    {a b c : (structurePresheaf B S hS X.1).obj (op U)} (hbc : b * c = 1)
    (h : m.val (op U) * chartToMeromorphic U b = chartToMeromorphic U a) :
    chartToMeromorphic U (a * c) = m.val (op U) :=
  chartToMeromorphic_mul_eq_section U (m.val (op U)) hbc h

/-- **A regular function on a Zariski open whose image in the meromorphic functions is a given
meromorphic function has the same property on every smaller Zariski open**, by naturality of
`𝒪_X ⟶ 𝒦_X` and of the meromorphic function. -/
theorem chartToMeromorphic_schematicSection_restrict (m : MeromorphicFunction B S hS X.1 X.2)
    {Ω D : (schematicChartScheme P).Opens} (hD : D ≤ Ω) (s : Γ(schematicChartScheme P, Ω))
    (hs : chartToMeromorphic (schematicOpenChart P Ω) (schematicSection P Ω s) =
      m.val (op (schematicOpenChart P Ω))) :
    chartToMeromorphic (schematicOpenChart P D)
        (schematicSection P D (((schematicChartScheme P).presheaf.map (homOfLE hD).op).hom s)) =
      m.val (op (schematicOpenChart P D)) := by
  rw [← schematicSection_map P hD s, chartToMeromorphic_naturality, hs,
    meromorphicFunction_val_naturality]

include hwa hfin in
/-- **A meromorphic function is a fraction over an affine open of the schematic chart.**  Over
the étale chart cut out by an affine open the ring of meromorphic functions is the total ring of
fractions of the ring of regular functions, by Stacks 0EN6 part (2). -/
theorem exists_localFraction (m : MeromorphicFunction B S hS X.1 X.2)
    (V : (schematicChartScheme P).affineOpens) :
    ∃ p q : Γ(schematicChartScheme P, V.1),
      q ∈ nonZeroDivisors Γ(schematicChartScheme P, V.1) ∧
        m.val (op (schematicOpenChart P V.1)) *
            chartToMeromorphic (schematicOpenChart P V.1) (schematicSection P V.1 q) =
          chartToMeromorphic (schematicOpenChart P V.1) (schematicSection P V.1 p) := by
  let : Algebra ((structurePresheaf B S hS X.1).obj (op (schematicOpenChart P V.1)))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op (schematicOpenChart P V.1))) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app
      (op (schematicOpenChart P V.1))).hom.toAlgebra
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin
    (schematicOpenChart P V.1) V.2
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
    (nonZeroDivisors ((structurePresheaf B S hS X.1).obj (op (schematicOpenChart P V.1))))
    (m.val (op (schematicOpenChart P V.1)))
  refine ⟨(schematicSection P V.1).symm a, (schematicSection P V.1).symm b.1, ?_, ?_⟩
  · rw [← MulEquivClass.map_nonZeroDivisors (schematicSection P V.1).symm]
    exact ⟨b.1, b.2, rfl⟩
  · rw [(schematicSection P V.1).apply_symm_apply, (schematicSection P V.1).apply_symm_apply]
    exact hab

include hwa hfin in
/-- **A meromorphic function is regular on a Zariski open containing every generic point of an
affine open of the schematic chart.**

Over the affine open `V` the meromorphic function is `p / q` with `q` a nonzerodivisor; on the
basic open of `q` the denominator becomes invertible, so the quotient is a regular function whose
image in the meromorphic functions is the given one, and that basic open contains every generic
point of the chart scheme lying in `V` by
`AlgebraicGeometry.mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints`. -/
theorem exists_openSection_of_affineOpen (m : MeromorphicFunction B S hS X.1 X.2)
    (V : (schematicChartScheme P).affineOpens) :
    ∃ (Ω : (schematicChartScheme P).Opens) (s : Γ(schematicChartScheme P, Ω)),
      (∀ y ∈ genericPoints (schematicChartScheme P), y ∈ V.1 → y ∈ Ω) ∧
        chartToMeromorphic (schematicOpenChart P Ω) (schematicSection P Ω s) =
          m.val (op (schematicOpenChart P Ω)) := by
  obtain ⟨p, q, hq, hpq⟩ := exists_localFraction P hwa hfin m V
  have hDV : (schematicChartScheme P).basicOpen q ≤ V.1 :=
    Scheme.basicOpen_le (schematicChartScheme P) q
  have hu : IsUnit (((schematicChartScheme P).presheaf.map (homOfLE hDV).op).hom q) :=
    (schematicChartScheme P).toRingedSpace.isUnit_res_basicOpen q
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
  refine ⟨(schematicChartScheme P).basicOpen q,
    ((schematicChartScheme P).presheaf.map (homOfLE hDV).op).hom p * w, fun y hy hyV =>
      mem_basicOpen_of_mem_nonZeroDivisors_of_mem_genericPoints
        (schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints B S hS X hwa
          P.schematicChart)
        (fun W hW =>
          finite_irreducibleComponents_chartScheme B S hS hfin P.schematicChart W hW)
        V.2 hq hy hyV, ?_⟩
  have hbc : schematicSection P ((schematicChartScheme P).basicOpen q)
        (((schematicChartScheme P).presheaf.map (homOfLE hDV).op).hom q) *
      schematicSection P ((schematicChartScheme P).basicOpen q) w = 1 := by
    rw [← map_mul, hw, map_one]
  have hres := congrArg (((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
    (openChartHomOfLE B S hS X.1 P.schematicChart hDV).op).hom) hpq
  rw [map_mul, ← chartToMeromorphic_naturality, ← chartToMeromorphic_naturality,
    schematicSection_map, schematicSection_map, meromorphicFunction_val_naturality] at hres
  rw [map_mul]
  exact chartToMeromorphic_mul_eq_val m _ hbc hres

include hwa hfin in
/-- **A regular function on a dense Zariski open of the schematic chart whose image in the
meromorphic functions over that chart is `m` exhibits `m` in the image of the comparison.**

The dense Zariski open cuts out a generic chart `C`, whose image is a dense open subspace `W` of
`X` isomorphic to `C`; transporting the regular function along that isomorphism gives a morphism
`W ⟶ 𝔸¹_S`, hence a rational function, and the value at `C` of its meromorphic function is by
`AlgebraicGeometry.Space.rationalToMeromorphic_val` the regular function itself, that is the
value of `m` at `C`.  A meromorphic function is determined by its value at a generic chart. -/
theorem exists_rationalToMeromorphic_eq (m : MeromorphicFunction B S hS X.1 X.2)
    (Ω : (schematicChartScheme P).Opens) (hΩ : Dense (Ω : Set (schematicChartScheme P)))
    (s : Γ(schematicChartScheme P, Ω))
    (hs : chartToMeromorphic (schematicOpenChart P Ω) (schematicSection P Ω s) =
      m.val (op (schematicOpenChart P Ω))) :
    ∃ x : rationalFunctions B S hS X.2, rationalToMeromorphic P hwa hfin x = m := by
  have hgc : P.IsGenericChart (schematicOpenChart P Ω) :=
    P.isGenericChart_openChart_schematicChart hfin Ω hΩ
  have := hgc.mono
  have hOI : IsOpenImmersion B S hS (schematicOpenChart P Ω).1.hom :=
    isOpenImmersion_openChart P.schematicChart P.isOpenImmersion_schematicChart Ω
  have hdr : DenseRange (pointsMap B S hS (yoneda.obj (schematicOpenChart P Ω).obj.left)
      (schematicOpenChart P Ω).1.hom) :=
    denseRange_pointsMap_openChart P.schematicChart P.denseRange_pointsMap_schematicChart Ω hΩ
  have hWdense : Dense (Set.range (pointsMap B S hS
      (Subfunctor.range (schematicOpenChart P Ω).1.hom).toFunctor
      (Subfunctor.range (schematicOpenChart P Ω).1.hom).ι)) := by
    have hr := range_pointsMap_ι_chartRange (schematicOpenChart P Ω) hOI
    rw [chartRange_eq_range] at hr
    rw [hr]
    exact hdr
  have hW : IsDenseOpenSubspace B S hS X.2 (Subfunctor.range (schematicOpenChart P Ω).1.hom) :=
    ⟨isOpenSubspace_chartRange (schematicOpenChart P Ω) hOI, hWdense⟩
  let f : PartialMap B S hS X.2 (affineLineFunctor B S hS) :=
    ⟨Subfunctor.range (schematicOpenChart P Ω).1.hom, hW,
      inv (Subfunctor.toRange (schematicOpenChart P Ω).1.hom) ≫ yonedaEquiv.symm
        (ofSection B S hS (op (schematicOpenChart P Ω).obj.left) (schematicSection P Ω s))⟩
  refine ⟨PartialMap.toRationalMap B S hS f, ?_⟩
  refine (hgc.bijective_val_genericChart hwa hfin).injective ?_
  rw [rationalToMeromorphic_val P hwa hfin _ (schematicOpenChart P Ω)
    (Subfunctor.toRange (schematicOpenChart P Ω).1.hom)
    (Subfunctor.toRange_ι (schematicOpenChart P Ω).1.hom), ← hs]
  refine congrArg (chartToMeromorphic (schematicOpenChart P Ω)) ?_
  rw [chartCoord, ← yonedaEquiv_comp, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
    Equiv.apply_symm_apply]
  exact affineLineCoordinate_ofSection B S hS _ _

include hwa hfin in
/-- **The canonical map from the rational functions on `X` to the meromorphic functions on `X`
is surjective.**

The basic opens produced by `AlgebraicGeometry.Space.exists_openSection_of_affineOpen` over the
affine opens of the chart scheme contain every generic point of that scheme, hence have dense
union `Ω`; the regular functions on them agree on overlaps because regular functions inject into
meromorphic functions, so they glue to a regular function on `Ω` whose image in the meromorphic
functions over the chart cut out by `Ω` is the given meromorphic function, by separatedness of
`𝒦_X` for that cover. -/
theorem surjective_rationalToMeromorphic :
    Function.Surjective (rationalToMeromorphic P hwa hfin) := by
  intro m
  choose Of sf hgen hval using exists_openSection_of_affineOpen P hwa hfin m
  have hle : ∀ V : (schematicChartScheme P).affineOpens,
      Of V ≤ ⨆ V' : (schematicChartScheme P).affineOpens, Of V' := fun V => le_iSup Of V
  have hdense : Dense ((⨆ V : (schematicChartScheme P).affineOpens, Of V :
      (schematicChartScheme P).Opens) : Set (schematicChartScheme P)) := by
    refine dense_of_genericPoints_subset fun y hy => ?_
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show y ∈ ⨆ V : (schematicChartScheme P).affineOpens,
          (V : (schematicChartScheme P).Opens) from
        (iSup_affineOpens_eq_top (schematicChartScheme P)).ge trivial)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hgen V y hy hV⟩
  have hcompat : TopCat.Presheaf.IsCompatible (schematicChartScheme P).sheaf.1
      (fun V : (schematicChartScheme P).affineOpens => Of V) sf := by
    intro V V'
    show ((schematicChartScheme P).presheaf.map (homOfLE inf_le_left).op).hom (sf V) =
      ((schematicChartScheme P).presheaf.map (homOfLE inf_le_right).op).hom (sf V')
    exact (schematicSection P (Of V ⊓ Of V')).injective
      (injective_toMeromorphicFunctionSheaf_app B S hS X hwa hfin
        (schematicOpenChart P (Of V ⊓ Of V'))
        ((chartToMeromorphic_schematicSection_restrict P m
            (inf_le_left : Of V ⊓ Of V' ≤ Of V) (sf V) (hval V)).trans
          (chartToMeromorphic_schematicSection_restrict P m
            (inf_le_right : Of V ⊓ Of V' ≤ Of V') (sf V') (hval V')).symm))
  obtain ⟨sΩ, hsΩ⟩ :
      ∃ s : Γ(schematicChartScheme P, ⨆ V : (schematicChartScheme P).affineOpens, Of V),
        ∀ V, ((schematicChartScheme P).presheaf.map (homOfLE (hle V)).op).hom s = sf V := by
    obtain ⟨t, ht, -⟩ := (schematicChartScheme P).sheaf.existsUnique_gluing
      (fun V : (schematicChartScheme P).affineOpens => Of V) sf hcompat
    exact ⟨t, fun V => ht V⟩
  refine exists_rationalToMeromorphic_eq P hwa hfin m _ hdense sΩ ?_
  refine eq_of_openChartHomOfLE_restriction_eq B S hS X.1
    (meromorphicFunctionSheaf B S hS X.1 X.2).obj
    (meromorphicFunctionSheaf B S hS X.1 X.2).property P.schematicChart Of hle le_rfl
    fun V => ?_
  rw [← chartToMeromorphic_naturality, schematicSection_map, meromorphicFunction_val_naturality,
    hsΩ V]
  exact hval V

end Surjective

/-! ### The third conclusion of Stacks 0ENA -/

section Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **Stacks 0ENA, the third conclusion.**  Let `X` be an algebraic space over a scheme `S`
such that (a) every weakly associated point of `X` has codimension `0`, (b) the irreducible
components of `X` are locally finite, and (c) every codimension-zero point of `X` is
representable by a monomorphism from the spectrum of a field.  Then the ring `R(X)` of rational
functions of `X` — the classes, modulo agreement on a dense open subspace, of morphisms to the
relative affine line defined on a dense open subspace, of Stacks 0EMP — is the ring
`Γ(X, 𝒦_X)` of meromorphic functions on `X`, the global sections of the sheaf of meromorphic
functions of Stacks 0EN3.

The comparison is the canonical one: a rational function represented by a morphism `ν` regular
on a dense open subspace `W` is sent to the meromorphic function whose value at an étale chart
`U` lying in `W` is the image in `𝒦_X(U)` of the coordinate of `ν` at `U`, and the displayed
equation says exactly that.  It is a ring homomorphism by
`AlgebraicGeometry.Space.rationalToMeromorphicRingHom`, injective by
`AlgebraicGeometry.Space.injective_rationalToMeromorphic` and surjective by
`AlgebraicGeometry.Space.surjective_rationalToMeromorphic`. -/
@[stacks 0ENA "the third conclusion: the ring of rational functions of the space is its ring of
meromorphic functions, R(X) = Γ(X, 𝒦_X), through the comparison that reads a rational function
regular on a dense open subspace as a meromorphic function on every étale chart lying in that
subspace", ega "IV 20.1.13" "Algebraic clause only"]
theorem exists_ringEquiv_rationalFunctions_meromorphicFunction
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS X.1) :
    ∃ e : rationalFunctions B S hS X.2 ≃+* MeromorphicFunction B S hS X.1 X.2,
      ∀ (f : PartialMap B S hS X.2 (affineLineFunctor B S hS))
        (U : SmallEtale B S hS X.1) (τ : yoneda.obj U.obj.left ⟶ f.domain.toFunctor),
        τ ≫ f.domain.ι = U.1.hom →
        (e (PartialMap.toRationalMap B S hS f)).val (op U) =
          ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom
            (affineLineCoordinate B S hS (op U.obj.left)
              (f.hom.app (op U.obj.left) (yonedaEquiv τ))) := by
  obtain ⟨P⟩ := exists_codimensionZeroPresentation B S hS X.2 hfin hmono
  exact ⟨RingEquiv.ofBijective (rationalToMeromorphicRingHom P hwa hfin)
      ⟨injective_rationalToMeromorphic P hwa hfin, surjective_rationalToMeromorphic P hwa hfin⟩,
    fun f U τ hτ => rationalToMeromorphic_val P hwa hfin f U τ hτ⟩

end Final

end Space

end AlgebraicGeometry

end
