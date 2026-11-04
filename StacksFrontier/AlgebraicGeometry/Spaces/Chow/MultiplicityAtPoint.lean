module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NoetherianQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLength
import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Length
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.SupportGenericPointLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkOrdinary
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPointEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportChartZariski

/-!
# Generic points of the support of a coherent module on an algebraic space

Let `X` be a locally Noetherian algebraic space over a scheme `S`, let `F` be a coherent
`𝒪_X`-module and let `x ∈ |X|`.  **Stacks 0EE4** asserts that the following are equivalent:

1. for some étale morphism `U → X` with `U` a scheme and some `u ∈ U` mapping to `x`, the point
   `u` is a generic point of an irreducible component of `Supp(F|_U)`;
2. the same for every such `U` and `u`;
3. the length of `F` at `x` is finite and nonzero;

and, if `X` is decent (equivalently quasi-separated), also to

4. `x` is a generic point of an irreducible component of `Supp(F)`.

## Main results

* `AlgebraicGeometry.Space.tfae_isGenericPoint_supp_restrictToChart_geometricLength`:
  **Stacks 0EE4, conditions (1), (2) and (3).**
* `AlgebraicGeometry.Space.tfae_isGenericPoint_supportOfSheaf_of_isDecentSpace`:
  **Stacks 0EE4, conditions (1) to (4) for a decent space.**
* `AlgebraicGeometry.Space.isDecentSpace_iff_isAbsolutelyQuasiSeparated_of_isLocallyNoetherian`:
  **the parenthetical of Stacks 0EE4**, a locally Noetherian algebraic space is decent if and
  only if it is quasi-separated.
* `AlgebraicGeometry.Space.geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf`:
  (4) ⇒ (3) with the component given in the subspace `Supp(F)`, the form in which the
  multiplicity of a component of the support is shown to be a positive integer.
* `AlgebraicGeometry.Space.exists_isGenericPoint_supp_restrictToChart_iff_geometricLength` and
  `AlgebraicGeometry.Space.exists_isGenericPoint_supp_restrictToChart_iff_supportOfSheaf`: the
  equivalence of the chart condition at one chart point with (3), and, for a decent space, with
  (4).
* `AlgebraicGeometry.Space.geometricLength_eq_length_stalk_restrictToChart`: the length of `F`
  at a geometric point is the length of the stalk of `F|_U` at any chart point below it.

## Implementation notes

The étale morphisms from schemes to `X` are its étale scheme charts
`AlgebraicGeometry.Space.SmallEtale`, the restriction `F|_U` is
`AlgebraicGeometry.Space.restrictToChart`, a module on the Zariski site of the chart's scheme,
its support is `SheafOfModules.supp`, and "`u` maps to `x`" is
`AlgebraicGeometry.Space.chartSchemeToPoints`.  The irreducible components of a support are
those of the subspace, read in the ambient space through the inclusion.

"The length of `F` at `x`" is the length of Stacks 0EE2: the length
`AlgebraicGeometry.Space.geometricLength` of the stalk at a geometric point above `x`, which by
Stacks 0EE1 (`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`) is independent of the
geometric point.  Condition (3) is stated at every geometric point above `x`.  The support
`Supp(F)` of condition (4) is `AlgebraicGeometry.Space.supportOfSheaf` of the underlying sheaf
of abelian groups.

The proof is the source's.  The chart restriction of a coherent module is quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`) and of finite type
(`AlgebraicGeometry.Space.isFiniteType_restrictToChart`) on a locally Noetherian scheme
(Stacks 03E8), which is where Stacks 07UB and 01XZ enter; the support of its stalk at `u` is the
pullback of its support along `Spec 𝒪_{U, u} → U`, so `u` is a generic point of a component of
the support exactly when the stalk has finite nonzero length, by Stacks 00L5
(`Stacks.Chow.exists_isGenericPoint_component_supp_iff_length`); and that length is the length
at a geometric point above `x`, by Stacks 05VN, 05VP and 0EE1.  For (4) the support of `F|_U`
is the inverse image of `Supp(F)` (Stacks 07TZ), specializations of `|X|` lift to the chart
(Stacks 03K2) and a nontrivial specialization of the chart stays nontrivial in `|X|`
(Stacks 03K5), and `|X|` and `U` are sober (Stacks 03K6, 01IS).

## References

* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 00L5](https://stacks.math.columbia.edu/tag/00L5)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 0BB6](https://stacks.math.columbia.edu/tag/0BB6)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The parenthetical of Stacks 0EE4.**  A locally Noetherian algebraic space over `S` is
decent if and only if it is quasi-separated.

Decency of a quasi-separated algebraic space is the chain of conditions of Stacks 03JX and needs
no finiteness hypothesis; quasi-separatedness of a locally Noetherian decent algebraic space is
Stacks 0BB6. -/
@[stacks 0EE4 "decent iff quasi-separated"]
theorem isDecentSpace_iff_isAbsolutelyQuasiSeparated_of_isLocallyNoetherian
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hNoeth : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y)) :
    IsDecentSpace B S hS X ↔ IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X :=
  ⟨isAbsolutelyQuasiSeparated_of_isLocallyNoetherian_of_isDecentSpace B S hS
      B.contains_terminal X hX hNoeth,
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX⟩

/-! ### Finiteness and positivity of the length of the structure sheaf -/

open IsLocalRing in
/-- The étale local ring of a locally Noetherian algebraic space at a geometric point is
Noetherian, under only the étale-local hypothesis of Stacks 03E6 (local Noetherianity) rather
than the full quasi-compact-and-quasi-separated bundle of
`AlgebraicGeometry.Space.IsNoetherian`.  The argument is the one of
`AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRing`: the geometric point lifts to a small
étale neighbourhood whose chart is a locally Noetherian scheme, so the local ring of the chart
there is Noetherian, and the étale local ring is the strict henselization of that local ring
(Stacks 04KF), which is Noetherian exactly when the ring it henselizes is. -/
private theorem isNoetherianRing_etaleLocalRing_of_hasEtaleLocalProperty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hNloc : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : GeometricPoint B S hS F) :
    IsNoetherianRing (etaleLocalRing B S hS F x) := by
  obtain ⟨U, f, hSurj, hEtale, hUloc⟩ := hNloc
  obtain ⟨⟨V, hVU⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF x f hSurj hEtale
  have hV : (bigEtaleSiteOfFppfSite B).Contains (chartScheme V.chart) := by
    show ((BigFppfOver.toScheme B S hS).obj V.chart.obj.left).size < B.cutoff
    rw [hVU]
    exact U.left.property
  have hVnoeth : IsLocallyNoetherian (chartScheme V.chart) := by
    show IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V.chart.obj.left)
    rw [hVU]
    exact hUloc
  let R := (chartScheme V.chart).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  let T := henselizationTower R
    (separableClosure (ResidueField R) (chartGeometricPoint V).residueField)
  have hT : IsNoetherianRing T.strictHenselization :=
    (isNoetherianRing_iff_henselizations R T.henselization T.strictHenselization
      (separableClosure (ResidueField R) (chartGeometricPoint V).residueField)).2.mp
        inferInstance
  exact isNoetherianRing_of_ringEquiv T.strictHenselization
    (strictHenselizationEquivEtaleLocalRing hF V (bigEtaleSiteOfFppfSite B) hV T)

/-- **The length of the structure sheaf at a generic point of a component of `|X|` is finite
and positive.**  Let `X` be a decent, locally Noetherian algebraic space over `S`, and let `x̄`
be a geometric point of `X` whose image is a generic point of an irreducible component of `|X|`.
Then the length of `𝒪_X` at `x̄` is finite and positive.

This is the case `F = 𝒪_X` of (4) ⇒ (3) of Stacks 0EE4
(`AlgebraicGeometry.Space.tfae_isGenericPoint_supportOfSheaf_of_isDecentSpace`), with the
hypothesis read on `|X| = Supp(𝒪_X)` and proved directly from the étale local ring.  Positivity
holds regardless of `x`: the stalk of `𝒪_X` at any geometric point is the étale local ring there
(`AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv`), which is nonzero because it is a
local ring (Stacks 08AH).  Finiteness uses the hypothesis on `x`: by Stacks 0ABV the local ring
of `X` at `x` has dimension zero, so by Stacks 04N9 the étale local ring at `x̄` has Krull
dimension zero; being also Noetherian, it is Artinian by Stacks 00KH
(`isArtinianRing_iff_krullDimLE_zero`), hence of finite length over itself
(`isFiniteLength_iff_isNoetherian_isArtinian`). -/
theorem geometricLength_structureSheafModule_ne_top_and_pos
    (X : AlgebraicSpaces B S hS)
    (hNloc : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdec : IsDecentSpace B S hS X.1) (x : GeometricPoint B S hS X.1)
    (hx : x.image ∈ genericPoints (points B S hS X.1)) :
    geometricLength B S hS X x (structureSheafModule B S hS X) ≠ ⊤ ∧
      0 < geometricLength B S hS X x (structureSheafModule B S hS X) := by
  have hloc : IsLocalRing (etaleLocalRing B S hS X.1 x) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  have hnoeth : IsNoetherianRing (etaleLocalRing B S hS X.1 x) :=
    isNoetherianRing_etaleLocalRing_of_hasEtaleLocalProperty B S hS X.1 X.2 hNloc x
  have hdim0 : localRingDimension B S hS x.image = 0 :=
    localRingDimension_eq_zero_of_mem_genericPoints B S hS X.2 hdec hx
  have hkrull0 : ringKrullDim (etaleLocalRing B S hS X.1 x) = 0 := by
    rw [ringKrullDim_etaleLocalRing_eq_localRingDimension X.2 x, hdim0]
    simp
  have hKrullDimLE : Ring.KrullDimLE 0 (etaleLocalRing B S hS X.1 x) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hkrull0
  have hArt : IsArtinianRing (etaleLocalRing B S hS X.1 x) :=
    isArtinianRing_iff_krullDimLE_zero.mpr hKrullDimLE
  have hfin : IsFiniteLength (etaleLocalRing B S hS X.1 x) (etaleLocalRing B S hS X.1 x) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have hlen : geometricLength B S hS X x (structureSheafModule B S hS X) =
      Module.length (etaleLocalRing B S hS X.1 x) (etaleLocalRing B S hS X.1 x) :=
    (structureSheafGeometricStalkEquiv B S hS X x).length_eq
  rw [hlen]
  exact ⟨Module.length_ne_top_iff.mpr hfin, Module.length_pos_iff.mpr hloc.toNontrivial⟩

/-! ### The length of a coherent module at a point and the support on a chart -/

section CoherentModule

variable (X : AlgebraicSpaces B S hS)

/-- A point of an étale scheme chart lies over the point of `|X|` it determines. -/
theorem chartPoint_chartSchemeToPoints (W : SmallEtale B S hS X.1) (u : chartScheme W) :
    ChartPoint B S hS W.obj.left W.obj.hom u (chartSchemeToPoints B S hS X.1 W u) :=
  ⟨canonicalSiteFieldPoint B S hS W.obj.left u,
    canonicalSiteFieldPoint_point B S hS W.obj.left u, rfl⟩

/-- **A point of an étale scheme chart above the image of a geometric point is the point of a
small étale neighbourhood of that geometric point with the same chart.**  This is Stacks 05VN
read on the chart, `AlgebraicGeometry.Space.exists_chartLift_of_chartPoint`. -/
theorem exists_smallEtaleNeighborhood_chart_eq (xbar : GeometricPoint B S hS X.1)
    (W : SmallEtale B S hS X.1) (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS X.1 W u = xbar.image) :
    ∃ V : SmallEtaleNeighborhood xbar, ∃ h : V.chart = W,
      h ▸ chartPoint B S hS X.1 V = u := by
  have hcp := chartPoint_chartSchemeToPoints B S hS X W u
  rw [hu] at hcp
  obtain ⟨q, hq, hqu⟩ := exists_chartLift_of_chartPoint B S hS X.2 xbar W u hcp
  exact ⟨⟨W, q, hq⟩, rfl, hqu⟩

/-- **The length of a coherent module at a geometric point is the length of the stalk of its
chart restriction.**  If `u` is a point of an étale scheme chart `W` of `X` whose image in `|X|`
is the image of the geometric point `x̄`, then the length of `F` at `x̄` is the length of the
stalk `(F|_W)_u` over `𝒪_{W, u}`.

The point `u` is the point of a small étale neighbourhood of `x̄` with chart `W`
(`AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_chart_eq`, Stacks 05VN), on which the
length at `x̄` is the length of the Zariski stalk (Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_chartZariskiLength`), which is the ordinary stalk
(`AlgebraicGeometry.Space.chartZariskiModuleStalkStalkEquiv`). -/
theorem geometricLength_eq_length_stalk_restrictToChart (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (xbar : GeometricPoint B S hS X.1) (W : SmallEtale B S hS X.1)
    (u : chartScheme W) (hu : chartSchemeToPoints B S hS X.1 W u = xbar.image) :
    geometricLength B S hS X xbar F =
      Module.length ((chartScheme W).presheaf.stalk u)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          (restrictToChart B S hS X.2 F W).val.presheaf u) := by
  obtain ⟨V, rfl, rfl⟩ := exists_smallEtaleNeighborhood_chart_eq B S hS X xbar W u hu
  rw [geometricLength_eq_chartZariskiLength B S hS X.2 V F,
    chartZariskiLength_chart_chartPoint B S hS X.2 V F]
  exact (chartZariskiModuleStalkStalkEquiv B S hS X.2 V F).length_eq

/-- **Stacks 0EE4 at one chart point.**  Let `X` be a locally Noetherian algebraic space, let
`F` be a coherent `𝒪_X`-module, let `u` be a point of an étale scheme chart `W` of `X`, and
let `x̄` be a geometric point of `X` with the same image in `|X|` as `u`.  Then `u` is a generic
point of an irreducible component of `Supp(F|_W)` exactly when the length of `F` at `x̄` is
finite and nonzero.

The chart restriction `F|_W` is quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`) and of finite type
(`AlgebraicGeometry.Space.isFiniteType_restrictToChart`, which is where coherence of `F`
enters, as in Stacks 07UB), on a locally Noetherian scheme (Stacks 03E8,
`AlgebraicGeometry.Space.isLocallyNoetherian_chartScheme`), so by Stacks 00L5 the generic points
of the components of its support are the points of finite nonzero stalk length
(`Stacks.Chow.exists_isGenericPoint_component_supp_iff_length`); and that stalk length is the
length at `x̄` (`AlgebraicGeometry.Space.geometricLength_eq_length_stalk_restrictToChart`). -/
theorem exists_isGenericPoint_supp_restrictToChart_iff_geometricLength
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F]
    (W : SmallEtale B S hS X.1) (u : chartScheme W) (xbar : GeometricPoint B S hS X.1)
    (hu : chartSchemeToPoints B S hS X.1 W u = xbar.image) :
    (∃ Z : irreducibleComponents
        (SheafOfModules.supp (restrictToChart B S hS X.2 F W) : Set (chartScheme W)),
        IsGenericPoint u (Subtype.val '' Z.1)) ↔
      geometricLength B S hS X xbar F ≠ ⊤ ∧ 0 < geometricLength B S hS X xbar F := by
  have : IsLocallyNoetherian (chartScheme W) := isLocallyNoetherian_chartScheme B S hS X hLN W
  have : (restrictToChart B S hS X.2 F W).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS X F inferInstance W
  have : (restrictToChart B S hS X.2 F W).IsFiniteType :=
    isFiniteType_restrictToChart B S hS X F inferInstance
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F) W
  rw [geometricLength_eq_length_stalk_restrictToChart B S hS X F xbar W u hu]
  exact Stacks.Chow.exists_isGenericPoint_component_supp_iff_length
    (X := chartScheme W) (restrictToChart B S hS X.2 F W) u

/-- A point of `|X|` is the image of a point of some étale scheme chart. -/
theorem exists_chartSchemeToPoints_eq (x : points B S hS X.1) :
    ∃ (W : SmallEtale B S hS X.1) (u : chartScheme W), chartSchemeToPoints B S hS X.1 W u = x := by
  obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X.1 x
  obtain ⟨V⟩ := nonempty_smallEtaleNeighborhood X.2 xbar
  refine ⟨V.chart, chartPoint B S hS X.1 V, ?_⟩
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]
  exact (chartPoint_iff_pointOfEtaleChart_eq B S hS V.chart _ _).mp
    (chartPoint_isChartPoint B S hS xbar V)

/-- **Stacks 0EE4, conditions (1), (2) and (3).**  Let `X` be a locally Noetherian algebraic
space over `S`, let `F` be a coherent `𝒪_X`-module and let `x ∈ |X|`.  The following are
equivalent:

1. for some étale morphism `U → X` with `U` a scheme and some `u ∈ U` mapping to `x`, the point
   `u` is a generic point of an irreducible component of `Supp(F|_U)`;
2. for every étale morphism `U → X` with `U` a scheme and every `u ∈ U` mapping to `x`, the
   point `u` is a generic point of an irreducible component of `Supp(F|_U)`;
3. the length of `F` at `x` is finite and nonzero.

The étale morphisms from schemes are the étale scheme charts `W` of `X`, and `u` maps to `x`
when `AlgebraicGeometry.Space.chartSchemeToPoints` sends it to `x`.  The length of `F` at `x`
is the length of Stacks 0EE2: the length at a geometric point above `x`, which by Stacks 0EE1
(`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`) does not depend on the geometric
point; condition (3) is stated at every geometric point above `x`.

Each chart point above `x` satisfies the chart condition exactly when the length is finite and
nonzero (`AlgebraicGeometry.Space.exists_isGenericPoint_supp_restrictToChart_iff_geometricLength`),
and a chart point above `x` exists. -/
@[stacks 0EE4 "conditions (1), (2) and (3)"]
theorem tfae_isGenericPoint_supp_restrictToChart_geometricLength
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F]
    (x : points B S hS X.1) :
    List.TFAE
      [∃ (W : SmallEtale B S hS X.1) (u : chartScheme W),
          chartSchemeToPoints B S hS X.1 W u = x ∧
            ∃ Z : irreducibleComponents
                (SheafOfModules.supp (restrictToChart B S hS X.2 F W) : Set (chartScheme W)),
              IsGenericPoint u (Subtype.val '' Z.1),
        ∀ (W : SmallEtale B S hS X.1) (u : chartScheme W),
          chartSchemeToPoints B S hS X.1 W u = x →
            ∃ Z : irreducibleComponents
                (SheafOfModules.supp (restrictToChart B S hS X.2 F W) : Set (chartScheme W)),
              IsGenericPoint u (Subtype.val '' Z.1),
        ∀ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x →
          geometricLength B S hS X xbar F ≠ ⊤ ∧ 0 < geometricLength B S hS X xbar F] := by
  tfae_have 1 → 3 := by
    rintro ⟨W, u, hu, hZ⟩ xbar hxbar
    exact (exists_isGenericPoint_supp_restrictToChart_iff_geometricLength B S hS X hLN F W u
      xbar (hu.trans hxbar.symm)).mp hZ
  tfae_have 3 → 2 := by
    intro h W u hu
    obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X.1 x
    exact (exists_isGenericPoint_supp_restrictToChart_iff_geometricLength B S hS X hLN F W u
      xbar (hu.trans hxbar.symm)).mpr (h xbar hxbar)
  tfae_have 2 → 1 := by
    intro h
    obtain ⟨W, u, hu⟩ := exists_chartSchemeToPoints_eq B S hS X x
    exact ⟨W, u, hu, h W u hu⟩
  tfae_finish

/-- The support of the chart restriction of a coherent module is the inverse image of the
support of the module under the map from the chart to `|X|`: this is Stacks 07TZ on the chart,
`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf`, whose comparison
hypothesis is Stacks 05VP, `AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`. -/
theorem supp_restrictToChart_eq_preimage_chartSchemeToPoints (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (W : SmallEtale B S hS X.1) :
    SheafOfModules.supp (restrictToChart B S hS X.2 F W) =
      chartSchemeToPoints B S hS X.1 W ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  refine (supp_restrictToChart_eq_preimage_supportOfSheaf B S hS X W F fun xbar V => ?_).trans ?_
  · have := isIso_chartStalkTensorComparison B S hS X.2 V F
    exact ⟨asIso (chartStalkTensorComparison B S hS X.2 V F)⟩
  · ext v
    rw [Set.mem_preimage, Set.mem_preimage, chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]

/-- **Stacks 0EE4, condition (4) against the chart condition.**  Let `X` be a decent algebraic
space, `F` a coherent `𝒪_X`-module and `u` a point of an étale scheme chart `W`.  Then `u` is a
generic point of an irreducible component of `Supp(F|_W)` exactly when its image in `|X|` is a
generic point of an irreducible component of `Supp(F)`.

The support of `F|_W` is the inverse image of `Supp(F)` (Stacks 07TZ,
`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_chartSchemeToPoints`).  In the sober
spaces `|X|` (Stacks 03K6) and `W` (Stacks 01IS) a generic point of a component of a closed set
is a point of it with no other generization in it
(`TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff`); specializations in `|X|`
lift to `W` (Stacks 03K2, `AlgebraicGeometry.Space.exists_specializes_pointsMap_eq_of_isEtale`),
and a specialization in `W` between two points with the same image is trivial (Stacks 03K5,
`AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers`). -/
theorem exists_isGenericPoint_supp_restrictToChart_iff_supportOfSheaf
    (hdec : IsDecentSpace B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    [IsCoherent B S hS X.1 X.2 F] (W : SmallEtale B S hS X.1) (u : chartScheme W) :
    (∃ Z : irreducibleComponents
        (SheafOfModules.supp (restrictToChart B S hS X.2 F W) : Set (chartScheme W)),
        IsGenericPoint u (Subtype.val '' Z.1)) ↔
      ∃ Z : irreducibleComponents (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)),
        IsGenericPoint (chartSchemeToPoints B S hS X.1 W u) (Subtype.val '' Z.1) := by
  have := t0Space_points_of_isDecentSpace B S hS X.2 hdec
  have := quasiSober_points_of_isDecentSpace B S hS X.2 hdec
  have : (restrictToChart B S hS X.2 F W).IsFiniteType :=
    isFiniteType_restrictToChart B S hS X F inferInstance
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F) W
  set T := supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) with hTdef
  have hT : IsClosed T := isClosed_supportOfSheaf_of_isCoherentOnSite B S hS X F
  set f := chartSchemeToPoints B S hS X.1 W with hfdef
  set e := schemePointsHomeomorph B S hS W.obj.left with hedef
  have hfe : ∀ v, f (e v) = pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom v := by
    intro v
    rw [hfdef, chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm, hedef,
      schemePointsHomeomorph_apply]
    exact congrArg _ ((pointsEquivScheme B S hS W.obj.left).symm_apply_apply v)
  have hfcont : Continuous f := by
    have h : f = pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom ∘ e.symm := by
      funext w
      rw [Function.comp_apply, ← hfe, e.apply_symm_apply]
    rw [h]
    exact (continuous_pointsMap B S hS W.obj.hom).comp e.symm.continuous
  have hfin := hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec
  rw [TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff
      (SheafOfModules.isClosed_supp _) u,
    TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff hT,
    supp_restrictToChart_eq_preimage_chartSchemeToPoints B S hS X F W]
  refine and_congr_right fun _ => ⟨fun hmin y hy hyx => ?_, fun hmin y hy hyu => ?_⟩
  · have hv : pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom (e.symm u) = f u := by
      rw [← hfe, e.apply_symm_apply]
    obtain ⟨v', hv'v, hv'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS X.2 hyx
      (fun V hV ψ hψ => hfin y V hV ψ hψ) W.obj.left W.obj.hom W.property (e.symm u) hv
    have hsp : e v' ⤳ u := by
      simpa only [e.apply_symm_apply] using hv'v.map e.continuous
    have hmem : e v' ∈ f ⁻¹' T := by
      rw [Set.mem_preimage, hfe, hv']
      exact hy
    rw [← hv', ← hfe, hmin _ hmem hsp]
  · have hfy : f y = f u := hmin _ hy (hyu.map hfcont)
    have himg : pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom (e.symm u) =
        pointsMap B S hS (yoneda.obj W.obj.left) W.obj.hom (e.symm y) := by
      rw [← hfe, ← hfe, e.apply_symm_apply, e.apply_symm_apply, hfy]
    have heq := eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS X.2 hfin
      W.obj.left W.obj.hom W.property (e.symm u) (e.symm y) himg (hyu.map e.symm.continuous)
    simpa only [e.apply_symm_apply] using (congrArg e heq).symm

/-- **Stacks 0EE4, conditions (1) to (4), for a decent space.**  Let `X` be a locally Noetherian
algebraic space over `S` which is decent (equivalently, by
`AlgebraicGeometry.Space.isDecentSpace_iff_isAbsolutelyQuasiSeparated_of_isLocallyNoetherian`,
quasi-separated), let `F` be a coherent `𝒪_X`-module and let `x ∈ |X|`.  The three conditions of
`AlgebraicGeometry.Space.tfae_isGenericPoint_supp_restrictToChart_geometricLength` are also
equivalent to

4. `x` is a generic point of an irreducible component of `Supp(F)`.

The support of `F` is the support of Stacks 04KA of its underlying sheaf of abelian groups
(`AlgebraicGeometry.Space.supportOfSheaf`).  Condition (4) is equivalent to the chart condition
at every chart point above `x`
(`AlgebraicGeometry.Space.exists_isGenericPoint_supp_restrictToChart_iff_supportOfSheaf`). -/
@[stacks 0EE4 "conditions (1) to (4), for a decent space"]
theorem tfae_isGenericPoint_supportOfSheaf_of_isDecentSpace
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdec : IsDecentSpace B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    [IsCoherent B S hS X.1 X.2 F] (x : points B S hS X.1) :
    List.TFAE
      [∃ (W : SmallEtale B S hS X.1) (u : chartScheme W),
          chartSchemeToPoints B S hS X.1 W u = x ∧
            ∃ Z : irreducibleComponents
                (SheafOfModules.supp (restrictToChart B S hS X.2 F W) : Set (chartScheme W)),
              IsGenericPoint u (Subtype.val '' Z.1),
        ∀ (W : SmallEtale B S hS X.1) (u : chartScheme W),
          chartSchemeToPoints B S hS X.1 W u = x →
            ∃ Z : irreducibleComponents
                (SheafOfModules.supp (restrictToChart B S hS X.2 F W) : Set (chartScheme W)),
              IsGenericPoint u (Subtype.val '' Z.1),
        ∀ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x →
          geometricLength B S hS X xbar F ≠ ⊤ ∧ 0 < geometricLength B S hS X xbar F,
        ∃ Z : irreducibleComponents
            (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)),
          IsGenericPoint x (Subtype.val '' Z.1)] := by
  have h := tfae_isGenericPoint_supp_restrictToChart_geometricLength B S hS X hLN F x
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 2 ↔ 3 := h.out 2 3
  tfae_have 1 → 4 := by
    rintro ⟨W, u, rfl, hZ⟩
    exact (exists_isGenericPoint_supp_restrictToChart_iff_supportOfSheaf B S hS X hdec F W u).mp
      hZ
  tfae_have 4 → 2 := by
    intro h4 W u hu
    subst hu
    exact (exists_isGenericPoint_supp_restrictToChart_iff_supportOfSheaf B S hS X hdec F W u).mpr
      h4
  tfae_finish

/-- **The length of a coherent module at a generic point of a component of its support is
finite and nonzero**, on a decent, locally Noetherian algebraic space: (4) ⇒ (3) of Stacks 0EE4,
`AlgebraicGeometry.Space.tfae_isGenericPoint_supportOfSheaf_of_isDecentSpace`, with the component
given in the subspace `Supp(F)`, at any geometric point above the generic point. -/
theorem geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdec : IsDecentSpace B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    [IsCoherent B S hS X.1 X.2 F] {x : points B S hS X.1}
    (hx : x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))
    (Z : irreducibleComponents (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)))
    (hZ : IsGenericPoint (⟨x, hx⟩ : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F))
      Z.1)
    (xbar : GeometricPoint B S hS X.1) (hxbar : xbar.LiesOver x) :
    geometricLength B S hS X xbar F ≠ ⊤ ∧ 0 < geometricLength B S hS X xbar F := by
  have hT := isClosed_supportOfSheaf_of_isCoherentOnSite B S hS X F
  have h43 := (tfae_isGenericPoint_supportOfSheaf_of_isDecentSpace B S hS X hLN hdec F x).out 4 3
  refine h43.mp ⟨Z, ?_⟩ xbar hxbar
  rw [isGenericPoint_def, ← hZ.def, ← hT.isClosedEmbedding_subtypeVal.closure_image_eq,
    Set.image_singleton]

end CoherentModule

end AlgebraicGeometry.Space

end
