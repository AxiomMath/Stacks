module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EtaleSiteOfFppfSite
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# Regular global functions on an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `f ∈ Γ(X, 𝒪_X)` be a global regular
function.  Following Stacks 0843, `f` is a *regular section* of `𝒪_X` when multiplication by
`f` is a monomorphism `𝒪_X ⟶ 𝒪_X` of `𝒪_X`-modules on the small étale site of `X`.  Stacks
0844 gives three equivalent tests for this: that the image of `f` in every étale local ring
of `X` at a geometric point is a nonzerodivisor, that the restriction of `f` to every affine
étale chart is a nonzerodivisor, and that the restriction of `f` to one surjective étale
scheme chart is a regular section there.

## Main definitions

* `AlgebraicGeometry.Space.chartValue` is the restriction of a global function on `X` to an
  étale chart, as a global regular function on the scheme underlying the chart, and
  `AlgebraicGeometry.Space.chartFunctionSections` reads that restriction as a global section
  of the chart's structure sheaf on its Zariski site.
* `AlgebraicGeometry.Space.chartPoint` is the point of the scheme underlying a small étale
  neighbourhood of a geometric point at which the local ring is taken.

## Main results

* `AlgebraicGeometry.Space.isRegularSection_iff_etaleLocalRing` is Stacks 0844, conditions
  (1) and (2).
* `AlgebraicGeometry.Space.isRegularSection_iff_affineEtale` is Stacks 0844, conditions (1)
  and (3).
* `AlgebraicGeometry.Space.isRegularSection_iff_exists_surjectiveChart` is Stacks 0844,
  conditions (1) and (4).
* `AlgebraicGeometry.Space.isSMulRegular_etaleLocalRing_iff_germ`: a germ is a nonzerodivisor
  in the étale local ring exactly when it is one in the local ring of a scheme chart.
* `AlgebraicGeometry.Space.etaleLocalRingGerm_chartValue_eq`: the germ of a global function in
  the étale local ring at a geometric point does not depend on the chosen neighbourhood.

## Implementation notes

`Γ(X, 𝒪_X)` is the type of global sections of the structure sheaf regarded as a sheaf of
modules over itself, a compatible family of regular functions on the étale charts, and
condition (1) is `AlgebraicGeometry.IsRegularSection` of Stacks 0843 applied to it.  The
small étale site need not have a terminal chart, so this limit over all charts is what
global sections on a site means; the sheaf of rings indexing the modules is the one of the
small étale ringed site of Stacks 03AD, so regularity of the canonical section of an
effective Cartier divisor (Stacks 0841) is an instance of the predicate.

Condition (1) reduces to regularity on *every* chart by the sectionwise criterion on an
arbitrary site, `AlgebraicGeometry.isRegularSection_iff_forall_isSMulRegular_obj`; conditions
(3) and (4) then compare that with the Zariski-local criteria of Stacks 01WZ on a chart,
which apply because every Zariski open of an étale chart is itself an étale chart
(`AlgebraicGeometry.Space.openChart`).

Condition (2) passes through Stacks 04KF: the étale local ring at a geometric point is the
strict henselization of the local ring of any small étale neighbourhood at the induced point,
and that henselization is faithfully flat over the local ring, so a germ is a nonzerodivisor
in one exactly when it is in the other.  The germ in condition (2) is taken over an arbitrary
small étale neighbourhood of the geometric point; germs over different neighbourhoods agree
by `etaleLocalRingGerm_chartValue_eq`, so quantifying over them states the source's condition
on `𝒪_{X, x̄}` without first having to exhibit a neighbourhood.

## References

* [Stacks Project, Tag 0844](https://stacks.math.columbia.edu/tag/0844)
* [Stacks Project, Tag 0843](https://stacks.math.columbia.edu/tag/0843)
* [Stacks Project, Tag 01WZ](https://stacks.math.columbia.edu/tag/01WZ)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- Global regular functions on the algebraic space `X`: the global sections of the structure
sheaf on the small étale site of `X`, regarded as a sheaf of modules over itself. -/
abbrev GlobalFunctions :=
  (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
    (structurePresheaf B S hS X) (structureRingPresheaf_isSheaf B S hS X hX))).sections

/-- The restriction of a global function on `X` to an étale chart, as a global regular
function on the scheme underlying the chart. -/
def chartValue (f : GlobalFunctions B S hS X hX) (U : SmallEtale B S hS X) :
    Γ(etaleChartScheme B S hS U, ⊤) :=
  structureSectionValue (structurePresheaf B S hS X)
    (structureRingPresheaf_isSheaf B S hS X hX) f (op U)

/-- The restrictions of a global function on `X` to the étale charts are compatible with
pullback along a morphism of charts. -/
theorem chartValue_map {U V : SmallEtale B S hS X} (g : U ⟶ V) (f : GlobalFunctions B S hS X hX) :
    ((structurePresheaf B S hS X).map g.op).hom (chartValue B S hS X hX f V) =
      chartValue B S hS X hX f U :=
  f.property g.op

/-- The restriction of a global function on `X` along a morphism of étale charts is its
pullback along the underlying morphism of schemes. -/
theorem chartValue_map_appTop {U V : SmallEtale B S hS X} (g : U ⟶ V)
    (f : GlobalFunctions B S hS X hX) :
    (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X).map g))).hom (chartValue B S hS X hX f V) =
      chartValue B S hS X hX f U :=
  f.property g.op

/-- **Stacks 0844, condition (1) read on all charts.** A global function on `X` is a regular
section of `𝒪_X` exactly when its restriction to every étale chart is a nonzerodivisor. -/
theorem isRegularSection_iff_forall_chart (f : GlobalFunctions B S hS X hX) :
    IsRegularSection (structurePresheaf B S hS X)
        (structureRingPresheaf_isSheaf B S hS X hX) f ↔
      ∀ U : SmallEtale B S hS X,
        IsSMulRegular (Γ(etaleChartScheme B S hS U, ⊤)) (chartValue B S hS X hX f U) :=
  (isRegularSection_iff_forall_isSMulRegular_obj (structurePresheaf B S hS X)
    (structureRingPresheaf_isSheaf B S hS X hX) f).trans
      ⟨fun h U ↦ h (op U), fun h U ↦ h U.unop⟩

/-- The restriction of a global function on `X` to an étale scheme chart, as a global section
of the structure sheaf of that chart on its Zariski site. -/
def chartFunctionSections (f : GlobalFunctions B S hS X hX) (U : SmallEtale B S hS X) :
    (SheafOfModules.unit ((sheafCompose
      (Opens.grothendieckTopology (etaleChartScheme B S hS U))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (etaleChartScheme B S hS U).sheaf)).sections :=
  globalFunctionSections (etaleChartScheme B S hS U) (chartValue B S hS X hX f U)

/-- The component of `AlgebraicGeometry.Space.chartFunctionSections` on the whole chart is the
restriction of the given global function to that chart. -/
@[simp]
theorem chartFunctionSections_val_top (f : GlobalFunctions B S hS X hX)
    (U : SmallEtale B S hS X) :
    (chartFunctionSections B S hS X hX f U).val (op ⊤) = chartValue B S hS X hX f U :=
  globalFunctionSections_val_top (etaleChartScheme B S hS U) (chartValue B S hS X hX f U)

/-- If a global function on `X` is a nonzerodivisor on every affine étale chart, then its
restriction to an arbitrary étale scheme chart is a regular section of the structure sheaf of
that chart: the affine opens of the chart are themselves affine étale charts of `X`, by
`AlgebraicGeometry.Space.openChart`. -/
theorem isRegularSection_chartFunctionSections (f : GlobalFunctions B S hS X hX)
    (h : ∀ U : SmallEtale B S hS X, IsAffine (etaleChartScheme B S hS U) →
      IsSMulRegular (Γ(etaleChartScheme B S hS U, ⊤)) (chartValue B S hS X hX f U))
    (C : SmallEtale B S hS X) :
    IsRegularSection (etaleChartScheme B S hS C).presheaf
      ((Presheaf.isSheaf_iff_isSheaf_comp _ (etaleChartScheme B S hS C).presheaf
        (forget₂ CommRingCat.{u} RingCat.{u})).mp (etaleChartScheme B S hS C).IsSheaf)
      (chartFunctionSections B S hS X hX f C) := by
  refine (isRegularSection_iff_affineOpen (etaleChartScheme B S hS C)
    (chartFunctionSections B S hS X hX f C)).2 ?_
  intro V hV
  have hW := h (openChart B S hS X C V) hV
  let e : Γ(V.toScheme, ⊤) ≃+* Γ(etaleChartScheme B S hS C, V) :=
    V.topIso.commRingCatIsoToRingEquiv
  have hg : (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X).map (openChartInclusion B S hS X C V)) = V.ι :=
    toScheme_map_toOver_map_openChartInclusion B S hS X C V
  have hfW : chartValue B S hS X hX f (openChart B S hS X C V) =
      (Scheme.Hom.appTop V.ι).hom (chartValue B S hS X hX f C) := by
    rw [← chartValue_map_appTop B S hS X hX (openChartInclusion B S hS X C V) f, hg]
    rfl
  have hmaps (a : Γ(etaleChartScheme B S hS C, ⊤)) :
      e ((Scheme.Hom.appTop V.ι).hom a) =
        (etaleChartScheme B S hS C).presheaf.map
          (homOfLE (show V ≤ ⊤ from le_top)).op a := by
    change ((etaleChartScheme B S hS C).presheaf.map (eqToHom V.ι_image_top.symm).op)
        (((etaleChartScheme B S hS C).presheaf.map
          (homOfLE (x := V.ι ''ᵁ (⊤ : V.toScheme.Opens))
            (show V.ι ''ᵁ (⊤ : V.toScheme.Opens) ≤ ⊤ from le_top)).op) a) =
      ((etaleChartScheme B S hS C).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op) a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    congr 1
  have he : e (chartValue B S hS X hX f (openChart B S hS X C V)) =
      (chartFunctionSections B S hS X hX f C).val (op V) := by
    rw [hfW, hmaps (chartValue B S hS X hX f C)]
    rfl
  rw [← he]
  exact (RingEquiv.isSMulRegular_congr e
    (chartValue B S hS X hX f (openChart B S hS X C V))).mp hW

/-- If the restriction of a global function to a chart is a regular section of the chart's
structure sheaf, its germ at every point of the chart is a nonzerodivisor in the stalk. -/
private theorem isSMulRegular_germ_chartValue_of_isRegularSection
    (f : GlobalFunctions B S hS X hX) (C : SmallEtale B S hS X)
    (hs : IsRegularSection (etaleChartScheme B S hS C).presheaf
      ((Presheaf.isSheaf_iff_isSheaf_comp _ (etaleChartScheme B S hS C).presheaf
        (forget₂ CommRingCat.{u} RingCat.{u})).mp (etaleChartScheme B S hS C).IsSheaf)
      (chartFunctionSections B S hS X hX f C))
    (z : etaleChartScheme B S hS C) :
    IsSMulRegular ((etaleChartScheme B S hS C).presheaf.stalk z)
      ((etaleChartScheme B S hS C).presheaf.germ ⊤ z trivial (chartValue B S hS X hX f C)) := by
  have ht := (isRegularSection_iff_stalk (etaleChartScheme B S hS C).toLocallyRingedSpace
    (chartFunctionSections B S hS X hX f C)).mp hs z
  rwa [chartFunctionSections_val_top] at ht

/-- The point of the scheme underlying a small étale neighbourhood of a geometric point at
which the local ring of the chart is taken: the image of the closed point of the field
spectrum defining the geometric point. -/
abbrev chartPoint {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x) :
    chartScheme V.chart :=
  (chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)

include hX in
/-- **Stacks 04KF.** A germ is a nonzerodivisor in the étale local ring of `X` at a geometric
point exactly when it is a nonzerodivisor in the local ring of a scheme chart at the induced
point: the étale local ring is the strict henselization of that local ring, and a strict
henselization is faithfully flat over the ring it henselizes. -/
theorem isSMulRegular_etaleLocalRing_iff_germ (x : GeometricPoint B S hS X)
    (V : SmallEtaleNeighborhood x) (a : Γ(chartScheme V.chart, ⊤)) :
    IsSMulRegular (etaleLocalRing B S hS X x)
        (etaleLocalRingGerm B S hS X x (op V) a) ↔
      IsSMulRegular ((chartScheme V.chart).presheaf.stalk (chartPoint B S hS X V))
        ((chartScheme V.chart).presheaf.germ ⊤ (chartPoint B S hS X V) trivial a) := by
  have hE : (bigEtaleSiteOfFppfSite B).Contains (chartScheme V.chart) :=
    V.chart.obj.left.left.property
  let A := (chartScheme V.chart).presheaf.stalk (chartPoint B S hS X V)
  let κ := separableClosure (ResidueField A) (chartGeometricPoint V).residueField
  let T := henselizationTower A κ
  let e := strictHenselizationEquivEtaleLocalRing hX V (bigEtaleSiteOfFppfSite B) hE T
  have : Module.FaithfullyFlat A T.strictHenselization :=
    IsLocalRing.IsHenselization.faithfullyFlat (L := κ)
  rw [← strictHenselizationEquivEtaleLocalRing_germ hX V (bigEtaleSiteOfFppfSite B) hE T a]
  exact ((Module.FaithfullyFlat.isSMulRegular_algebraMap_iff (A := A)
    (C := T.strictHenselization)
      ((chartScheme V.chart).presheaf.germ ⊤ (chartPoint B S hS X V) trivial a)).trans
    (RingEquiv.isSMulRegular_congr e _)).symm

/-- The germ in the étale local ring of the restriction of a global function to a chart is
unchanged by passing to a refinement of the small étale neighbourhood. -/
theorem etaleLocalRingGerm_chartValue_eq_of_hom (f : GlobalFunctions B S hS X hX)
    {x : GeometricPoint B S hS X} {U V : SmallEtaleNeighborhood x} (g : U ⟶ V) :
    etaleLocalRingGerm B S hS X x (op U) (chartValue B S hS X hX f U.chart) =
      etaleLocalRingGerm B S hS X x (op V) (chartValue B S hS X hX f V.chart) := by
  let D := SmallEtaleNeighborhood.sections (x := x) (liftedStructurePresheaf B S hS X)
  have hw := CategoryTheory.Limits.colimit.w D (op g)
  have hw' := congrArg
    (fun q ↦ q.hom (ULift.up (chartValue B S hS X hX f V.chart))) hw
  change (CategoryTheory.Limits.colimit.ι D (op U)).hom
      (ULift.up (chartValue B S hS X hX f U.chart)) =
    (CategoryTheory.Limits.colimit.ι D (op V)).hom
      (ULift.up (chartValue B S hS X hX f V.chart))
  simpa [D, SmallEtaleNeighborhood.sections, liftedStructurePresheaf, Functor.comp_map,
    RingHom.ulift_apply, chartValue_map B S hS X hX g.hom f] using hw'

/-- The germ in the étale local ring at a geometric point of the restriction of a global
function to a chart does not depend on the chosen small étale neighbourhood: any two
neighbourhoods are refined by a third. -/
theorem etaleLocalRingGerm_chartValue_eq (f : GlobalFunctions B S hS X hX)
    {x : GeometricPoint B S hS X} (U V : SmallEtaleNeighborhood x) :
    etaleLocalRingGerm B S hS X x (op U) (chartValue B S hS X hX f U.chart) =
      etaleLocalRingGerm B S hS X x (op V) (chartValue B S hS X hX f V.chart) := by
  obtain ⟨W, ⟨gU, gV⟩⟩ := SmallEtaleNeighborhood.exists_common_refinement hX U V
  exact (etaleLocalRingGerm_chartValue_eq_of_hom B S hS X hX f gU).symm.trans
    (etaleLocalRingGerm_chartValue_eq_of_hom B S hS X hX f gV)

include hX in
/-- A geometric point of `X` lifts to every surjective étale scheme chart of `X`, so such a
chart is the chart of a small étale neighbourhood of the point. -/
theorem exists_chartLift_of_isSurjective (C : SmallEtale B S hS X)
    (hC : IsSurjective B S hS C.obj.hom) (x : GeometricPoint B S hS X) :
    ∃ p : x.val.siteObject ⟶ C.obj.left,
      C.obj.hom.app (op x.val.siteObject) p = x.val.value := by
  obtain ⟨t, ht⟩ := hC x.image
  obtain ⟨y, -, hmap⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS C.obj.left) hX C.obj.hom
    (isEtale_of_presheaf_etale B S hS C.property) x t ht
  obtain ⟨xv, hxv⟩ := x
  cases hmap
  exact ⟨y.val.value, rfl⟩

/-- **Stacks 0844, conditions (1) and (2).** A global regular function on an algebraic space
is a regular section of the structure sheaf if and only if its image in the étale local ring
at every geometric point is a nonzerodivisor. -/
@[stacks 0844 "conditions (1) and (2)"]
theorem isRegularSection_iff_etaleLocalRing (f : GlobalFunctions B S hS X hX) :
    IsRegularSection (structurePresheaf B S hS X)
        (structureRingPresheaf_isSheaf B S hS X hX) f ↔
      ∀ (x : GeometricPoint B S hS X) (V : SmallEtaleNeighborhood x),
        IsSMulRegular (etaleLocalRing B S hS X x)
          (etaleLocalRingGerm B S hS X x (op V)
            (chartValue B S hS X hX f V.chart)) := by
  rw [isRegularSection_iff_forall_chart B S hS X hX f]
  constructor
  · intro h x V
    rw [isSMulRegular_etaleLocalRing_iff_germ B S hS X hX x V]
    exact isSMulRegular_germ_chartValue_of_isRegularSection B S hS X hX f V.chart
      (isRegularSection_chartFunctionSections B S hS X hX f (fun W _ ↦ h W) V.chart) _
  · intro h U
    refine isSMulRegular_of_forall_isSMulRegular_germ (etaleChartScheme B S hS U)
      (chartValue B S hS X hX f U) fun z ↦ ?_
    obtain ⟨x, p, z', hz⟩ := exists_geo_lift_at_chart_point B S hS X U z
    let N : SmallEtaleNeighborhood x := ⟨U, p.1, p.2⟩
    let _ : Field x.val.carrier := x.val.field
    let _ : Unique ((BigFppfOver.toScheme B S hS).obj x.val.siteObject) := by
      change Unique (Spec (.of x.val.carrier))
      infer_instance
    obtain rfl : z' = closedPoint (chartGeometricPoint N).residueField := Subsingleton.elim _ _
    subst z
    exact (isSMulRegular_etaleLocalRing_iff_germ B S hS X hX x N
      (chartValue B S hS X hX f U)).mp (h x N)

/-- **Stacks 0844, conditions (1) and (3).** A global regular function on an algebraic space
is a regular section of the structure sheaf if and only if its restriction to every affine
étale chart is a nonzerodivisor there. -/
@[stacks 0844 "conditions (1) and (3)"]
theorem isRegularSection_iff_affineEtale (f : GlobalFunctions B S hS X hX) :
    IsRegularSection (structurePresheaf B S hS X)
        (structureRingPresheaf_isSheaf B S hS X hX) f ↔
      ∀ U : SmallEtale B S hS X, IsAffine (etaleChartScheme B S hS U) →
        IsSMulRegular (Γ(etaleChartScheme B S hS U, ⊤))
          (chartValue B S hS X hX f U) := by
  rw [isRegularSection_iff_forall_chart B S hS X hX f]
  refine ⟨fun h U _ ↦ h U, fun h U ↦ ?_⟩
  exact isSMulRegular_of_forall_isSMulRegular_germ (etaleChartScheme B S hS U)
    (chartValue B S hS X hX f U) fun z ↦ isSMulRegular_germ_chartValue_of_isRegularSection
      B S hS X hX f U (isRegularSection_chartFunctionSections B S hS X hX f h U) z

/-- **Stacks 0844, conditions (1) and (4).** A global regular function on an algebraic space
is a regular section of the structure sheaf if and only if there is a surjective étale scheme
chart on which its restriction is a regular section. -/
@[stacks 0844 "conditions (1) and (4)"]
theorem isRegularSection_iff_exists_surjectiveChart (f : GlobalFunctions B S hS X hX) :
    IsRegularSection (structurePresheaf B S hS X)
        (structureRingPresheaf_isSheaf B S hS X hX) f ↔
      ∃ C : SmallEtale B S hS X, IsSurjective B S hS C.obj.hom ∧
        IsRegularSection (etaleChartScheme B S hS C).presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ (etaleChartScheme B S hS C).presheaf
            (forget₂ CommRingCat.{u} RingCat.{u})).mp
              (etaleChartScheme B S hS C).IsSheaf)
          (chartFunctionSections B S hS X hX f C) := by
  constructor
  · intro hreg
    obtain ⟨T, a, haSurj, haEtale⟩ := hX.exists_atlas
    exact ⟨⟨CostructuredArrow.mk a, haEtale⟩,
      (surjective_iff_surjective_pointsMap B S hS X hX T a).mp haSurj,
      isRegularSection_chartFunctionSections B S hS X hX f
        ((isRegularSection_iff_affineEtale B S hS X hX f).mp hreg) _⟩
  · rintro ⟨C, hC, hs⟩
    rw [isRegularSection_iff_etaleLocalRing B S hS X hX f]
    intro x U
    obtain ⟨p, hp⟩ := exists_chartLift_of_isSurjective B S hS X hX C hC x
    let V : SmallEtaleNeighborhood x := ⟨C, p, hp⟩
    rw [etaleLocalRingGerm_chartValue_eq B S hS X hX f U V,
      isSMulRegular_etaleLocalRing_iff_germ B S hS X hX x V]
    exact isSMulRegular_germ_chartValue_of_isRegularSection B S hS X hX f C hs _

end AlgebraicGeometry.Space

end
