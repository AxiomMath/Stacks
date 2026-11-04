module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# The locus where a meromorphic section generates an invertible module

Let `X` be a reduced algebraic space over a scheme `S` with a nonempty space of points — in
particular an integral one (Stacks 0AD4) — let `ℒ` be an invertible `𝒪_X`-module and let `s` be
a regular meromorphic section of `ℒ` (Stacks 0ENB).  The proof of Stacks 0EPS opens with the
assertion that **there is a nonempty open subspace `U ⊆ X` over which `s` corresponds to a
section of `Γ(U, ℒ)` generating `ℒ`**; this file proves it.

The open of `|X|` is the image on points of an étale chart `V` of `X` carrying a section of `ℒ`
over `V` which generates `ℒ` freely over every chart over `V` and whose image in the meromorphic
sections is `s`.

## Main definitions

* `AlgebraicGeometry.Space.GeneratesOnChart`: the meromorphic section `s` generates `ℒ` over an
  étale chart.
* `AlgebraicGeometry.Space.generatingLocus`: the set of points of `|X|` lying in the image of a
  chart over which `s` generates `ℒ`.

## Main results

* `AlgebraicGeometry.Space.exists_nonempty_chart_free_of_isInvertibleModule`: an invertible
  `𝒪_X`-module is free of rank one on an étale chart with a nonempty scheme, hence trivial over
  a nonempty open of `|X|`.
* `AlgebraicGeometry.Space.exists_chart_isUnit_eq_algebraMap_of_isUnit`: a unit of `𝒦_X` over a
  chart is, over a chart of a covering of it whose scheme is nonempty, the image of a unit
  regular function.
* `AlgebraicGeometry.Space.exists_generatesOnChart_of_isRegularMeromorphicSection`: a regular
  meromorphic section of an invertible module generates it over a chart with a nonempty scheme.
* `AlgebraicGeometry.Space.isOpen_generatingLocus` and
  `AlgebraicGeometry.Space.nonempty_generatingLocus_of_isRegularMeromorphicSection`: the
  generating locus is open and, for a regular meromorphic section, nonempty.
* `AlgebraicGeometry.Space.exists_isOpen_nonempty_generatesOnChart`: **the input of the proof of
  Stacks 0EPS** — a nonempty open of `|X|` each of whose points lies in the image of a chart
  over which `s` generates `ℒ`.

## Implementation notes

The open subspace of the source appears here as a set of points of `|X|` together with the étale
chart realizing it.  An open subspace of an algebraic space is not a scheme, so "`s` corresponds
to a section of `Γ(U, ℒ)` which generates `ℒ`" cannot be read on `U` itself; it is read,
étale-locally, on a chart whose image on points is `U`, which is also the form in which
`AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero` consumes such an open.  The
generator is carried as the compatible family of its restrictions to all charts over `V`, rather
than as a single section, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionPullbackRegular.lean`: the restriction of
a module element has for its type the restriction-of-scalars spelling, at which the module
instances are not registered, so freeness of a restriction cannot be stated at face value.

The argument is the composite of three steps.
`AlgebraicGeometry.Space.unitPresentationSieve_mem` makes `s`, over a covering sieve of every
chart, a *unit* multiple `c ⊗ e` of a free generator of `ℒ`; a member of that sieve whose scheme
is nonempty exists because a covering sieve is jointly surjective on points
(`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`).  The unit `c` of `𝒦_X`
is then brought into `𝒪_X`: it is a fraction `b/d` of regular functions over a covering sieve
(`AlgebraicGeometry.Space.imageSieve_toSheafify_localizationPresheaf_mem`), where `b` is regular
because `c` is a unit and `d` is, and on the non-vanishing locus of `b · d` both `b` and `d`
become units, so `c` is the image of the unit `b · d⁻¹`.  That locus is nonempty exactly because
the chart is a *reduced* scheme, which is where reducedness of `X` enters
(`AlgebraicGeometry.nonempty_basicOpen_of_ne_zero`).  Finally `c ⊗ e` becomes `1 ⊗ (b · d⁻¹) e`,
and a unit multiple of a free generator is a free generator.

Of the source's hypotheses only reducedness and nonemptiness of `|X|` are used: irreducibility
and the local Noetherian condition are not, so the statements below take the two conditions they
need rather than `AlgebraicGeometry.Space.IsIntegralSpace`, and the integral case is recorded
separately.

`Stacks.SheafOfModules.generatingLocus` of
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartSaturation.lean` is a namesake for a
different object: the locus where a section of an invertible module *on a scheme* generates it,
cut out by a germ condition on the Zariski stalks.  Nothing relates the two, the section there
being a section of the module itself rather than a meromorphic one.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two auxiliary facts about charts -/

section Chart

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A member of a covering sieve of an étale chart whose own scheme is nonempty, obtained from a
point of the scheme of the chart: a covering sieve is jointly surjective on points. -/
theorem exists_mem_nonempty_of_mem_topology (W : SmallEtale B S hS F) {T : Sieve W}
    (hT : T ∈ SmallEtale.topology B S hS F W) (x : chartScheme W) :
    ∃ (W' : SmallEtale B S hS F) (k : W' ⟶ W), T k ∧ Nonempty (chartScheme W') := by
  obtain ⟨W', k, hk, z, -⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS F T).1 hT x
  exact ⟨W', k, hk, ⟨z⟩⟩

/-- A regular section of `𝒪_F` over an étale chart whose scheme has a point is nonzero: a
regular section is a nonzerodivisor, so a zero one forces `1 = 0` and the chart scheme to be
empty. -/
theorem ne_zero_of_isRegularSection (W : SmallEtale B S hS F)
    (b : (structurePresheaf B S hS F).obj (op W)) (hb : IsRegularSection B S hS F W b)
    (x : chartScheme W) : b ≠ 0 := by
  intro hb0
  have h1 : (1 : Γ(chartScheme W, ⊤)) = 0 :=
    (mem_nonZeroDivisors_iff.mp (regularSections_le_nonZeroDivisors B S hS F W hb)).2 1
      (by rw [hb0, mul_zero])
  have hbot : (⊤ : (chartScheme W).Opens) = ⊥ := by
    rw [← Scheme.basicOpen_one (X := chartScheme W) (U := ⊤), h1, Scheme.basicOpen_zero]
  have hx : x ∈ (⊥ : (chartScheme W).Opens) :=
    hbot ▸ (show x ∈ (⊤ : (chartScheme W).Opens) from trivial)
  simp at hx

end Chart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-! ### An invertible module is free of rank one on a nonempty chart -/

include hX in
/-- **An invertible `𝒪_X`-module is free of rank one on an étale chart with a nonempty scheme**,
hence trivial over a nonempty open of `|X|`.

A trivializing cover of a chart which is surjective on points has a member whose scheme is
nonempty, because a covering sieve is jointly surjective on points.  The generator is given as
the compatible family of its restrictions to the charts over that member. -/
theorem exists_nonempty_chart_free_of_isInvertibleModule
    (hne : Nonempty (points B S hS X)) (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L) :
    ∃ (V : SmallEtale B S hS X)
      (e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W)),
      Nonempty (chartScheme V) ∧
      (∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
        (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
      ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
        Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k := by
  obtain ⟨V₀, hV₀⟩ := exists_isSurjective_chart B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)
  obtain ⟨x₀, -⟩ := surjective_chartSchemeToPoints B S hS X V₀ hV₀ hne.some
  obtain ⟨I, V, a, hcov, hgen⟩ := exists_generator_cover_smul_of_isInvertible B S hS
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) V₀
  obtain ⟨W, k, hk, hWne⟩ := exists_mem_nonempty_of_mem_topology B S hS X V₀ hcov x₀
  obtain ⟨Z, h, g, hg, -⟩ := hk
  obtain ⟨i⟩ := hg
  obtain ⟨e, hecompat, hebij⟩ := hgen i
  refine ⟨W, fun Z' j ↦ e Z' (j ≫ h), hWne, fun W₁ W₂ k₁ g₁ ↦ ?_,
    fun W₁ k₁ ↦ hebij W₁ (k₁ ≫ h)⟩
  exact (hecompat W₁ W₂ (k₁ ≫ h) g₁).trans (congrArg (e W₂) (Category.assoc g₁ k₁ h).symm)

/-! ### A unit meromorphic function is locally the image of a unit regular function -/

include hX in
/-- **A unit of `𝒦_X` over a chart is, over a chart of a covering of it, the image of a unit
regular function.**

Over a member of the covering sieve of
`AlgebraicGeometry.Space.imageSieve_toSheafify_localizationPresheaf_mem` the unit `c` is a
fraction `b/d` with `d` a regular function; then `b = c · d` is a unit of `𝒦_X`, hence `b` is a
regular function too, and so is `b · d`.  On the non-vanishing locus of `b · d` — a nonempty
open of the chart, because the chart of a reduced algebraic space is a reduced scheme — both `b`
and `d` restrict to units of `𝒪_X`, and `c` is the image of `b · d⁻¹`. -/
theorem exists_chart_isUnit_eq_algebraMap_of_isUnit
    (hred : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsReduced Y))
    (W : SmallEtale B S hS X)
    (c : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.obj (op W))
    (hc : IsUnit c)
    (x : chartScheme W) :
    ∃ (W' : SmallEtale B S hS X) (k : W' ⟶ W) (y : chartRing B S hS X hX W'),
      Nonempty (chartScheme W') ∧ IsUnit y ∧
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X hX).O).obj.map k.op).hom c =
        algebraMap (chartRing B S hS X hX W')
          ((meromorphicChartSheaf B S hS X hX).obj.obj (op W')) y := by
  obtain ⟨W₁, k₁, hk₁, ⟨x₁⟩⟩ := exists_mem_nonempty_of_mem_topology B S hS X W
    (imageSieve_toSheafify_localizationPresheaf_mem B S hS X hX W c) x
  obtain ⟨z, hz⟩ := hk₁
  have hz' : ((toSheafify (SmallEtale.topology B S hS X)
        (regularSectionsSubpresheaf B S hS X hX).localizationPresheaf).app (op W₁)).hom z =
      ((meromorphicFunctionSheaf B S hS X hX).obj.map k₁.op).hom c := hz
  obtain ⟨b, d, hbd⟩ := IsLocalization.exists_mk'_eq (M := regularSections B S hS X W₁) z
  -- the fraction identity `b = c · d` in `𝒦_X(W₁)`
  have hkey : ((toMeromorphicFunctionSheaf B S hS X hX).hom.app (op W₁)).hom b =
      ((meromorphicFunctionSheaf B S hS X hX).obj.map k₁.op).hom c *
        ((toMeromorphicFunctionSheaf B S hS X hX).hom.app (op W₁)).hom
          (d : (structurePresheaf B S hS X).obj (op W₁)) := by
    rw [toMeromorphicFunctionSheaf_app_apply_eq_toSheafify,
      toMeromorphicFunctionSheaf_app_apply_eq_toSheafify, ← hz', ← hbd]
    have hspec := IsLocalization.mk'_spec
      (ToType ((regularSectionsSubpresheaf B S hS X hX).localizationPresheaf.obj (op W₁))) b d
    refine Eq.trans (congrArg (fun w ↦ ((toSheafify (SmallEtale.topology B S hS X)
        (regularSectionsSubpresheaf B S hS X hX).localizationPresheaf).app (op W₁)).hom w)
      hspec.symm) ?_
    exact map_mul _ _ _
  have hdunit : IsUnit (((toMeromorphicFunctionSheaf B S hS X hX).hom.app (op W₁)).hom
      (d : (structurePresheaf B S hS X).obj (op W₁))) :=
    isUnit_toMeromorphicFunctionSheaf B S hS X hX W₁ _ d.2
  have hbunit : IsUnit (((toMeromorphicFunctionSheaf B S hS X hX).hom.app (op W₁)).hom b) := by
    rw [hkey]
    exact (hc.map ((meromorphicFunctionSheaf B S hS X hX).obj.map k₁.op).hom).mul hdunit
  -- naturality of `𝒪_X → 𝒦_X`
  have hnat : ∀ {Z : SmallEtale B S hS X} (j : Z ⟶ W₁)
      (a : (structurePresheaf B S hS X).obj (op W₁)),
      ((toMeromorphicFunctionSheaf B S hS X hX).hom.app (op Z)).hom
          ((structurePresheaf B S hS X).map j.op a) =
        ((meromorphicFunctionSheaf B S hS X hX).obj.map j.op).hom
          (((toMeromorphicFunctionSheaf B S hS X hX).hom.app (op W₁)).hom a) :=
    fun j a ↦ NatTrans.naturality_apply (toMeromorphicFunctionSheaf B S hS X hX).hom j.op a
  -- hence `b` is a regular function, and so is `b · d`
  have hbreg : IsRegularSection B S hS X W₁ b := by
    refine isRegularSection_of_injective_mul_toMeromorphicFunctionSheaf B S hS X hX W₁ b ?_
    intro Z j
    rw [hnat j b]
    exact (hbunit.map _).mul_left_injective
  -- the non-vanishing locus of `b · d` is a nonempty open of the chart
  have _ : IsReduced (chartScheme W₁) :=
    isReduced_chartScheme B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS) hred W₁
  set g : (structureSheaf B S hS X hX).obj.obj (op W₁) :=
    (b : (structureSheaf B S hS X hX).obj.obj (op W₁)) *
      (d : (structurePresheaf B S hS X).obj (op W₁)) with hg
  have hgreg : IsRegularSection B S hS X W₁ g :=
    isRegularSection_mul B S hS X W₁ b _ hbreg d.2
  obtain ⟨pt, hpt⟩ := nonempty_basicOpen_of_ne_zero (chartScheme W₁)
    (ne_zero_of_isRegularSection B S hS X W₁ g hgreg x₁)
  set O : (chartScheme W₁).Opens := (chartScheme W₁).basicOpen g with hO
  set k' : openChart B S hS X W₁ O ⟶ W₁ := openChartInclusion B S hS X W₁ O with hk'
  have hgu : IsUnit (((structureSheaf B S hS X hX).obj.map k'.op).hom g) :=
    isUnit_chartRestrict_basicOpenChart B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS) W₁ g
  have hsplit : ((structureSheaf B S hS X hX).obj.map k'.op).hom g =
      ((structureSheaf B S hS X hX).obj.map k'.op).hom
          (b : (structureSheaf B S hS X hX).obj.obj (op W₁)) *
        ((structureSheaf B S hS X hX).obj.map k'.op).hom
          (d : (structurePresheaf B S hS X).obj (op W₁)) :=
    map_mul _ _ _
  rw [hsplit] at hgu
  have hbu : IsUnit (((structureSheaf B S hS X hX).obj.map k'.op).hom
      (b : (structureSheaf B S hS X hX).obj.obj (op W₁))) := isUnit_of_mul_isUnit_left hgu
  have hdu : IsUnit (((structureSheaf B S hS X hX).obj.map k'.op).hom
      (d : (structurePresheaf B S hS X).obj (op W₁))) := isUnit_of_mul_isUnit_right hgu
  refine ⟨openChart B S hS X W₁ O, k' ≫ k₁,
    (((structureSheaf B S hS X hX).obj.map k'.op).hom
        (b : (structureSheaf B S hS X hX).obj.obj (op W₁)) * ↑hdu.unit⁻¹ :
      (structureSheaf B S hS X hX).obj.obj (op (openChart B S hS X W₁ O))),
    ⟨(⟨pt, hpt⟩ : (O : Type u))⟩, hbu.mul (Units.isUnit hdu.unit⁻¹), ?_⟩
  -- the restricted fraction identity, and cancellation of the unit `d`
  have hcomp : ((meromorphicFunctionSheaf B S hS X hX).obj.map k'.op).hom
        (((meromorphicFunctionSheaf B S hS X hX).obj.map k₁.op).hom c) =
      ((meromorphicFunctionSheaf B S hS X hX).obj.map (k' ≫ k₁).op).hom c := by
    rw [op_comp, Functor.map_comp]
    rfl
  have hres : ((toMeromorphicFunctionSheaf B S hS X hX).hom.app
          (op (openChart B S hS X W₁ O))).hom
        (((structureSheaf B S hS X hX).obj.map k'.op).hom
          (b : (structureSheaf B S hS X hX).obj.obj (op W₁))) =
      ((meromorphicFunctionSheaf B S hS X hX).obj.map (k' ≫ k₁).op).hom c *
        ((toMeromorphicFunctionSheaf B S hS X hX).hom.app
            (op (openChart B S hS X W₁ O))).hom
          (((structureSheaf B S hS X hX).obj.map k'.op).hom
            (d : (structurePresheaf B S hS X).obj (op W₁))) := by
    erw [hnat k' b, hnat k' d]
    rw [hkey, map_mul, hcomp]
  have hd1 : ((structureSheaf B S hS X hX).obj.map k'.op).hom
        (d : (structurePresheaf B S hS X).obj (op W₁)) *
      (↑hdu.unit⁻¹ :
        (structureSheaf B S hS X hX).obj.obj (op (openChart B S hS X W₁ O))) = 1 :=
    (congrArg (fun w : (structureSheaf B S hS X hX).obj.obj
        (op (openChart B S hS X W₁ O)) ↦
      w * (↑hdu.unit⁻¹ : (structureSheaf B S hS X hX).obj.obj
        (op (openChart B S hS X W₁ O)))) hdu.unit_spec.symm).trans hdu.unit.mul_inv
  show ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS X hX).O).obj.map (k' ≫ k₁).op).hom c =
      ((toMeromorphicFunctionSheaf B S hS X hX).hom.app
          (op (openChart B S hS X W₁ O))).hom
        ((((structureSheaf B S hS X hX).obj.map k'.op).hom
            (b : (structureSheaf B S hS X hX).obj.obj (op W₁)) * ↑hdu.unit⁻¹ :
          (structureSheaf B S hS X hX).obj.obj (op (openChart B S hS X W₁ O))))
  rw [map_mul, hres, mul_assoc, ← map_mul, hd1, map_one, mul_one]
  rfl

/-! ### The generating locus -/

variable (L : Modules.{u, u} B S hS X hX)

/-- A meromorphic section `s` of an `𝒪_X`-module `L` **generates `L` over the étale chart `V`**
when there is a section of `L` over `V`, carried as the compatible family `e` of its restrictions
to the charts over `V`, which generates `L` freely over each of them and whose image in the
meromorphic sections is `s`. -/
def GeneratesOnChart (s : MeromorphicSection.{u, u} B S hS X hX L)
    (V : SmallEtale B S hS X) : Prop :=
  ∃ e : (W : SmallEtale B S hS X) → (W ⟶ V) → L.val.obj (op W),
    (∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
        (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
      (∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
        Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k) ∧
      s.eval (op V) = toMeromorphicSectionSheaf B S hS X hX L V
        ((1 : (Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS X hX).O).obj.obj (op V)) ⊗ₜ[
          chartRing B S hS X hX V] e V (𝟙 V) :
          (meromorphicSectionModule B S hS X hX L).obj (op V))

/-- The set of points of `|X|` at which a meromorphic section `s` of `L` **generates `L`**: those
lying in the image on points of an étale chart over which `s` generates `L`. -/
def generatingLocus (s : MeromorphicSection.{u, u} B S hS X hX L) :
    Set (points B S hS X) :=
  {x | ∃ V : SmallEtale B S hS X,
    x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom) ∧
      GeneratesOnChart B S hS hX L s V}

include hX in
/-- The generating locus of a meromorphic section is open in `|X|`: around each of its points it
contains the image on points of an étale morphism of algebraic spaces into `X`, which is open by
Stacks 03IR. -/
theorem isOpen_generatingLocus (s : MeromorphicSection.{u, u} B S hS X hX L) :
    IsOpen (generatingLocus B S hS hX L s) := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro x ⟨V, hxV, hgen⟩
  exact ⟨Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom),
    fun y hy ↦ ⟨V, hy, hgen⟩,
    isOpen_range_pointsMap_of_isEtale B S hS V.obj.hom
      (isAlgebraicSpace_yoneda B S hS _) hX
      ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).mpr V.property), hxV⟩

include hX in
/-- **A regular meromorphic section of an invertible `𝒪_X`-module generates it over an étale
chart with a nonempty scheme**, for `X` reduced with a nonempty space of points.

This is the open subspace the proof of Stacks 0EPS opens with.  A covering sieve of a surjective
chart over which `s` is a unit multiple `c ⊗ e` of a free generator
(`AlgebraicGeometry.Space.unitPresentationSieve_mem`) has a member `W` with a nonempty scheme;
over a chart of a covering of `W` the unit `c` becomes the image of a unit regular function `y`
(`AlgebraicGeometry.Space.exists_chart_isUnit_eq_algebraMap_of_isUnit`), and there
`c ⊗ e = 1 ⊗ (y · e)` with `y · e` again a free generator. -/
theorem exists_generatesOnChart_of_isRegularMeromorphicSection
    (hred : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsReduced Y))
    (hne : Nonempty (points B S hS X))
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s) :
    ∃ V : SmallEtale B S hS X, Nonempty (chartScheme V) ∧
      GeneratesOnChart B S hS hX L s V := by
  obtain ⟨V₀, hV₀⟩ := exists_isSurjective_chart B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)
  obtain ⟨x₀, -⟩ := surjective_chartSchemeToPoints B S hS X V₀ hV₀ hne.some
  obtain ⟨W, k₀, hk₀, ⟨xW⟩⟩ := exists_mem_nonempty_of_mem_topology B S hS X V₀
    (unitPresentationSieve_mem B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS) L s
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) hs V₀) x₀
  obtain ⟨e, c, hecompat, hebij, hcunit, hpres⟩ := hk₀
  obtain ⟨W', k, y, hW'ne, hyu, hyc⟩ :=
    exists_chart_isUnit_eq_algebraMap_of_isUnit B S hS hX hred W c hcunit xW
  refine ⟨W', hW'ne, fun Z j ↦ chartRestrict (hF := hX) j y • e Z (j ≫ k), ?_, ?_, ?_⟩
  · intro Z Z' j g
    show (L.val.map g.op).hom (chartRestrict (hF := hX) j y • e Z (j ≫ k)) =
      chartRestrict (hF := hX) (g ≫ j) y • e Z' ((g ≫ j) ≫ k)
    refine Eq.trans
      (L.val.map_smul g.op (chartRestrict (hF := hX) j y) (e Z (j ≫ k))) ?_
    rw [hecompat Z Z' (j ≫ k) g, Category.assoc]
    exact congrArg (fun v : chartRing B S hS X hX Z' ↦ v • e Z' (g ≫ j ≫ k))
      (DFunLike.congr_fun (chartRestrict_comp (hF := hX) j g) y).symm
  · intro Z j
    show Function.Bijective fun r : chartRing B S hS X hX Z ↦
      r • (chartRestrict (hF := hX) j y • e Z (j ≫ k))
    have huZ : IsUnit (chartRestrict (hF := hX) j y) := hyu.map (chartRestrict (hF := hX) j)
    have hmul : Function.Bijective
        fun r : chartRing B S hS X hX Z ↦ r * chartRestrict (hF := hX) j y := by
      refine ⟨huZ.mul_left_injective, fun w ↦ ⟨w * ↑huZ.unit⁻¹, ?_⟩⟩
      show w * ↑huZ.unit⁻¹ * chartRestrict (hF := hX) j y = w
      have hinv : (↑huZ.unit⁻¹ : chartRing B S hS X hX Z) *
          chartRestrict (hF := hX) j y = 1 :=
        (congrArg (fun v : chartRing B S hS X hX Z ↦
          (↑huZ.unit⁻¹ : chartRing B S hS X hX Z) * v) huZ.unit_spec.symm).trans
          huZ.unit.inv_mul
      rw [mul_assoc, hinv, mul_one]
    have heq : (fun r : chartRing B S hS X hX Z ↦
          r • (chartRestrict (hF := hX) j y • e Z (j ≫ k))) =
        (fun w : chartRing B S hS X hX Z ↦ w • e Z (j ≫ k)) ∘
          fun r : chartRing B S hS X hX Z ↦ r * chartRestrict (hF := hX) j y :=
      funext fun r ↦ smul_smul r (chartRestrict (hF := hX) j y) (e Z (j ≫ k))
    rw [heq]
    exact (hebij Z (j ≫ k)).comp hmul
  · show s.eval (op W') = toMeromorphicSectionSheaf B S hS X hX L W'
      ((1 : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.obj (op W')) ⊗ₜ[
        chartRing B S hS X hX W'] (chartRestrict (hF := hX) (𝟙 W') y • e W' (𝟙 W' ≫ k)) :
        (meromorphicSectionModule B S hS X hX L).obj (op W'))
    have hidr : chartRestrict (hF := hX) (𝟙 W') y = y :=
      DFunLike.congr_fun (chartRestrict_id (hF := hX) W') y
    rw [hidr, Category.id_comp,
      eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS X hX L s W e hecompat c hpres W' k,
      hyc]
    refine congrArg (toMeromorphicSectionSheaf B S hS X hX L W') ?_
    refine Eq.trans (congrArg
      (fun w : (Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X hX).O).obj.obj (op W') ↦
        (w ⊗ₜ[chartRing B S hS X hX W'] e W' k :
          (meromorphicSectionModule B S hS X hX L).obj (op W')))
      (mul_one (algebraMap (chartRing B S hS X hX W')
        ((meromorphicChartSheaf B S hS X hX).obj.obj (op W')) y)).symm)
      (meromorphicSectionModule_tmul_smul B S hS X hX L W' y 1 (e W' k)).symm

include hX in
/-- The generating locus of a regular meromorphic section of an invertible `𝒪_X`-module is
nonempty, for `X` reduced with a nonempty space of points. -/
theorem nonempty_generatingLocus_of_isRegularMeromorphicSection
    (hred : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsReduced Y))
    (hne : Nonempty (points B S hS X))
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s) :
    (generatingLocus B S hS hX L s).Nonempty := by
  obtain ⟨V, ⟨xV⟩, hgen⟩ :=
    exists_generatesOnChart_of_isRegularMeromorphicSection B S hS hX L hred hne hL s hs
  obtain ⟨p, -⟩ :=
    surjective_pointsToScheme B S hS ((SmallEtale.toOver B S hS X).obj V) xV
  exact ⟨_, V, ⟨p, rfl⟩, hgen⟩

include hX in
/-- **The input of the proof of Stacks 0EPS.**  For `X` reduced with a nonempty space of points,
`ℒ` an invertible `𝒪_X`-module and `s` a regular meromorphic section of `ℒ`, there is a nonempty
open `U ⊆ |X|` each of whose points lies in the image of an étale chart over which `s` generates
`ℒ`. -/
theorem exists_isOpen_nonempty_generatesOnChart
    (hred : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsReduced Y))
    (hne : Nonempty (points B S hS X))
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s) :
    ∃ U : Set (points B S hS X), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ V : SmallEtale B S hS X,
        x ∈ Set.range (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom) ∧
          GeneratesOnChart B S hS hX L s V :=
  ⟨generatingLocus B S hS hX L s, isOpen_generatingLocus B S hS hX L s,
    nonempty_generatingLocus_of_isRegularMeromorphicSection B S hS hX L hred hne hL s hs,
    fun _ hx ↦ hx⟩

include hX in
/-- **The input of the proof of Stacks 0EPS on an integral algebraic space.**  An integral
algebraic space is reduced and has an irreducible, in particular nonempty, space of points
(Stacks 0AD4), which is all that
`AlgebraicGeometry.Space.exists_isOpen_nonempty_generatesOnChart` asks for. -/
theorem exists_isOpen_nonempty_generatesOnChart_of_isIntegralSpace
    (hInt : IsIntegralSpace B S hS X)
    (hL : IsInvertibleModule (⟨X, hX⟩ : AlgebraicSpaces B S hS) L)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X hX L s) :
    ∃ U : Set (points B S hS X), IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∃ V : SmallEtale B S hS X,
        x ∈ Set.range (pointsMap B S hS
            (yoneda.obj ((SmallEtale.toOver B S hS X).obj V)) V.obj.hom) ∧
          GeneratesOnChart B S hS hX L s V :=
  exists_isOpen_nonempty_generatesOnChart B S hS hX L
    hInt.hasEtaleLocalProperty_isReduced hInt.irreducibleSpace.toNonempty hL s hs

end AlgebraicGeometry.Space

end
