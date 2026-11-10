module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkGermVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkOrdinary
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAtPointBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkGerm
import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPointEquiv
import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformLocalGenerators

/-!
# Sections of a flat module supported on the inverse image of a Cartier divisor

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`D ⊆ X` be a closed subspace whose inverse images are effective Cartier divisors on the étale
scheme charts of `X`.  If a quasi-coherent `𝒪_Y`-module `G` is flat over `X` at every geometric
point of `Y` lying over `|D|`, then `G` has no nonzero local section supported on `|f^{-1}D|`.

Applied to the projection `X ×_A A' ⟶ A'` of a blowup `b : A' ⟶ A` of `A` in `Z` and to the
pullback `pr_X^*F` of a quasi-coherent `𝒪_X`-module `F`, this is the vanishing of the submodule
of supported sections that **Stacks 0865, part (2)** needs, and it is what makes
`AlgebraicGeometry.Space.isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint`
carry the source's hypotheses and nothing else.

This is the module counterpart of the structure-sheaf statement
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_preimage_of_isFlatAt` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAtPointBaseChange.lean`, which is what part (1) of
Stacks 0865 needs, and it is proved by the same route.

## Main results

* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_preimage_of_isFlatOverAtGeometricPoint`:
  the vanishing of the sections of `G` supported on `|f^{-1}D|`.
* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback_strictTransform`: the
  pullback `pr_X^*F` is flat over `A'` above the exceptional divisor of a blowup.
* `supportedSections_exceptionalPreimage_ι_eq_zero_of_isFlatOverAtGeometricPoint` (in the
  namespace `AlgebraicGeometry.Space`): the vanishing at the blowup, for the pullback of a
  quasi-coherent module to the ambient base change — the input of Stacks 0865, part (2).

## Implementation notes

**The route is native to algebraic spaces**, as it is for part (1).  The source proves
Stacks 0865 by reducing to the case of schemes, Stacks 080F, by étale localization, Stacks 0863
parts (2) and (3); what replaces that here is the chart-level computation of the supported
sections as an ideal-power torsion, Stacks 0859 (2) in the form
`AlgebraicGeometry.Space.mem_supportedSectionsSubmodule_iff_mem_primaryComponent`, which is
available for the module `G` because `G` is quasi-coherent — the hypothesis the source carries
on `F` — and killing that torsion is then commutative algebra in one local ring of one chart
scheme.

Where part (1) reads flatness of a morphism at a point of a chart scheme and kills the torsion
in the Zariski stalk of the structure sheaf, this reads flatness of `G` over `X` at a geometric
point, condition (2) of Stacks 05VU, and kills the torsion in the Zariski stalk
`AlgebraicGeometry.Space.chartZariskiModuleStalk` of the restriction of `G` to the chart.  The
two are matched by
`AlgebraicGeometry.Space.flat_chartZariskiModuleStalk_of_isFlatOverAtGeometricPoint` below,
which composes the chart criterion of Stacks 05VU,
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint`, with the
reading of condition (1) on the Zariski stalk,
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_flat_chartZariskiModuleStalk`.

A germ of `G` on the chart is `AlgebraicGeometry.Space.chartZariskiSectionGermOfVanishing`, and
what turns the vanishing of a germ back into a statement about the section is
`AlgebraicGeometry.Space.exists_restrict_eq_zero_of_chartZariskiSectionGermOfVanishing_eq_zero`:
the section dies on a Zariski open of the chart, which is again an object of the small étale
site, so it exhibits the point as a zero image and no separation argument over the whole chart
is needed.

Most imports are not `public`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAtPointBaseChange.lean`: re-exporting the flat-locus
and regular-section theories would put `AlgebraicGeometry.IsRegular` of
`StacksFrontier/AlgebraicGeometry/Properties/Regular.lean` into the scope of the modules above
this one, where `IsRegular` means the predicate on a ring element.

## References

* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0865](https://stacks.math.columbia.edu/tag/0865)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Ideal-power torsion of a module at a principal ideal -/

/-- Membership in the primary component of a principal ideal, for a module: being annihilated
by a power of the generator. -/
private theorem mem_primaryComponent_span_singleton_smul_iff {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (a : R) (s : M) :
    s ∈ Ideal.primaryComponent M (Ideal.span {a}) ↔ ∃ n : ℕ, a ^ n • s = 0 := by
  simp only [Ideal.primaryComponent_mem, Ideal.span_singleton_pow,
    Submodule.torsionBySet_ideal_span_singleton_eq, Submodule.mem_torsionBy_iff]

/-- **An element of a module killed by a power of the pullback of a nonzerodivisor vanishes,
if the module is flat where that pullback is not invertible.**  Let `h : V₀ ⟶ U₀` be a morphism
of schemes with `U₀` affine, let `a` be a nonzerodivisor on `U₀` and let `M` be a module over
the local ring of `V₀` at a point `y`.  An element of `M` annihilated by a power of the germ of
the pullback of `a` is zero: if that germ is a unit this is immediate, and otherwise flatness of
`M` over the local ring of `U₀` carries the nonzerodivisor `a` across.

This is the module form of
`AlgebraicGeometry.Space.germ_eq_zero_of_pow_mul_eq_zero_of_isFlatAt`, whose structure-sheaf
case is what part (1) of Stacks 0865 uses. -/
private theorem eq_zero_of_pow_smul_eq_zero_of_flat {V₀ U₀ : Scheme.{u}} [IsAffine U₀]
    (h : V₀ ⟶ U₀) {a : Γ(U₀, ⊤)} (ha : IsSMulRegular Γ(U₀, ⊤) a) (y : V₀)
    (M : Type*) [AddCommGroup M] [Module ↥(V₀.presheaf.stalk y) M] (z : M) (n : ℕ)
    (hz : V₀.presheaf.germ ⊤ y trivial (h.appTop a ^ n) • z = 0)
    (hflat : ¬ IsUnit (V₀.presheaf.germ ⊤ y trivial (h.appTop a)) →
      letI : Module ↥(U₀.presheaf.stalk (h.base y)) M :=
        Module.compHom _ (h.stalkMap y).hom
      Module.Flat ↥(U₀.presheaf.stalk (h.base y)) M) :
    z = 0 := by
  rw [map_pow] at hz
  by_cases hu : IsUnit (V₀.presheaf.germ ⊤ y trivial (h.appTop a))
  · exact ((hu.pow n).smul_eq_zero).mp hz
  · let : Module ↥(U₀.presheaf.stalk (h.base y)) M := Module.compHom _ (h.stalkMap y).hom
    have : Module.Flat ↥(U₀.presheaf.stalk (h.base y)) M := hflat hu
    set aR : U₀.presheaf.stalk (h.base y) :=
      U₀.presheaf.germ ⊤ (h.base y) trivial a with haR
    have hregR : IsSMulRegular (U₀.presheaf.stalk (h.base y)) aR :=
      isSMulRegular_germ_of_isAffineOpen U₀ (isAffineOpen_top U₀) ha ⟨h.base y, trivial⟩
    have hnzd : ∀ {R : Type u} [CommRing R] {c : R},
        IsSMulRegular R c → c ∈ nonZeroDivisors R := fun hc =>
      mem_nonZeroDivisors_iff.mpr
        ⟨fun x hx => hc (by simpa [smul_eq_mul] using hx),
          fun x hx => hc (by simpa [smul_eq_mul, mul_comm] using hx)⟩
    have hscalar : V₀.presheaf.germ ⊤ y trivial (h.appTop a) = (h.stalkMap y).hom aR := by
      rw [haR, Scheme.Hom.germ_stalkMap_apply h ⊤ y trivial a]
      rfl
    have hsmulR : ∀ x : M, aR ^ n • x = (h.stalkMap y).hom (aR ^ n) • x := fun _ => rfl
    have key : aR ^ n • z = aR ^ n • (0 : M) := by
      rwa [smul_zero, hsmulR, map_pow, ← hscalar]
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (pow_mem (hnzd hregR) n) key

/-! ### Flatness at a geometric point read on the Zariski stalk of a chart -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flatness over the target at a geometric point is flatness of the Zariski stalk of the
chart restriction over the local ring of a chart of the target.**  This composes the chart
criterion of Stacks 05VU with the reading of its condition (1) on the Zariski stalk of
Stacks 05VP. -/
private theorem flat_chartZariskiModuleStalk_of_isFlatOverAtGeometricPoint
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (G : Modules.{u, u} B S hS Y.1 Y.2)
    [G.IsQuasicoherentOnSite] {ybar : GeometricPoint B S hS Y.1}
    (N : SmallEtaleNeighborhood ybar) (W : SmallEtale B S hS X.1)
    (g : (SmallEtale.toOver B S hS Y.1).obj N.chart ⟶ (SmallEtale.toOver B S hS X.1).obj W)
    (hcomm : N.chart.obj.hom ≫ f.hom = yoneda.map g ≫ W.obj.hom)
    (hF : IsFlatOverAtGeometricPoint B S hS f G ybar) :
    letI : Module ↥((chartScheme W).presheaf.stalk
        (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS Y.1 N)))
        ↥(chartZariskiModuleStalk B S hS Y.1 Y.2 N G) :=
      Module.compHom _ (((BigFppfOver.toScheme B S hS).map g).stalkMap
        (chartPoint B S hS Y.1 N)).hom
    Module.Flat ↥((chartScheme W).presheaf.stalk
        (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS Y.1 N)))
      ↥(chartZariskiModuleStalk B S hS Y.1 Y.2 N G) :=
  (isFlatOverAtOnChartDiagram_iff_flat_chartZariskiModuleStalk B S hS Y.2 G N W g hcomm).mp
    ((isFlatOverAtOnChartDiagram_iff_isFlatOverAtGeometricPoint B S hS f G N W g hcomm).mpr hF)

/-! ### No sections supported on the inverse image -/

/-- **A quasi-coherent module flat over the target above a Cartier divisor has no sections
supported on its inverse image.**

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let `D ⊆ X` be a closed subspace
whose inverse image is an effective Cartier divisor on every étale scheme chart of `X`,
condition (3) of Stacks 083C.  If the quasi-coherent `𝒪_Y`-module `G` is flat over `X` at every
geometric point of `Y` lying over `|D|`, then every local section of `G` whose support maps into
the point set of `f^{-1}D` is zero.

This is the algebraic-spaces form of the vanishing that the proof of Stacks 080F, part (2),
establishes for schemes.  Through every point of the chart carrying the section there is an
affine chart `T` over an affine chart `U` of `X` on which `D` is cut out by a nonzerodivisor
`a`, by `AlgebraicGeometry.Space.exists_affine_chartPair_isRegular_span_definingIdealAt`; on it
the section is annihilated by a power of the pullback of `a`, because Stacks 0859 (2) in the
form `AlgebraicGeometry.Space.mem_supportedSectionsSubmodule_iff_mem_primaryComponent`
identifies the supported sections with that ideal-power torsion, `G` being quasi-coherent; and
the germ of that section in the Zariski stalk of the restriction of `G` to `T` therefore
vanishes — where the pullback of `a` is invertible because its germ is a unit, and where it is
not because the point then lies over `|D|`, so `G` is flat over `X` at a geometric point above
it and the nonzerodivisor `a` acts injectively on the stalk.  A germ that vanishes makes the
section die on a Zariski open of `T`, which is again an étale chart, and that exhibits the
point as a zero image; a section all of whose points are zero images vanishes.

The conclusion is `AlgebraicGeometry.Space.HasNoSectionsSupportedIn` of
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformUniversalProperty.lean`, spelled out: that
module cannot be imported here, since it lies above
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean`, which consumes this
file. -/
theorem hasNoSectionsSupportedIn_preimage_of_isFlatOverAtGeometricPoint
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (D : ClosedSubspaces B S hS X.1)
    (hD : HasEffectiveCartierEtalePullbacks B S hS X D)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite)
    (hflat : ∀ ybar : GeometricPoint B S hS Y.1,
      pointsMap B S hS Y.1 f.hom ybar.image ∈
          Set.range (pointsMap B S hS D.1.toFunctor D.1.ι) →
        IsFlatOverAtGeometricPoint B S hS f G ybar) :
    ∀ (W₀ : SmallEtale B S hS Y.1) (s : G.val.obj (op W₀)),
      SectionSupportedIn B S hS Y.1 Y.2
        (Set.range (pointsMap B S hS
          (⟨D.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ :
            ClosedSubspaces B S hS Y.1).1.toFunctor
          (⟨D.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ :
            ClosedSubspaces B S hS Y.1).1.ι))
        G W₀ s →
      s = 0 := by
  classical
  set Dpre : ClosedSubspaces B S hS Y.1 :=
    ⟨D.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ with hDpre
  intro W₀ s hs
  have hzi : ∀ x : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj W₀)),
      x ∈ zeroImages B S hS Y.1 (moduleAddSheaf B S hS Y.1 Y.2 G) W₀ s := by
    intro x
    obtain ⟨T, π, U, p, a, hp, hTaff, hUaff, hareg, hgen, w, hw⟩ :=
      exists_affine_chartPair_isRegular_span_definingIdealAt B S hS f D hD W₀
        (pointsToScheme B S hS ((SmallEtale.toOver B S hS Y.1).obj W₀) x)
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hUaff
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj T.1.left) := hTaff
    -- the restriction of the section to `T` is annihilated by a power of the generator
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : G.val.obj (op T), t₀ = G.val.map π.op s := ⟨_, rfl⟩
    have hsT : SectionSupportedIn B S hS Y.1 Y.2
        (Set.range (pointsMap B S hS Dpre.1.toFunctor Dpre.1.ι)) G T t₀ :=
      ht₀ ▸ sectionSupportedIn_restrict π s hs
    obtain ⟨n, hn⟩ :=
      (mem_primaryComponent_span_singleton_smul_iff _ t₀).mp
        ((mem_supportedSectionsSubmodule_iff_mem_primaryComponent B S hS Y Dpre G hG T hTaff
            _ hgen t₀).mp
          ((mem_supportedSectionsSubmodule_iff B S hS Y.1 Y.2 _ G T t₀).mpr hsT))
    -- a geometric point of `Y` lying under the chosen point of `T`
    obtain ⟨ybar, q, hq, hyw⟩ := exists_geometricPoint_chartLift B S hS Y.2 T w
    let N : SmallEtaleNeighborhood ybar := ⟨T, q, hq⟩
    have hNpt : chartPoint B S hS Y.1 N = w := hyw
    have hcomm : N.chart.obj.hom ≫ f.hom = yoneda.map p ≫ U.obj.hom := hp.symm
    -- the section transported to the chart cut out by the whole of the chart scheme
    set t : G.val.obj (op ((chartOpens B S hS T).obj ⊤)) :=
      G.val.map (chartOpensTopHom B S hS Y T).op t₀ with ht
    have htop : chartPoint B S hS Y.1 N ∈ (⊤ : (etaleChartScheme B S hS N.chart).Opens) :=
      trivial
    -- its germ is killed by a power of the germ of the generator
    have hgermzero : chartZariskiSectionGermOfVanishing B S hS Y.2 N G ⊤ htop t = 0 := by
      have harg : (show (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj
            (op ((chartOpens B S hS N.chart).obj ⊤)) from
          ((chartRestrictionRingHom B S hS Y.2 N.chart).app (op ⊤)).hom
            (((BigFppfOver.toScheme B S hS).map p).appTop a ^ n)) • t = 0 :=
        (G.val.map_smul (chartOpensTopHom B S hS Y T).op
            (((BigFppfOver.toScheme B S hS).map p).appTop a ^ n) t₀).symm.trans
          ((congrArg (G.val.map (chartOpensTopHom B S hS Y T).op) hn).trans (map_zero _))
      have hzero :=
        (chartZariskiSectionGermOfVanishing_smul B S hS Y.2 N G ⊤ htop
            (((BigFppfOver.toScheme B S hS).map p).appTop a ^ n) t).symm.trans
          ((congrArg (chartZariskiSectionGermOfVanishing B S hS Y.2 N G ⊤ htop) harg).trans
            (map_zero _))
      refine eq_zero_of_pow_smul_eq_zero_of_flat ((BigFppfOver.toScheme B S hS).map p) hareg
        (chartPoint B S hS Y.1 N) _ _ n hzero fun hnotunit => ?_
      -- off the unit locus the point lies over `|D|`, so `G` is flat there
      refine flat_chartZariskiModuleStalk_of_isFlatOverAtGeometricPoint B S hS f G N U p hcomm
        (hflat ybar ?_)
      have hptD : chartPointsMap T (chartPoint B S hS Y.1 N) ∈
          Set.range (pointsMap B S hS Dpre.1.toFunctor Dpre.1.ι) := by
        have heq := preimage_chartPointsMap_range_ι_eq_zeroLocus B S hS Y Dpre T hTaff
          (Ideal.span {((BigFppfOver.toScheme B S hS).map p).appTop.hom a}) hgen
        have hmem : chartPoint B S hS Y.1 N ∈ chartPointsMap T ⁻¹'
            Set.range (pointsMap B S hS Dpre.1.toFunctor Dpre.1.ι) := by
          rw [heq]
          refine (Scheme.mem_zeroLocus_iff _ _ (chartPoint B S hS Y.1 N)).mpr ?_
          rintro z hz
          obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hz
          rw [Scheme.basicOpen_mul]
          intro hmemc
          exact hnotunit ((Scheme.mem_basicOpen (chartScheme T) (U := ⊤) _
            (chartPoint B S hS Y.1 N) trivial).mp hmemc.1)
        exact hmem
      have himage : chartPointsMap T (chartPoint B S hS Y.1 N) = ybar.image :=
        (chartPoint_iff_pointOfEtaleChart_eq B S hS T (chartPoint B S hS Y.1 N) ybar.image).mp
          (chartPoint_isChartPoint B S hS ybar N)
      rw [← himage]
      rw [hDpre] at hptD
      exact (range_pointsMap_preimage_ι B S hS f.hom D.1).le hptD
    -- the section dies on a Zariski open of the chart through the point
    obtain ⟨W', i, hw', hres⟩ :=
      exists_restrict_eq_zero_of_chartZariskiSectionGermOfVanishing_eq_zero B S hS Y.2 N G ⊤ htop t
        hgermzero
    -- the inclusion of that open into `T`, as a morphism of étale charts
    have hcompose : (SmallEtale.toOver B S hS Y.1).map
        ((chartOpens B S hS T).map i ≫ chartOpensTopHom B S hS Y T) =
        chartOpenOverι B S hS T W' := by
      rw [Functor.map_comp]
      exact chartOpenOverMap_comp_ι B S hS T i
    have hmemW' : w ∈ W' := hNpt ▸ hw'
    obtain ⟨wW', hwW'⟩ : ∃ v : (BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS Y.1).obj ((chartOpens B S hS T).obj W')),
        (BigFppfOver.toScheme B S hS).map (chartOpenOverι B S hS T W') v = w :=
      ⟨⟨w, hmemW'⟩, rfl⟩
    refine ⟨(chartOpens B S hS T).obj W',
      ((chartOpens B S hS T).map i ≫ chartOpensTopHom B S hS Y T) ≫ π, ?_, ?_⟩
    · have h1 : G.val.map
            ((((chartOpens B S hS T).map i ≫ chartOpensTopHom B S hS Y T) ≫ π).op) s =
          G.val.map (((chartOpens B S hS T).map i ≫ chartOpensTopHom B S hS Y T).op)
            (G.val.map π.op s) := G.val.map_comp_apply π.op _ s
      have h2 : G.val.map (((chartOpens B S hS T).map i ≫ chartOpensTopHom B S hS Y T).op) t₀ =
          G.val.map (((chartOpens B S hS T).map i).op)
            (G.val.map (chartOpensTopHom B S hS Y T).op t₀) :=
        G.val.map_comp_apply (chartOpensTopHom B S hS Y T).op _ t₀
      have hchain : G.val.map
          ((((chartOpens B S hS T).map i ≫ chartOpensTopHom B S hS Y T) ≫ π).op) s = 0 := by
        rw [h1, ← ht₀, h2, ← ht]
        exact hres
      exact hchain
    · -- the chosen point of the open maps to `x`
      refine ⟨(pointsEquivScheme B S hS
        ((SmallEtale.toOver B S hS Y.1).obj ((chartOpens B S hS T).obj W'))).symm wW', ?_⟩
      refine injective_pointsToScheme B S hS ((SmallEtale.toOver B S hS Y.1).obj W₀) ?_
      rw [pointsToScheme_pointsMap]
      have hb : pointsToScheme B S hS
          ((SmallEtale.toOver B S hS Y.1).obj ((chartOpens B S hS T).obj W'))
          ((pointsEquivScheme B S hS
            ((SmallEtale.toOver B S hS Y.1).obj ((chartOpens B S hS T).obj W'))).symm wW') =
          wW' :=
        (pointsEquivScheme B S hS _).apply_symm_apply _
      rw [hb, Functor.map_comp (SmallEtale.toOver B S hS Y.1),
        Functor.map_comp (BigFppfOver.toScheme B S hS), Scheme.Hom.comp_apply, hcompose]
      exact (congrArg (fun v => (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS Y.1).map π) v) hwW').trans hw
  have hzero := eq_zero_of_imageInOpen_zeroImages B S hS Y.1
    (moduleAddSheaf B S hS Y.1 Y.2 G) W₀ s W₀ (𝟙 W₀) fun _ => by simpa using hzi _
  rwa [op_id, (moduleAddSheaf B S hS Y.1 Y.2 G).obj.map_id (op W₀)] at hzero

/-! ### The supported sections on the strict-transform fibre product -/

section Blowup

variable {A X A' : AlgebraicSpaces B S hS}

/-- **The pullback `pr_X^*F` is flat over `A'` at every geometric point lying over the
exceptional divisor**, when `F` is flat over `A` at every geometric point lying over the centre
`Z`.

The exceptional divisor is the inverse image of `Z`, so a geometric point of `X ×_A A'` lying
over it lies over `Z`, and its image in `|X|` therefore lies over `Z` as well; flatness of `F`
there passes to the pullback by part (1) of Stacks 05VW,
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback`. -/
theorem isFlatOverAtGeometricPoint_modulePullback_strictTransform (f : X ⟶ A) (b : A' ⟶ A)
    (Z : ClosedSubspaces B S hS A.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hflat : ∀ xbar : GeometricPoint B S hS X.1,
      pointsMap B S hS X.1 f.hom xbar.image ∈
          Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
        IsFlatOverAtGeometricPoint B S hS f F xbar)
    (wbar : GeometricPoint B S hS (strictTransformPullback B S hS f b).1)
    (hw : pointsMap B S hS (strictTransformPullback B S hS f b).1
        (strictTransformPullbackToBlowUp B S hS f b).hom wbar.image ∈
      Set.range (pointsMap B S hS (preimageClosedSubspace b Z).1.toFunctor
        (preimageClosedSubspace b Z).1.ι)) :
    IsFlatOverAtGeometricPoint B S hS (strictTransformPullbackToBlowUp B S hS f b)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj F) wbar := by
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS f b
  have hcomp : pointsMap B S hS A'.1 b.hom
        (pointsMap B S hS (strictTransformPullback B S hS f b).1
          (strictTransformPullbackToBlowUp B S hS f b).hom wbar.image) =
      pointsMap B S hS X.1 f.hom
        (pointsMap B S hS (strictTransformPullback B S hS f b).1
          (strictTransformPullbackToSource B S hS f b).hom wbar.image) := by
    have h := congrArg (fun k : strictTransformPullback B S hS f b ⟶ A =>
      pointsMap B S hS (strictTransformPullback B S hS f b).1 k.hom wbar.image) sq.w
    have e1 := congrFun (pointsMap_comp B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullbackToSource B S hS f b).hom f.hom) wbar.image
    have e2 := congrFun (pointsMap_comp B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullbackToBlowUp B S hS f b).hom b.hom) wbar.image
    exact e2.symm.trans (h.symm.trans e1)
  have hmem : pointsMap B S hS X.1 f.hom
      (pointsMap B S hS (strictTransformPullback B S hS f b).1
        (strictTransformPullbackToSource B S hS f b).hom wbar.image) ∈
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
    rw [← hcomp]
    exact (range_pointsMap_preimage_ι B S hS b.hom Z.1).le hw
  exact isFlatOverAtGeometricPoint_modulePullback B S hS sq F wbar (hflat _ hmem)

/-- **Stacks 0865, part (2), the submodule of supported sections.**  Let `Z ⊆ A` be a closed
subspace of an algebraic space over `S`, let `b : A' ⟶ A` be the blowup of `A` in `Z` and let
`F` be a quasi-coherent `𝒪_X`-module on an algebraic space `f : X ⟶ A` over `A` which is flat
over `A` at every geometric point lying over `Z`.  Then the submodule of sections of `pr_X^*F`
supported on the exceptional preimage is zero, so its inclusion is the zero morphism.

This is the input `hloc` needed by
`AlgebraicGeometry.Space.isIso_strictTransformSheafQuotient_of_isFlatOverAtGeometricPoint`: the
exceptional divisor is an effective Cartier divisor on `A'`
because `b` is a blowup, the pullback `pr_X^*F` is quasi-coherent by Stacks 03GA and flat over
`A'` above the exceptional divisor by part (1) of Stacks 05VW, so
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_preimage_of_isFlatOverAtGeometricPoint`
applies to the projection `X ×_A A' ⟶ A'`. -/
theorem supportedSections_exceptionalPreimage_ι_eq_zero_of_isFlatOverAtGeometricPoint
    (f : X ⟶ A) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (hflat : ∀ xbar : GeometricPoint B S hS X.1,
      pointsMap B S hS X.1 f.hom xbar.image ∈
          Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) →
        IsFlatOverAtGeometricPoint B S hS f F xbar) :
    (supportedSectionsSubmodule B S hS (strictTransformPullback B S hS f b).1
        (strictTransformPullback B S hS f b).2
        (exceptionalPreimageSet B S hS f b (Z.1.preimage b.hom))
        ((modulePullback B S hS
          (strictTransformPullbackToSource B S hS f b)).obj F)).ι = 0 := by
  have hD : HasEffectiveCartierEtalePullbacks B S hS A' (preimageClosedSubspace b Z) :=
    hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS A'
      (preimageClosedSubspace b Z) hb.isPullbackDefined
  have hQ : ((modulePullback B S hS
      (strictTransformPullbackToSource B S hS f b)).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (strictTransformPullbackToSource B S hS f b) F hF
  have hno := hasNoSectionsSupportedIn_preimage_of_isFlatOverAtGeometricPoint B S hS
    (strictTransformPullbackToBlowUp B S hS f b) (preimageClosedSubspace b Z) hD _ hQ
    (isFlatOverAtGeometricPoint_modulePullback_strictTransform B S hS f b Z F hflat)
  ext W x
  exact hno W.unop x.1 ((mem_supportedSectionsSubmodule_iff B S hS
    (strictTransformPullback B S hS f b).1 (strictTransformPullback B S hS f b).2 _ _
    W.unop x.1).mp x.2)

end Blowup

end AlgebraicGeometry.Space

end
