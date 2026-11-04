module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSite
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOnTheSlice
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks

/-!
# Čech vanishing on the small étale site of an algebraic space, at an affine chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `W` be an
*affine* étale chart of `F` and let `{V_i → W}` be a finite covering family of `W` by affine
étale charts.  This file proves that the higher Čech cohomology of that family vanishes, for
coefficients the associated presheaf `𝓕ᵃ` of [Stacks, Tag 03DS] of a quasi-coherent module `𝓕`
on the scheme `chartScheme W` underlying `W`, read on the slice at `W` through
`AlgebraicGeometry.Space.SmallEtale.sliceToOver`.

It is the transport of [Stacks, Tag 03FJ] case (a) — Čech vanishing for a standard `τ`-covering
of an object of `Over S`, `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf` —
from the schemes over a base to the small étale site of an algebraic space.

## The shape of the transport

The Čech complex of a family `{V_i → W}` with target `W` is built from the products, in the
*slice* `Over W`, of the selected objects `Over.mk (V_i → W)`; and the Čech complex of a family
with target an object `U` of `Over T` is built from products in the *double* slice `Over U`.
So the source family has to be lifted one slice before the comparison can be made: that is
`AlgebraicGeometry.Space.SmallEtale.sliceHypercover`, the same family read as a family in
`Over W` with target the terminal object `Over.mk (𝟙 W)`.  Its image

* under `CategoryTheory.Over.forget W` is the original family, by `rfl`, and
* under `AlgebraicGeometry.Space.SmallEtale.sliceToOver` — which is
  `CategoryTheory.Over.post` of the projection taking a chart to its scheme — is a family of
  schemes over `chartScheme W` with target `Over.mk (𝟙 (chartScheme W))` up to the identity
  functor laws.

`Stacks.CechSite.cechCohomologyIsoOfFunctor` applied along each of those two functors identifies
the three Čech complexes, its hypothesis being supplied in both cases by
`Stacks.Sites.preservesLimit_fibreProducts_overPost`: the slice of the small étale site has
fibre products, `CategoryTheory.Over.forget` preserves them, and so does `sliceToOver`, because
the scheme underlying a fibre product of charts is the fibre product of the schemes
(`AlgebraicGeometry.Space.SmallEtale.instPreservesPullbacksToSchemes`).  The coefficients are
matched in the middle, on the slice at `W`, which is the only place where the module `𝓕ᵃ` of
Tag 03DU is defined.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_mem_arrows_mem_range`: **every covering sieve of
  the small étale site of `F` is jointly surjective on points.**  This is the analogue, for an
  algebraic space, of `AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`.
* `AlgebraicGeometry.Space.SmallEtale.iUnion_range_eq_univ_of_sieve₀_mem_topology`: a family of
  étale charts whose generated sieve is covering is jointly surjective on the underlying
  schemes.  This is what turns the covering condition that a Čech statement carries into the
  `jointly_surjective` field of `AlgebraicGeometry.IsStandardCovering`.
* `AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceHypercover_map`: a finite covering
  family of an affine chart by affine charts has, as a family of schemes over the chart's
  scheme, standard étale form in the sense of [Stacks, Tag 03X9].
* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_associatedPresheafIso`:
  **the Čech vanishing**, for an abelian presheaf identified on the slice at `W` with `𝓕ᵃ`.
* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_essSurj_at`: **the same for
  the abelian presheaf underlying an `𝒪_F`-module**, granted only that the restriction of the
  module to the slice at `W` is isomorphic to some `Mᵃ` — the single-chart instance of the
  hypothesis `hEss` of
  `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`.

## Implementation notes

**The coefficients enter through an isomorphism, not through a module.**  The headline
statement is about an arbitrary abelian presheaf `P` on the small étale site of `F` whose
restriction to the slice at `W` is identified with `𝓕ᵃ`.  That costs nothing — the Čech complex
is a functor of the coefficient presheaf on the slice
(`Stacks.CechSite.cechComplexFunctor`, through
`Stacks.CechSite.cechComplex_eq_sliceCechComplex`) — and it is what lets the module form be a
corollary.

**What the module form still needs, and what it does not.**  For an `𝒪_F`-module `K` the
identification of its restriction to the slice at `W` with an `Mᵃ` is *not* available in this
tree, and it is the only thing missing.  It is **not** the implication between cartesianness and
quasi-coherence: both directions of that are proved and unconditional,
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.  It is
the *essential surjectivity* of `(-)ᵃ` on the slice at an affine chart — the hypothesis `hEss`
of `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj`.  What blocks
`hEss` is not a localization argument, quasi-coherence on a site giving a global presentation
only on the members of *some* covering of each object: the global presentation *on the slice*
at an affine chart is proved and unconditional, as
`AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isAffine` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSpaceGlobalPresentation.lean`, and so are the free
step and the full faithfulness that the Stacks proof of 03DX (2) consumes after it; the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleEssSurj.lean` record the one step
that is left, which is that `M ↦ Mᵃ` on the slice carries a cokernel of free modules to the
cokernel.  `isZero_cechCohomology_succ_of_essSurj_at` takes `hEss` at the one chart and nothing
else, and `StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSurjectivityFromEssSurj.lean`
composes it with the Čech computation into Stacks 03DW on this site from `hEss` alone.

**The index universe is the universe of the schemes.**  The covering family is a
`CategoryTheory.PreZeroHypercover.{u}`, because
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf` is stated at a single
universe and its family is a `PreZeroHypercover.{u}` over `Scheme.{u}`.  A family presented at
index universe `0` — which is what
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement` produces — is *not* covered
by the statement below.  Crossing that gap needs no isomorphism between the Čech complex of a
family and the Čech complex of its `ULift` reindexing: the cofinal system Stacks 03F8 is applied
to can be produced at index universe `u` to begin with, by
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_preZeroHypercover_univ`, whose lifted
family has the same arrows and hence literally the same generated sieve.  No Čech complex is
reindexed anywhere.

**No `@[stacks]` attribute is claimed.**  [Stacks, Tag 03FJ] is stated for the three cases of
[Stacks, Tag 03FI] — a big `τ`-site, the small étale site of a *scheme*, and the small Zariski
site of a scheme — and all three are already registered in this tree
(`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf` and the two declarations of
`StacksFrontier/AlgebraicGeometry/Topologies/CechAmitsurSmallSites.lean`).  The small étale site of
an algebraic space is not one of them, so nothing here would prove a clause of the tag that is
not already proved.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite

universe v u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Covering sieves are jointly surjective -/

/-- **Every covering sieve of the small étale site of an algebraic space is jointly surjective
on points:** some member of the sieve has the given point of the chart's scheme in its image.
This is the analogue of `AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range` for the small
étale site of a scheme. -/
theorem exists_mem_arrows_mem_range {V : SmallEtale B S hS F} {R : Sieve V}
    (hR : R ∈ topology B S hS F V) (x : chartScheme V) :
    ∃ (Z : SmallEtale B S hS F) (g : Z ⟶ V), R g ∧
      x ∈ Set.range ((toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map g) := by
  obtain ⟨Rp, hRp, hle⟩ := (mem_topology_iff B S hS F).mp hR
  obtain ⟨E, rfl, hE⟩ := (mem_precoverage_iff B S hS F).mp hRp
  have hcov : (E.map (toOver B S hS F ⋙ BigFppfOver.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage (chartScheme V) := hE.2
  obtain ⟨i, hi⟩ := ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mp hcov).1 x
  exact ⟨E.X i, E.f i, hle _ _ (Presieve.ofArrows.mk i), hi⟩

/-- **A family of étale charts generating a covering sieve is jointly surjective on the
underlying schemes.** -/
theorem iUnion_range_eq_univ_of_sieve₀_mem_topology {W : SmallEtale B S hS F}
    (E : PreZeroHypercover.{v} W) (hE : E.sieve₀ ∈ topology B S hS F W) :
    (⋃ i, Set.range ((toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (E.f i)))
      = Set.univ := by
  refine Set.eq_univ_iff_forall.2 fun x ↦ ?_
  obtain ⟨Z, g, hg, hx⟩ := exists_mem_arrows_mem_range B S hS F hE x
  obtain ⟨Y, h, f', hf', rfl⟩ := hg
  obtain ⟨i⟩ := hf'
  obtain ⟨y, hy⟩ := hx
  refine Set.mem_iUnion.2 ⟨i, (toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map h y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
  exact hy

/-! ### The covering family, lifted into the slice at the covered chart -/

variable (W : SmallEtale B S hS F)

/-- A family of morphisms of étale charts with target `W`, read as a family in the slice `Over W`
with target the terminal object `Over.mk (𝟙 W)`: the member `V_i → W` becomes the object
`Over.mk (V_i → W)` together with its own structure morphism. -/
def sliceHypercover (E : PreZeroHypercover.{u} W) :
    PreZeroHypercover.{u} (Over.mk (𝟙 W)) where
  I₀ := E.I₀
  X i := Over.mk (E.f i)
  f i := Over.homMk (E.f i) (by simp)

/-- Pushing the slice reading of a family back down along the slice projection returns the
family itself, on the nose. -/
theorem sliceHypercover_map_forget (E : PreZeroHypercover.{u} W) :
    (sliceHypercover B S hS F W E).map (Over.forget W) = E := rfl

/-- **A finite covering family of an affine chart by affine charts has standard étale form
downstairs.**  Its image under `AlgebraicGeometry.Space.SmallEtale.sliceToOver` is a family of
schemes over the affine scheme `chartScheme W` which is finite, has affine members, is jointly
surjective and consists of étale morphisms — a standard étale covering in the sense of
[Stacks, Tag 03X9]. -/
theorem isStandardCovering_sliceHypercover_map (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ topology B S hS F W) :
    letI : IsAffine ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W))).left := hW
    IsStandardCovering .etale
      (fun i ↦ (((sliceHypercover B S hS F W E).map (sliceToOver B S hS F W)).X i).left)
      (fun i ↦ (((sliceHypercover B S hS F W E).map (sliceToOver B S hS F W)).f i).left) :=
  let : IsAffine ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W))).left := hW
  { finite_index := hfin
    affine_source := haff
    jointly_surjective := iUnion_range_eq_univ_of_sieve₀_mem_topology B S hS F E hcov
    standard := fun i ↦ etale_sliceToOver_obj_hom B S hS F W (Over.mk (E.f i)) }

/-! ### The vanishing -/

/-- **Čech vanishing in positive degrees for a finite affine covering family of an affine étale
chart of an algebraic space**, with coefficients an abelian presheaf whose restriction to the
slice at the chart is the associated presheaf `𝓕ᵃ` of [Stacks, Tag 03DS] of a quasi-coherent
module `𝓕` on the chart's scheme.

This is [Stacks, Tag 03FJ] case (a),
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf`, transported to the small
étale site of the algebraic space.  The finite products in the slice at `W` which the Čech
complex is built from come from the terminal object of the slice and the fibre products of the
site. -/
theorem isZero_cechCohomology_succ_of_associatedPresheafIso
    (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ topology B S hS F W)
    (M : (chartScheme W).Modules) [M.IsQuasicoherent]
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : (Over.forget W).op ⋙ P ≅
      Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W))
    (p : ℕ) (hp : 0 < p) :
    letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsZero (cechCohomology E P p) := by
  let : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : IsAffine (chartScheme W) := hW
  let : HasFiniteLimits (Over (Over.mk (𝟙 W))) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : IsAffine ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W))).left := hW
  let : HasFiniteLimits (Over ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W)))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let hpW : ∀ (n : ℕ)
      (i : Fin (n + 1) → ((sliceHypercover B S hS F W E).map (Over.forget W)).I₀),
      HasProduct (fun a ↦
        Over.mk (((sliceHypercover B S hS F W E).map (Over.forget W)).f (i a))) :=
    fun n i ↦ (inferInstance : HasProduct (fun a ↦ Over.mk (E.f (i a))))
  have hforget : ∀ (n : ℕ) (i : Fin (n + 1) → (sliceHypercover B S hS F W E).I₀),
      IsIso (cechProductMapOfFunctor (Over.forget W) (sliceHypercover B S hS F W E) n i) := by
    intro n i
    let := Stacks.Sites.preservesLimit_fibreProducts_overPost (Over.forget W)
      (sliceHypercover B S hS F W E)
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
    exact isIso_cechProductMapOfFunctor (Over.forget W) (sliceHypercover B S hS F W E) n i
  have hslice : ∀ (n : ℕ) (i : Fin (n + 1) → (sliceHypercover B S hS F W E).I₀),
      IsIso (cechProductMapOfFunctor (sliceToOver B S hS F W)
        (sliceHypercover B S hS F W E) n i) := by
    intro n i
    let := Stacks.Sites.preservesLimit_fibreProducts_overPost (sliceToOver B S hS F W)
      (sliceHypercover B S hS F W E)
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) n i
    exact isIso_cechProductMapOfFunctor (sliceToOver B S hS F W)
      (sliceHypercover B S hS F W E) n i
  have hzero : IsZero (cechCohomology
      ((sliceHypercover B S hS F W E).map (sliceToOver B S hS F W))
      (quasiCoherentPresheafFunctor (chartScheme W) M) p) :=
    isZero_cechCohomology_succ_quasiCoherentPresheaf
      ((sliceToOver B S hS F W).obj (Over.mk (𝟙 W))) .etale M
      ((sliceHypercover B S hS F W E).map (sliceToOver B S hS F W))
      (isStandardCovering_sliceHypercover_map B S hS F W hW E hfin haff hcov) p hp
  have hslicezero : IsZero (cechCohomology (sliceHypercover B S hS F W E)
      (Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W)) p) :=
    hzero.of_iso (cechCohomologyIsoOfFunctor (sliceToOver B S hS F W)
      (sliceHypercover B S hS F W E)
      (quasiCoherentPresheafFunctor (chartScheme W) M) hslice p).symm
  have hcoeff : IsZero (cechCohomology (sliceHypercover B S hS F W E)
      ((Over.forget W).op ⋙ P) p) :=
    hslicezero.of_iso
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).mapIso
        ((Stacks.CechSite.cechComplexFunctor (sliceHypercover B S hS F W E)).mapIso e))
  exact hcoeff.of_iso (cechCohomologyIsoOfFunctor (Over.forget W)
    (sliceHypercover B S hS F W E) P hforget p)

/-- **The Čech vanishing for the abelian presheaf underlying an `𝒪_F`-module**, granted that the
restriction of the module to the slice at the affine chart `W` is isomorphic to some `Mᵃ`. -/
theorem isZero_cechCohomology_succ_of_essSurj_at {hF : IsAlgebraicSpace B S hS F}
    (hW : IsAffine (chartScheme W))
    (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ topology B S hS F W)
    (K : Modules.{u, u} B S hS F hF)
    (hEss : ∃ (M : (chartScheme W).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((topology B S hS F).over W)
        (Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W))),
      Nonempty (sliceModule B S hS F hF W K ≅ sliceAssociatedModule B S hS F hF W M hM))
    (p : ℕ) (hp : 0 < p) :
    letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    IsZero (cechCohomology E
      ((sheafToPresheaf (topology B S hS F) AddCommGrpCat.{u}).obj
        ((SheafOfModules.toSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O))).obj K)) p) := by
  obtain ⟨M, hMqc, hM, ⟨α⟩⟩ := hEss
  let := hMqc
  exact isZero_cechCohomology_succ_of_associatedPresheafIso B S hS F W hW E hfin haff hcov M
    ((sheafToPresheaf (topology B S hS F) AddCommGrpCat.{u}).obj
      ((SheafOfModules.toSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj K))
    ((sheafToPresheaf ((topology B S hS F).over W) AddCommGrpCat.{u}).mapIso
      ((SheafOfModules.toSheaf (sliceRingSheaf B S hS F hF W)).mapIso α)) p hp

end AlgebraicGeometry.Space.SmallEtale

end

