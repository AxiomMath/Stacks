module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BoundedSmallEtaleCechRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstVanishingAndSections

/-!
# Surjectivity on affine sections for the small étale site of a scheme

Let `S` be a scheme contained in a big étale site `B`.  This file proves that in a short exact
sequence `0 → 𝓜₁ → 𝓜₂ → 𝓜₃ → 0` of `𝒪`-modules on the small étale site of `S` whose *left* term
is quasi-coherent, the right-hand map is surjective on the sections over every object with
affine total space.

Nothing is asked of the middle or the right term.

## Main results

* `AlgebraicGeometry.SmallEtale.shortExact_map_toSheaf`: the sequence of underlying abelian
  sheaves of a short exact sequence of sheaves of modules is short exact.
* `AlgebraicGeometry.SmallEtale.exists_sieve₀_le_isZero_cechCohomology_one_toSheaf`: **every
  covering sieve of an object with affine total space contains a covering family along which the
  first Čech cohomology of a quasi-coherent `𝒪`-module vanishes.**
* `AlgebraicGeometry.SmallEtale.surjective_g_val_app_of_shortExact`: **the right-hand map of a
  short exact sequence whose left term is quasi-coherent is surjective on the sections over an
  object with affine total space.**

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The underlying sequence of abelian sheaves -/

/-- **The sequence of underlying abelian sheaves of a short exact sequence of sheaves of modules
is short exact.** -/
theorem shortExact_map_toSheaf
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact) :
    (T.map (SheafOfModules.toSheaf (structureSheaf B S hS))).ShortExact :=
  have := hT.mono_f
  have := hT.epi_g
  { exact := ShortComplex.Exact.map_of_mono_of_preservesKernel hT.exact _ hT.mono_f inferInstance
    mono_f := (SheafOfModules.toSheaf (structureSheaf B S hS)).map_mono _
    epi_g := (SheafOfModules.toSheaf (structureSheaf B S hS)).map_epi _ }

/-! ### Čech-acyclic refinements for a quasi-coherent module -/

/-- **Every covering sieve of an object of the small étale site with affine total space contains
a covering family along which the first Čech cohomology of a quasi-coherent `𝒪`-module
vanishes.** -/
theorem exists_sieve₀_le_isZero_cechCohomology_one_toSheaf
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS)
    (hW : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj W))
    {R : Sieve W} (hR : R ∈ topology B S hS W) :
    ∃ E : PreZeroHypercover.{u} W, (E.sieve₀ ∈ topology B S hS W ∧
        IsZero (Stacks.CechSite.cechCohomology E
          ((sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).obj
            ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj G)) 1)) ∧
      E.sieve₀ ≤ R := by
  let : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := isQuasicoherent_restrictModule B S hS G hG
  let := isIso_counit B S hS G hG (isQuasicoherent_restrictModule B S hS G hG)
  obtain ⟨E, hE, hle⟩ :=
    exists_isSmallEtaleStandardCovering_map_sieve₀_le B S hS W hW hR
  refine ⟨E, ⟨?_, ?_⟩, hle⟩
  · refine generate_ofArrows_mem_topology_of_jointlySurjective B S hS E.X E.f fun x ↦ ?_
    obtain ⟨hU, hstd⟩ := hE
    let := hU
    have hx : x ∈ ⋃ i, Set.range ((E.map (toEtaleSite B S hS)).f i).left :=
      hstd.jointly_surjective ▸ Set.mem_univ x
    exact Set.mem_iUnion.mp hx
  · exact (isZero_cechCohomology_succ_associatedModule B S hS
      ((restrictModule B S hS).obj G) E hE 1 Nat.one_pos).of_iso
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) 1).mapIso
        ((Stacks.CechSite.cechComplexFunctor E).mapIso
          ((SheafOfModules.toSheaf (structureSheaf B S hS) ⋙
            sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).mapIso
              (asIso ((associatedModuleAdjunction B S hS).counit.app G)).symm)))

/-! ### Surjectivity on the sections over an affine object -/

/-- **The right-hand map of a short exact sequence of `𝒪`-modules on the small étale site of a
scheme whose left term is quasi-coherent is surjective on the sections over every object with
affine total space.**

Nothing is asked of the middle or of the right term. -/
theorem surjective_g_val_app_of_shortExact
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (W : SmallEtale B S hS)
    (hW : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj W)) :
    Function.Surjective (T.g.val.app (op W)) :=
  Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology.{u, u, u + 1, u}
    (topology B S hS) _ (shortExact_map_toSheaf B S hS hT) W
    {E : PreZeroHypercover.{u} W | E.sieve₀ ∈ topology B S hS W ∧
      IsZero (Stacks.CechSite.cechCohomology E
        ((sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).obj
          ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj T.X₁)) 1)}
    (fun _ hE ↦ hE.1)
    (fun _ hR ↦ exists_sieve₀_le_isZero_cechCohomology_one_toSheaf B S hS T.X₁ h₁ W hW hR)
    (fun _ _ _ _ ↦ inferInstance) (fun _ hE ↦ hE.2)

end AlgebraicGeometry.SmallEtale

end
