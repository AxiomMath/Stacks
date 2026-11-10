module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSiteLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOverTheTerminalSlice

/-!
# Čech vanishing on the small étale site of an algebraic space, for an associated module

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `W` be an
étale chart of `F` with *affine* underlying scheme `Y`, and let `M` be a quasi-coherent
`𝒪_Y`-module.  Restricting along `AlgebraicGeometry.Space.SmallEtale.sliceToOver` turns `M` into
the presheaf `Mᵃ` of [Stacks, Tag 03DU] on the slice of the small étale site of `F` at `W`.  This
file proves that the Čech cohomology of `Mᵃ` on a covering family of `W` whose image is a
standard étale covering of `Y` vanishes in every positive degree: the `Ȟ^p(𝒰, Fᵃ) = 0` clause of
Descent, Lemma 03FJ, for the small étale site of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isStandardCovering_sliceImageFamily`: the image of a
  finite affine covering family of an affine chart is a standard étale covering of the chart's
  scheme.
* `AlgebraicGeometry.Space.SmallEtale.isZero_sliceCechCohomology_associatedPresheaf`: the Čech
  cohomology of `Mᵃ` vanishes in every positive degree, for a covering family of an affine chart
  whose image is a standard étale covering of the chart's scheme.
* `AlgebraicGeometry.Space.SmallEtale.isZero_sliceCechCohomology_associatedPresheaf_of_covering`:
  the same for a finite covering family of an affine chart by affine charts.
* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_of_iso_associatedPresheaf`: the same
  for a coefficient presheaf on the site whose restriction to the slice is identified with `Mᵃ`.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : SmallEtale B S hS F)

/-- The image of a finite affine covering family of an affine chart is a standard étale
covering of the chart's scheme. -/
theorem isStandardCovering_sliceImageFamily [IsAffine (chartScheme W)]
    (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W) :
    IsStandardCovering .etale
      (Stacks.CechSite.sliceImageFamily E (sliceToOver B S hS F W)).X
      (Stacks.CechSite.sliceImageFamily E (sliceToOver B S hS F W)).f where
  finite_index := hfin
  affine_source := haff
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    obtain ⟨V, g, hg, y, hy⟩ :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS F E.sieve₀).mp hcov x
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff E.X E.f g).mp hg
    refine ⟨i, ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS F).map h)) y, ?_⟩
    rw [← hy]
    change ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (E.f i)))
        (((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map h)) y) =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (h ≫ E.f i))) y
    rw [Functor.map_comp, Functor.map_comp]
    simp
  standard := fun i ↦ etale_sliceToOver_obj_hom B S hS F W (Over.mk (E.f i))

/-- Let `W` be an étale chart of `F` whose underlying scheme `Y` is affine, let `M` be a
quasi-coherent `𝒪_Y`-module, and let `E` be a family of charts over `W` whose image family of
schemes over `Y` is a standard étale covering.  Then the Čech cohomology of the associated
presheaf `Mᵃ` on the slice at `W` vanishes in every positive degree. -/
theorem isZero_sliceCechCohomology_associatedPresheaf [hY : IsAffine (chartScheme W)]
    (E : PreZeroHypercover.{u} W)
    [hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (M : (chartScheme W).Modules) [M.IsQuasicoherent]
    (hstd : IsStandardCovering .etale
      (Stacks.CechSite.sliceImageFamily E (sliceToOver B S hS F W)).X
      (Stacks.CechSite.sliceImageFamily E (sliceToOver B S hS F W)).f)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.sliceCechCohomology E
      (Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W)) p) := by
  set 𝒢 := Stacks.CechSite.sliceImageFamily E (sliceToOver B S hS F W) with h𝒢
  have hprod𝒢 : ∀ (n : ℕ) (i : Fin (n + 1) → 𝒢.I₀),
      HasProduct (fun a ↦ Over.mk (𝒢.f (i a))) := fun _ _ ↦ inferInstance
  have hfl : HasFiniteLimits (Over (Over.mk (𝟙 (chartScheme W)))) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have hYU : IsAffine (Over.mk (𝟙 (chartScheme W))).left := hY
  have hprodT : ∀ (n : ℕ) (i : Fin (n + 1) → (Stacks.CechSite.toTerminalSliceFamily 𝒢).I₀),
      HasProduct (fun a ↦ Over.mk ((Stacks.CechSite.toTerminalSliceFamily 𝒢).f (i a))) :=
    fun _ _ ↦ inferInstance
  have hiso : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (Stacks.CechSite.cechProductMapOfSliceFunctor E (sliceToOver B S hS F W) n i) :=
    fun n i ↦ Stacks.CechSite.isIso_cechProductMapOfSliceFunctor E (sliceToOver B S hS F W) n i
  have hcase : IsZero (Stacks.CechSite.cechCohomology
      (Stacks.CechSite.toTerminalSliceFamily 𝒢)
      (quasiCoherentPresheafFunctor (chartScheme W) M) p) :=
    isZero_cechCohomology_succ_quasiCoherentPresheaf (Over.mk (𝟙 (chartScheme W))) .etale M
      (Stacks.CechSite.toTerminalSliceFamily 𝒢) hstd p hp
  exact Stacks.CechSite.isZero_sliceCechCohomology_of_isZero_of_sliceFunctor E
    (sliceToOver B S hS F W) (quasiCoherentPresheafFunctor (chartScheme W) M) hiso p
    (Stacks.CechSite.isZero_sliceCechCohomology_of_isZero_cechCohomology_toTerminalSliceFamily
      𝒢 (quasiCoherentPresheafFunctor (chartScheme W) M) p hcase)

/-- Let `W` be an étale chart of `F` whose underlying scheme is affine, let `M` be a
quasi-coherent module on it, and let `E` be a finite covering family of `W` by charts with affine
underlying schemes.  Then the Čech cohomology of the associated presheaf `Mᵃ` on the slice at `W`
vanishes in every positive degree. -/
theorem isZero_sliceCechCohomology_associatedPresheaf_of_covering
    [IsAffine (chartScheme W)] (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W)
    [hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (M : (chartScheme W).Modules) [M.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.sliceCechCohomology E
      (Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W)) p) :=
  isZero_sliceCechCohomology_associatedPresheaf B S hS F W E M
    (isStandardCovering_sliceImageFamily B S hS F W E hfin haff hcov) p hp

/-- Let `W` be an étale chart of `F` whose underlying scheme is affine, let `M` be a
quasi-coherent module on it, and let `E` be a finite covering family of `W` by charts with affine
underlying schemes.  For a coefficient presheaf on the site whose restriction to the slice at `W`
is identified with `Mᵃ`, the Čech cohomology on `E` vanishes in every positive degree. -/
theorem isZero_cechCohomology_of_iso_associatedPresheaf
    [IsAffine (chartScheme W)] (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W)
    [hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (M : (chartScheme W).Modules) [M.IsQuasicoherent]
    (Coeff : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : (Over.forget W).op ⋙ Coeff ≅
      Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W))
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E Coeff p) :=
  Stacks.CechSite.isZero_cechCohomology_of_isZero_slice E e p
    (isZero_sliceCechCohomology_associatedPresheaf_of_covering B S hS F W E hfin haff hcov M p hp)

end AlgebraicGeometry.Space.SmallEtale

end
