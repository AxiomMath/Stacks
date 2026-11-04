module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishing

/-!
# The uniform form of Stacks 03DW from essential surjectivity of `(-)ᵃ`

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  This file
derives the uniform form of Descent, Proposition 03DW, namely that an epimorphism of
`𝒪_F`-modules whose kernel is cartesian on affine charts is surjective on sections over every
affine chart, from the hypothesis

    (hEss : ∀ (K : Modules.{u, u} B S hS F hF) (W : SmallEtale B S hS F),
      IsAffine (chartScheme W) → IsCartesianOnAffineCharts K →
      ∃ (M : (chartScheme W).Modules) (_ : M.IsQuasicoherent) (hM : _),
        Nonempty (sliceModule B S hS F hF W K ≅ sliceAssociatedModule B S hS F hF W M hM))

that every module cartesian on affine charts restricts, on the slice at an affine chart, to the
module `Mᵃ` of Tag 03DU of a quasi-coherent module `M` on the chart's scheme.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isoAssociatedPresheaf_of_sliceAssociatedModuleIso`: an
  isomorphism `K|_W ≅ Mᵃ` of sheaves of modules on the slice gives an isomorphism of the
  underlying abelian presheaves.
* `AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_of_sliceAssociatedModuleIso`: hence
  the Čech cohomology of the coefficient presheaf vanishes in every positive degree, on a finite
  affine covering family of an affine chart.
* `AlgebraicGeometry.Space.isZero_cechCohomology_of_essSurj`: the vanishing of the first Čech
  cohomology of a module cartesian on affine charts on every finite affine covering family of an
  affine chart, from `hEss`.
* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_of_essSurj'`: the
  uniform form of Stacks 03DW from `hEss`.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (W : SmallEtale B S hS F)

/-- An isomorphism `K|_W ≅ Mᵃ` of sheaves of modules on the slice at `W` induces an isomorphism
between the restriction to the slice of the underlying abelian presheaf of `K` and the
associated presheaf `Mᵃ`. -/
noncomputable def isoAssociatedPresheaf_of_sliceAssociatedModuleIso
    (K : Modules.{u, u} B S hS F hF)
    (M : (chartScheme W).Modules) [M.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((topology B S hS F).over W)
      (Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W)))
    (e : sliceModule B S hS F hF W K ≅ sliceAssociatedModule B S hS F hF W M hM) :
    (Over.forget W).op ⋙
        ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
          ((SheafOfModules.toSheaf
            (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K)) ≅
      Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W) :=
  (sheafToPresheaf _ _).mapIso
    ((SheafOfModules.toSheaf (sliceRingSheaf B S hS F hF W)).mapIso e)

/-- The Čech cohomology of the underlying abelian presheaf of an `𝒪_F`-module `K` vanishes in
every positive degree on a finite affine covering family of an affine chart `W`, given an
isomorphism `K|_W ≅ Mᵃ` for a quasi-coherent module `M` on the chart's scheme. -/
theorem isZero_cechCohomology_of_sliceAssociatedModuleIso
    [IsAffine (chartScheme W)] (E : PreZeroHypercover.{u} W) (hfin : Finite E.I₀)
    (haff : ∀ i, IsAffine (chartScheme (E.X i)))
    (hcov : E.sieve₀ ∈ SmallEtale.topology B S hS F W)
    [hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (K : Modules.{u, u} B S hS F hF)
    (M : (chartScheme W).Modules) [M.IsQuasicoherent]
    (hM : Presheaf.IsSheaf ((topology B S hS F).over W)
      (Stacks.Sites.associatedPresheaf (chartScheme W) M (sliceToOver B S hS F W)))
    (e : sliceModule B S hS F hF W K ≅ sliceAssociatedModule B S hS F hF W M hM)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E
      ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
        ((SheafOfModules.toSheaf
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K)) p) :=
  isZero_cechCohomology_of_iso_associatedPresheaf B S hS F W E hfin haff hcov M _
    (isoAssociatedPresheaf_of_sliceAssociatedModuleIso B S hS F hF W K M hM e) p hp

end AlgebraicGeometry.Space.SmallEtale

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Suppose that every module cartesian on affine charts restricts, on the slice at an affine
chart, to the module `Mᵃ` of Tag 03DU of a quasi-coherent module on the chart's scheme.  Then the
first Čech cohomology of the underlying abelian presheaf of a module cartesian on affine charts
vanishes on every finite affine covering family of an affine chart. -/
theorem isZero_cechCohomology_of_essSurj
    (hEss : ∀ (K : Modules.{u, u} B S hS F hF) (W : SmallEtale B S hS F),
      IsAffine (chartScheme W) → IsCartesianOnAffineCharts K →
      ∃ (M : (chartScheme W).Modules) (_ : M.IsQuasicoherent)
        (hM : Presheaf.IsSheaf ((SmallEtale.topology B S hS F).over W)
          (Stacks.Sites.associatedPresheaf (chartScheme W) M
            (SmallEtale.sliceToOver B S hS F W))),
        Nonempty (SmallEtale.sliceModule B S hS F hF W K ≅
          SmallEtale.sliceAssociatedModule B S hS F hF W M hM)) :
    ∀ K : Modules.{u, u} B S hS F hF, IsCartesianOnAffineCharts K →
      ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
        ∀ E : PreZeroHypercover.{u} W, Finite E.I₀ →
          (∀ i, IsAffine
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (E.X i))) →
          E.sieve₀ ∈ SmallEtale.topology B S hS F W →
          letI : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
          IsZero (Stacks.CechSite.cechCohomology E
            ((sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}).obj
              ((SheafOfModules.toSheaf
                (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj K)) 1) := by
  intro K hK W hW E hfin haff hcov
  let : HasFiniteLimits (Over W) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : IsAffine (chartScheme W) := hW
  have hprodE : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a))) := fun _ _ ↦ inferInstance
  obtain ⟨M, hMqc, hM, ⟨e⟩⟩ := hEss K W hW hK
  exact SmallEtale.isZero_cechCohomology_of_sliceAssociatedModuleIso B S hS F hF W E hfin haff
    hcov K M hM e 1 Nat.one_pos

/-- Suppose that every module cartesian on affine charts restricts, on the slice at an affine
chart, to the module `Mᵃ` of Tag 03DU of a quasi-coherent module on the chart's scheme.  Then an
epimorphism of `𝒪_F`-modules whose kernel is cartesian on affine charts is surjective on
sections over every affine chart. -/
theorem surjective_val_app_of_epi_of_kernel_isCartesian_of_essSurj'
    (hEss : ∀ (K : Modules.{u, u} B S hS F hF) (W : SmallEtale B S hS F),
      IsAffine (chartScheme W) → IsCartesianOnAffineCharts K →
      ∃ (M : (chartScheme W).Modules) (_ : M.IsQuasicoherent)
        (hM : Presheaf.IsSheaf ((SmallEtale.topology B S hS F).over W)
          (Stacks.Sites.associatedPresheaf (chartScheme W) M
            (SmallEtale.sliceToOver B S hS F W))),
        Nonempty (SmallEtale.sliceModule B S hS F hF W K ≅
          SmallEtale.sliceAssociatedModule B S hS F hF W M hM)) :
    ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)) :=
  surjective_val_app_of_epi_of_kernel_isCartesian_univ
    (isZero_cechCohomology_of_essSurj hEss)

end AlgebraicGeometry.Space

end
