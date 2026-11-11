module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GrauertRiemenschneider
public import StacksCore.Tactic.StacksAttribute

/-!
# The finiteness hypothesis of Grauert-Riemenschneider vanishing, discharged

`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_dualizingModule` of
`ResolutionOfSurfaces/Vanishing/GrauertRiemenschneider.lean` is [Stacks, Tag 0AXD] granted two
inputs of the source's proof: the finiteness of `H¹(X, ω_X)` over `A`, and the outcome of the
source's duality step. The first of those is proved here, and the resulting form of the tag,
carrying only the duality step, is stated below.

## Main results

* `AlgebraicGeometry.moduleFinite_firstCohomologySheafAsBaseModule`: for a proper morphism to the
  spectrum of a Noetherian ring and a coherent module, `H¹(X, ℱ)` is a finite module over that
  ring.
* `VanishingSituation.isZero_firstCohomology_dualizingModule_of_forall_linearMap_eq_zero`:
  [Stacks, Tag 0AXD] with the finiteness hypothesis discharged.

## Implementation notes

Finiteness is the sentence *if the proposition is false, then we can find a nonzero map
`R¹f_*ω_X → κ`* of the source's proof: a module admits a nonzero map to the residue field of a
local ring as soon as it is finite and nonzero. Since `ω_X` is coherent and `f` is proper, the
higher direct image is coherent ([Stacks, Tag 02O5]) and over the affine base its sections are
the cohomology.

## References

* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

-- `ModuleCat.hasDerivedCategory` of `Homology/DerivedCategory/LocallySmall.lean` arrives through
-- the imports above and instance search prefers a global instance to a file-local one, which
-- would elaborate `DerivedCategory (ModuleCat.{u} V.A)` at a different morphism universe from the
-- one `GrauertRiemenschneider.lean` states its theorem at. Removing it here restores that file's
-- instance environment, so the statement below is the statement there minus `hfin`.

universe u

namespace AlgebraicGeometry

/-- For a proper morphism to the spectrum of a Noetherian ring and a coherent module, the first
cohomology is a finite module over that ring.

The higher direct image of a coherent module under a proper morphism is coherent, and over an
affine base the sections of that coherent module are the cohomology. -/
public theorem moduleFinite_firstCohomologySheafAsBaseModule {A : Type u} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    Module.Finite A (firstCohomologySheafAsBaseModule X f ℱ) := by
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hΓ := ProperCoherenceWitness.moduleFinite_cohomology f ℱ 1
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  exact Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hsurj
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj ℱ))

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-- **Stacks Project, Tag 0AXD** (Grauert-Riemenschneider), with the finiteness hypothesis of
`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_dualizingModule` discharged. In the
vanishing situation of [Stacks, Tag 0AX8] with `X` normal and `A` Nagata carrying a dualizing
complex `ω_A^•`, the first cohomology of the dualizing module `ω_X` of `X` vanishes; over the
affine base `S = Spec(A)` this is `R¹f_*ω_X = 0`.

Finiteness of `H¹(X, ω_X)` over `A`, which is what lets a nonzero module be detected by a map to
`κ`, comes from coherence of the higher direct images under the proper morphism `f`
([Stacks, Tag 02O5]) and is `AlgebraicGeometry.moduleFinite_firstCohomologySheafAsBaseModule`.
The one hypothesis carried from the source's proof is `hvanish`, the outcome of its duality step,
in which a nonzero `R¹f_*ω_X → κ` is dualized by `RHom_A(-, ω_A^•)` into a nonzero
`κ[-1] → Rf_*𝒪_X` and contradicts [Stacks, Tag 0AXC]. The normalization of `ω_X` with respect to
`ω_A` is used by the source only inside that step and is subsumed in `hvanish`.

**No `@[stacks 0AXD]` attribute is placed here.** This form still carries `hvanish`, the
source's duality step, so it is not an unconditional statement of the tag; the registration is
`AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_of_properRightAdjoint_isoShiftTwo`
of `GrauertRiemenschneiderUnconditional.lean`. -/
public theorem isZero_firstCohomology_dualizingModule_of_forall_linearMap_eq_zero
    [IsNormal V.X] [IsLocallyNoetherian V.X]
    (hnag : IsNagataRing V.A)
    (ωA : DerivedCategory (ModuleCat.{u} V.A)) (hωA : Dualizing.IsDualizingComplex ωA)
    (ω : V.X.Modules) (hω : Stacks.Duality.IsDualizingModule ω)
    (hvanish : ∀ φ : firstCohomologySheafAsBaseModule V.X V.f ω →ₗ[V.A]
      IsLocalRing.ResidueField V.A, φ = 0) :
    IsZero (firstCohomologySheafAsBaseModule V.X V.f ω) := by
  -- A coherent module on a proper source has finite cohomology, which is what lets a nonzero
  -- module be detected by a map to the residue field.
  have : ω.IsCoherent := hω.1
  exact isZero_firstCohomology_dualizingModule V hnag ωA hωA ω hω
    (moduleFinite_firstCohomologySheafAsBaseModule V.f ω) hvanish

end VanishingSituation

end AlgebraicGeometry

end
