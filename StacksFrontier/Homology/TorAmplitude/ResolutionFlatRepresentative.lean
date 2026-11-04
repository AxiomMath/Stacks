module

public import StacksFrontier.Homology.KFlat.FreeResolution
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat representatives from Tor vanishing against free resolutions

Let `R` be a commutative ring and `P` a K-flat complex of `R`-modules. For a module `M` and a
free resolution `F → M[0]`, the total tensor product `P ⊗ F` computes the derived tensor
product `P ⊗^L M`. So if all the complexes `P ⊗ F` have cohomology in `[a, b]`, then `P` has
Tor amplitude in `[a, b]`, hence (Stacks 0654) is represented in `D(R)` by a complex of flat
modules concentrated in degrees `[a, b]`.

## Main results

* `StacksDraft.TorAmplitude.hasFlatRepresentative_of_isZero_homology_tensor`.

## References

* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

/-- **A flat representative from Tor vanishing against free resolutions.** Let `P` be a K-flat
complex of `R`-modules such that `P ⊗ F` has vanishing cohomology outside `[a, b]` for every
free resolution `F → M[0]` of a module `M` by a K-flat complex of free modules concentrated in
degrees `≤ 0`. Then `P` is represented in
`D(R)` by a complex of flat modules concentrated in degrees `[a, b]`: for a module `M`, a free
resolution `F → M[0]` (Stacks 064K) computes `P ⊗^L M` as `P ⊗ F`, so `P` has Tor amplitude in
`[a, b]` (Stacks 0654). -/
@[sga "6 I 5.4" "Necessity direction"]
theorem hasFlatRepresentative_of_isZero_homology_tensor {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (a b : ℤ)
    (h : ∀ (M : ModuleCat.{u} R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
      (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M), QuasiIso f →
        F.KFlat → F.IsStrictlyLE 0 → (∀ n : ℤ, Module.Free R (F.X n)) → ∀ i : ℤ,
          i ∉ Set.Icc a b → IsZero ((P ⊗ F).homology i)) :
    HasFlatRepresentative (DerivedCategory.Q.obj P) a b := by
  refine (hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) _ a b).1 fun M i hi => ?_
  obtain ⟨F, f, hF, hFle, hFfree, hf⟩ := CochainComplex.KFlat.exists_free_kFlat_resolution M
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  let e₁ : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ≅ DerivedCategory.Q.obj F :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app M ≪≫ (asIso (DerivedCategory.Q.map f)).symm
  exact ((h M F f hf hF hFle hFfree i hi).of_iso
    ((DerivedCategory.homologyFunctorFactors _ i).app _)).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((T.tensor.obj (DerivedCategory.Q.obj P)).mapIso e₁ ≪≫ T.comparison P F hP hF))

end StacksDraft.TorAmplitude

end
