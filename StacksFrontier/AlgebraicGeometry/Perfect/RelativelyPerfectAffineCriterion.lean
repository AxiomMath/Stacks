module

public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Perfect.InverseImageTorAmplitudeStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionNestedRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Relative perfectness is tested on affine charts

Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation, and
let `E` be an object of `D_QCoh(𝒪_X)`. Then `E` is `S`-perfect (Stacks 0DI0) exactly when, for
every affine open `U ⊆ X` mapping into an affine open `V ⊆ S`, the complex `RΓ(U, E)` is
`𝒪_S(V)`-perfect (Stacks 0DHS), and it is enough to check this on the members of an affine open
covering of `S` and of affine open coverings of their preimages. This is Stacks 0DI2.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae`: **Stacks 0DI2.**

## Implementation notes

`S`-perfectness is `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` at the canonical family
of derived tensor products of Stacks 06YU on the open subspaces of `(X, f⁻¹𝒪_S)`,
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`. The module-side
condition is `AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect`, whose `Γ(S, V)`-algebra
structure on `Γ(X, U)` is the chart ring map `f.appLE V U e`.

On one chart the module-side condition is the conjunction of the two sheaf-side conditions,
pseudo-coherence of `E|_U` and finite Tor dimension of `E|_U` over `f⁻¹𝒪_S`
(`AlgebraicGeometry.Scheme.Hom.sectionsRelativelyPerfect_iff` with
`AlgebraicGeometry.Scheme.Hom.chartTorSpellingsAgree`). The three implications are then the
affine-locality statements of the two conjuncts: for pseudo-coherence
`AlgebraicGeometry.pseudoCoherent_derivedSections_tfae`, and for Tor dimension
`AlgebraicGeometry.Scheme.Hom.chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension` and
`AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimension_of_exists_affineCovering`.

## References

* [The Stacks Project, Lemma 36.35.3 (0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [The Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [The Stacks Project, Definition 15.85.1 (0DHS)](https://stacks.math.columbia.edu/tag/0DHS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks 0DI2.** Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite
presentation, and let `E` be an object of the derived category of `𝒪_X`-modules all of whose
cohomology sheaves are quasi-coherent. The following are equivalent:

1. `E` is `S`-perfect;
2. for every affine open `U ⊆ X` mapping into an affine open `V ⊆ S`, the complex `RΓ(U, E)` is
   `𝒪_S(V)`-perfect;
3. there are an affine open covering `S = ⋃ V i` and, for each `i`, an affine open covering
   `f⁻¹(V i) = ⋃ U i j` such that `RΓ(U i j, E)` is `𝒪_S(V i)`-perfect.

`S`-perfectness is read at the derived tensor product of Stacks 06YU on the open subspaces of
`(X, f⁻¹𝒪_S)`, and `𝒪_S(V)`-perfectness of `RΓ(U, E)` is Stacks 0DHS for the chart ring map
`f.appLE V U e`, which is flat and of finite presentation. -/
@[stacks 0DI2]
public theorem isPerfectRelativeTo_tfae [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    List.TFAE
      [IsPerfectRelativeTo f
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
            (RingedSpace.inverseImage S.toRingedSpace f.base)) E,
        ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
          (e : U ≤ f ⁻¹ᵁ V), SectionsRelativelyPerfect f E hV hU e,
        ∃ (ι : Type u) (V : ι → S.affineOpens),
          (⨆ i, (V i : S.Opens)) = ⊤ ∧
            ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens) (hle : ∀ j, (U j).1 ≤ f ⁻¹ᵁ (V i).1),
              (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
                ∀ j, SectionsRelativelyPerfect f E (V i).2 (U j).2 (hle j)] := by
  have key : ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), SectionsRelativelyPerfect f E hV hU e ↔
        (RingedSpace.IsPseudoCoherent
            ((RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E) ∧
          ChartHasFiniteTorDimension f
            (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
              (RingedSpace.inverseImage S.toRingedSpace f.base)) E U) :=
    fun U hU V hV e =>
      sectionsRelativelyPerfect_iff f E hE hV hU e (chartTorSpellingsAgree f E V U e)
  have hpc := pseudoCoherent_derivedSections_tfae f E hE
  have h12 := hpc.out 1 2
  have h31 := hpc.out 3 1
  tfae_have 1 → 2 := by
    rintro ⟨hp, ht⟩ U hU V hV e
    refine (key U hU V hV e).2 ⟨?_, chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension
      f E ht U hU⟩
    exact (isPseudoCoherent_derivedRestrictModules_iff_derivedSections E hE hU).2
      (h12.1 hp U hU V hV e)
  tfae_have 2 → 3 := exists_affineCovering_sectionsRelativelyPerfect f E
  tfae_have 3 → 1 := by
    rintro ⟨ι, V, hVtop, hcov⟩
    choose κ U hle hUtop hU using hcov
    refine ⟨h31.1 ⟨ι, V, hVtop, fun i =>
      ⟨κ i, U i, hUtop i, fun j => (hU i j).isPseudoCoherent⟩⟩, ?_⟩
    exact locallyHasFiniteTorDimension_of_exists_affineCovering f _ E ⟨ι, V, hVtop, fun i =>
      ⟨κ i, U i, hUtop i, fun j => ((key _ (U i j).2 _ (V i).2 (hle i j)).1 (hU i j)).2⟩⟩
  tfae_finish

end AlgebraicGeometry.Scheme.Hom

end
