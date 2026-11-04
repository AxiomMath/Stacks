module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimension
public import StacksFrontier.Homology.Perfect.Defs

/-!
# Boundedness and perfectness of crystalline cohomology: the statements of 07MR, 07MX and 07MY

Three remarks of the chapter assert something about the size of the crystalline cohomology of a
crystal `F` in quasi-coherent `𝒪_{X/S}`-modules:

* [Stacks, Tag 07MR] bounds the degrees in which `H^i(Cris(X/S), F)` is nonzero, in two ways: by
  `d + e` with `d` the dimension of `X` and `e` the embedding dimension of `X/S₀`, and by `q + e`
  with `q` the number of affines in a cover of a separated `X`;
* [Stacks, Tag 07MX] asserts that `RΓ(Cris(X/S), F)` is a perfect object of `D(A)` when `X/S₀` is
  proper and smooth, `F` is a crystal in finite locally free modules and `p` is nilpotent in `A`;
* [Stacks, Tag 07MY] asserts the same with `p` nilpotent only in `A/I` and `A` `p`-adically
  complete.

We state all three as propositions, about the cohomology `moduleULiftCohomology` and the derived
global sections `moduleULiftDerivedGlobalSections` of a sheaf of `𝒪_{X/S}`-modules. Situation
[Stacks, Tag 07MF] is `Crystalline.GlobalCrystallineSituation`, and every further assumption of the
remarks is an explicit hypothesis of the propositions. A crystal in quasi-coherent modules is a
sheaf satisfying `SheafOfModules.IsQuasicoherentOnSite`, form (1) of [Stacks, Tag 07IT], and a
crystal in finite locally free quasi-coherent modules is one satisfying
`IsFiniteLocallyFreeQuasicoherentCrystal`. That `S₀` has a unique point is `Subsingleton` and
`Nonempty` on its carrier; that `X → S₀` is of finite presentation is
`LocallyOfFinitePresentation`, `QuasiCompact` and `QuasiSeparated` ([Stacks, Tag 01TQ]); and that
`p` is nilpotent in `A/I` is the nilpotence of `p` in `Γ(S₀, 𝒪_{S₀})`.

We also state the abelian form of [Stacks, Tag 07MR], with the `A`-module `H^i(Cris(X/S), F)`
replaced by the cohomology of the abelian sheaf underlying `F`, and show that [Stacks, Tag 07MR]
follows from it together with the vanishing-transfer form of [Stacks, Tag 03FD].

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `Vanishing07MR`: the statement of [Stacks, Tag 07MR], both clauses.
* `AbelianVanishing07MR`: the same two clauses for the cohomology of the abelian sheaf underlying
  `F`.
* `VanishingTransfer03FD`: the implication of [Stacks, Tag 03FD] that carries vanishing of the
  abelian cohomology of a module to vanishing of its module cohomology.
* `Perfect07MX`: the statement of [Stacks, Tag 07MX].
* `Perfect07MY`: the statement of [Stacks, Tag 07MY].

## Main results

* `isZero_moduleULiftCohomology_of_subsingleton_cohomology`: under `VanishingTransfer03FD`,
  vanishing of the abelian cohomology of `F` in degree `j` gives vanishing of its module
  cohomology in degree `j`.
* `vanishing07MR_of_abelianVanishing07MR`: `Vanishing07MR` follows from `AbelianVanishing07MR`
  together with `VanishingTransfer03FD`.

## References

* [Stacks Project, Tag 07MR](https://stacks.math.columbia.edu/tag/07MR)
* [Stacks Project, Tag 07MX](https://stacks.math.columbia.edu/tag/07MX)
* [Stacks Project, Tag 07MY](https://stacks.math.columbia.edu/tag/07MY)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
* [Stacks Project, Tag 01TQ](https://stacks.math.columbia.edu/tag/01TQ)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/



@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The statement of [Stacks, Tag 07MR] -/

/-- The statement of [Stacks, Tag 07MR]. In Situation [Stacks, Tag 07MF], with `S₀` a one-point
scheme and `X → S₀` of finite presentation, let `F` be a crystal in quasi-coherent
`𝒪_{X/S}`-modules. Then

1. if `dim X = d` and `X/S₀` has embedding dimension at most `e`, the cohomology
   `H^i(Cris(X/S), F)` vanishes for `i > d + e`, and
2. if `X` is separated and covered by `q` affine opens and `X/S₀` has embedding dimension at most
   `e`, the cohomology `H^i(Cris(X/S), F)` vanishes for `i > q + e`.

The dimension of `X` is its topological Krull dimension, `topologicalKrullDim`, which is the
dimension of a scheme in the sense of [Stacks, Tag 0055]; the embedding dimension is
`AlgebraicGeometry.Scheme.Hom.HasEmbeddingDimensionLE`, the existence of a local closed immersion
over `S₀` into something smooth of relative dimension `e`. The cohomology is
`moduleULiftCohomology`, the `A`-module `H^i(Cris(X/S), F)`. -/
def Vanishing07MR (S : GlobalCrystallineSituation.{u}) : Prop :=
  Subsingleton ↥(DividedPowerScheme.closedFiber S.S) →
    Nonempty ↥(DividedPowerScheme.closedFiber S.S) →
      LocallyOfFinitePresentation S.toClosedFiber → QuasiCompact S.toClosedFiber →
        QuasiSeparated S.toClosedFiber →
          ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
              (∀ d e : ℕ, topologicalKrullDim ↥S.X = (d : WithBot ℕ∞) →
                  S.toClosedFiber.HasEmbeddingDimensionLE e →
                    ∀ i : ℕ, d + e < i → IsZero (moduleULiftCohomology S F i)) ∧
                ∀ q e : ℕ, Scheme.IsSeparated S.X →
                  (∃ U : Fin q → S.X.Opens, (∀ k, IsAffineOpen (U k)) ∧ (⨆ k, U k) = ⊤) →
                    S.toClosedFiber.HasEmbeddingDimensionLE e →
                      ∀ i : ℕ, q + e < i → IsZero (moduleULiftCohomology S F i)

/-! ### The abelian form of [Stacks, Tag 07MR], and the comparison it needs -/

/-- The vanishing-transfer form of [Stacks, Tag 03FD] at the small crystalline site: if the
abelian-valued `R^j Γ(Cris(X/S), -)` of the abelian sheaf underlying a sheaf of
`𝒪_{X/S}`-modules vanishes, then so does the module-valued `H^j(Cris(X/S), -)` of that module. -/
def VanishingTransfer03FD (S : GlobalCrystallineSituation.{u}) : Prop :=
  ∀ (M : ModuleSheaf S) (j : ℕ),
    IsZero (((globalSections S).rightDerived j).obj ((toAbelianSheaf S).obj M)) →
      IsZero (moduleCohomology S M j)

/-- Under `VanishingTransfer03FD`, vanishing of the abelian-valued `H^j(Cris(X/S), F)` of the
abelian sheaf underlying `F` gives vanishing of the `A`-module `H^j(Cris(X/S), F)`. -/
theorem isZero_moduleULiftCohomology_of_subsingleton_cohomology
    (S : GlobalCrystallineSituation.{u}) (h : VanishingTransfer03FD S)
    (F : SheafOfModules.{u} (structureSheaf S)) (j : ℕ)
    (hF : Subsingleton (cohomology S (abelianSheaf F) j)) :
    IsZero (moduleULiftCohomology S F j) :=
  h ((moduleULift S).obj F) j
    ((subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections S (abelianSheaf F) j).1 hF)

/-- The abelian form of [Stacks, Tag 07MR]: both clauses of `Vanishing07MR`, with the `A`-module
`H^i(Cris(X/S), F)` replaced by the abelian group `H^i(Cris(X/S), -)` of the abelian sheaf
underlying `F`, under the same hypotheses. -/
def AbelianVanishing07MR (S : GlobalCrystallineSituation.{u}) : Prop :=
  Subsingleton ↥(DividedPowerScheme.closedFiber S.S) →
    Nonempty ↥(DividedPowerScheme.closedFiber S.S) →
      LocallyOfFinitePresentation S.toClosedFiber → QuasiCompact S.toClosedFiber →
        QuasiSeparated S.toClosedFiber →
          ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
              (∀ d e : ℕ, topologicalKrullDim ↥S.X = (d : WithBot ℕ∞) →
                  S.toClosedFiber.HasEmbeddingDimensionLE e →
                    ∀ i : ℕ, d + e < i → Subsingleton (cohomology S (abelianSheaf F) i)) ∧
                ∀ q e : ℕ, Scheme.IsSeparated S.X →
                  (∃ U : Fin q → S.X.Opens, (∀ k, IsAffineOpen (U k)) ∧ (⨆ k, U k) = ⊤) →
                    S.toClosedFiber.HasEmbeddingDimensionLE e →
                      ∀ i : ℕ, q + e < i → Subsingleton (cohomology S (abelianSheaf F) i)

/-- [Stacks, Tag 07MR] follows from its abelian form `AbelianVanishing07MR` together with the
vanishing transfer `VanishingTransfer03FD` of [Stacks, Tag 03FD]. -/
theorem vanishing07MR_of_abelianVanishing07MR (S : GlobalCrystallineSituation.{u})
    (h03FD : VanishingTransfer03FD S) (hab : AbelianVanishing07MR S) : Vanishing07MR S := by
  intro hsub hne hfp hqc hqs F hqcoh
  obtain ⟨hone, htwo⟩ := hab hsub hne hfp hqc hqs F hqcoh
  exact ⟨fun d e hdim he i hi ↦ isZero_moduleULiftCohomology_of_subsingleton_cohomology S h03FD F i
      (hone d e hdim he i hi),
    fun q e hsep hcov he i hi ↦ isZero_moduleULiftCohomology_of_subsingleton_cohomology S h03FD F i
      (htwo q e hsep hcov he i hi)⟩

/-! ### The statements of [Stacks, Tag 07MX] and [Stacks, Tag 07MY] -/

section Perfectness

variable (S : GlobalCrystallineSituation.{u}) [HasDerivedCategory.{w} (ModuleSheaf S)]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- The statement of [Stacks, Tag 07MX]. Let `(A, I, γ)` be the divided power base of a global
crystalline situation with `S = Spec(A)` affine and `p` nilpotent in `A`, let `X` be proper and
smooth over `S₀ = Spec(A/I)`, and let `F` be a crystal in finite locally free quasi-coherent
`𝒪_{X/S}`-modules. Then `RΓ(Cris(X/S), F)` is a perfect object of `D(A)`.

The derived global sections are
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULiftDerivedGlobalSections`, an object of
`D⁺(Mod_A)`; perfectness is `StacksDraft.Perfect.IsPerfect`, which is [Stacks, Tag 0657] part (1)
and is a condition on an object of `D(A)`, so the bounded below object is carried into `D(A)`
along `CategoryTheory.DerivedCategory.Plus.ι`. A crystal in finite locally free quasi-coherent
`𝒪_{X/S}`-modules is a sheaf satisfying `IsFiniteLocallyFreeQuasicoherentCrystal`, the predicate of
[Stacks, Tag 07IU]. -/
def Perfect07MX : Prop :=
  IsAffine S.S.scheme → IsNilpotent (S.p : Γ(S.S.scheme, ⊤)) →
    IsProper S.toClosedFiber → Smooth S.toClosedFiber →
      ∀ F : SheafOfModules.{u} (structureSheaf S),
        IsFiniteLocallyFreeQuasicoherentCrystal F →
          StacksDraft.Perfect.IsPerfect
            (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections S F))

/-- The statement of [Stacks, Tag 07MY]. Let `(A, I, γ)` be the divided power base of a global
crystalline situation with `S = Spec(A)` affine, `A` `p`-adically complete and `p` nilpotent in
`A/I`, let `X` be proper and smooth over `S₀ = Spec(A/I)`, and let `F` be a crystal in finite
locally free quasi-coherent `𝒪_{X/S}`-modules. Then `RΓ(Cris(X/S), F)` is a perfect object of
`D(A)`. Here `p`-adic completeness is `IsAdicComplete` for the ideal generated by `p`, and `A/I`
is `Γ(S₀, 𝒪_{S₀})`. -/
def Perfect07MY : Prop :=
  IsAffine S.S.scheme →
    IsAdicComplete (Ideal.span {(S.p : Γ(S.S.scheme, ⊤))}) ↥Γ(S.S.scheme, ⊤) →
      IsNilpotent (S.p : Γ(DividedPowerScheme.closedFiber S.S, ⊤)) →
        IsProper S.toClosedFiber → Smooth S.toClosedFiber →
          ∀ F : SheafOfModules.{u} (structureSheaf S),
            IsFiniteLocallyFreeQuasicoherentCrystal F →
              StacksDraft.Perfect.IsPerfect
                (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections S F))

end Perfectness

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
