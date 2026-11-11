module

public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.GradedConsequence
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.GradedTwistComparison
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackLocallySurjective
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ScalarIdentity
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.SchemePropertiesPermanence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# [Stacks, Tag 0897]

Let `A` be a Noetherian ring, `B` a finitely generated graded `A`-algebra, `f : X ⟶ Spec A` a
proper morphism and `𝓑 = f^* B̃`. Let `F` be a quasi-coherent graded `𝓑`-module of finite type.
Then the graded `B`-module `Hᵖ(X, F) = ⨁ₙ Hᵖ(X, Fₙ)` is a finite `B`-module for every `p`.

**This file proves that**, with nothing assumed beyond the source's own hypotheses: the base
change of the source's proof is built as the relative spectrum `X' = Spec_X(𝓑)`, its structure
morphism `f' : X' ⟶ Spec B` is proper
(`Stacks.AlgebraicGeometry.GradedProperCohomology.isProper_pullbackStructureHom`), and the scalar
identity tying `f'` to the graded sections of `𝓑` is
`HomogeneousSections.isScalarIdentity_structureHom`.

Part (2) says: if `L` is an ample invertible `𝒪_X`-module there is a `d₀` with
`Hᵖ(X, Fₙ ⊗ L^{⊗d}) = 0` for every `p > 0`, every `d ≥ d₀` and every graded degree `n` at once.
**This file proves that too**, from the same base change: `F'` is coherent, `π^* L` is ample
relative to `f'`, [Stacks, Tag 02O1] gives the bound upstairs, [Stacks, Tag 01XK] turns the
vanishing of the higher direct image into the vanishing of the cohomology upstairs, and
`GradedQcohAlgebra.isZero_pieceTwist_of_isZero_baseChangeTwist` transports it to `X`.

## Main results

* `Stacks.AlgebraicGeometry.GradedProperCohomology.moduleFinite_gradedCohomologySum_pullback`:
  **[Stacks, Tag 0897] part (1).**
* `Stacks.AlgebraicGeometry.GradedProperCohomology.exists_isZero_pieceTwistCohomology_pullback`:
  **[Stacks, Tag 0897] part (2).**
* `moduleFinite_gradedCohomologySum_and_exists_isZero_pieceTwistCohomology`: **the whole tag**,
  and the one declaration registered to Tag 0897. The forms of the two parts that take the
  base change `X'`, `f'`, `F'` and the cohomology comparison as arguments
  (`exists_isZero_pieceTwistCohomology` in `Basic`, `moduleFinite_gradedCohomologySum` in
  `ProperCohomologyFiniteness`, `moduleFinite_gradedCohomologySum_gradedPullback` in
  `ProperCohomologyFinitenessSupplement`) are not registered.

## Implementation notes

Part (2) is proved here rather than obtained from
`Stacks.AlgebraicGeometry.GradedProperCohomology.exists_isZero_pieceTwistCohomology'` because
that statement renders the source's "of finite type" as
`Stacks.Coherent.IsFiniteTypeOnAffine` — the affine-local predicate [Stacks, Tag 087Z] produces,
where it is inert — while part (1) consumes `SheafOfModules.GradedModule.IsFiniteType`, the
covering-family predicate of [Stacks, Tag 03DL] part (5). The tag has **one** finiteness
hypothesis, so the whole statement must carry one; it is the latter, because it is the one that
does work, namely in making `F'` coherent.

Neither predicate is proved to imply the other in this tree. The implication from the
affine-local predicate to the covering-family one holds for a graded module with
quasi-coherent pieces, by this argument: the sections of a quasi-coherent homogeneous piece on a
basic open of an affine open are the sections over that affine open localized
([Stacks, Tag 01P7]), so generation over an affine open descends to the opens below it, which is
what `SheafOfModules.GradedModule.Generates` asks for beyond the affine-local statement. Once
that implication is written, a caller holding `Stacks.Coherent.IsFiniteTypeOnAffine` together
with `hqc` meets `hft`, and the theorems here apply to it. The choice of `hft` does not weaken
the statement: the covering-family predicate is the source's definition of finite type.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open scoped DirectSum AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  (𝒜 : ℕ → Submodule A B) [_root_.GradedAlgebra 𝒜] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **A scheme proper over an affine scheme is quasi-compact and quasi-separated**: an affine
scheme is, and a proper morphism is quasi-compact and separated. -/
theorem compactSpace_and_quasiSeparatedSpace_of_isProper
    [_root_.AlgebraicGeometry.IsProper f] :
    CompactSpace (X : Type u) ∧ QuasiSeparatedSpace (X : Type u) :=
  (quasiCompact_and_quasiSeparated_iff f).1 ⟨inferInstance, inferInstance⟩

/-- **[Stacks, Tag 0897] part (1).** Let `A` be a Noetherian ring, `B` a finitely generated
graded `A`-algebra, `f : X ⟶ Spec A` proper, `𝓑 = f^* B̃` and `F` a quasi-coherent graded
`𝓑`-module of finite type. Then the graded `B`-module `⨁ₙ Hᵖ(X, Fₙ)` is a finite `B`-module, for
every `p`.

The `B`-module structure is `HomogeneousSections.gradedCohomologyModule` for the
homogeneous-sections datum of `𝓑 = f^* B̃`: a homogeneous `b ∈ 𝒜ₖ` acts on the degree-`n`
summand by `Hᵖ(X, −)` of multiplication by the global section of `𝓑ₖ` it names, landing in the
degree-`n + k` summand. -/
theorem moduleFinite_gradedCohomologySum_pullback [IsNoetherianRing A] [Algebra.FiniteType A B]
    [_root_.AlgebraicGeometry.IsProper f]
    (F : _root_.SheafOfModules.GradedModule.{u, u, u} (pullbackGradedAlg 𝒜 f))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent)
    (hft : F.IsFiniteType) (p : ℕ) :
    letI := (pullbackHomogeneousSections 𝒜 f).gradedCohomologyModule F p
    Module.Finite B (gradedCohomologySum F p) := by
  have hqcs := compactSpace_and_quasiSeparatedSpace_of_isProper f
  have := hqcs.1
  have := hqcs.2
  have : _root_.AlgebraicGeometry.IsProper (pullbackStructureHom 𝒜 f) :=
    isProper_pullbackStructureHom 𝒜 f ‹_root_.AlgebraicGeometry.IsProper f›
  exact moduleFinite_gradedCohomologySum_of_scalarIdentity (pullbackGradedQcoh 𝒜 f)
    (pullbackHomogeneousSections 𝒜 f) F hqc p f hft (pullbackStructureHom 𝒜 f)
    (HomogeneousSections.isScalarIdentity_structureHom (pullbackGradedQcoh 𝒜 f)
      (pullbackHomogeneousSections 𝒜 f) f (isStructureCompatible_pullbackGradedQcoh 𝒜 f))

/-- `X' = Spec_X(f^* B̃)` is locally Noetherian, because `f' : X' ⟶ Spec B` is proper and `B` is
Noetherian. This is what makes `F'` coherent. -/
theorem isLocallyNoetherian_relSpec [IsNoetherianRing A] [Algebra.FiniteType A B]
    [_root_.AlgebraicGeometry.IsProper f] :
    IsLocallyNoetherian (pullbackGradedQcoh 𝒜 f).relSpec.left :=
  have hBN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of B)) :=
    _root_.AlgebraicGeometry.isLocallyNoetherian_Spec.mpr hBN
  have : _root_.AlgebraicGeometry.IsProper (pullbackStructureHom 𝒜 f) :=
    isProper_pullbackStructureHom 𝒜 f ‹_root_.AlgebraicGeometry.IsProper f›
  _root_.AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    (pullbackStructureHom 𝒜 f)

/-- **[Stacks, Tag 0897] part (2).** Let `A` be a Noetherian ring, `B` a finitely generated
graded `A`-algebra, `f : X ⟶ Spec A` proper, `𝓑 = f^* B̃`, `F` a quasi-coherent graded
`𝓑`-module of finite type and `L` an ample invertible `𝒪_X`-module. Then there is a `d₀` such
that

`Hᵖ(X, Fₙ ⊗ L^{⊗d}) = 0` for every `p > 0`, every `d ≥ d₀` and **every** graded degree `n`,

the uniformity in `n` being the whole point.

The base change of the source's proof is supplied: `F'` on `X' = Spec_X(𝓑)` is coherent because
`X'` is locally Noetherian (`isLocallyNoetherian_relSpec`) and `F` is of finite type, `π^* L` is
ample on `X'` because `π` is affine ([Stacks, Tag 0892] part (2)) hence ample relative to `f'`
because `Spec B` is affine ([Stacks, Tag 01VK]), [Stacks, Tag 02O1] gives the bound upstairs with
no hypothesis (`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.vanishingOverAffineBase`),
[Stacks, Tag 01XK] turns the vanishing of `Rᵖ f'_*` into that of `Hᵖ(X', −)`, and
`GradedQcohAlgebra.isZero_pieceTwist_of_isZero_baseChangeTwist` transports it to `X`. -/
@[ega "III 2.4.2" "special case"]
theorem exists_isZero_pieceTwistCohomology_pullback [IsNoetherianRing A]
    [Algebra.FiniteType A B] [_root_.AlgebraicGeometry.IsProper f]
    (F : _root_.SheafOfModules.GradedModule.{u, u, u} (pullbackGradedAlg 𝒜 f))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent) (hft : F.IsFiniteType)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (cohomologyOf X p (pieceTwist F L n (d : ℤ))) := by
  have hBN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hSN : _root_.AlgebraicGeometry.IsNoetherian (Spec (.of B)) :=
    _root_.AlgebraicGeometry.isNoetherian_Spec.mpr hBN
  have hf' : _root_.AlgebraicGeometry.IsProper (pullbackStructureHom 𝒜 f) :=
    isProper_pullbackStructureHom 𝒜 f ‹_root_.AlgebraicGeometry.IsProper f›
  have hF'c : ((pullbackGradedQcoh 𝒜 f).baseChangeModule F hqc).IsCoherent :=
    (pullbackGradedQcoh 𝒜 f).isCoherent_baseChangeModule F hqc
      (isLocallyNoetherian_relSpec 𝒜 f) hft
  -- `π^* L` is ample on `X'`, hence ample relative to `f'`
  have hL' : Stacks.RelativeAmple.IsRelativelyAmple (pullbackStructureHom 𝒜 f)
      (Stacks.AmpleLocallyClosed.pullbackModule (pullbackGradedQcoh 𝒜 f).relSpec.hom L) :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
      (pullbackStructureHom 𝒜 f) _).mpr
      (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom
        (pullbackGradedQcoh 𝒜 f).relSpec.hom L hL)
  obtain ⟨d₀, hd₀⟩ :=
    RelativeAmpleTwistVanishing.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
      Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.vanishingOverAffineBase.{u}
      (pullbackStructureHom 𝒜 f) ((pullbackGradedQcoh 𝒜 f).baseChangeModule F hqc)
      (Stacks.AmpleLocallyClosed.pullbackModule (pullbackGradedQcoh 𝒜 f).relSpec.hom L) hL'
  refine ⟨d₀, fun d hd p hp => ?_⟩
  refine (pullbackGradedQcoh 𝒜 f).isZero_pieceTwist_of_isZero_baseChangeTwist F hqc L
    (pullbackStructureHom 𝒜 f) p d ?_
  -- the twist upstairs, and its quasi-coherence
  have hGqc : (tensorModules (pullbackGradedQcoh 𝒜 f).relSpec.left
      ((pullbackGradedQcoh 𝒜 f).baseChangeModule F hqc)
      (tensorPowModule (pullbackGradedQcoh 𝒜 f).relSpec.left
        (Stacks.AmpleLocallyClosed.pullbackModule
          (pullbackGradedQcoh 𝒜 f).relSpec.hom L) (d : ℤ))).IsQuasicoherent :=
    RelativeAmpleTwistVanishing.isQuasicoherent_tensorPowTwist
      ((pullbackGradedQcoh 𝒜 f).baseChangeModule F hqc) _ (d : ℤ)
  -- the derived categories, at the universe the two comparisons below are stated at
  let : HasDerivedCategory.{u + 1} (pullbackGradedQcoh 𝒜 f).relSpec.left.Modules :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u} ↥Γ((pullbackGradedQcoh 𝒜 f).relSpec.left, ⊤)) :=
    HasDerivedCategory.standard _
  -- [Stacks, Tag 02O1]: the higher direct image vanishes, and with it its global sections
  have hz0 := Functor.map_isZero
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (Spec (.of B))) (hd₀ d p hd hp)
  -- [Stacks, Tag 01XK]: those global sections are the cohomology upstairs
  have hz1 := hz0.of_iso
    ((Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward
      (pullbackStructureHom 𝒜 f) (p : ℤ)).app ⟨_, hGqc⟩)
  -- passing from the `ℤ`-indexed to the `ℕ`-indexed derived functor
  exact hz1.of_iso
    ((ModuleCat.restrictScalars (pullbackStructureHom 𝒜 f).appTop.hom).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Stacks.Cohomology.AffineBase.moduleGlobalSections
          (pullbackGradedQcoh 𝒜 f).relSpec.left) p).app _))

/-- **[Stacks, Tag 0897].** Let `A` be a Noetherian ring, `B` a finitely generated graded
`A`-algebra, `f : X ⟶ Spec A` a proper morphism and `𝓑 = f^* B̃`. Let `F` be a quasi-coherent
graded `𝓑`-module of finite type. Then

1. for every `p` the graded `B`-module `Hᵖ(X, F) = ⨁ₙ Hᵖ(X, Fₙ)` is a finite `B`-module, and
2. if `L` is an ample invertible `𝒪_X`-module there is a `d₀` with
   `Hᵖ(X, Fₙ ⊗ L^{⊗d}) = 0` for all `p > 0` and all `d ≥ d₀`, uniformly in the graded degree
   `n`.

The `B`-module structure in (1) is `HomogeneousSections.gradedCohomologyModule` for the
homogeneous-sections datum of `𝓑 = f^* B̃`: a homogeneous `b ∈ 𝒜ₖ` carries the degree-`n` summand
to the degree-`n + k` summand by `Hᵖ(X, −)` of multiplication by the global section of `𝓑ₖ` that
`b` names. -/
@[stacks 0897 "both parts, at the hypotheses of the source: A Noetherian, B a finitely \
generated graded A-algebra, f : X → Spec A proper, F a quasi-coherent graded f^* B-tilde-module \
of finite type, and L ample invertible in part (2); (1) is finiteness of ⨁_n H^p(X, F_n) over B \
for the degreewise B-action, (2) is H^p(X, F_n ⊗ L^d) = 0 for p > 0, d ≥ d_0 and every \
degree n, which is H^p(X, F ⊗ L^d) = 0 since cohomology on X commutes with direct sums",
  sga "2 XII 5.8" "(i), special case"]
theorem moduleFinite_gradedCohomologySum_and_exists_isZero_pieceTwistCohomology
    [IsNoetherianRing A] [Algebra.FiniteType A B] [_root_.AlgebraicGeometry.IsProper f]
    (F : _root_.SheafOfModules.GradedModule.{u, u, u} (pullbackGradedAlg 𝒜 f))
    (hqc : ∀ n : ℤ, (pieceModule F n).IsQuasicoherent) (hft : F.IsFiniteType) :
    (letI := (pullbackHomogeneousSections 𝒜 f).gradedCohomologyModule F
     ∀ p : ℕ, Module.Finite B (gradedCohomologySum F p)) ∧
      ∀ (L : X.Modules) (_ : IsInvertibleModule X L), IsAmple X L →
        ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
          IsZero (cohomologyOf X p (pieceTwist F L n (d : ℤ))) :=
  ⟨fun p => moduleFinite_gradedCohomologySum_pullback 𝒜 f F hqc hft p,
    fun L hinv hL =>
      let := hinv
      exists_isZero_pieceTwistCohomology_pullback 𝒜 f F hqc hft L hL⟩

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
