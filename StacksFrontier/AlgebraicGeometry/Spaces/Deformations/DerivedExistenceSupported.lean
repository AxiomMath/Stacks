module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentPushforwardSupported
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorSupportClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPerfectPushforwardPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedHigherDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeAbsoluteChartDictionary

/-!
# Grothendieck's existence theorem in its derived form, with supports proper over the base

Let `(Aₙ)` be an inverse system of rings with surjective transitions whose kernels are locally
nilpotent, `A = lim Aₙ`, `X` an algebraic space separated, flat and of finite presentation over
`A`, and `Xₙ = X ×_{Spec A} Spec Aₙ`. Let `Kₙ ∈ D(𝒪_{Xₙ})` be pseudo-coherent (equivalently, `Xₙ`
being flat and of finite presentation over `Aₙ`, pseudo-coherent relative to `Aₙ`, Stacks 0DII),
supported on a closed subset `Zₙ ⊆ |Xₙ|` proper over `Aₙ`, with isomorphisms
`Liₙ^* Kₙ₊₁ ≅ Kₙ`. Then there is `K ∈ D(𝒪_X)`, pseudo-coherent relative to `A`, with isomorphisms
`Ljₙ^* K ≅ Kₙ` compatible with the given ones. This is the generalization of Stacks 0DIQ proposed
in Stacks 0DIR, for `X` flat over `A`.

The proof is the source's proof of 0DIQ. Properness of `X` enters that proof only through the
pseudo-coherence of `Mₙ = RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` for perfect `E`; here it comes from the supports:
`Lpₙ^*E ⊗^L Kₙ` is pseudo-coherent and supported on `Zₙ`, which lies in a closed subspace
`Wₙ ⊆ Xₙ` of finite presentation proper over `Aₙ`; approximation by perfect complexes supported on
`|Wₙ|` (Stacks 08HP) reduces the claim to perfect objects supported on `|Wₙ|`, whose direct images
are pseudo-coherent by Noetherian approximation.

## On the support of `K`

The source also asserts that `K` is supported on a closed subset of `|X|` proper over `A`. That
assertion fails: over `A = ℤ_p`, `Aₙ = ℤ/pⁿ`, `X = 𝔸¹_A = Spec A[x]`, the system
`Kₙ = ⊕_{i ≥ 0} 𝒪_{Xₙ}/(x - pⁱ)[i]` satisfies every hypothesis (each `Kₙ` is supported on
`V(x) ⊆ Xₙ`, finite over `Aₙ`), but every pseudo-coherent `K` with `Ljₙ^* K ≅ Kₙ` compatibly is
`⊕ 𝒪_X/(x - pⁱ)[i]`, whose support is not contained in any closed subset proper over `A`. See the
entry for 0DIR in `errata.md`. The theorem here states the remaining conclusions.

## Main definitions

* `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem`: the data of the generalization.

## Main results

* `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem.stageSectionsPseudoCoherent`: the
  `Mₙ` are pseudo-coherent.
* `…SupportedDerivedExistenceSystem.exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso`:
  the generalized existence theorem.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] pointTopology

/-- **The data of the generalized derived existence theorem (Stacks 0DIR, `X` flat).** An inverse
system of rings `(Aₙ)` with surjective transitions whose kernels are locally nilpotent, an
algebraic space `X` separated, flat and of finite presentation over `A = lim Aₙ`, and
pseudo-coherent `Kₙ ∈ D(𝒪_{Xₙ})` with isomorphisms `Liₙ^* Kₙ₊₁ ≅ Kₙ`, each `Kₙ` supported on a
closed subset `Zₙ` of `|Xₙ|` proper over `Spec Aₙ`. -/
@[stacks 0DIR "the setting of the corrected remark: A = lim A_n with surjective transitions and \
locally nilpotent kernels, X separated, flat and of finite presentation over A, \
K_n pseudo-coherent on X_n supported on a closed subset proper over A_n, phi_n isomorphisms; \
flatness is necessary, \
see the errata entry 0DIR(flatness dropped)"]
structure SupportedDerivedExistenceSystem extends SeparatedDerivedExistenceSystem.{u} where
  /-- The closed subset `Zₙ ⊆ |Xₙ|` supporting `Kₙ`. -/
  support (n : ℕ) :
    Set (points B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).1)
  /-- `Zₙ` is closed. -/
  isClosed_support (n : ℕ) : IsClosed (support n)
  /-- `Zₙ` is proper over `Spec Aₙ`. -/
  isProperOver_support (n : ℕ) :
    IsProperOver B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).2
      (schemeSpace (baseObjectAt system B containsLimitBase containsBaseAt n)).2
      (spaceBaseProjection system B containsLimitBase containsBaseAt X n).hom
      (isLocallyOfFiniteType_spaceBaseProjection system B containsLimitBase containsBaseAt X
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (limitBase system)
          containsLimitBase finitePresentation.1) n)
      (support n) (isClosed_support n)
  /-- `Kₙ` is supported on `Zₙ`. -/
  supported (n : ℕ) :
    CohomologySupportedOn B (limitBase system) containsLimitBase
      (spaceAt system B containsLimitBase containsBaseAt X n).1
      (spaceAt system B containsLimitBase containsBaseAt X n).2 (support n) (K n)

namespace SupportedDerivedExistenceSystem

variable (D : SupportedDerivedExistenceSystem.{u})

/-- **The derived sections `Mₙ = RΓ(Xₙ, Lpₙ^*E ⊗^L Kₙ)` are pseudo-coherent** for every perfect
`E` and every `n`. `Lpₙ^*E ⊗^L Kₙ` is pseudo-coherent and supported on `Zₙ`; `Zₙ` lies in a closed
subspace `Wₙ ⊆ Xₙ` of finite presentation, proper over `Spec Aₙ`, whose open complement has
quasi-compact inclusion; so approximation by perfect complexes supported on `|Wₙ|` reduces the
pseudo-coherence of the direct image to that of perfect objects supported on `|Wₙ|`. -/
theorem stageSectionsPseudoCoherent :
    D.toSeparatedDerivedExistenceSystem.StageSectionsPseudoCoherent := by
  intro E hE n
  let D' := D.toSeparatedDerivedExistenceSystem
  let f := spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n
  have hfp : IsFinitePresentation D.B (limitBase D.system) D.containsLimitBase f.hom :=
    isFinitePresentation_spaceBaseProjection _ _ _ _ _ D.finitePresentation n
  have hfl : IsFlat D.B (limitBase D.system) D.containsLimitBase f.hom :=
    isFlat_spaceBaseProjection _ _ _ _ _ D.flat n
  have hsep : IsSeparated D.B (limitBase D.system) D.containsLimitBase f.hom :=
    isSeparated_of_isPullback_algebraicSpaces D.B (limitBase D.system) D.containsLimitBase
      (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip
      D.separated
  have hY : IsAffineSpace D.B (limitBase D.system) D.containsLimitBase
      (schemeSpace (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).1 :=
    isAffineSpace_yoneda _ _ _ _ inferInstance
  have hXqc := isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace D.B (limitBase D.system)
    D.containsLimitBase f hfp.2.1 hY
  have hXqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace D.B
    (limitBase D.system) D.containsLimitBase D.B.contains_terminal f hfp.2.2 hY
  obtain ⟨W, hWfp, hWp, hT, hZT, -, hTqc⟩ :=
    exists_closedSubspace_isFinitePresentation_of_isProperOver D.B (limitBase D.system)
      D.containsLimitBase D.B.contains_terminal _ _ f.hom hsep
      (isFiniteType_of_isFinitePresentation D.B (limitBase D.system) D.containsLimitBase hfp)
      hXqc hXqs hY.isQuasiCompactSpace (D.support n) (D.isClosed_support n)
      (D.isProperOver_support n)
  have hET : CohomologySupportedOn D.B (limitBase D.system) D.containsLimitBase _ _
      (Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase W.1.toFunctor W.1.ι))
      (D'.stageTensor E n) := fun i =>
    (cohomologySupportedOn_smallEtaleDerivedTensor_of_right (D.support n) (D.isClosed_support n)
      _ _ (D.supported n) i).trans hZT
  have hRf := isPseudoCoherent_derivedModulePushforward_of_cohomologySupportedOn f hfp.2.1 hfp.2.2
    hY (D'.stageTensor E n) (D'.isPseudoCoherent_stageTensor E hE n) _ hT hTqc hET
    (fun P hP hPT => isPseudoCoherent_derivedModulePushforward_of_isProper_closedSubspace f hfp hfl
      hY W hWfp hWp P hP hPT)
  have hq := derivedCategoryB_of_isPseudoCoherent_unconditional D.B (limitBase D.system)
    D.containsLimitBase _ _ _ hRf
  rw [@StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _ _ (_)]
  intro m
  obtain ⟨L, hL, e⟩ := hRf
  exact isPseudoCoherentFrom_representedAffineDerivedSections_obj D.B (limitBase D.system)
    D.containsLimitBase (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n) _ hq m
    ⟨L, hL m, e⟩

/-- **Grothendieck's existence theorem in its derived form, with supports proper over the base
(Stacks 0DIR, `X` flat over `A`).** There is `K ∈ D(𝒪_X)`, pseudo-coherent relative to `A`, with
isomorphisms `ψₙ : Ljₙ^* K ≅ Kₙ` such that `ψₙ = (Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*) ≫ Liₙ^* ψₙ₊₁ ≫ φₙ`. -/
theorem exists_isRelativelyPseudoCoherent_stageDerivedPullback_iso :
    ∃ (K : D.limitDerivedCategory)
      (ψ : ∀ n : ℕ, (D.stageDerivedPullback n).obj K ≅ D.K n)
      (hK : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left K),
      IsRelativelyPseudoCoherent D.B (limitBase D.system) D.containsLimitBase D.X.left.1
          D.X.left.2 D.X.hom.hom
          (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
            D.containsLimitBase D.finitePresentation.1) ⟨K, hK⟩ ∧
        ∀ n : ℕ, (ψ n).hom = (D.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback D.system D.B D.containsLimitBase D.containsBaseAt D.X n).map
            (ψ (n + 1)).hom ≫ D.φ n := by
  obtain ⟨K, ψ, hpc, hψ⟩ :=
    D.1.exists_isPseudoCoherent_stageDerivedPullback_iso_of_stageSectionsPseudoCoherent
      D.stageSectionsPseudoCoherent
  have hK := derivedCategoryB_of_isPseudoCoherent_unconditional D.B (limitBase D.system)
    D.containsLimitBase _ _ K hpc
  exact ⟨K, ψ, hK, (isRelativelyPseudoCoherent_iff_isPseudoCoherent D.B (limitBase D.system)
    D.containsLimitBase D.X.hom D.flat D.finitePresentation.1 ⟨K, hK⟩).2 hpc, hψ⟩

end SupportedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
