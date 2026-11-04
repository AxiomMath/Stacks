module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelMaps
public import
  StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistencePseudoCoherent

/-!
# Grothendieck's existence theorem for flat modules with proper support

In Situation [Stacks, Tag 0CTC], [Stacks, Tag 0CTK] produces a finitely presented `𝒪_X`-module
`ℱ`, flat over `A` and with support proper over `A`, with `ℱₙ = ℱ ⊗ 𝒪_{Xₙ}` compatibly with the
`φₙ`. The source's proof runs through [Stacks, Tag 0CTD] to [Stacks, Tag 0CTI]; this file
records the final assembly.

## Main results

* `ExistenceSituation.exists_algebraization_of_zerothLevelMap`:
  the conclusion of [Stacks, Tag 0CTK] from an open `W ⊇ X₀` as in [Stacks, Tag 0CTH], on which
  `H⁰(K)` is of finite presentation and whose canonical maps to the `ℱₙ` are adjoint to
  isomorphisms.
* `ExistenceSituation.exists_algebraization_of_isPseudoCoherent_of_isIso_sectionsOverComparison`:
  the conclusion of [Stacks, Tag 0CTK] from [Stacks, Tag 0CTF] and [Stacks, Tag 0CTG], through
  [Stacks, Tag 0CTD] and [Stacks, Tag 0CTH].

## References

* [Stacks Project, Tag 0CTK](https://stacks.math.columbia.edu/tag/0CTK)
* [Stacks Project, Tag 0CTH](https://stacks.math.columbia.edu/tag/0CTH)
* [Stacks Project, Tag 0CTI](https://stacks.math.columbia.edu/tag/0CTI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

/-- **The proof of [Stacks, Tag 0CTK] from the conclusion of [Stacks, Tag 0CTH].** Let `W` be an
open containing `X₀` on which `H⁰(K)` is of finite presentation and such that the canonical maps
`H⁰(K) ⟶ iₙ,* ℱₙ` have invertible adjoints `iₙ^* H⁰(K) ⟶ ℱₙ`. Then the conclusion of
[Stacks, Tag 0CTK] holds: shrink `W` as in [Stacks, Tag 0CTI] and algebraize. -/
theorem exists_algebraization_of_zerothLevelMap [HasDerivedCategory.{w} S.X.left.Modules]
    (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p) (W : S.X.left.Opens)
    (hW : Set.range (S.closedImmersion 0) ⊆ W)
    (hfp : (((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K).restrict
      W.ι).IsFinitePresentation)
    (hiso : ∀ n, IsIso
      (((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).homEquiv _ _).symm
        (S.zerothLevelMap d p n))) :
    ∃ (F : S.X.left.Modules) (_ : F.IsFinitePresentation),
      IsFlatOver S.X.hom.toLRSHom.toShHom F ∧
      (∃ Z : Closeds S.X.left, (Z : Set S.X.left) = SheafOfModules.supp F ∧
        IsProperOver S.X.hom Z) ∧
      ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n,
        ∀ n : ℕ,
          (Scheme.Modules.pullbackComp (S.transitionScheme n) (S.closedImmersion (n + 1))).app F ≪≫
            (Scheme.Modules.pullbackCongr (S.transition_fst n)).app F ≪≫ e n =
          (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n :=
  S.exists_algebraization_of_isIso_adjoint W
    (fun n => (S.range_closedImmersion_eq n).trans_subset hW) _ (S.zerothLevelMap d p)
    (S.zerothLevelMap_comp_pushforwardTransition d p hp) hiso

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTI] from [Stacks, Tag 0CTF] and [Stacks, Tag 0CTG].** After shrinking the
open `W ⊇ X₀` of [Stacks, Tag 0CTH], the support of `ℱ = H⁰(K)|_W` is proper over `A`, while
parts (1), (2) and (3) of [Stacks, Tag 0CTH] still hold. Stated at the standard model. -/
theorem exists_open_isProperOver_of_isPseudoCoherent_of_isIso_sectionsOverComparison
    (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hpc : S.X.hom.IsPseudoCoherent d.K)
    (hG : ∀ U : S.X.left.Opens, IsAffineOpen U → ∀ n : ℕ,
      IsIso (S.sectionsOverComparison d p U n)) :
    ∃ W : S.X.left.Opens, Set.range (S.closedImmersion 0) ⊆ W ∧
      (∀ j : ℤ, j ≠ 0 →
        IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict W.ι)) ∧
      (((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K).restrict
        W.ι).IsFinitePresentation ∧
      (∀ n : ℕ, IsIso
        (((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).homEquiv _ _).symm
          (S.zerothLevelMap d p n))) ∧
      ∃ Z : Closeds W.toScheme, (Z : Set W.toScheme) = SheafOfModules.supp
          (((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K).restrict W.ι) ∧
        IsProperOver (W.ι ≫ S.X.hom) Z := by
  obtain ⟨W, hW, hvan, hfp, hiso⟩ :=
    S.exists_open_of_isPseudoCoherent_of_isIso_sectionsOverComparison d p hpc hG
  have := hfp
  obtain ⟨W', hW'W, hW', hfp', Z, hZ, hprop⟩ := S.exists_le_isProperOver_supp W
    (fun n => (S.range_closedImmersion_eq n).trans_subset hW) _
    (@asIso _ _ _ _ _ (hiso 0))
  exact ⟨W', hW' 0, fun j hj => isZero_restrict_of_le _ hW'W (hvan j hj), hfp', hiso, Z, hZ,
    hprop⟩

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The proof of [Stacks, Tag 0CTK] from [Stacks, Tag 0CTF] and [Stacks, Tag 0CTG].** Granted
that the object `K` of [Stacks, Tag 0CTD] is pseudo-coherent relative to `A` and that the
comparison maps `RΓ(U, K) ⊗_A^𝐋 Aₙ ⟶ RΓ(Uₙ, ℱₙ)` are invertible over affine opens, the
conclusion of [Stacks, Tag 0CTK] holds: take `K` from [Stacks, Tag 0CTD] and a derived-limit cone,
the open `W` of [Stacks, Tag 0CTH], and algebraize. Stated at the standard model of `D(𝒪_X)`, at
which [Stacks, Tag 09UI] (relative pseudo-coherence) is available. -/
theorem exists_algebraization_of_isPseudoCoherent_of_isIso_sectionsOverComparison
    (hpc : ∀ d : S.DerivedLimitQCoh, S.X.hom.IsPseudoCoherent d.K)
    (hG : ∀ (d : S.DerivedLimitQCoh)
      (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩),
      S.IsDerivedLimitCone p → ∀ U : S.X.left.Opens, IsAffineOpen U → ∀ n : ℕ,
        IsIso (S.sectionsOverComparison d p U n)) :
    ∃ (F : S.X.left.Modules) (_ : F.IsFinitePresentation),
      IsFlatOver S.X.hom.toLRSHom.toShHom F ∧
      (∃ Z : Closeds S.X.left, (Z : Set S.X.left) = SheafOfModules.supp F ∧
        IsProperOver S.X.hom Z) ∧
      ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n,
        ∀ n : ℕ,
          (Scheme.Modules.pullbackComp (S.transitionScheme n) (S.closedImmersion (n + 1))).app F ≪≫
            (Scheme.Modules.pullbackCongr (S.transition_fst n)).app F ≪≫ e n =
          (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n := by
  obtain ⟨d⟩ := S.nonempty_derivedLimitQCoh
  obtain ⟨p, hp⟩ := d.exists_isDerivedLimitCone
  obtain ⟨W, hW, -, hfp, hiso⟩ :=
    S.exists_open_of_isPseudoCoherent_of_isIso_sectionsOverComparison d p (hpc d) (hG d p hp)
  exact S.exists_algebraization_of_zerothLevelMap d p hp W hW hfp hiso

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The proof of [Stacks, Tag 0CTK] from [Stacks, Tag 0CTF], [Stacks, Tag 0CTE] (1) and the
projection-formula square.** These give [Stacks, Tag 0CTG] over every quasi-compact open
(`isIso_sectionsOverComparison_of_isIso_tensorBaseChange_of_square`), and
`exists_algebraization_of_isPseudoCoherent_of_isIso_sectionsOverComparison` finishes. Stated at
the standard model. -/
theorem exists_algebraization_of_isPseudoCoherent_of_isIso_tensorBaseChange
    (h0CTF : ∀ d : S.DerivedLimitQCoh, S.X.hom.IsPseudoCoherent d.K)
    (h0CTE : ∀ (d : S.DerivedLimitQCoh)
      (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩),
      S.IsDerivedLimitCone p → ∀ (n : ℕ) (E : DerivedCategory S.X.left.Modules),
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.X.left.toRingedSpace) E →
          IsIso ((DerivedLimitQCoh.tensorBaseChange S d p n).app E))
    (hC : ∀ U : S.X.left.Opens, IsCompact (U : Set S.X.left) → ∀ n : ℕ,
      S.ProjectionFormulaSquare U n) :
    ∃ (F : S.X.left.Modules) (_ : F.IsFinitePresentation),
      IsFlatOver S.X.hom.toLRSHom.toShHom F ∧
      (∃ Z : Closeds S.X.left, (Z : Set S.X.left) = SheafOfModules.supp F ∧
        IsProperOver S.X.hom Z) ∧
      ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n,
        ∀ n : ℕ,
          (Scheme.Modules.pullbackComp (S.transitionScheme n) (S.closedImmersion (n + 1))).app F ≪≫
            (Scheme.Modules.pullbackCongr (S.transition_fst n)).app F ≪≫ e n =
          (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n :=
  S.exists_algebraization_of_isPseudoCoherent_of_isIso_sectionsOverComparison h0CTF
    fun d p hp U hU n => S.isIso_sectionsOverComparison_of_isIso_tensorBaseChange_of_square d p n U
      hU.isCompact (h0CTE d p hp n) (hC U hU.isCompact n)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The proof of [Stacks, Tag 0CTK] from [Stacks, Tag 0CTF] and the projection-formula
square**, [Stacks, Tag 0CTE] (1) being proved
(`DerivedLimitQCoh.isIso_tensorBaseChange_app`). Stated at the standard model. -/
theorem exists_algebraization_of_isPseudoCoherent_of_projectionFormulaSquare
    (h0CTF : ∀ d : S.DerivedLimitQCoh, S.X.hom.IsPseudoCoherent d.K)
    (hC : ∀ U : S.X.left.Opens, IsCompact (U : Set S.X.left) → ∀ n : ℕ,
      S.ProjectionFormulaSquare U n) :
    ∃ (F : S.X.left.Modules) (_ : F.IsFinitePresentation),
      IsFlatOver S.X.hom.toLRSHom.toShHom F ∧
      (∃ Z : Closeds S.X.left, (Z : Set S.X.left) = SheafOfModules.supp F ∧
        IsProperOver S.X.hom Z) ∧
      ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n,
        ∀ n : ℕ,
          (Scheme.Modules.pullbackComp (S.transitionScheme n) (S.closedImmersion (n + 1))).app F ≪≫
            (Scheme.Modules.pullbackCongr (S.transition_fst n)).app F ≪≫ e n =
          (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n :=
  S.exists_algebraization_of_isPseudoCoherent_of_isIso_tensorBaseChange h0CTF
    (fun d p hp n E hE => DerivedLimitQCoh.isIso_tensorBaseChange_app S d p hp n E hE) hC

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The proof of [Stacks, Tag 0CTK] from the projection-formula square of the proof of
[Stacks, Tag 0CTG]**, [Stacks, Tag 0CTF] (`DerivedLimitQCoh.isPseudoCoherent`) and
[Stacks, Tag 0CTE] (1) being proved. Stated at the standard model. -/
theorem exists_algebraization_of_projectionFormulaSquare
    (hC : ∀ U : S.X.left.Opens, IsCompact (U : Set S.X.left) → ∀ n : ℕ,
      S.ProjectionFormulaSquare U n) :
    ∃ (F : S.X.left.Modules) (_ : F.IsFinitePresentation),
      IsFlatOver S.X.hom.toLRSHom.toShHom F ∧
      (∃ Z : Closeds S.X.left, (Z : Set S.X.left) = SheafOfModules.supp F ∧
        IsProperOver S.X.hom Z) ∧
      ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n,
        ∀ n : ℕ,
          (Scheme.Modules.pullbackComp (S.transitionScheme n) (S.closedImmersion (n + 1))).app F ≪≫
            (Scheme.Modules.pullbackCongr (S.transition_fst n)).app F ≪≫ e n =
          (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n :=
  S.exists_algebraization_of_isPseudoCoherent_of_projectionFormulaSquare
    (fun d => DerivedLimitQCoh.isPseudoCoherent d) hC

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
