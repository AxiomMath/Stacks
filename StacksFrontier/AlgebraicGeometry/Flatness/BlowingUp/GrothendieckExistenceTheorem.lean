module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceFlat
public import
  StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelSectionsSquare

/-!
# Grothendieck's existence theorem for flat modules with proper support

In Situation [Stacks, Tag 0CTC], with `K` the object of [Stacks, Tag 0CTD]: the comparison
`RΓ(U, K) ⊗_A^𝐋 Aₙ = RΓ(Uₙ, ℱₙ)` over quasi-compact opens ([Stacks, Tag 0CTG]), the open
`W ⊇ X₀` on which `K` is a finitely presented sheaf in degree zero restricting to the `ℱₙ`
([Stacks, Tag 0CTH]), with proper support after shrinking ([Stacks, Tag 0CTI]), and the existence
theorem itself ([Stacks, Tag 0CTK]).

## Main results

* `ExistenceSituation.isIso_sectionsOverComparison`: [Stacks, Tag 0CTG].
* `ExistenceSituation.exists_open_isZero_homology_isFinitePresentation_isIso`:
  [Stacks, Tag 0CTH].
* `ExistenceSituation.exists_open_isProperOver_supp`: [Stacks, Tag 0CTI].
* `ExistenceSituation.exists_algebraization`: [Stacks, Tag 0CTK].

## Implementation notes

The first three are stated at the standard model of the derived categories, scoped to each
declaration, as [Stacks, Tag 09UI] and the projection formula are available there only; the
statement of the fourth involves no derived category.

## References

* [Stacks Project, Tag 0CTG](https://stacks.math.columbia.edu/tag/0CTG)
* [Stacks Project, Tag 0CTH](https://stacks.math.columbia.edu/tag/0CTH)
* [Stacks Project, Tag 0CTI](https://stacks.math.columbia.edu/tag/0CTI)
* [Stacks Project, Tag 0CTK](https://stacks.math.columbia.edu/tag/0CTK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u})

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTG].** In Situation [Stacks, Tag 0CTC], let `K` be as in
[Stacks, Tag 0CTD], with a derived-limit cone `p` of `R lim (iₙ,* ℱₙ)`. For every quasi-compact
open `U ⊆ X`, the canonical map `RΓ(U, K) ⊗_A^𝐋 Aₙ ⟶ RΓ(Uₙ, ℱₙ)` of `D(Aₙ)`, `Uₙ = U ∩ Xₙ`, is an
isomorphism. Stated at the standard model. -/
@[stacks 0CTG]
theorem isIso_sectionsOverComparison (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p) (U : S.X.left.Opens) (hU : IsCompact (U : Set S.X.left))
    (n : ℕ) : IsIso (S.sectionsOverComparison d p U n) :=
  S.isIso_sectionsOverComparison_of_isIso_tensorBaseChange_of_square d p n U hU
    (fun E hE => DerivedLimitQCoh.isIso_tensorBaseChange_app S d p hp n E hE)
    (S.projectionFormulaSquare U hU n)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTH].** In Situation [Stacks, Tag 0CTC], let `K` be as in
[Stacks, Tag 0CTD], with a derived-limit cone `p`. There is an open `W ⊆ X` containing `X₀` such
that `Hⁱ(K)|_W = 0` for `i ≠ 0`, `ℱ = H⁰(K)|_W` is of finite presentation, and
`ℱₙ = ℱ ⊗_{𝒪_X} 𝒪_{Xₙ}`: the canonical maps `iₙ^* H⁰(K) ⟶ ℱₙ`, adjoint to the maps
`H⁰(K) ⟶ iₙ,* ℱₙ` induced by `K ⟶ iₙ,* ℱₙ`, are isomorphisms. Stated at the standard model. -/
@[stacks 0CTH]
theorem exists_open_isZero_homology_isFinitePresentation_isIso (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p) :
    ∃ W : S.X.left.Opens, Set.range (S.closedImmersion 0) ⊆ W ∧
      (∀ j : ℤ, j ≠ 0 →
        IsZero (((DerivedCategory.homologyFunctor S.X.left.Modules j).obj d.K).restrict W.ι)) ∧
      (((DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K).restrict
        W.ι).IsFinitePresentation ∧
      ∀ n : ℕ, IsIso
        (((Scheme.Modules.pullbackPushforwardAdjunction (S.closedImmersion n)).homEquiv _ _).symm
          (S.zerothLevelMap d p n)) :=
  S.exists_open_of_isPseudoCoherent_of_isIso_sectionsOverComparison d p
    (DerivedLimitQCoh.isPseudoCoherent d)
    fun U hU n => S.isIso_sectionsOverComparison d p hp U hU.isCompact n

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 0CTI].** In Situation [Stacks, Tag 0CTC], with `K` as in [Stacks, Tag 0CTD]
and `W` as in [Stacks, Tag 0CTH]: after shrinking `W`, the support of `ℱ = H⁰(K)|_W` is proper over
`A`. The open produced keeps the three properties of [Stacks, Tag 0CTH]. Stated at the standard
model. -/
@[stacks 0CTI]
theorem exists_open_isProperOver_supp (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p) :
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
        IsProperOver (W.ι ≫ S.X.hom) Z :=
  S.exists_open_isProperOver_of_isPseudoCoherent_of_isIso_sectionsOverComparison d p
    (DerivedLimitQCoh.isPseudoCoherent d)
    fun U hU n => S.isIso_sectionsOverComparison d p hp U hU.isCompact n

/-- **[Stacks, Tag 0CTK], Grothendieck's existence theorem for flat modules.** In Situation
[Stacks, Tag 0CTC] there is a finitely presented `𝒪_X`-module `ℱ`, flat over `A`, with support
proper over `A`, such that `ℱₙ = ℱ ⊗_{𝒪_X} 𝒪_{Xₙ}` for all `n` compatibly with the maps `φₙ`.
The derived categories in the proof are the standard ones; none appears in the statement. -/
@[stacks 0CTK]
theorem exists_algebraization :
    ∃ (F : S.X.left.Modules) (_ : F.IsFinitePresentation),
      IsFlatOver S.X.hom.toLRSHom.toShHom F ∧
      (∃ Z : Closeds S.X.left, (Z : Set S.X.left) = SheafOfModules.supp F ∧
        IsProperOver S.X.hom Z) ∧
      ∃ e : ∀ n : ℕ, (Scheme.Modules.pullback (S.closedImmersion n)).obj F ≅ S.F n,
        ∀ n : ℕ,
          (Scheme.Modules.pullbackComp (S.transitionScheme n) (S.closedImmersion (n + 1))).app F ≪≫
            (Scheme.Modules.pullbackCongr (S.transition_fst n)).app F ≪≫ e n =
          (Scheme.Modules.pullback (S.transitionScheme n)).mapIso (e (n + 1)) ≪≫ S.φ n :=
  S.exists_algebraization_of_projectionFormulaSquare fun U hU n => S.projectionFormulaSquare U hU n

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
