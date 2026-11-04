module
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
import all StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic

/-!
# BasicUnconditional

Stronger forms of declarations of `StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic`,
stated as separate declarations beside the ones there: over more general coefficient universes, or
with inputs that are carried there as hypotheses discharged, together with the new results built
on them.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SectionsToProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

section Span

variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

end Span

variable {X : Scheme.{u}} {n : ℕ}

variable (s : Fin (n + 1) → Γ(X, ⊤)) (hs : Ideal.span (Set.range s) = ⊤)

section Universe0

end Universe0

/-- **The glueing step of Stacks Tag 01NE.** Given a cover of `X` by opens `U i`, on each of which
a family `t i` of sections of `𝒪_X` spans the unit ideal, and given that on each overlap the two
families differ by a unit, the chart morphisms glue to a single morphism `X ⟶ ℙⁿ_ℤ`.

For an invertible `L` with generating global sections `s₀, …, sₙ` the hypotheses hold with
`U i = X_{sᵢ}` and `t i k` the ratio `s_k / sᵢ` produced by the trivialization of Tag 01CY; the
unit on the overlap is `t i j`, invertible there by the cocycle identity. See the module
docstring.

Conditional on `Stacks.SectionsToProjectiveSpace.HasPullbackNaturality` and
`Stacks.SectionsToProjectiveSpace.HasUnitInvariance`. -/
theorem exists_hom_of_cover_general (hA : HasPullbackNaturality.{u}) (hB : HasUnitInvariance.{u})
    {X : Scheme.{u}} {n : ℕ} {ι : Type*} (U : ι → X.Opens) (hU : IsOpenCover U)
    (t : ∀ i, Fin (n + 1) → Γ((U i).toScheme, ⊤))
    (ht : ∀ i, Ideal.span (Set.range (t i)) = ⊤)
    (hagree : ∀ i j, ∃ u : Γ((U i ⊓ U j : X.Opens).toScheme, ⊤)ˣ, ∀ k,
      resOfLE (inf_le_left : U i ⊓ U j ≤ U i) (t i k) =
        (u : Γ((U i ⊓ U j : X.Opens).toScheme, ⊤)) *
          resOfLE (inf_le_right : U i ⊓ U j ≤ U j) (t j k)) :
    ∃ g : X ⟶ projectiveSpaceAtUniverse.{u} n,
      ∀ i, (U i).ι ≫ g = toProjectiveSpaceAtUniverse (t i) (ht i) := by
  have key : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫
      toProjectiveSpaceAtUniverse (t i) (ht i) =
        X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫
          toProjectiveSpaceAtUniverse (t j) (ht j) := by
    intro i j
    obtain ⟨u, hu⟩ := hagree i j
    rw [hA _ (t i) (ht i) (span_range_comp _ _ (ht i)),
      hA _ (t j) (ht j) (span_range_comp _ _ (ht j))]
    have hfun := funext hu
    have h2 := hB u (fun k => (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).appTop (t j k))
      (span_range_comp _ _ (ht j))
      (by rw [span_range_unit_smul]; exact span_range_comp _ _ (ht j))
    exact (toProjectiveSpaceAtUniverse_congr hfun _ _).trans h2
  refine ⟨(X.openCoverOfIsOpenCover U hU).glueMorphisms
    (fun i => toProjectiveSpaceAtUniverse (t i) (ht i)) ?_, ?_⟩
  · intro i j
    show pullback.fst (U i).ι (U j).ι ≫ toProjectiveSpaceAtUniverse (t i) (ht i) =
      pullback.snd (U i).ι (U j).ι ≫ toProjectiveSpaceAtUniverse (t j) (ht j)
    rw [← cancel_epi (isPullback_opens_inf (U i) (U j)).isoPullback.hom, ← Category.assoc,
      ← Category.assoc, (isPullback_opens_inf (U i) (U j)).isoPullback_hom_fst,
      (isPullback_opens_inf (U i) (U j)).isoPullback_hom_snd]
    exact key i j
  · intro i
    exact (X.openCoverOfIsOpenCover U hU).ι_glueMorphisms _ _ i

end Stacks.SectionsToProjectiveSpace

end
