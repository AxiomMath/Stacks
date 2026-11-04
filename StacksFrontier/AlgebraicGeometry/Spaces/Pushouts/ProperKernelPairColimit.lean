module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairCechDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairSpecSurjective

/-!
# The coequalizer property of the relative spectrum `X'` of Stacks 0AGG, through Stacks 0GHL

Let `g : Y ⟶ X` be a proper morphism of algebraic spaces over `S` with `X` locally Noetherian,
and let `π : Y ⟶ X' = \underline{Spec}_X(𝒜)` be the morphism to the relative spectrum of the
equalizer `𝒜` of `s♯, t♯ : g_* 𝒪_Y ⟶ h_* 𝒪_R`. Granted étale descent of algebraic spaces along
proper surjective morphisms and condition (2) of Stacks 0GHL for the Čech cocone of `π`, the
morphism `π` is a coequalizer of the two projections of `R = Y ×_X Y`.

## Main definitions

* `AlgebraicGeometry.Space.CechAffineDescent`: condition (2) of Stacks 0GHL for the Čech cocone
  of a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isColimit_kernelPairSpecCofork_of_cechAffineDescent`: the
  coequalizer property of `X'`, from étale descent along proper surjective morphisms and
  condition (2) of Stacks 0GHL.

## References

* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 0GHL](https://stacks.math.columbia.edu/tag/0GHL)
* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Condition (2) of Stacks 0GHL for the Čech cocone of `p : Y ⟶ X'` over `ν : X' ⟶ B₀`**:
for every affine `B'` étale over `B₀`, every affine `Z` over `B'`, and every realization `r` with
affine total space of a compatible étale diagram `E` over the Čech nerve, with a morphism
`u : r.U ⟶ B'`, a cocone of morphisms `Eₙ ⟶ Z` over `B'` descends uniquely to a morphism
`r.U ⟶ Z` over `B'`. -/
def CechAffineDescent {X Y B₀ : AlgebraicSpaces B S hS} (p : Y ⟶ X) (ν : X ⟶ B₀) : Prop :=
  ∀ (B' : AlgebraicSpaces B S hS) (b : B' ⟶ B₀),
    IsAffineSpace B S hS B'.1 → IsEtale B S hS b.hom →
    ∀ (Z : AlgebraicSpaces B S hS) (z : Z ⟶ B'),
      IsAffineSpace B S hS Z.1 →
      ∀ (E : CompatibleEtaleDiagram B S hS (cechDiagram p ν))
        (r : EtaleRealization B S hS (cechCocone p ν) E),
        IsAffineSpace B S hS r.U.1 →
        ∀ (u : r.U ⟶ B'),
          r.toX ≫ (cechCocone p ν).pt.hom = u ≫ b →
          ∀ (fᵢ : E.U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Z),
            (∀ i, fᵢ.app i ≫ z = r.baseChange.app i ≫ u) →
            ∃! f : r.U ⟶ Z,
              (f ≫ z = u) ∧
                (∀ i, r.baseChange.app i ≫ f = fᵢ.app i)

variable {X Y : AlgebraicSpaces B S hS} {g : Y ⟶ X}

/-- **The coequalizer property of `X' = \underline{Spec}_X(𝒜)`** (the last paragraphs of the
proof of Stacks 0AGG), from Stacks 0GHL applied to the Čech nerve of `π : Y ⟶ X'`: condition (1)
is étale descent of algebraic spaces along the proper surjective `π`, carried as `h`, and
condition (2) is `h₂`. -/
theorem isColimit_kernelPairSpecCofork_of_cechAffineDescent
    (h : EtaleSpaceDescentAlongProperSurjective B S hS) (hg : IsProper B S hS g.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (h₂ : CechAffineDescent (kernelPairSpecπ hg) (kernelPairSpecToTarget hg)) :
    Nonempty (IsColimit (kernelPairSpecCofork hg)) := by
  have h₁ := etaleComparisonIsEquivalence_cechCocone (kernelPairSpecπ hg)
    (kernelPairSpecToTarget hg) h (isSurjective_kernelPairSpecπ hg hX)
    (isProper_kernelPairSpecπ hg hX)
  obtain ⟨hc⟩ := isColimit_of_etale_local_affine_descent B S hS
    (cechCocone (kernelPairSpecπ hg) (kernelPairSpecToTarget hg)) h₁ h₂
  exact ⟨isColimitCofork_of_isColimit_cechCoconeSpace (kernelPairSpecπ hg)
    (kernelPairSpecπ_comp_toTarget hg) (isColimitCechCoconeSpace _ _ hc)
    (kernelPairSpecπ_equalizes hg)⟩

end AlgebraicGeometry.Space

end
