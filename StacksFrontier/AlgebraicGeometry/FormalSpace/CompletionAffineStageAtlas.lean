module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# The stage atlas of the completion of an affine scheme

Let `S` be a scheme contained in a big fppf site `B`, let `X = Spec A` be an affine scheme over
`S` lying in that site and let `I ⊆ A` be an ideal. The completion of `X` along `V(I)` is the
colimit of the quotient spectra `Spec (A ⧸ J)` over the ideals `J` with `V(J) = V(I)`
(`AlgebraicGeometry.FormalSpace.isIso_supportComparison`). This file proves that the chosen
site always carries an atlas for that colimit, that is
`AlgebraicGeometry.FormalSpace.HasStageAtlas`, and so removes that hypothesis from Stacks 0AIY.

## Main results

* `AlgebraicGeometry.FormalSpace.hasStageAtlas`: the coproduct of the sheaves represented by
  the quotient stages is the sheaf represented by an object of the site.
* `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf_of_isClosed`:
  **Stacks 0AIY**, under the source's hypotheses only.

## Implementation notes

The bound that puts the coproduct of the stages in the site is a *uniform* one, not a
cofinality bound. Since `Spec A` lies in the site, `max ℵ₀ #A` is below the cutoff, hence so is
`μ = max ℵ₀ (2 ^ #A)`, the cutoff being a strong prelimit. There are at most `2 ^ #A` ideals of
`A`, and each stage `Spec (A ⧸ J)` has size `max ℵ₀ #(A ⧸ J) ≤ μ`. So
`AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le` produces the coproduct
`V` of the stages in the site together with the identification of the universe-lifted
representable sheaf of `V` with the coproduct of those of the stages. No regularity of the
cutoff is used: the family of ideals with a given zero locus is in general of cardinality above
the cofinality of the cutoff, which is why the cofinality form
`AlgebraicGeometry.BigFppfSite.contains_sigma` does not apply, but its members are uniformly
bounded. This is the argument of `AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff`
for the quotient systems of Stacks 0AIF, run for the index of Stacks 0AIY.

## References

* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {A : Type u} [CommRing A]
  (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S) (I : Ideal A)

/-- The ideals with a given zero locus, read as the index of the presentation of the
completion. -/
def supportIdealEquivIndex : SupportIdeal I ≃ SupportIndex I where
  toFun K := ULift.up (OrderDual.toDual K)
  invFun K := OrderDual.ofDual K.down
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The site carries an atlas for the completion of an affine scheme.** The coproduct of the
sheaves represented by the quotient stages `Spec (A ⧸ J)`, over the ideals `J` with
`V(J) = V(I)`, is the sheaf represented by an object of the site: the stages and their index
are bounded by the single cardinal `max ℵ₀ (2 ^ #A)`, which lies below the cutoff because
`Spec A` lies in the site and the cutoff is a strong prelimit. -/
theorem hasStageAtlas : HasStageAtlas B S hS hA f I := by
  classical
  let J := BigFppfOver.topology B S hS
  let X : SupportIdeal I → BigFppfOver B S hS := fun K ↦
    (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA f I K)
  have hAc : #A < B.cutoff := by
    have h : (Spec (.of A)).size < B.cutoff := hA
    rw [Scheme.size_Spec] at h
    exact (le_max_right _ _).trans_lt h
  set μ : Cardinal.{u} := max ℵ₀ (2 ^ #A)
  have hμ : μ < B.cutoff := max_lt B.aleph0_lt_cutoff (B.cutoff_isStrongPrelimit hAc)
  have hι : #(SupportIdeal I) ≤ μ :=
    calc #(SupportIdeal I) ≤ #(Ideal A) := mk_subtype_le _
      _ ≤ #(Set A) := mk_le_of_injective (f := fun K : Ideal A ↦ (K : Set A))
          SetLike.coe_injective
      _ = 2 ^ #A := mk_set
      _ ≤ μ := le_max_right _ _
  have hX : ∀ K, ((BigFppfOver.toScheme B S hS).obj (X K)).size ≤ μ := fun K ↦ by
    change (Spec (.of (A ⧸ K.1))).size ≤ μ
    rw [Scheme.size_Spec]
    exact max_le (le_max_left _ _)
      (mk_quotient_le.trans ((Cardinal.cantor _).le.trans (le_max_right _ _)))
  obtain ⟨V, j, -, -, -, -, ⟨hV⟩⟩ :=
    BigFppfOver.exists_isColimitUliftYoneda_of_size_le B S hS X hμ hι hX
  refine ⟨V, J.uliftYoneda.{u + 1}.obj V, ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app V⟩, ?_⟩
  let eSmall : J.uliftYoneda.{u + 1}.obj V ≅
      ∐ fun K : SupportIdeal I ↦ (Sheaf.sheafifiedYoneda J).obj (X K) :=
    IsColimit.coconePointsIsoOfNatIso hV (coproductIsCoproduct _)
      (Discrete.natIso fun K ↦
        (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm.app (X K.as))
  exact ⟨eSmall ≪≫ Sigma.whiskerEquiv
    (f := fun K : SupportIdeal I ↦ (Sheaf.sheafifiedYoneda J).obj (X K))
    (g := fun K : SupportIndex I ↦ (Sheaf.sheafifiedYoneda J).obj
      ((BigAffineFppf.inclusion B S hS).obj ((supportDiagram B S hS hA f I).obj K)))
    (supportIdealEquivIndex I) fun _ ↦ Iso.refl _⟩

/-- **Stacks 0AIY.** Let `S` be a scheme, let `X = Spec A` be an affine scheme over `S` lying
in the big fppf site and let `T ⊆ |X|` be a closed subset. The completion of `X` along `T` —
the fppf sheaf attached to the functor sending `U` to the set of morphisms `f : U ⟶ X` with
`f(|U|) ⊆ T` — is a McQuillan affine formal algebraic space.

This is `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf` with its
atlas hypothesis discharged by `AlgebraicGeometry.FormalSpace.hasStageAtlas`. -/
@[stacks 0AIY "McQuillan affine formal algebraic space"]
theorem hasSomeSurjectivePresentation_completionSheaf_of_isClosed
    (T : Set ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA f))) (hT : IsClosed T) :
    HasSomeSurjectivePresentation B S hS
      (Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hA f))
        (supportedPoints B S hS (affineOver B S hS hA f) T)) :=
  hasSomeSurjectivePresentation_completionSheaf B S hS hA f T hT
    (hasStageAtlas B S hS hA f _)

end AlgebraicGeometry.FormalSpace

end
