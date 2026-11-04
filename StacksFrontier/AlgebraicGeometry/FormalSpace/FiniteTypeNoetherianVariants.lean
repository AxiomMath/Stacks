module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSourceVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeDescentAlongAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherianRefined

/-!
# Variants of the results of `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian`

The declarations below extend `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian` and
are kept in a module of their own so that that module stays unchanged. A primed name `X'` is a
variant of the declaration `X` there.

## Main declarations

* `isLocallyNoetherian_source_of_isLocallyOfFiniteType'`
* `isLocallyNoetherian_of_isPullback_of_setTheoreticCondition`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AQ8**, granting Stacks 0ANL and the two inputs of the general Stacks 0AJI. Let
`f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of formal algebraic spaces over `S`. If `Z` is locally
Noetherian and `f` is locally of finite type, then `Z ×_Y X` is locally Noetherian.

The projection `p : Z ×_Y X ⟶ Z` is a base change of `f`, so it is locally of finite type by
Stacks 0AQ5; being representable by algebraic spaces it also makes `Z ×_Y X` a formal
algebraic space by Stacks 0AJI, and Stacks 0AQ7 applies to `p`. The fibre product is presented
as an arbitrary cartesian square, so the statement covers either order of its two legs.

`p` carries no étaleness, so the step that sees `Z ×_Y X` as a formal algebraic space is the
general Stacks 0AJI and not its étale case, and `h0AIU` together with the set-theoretic
condition `hWset` of Stacks 0AIS are hypotheses. They are used for that step alone: Stacks
0AQ7 itself no longer asks for either, and the proof does not use the hypothesis `_h0ANL`
(Stacks 0ANL). -/
theorem isLocallyNoetherian_of_isPullback_of_setTheoreticCondition
    {W X Y Z : FppfSheaf B S hS} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsLocallyOfFiniteType B S hS f)
    (hWset : SatisfiesSetTheoreticCondition B S hS W)
    (h0AIU : ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
      (E : Λ ⥤ FppfSheaf B S hS),
      (∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj) →
      (∀ ⦃i j : Λ⦄ (e : i ⟶ j),
        Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map e).hom) →
      ∀ T : FppfSheaf B S hS, SatisfiesSetTheoreticCondition B S hS T →
        Nonempty (T ≅ colimit E) → IsFormalAlgebraicSpace B S hS T)
    (_h0ANL : IsLocallyOfFiniteType B S hS p →
      ∀ (U₀ V₀ : FppfSheaf B S hS) (a : U₀ ⟶ W) (b : V₀ ⟶ Z) (t : U₀ ⟶ V₀),
        IsAffineFormalAlgebraicSpace B S hS U₀ → IsAffineFormalAlgebraicSpace B S hS V₀ →
        IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b →
        a ≫ p = t ≫ b → IsLocallyOfFiniteType B S hS t) :
    IsLocallyNoetherian B S hS W := by
  obtain ⟨hprep, hpprop⟩ := IsLocallyOfFiniteType.of_isPullback B S hS sq hf
  exact isLocallyNoetherian_source_of_isLocallyOfFiniteType' B S hS p
    (isFormalAlgebraicSpace_of_representable_over_formal' B S hS p hZ.1 hprep hWset h0AIU)
    hZ ⟨hprep, hpprop⟩

end AlgebraicGeometry.FormalSpace

end
