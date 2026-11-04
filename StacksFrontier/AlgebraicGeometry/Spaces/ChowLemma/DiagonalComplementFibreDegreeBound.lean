module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementDistinct

/-!
# A named bound on the fibre degrees of a chart, and the diagonal complements it empties

`AlgebraicGeometry.Space.HasUniversallyBoundedFibers` ([Stacks, Tag 03JL]) asserts that *some*
integer bounds the degree of every field-valued fibre of a scheme morphism to a presheaf. This
file names the bounding predicate and states two consequences of the universal bound at a named
bound.

## Main definitions

* `AlgebraicGeometry.Space.BoundsFibreDegrees`: an integer bounds the degree of the finite
  scheme obtained by pulling back along each field-valued point.

## Main results

* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_iff_exists_boundsFibreDegrees`: the
  universal bound of [Stacks, Tag 03JL] is the existence of such an integer.
* `AlgebraicGeometry.Space.BoundsFibreDegrees.mono`: a bound stays a bound when enlarged.
* `AlgebraicGeometry.Space.forall_le_of_boundsFibreDegrees`: a bound on the fibre degrees of a
  chart bounds the number of pairwise distinct lifts of every field-valued point.
* `AlgebraicGeometry.Space.SpacesEtale.isEmpty_points_diagonalComplement_of_boundsFibreDegrees`:
  the complement of the diagonals in the `n`-fold self-product of a chart has no points once `n`
  exceeds such a bound.

## References

* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- An integer *bounds the fibre degrees* of a scheme morphism to a presheaf when every
field-valued base change of it is represented by a finite locally free scheme over the field
spectrum of rank at most that integer. -/
abbrev BoundsFibreDegrees (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ X) (n : ℤ) : Prop :=
  ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
    ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ∃ (V : BigFppfOver B S hS) (p : V ⟶ T) (i : yoneda.obj V ⟶ yoneda.obj U) (r : ℕ),
          (r : ℤ) ≤ n ∧
            Stacks.Morphisms.IsFiniteLocallyFreeOfRank
              ((BigFppfOver.toScheme B S hS).map p) r ∧
            IsPullback i (yoneda.map p) f ξ

/-- **The universal bound of [Stacks, Tag 03JL] is the existence of a bound on the fibre
degrees.** -/
theorem hasUniversallyBoundedFibers_iff_exists_boundsFibreDegrees (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X) :
    HasUniversallyBoundedFibers B S hS U f ↔ ∃ n : ℤ, BoundsFibreDegrees B S hS U f n :=
  Iff.rfl

/-- A bound on the fibre degrees stays a bound when it is enlarged. -/
theorem BoundsFibreDegrees.mono {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {f : yoneda.obj U ⟶ X} {n n' : ℤ} (h : BoundsFibreDegrees B S hS U f n) (hle : n ≤ n') :
    BoundsFibreDegrees B S hS U f n' := by
  intro k _ T hT ξ
  obtain ⟨V, p, i, r, hr, hrest⟩ := h k T hT ξ
  exact ⟨V, p, i, r, hr.trans hle, hrest⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A bound on the fibre degrees of a chart bounds the number of pairwise distinct lifts of
every field-valued point.** If `N` bounds the fibre degrees of `c : W ⟶ X`, then any `n` pairwise
distinct morphisms `T ⟶ W` over one field-valued point `T ⟶ X` satisfy `n ≤ N`. -/
theorem forall_le_of_boundsFibreDegrees
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X)
    (N : ℤ) (hN : BoundsFibreDegrees B S hS W c N) :
    ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X) (n : ℕ) (w : Fin n → (T ⟶ W)),
        (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w → (n : ℤ) ≤ N := by
  intro K hK T eT ξ n w hw hwinj
  obtain ⟨V, p, i, r, hrle, hrank, hsq⟩ := hN K T eT ξ
  have hnr := le_of_injective_lifts_of_isFiniteLocallyFreeOfRank_fibre B S hS W c T eT ξ
    V p i r n hrank hsq w hw hwinj
  omega

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-- **The complement of the diagonals in a self-product of a chart has no points beyond a bound
on the fibre degrees of the chart.** If `d` bounds the fibre degrees of an étale separated
chart `c : W ⟶ X`, then for every `n > d` the complement of the diagonals in the `n`-fold
self-product of the chart has no points. -/
theorem isEmpty_points_diagonalComplement_of_boundsFibreDegrees (W : BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c) (hsep : IsSeparated B S hS c)
    (d : ℕ) (hbound : BoundsFibreDegrees B S hS W c (d : ℤ)) :
    ∀ n : ℕ, d < n →
      IsEmpty (points B S hS (underlying B S hS X
        (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep)).1) := by
  have hd := forall_le_of_boundsFibreDegrees B S hS W c (d : ℤ) hbound
  refine fun n hn ↦ ⟨fun x ↦ ?_⟩
  obtain ⟨z, -⟩ := Quot.exists_rep x
  obtain ⟨w, hwmap⟩ : ∃ w : Fin n → (z.siteObject B S hS _ ⟶ W), ∀ i : Fin n,
      yoneda.map (w i) = (fieldMorphism B S hS _ z ≫ ((toSpaces B S hS X).map
          (diagonalComplementπ B S hS X (chartObj B S hS X W c hc) n hsep i)).hom :
        yoneda.obj (z.siteObject B S hS _) ⟶ yoneda.obj W) :=
    ⟨fun i ↦ yoneda.preimage ((fieldMorphism B S hS _ z ≫ ((toSpaces B S hS X).map
        (diagonalComplementπ B S hS X (chartObj B S hS X W c hc) n hsep i)).hom :
      yoneda.obj (z.siteObject B S hS _) ⟶ yoneda.obj W)),
      fun i ↦ yoneda.map_preimage _⟩
  have hwinj : Function.Injective w := by
    intro a b hab
    by_contra hne
    refine comp_diagonalComplementπ_ne B S hS X (chartObj B S hS X W c hc) n hsep
      (fieldMorphism B S hS _ z) ((z.tautologicalPoint B S hS _).class B S hS _) hne ?_
    exact (hwmap a).symm.trans ((congrArg yoneda.map hab).trans (hwmap b))
  have hwover : ∀ i : Fin n, yoneda.map (w i) ≫ c =
      fieldMorphism B S hS _ z ≫
        (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep).obj.hom.hom := by
    intro i
    rw [hwmap i]
    exact (Category.assoc _ _ _).trans (congrArg (fun k ↦ fieldMorphism B S hS _ z ≫ k)
      (hom_toSpaces_map_diagonalComplementπ_comp B S hS X
        (chartObj B S hS X W c hc) n hsep i))
  have hle := hd z.carrier z.field (z.siteObject B S hS _) (Iso.refl _)
    (fieldMorphism B S hS _ z ≫
      (diagonalComplement B S hS X (chartObj B S hS X W c hc) n hsep).obj.hom.hom)
    n w hwover hwinj
  omega

end SpacesEtale

end AlgebraicGeometry.Space

end
