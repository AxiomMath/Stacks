module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth
public import StacksFrontier.AlgebraicGeometry.Conormal.SmoothRank
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEtaleSection
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.PreimageDimension

/-!
# Local complete intersection morphisms of a given relative dimension: examples

Two facts about the conditions of relative dimension used for part (2) of Stacks tag 0AZN.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphismOfRelativeDimension_affineSpace`: the
  projection `𝐀^n_Y ⟶ Y` is a local complete intersection morphism of relative dimension `n`,
  in the sense of `AlgebraicGeometry.IsLocalCompleteIntersectionMorphismOfRelativeDimension`.
  In particular that condition is satisfiable for every `n ≥ 0`.
* `AlgebraicGeometry.not_isLocalCompleteIntersectionOfRelativeDimension_of_pos`: the condition
  `AlgebraicGeometry.IsLocalCompleteIntersectionOfRelativeDimension` holds for no morphism when
  `r ≥ 1`, because it imposes its rank condition also on the factorization over the empty open.

## References

* [Stacks Project, Tag 0AZN](https://stacks.math.columbia.edu/tag/0AZN)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The projection `𝐀^n_Y ⟶ Y` is a local complete intersection morphism of relative dimension
`n`: over the whole of `𝐀^n_Y` it factors as the identity immersion of `𝐀^n_Y`, a closed
immersion of smooth `Y`-schemes and hence Koszul-regular, whose conormal sheaf has rank
`n - n = 0`, followed by the projection. -/
theorem isLocalCompleteIntersectionMorphismOfRelativeDimension_affineSpace (Y : Scheme.{u})
    (n : ℕ) :
    IsLocalCompleteIntersectionMorphismOfRelativeDimension (𝔸(ULift.{u} (Fin n); Y) ↘ Y) n := by
  have := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver Y n
  have : Smooth (𝔸(ULift.{u} (Fin n); Y) ↘ Y) := SmoothOfRelativeDimension.smooth n _
  intro x
  let U : (𝔸(ULift.{u} (Fin n); Y)).Opens := ⊤
  have : SmoothOfRelativeDimension n (U.ι ≫ (𝔸(ULift.{u} (Fin n); Y) ↘ Y)) := by
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + n)
      (U.ι ≫ (𝔸(ULift.{u} (Fin n); Y) ↘ Y)))
  have : Smooth (U.ι ≫ (𝔸(ULift.{u} (Fin n); Y) ↘ Y)) := SmoothOfRelativeDimension.smooth n _
  have : IsIso U.ι := by
    change IsIso (⊤ : (𝔸(ULift.{u} (Fin n); Y)).Opens).ι
    rw [← Scheme.topIso_hom]
    infer_instance
  refine ⟨ULift.{u} (Fin n), inferInstance, U, trivial, U.ι, inferInstance,
    Stacks.Gysin.isKoszulRegularImmersion_of_smooth_of_smooth U.ι (𝔸(ULift.{u} (Fin n); Y) ↘ Y),
    rfl, 0, ?_, by simp⟩
  have h := Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension
    U.ι (𝔸(ULift.{u} (Fin n); Y) ↘ Y) n n
  rw [Nat.sub_self] at h
  exact h

/-- The condition `AlgebraicGeometry.IsLocalCompleteIntersectionOfRelativeDimension f r` fails
for every morphism `f` when `r ≥ 1`. Its second clause applies to the empty open `U = ⊥` with
`J` empty: the unique morphism `∅ ⟶ 𝐀^∅_Y` is an immersion, it is Koszul-regular because the
support of the quotient by its defining ideal sheaf is empty, and the factorization through it
holds trivially, so the clause demands `0 = r + c` for some `c : ℕ`. -/
theorem not_isLocalCompleteIntersectionOfRelativeDimension_of_pos {X Y : Scheme.{u}}
    (f : X ⟶ Y) {r : ℤ} (hr : 0 < r) :
    ¬ IsLocalCompleteIntersectionOfRelativeDimension f r := by
  intro h
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x => by simpa using x.2⟩
  let i : (⊥ : X.Opens).toScheme ⟶ AffineSpace PEmpty.{u + 1} Y :=
    isInitialOfIsEmpty.to _
  have hi : IsImmersion i := inferInstance
  have hkos : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion i := by
    intro x hx
    have hx' := (mem_idealQuotientSupport_definingIdealOfHom_iff i.liftCoborder x).mp hx
    rw [Set.range_eq_empty, closure_empty] at hx'
    exact hx'.elim
  obtain ⟨c, -, hc⟩ := h.2 PEmpty (⊥ : X.Opens) i hi hkos (isInitialOfIsEmpty.hom_ext _ _)
  simp only [Fintype.card_ofIsEmpty, Nat.cast_zero] at hc
  omega

end AlgebraicGeometry

end
