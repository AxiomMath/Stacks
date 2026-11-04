module

public import StacksFrontier.RingTheory.Dualizing.GorensteinOfDualizingQuotient
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic

/-!
# The pointwise end of the proof of [Stacks, Tag 0BBV]

Let `A` be a Noetherian domain with a dualizing module `ω_A`, isomorphic to a nonzero ideal `J`,
and let `f : X ⟶ Spec(A)` be a morphism from a locally Noetherian integral scheme such that
`A ⟶ 𝒪_{X,x}` is injective at every point. The proof of [Stacks, Tag 0BBV] concludes that `X` is
Gorenstein from two facts at every singular point `x` of `X`: some dualizing module of `𝒪_{X,x}`
is a quotient of `𝒪_{X,x} ⊗_A ω_A` (the canonical map `f^*ω_A ⟶ ω_X` is surjective at `x`, which
is [Stacks, Tag 0B64] (3) propagated along the sequence of blowups), and `J 𝒪_{X,x}` is
principal (`X` dominates the blowup of `Spec(A)` in `J`). Regular local rings are Gorenstein
([Stacks, Tag 0AWX]).

## Main definitions

* `AlgebraicGeometry.DualizingQuotientAt`: some dualizing module of `𝒪_{X,x}` is a quotient of
  `𝒪_{X,x} ⊗_A ω_A`.

## Main results

* `AlgebraicGeometry.isGorenstein_of_forall_not_isRegularLocalRing`: a locally Noetherian scheme
  whose non-regular local rings are Gorenstein is Gorenstein.
* `AlgebraicGeometry.isGorenstein_of_dualizingQuotientAt`: the end of the proof of 0BBV.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- A locally Noetherian scheme whose non-regular local rings are Gorenstein is Gorenstein:
regular local rings are Gorenstein ([Stacks, Tag 0AWX]). -/
theorem isGorenstein_of_forall_not_isRegularLocalRing (X : Scheme.{u}) [IsLocallyNoetherian X]
    (h : ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
      Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x)) : IsGorenstein X where
  isGorensteinLocalRing x := by
    by_cases hx : IsRegularLocalRing (X.presheaf.stalk x)
    · exact Dualizing.IsRegularLocalRing.isGorensteinLocalRing _
    · exact h x hx

/-- The ring map `A ⟶ 𝒪_{X,x}` of a scheme over `Spec(A)`. -/
abbrev stalkAlgebraOfSpec (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (x : X) : A →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom

/-- **Some dualizing module of `𝒪_{X,x}` is a quotient of `𝒪_{X,x} ⊗_A ω_A`.** For the dualizing
module `ω_X` of [Stacks, Tag 0BBU] this says that the canonical map `f^*ω_A ⟶ ω_X` is surjective
on stalks at `x`, the stalk of `f^*ω_A` being `𝒪_{X,x} ⊗_A ω_A`. -/
def DualizingQuotientAt (A : Type u) [CommRing A] (ωA : Type u) [AddCommGroup ωA] [Module A ωA]
    {X : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Spec (.of A)) (x : X) : Prop :=
  letI : Algebra A (X.presheaf.stalk x) := (stalkAlgebraOfSpec A f x).toAlgebra
  ∃ (ω : Type u) (_ : AddCommGroup ω) (_ : Module (X.presheaf.stalk x) ω),
    Stacks.Duality.IsDualizingRingModule (X.presheaf.stalk x) ω ∧
      ∃ π : X.presheaf.stalk x ⊗[A] ωA →ₗ[X.presheaf.stalk x] ω, Function.Surjective π

/-- **The end of the proof of [Stacks, Tag 0BBV].** Let `A` be a Noetherian domain whose
dualizing module `ω_A` is isomorphic to the nonzero ideal `J`, and `f : X ⟶ Spec(A)` a morphism
from a locally Noetherian integral scheme with `A ⟶ 𝒪_{X,x}` injective. If at every singular
point `x` the ideal `J 𝒪_{X,x}` is principal and a dualizing module of `𝒪_{X,x}` is a quotient of
`𝒪_{X,x} ⊗_A ω_A`, then `X` is Gorenstein. -/
theorem isGorenstein_of_dualizingQuotientAt (A : Type u) [CommRing A] [IsDomain A]
    (ωA : Type u) [AddCommGroup ωA] [Module A ωA] {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsIntegral X] (f : X ⟶ Spec (.of A))
    (hinj : ∀ x : X, Function.Injective (stalkAlgebraOfSpec A f x))
    (J : Ideal A) (hJ : J ≠ ⊥) (eJ : ωA ≃ₗ[A] J)
    (hprinc : ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
      ∃ t : X.presheaf.stalk x, Ideal.map (stalkAlgebraOfSpec A f x) J = Ideal.span {t})
    (hQ : ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) → DualizingQuotientAt A ωA f x) :
    IsGorenstein X := by
  refine isGorenstein_of_forall_not_isRegularLocalRing X fun x hx => ?_
  let : Algebra A (X.presheaf.stalk x) := (stalkAlgebraOfSpec A f x).toAlgebra
  obtain ⟨t, ht⟩ := hprinc x hx
  obtain ⟨ω, _, _, hω, π, hπ⟩ := hQ x hx
  exact Dualizing.isGorensteinLocalRing_of_surjective_tensor_of_linearEquiv_ideal (hinj x) J hJ t
    ht eJ hω π hπ

end AlgebraicGeometry

end
