module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# A monomorphism which is a closed immersion on a thickening

Let `r : Q ⟶ W` be a monomorphism of schemes which is locally of finite type, with `W` affine,
and let `j : P ⟶ Q` be a thickening such that `j ≫ r` is a closed immersion. Then `r` itself
is a closed immersion.

The proof is the ring-theoretic half of the argument of Stacks 0AJ6. Affineness of `Q` is
affineness of a thickening of the affine scheme `P` (Stacks 06AD). The ring map on global
sections `Γ(W, ⊤) ⟶ Γ(Q, ⊤)` is then an epimorphism of rings, because `r` is a monomorphism of
affine schemes, and it is of finite type, because `r` is locally of finite type. Every section of
`Q` becomes a section pulled back from `W` after restricting to `P`, and the kernel of
restriction to a thickening of a quasi-compact scheme consists of nilpotents, so every section of
`Q` differs from one pulled back from `W` by a nilpotent. Hence `Γ(Q, ⊤)` is integral over
`Γ(W, ⊤)`, so finite, and a finite epimorphism of rings is surjective (Stacks 04VT) — which for
a morphism of affine schemes is exactly the closed immersion condition.

## Main results

* `RingHom.surjective_of_epi_of_finiteType_of_forall_isNilpotent_sub`: a ring epimorphism of
  finite type each of whose target elements differs from an element of the image by a nilpotent
  is surjective.
* `AlgebraicGeometry.isClosedImmersion_of_isThickening_of_mono`: the statement above.

## References

* [Stacks Project, Tag 01WJ](https://stacks.math.columbia.edu/tag/01WJ)
* [Stacks Project, Tag 04VT](https://stacks.math.columbia.edu/tag/04VT)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory

universe u

/-- **A ring epimorphism of finite type whose target is a nilpotent thickening of the image is
surjective.** If `φ : R ⟶ C` is an epimorphism of commutative rings which is of finite type and
every element of `C` differs from an element of the image of `φ` by a nilpotent element, then
`φ` is surjective.

Each element of `C` is a root of a power of a linear monic polynomial over `R`, so `C` is
integral over `R`; being also of finite type it is a finite `R`-module, and a finite epimorphism
of rings is surjective. -/
theorem RingHom.surjective_of_epi_of_finiteType_of_forall_isNilpotent_sub
    {R C : CommRingCat.{u}} (φ : R ⟶ C) [Epi φ] (hft : RingHom.FiniteType φ.hom)
    (hnil : ∀ c : C, ∃ x : R, IsNilpotent (c - φ.hom x)) :
    Function.Surjective φ := by
  have hint : φ.hom.IsIntegral := by
    intro c
    obtain ⟨x, n, hn⟩ := hnil c
    refine ⟨(Polynomial.X - Polynomial.C x) ^ n, (Polynomial.monic_X_sub_C x).pow n, ?_⟩
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact hn
  exact RingHom.surjective_iff_epi_and_finite.mpr
    ⟨‹_›, RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨hint, hft⟩⟩

namespace AlgebraicGeometry

/-- **A monomorphism locally of finite type into an affine scheme which is a closed immersion on
a thickening of its source is a closed immersion.** Let `r : Q ⟶ W` be a monomorphism of schemes
which is locally of finite type, with `W` affine, and let `j : P ⟶ Q` be a thickening for which
`j ≫ r` is a closed immersion. Then `r` is a closed immersion.

The source `P` of the closed immersion `j ≫ r` is affine and `j ≫ r` is surjective on global
sections; hence `Q` is affine, being a thickening of an affine scheme. The map
`Γ(W, ⊤) ⟶ Γ(Q, ⊤)` is an epimorphism of rings, `r` being a monomorphism of affine schemes, and
of finite type, `r` being locally of finite type between affine schemes. Every section of `Q`
differs from one pulled back along `r` by a section killed by restriction along `j`, hence by a
nilpotent. So the map on global sections is surjective and `r` is a closed immersion. -/
theorem isClosedImmersion_of_isThickening_of_mono {P Q W : Scheme.{u}} [IsAffine W]
    (r : Q ⟶ W) [Mono r] [LocallyOfFiniteType r] {j : P ⟶ Q}
    (hj : Stacks.Thickenings.IsThickening j) (hjr : IsClosedImmersion (j ≫ r)) :
    IsClosedImmersion r := by
  obtain ⟨_, hPsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (j ≫ r)
  have _ : IsAffine Q := Stacks.Thickenings.isAffine_of_isThickening hj
  have _ : Epi r.appTop := by simpa using epi_appTop_of_mono r
  have hft : RingHom.FiniteType r.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp ‹_›
  refine IsClosedImmersion.of_surjective_of_isAffine r
    (RingHom.surjective_of_epi_of_finiteType_of_forall_isNilpotent_sub r.appTop hft ?_)
  intro c
  obtain ⟨x, hx⟩ := hPsurj (j.appTop c)
  have hx' : (j ≫ r).appTop.hom x = j.appTop.hom c := hx
  have hcomp : (j ≫ r).appTop.hom x = j.appTop.hom (r.appTop.hom x) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  refine ⟨x, hj.isNilpotent_of_mem_ker_appTop_of_compactSpace ?_⟩
  rw [RingHom.mem_ker, map_sub, ← hcomp, hx', sub_self]

end AlgebraicGeometry

end
