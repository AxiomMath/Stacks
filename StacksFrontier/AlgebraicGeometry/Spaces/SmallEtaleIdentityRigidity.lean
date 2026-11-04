module

public import StacksFrontier.CategoryTheory.Sites.SubcanonicalIdentityEndomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBaseChangePresieve
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct

/-!
# Rigidity of the identity of the small étale topos of an algebraic space

Let `X` be an algebraic space over a scheme `S`. A natural endomorphism `τ` of the identity
functor of the topos `Sh(X_étale)` of sheaves of sets on the small étale site of `X` which is
the identity on the underlying sheaf of sets of the structure sheaf `𝒪_X` is the identity.

The condition on `𝒪_X` cannot be dropped: for `X = Spec ℝ` the topos is that of `Gal(ℂ/ℝ)`-sets
and the action of complex conjugation is a nontrivial natural automorphism of the identity; it
acts on `𝒪_X(Spec ℂ) = ℂ` by conjugation.

## Main results

* `AlgebraicGeometry.Space.smallEtale_identityEnd_eq_id`: a natural endomorphism of the identity
  of `Sh(X_étale)` which is the identity on `𝒪_X` is the identity.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A natural endomorphism of the identity of `Sh(X_étale)` which fixes `𝒪_X` is the
identity.** -/
theorem smallEtale_identityEnd_eq_id (X : AlgebraicSpaces B S hS)
    (τ : 𝟭 (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) ⟶ 𝟭 _)
    (hτ : τ.app ((smallEtaleRingedTopos B S hS X).forgetRing.obj
      (smallEtaleRingedTopos B S hS X).O) = 𝟙 _) :
    τ = 𝟙 _ := by
  have := smallEtaleTopology_subcanonical B S hS X
  refine GrothendieckTopology.identityEnd_eq_id_of_generate _ τ
    (SmallEtale.affineChartPresieve B S hS X.1)
    (SmallEtale.generate_affineChartPresieve_mem B S hS X.1) fun U V g hV => ?_
  have : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) := hV
  apply (SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map_injective
  rw [CategoryTheory.Functor.map_id]
  apply ext_of_isAffine
  ext s
  have h := GrothendieckTopology.identityEnd_app_apply _ τ
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O) V s
  rw [hτ] at h
  exact h.symm

end AlgebraicGeometry.Space
