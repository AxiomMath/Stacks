module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleAffineObjectVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation

/-!
# The affine coverings of an object of the spaces-étale site are cofinal

Let `X` be an algebraic space over a scheme `S`.  An object of the spaces-étale site
`X_{spaces, étale}` of [Stacks, Tag 03G0] is *affine* when its underlying algebraic space is an
affine algebraic space (`AlgebraicGeometry.Space.IsAffineSpace`).  This file proves that the
coverings of an object `V` all of whose members are affine form a cofinal system of coverings of
`V`, in the sense of `Stacks.Cohomology.CofinalCoveringSystem`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.IsAffineObject`: an object of the spaces-étale site with
  affine underlying algebraic space.
* `AlgebraicGeometry.Space.SpacesEtale.affineSchemeCover`: the covering family of an object by all
  arrows into it from objects representable by an affine scheme.
* `AlgebraicGeometry.Space.SpacesEtale.affineCoverings`: the cofinal system of coverings of `V`
  whose members are affine.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.affineSchemeCover_mem`: the family `affineSchemeCover` is a
  covering, by `AlgebraicGeometry.Space.SpacesEtale.generate_affineSchemePresieve_mem`.
* `AlgebraicGeometry.Space.SpacesEtale.affineCoverings`, field `cofinal`: every covering of `V` is
  refined by an affine one, obtained by covering each member by affine schemes.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 0DC5](https://stacks.math.columbia.edu/tag/0DC5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The property of an object of the spaces-étale site of `X` that its underlying algebraic
space is affine. -/
abbrev IsAffineObject : ObjectProperty (SpacesEtale B S hS X) :=
  fun U ↦ IsAffineSpace B S hS U.obj.left.1

/-- The covering family of an object of the spaces-étale site by all the arrows into it out of
objects representable by an affine scheme. -/
def affineSchemeCover (U : SpacesEtale B S hS X) : PreZeroHypercover.{u + 1} U where
  I₀ := Σ Z : SpacesEtale B S hS X, {_g : Z ⟶ U // IsAffineScheme B S hS X Z}
  X i := i.1
  f i := i.2.1

/-- The family of all arrows into `U` out of objects representable by an affine scheme is a
covering family. -/
theorem affineSchemeCover_mem (U : SpacesEtale B S hS X) :
    (affineSchemeCover B S hS X U).sieve₀ ∈ topology B S hS X U := by
  refine GrothendieckTopology.superset_covering _ ?_ (generate_affineSchemePresieve_mem B S hS X U)
  rw [Sieve.generate_le_iff]
  intro Z g hg
  exact Sieve.ofArrows_mk _ (affineSchemeCover B S hS X U).f ⟨Z, g, hg⟩

/-- Every member of `affineSchemeCover` is affine. -/
theorem isAffineObject_affineSchemeCover (U : SpacesEtale B S hS X)
    (i : (affineSchemeCover B S hS X U).I₀) :
    IsAffineObject B S hS X ((affineSchemeCover B S hS X U).X i) :=
  isAffineSpace_of_isAffineScheme B S hS X _ i.2.2

/-- **The cofinal system of affine coverings** of an object `V` of the spaces-étale site: the
coverings of `V` all of whose members have affine underlying algebraic space.  It is cofinal
because every member of a covering is in turn covered by affine schemes. -/
def affineCoverings (V : SpacesEtale B S hS X) :
    Stacks.Cohomology.CofinalCoveringSystem (topology B S hS X) V where
  cov := fun 𝒰 ↦ 𝒰.sieve₀ ∈ topology B S hS X V ∧ ∀ i, IsAffineObject B S hS X (𝒰.X i)
  isCover := fun _ h ↦ h.1
  cofinal := by
    intro 𝒰 h𝒰
    refine ⟨𝒰.bind (fun i ↦ affineSchemeCover B S hS X (𝒰.X i)), ⟨?_, fun j ↦
      isAffineObject_affineSchemeCover B S hS X _ j.2⟩,
      ⟨{ s₀ := fun j ↦ j.1, h₀ := fun j ↦ (affineSchemeCover B S hS X (𝒰.X j.1)).f j.2 }⟩⟩
    refine (topology B S hS X).transitive h𝒰 _ ?_
    intro Y f hf
    obtain ⟨Z, a, b, ⟨i⟩, rfl⟩ := hf
    refine (topology B S hS X).superset_covering ?_ ((topology B S hS X).pullback_stable a
      (affineSchemeCover_mem B S hS X (𝒰.X i)))
    intro W g hg
    obtain ⟨_, c, _, ⟨j⟩, hcd⟩ := hg
    refine ⟨_, c, (affineSchemeCover B S hS X (𝒰.X i)).f j ≫ 𝒰.f i,
      (𝒰.bind fun i ↦ affineSchemeCover B S hS X (𝒰.X i)).presieve₀_f ⟨i, j⟩, ?_⟩
    rw [← Category.assoc, hcd, Category.assoc]

end AlgebraicGeometry.Space.SpacesEtale
