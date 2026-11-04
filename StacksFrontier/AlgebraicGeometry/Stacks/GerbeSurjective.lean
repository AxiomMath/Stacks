module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage

/-!
# A gerbe morphism of algebraic stacks is surjective (Stacks 06QI, surjectivity)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` exhibiting `𝒳` as a gerbe over
`𝒴` for the localized big fppf topology, in the sense of Stacks 06P2 — the predicate
`CategoryTheory.IsGerbeOver` on which Stacks 06QC registers the relative notion. Then `f` is
surjective: the map it induces on the point sets of Stacks 04XG is surjective.

Surjectivity separates from the other two conclusions of Stacks 06QI. Flatness and local
finite presentation of a 1-morphism are conditions on a *smooth diagram* of algebraic spaces
over `f` (Stacks 06PW and 06Q2 over the tests of Stacks 06FM), and the source proves them by
descending along a surjective, flat and locally finitely presented base change until `𝒴` is an
algebraic space and `𝒳` is a quotient stack. Surjectivity is instead a condition on points
alone (Stacks 04ZS), and the gerbe hypothesis gives it directly: by Stacks 06P1 (2)(a) every
object of a fibre of `𝒴` acquires a lift to `𝒳` after restriction along a covering sieve, and a
covering sieve of a field spectrum contains an arrow from a field spectrum, so every object
over a field lifts after a field extension. That is exactly surjectivity *on objects* in the
sense of Stacks 06D4, which Stacks 04XI turns into surjectivity on points.

The one geometric input is therefore the passage from a covering sieve to a field-valued
member of it. A covering sieve of the big fppf site of `S` contains a flat, locally finitely
presented, jointly surjective family
(`AlgebraicGeometry.exists_family_of_mem_topology`); joint surjectivity applied to a point of
the field spectrum selects a member through which that point is hit; and a point of a scheme
in the site is dominated by a field spectrum in the site, because an affine open around it is
again an object of the site (the source of an open immersion, Stacks 000R (3)) and a nonempty
affine scheme in the site receives a morphism from a field spectrum in the site
(`AlgebraicGeometry.Space.exists_fieldSpec_of_isAffine`). Sieves are closed under
precomposition, so the resulting arrow from the field spectrum belongs to the sieve.

## Main results

* `AlgebraicGeometry.Space.exists_fieldSpec_of_contains`: a nonempty scheme in a big fppf site
  receives a morphism from a field spectrum which is again an object of the site. This drops
  the affineness hypothesis of
  `AlgebraicGeometry.Space.exists_fieldSpec_of_isAffine`.
* `AlgebraicGeometry.Stack.exists_isFieldObject_arrow_of_mem_topology`: a covering sieve of an
  object of the big fppf site of `S` whose underlying scheme is the spectrum of a field
  contains an arrow whose source is again the spectrum of a field.
* `AlgebraicGeometry.Stack.isSurjective_of_isGerbeOver`: **Stacks 06QI**, the surjectivity
  clause.

## Implementation notes

The source and target objects of the sieve arrow are named before being assembled, rather than
written inline into the existential: the arrow out of the field spectrum is a morphism of the
size-bounded full subcategory wrapping a morphism of schemes, and leaving the target of the
family member to be inferred from the arrow leaves the wrapper's object field as a
metavariable.

The object of `𝒳` produced by Stacks 06P1 (2)(a) lies over the source of the sieve arrow by
`CategoryTheory.BasedFunctor.w_obj` composed with
`CategoryTheory.IsHomLift.domain_eq`: the lifting datum records the image of the object under
the target's structural functor, and the based functor underlying `f` commutes with the two
structural functors, so the image under the source's structural functor agrees.

## References

* [Stacks Project, Tag 06QI](https://stacks.math.columbia.edu/tag/06QI)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Space

universe u

/-- A nonempty scheme in a big fppf site receives a morphism from the spectrum of a field which
is itself an object of the site.

An affine open around the given point is an object of the site, being the source of an open
immersion into one, and `AlgebraicGeometry.Space.exists_fieldSpec_of_isAffine` applies to it. -/
theorem exists_fieldSpec_of_contains (B : BigFppfSite.{u}) (X : Scheme.{u}) (x : X)
    (hX : B.Contains X) :
    ∃ (K : Type u) (_ : Field K), ∃ _ : B.Contains (Spec (.of K)),
      Nonempty (Spec (.of K) ⟶ X) := by
  obtain ⟨A, j, hj, y, -⟩ := Scheme.exists_Spec_apply_eq x
  obtain ⟨K, instK, hK, ⟨c⟩⟩ :=
    exists_fieldSpec_of_isAffine B (Spec A) y (Scheme.size_lt_of_isOpenImmersion j hX)
  exact ⟨K, instK, hK, ⟨c ≫ j⟩⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

/-- A covering sieve of an object of the big fppf site of `S` whose underlying scheme is the
spectrum of a field contains an arrow whose source is again the spectrum of a field.

The sieve contains a flat, locally finitely presented and jointly surjective family; joint
surjectivity at a point of the field spectrum selects a member hitting it, that member's source
is dominated by a field spectrum in the site, and the sieve is closed under precomposition. -/
theorem exists_isFieldObject_arrow_of_mem_topology
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigFppfOver B S hS} (hU : IsFieldObject B S hS U)
    {R : Sieve U} (hR : R ∈ BigFppfOver.topology B S hS U) :
    ∃ (V : BigFppfOver B S hS) (g : V ⟶ U), IsFieldObject B S hS V ∧ R.arrows g := by
  obtain ⟨I, W, m, harrows, -, -, hsurj⟩ := exists_family_of_mem_topology B S hS hR
  obtain ⟨k, instk, ⟨e⟩⟩ := hU
  let _ : Field k := instk
  obtain ⟨i, w, -⟩ := hsurj (e.inv.base (Classical.arbitrary (Spec (.of k))))
  obtain ⟨K, instK, hK, ⟨c⟩⟩ :=
    Space.exists_fieldSpec_of_contains B (B.inclusion.obj (W i)) w (W i).property
  let _ : Field K := instK
  let c' : B.obj hK ⟶ W i := ⟨c⟩
  let T : BigFppfOver B S hS := Over.mk (m i ≫ U.hom)
  let V : BigFppfOver B S hS := Over.mk (c' ≫ m i ≫ U.hom)
  let h : V ⟶ T := Over.homMk c'
  let t : T ⟶ U := Over.homMk (m i)
  exact ⟨V, h ≫ t, ⟨K, instK, ⟨Iso.refl _⟩⟩, R.downward_closed (harrows i) h⟩

/-- **Stacks 06QI**, surjectivity. A 1-morphism of algebraic stacks over `S` whose underlying
functor exhibits its source as a gerbe over its target for the localized big fppf topology is
surjective.

Stacks 06P1 (2)(a) lifts an object of a fibre of the target along a covering sieve; the sieve
contains an arrow from a field spectrum, so an object over a field lifts after a field
extension, which is surjectivity on objects in the sense of Stacks 06D4; and Stacks 04XI
identifies that with surjectivity of the map on points. -/
@[stacks 06QI "surjective"]
theorem isSurjective_of_isGerbeOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴)
    (hf : CategoryTheory.IsGerbeOver
      (BigFppfOver.topology B S hS)
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)) :
    IsSurjective B S hS f := by
  refine pointsMap_surjective_of_isSurjectiveOnObjects B S hS f ?_
  intro U hU y hy
  obtain ⟨R, hR, hcov⟩ := hf.locally_essSurj y hy
  obtain ⟨V, g, hV, hgR⟩ := exists_isFieldObject_arrow_of_mem_topology B S hS hU hR
  obtain ⟨x, ψ, hψ⟩ := hcov g hgR
  have := hψ
  refine ⟨V, hV, g, x, ?_, ψ, hψ⟩
  exact (BasedFunctor.w_obj f.hom.hom x).symm.trans
    (IsHomLift.domain_eq 𝒴.val.val.p g ψ)

end AlgebraicGeometry.Stack

end
