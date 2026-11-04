module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruples

/-!
# Quadruples of a restricted graded algebra and the base change of the relative Proj

In Situation 0849 let `X` be an algebraic space over a scheme `S`, let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra and let `F` be the functor of quadruples of Stacks 084A.  Stacks 084B
asserts, for a morphism `g : Z ⟶ X`, a canonical isomorphism `Proj_Z(g^*𝒜) = Z ×_X F`; the
source proves it by introducing the functor `F'` of quadruples of the restricted algebra
`g^*𝒜` on `Z`, exhibiting `F' = Z ×_X F` — "the verification is omitted" — and quoting the
representability of `F'` by `Proj_Z(g^*𝒜)`.

This file is the first of those two steps, and it is the step whose verification the source
omits: the restriction of the datum of Stacks 084A along `g`, and the canonical bijection
between the value of `F'` at a test object and the value of `Z ×_X F` there.  The map is
`(d, f : T ⟶ Z, ℒ, ψ) ↦ (d, g ∘ f, ℒ, ψ)`, which is the source's own formula.

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.toBaseChange` is the comparison map
  `F'(T) ⟶ (Z ×_X F)(T)`, that is the source's `(d, f, ℒ, ψ) ↦ (d, g ∘ f, ℒ, ψ)`.

The restriction `g^*𝒜` of the datum of Stacks 084A along a morphism `g : Z ⟶ X` — the family
whose algebra at a `T`-point `f` of `Z` is the algebra of the original family at the `T`-point
`f ≫ g` of `X` — is `AlgebraicGeometry.Space.GradedAlgebraPoints.comap`, which is already in the
tree in `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjBaseChange.lean` and is reused here
rather than redefined.

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.bijective_toBaseChange` is **the canonical
  isomorphism `F' = Z ×_X F` of Stacks 084B**, at every test object: the comparison map is
  bijective.  `…F.toBaseChangeEquiv` packages it as a bijection, and
  `…F.toBaseChangeEquiv_apply` says it is computed by the formula above.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.comap_comp` is the **compatibility with further
  base change**: `g'^*(g^*𝒜) = (g ∘ g')^*𝒜`.  `…comap_id` says restricting along the identity
  changes nothing.
* `AlgebraicGeometry.Space.GradedAlgebraPoints.F.toBaseChange_comp` and
  `…F.point_toBaseChange_comp` are that compatibility for the comparison map itself: iterating
  the comparison leaves the class of quadruples untouched and records the composite point.

Everything here is proved outright from the datum of Stacks 084A — the same datum
`AlgebraicGeometry.Space.GradedAlgebraPoints.F` of Stacks 084A is built from — and from a
morphism `g`.  No result is assumed.

## Implementation notes

**Why the comparison is a bijection and not an equality of functors.**  Stacks 084A is
formalized in this library as the *value* `AlgebraicGeometry.Space.GradedAlgebraPoints.F` of the
functor on each test object and not as a functor, because the pullback of a quadruple along a
morphism of test schemes is not constructed; the reason is recorded in the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruples.lean`.  So `Z ×_X F` is likewise
only available object by object, as the set of pairs consisting of a `T`-point of `Z` and a
point of `F(T)` lying over its image in `X`, and the content of the source's identification is
that the comparison map is bijective at each test object.  That is what is proved.  Nothing is
weakened: the map is the source's formula, and both sides are the sets the source compares.

**The comparison map needs no transport.**  A point of `F'(T)` is a pair of a `T`-point `f` of
`Z` and a class of quadruples of `(g^*𝒜)` at `f`, and the algebra of `g^*𝒜` at `f` is *by
definition* the algebra of `𝒜` at `f ≫ g`, so the class of quadruples already has the type the
target asks for.  This is why `AlgebraicGeometry.Space.GradedAlgebraPoints.comap` is defined by
reindexing the family rather than by pulling the algebras back: the comparison map is then
cast-free and its two components are literally the source's `g ∘ f` and `ψ`.  The inverse is
not written out — it needs the transport along the fibre equation — which is why the result is
stated as bijectivity and the bijection is obtained from it; the *definition*
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.toBaseChange` has a body, so
`…F.toBaseChangeEquiv_apply` holds and the bijection is computed by the formula.

**What this does not give.**  The second step of the source's proof is the representability of
`F'` by `Proj_Z(g^*𝒜)`, and that step *is* available: the scheme-level representability of the
functor of quadruples is proved in this library unconditionally, under Situation 01NN alone, as
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.isRepresentable_limFunctor` (Stacks 01NY) and
`...RelativeProjQcohSheaf.relativeProjRepresentableByFunctorUnconditional` (Stacks 01NZ).  It is
fed into the datum of Stacks 084A in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruplesRepresentability.lean`, which needs
the restricted algebras to be quasi-coherent — a `SheafGradedAlgebra` at each scheme point —
where `AlgebraicGeometry.Space.GradedAlgebraPoints` records only a bare graded algebra.  What is
still missing for the full isomorphism `Proj_Z(g^*𝒜) = Z ×_X F` is recorded there: the image of
a fibre among the morphisms into the relative homogeneous spectrum is not identified as the set
of sections, which needs the representation to be a representation over the base, the field
`homEquiv_symm_incl_comp_toBase` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RepresentingProjData`.  That field is the only
part of `RepresentingProjData` still owed; its `representableBy` field is now a theorem.
Separately, the restriction `g^*𝒜` is a datum of
`AlgebraicGeometry.Space.GradedAlgebraPoints` rather than a construction out of `𝒜`.  That is
not because the restriction is unavailable — it is available, and the pieces are listed in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjQuadruples.lean`, which also record the two
narrow things that stand in the way of assembling them into the family: the chain runs only at
the second universe parameter `= u`, and the comparison `g^*(f^*𝒜) ≅ (f ∘ g)^*𝒜` is not
transported from the small étale site through the chart restriction.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace GradedAlgebraPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : GradedAlgebraPoints B S hS X)

/-! ### The restriction of the datum along a morphism -/

/-- Two restriction data are equal when their algebras agree at every point. -/
private theorem eq_of_algebra_eq {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p q : GradedAlgebraPoints B S hS Y} (h : ∀ T f, p.algebra T f = q.algebra T f) : p = q :=
  congrArg GradedAlgebraPoints.mk (funext fun T => funext (h T))

/-- **Compatibility with further base change.** Restricting along `g' : W ⟶ Z` the restriction
along `g : Z ⟶ X` is restricting along the composite: `g'^*(g^*𝒜) = (g ∘ g')^*𝒜`.

The restricted datum is the original family reindexed along composition with `g`, so this is
the associativity of composition in the site. -/
theorem comap_comp {Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ X) (g' : W ⟶ Z) :
    (r.comap g).comap g' = r.comap (g' ≫ g) :=
  eq_of_algebra_eq fun _ f => congrArg (r.algebra _) (Category.assoc f g' g)

/-- Restricting along the identity changes nothing. -/
theorem comap_id : r.comap (CategoryTheory.CategoryStruct.id X) = r :=
  eq_of_algebra_eq fun _ f => congrArg (r.algebra _) (Category.comp_id f)

/-! ### The canonical isomorphism `F' = Z ×_X F` -/

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ X)

/-- **The value of `Z ×_X F` at a test object.** A `T`-point of `Z` together with a point of
`F(T)` whose `T`-point of `X` is its image under `g`. -/
abbrev F.BaseChange (T : BigFppfOver B S hS) : Type (u + 1) :=
  Σ f : yoneda.obj T ⟶ Z, {ξ : r.F T // F.point r ξ = f ≫ g}

/-- **The comparison map `F'(T) ⟶ (Z ×_X F)(T)` of Stacks 084B**, that is the source's
`(d, f : T ⟶ Z, ℒ, ψ) ↦ (d, g ∘ f, ℒ, ψ)`.

No transport is involved: the algebra of `g^*𝒜` at a `T`-point `f` of `Z` is by definition the
algebra of `𝒜` at `f ≫ g`, so the class of quadruples is already a class of quadruples over the
`T`-point `f ≫ g` of `X`. -/
def F.toBaseChange {T : BigFppfOver B S hS} (ξ : (r.comap g).F T) : F.BaseChange r g T :=
  ⟨ξ.1, ⟨⟨ξ.1 ≫ g, ξ.2⟩, rfl⟩⟩

/-- The comparison map does not change the `T`-point of `Z`. -/
@[simp] theorem F.toBaseChange_fst {T : BigFppfOver B S hS} (ξ : (r.comap g).F T) :
    (F.toBaseChange r g ξ).1 = ξ.1 :=
  rfl

/-- **The comparison map `F' ⟶ Z ×_X F` is bijective at every test object.**

A point of `Z ×_X F` over a `T`-point `f` of `Z` is a class of quadruples over the `T`-point
`f ≫ g` of `X`, which is exactly a class of quadruples of the restricted algebra over `f`. -/
theorem F.bijective_toBaseChange (T : BigFppfOver B S hS) :
    Function.Bijective (F.toBaseChange r g (T := T)) := by
  constructor
  · rintro ⟨f, q⟩ ⟨f', q'⟩ hfull
    obtain rfl : f = f' := congrArg Sigma.fst hfull
    have h2 : (⟨f ≫ g, q⟩ : r.F T) = ⟨f ≫ g, q'⟩ := congrArg (fun p => p.2.1) hfull
    exact congrArg (Sigma.mk f) (eq_of_heq (Sigma.mk.inj h2).2)
  · rintro ⟨f, ⟨⟨k, q⟩, hk⟩⟩
    obtain rfl : k = f ≫ g := hk
    exact ⟨⟨f, q⟩, rfl⟩

/-- **The canonical isomorphism `F' = Z ×_X F` of Stacks 084B**, packaged as a bijection onto
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.BaseChange`.  It is the comparison map, by
`AlgebraicGeometry.Space.GradedAlgebraPoints.F.toBaseChangeEquiv_apply`. -/
def F.toBaseChangeEquiv (T : BigFppfOver B S hS) : (r.comap g).F T ≃ F.BaseChange r g T :=
  Equiv.ofBijective _ (F.bijective_toBaseChange r g T)

/-- The bijection `F.toBaseChangeEquiv` is given by the comparison map `F.toBaseChange`. -/
@[simp] theorem F.toBaseChangeEquiv_apply (T : BigFppfOver B S hS) (ξ : (r.comap g).F T) :
    F.toBaseChangeEquiv r g T ξ = F.toBaseChange r g ξ :=
  rfl

/-- **The comparison maps compose.** For `g' : W ⟶ Z`, applying the comparison map of `g'` and
then that of `g` to the resulting point of `(g^*𝒜)`'s functor leaves the class of quadruples
untouched and records the composite point of the base. -/
theorem F.toBaseChange_comp {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g' : W ⟶ Z)
    {T : BigFppfOver B S hS} (ξ : ((r.comap g).comap g').F T) :
    F.toBaseChange r g (F.toBaseChange (r.comap g) g' ξ).2.1 =
      ⟨ξ.1 ≫ g', ⟨⟨(ξ.1 ≫ g') ≫ g, ξ.2⟩, rfl⟩⟩ :=
  rfl

/-- The point of `X` the iterated comparison records is the composite `g ∘ g' ∘ f`, which is
the point the comparison map of `g' ≫ g` records. -/
theorem F.point_toBaseChange_comp {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g' : W ⟶ Z)
    {T : BigFppfOver B S hS} (ξ : ((r.comap g).comap g').F T) :
    F.point r (F.toBaseChange r g (F.toBaseChange (r.comap g) g' ξ).2.1).2.1 =
      ξ.1 ≫ g' ≫ g :=
  Category.assoc ξ.1 g' g

end GradedAlgebraPoints

end AlgebraicGeometry.Space

end
