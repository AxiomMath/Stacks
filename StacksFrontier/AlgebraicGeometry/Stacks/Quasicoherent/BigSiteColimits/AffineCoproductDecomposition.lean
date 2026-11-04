module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.BaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.StructureSections

/-!
# The sections of a coproduct of structure sheaves over an affine object of a slice site

Over an object all of whose coverings admit a finite subcovering, the sections of a coproduct of
copies of the structure sheaf of a ringed site are the direct sum of the sections of the
structure sheaf; this is `SheafOfModules.sectionsEquivFinsupp`, and it is stated for an abstract
topology with the finite subcovering property as a hypothesis.  This file discharges that
hypothesis on the sites where the statement is used: the slices of the fppf site associated with
a category fibred in groupoids over a big fppf category of schemes, at their affine objects.

The discharge is not quite
`AlgebraicGeometry.BigFppfOver.hasFiniteSubcovering_over_associatedTopology`, which produces the
property at an object of the shape `Over.mk f`.  What quantifies over the objects of a slice is
phrased for an arbitrary `W : Over x` carrying the hypothesis that the scheme underlying
`p W.left` is affine, and the terminal object of the slice at `x` is `Over.mk (𝟙 x)`; so the
property is established here for an arbitrary object of a slice, from affineness of its own
underlying scheme alone, and the two shapes that occur — an arbitrary affine object and the
terminal object of the slice at an affine object — are both instances of that.

Only the objects of the slice are involved, not the morphism `x` sits over: an object of
`Over x` is affine or not according to its own left component, so affineness of `x` itself is
needed for the terminal object and for nothing else.

## Main definitions

* `AlgebraicGeometry.FibredSite.sectionsEquivFinsuppOfIsAffineOver`: **the sections of a
  coproduct of copies of the structure sheaf over an affine object of a slice of the associated
  fppf site are the finitely supported families of sections of the structure sheaf.**
* `AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOver`: the same read as a basis, the
  tautological generators of the coproduct being the basis vectors.
* `AlgebraicGeometry.FibredSite.sectionRingEquivGamma`: the ring of sections of the coefficient
  sheaf of rings of a slice, identified with the commutative ring of global functions on the
  underlying scheme.
* `AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs`: **the tautological generators as a
  basis over a commutative ring identified with the ring of sections**, which is the form in which
  a comparison of the sections of a presented module with a base change consumes the
  decomposition.

## Main results

* `AlgebraicGeometry.FibredSite.hasFiniteSubcovering_over_of_isAffineOver`: **an object of a
  slice of the associated fppf site whose underlying scheme is affine has the finite subcovering
  property.**
* `AlgebraicGeometry.FibredSite.hasFiniteSubcovering_mkId_of_isAffineOver`: the terminal object
  of the slice at an affine object has it.
* `AlgebraicGeometry.FibredSite.ringStructureSheafCore_over_obj_obj`: the sections of the
  coefficient sheaf of rings of a slice at an object are the global functions on the underlying
  scheme.
* `AlgebraicGeometry.FibredSite.sectionsEquivFinsuppOfIsAffineOver_apply`,
  `AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOver_apply` and
  `AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs_apply`: all three identifications
  are the linear combination of the tautological generators, transporting the coefficients not
  moving the basis vectors.

## Implementation notes

The universes of the objects and of the morphisms of the fibred category, the universe of the
schemes, the universe of the sections of the structure sheaf, the amount by which the structure
sheaf is lifted and the universe of the index type of the coproduct are six independent
universes here, and none of the statements below relates them.  In particular the index type of
the coproduct is free of the universe of the site, which is what a consumer presenting a module
over a coproduct indexed by its own sections needs.  The coefficient ring of
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs` lives at a seventh, equally free
universe.

The two statements naming the global functions on the underlying scheme are the exception: there
the universe of the ring of sections is the universe of the schemes, since the coefficient sheaf
of rings of an associated site takes its values in `RingCat` at that universe.

The module structure over the commutative ring is a hypothesis of
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs` rather than being built from the
definitional identification of the two rings, so that it is the consumer's own: a consumer holds
it together with a scalar tower over the ring of sections at a terminal object, and a second
structure obtained here would not be the one that tower is stated for.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0D05](https://stacks.math.columbia.edu/tag/0D05)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe z v w u r t

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **An object of a slice of the associated fppf site whose underlying scheme is affine has the
finite subcovering property.**  Affineness of the scheme underlying `p W.left` gives the property
at `W.left` in the associated topology
(`AlgebraicGeometry.BigFppfOver.hasFiniteSubcovering_associatedTopology`), and the property
passes from an object to the objects of the slice lying over it
(`CategoryTheory.GrothendieckTopology.hasFiniteSubcovering_over`).

The morphism `W.hom` plays no part: an object of a slice has the property as soon as its own left
component does. -/
theorem hasFiniteSubcovering_over_of_isAffineOver (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    (W : Over x) (hW : IsAffineOver B S hS (p.obj W.left)) :
    ((BigFppfOver.associatedTopology B S hS p .fppf).over x).HasFiniteSubcovering W :=
  (BigFppfOver.associatedTopology B S hS p .fppf).hasFiniteSubcovering_over W
    (BigFppfOver.hasFiniteSubcovering_associatedTopology B S hS p hp W.left hW)

/-- **The terminal object of the slice at an affine object has the finite subcovering property.**
The terminal object of `Over x` is `Over.mk (𝟙 x)`, whose left component is `x` itself, so this is
`AlgebraicGeometry.FibredSite.hasFiniteSubcovering_over_of_isAffineOver` there. -/
theorem hasFiniteSubcovering_mkId_of_isAffineOver (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    (hx : IsAffineOver B S hS (p.obj x)) :
    ((BigFppfOver.associatedTopology B S hS p .fppf).over x).HasFiniteSubcovering
      (Over.mk (𝟙 x)) :=
  hasFiniteSubcovering_over_of_isAffineOver B S hS p hp (Over.mk (𝟙 x)) hx

section Decomposition

variable (hp : p.IsFiberedInGroupoids) {x : 𝒳}
  {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
  {I : Type z} {N : SheafOfModules.{max t r} R}
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{max v w, w, r, r, t}
    (SheafOfModules.unit R) ⟶ N)
  (hN : IsColimit (Cofan.mk N ι)) (W : Over x)
  (hW : IsAffineOver B S hS (p.obj W.left))

/-- **The sections of a coproduct of copies of the universe lift of the structure sheaf over an
affine object of a slice of the associated fppf site are the finitely supported families of
sections of the structure sheaf.**  This is `SheafOfModules.sectionsEquivFinsupp` with its finite
subcovering hypothesis discharged by
`AlgebraicGeometry.FibredSite.hasFiniteSubcovering_over_of_isAffineOver`.

Nothing is assumed of the sheaf of rings on the slice beyond its being one: the identification is
the statement that the coproduct is computed section by section at an affine object, and the
finiteness which makes that true comes from quasi-compactness of the affine scheme alone. -/
noncomputable def sectionsEquivFinsuppOfIsAffineOver :
    (I →₀ R.obj.obj (op W)) ≃ₗ[R.obj.obj (op W)] N.val.obj (op W) :=
  SheafOfModules.sectionsEquivFinsupp ι hN
    (hasFiniteSubcovering_over_of_isAffineOver B S hS p hp W hW)

/-- `AlgebraicGeometry.FibredSite.sectionsEquivFinsuppOfIsAffineOver` is the linear combination of
the tautological generators. -/
lemma sectionsEquivFinsuppOfIsAffineOver_apply (c : I →₀ R.obj.obj (op W)) :
    sectionsEquivFinsuppOfIsAffineOver B S hS p hp ι hN W hW c =
      Finsupp.linearCombination (R.obj.obj (op W))
        (fun i ↦ SheafOfModules.tautGen ι i (op W)) c :=
  SheafOfModules.sectionsEquivFinsupp_apply ι hN _ c

/-- **The tautological generators of a coproduct of copies of the universe lift of the structure
sheaf form a basis of its sections over an affine object of a slice of the associated fppf
site.**  This is `SheafOfModules.tautBasis` with its finite subcovering hypothesis discharged by
`AlgebraicGeometry.FibredSite.hasFiniteSubcovering_over_of_isAffineOver`; it is the shape in
which the comparison of the sections of a presented module with a base change consumes the
decomposition. -/
noncomputable def tautBasisOfIsAffineOver :
    Module.Basis I (R.obj.obj (op W)) (N.val.obj (op W)) :=
  SheafOfModules.tautBasis ι hN (hasFiniteSubcovering_over_of_isAffineOver B S hS p hp W hW)

/-- `AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOver` is the family of tautological
generators. -/
@[simp]
lemma tautBasisOfIsAffineOver_apply (i : I) :
    tautBasisOfIsAffineOver B S hS p hp ι hN W hW i = SheafOfModules.tautGen ι i (op W) :=
  SheafOfModules.tautBasis_apply ι hN _ i

end Decomposition

section Coefficients

/-- **The sections of the coefficient sheaf of rings of a slice of an associated site at an object
are the global functions on the underlying scheme.**  The restriction of a sheaf to a slice is its
composite with the forgetful functor of the slice, so this is
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_obj_obj` at the left component.

Like that lemma this is a definitional equation between objects of `RingCat` rather than a `simp`
lemma: it is named so that a statement about the sections of a sheaf of modules on a slice can be
matched with a statement about modules over a commutative ring, which is what
`AlgebraicGeometry.FibredSite.sectionRingEquivGamma` then does. -/
theorem ringStructureSheafCore_over_obj_obj (hp : p.IsFiberedInGroupoids) (τ : SiteKind) {x : 𝒳}
    (W : Over x) :
    ((ringStructureSheafCore B S hS p hp τ).over x).obj.obj (op W) =
      RingCat.of Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) := rfl

/-- **The ring of sections of the coefficient sheaf of rings of a slice at an object, identified
with a commutative ring.**  By
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_over_obj_obj` the two are the same ring, so
the identification is the identity; its point is that the right-hand side is the carrier of a
`CommRingCat` and therefore carries a `CommRing` instance, which the ring of sections of a sheaf of
`RingCat` does not.

This is what a consumer asking for a basis over a commutative ring supplies to
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs`. -/
noncomputable def sectionRingEquivGamma (hp : p.IsFiberedInGroupoids) (τ : SiteKind) {x : 𝒳}
    (W : Over x) :
    (((ringStructureSheafCore B S hS p hp τ).over x).obj.obj (op W) : Type u) ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤) :=
  RingEquiv.refl _

variable (hp : p.IsFiberedInGroupoids) {x : 𝒳}
  {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
  {I : Type z} {N : SheafOfModules.{max t r} R}
  (ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{max v w, w, r, r, t}
    (SheafOfModules.unit R) ⟶ N)
  (hN : IsColimit (Cofan.mk N ι)) (W : Over x)
  (hW : IsAffineOver B S hS (p.obj W.left))
  {A : Type*} [Semiring A] [Module A (N.val.obj (op W))]
  (f : (R.obj.obj (op W) : Type r) ≃+* A)
  (hf : ∀ (c : R.obj.obj (op W)) (n : N.val.obj (op W)), f c • n = c • n)

/-- **The tautological generators as a basis over a ring identified with the ring of sections.**
`AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOver` is a basis over the ring of sections of the
structure sheaf, which is an object of `RingCat` and so carries no commutativity; a consumer
comparing the sections of a presented module with a base change needs a basis over a genuine
commutative ring.  Transporting along a ring equivalence acting in the same way supplies it.

The equivalence and the agreement of the two actions are hypotheses rather than being produced
here, because the module structure over `A` is the consumer's: it arrives together with the
scalar tower over the ring of sections at a terminal object which the base change is taken along.
For the coefficient sheaf of rings of a slice of an associated site the equivalence is
`AlgebraicGeometry.FibredSite.sectionRingEquivGamma`. -/
noncomputable def tautBasisOfIsAffineOverCoeffs : Module.Basis I A (N.val.obj (op W)) :=
  (tautBasisOfIsAffineOver B S hS p hp ι hN W hW).mapCoeffs f hf

/-- `AlgebraicGeometry.FibredSite.tautBasisOfIsAffineOverCoeffs` is still the family of
tautological generators: transporting the coefficients does not move the basis vectors.  This is
the identification of the basis vectors which the base-change comparison asks for alongside the
basis itself. -/
@[simp]
lemma tautBasisOfIsAffineOverCoeffs_apply (i : I) :
    tautBasisOfIsAffineOverCoeffs B S hS p hp ι hN W hW f hf i =
      SheafOfModules.tautGen ι i (op W) :=
  (Module.Basis.mapCoeffs_apply _ f hf i).trans
    (tautBasisOfIsAffineOver_apply B S hS p hp ι hN W hW i)

end Coefficients

end AlgebraicGeometry.FibredSite

end
