module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal

/-!
# The diagonal of the stack of coherent sheaves (Stacks 08W6)

In the standing data of Stacks 08KB — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` of a big fppf site, of finite presentation — write `𝒳 = Coh_{X/Y}` for the category of
coherent sheaves with proper support of that tag.  Stacks 08W6 asserts that the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces.

The proof of the source is in two steps.  First, by Algebraic Stacks, Lemma 045G it suffices to
show that for every test scheme `T` and every pair of objects `x = (T, g, ℱ)`, `y = (T, h, 𝒢)` of
the fibre over `T` the isomorphism sheaf `Isom_𝒳(x, y)` is an algebraic space over `T`.  Second,
that isomorphism sheaf maps to the equalizer of `g` and `h`, which is a scheme because the
diagonal of `Y` is representable; over that equalizer the two base maps agree and the isomorphism
sheaf becomes the relative isomorphism sheaf `Isom(ℱ, 𝒢)` of two modules, which is an algebraic
space by Proposition 08K9.

## Main definitions

* `AlgebraicGeometry.Space.coherentCatFiberedInGroupoids`: `Coh_{X/Y}` as a category fibred in
  groupoids over the big fppf site of `S`, that is, the category of Stacks 08KB together with the
  fibred-in-groupoids structure of Stacks 08W5.

## Main results

* `AlgebraicGeometry.Space.coherentDiagonal_isRepresentableByAlgebraicSpaces` and
  `AlgebraicGeometry.Space.coherentHasRepresentableDiagonal`: the conclusion of Stacks 08W6 for
  `Coh_{X/Y}`, in the two equivalent forms of condition (1) of Stacks 045G, granted condition (2)
  of that tag for `Coh_{X/Y}`.  **Neither carries a tag**; see the implementation notes.

## Implementation notes

**Stacks 08W6 is not carried here, and no declaration in this file claims it.**  It is carried,
unconditionally and for the canonical `AlgebraicGeometry.Space.CoherentSituation.coherentCFG`, by
`AlgebraicGeometry.Space.CoherentSituation.coherentCFG_diagonal_isRepresentableByAlgebraicSpaces`
in `StacksFrontier/AlgebraicGeometry/Stacks/CoherentStackDiagonalRepresentable.lean`; the rest of this
note describes the state of the development when this file was written.  The second step
of the proof is Proposition 08K9, that the relative isomorphism sheaf of two quasi-coherent
modules of finite presentation, flat with proper support, is an algebraic space affine and of
finite presentation over the base, applied after the reduction to a common base map over the
equalizer of the two base maps.  Neither is carried anywhere in this development: the relative
isomorphism *functor* of Stacks 08K7 and its fpqc sheaf property of Stacks 08K8 are available
(`AlgebraicGeometry.Space.HomSituation.isomFunctor` and
`AlgebraicGeometry.Space.HomSituation.isSheafFor_isomFunctor` in
`StacksFrontier/AlgebraicGeometry/Quot/RelativeIsom.lean`), but nothing identifies that functor with
an algebraic space, and the equalizer reduction is absent.

What the two theorems below do is transport condition (2) of Stacks 045G for `Coh_{X/Y}` to
condition (1) across `AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff` and
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`.  Both of
those equivalences hold for an *arbitrary* category fibred in groupoids over the big fppf site,
so deleting the hypothesis leaves no statement about coherent sheaves at all; that is why they
are convenience bridges rather than carriers.  They become a proof of Stacks 08W6 exactly when
their hypothesis is discharged, which is the equalizer reduction together with Proposition 08K9.

The fibred-in-groupoids structure comes from
`AlgebraicGeometry.Space.coherentProjection_isFiberedInGroupoids`, Stacks 08W5, which is itself
conditional on the three base-change stability results of its own file; those hypotheses
(`hc`, `hst`, `cd`) are carried unchanged.

The hom-sets of `Coh_{X/Y}` live one universe above those of the site, so the object constructed
here is a `CategoryTheory.CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}`; the equivalence of
Stacks 045G is stated at independent universes and applies.

## References

* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {hc : ModulePushforwardCoherence B S hS} {D : CoherentSituation B S hS}

/-- `Coh_{X/Y}` as a category fibred in groupoids over the big fppf site of `S`: the category of
Stacks 08KB, projecting an object `(T, g, ℱ)` to the scheme `T`, together with the
fibred-in-groupoids structure of Stacks 08W5. -/
def coherentCatFiberedInGroupoids (hst : ModulePullbackStability B S hS)
    (cd : CoherentCategoryData hc D) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (coherentBasedCategory cd) (by
    have h := coherentProjection_isFiberedInGroupoids hc hst cd
    rw [coherentSiteProjection_eq cd] at h
    exact h)

/-- The underlying category over the site of `AlgebraicGeometry.Space`'s category fibred in
groupoids is `Coh_{X/Y}` as a category over the site. -/
theorem coherentCatFiberedInGroupoids_val (hst : ModulePullbackStability B S hS)
    (cd : CoherentCategoryData hc D) :
    (coherentCatFiberedInGroupoids hst cd).val = coherentBasedCategory cd :=
  rfl

/-- The conclusion of Stacks 08W6 for `Coh_{X/Y}`, granted condition (2) of Stacks 045G for it:
the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` of `𝒳 = Coh_{X/Y}` is representable by algebraic spaces.

**This is a convenience bridge and carries no tag.**  Its hypothesis `h045G2` is condition (2)
of Stacks 045G for `Coh_{X/Y}` — that each isomorphism sheaf `Isom_𝒳(x, y)` of two objects of a
fibre is an algebraic space over the scheme the fibre sits over — and the proof is the two
pre-existing equivalences `AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff` and
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`, both of
which hold for an arbitrary category fibred in groupoids.  Deleting `h045G2` leaves nothing
about coherent sheaves, so this is not a carrier for Stacks 08W6; the step of the source that
would make it one — the reduction to a common base map over the equalizer of the two base maps,
followed by Proposition 08K9 — is not carried in this development.  See the implementation notes
of the file. -/
theorem coherentDiagonal_isRepresentableByAlgebraicSpaces
    (hst : ModulePullbackStability B S hS) (cd : CoherentCategoryData hc D)
    (h045G2 : Stack.IsAlgebraicSpaceIsomPresheaf B S hS
      (coherentCatFiberedInGroupoids hst cd)) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.diagonalBasedFunctor B S hS (coherentCatFiberedInGroupoids hst cd)) :=
  (Stack.hasRepresentableDiagonal_iff B S hS (coherentCatFiberedInGroupoids hst cd)).mp
    ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
      (coherentCatFiberedInGroupoids hst cd)).mpr h045G2)

/-- The statement of Stacks 08W6 in the form `AlgebraicGeometry.Stack.HasRepresentableDiagonal`,
which is condition (1) of Stacks 045G.  Granted the same hypothesis as
`AlgebraicGeometry.Space.coherentDiagonal_isRepresentableByAlgebraicSpaces`. -/
theorem coherentHasRepresentableDiagonal (hst : ModulePullbackStability B S hS)
    (cd : CoherentCategoryData hc D)
    (h045G2 : Stack.IsAlgebraicSpaceIsomPresheaf B S hS
      (coherentCatFiberedInGroupoids hst cd)) :
    Stack.HasRepresentableDiagonal B S hS (coherentCatFiberedInGroupoids hst cd) :=
  (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
    (coherentCatFiberedInGroupoids hst cd)).mpr h045G2

end AlgebraicGeometry.Space

end
