module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Numerical invariants of coherent sheaves with proper support (Stacks 0DNC)

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces of finite presentation, as in the
introduction to the source's section on the stack of coherent sheaves.  Stacks 0DNC fixes, over
that morphism, a set `I`, a perfect object `E i` of `D(𝒪_X)` for each `i ∈ I`, and a map
`P : I → ℤ` of prescribed numerical invariants.  Those data are what every statement about the
numerical substack `Coh^P_{X/Y} ⊆ Coh_{X/Y}` is relative to.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation`: **Stacks 0DNC**, the standing data over a
  `AlgebraicGeometry.Space.CoherentSituation` — separatedness of the structure morphism, the
  index set, the family of perfect objects of `D(𝒪_X)`, and the prescribed invariants.
* `AlgebraicGeometry.Space.NumericalSituation.restrict`: the same data with the index set cut
  down to a subset of it, which is the passage from `P` to `P|_{I'}` that the source's
  reduction of an infinite `I` to its finite subsets uses.

## Implementation notes

**What is here, and what the source's remaining assertions need.**  The source goes on to form,
for an object `(T, g, 𝓕)` of `Coh_{X/Y}`, the derived pullback `E_{i,T}` of `E i` to `X_T`, the
object `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕)` of `D(𝒪_T)`, the Euler-characteristic function
`χ_i : |T| → ℤ`, and the substack cut out by `χ_i = P i`.  None of the four is constructed here,
and each is blocked on a different absent input:

* the derived pullback along `X_T ⟶ X` exists for a morphism of algebraic spaces only relative to
  a resolving datum for degreewise pullback — the K-flat resolutions of Stacks 06YS, which are
  available in this tree only over a site that is `CategoryTheory.SmallCategory`, whereas the
  small étale site of an algebraic space is only essentially small;
* the derived tensor product of Stacks 06YU is constructed on a ringed site whose underlying
  category is small, and the small étale ringed site of an algebraic space is
  `AlgebraicGeometry.RingedSite.{u + 1, u, u}`;
* the Euler characteristic of a perfect object on an algebraic space cannot be constructed for
  the same reason its Betti numbers cannot, namely clause (2) of Stacks 03OJ; on an algebraic
  space those Betti numbers are therefore taken as data characterised étale locally, by
  `AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`.

The derived direct image itself is not an obstruction:
`AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward` gives `Rf_*` on the whole of
`D(𝒪_{X_T})` for every morphism of algebraic spaces.

**The sheafification hypotheses.**  Perfectness is `AlgebraicGeometry.RingedSite.IsPerfect` of
Stacks 08G5 on the small étale ringed site of `X`, and that predicate is stated over a ringed
site admitting sheafification of presheaves of abelian groups on the site and on each of its
slices.  Those four instances and the sheaf-composition instance are carried here in the binder
shape `AlgebraicGeometry.Space.ApproximationHolds` carries them: instance search does not unfold
the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`, so they do not follow from the
instances of the small étale site itself.

**Separatedness is a field and not part of `CoherentSituation`.**  Stacks 08KB forms `Coh_{X/Y}`
for a morphism of finite presentation, which is what
`AlgebraicGeometry.Space.CoherentSituation` records; separatedness enters only with the section
introduction that Stacks 0DNC refers to, so it is added here rather than imposed there.

## References

* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public section

open CategoryTheory

universe u v m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : CoherentSituation B S hS)
    [HasSheafify (smallEtaleRingedSite B S hS D.X.1 D.X.2).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS D.X.1 D.X.2).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [∀ U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C,
      HasSheafify ((smallEtaleRingedSite B S hS D.X.1 D.X.2).J.over U) AddCommGrpCat.{m}]
    [∀ U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C,
      ((smallEtaleRingedSite B S hS D.X.1 D.X.2).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{m}]
    [hSheafCompose : ∀ U : (smallEtaleRingedSite B S hS D.X.1 D.X.2).C,
      ((smallEtaleRingedSite B S hS D.X.1 D.X.2).J.over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- **Stacks 0DNC, the standing data.**  Over a morphism `f : X ⟶ Y` of algebraic spaces of
finite presentation: separatedness of `f`, a set `I`, a perfect object of `D(𝒪_X)` for each
`i ∈ I`, and the prescribed numerical invariants `P : I → ℤ`. -/
@[stacks 0DNC "the standing data: separatedness of the relative space, the index set, the family
of perfect objects of `D(𝒪_X)`, and the prescribed numerical invariants"]
structure NumericalSituation where
  /-- The morphism of the coherent situation is separated (Stacks 03HL), which is the hypothesis
  of the section introduction that the source refers to. -/
  separated : IsSeparated B S hS D.f.hom
  /-- The index set of the numerical invariants. -/
  I : Type v
  /-- The object `E i` of `D(𝒪_X)` whose Euler characteristics the invariant `i` records. -/
  E : I → DerivedCategory (Modules.{u, m} B S hS D.X.1 D.X.2)
  /-- Each `E i` is perfect (Stacks 08G5). -/
  perfect : ∀ i : I, (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect (E i)
  /-- The prescribed numerical invariants. -/
  P : I → ℤ

namespace NumericalSituation

variable {B S hS D}

/-- The standing data of Stacks 0DNC re-indexed by a subset of its index set: the same perfect
objects and the same prescribed invariants, taken only at the indices in `J`.

This is the passage from `P` to `P|_{I'}` by which the source reduces an infinite index set to
its finite subsets. -/
def restrict (N : NumericalSituation.{u, v, m} B S hS D) (J : Set N.I) :
    NumericalSituation.{u, v, m} B S hS D where
  separated := N.separated
  I := J
  E i := N.E i.1
  perfect i := N.perfect i.1
  P i := N.P i.1

omit hSheafCompose in
/-- The perfect object of `N.restrict J` at `i ∈ J` is the object `N.E i` of `N`. -/
@[simp]
theorem restrict_E (N : NumericalSituation.{u, v, m} B S hS D) (J : Set N.I) (i : J) :
    (N.restrict J).E i = N.E i.1 :=
  rfl

omit hSheafCompose in
/-- The prescribed invariant of `N.restrict J` at `i ∈ J` is the invariant `N.P i` of `N`. -/
@[simp]
theorem restrict_P (N : NumericalSituation.{u, v, m} B S hS D) (J : Set N.I) (i : J) :
    (N.restrict J).P i = N.P i.1 :=
  rfl

end NumericalSituation

end AlgebraicGeometry.Space

end
