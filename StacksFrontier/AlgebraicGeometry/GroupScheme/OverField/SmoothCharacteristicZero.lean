module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Differentials
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.LocallyFreeDifferentials
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Smoothness and reducedness of a group scheme over a field of characteristic zero

Let `k` be a field of characteristic `0` and let `G` be a locally algebraic group scheme over
`k`, that is, a scheme whose structure morphism `f : G ⟶ Spec k` is locally of finite type and
which carries a group object structure in the category of schemes over `Spec k`.  Then `f` is
smooth: `G` is a smooth group scheme.  This is Cartier's theorem in the form the chapter on
groupoid schemes uses.  In particular `G` is reduced, the spectrum of a field being reduced and
a scheme smooth over a reduced affine scheme being reduced.

The proof is the one the source gives, and it is exactly two steps.  The sheaf of relative
differentials `Ω_{G/k}` is free, because translation invariance identifies it with the inverse
image along `f` of its restriction along the identity section, and that restriction is a vector
space over `k`; and a scheme locally of finite type over a field of characteristic `0` whose
sheaf of relative differentials is locally free is smooth.

## Main results

* `AlgebraicGeometry.smooth_of_groupScheme_of_charZero`: **[Stacks, Tag 047N]** the structure
  morphism of a locally algebraic group scheme over a field of characteristic `0` is smooth.
* `AlgebraicGeometry.isReduced_of_groupScheme_of_charZero`: **[Stacks, Tag 047O]**, for a group
  scheme locally of finite type, the case of that remark the source proves: a locally algebraic
  group scheme over a field of characteristic `0` is reduced.

## Implementation notes

A locally algebraic group scheme over `k` is recorded, as elsewhere in this tree, by its
structure morphism `f : G ⟶ Spec (CommRingCat.of k)` carrying `GrpObj (Over.mk f)` — the group
object structure in the category of schemes over `Spec k` — together with
`LocallyOfFiniteType f`, which is what "locally algebraic" means.  Smoothness of the structure
morphism is `AlgebraicGeometry.Smooth f`, the predicate on the morphism itself, so the
conclusion is literally the assertion of the source.

Characteristic `0` is used in exactly one place, and that place is not in this file: it is a
hypothesis of `AlgebraicGeometry.smooth_of_isLocallyFree_relativeDifferentials_of_charZero`,
the formalization of [Stacks, Tag 04QN], where it feeds the commutative-algebra input [Stacks,
Tag 00TX] turning freeness of the Kähler differentials of a local ring of a finite type algebra
over the field into smoothness at the corresponding prime.  The freeness of `Ω_{G/k}` used here
holds over an arbitrary field.

The two halves do not quite meet on the nose.  [Stacks, Tag 047I] is available as
`AlgebraicGeometry.GroupSchemeDifferentials.exists_free_iso_relativeDifferentials_of_field`,
which produces an index type and an isomorphism of `Ω_{G/k}` with the free sheaf of modules on
it, whereas [Stacks, Tag 04QN] asks for `SheafOfModules.IsLocallyFree`.  The private lemma
`isLocallyFree_of_iso_free` bridges them, transporting the canonical locally free data of a free
sheaf — its global basis — along the inverse of that isomorphism with
`Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso`.  It is stated over an arbitrary site, as
the declarations it is assembled from are: the universes of a module on a scheme are then fixed
by unification at the point of use rather than written down, which is what lets the conclusion
match the explicitly universe-annotated hypothesis of Tag 04QN.

[Stacks, Tag 047O] asserts reducedness of an *arbitrary* group scheme over a field of
characteristic `0`, with no finiteness hypothesis, and for that generality the source defers to
Perrin; what it proves is the locally finite type case, as a consequence of [Stacks, Tag 047N].
That consequence is `AlgebraicGeometry.isReduced_of_groupScheme_of_charZero`, and the attribute
carries the restriction as its description.  The affine case, with no finiteness hypothesis, is
`AlgebraicGeometry.isReduced_of_groupScheme_of_charZero_of_isAffine` in
`StacksFrontier.RingTheory.HopfAlgebra.ReducedCharacteristicZero` (Cartier's theorem for Hopf
algebras: a commutative Hopf algebra is the directed union of its finitely generated Hopf
subalgebras, each reduced by the present file).  Perrin obtains the general case
([Perrin, Corollaire 4.2.8], Bull. SMF 104 (1976)) from his theorem that every quasi-compact
group scheme over a field is a filtered limit of algebraic groups which are fpqc quotients of it,
whose proof rests on Weil's theorem on birational group laws; that is not formalized here.

## References

* [Stacks Project, Tag 047N](https://stacks.math.columbia.edu/tag/047N)
* [Stacks Project, Tag 047O](https://stacks.math.columbia.edu/tag/047O)
* [Stacks Project, Tag 047I](https://stacks.math.columbia.edu/tag/047I)
* [Stacks Project, Tag 04QN](https://stacks.math.columbia.edu/tag/04QN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace AlgebraicGeometry

/-- A sheaf of modules isomorphic to a free sheaf of modules is locally free: the global basis
of the free sheaf is locally free data for it, and local generators data transports along an
isomorphism. -/
theorem isLocallyFree_of_iso_free {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} {I : Type u} (e : M ≅ SheafOfModules.free (R := R) I) :
    M.IsLocallyFree :=
  (Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso e.inv
    (SheafOfModules.free.generatingSections (R := R) I).localGeneratorsData).isLocallyFree

/-- **Stacks Project, Tag 047N.**  Let `k` be a field of characteristic `0` and let `G` be a
locally algebraic group scheme over `k`, i.e. a scheme whose structure morphism
`f : G ⟶ Spec k` is locally of finite type and which is a group object over `Spec k`.  Then `f`
is smooth, i.e. `G` is a smooth group scheme.

By [Stacks, Tag 047I] the sheaf of relative differentials of `f` is free, hence locally free,
and [Stacks, Tag 04QN] turns that into smoothness over a field of characteristic `0`. -/
@[stacks 047N,
  sga "3 VIA 1.1",
  sga "3 VIA 6.9" "special case",
  sga "3 VIB 1.6" "Case S = Spec k",
  sga "3 VIB 1.6.1",
  sga "3 VIIA 8.4" "more general",
  sga "3 VIIA 8.5.1" "more general",
  sga "3 XV 6.5" "partial",
  sga "3 XVII 5.5" "partial"]
theorem smooth_of_groupScheme_of_charZero (k : Type u) [Field k] [CharZero k] (G : Scheme.{u})
    (f : G ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk f)] [LocallyOfFiniteType f] :
    Smooth f := by
  obtain ⟨I, ⟨e⟩⟩ :=
    GroupSchemeDifferentials.exists_free_iso_relativeDifferentials_of_field k G f
  refine smooth_of_isLocallyFree_relativeDifferentials_of_charZero f ?_
  exact isLocallyFree_of_iso_free.{u, u, u} e

/-- **Stacks Project, Tag 047O**, the case the source proves.  A locally algebraic group scheme
over a field `k` of characteristic `0` is reduced: it is smooth over `k` by [Stacks, Tag 047N],
`Spec k` is a reduced affine scheme, and a scheme smooth over a reduced affine scheme is
reduced.

The source states reducedness for an arbitrary group scheme over a field of characteristic `0`,
citing Perrin for that generality, and records that the locally finite type case is the
consequence of [Stacks, Tag 047N] proved here. -/
@[stacks 047O "locally of finite type case; the general case is cited to Perrin",
  sga "3 VIA 6.9" "partial",
  sga "3 VIIA 8.5.1" "more general",
  sga "3 VIII 7.1" "more general"]
theorem isReduced_of_groupScheme_of_charZero (k : Type u) [Field k] [CharZero k] (G : Scheme.{u})
    (f : G ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk f)] [LocallyOfFiniteType f] :
    IsReduced G :=
  have := smooth_of_groupScheme_of_charZero k G f
  isReduced_of_smooth_of_isAffine f

end AlgebraicGeometry

end
