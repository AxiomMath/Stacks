module

public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree

/-!
# Invertible sheaves of modules and local freeness of rank one

Let `O` be a sheaf of commutative rings on a site `(C, J)`. Stacks Tag 0B8M has three clauses:
a sheaf of `O`-modules that is locally free of rank one is invertible; the converse holds when
every stalk of `O` is a local ring; and the converse fails in general, as a one-point space with
a ring of nontrivial Picard group shows.

This file does the whole of clause 1 except its final descent step, and isolates that step as a
single named hypothesis. Concretely: a sheaf of modules that is finite locally free of rank one
is shown to be *locally* invertible, on a covering of the terminal object, with invertibility
read on the restricted site in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible`. Going from there to invertibility on `(C, J)`
is the descent step, and it is supplied here as the hypothesis
`Stacks.InvertibleLocallyFree.InvertibleIsLocal`; see the implementation notes for why the route
sketched in this file cannot discharge it.

**That hypothesis is now proved, elsewhere.** `Stacks.SheafOfModules.invertibleIsLocal`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalDual.lean`) proves
`InvertibleIsLocal` on an arbitrary site at the module universe `max u v`, and
`Stacks.SheafOfModules.invertibleIsLocal_opens`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalSpace.lean`) specializes it to the
site of opens of a topological space, where its sheafification hypotheses are automatic. Neither
of those files can be imported here — they depend on the dual sheaf, which depends on this file
— so the hypothesis stays in the statements below, but it is no longer open: pass
`Stacks.SheafOfModules.invertibleIsLocal` for it.

Along the way the trivial case is settled unconditionally and over the library class: the
structure sheaf, viewed as a module over itself, is invertible, and so is anything isomorphic to
it. These statements are stated against `AlgebraicGeometry.SheafOfModules.IsInvertible`.

## Main definitions

* `Stacks.InvertibleLocallyFree.overPresheaf`: the presheaf of commutative rings `O` restricted
  along `Over.forget X`, so that the structure data of the site is available on `Over X`.
* `Stacks.InvertibleLocallyFree.InvertibleIsLocal`: the descent step of Tag 0B8M, stated as a
  hypothesis — a sheaf of modules invertible on every member of a covering of the terminal
  object is invertible.

## Main results

* `Stacks.InvertibleLocallyFree.structureSheaf_over`: restricting the structure sheaf of rings to
  `Over X` gives the structure sheaf of the restricted presheaf of commutative rings. This holds
  by `rfl` and is what makes invertibility on the restricted site expressible at all.
* `Stacks.InvertibleLocallyFree.isInvertible_of_iso_unit` and
  `Stacks.InvertibleLocallyFree.isInvertible_of_isTrivial`: a trivial sheaf of modules is
  invertible. This is a statement about Tag 01CS, not about Tag 0B8M. That the structure sheaf
  itself is invertible is `Stacks.SheafOfModules.isInvertible_unit` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne.lean`, imported here.
* `exists_coversTop_isInvertible_over_of_isFiniteLocallyFreeOfRank_one`, in this namespace:
  a sheaf of modules that is finite locally free of rank one is invertible on each member of a
  covering of the terminal object. This is clause 1 of Tag 0B8M with the descent step removed,
  and it is unconditional.
* `InvertibleLocallyFree.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_invertibleIsLocal`:
  clause 1 of Tag 0B8M, **under the extra hypothesis** `InvertibleIsLocal`. The hypothesis is
  named in the declaration name because it is not discharged here.
* `InvertibleLocallyFree.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank` and
  `InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank`:
  bridges from fixed rank to the two copies of finite local freeness that the repository carries,
  so that the Tag 05P2 consequences hanging off
  `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` apply to a rank-one sheaf.
* `InvertibleLocallyFree.isFiniteLocallyFreeOfRank_iff_invertible_isFiniteLocallyFreeOfRank`:
  the two copies of fixed-rank finite local freeness in the repository agree.

## Implementation notes

**Which `IsFiniteLocallyFree` is used.** All results are stated over the library class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`
(`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean`). It is the only rank-indexed one in a
library namespace, it carries the Stacks attribute for Tag 01C6 (3), and it is the one
`curveDegree` consumes. The repository has two further copies with the same body —
`Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank` in the draft tree and the
rank-unindexed `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, off which the Tag 05P2
consequences hang. Both are reached from the library class by the bridges listed above, whose
proofs are nothing but the anonymous constructor, so no content is lost by the choice.

**Why the route through effective descent fails, and why clause 1 does not need it.**
`InvertibleIsLocal` — local invertibility implies invertibility — cannot be proved the way this
file's constructions suggest, namely by descending the equivalence. Every
one of the three properties making a functor an equivalence descends only against effective
descent for sheaves of modules: faithfulness and fullness need gluing of morphisms, essential
surjectivity needs gluing of objects. Mathlib has the vocabulary for this,
`CategoryTheory.Pseudofunctor.IsPrestack` and `CategoryTheory.Pseudofunctor.IsStack`, and
instantiates it at no pseudofunctor at all; this repository instantiates it only over the
category of schemes, and only for the Zariski topology —
`Stacks.Descent.isPrestack_qcohPseudofunctor`
and `Stacks.Descent.isPrestack_modulePullbackPseudofunctor` in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/ZariskiGluing.lean`, and
`Stacks.Descent.isStack_qcohPseudofunctor` in `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/ZariskiStack.lean`. None of those transports
to a general site: there is no pseudofunctor `X ↦ SheafOfModules (𝒪.over X)` anywhere, and the
transport machinery of `StacksFrontier/CategoryTheory/Sites/Stack/` needs a comparison that does
not exist here. So that route is a dead end — which is why `InvertibleIsLocal` is proved by a
different one, the source's own, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalDual.lean`: the dual sheaf is a
global construction, so no object has to be glued, and all that descends is local bijectivity
of the evaluation pairing. Nothing is descended as an equivalence anywhere in that proof.

**Clause 1, however, does not go through it, and is proved unconditionally** in
`StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/DualBasis.lean`. The source's own route
produces an inverse outright rather than gluing one: the inverse of `L` is the dual sheaf
`L^∨ = SheafHom(L, 𝒪)`, which is a global construction, and the pairing `L^∨ ⊗ L ⟶ 𝒪` is
inverted by sheafification because it is bijective on a covering. The dual sheaf, the pairing
and the criterion `Stacks.SheafOfModules.isInvertible_of_dualBasisOne` are all in this
repository already, over an arbitrary site, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean`; so is a monoidal structure on
`SheafOfModules` over an arbitrary site, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean`. What was missing was only the
conversion of a rank-one trivialization into the dual-basis data, and that is what `DualBasis.lean`
supplies. The results in *this* file are therefore a second, independent partial route, kept
because they are what makes invertibility on the restricted site expressible, not because
clause 1 depends on them.

It remains true that Mathlib itself has no monoidal structure on `SheafOfModules` and no
comparison between the native left tensor actions on `(C, J)` and on `(Over X, J.over X)`; the
presheaf-level half of such a comparison does exist, since
`PresheafOfModules.pushforward₀OfCommRingCat` is monoidal, but the sheafification half is absent
from Mathlib. The dual-sheaf proof of `InvertibleIsLocal` does not need the sheafification half:
it compares the *presheaf*-level pairings and lets local bijectivity, not the tensor functor, do
the descending.

**Which clauses of Tag 0B8M are proved.** In *this file*, clause 1 only, and only modulo
`InvertibleIsLocal`; clause 1 is proved unconditionally, by the dual-sheaf route and at the
forced universe `w = max u v`, in
`StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/DualBasis.lean`, which is where the
Tag 0B8M attribute sits.
Clause 2, the converse under the hypothesis that the stalks of `O` are local rings, is untouched:
it needs the finite presentation of an invertible module, which the Stacks proof takes from Tag
0B8K. Clause 3 is a counterexample construction and is also untouched. No
Stacks attribute for Tag 0B8M is attached anywhere in this file, because nothing here asserts a
clause of it unconditionally.

**Transparency gotchas.** `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is a plain
  `def`, so
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj` is definitionally
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O`
only at default transparency. The monoidal structure on presheaves of modules over the structure
sheaf therefore has to be introduced by hand, with `change` followed by `infer_instance`, exactly
as the library file does; `infer_instance` alone fails. The same `def` is what makes
`structureSheaf_over` worth stating: the identification is a `rfl`, but it is not available to
instance search, and without it the restricted sheaf of modules `L.over X` cannot be fed to
`IsInvertible` on the restricted site. No transparency pragma is used; the `change` route
suffices throughout, and no banned `backward.isDefEq.respectTransparency` escape was needed.

**The `include` clauses.** `isSheaf_over` mentions the sheaf condition `hO` only in its proof, so
`hO` has to be pulled in explicitly; the statement itself is about the restricted presheaf alone.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

universe v u w

namespace Stacks.InvertibleLocallyFree

open AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

section OverSite

/-- The structure data of the site, restricted to the slice category over an object: the
presheaf of commutative rings `O` composed with the forgetful functor of `Over X`. -/
abbrev overPresheaf (X : C) : (Over X)ᵒᵖ ⥤ CommRingCat.{w} := (Over.forget X).op ⋙ O

include hO in
/-- The restricted presheaf of rings is a sheaf for the restricted topology: it is the underlying
presheaf of the restriction of the structure sheaf. -/
theorem isSheaf_over (X : C) :
    Presheaf.IsSheaf (J.over X) (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      (overPresheaf O X)) :=
  ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).over X).property

/-- Restricting the structure sheaf of rings to `Over X` gives the structure sheaf of the
restricted presheaf of commutative rings. This is an equality, not merely an isomorphism, because
composition of functors is associative definitionally and the sheaf condition is a proposition.
It is what lets a restricted sheaf of modules be fed to the invertibility predicate on the
restricted site. -/
theorem structureSheaf_over (X : C) :
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).over X =
      Stacks.SheafOfModules.TensorSheafification.structureSheaf (overPresheaf O X) (isSheaf_over O
        hO X) :=
  rfl

end OverSite

section Trivial

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafification is inverse to the inclusion of sheaves of modules into presheaves of modules:
the counit of the sheafification adjunction is an isomorphism, sheaves of modules forming a
reflective subcategory. -/
noncomputable def sheafifyForgetIso :
    (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        PresheafOfModules.restrictScalars (𝟙
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)) ⋙
      PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        O hO).obj) ≅ 𝟭 _ :=
  asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).counit

/-- Tensoring on the left by the structure sheaf is the identity functor: the underlying presheaf
of the structure sheaf is the monoidal unit, so the presheaf-level tensor functor is the left
unitor, and sheafification undoes the inclusion of sheaves into presheaves. Restriction of scalars
along the identity, which occurs in the right adjoint of the sheafification adjunction, is the
identity functor, so the two steps compose with no comparison map. -/
noncomputable def tensorLeftFunctorUnitIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
      (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅ 𝟭 _ := by
  refine Iso.trans ?_ (sheafifyForgetIso O hO)
  exact Functor.isoWhiskerLeft (SheafOfModules.forget
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (Functor.isoWhiskerRight
      (leftUnitorNatIso (PresheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj))
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO))

/-- A sheaf of modules isomorphic to the structure sheaf is invertible: its tensor functor is
isomorphic to that of the structure sheaf, hence to the identity functor. -/
theorem isInvertible_of_iso_unit
    {L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (e : L ≅ SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    IsInvertible O hO L :=
  (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L).mpr
    (Functor.isEquivalence_of_iso
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso
          (X := L) (Y := SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) e).trans
        (tensorLeftFunctorUnitIso O hO)).symm)

/-- A trivial sheaf of modules is invertible. Both predicates are the library ones of Tag 01CS. -/
theorem isInvertible_of_isTrivial
    {L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (h :
      IsTrivial O hO L) :
    IsInvertible O hO L :=
  isInvertible_of_iso_unit O hO h.some

end Trivial

section Rank

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The two copies of fixed-rank finite local freeness carried by the repository agree: the
library class and the draft class of the same name have the same body. -/
theorem isFiniteLocallyFreeOfRank_iff_invertible_isFiniteLocallyFreeOfRank
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (r :
      ℕ) :
    IsFiniteLocallyFreeOfRank L r ↔
      Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank L r :=
  ⟨fun h ↦ ⟨h.exists_isFiniteLocallyFreeOfRankData⟩,
    fun h ↦ ⟨h.exists_isFiniteLocallyFreeOfRankData⟩⟩

/-- A sheaf of modules of fixed finite rank is finite locally free, for the library class. This is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree`, restated with
the rank implicit in the instance. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (r :
      ℕ)
    [IsFiniteLocallyFreeOfRank L r] : IsFiniteLocallyFree L :=
  IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L r

/-- A sheaf of modules of fixed finite rank is finite locally free for the
`Stacks.FiniteLocallyFree` class as well. This is the bridge that makes the Tag 05P2 consequences
— local freeness, finite type, finite presentation — available to a rank-one sheaf, since those
hang off `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` and not off the library class. -/
theorem finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (r :
      ℕ)
    [IsFiniteLocallyFreeOfRank L r] : Stacks.FiniteLocallyFree.IsFiniteLocallyFree L :=
  ⟨(isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank O hO L r).exists_isFiniteLocallyFreeData⟩

/-- A sheaf of modules that is finite locally free of rank one is trivial on each member of a
covering of the terminal object: a local basis of one element is a trivialization, once the free
sheaf on a one-element type is identified with the structure sheaf. -/
theorem exists_coversTop_nonempty_iso_unit_of_isFiniteLocallyFreeOfRank_one
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [h : IsFiniteLocallyFreeOfRank L 1] :
    ∃ (I : Type u) (X : I → C) (_ : J.CoversTop X),
      ∀ i, Nonempty (L.over (X i) ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).over
          (X i))) :=
  have : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank L 1 :=
    (isFiniteLocallyFreeOfRank_iff_invertible_isFiniteLocallyFreeOfRank O hO L 1).mp h
  (Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isFiniteLocallyFreeOfRank_one
    L).exists_trivializing_cover

/-- **Clause 1 of Stacks Tag 0B8M, with the descent step removed.** A sheaf of modules that is
finite locally free of rank one is invertible on each member of a covering of the terminal object,
invertibility being read on the restricted site `(Over (X i), J.over (X i))` with its restricted
structure sheaf. This is unconditional; what the source then does, and what is not available
here, is to descend the conclusion along the covering. -/
theorem exists_coversTop_isInvertible_over_of_isFiniteLocallyFreeOfRank_one
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsFiniteLocallyFreeOfRank L 1] :
    ∃ (I : Type u) (X : I → C) (_ : J.CoversTop X),
      ∀ i, IsInvertible (overPresheaf O (X i)) (isSheaf_over O hO (X i)) (L.over (X i)) := by
  obtain ⟨I, X, hX, e⟩ :=
    exists_coversTop_nonempty_iso_unit_of_isFiniteLocallyFreeOfRank_one O hO L
  exact ⟨I, X, hX, fun i ↦ isInvertible_of_iso_unit _ _ (e i).some⟩

/-- The descent step of Stacks Tag 0B8M, as a hypothesis: a sheaf of modules invertible on every
member of a covering of the terminal object is invertible. This is not proved anywhere in this
repository — see the implementation notes of this file for what is missing. It is phrased as a
`Prop` so that the one theorem needing it can take it as an argument and name it.

Note that this statement is *stronger* than what clause 1 of Tag 0B8M needs, and clause 1 does
not use it: clause 1 has only locally *trivial* sheaves to descend, and for those an inverse is
constructed globally as the dual sheaf. See
`Stacks.InvertibleLocallyFree.isInvertible_of_isFiniteLocallyFreeOfRank_one`. The hypothesis
here quantifies over sheaves merely invertible on each member of the covering, which is the
genuine descent problem. -/
def InvertibleIsLocal : Prop :=
  ∀ (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (I :
    Type u) (X : I → C),
    J.CoversTop X →
      (∀ i, IsInvertible (overPresheaf O (X i)) (isSheaf_over O hO (X i)) (M.over (X i))) →
        IsInvertible O hO M

/-- **Clause 1 of Stacks Tag 0B8M, under the added hypothesis `InvertibleIsLocal`.** A sheaf of
modules that is finite locally free of rank one is invertible. The hypothesis is the descent step
of the source's proof and is not discharged here; it is named in the declaration name for that
reason, and no Stacks attribute is attached to this declaration.

This is superseded as a route to clause 1 by
`Stacks.InvertibleLocallyFree.isInvertible_of_isFiniteLocallyFreeOfRank_one`, which is
unconditional. It is kept because it is stated for an arbitrary section universe `w`, whereas
the unconditional version is forced to `w = max u v` by the internal hom of Tag 03EM; so at a
section universe where the dual sheaf is unavailable this is still the only form of clause 1
on offer. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one_of_invertibleIsLocal
    (hdescent : InvertibleIsLocal O hO)
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsFiniteLocallyFreeOfRank L 1] :
    IsInvertible O hO L :=
  have ⟨I, X, hX, h⟩ :=
    exists_coversTop_isInvertible_over_of_isFiniteLocallyFreeOfRank_one O hO L
  hdescent L I X hX h

end Rank

end Stacks.InvertibleLocallyFree

end
