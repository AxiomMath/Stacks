module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSiteGeneral
import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# The group of isomorphism classes of torsors under an abelian sheaf

Tag 03AJ identifies the isomorphism classes of torsors under an abelian sheaf `H` on a site with
`H¹(H)`, as a bijection of types: `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1`.  The
isomorphism classes also carry an abelian group structure of their own — the *contracted product*
`F ∧_H G`, the quotient of `F × G` by the antidiagonal action of `H` — and the bijection is an
isomorphism of groups for it.  This file supplies that group structure and the isomorphism.

The group structure is transported across the bijection, and then *pinned* by two laws that
describe it without reference to the transport:

* `Stacks.Cohomology.Torsors.torsorIsoClasses_mk_add_of_equivariant`: the sum of two classes is
  the class of any torsor receiving an equivariant pairing out of the product of the two — which
  is exactly a torsor identified with their contracted product.  Since a torsor under `H` admits
  at most one class, this determines the addition completely.
* `Stacks.Cohomology.Torsors.torsorIsoClasses_trivial_eq_zero`: the zero is the class of the
  trivial torsor.

This is the same presentation that
`Stacks.Cohomology.SheafTorsor.instAddCommGroupTorsorClass` gives to the torsor classes of Tag
02FQ on a topological space, where the two laws are the fields
`Stacks.Cohomology.SheafTorsor.TorsorCohomologyClassification.pairing` and
`.of_global_section` of the classification.  Transporting rather than building the contracted
product is what lets the group laws be the group laws of `Ext¹`: associativity, commutativity and
the existence of inverses of the contracted product are not proved again, and no isomorphism
`(F ∧ G) ∧ K ≅ F ∧ (G ∧ K)` has to be written down.

## Main definitions

* `Stacks.Cohomology.Torsors.instAddCommGroupTorsorIsoClasses`: **the isomorphism classes of
  torsors under an abelian sheaf form an abelian group.**
* `Stacks.Cohomology.Torsors.torsorIsoClassesAddEquivH1`: **Tag 03AJ as an isomorphism of abelian
  groups**, `torsorIsoClasses H ≃+ H¹(H)`.

## Main results

* `Stacks.Cohomology.Torsors.torsorIsoClasses_mk_add_of_equivariant` and
  `Stacks.Cohomology.Torsors.torsorIsoClasses_trivial_eq_zero`: the two laws pinning the group
  structure, as above.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w t v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- **The isomorphism classes of torsors under an abelian sheaf form an abelian group.**  The
addition is the contracted product and the zero is the trivial torsor, by
`Stacks.Cohomology.Torsors.torsorIsoClasses_mk_add_of_equivariant` and
`Stacks.Cohomology.Torsors.torsorIsoClasses_trivial_eq_zero`; the group laws themselves are
those of `Ext¹`, carried across the bijection of Tag 03AJ. -/
@[stacks 03AJ "the abelian-group structure on the isomorphism classes of torsors, with addition \
the contracted product and zero the trivial torsor"]
public instance instAddCommGroupTorsorIsoClasses (H : Sheaf J AddCommGrpCat.{t}) :
    AddCommGroup (torsorIsoClasses H) :=
  (torsorIsoClassesEquivH1 H).addCommGroup

/-- **Stacks Project, Tag 03AJ as an isomorphism of abelian groups.**  The canonical bijection
between the isomorphism classes of torsors under an abelian sheaf and its first cohomology group
carries the contracted product of torsors to the addition of `Ext¹`. -/
@[stacks 03AJ "the canonical bijection as a group isomorphism, for the contracted product of \
torsors",
  sga "4½ Cycle 1.1.1" "as a group map"]
public def torsorIsoClassesAddEquivH1 (H : Sheaf J AddCommGrpCat.{t}) :
    torsorIsoClasses H ≃+ Sheaf.H H 1 :=
  (torsorIsoClassesEquivH1 H).addEquiv

/-- The group isomorphism of Tag 03AJ has exactly the bijection of Tag 03AJ underneath it. -/
@[simp]
public theorem torsorIsoClassesAddEquivH1_toEquiv (H : Sheaf J AddCommGrpCat.{t}) :
    (torsorIsoClassesAddEquivH1 H).toEquiv = torsorIsoClassesEquivH1 H := rfl

/-- The group isomorphism of Tag 03AJ, read on a class. -/
public theorem torsorIsoClassesAddEquivH1_apply (H : Sheaf J AddCommGrpCat.{t})
    (x : torsorIsoClasses H) :
    torsorIsoClassesAddEquivH1 H x = torsorIsoClassesEquivH1 H x := rfl

/-- **The zero of the group of torsor classes is the class of the trivial torsor.**  One of the
two laws pinning the group structure of
`Stacks.Cohomology.Torsors.instAddCommGroupTorsorIsoClasses`. -/
@[stacks 03AJ "the zero of the group of torsor classes is the trivial torsor"]
public theorem torsorIsoClasses_trivial_eq_zero (H : Sheaf J AddCommGrpCat.{t}) :
    (by exact (Quotient.mk (torsorSetoid H)
        ⟨trivialTorsor (abelianSheafAsGroupSheaf H),
          trivialTorsor_isTorsor (abelianSheafAsGroupSheaf H)⟩) : torsorIsoClasses H) = 0 :=
  (torsorIsoClassesAddEquivH1 H).injective <|
    (torsorIsoClassesEquivH1_trivial H).trans (AddEquiv.map_zero _).symm

/-- **The sum of two torsor classes is the class of their contracted product.**  A torsor `T`
receiving a morphism out of the product of the presheaves of `F` and `G` which adds the two
acting sections is precisely a torsor identified with the contracted product `F ∧_H G`, and its
class is the sum of the two classes.  This is the second of the two laws pinning the group
structure of `Stacks.Cohomology.Torsors.instAddCommGroupTorsorIsoClasses`, and together with
`Stacks.Cohomology.Torsors.torsorIsoClasses_trivial_eq_zero` it determines the addition. -/
@[stacks 03AJ "the addition of torsor classes is the contracted product of torsors",
  sga "4 XVIII 1.3.3" "partial",
  sga "4½ Sommes_trig 1.3" "partial"]
public theorem torsorIsoClasses_mk_add_of_equivariant (H : Sheaf J AddCommGrpCat.{t})
    (F G T : AbelianTorsor H)
    (f : Generators.productPresheaf' F.1.presheaf G.1.presheaf ⟶ T.1.presheaf)
    (hf : ∀ (U : Cᵒᵖ) (a b : H.obj.obj U) (s : F.1.presheaf.obj U) (t : G.1.presheaf.obj U),
      f.app U (F.1.act U (Multiplicative.ofAdd a) s,
          G.1.act U (Multiplicative.ofAdd b) t) =
        T.1.act U (Multiplicative.ofAdd (a + b)) (f.app U (s, t))) :
    (by exact Quotient.mk (torsorSetoid H) F : torsorIsoClasses H) +
        (by exact Quotient.mk (torsorSetoid H) G : torsorIsoClasses H) =
      Quotient.mk (torsorSetoid H) T := by
  apply (torsorIsoClassesAddEquivH1 H).injective
  refine (AddEquiv.map_add (torsorIsoClassesAddEquivH1 H) _ _).trans ?_
  exact Generators.torsorClass_add_of_equivariant' H F G T f hf

end Stacks.Cohomology.Torsors

end
