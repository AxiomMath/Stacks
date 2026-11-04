module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkInverseImageModules

/-!
# The fibre of a sheaf of commutative rings, naturally in the sheaf

Let `Φ` be a point of a site.  The fibre at `Φ` of a sheaf of commutative rings can be taken in
three places — in `Type`, in `RingCat` and in `CommRingCat` — and the two passages between them
are `Stacks.Sheaves.StalkTransport.ringStalkComparison` and `Stacks.commRingPresheafFiberIso`,
each a component of `CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso`.  This file
records that their composite is natural in the sheaf of commutative rings.

It is pure bookkeeping, and it exists for one purpose: a computation that has to use the
naturality of an *isomorphism of stalk functors* — which is a statement about fibres of sheaves of
**sets** — must first move the ring-valued fibre of a morphism of sheaves of rings into the
set-valued world.  That is what this lemma does, and it is the last thing the coefficient
compatibility of step (3) of [Stacks Project, Tag 04I6] needed.

## Main results

* `Stacks.Sheaves.StalkTransport.commRingFiber_map_ringStalkComparison` — the naturality just
  described.

## References

* [Stacks Project, Tag 04EH](https://stacks.math.columbia.edu/tag/04EH)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace Stacks.Sheaves.StalkTransport

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget CommRingCat.{w})]
  (Φ : J.Point.{w}) {O O' : Sheaf J CommRingCat.{w}} (α : O ⟶ O')

omit [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The comparison from the `Type`-valued fibre to the `CommRingCat`-valued fibre is natural in
the sheaf of commutative rings.**

The fibre at a point of a site of a sheaf of commutative rings is computed in three ways — as a
set, as a ring, and as a commutative ring — and the passages between them are
`Stacks.Sheaves.StalkTransport.ringStalkComparison` and `Stacks.commRingPresheafFiberIso`.  This
says that their composite commutes with the map induced by a morphism `α` of sheaves of
commutative rings: the fibre of `α` read at `CommRingCat` is the fibre of the underlying map of
sheaves of sets, read through the comparison.

There is no mathematics in it.  Both comparisons are components of
`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso`, so the statement is two
naturality squares pasted together.  It is recorded because the coefficient compatibility of step
(3) of [Stacks Project, Tag 04I6] has to move the fibre of the structure map
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` out of the ring-valued world and into the
set-valued one, where naturality of an isomorphism of stalk functors is available. -/
theorem commRingFiber_map_ringStalkComparison
    (z : (Φ.sheafFiber (A := Type w)).obj
      (Sheaf.ringSheaf ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj O))) :
    ((Φ.sheafFiber (A := CommRingCat.{w})).map α).hom
        ((Stacks.commRingPresheafFiberIso Φ O.obj).ringCatIsoToRingEquiv
          (ringStalkComparison Φ
            ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj O) z)) =
      (Stacks.commRingPresheafFiberIso Φ O'.obj).ringCatIsoToRingEquiv
        (ringStalkComparison Φ
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj O')
          ((Φ.sheafFiber (A := Type w)).map
            ((sheafCompose J (forget CommRingCat.{w})).map α) z)) := by
  have h1 := ConcreteCategory.congr_hom
    ((Φ.presheafFiberCompIso (forget RingCat.{w})).hom.naturality
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α).hom) z
  have h2 := ConcreteCategory.congr_hom
    ((Φ.presheafFiberCompIso (forget₂ CommRingCat.{w} RingCat.{w})).hom.naturality α.hom)
    (ringStalkComparison Φ ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj O) z)
  exact h2.symm.trans (congrArg
    (Stacks.commRingPresheafFiberIso Φ O'.obj).ringCatIsoToRingEquiv h1.symm)

end Stacks.Sheaves.StalkTransport

end

end
