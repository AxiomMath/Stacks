module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassBijection

/-!
# A torsor with sections on a covering and vanishing first Čech cohomology is trivial

Let `(C, J)` be a site, let `G` be an abelian sheaf on it, let `U` be an object and let
`𝒰 = {U_i → U}` be a covering family of `U`.  A torsor under the restriction `G|_U` which has
a section over every member of the family is trivial as soon as `Ȟ¹(𝒰, G)` vanishes.

## Main results

* `Stacks.Cohomology.Torsors.isTrivial_of_subsingleton_cechH1`: the statement above.

## Implementation notes

This is the triviality criterion read off the bijection
`Stacks.Cohomology.Torsors.locallyTrivialClassEquivCechH1` of [Stacks Project, Tag 0A6G]: the
isomorphism classes of torsors under `G|_U` with a section over every member of the family are
in bijection with `Ȟ¹(𝒰, G)`, so when that group has one element such a torsor is in the class
of the trivial torsor, which by `Stacks.Cohomology.Torsors.trivialTorsor_isTorsor` is itself
such a class.

The criterion is stated with `Ȟ¹(𝒰, G)` as the explicit quotient
`Stacks.CechSite.cechH1` of cocycles by coboundaries, which is where the bijection lands.
`Stacks.CechSite.subsingleton_cechCohomologyOne_iff` converts a vanishing statement for the
degree-one Čech cohomology computed as a cohomology group of the Čech complex into this form,
so a vanishing theorem proved for the Čech complex — as the vanishing of the positive-degree
Čech cohomology of a quasi-coherent module on a standard covering of an affine scheme is — is
usable here directly, with no comparison with the `Ext`-group first cohomology of
[Stacks Project, Tag 03AJ] and no bijection of that tag.

## References

* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
* [Stacks Project, Tag 03AI](https://stacks.math.columbia.edu/tag/03AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe h a w v u

namespace Stacks.Cohomology.Torsors

open Stacks.CechSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{max a u v w}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify J AddCommGrpCat.{max a u v w}]
  [HasSheafify (J.over U) AddCommGrpCat.{max a u v w}]
  [HasExt.{h} (Sheaf J AddCommGrpCat.{max a u v w})]
  [HasExt.{h} (Sheaf (J.over U) AddCommGrpCat.{max a u v w})]

/-- **A torsor with a section over every member of a covering family and vanishing first Čech
cohomology is trivial.**  The isomorphism classes of torsors under `G|_U` with a section over
every member of the family are in bijection with `Ȟ¹(𝒰, G)` by [Stacks Project, Tag 0A6G], and
the trivial torsor is one of them, so when `Ȟ¹(𝒰, G)` has a single element the given torsor is
equivariantly isomorphic to the trivial one. -/
theorem isTrivial_of_subsingleton_cechH1 (hE : E.sieve₀ ∈ J U)
    (G : Sheaf J AddCommGrpCat.{max a u v w})
    (hvanish : Subsingleton (cechH1 E G.obj))
    (F : AbelianTorsor (G.over U))
    (hs : ∀ i, Nonempty (F.1.presheaf.obj (op (Over.mk (E.f i))))) :
    F.1.IsTrivial := by
  let T : AbelianTorsor (G.over U) :=
    ⟨trivialTorsor (abelianSheafAsGroupSheaf (G.over U)), trivialTorsor_isTorsor _⟩
  have hTs : ∀ i, Nonempty (T.1.presheaf.obj (op (Over.mk (E.f i)))) := fun i =>
    ⟨(1 : (abelianSheafAsGroupSheaf (G.over U)).presheaf.obj (op (Over.mk (E.f i))))⟩
  have hclass : (⟨Quotient.mk (torsorSetoid (G.over U)) F, ⟨F, rfl, hs⟩⟩ :
        LocallyTrivialClass E G) =
      ⟨Quotient.mk (torsorSetoid (G.over U)) T, ⟨T, rfl, hTs⟩⟩ :=
    (locallyTrivialClassEquivCechH1.{h, a, w, v, u} E hE G).injective
      (@Subsingleton.elim _ hvanish _ _)
  obtain ⟨e, he⟩ := (torsorSetoid (G.over U)).iseqv.symm
    (Quotient.exact (congrArg Subtype.val hclass))
  exact ⟨e, he⟩

end Stacks.Cohomology.Torsors

end
