module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalDual

/-!
# Invertibility of a sheaf of modules is local on a ringed space

`Stacks.SheafOfModules.invertibleIsLocal` proves the descent step of
[Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M) — a sheaf of modules invertible on
every member of a covering of the final object is invertible — on an arbitrary site, under the
four sheafification hypotheses that the dual-sheaf route needs on that site and on each of its
localizations. This file discharges those four hypotheses for the site of opens of a topological
space, where they are automatic because that site and all its localizations are essentially
small. The result is the form of the descent step that the ringed-space developments, and in
particular Tag 0FJN, can use.

## Main results

* `Stacks.SheafOfModules.invertibleIsLocal_opens`: **invertibility of a sheaf of modules on the
  site of opens of a topological space is local.**
* `Stacks.SheafOfModules.invertibleIsLocal_ringedSpace`: the same statement for the structure
  sheaf of a ringed space, at the spelling of the sheaf condition that the determinant
  development carries.

## Implementation notes

The four hypotheses are `HasWeakSheafify` and `WEqualsLocallyBijective` for presheaves of
abelian groups, on the site itself and on each of its localizations. On the site of opens they
all follow from essential smallness, by `CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`; the
localization `(Opens X)/V` is again essentially small, being a `u`-small category when
`Opens X` is, so the same two lemmas apply there.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

/-- Sheafification of presheaves of abelian groups exists on the site of opens of a topological
space, and on each of its localizations: the sites are essentially small. -/
theorem hasSheafify_opens {X : Type u} [TopologicalSpace X] :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of presheaves of abelian groups on the site of opens of a topological
space are the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_opens {X : Type u} [TopologicalSpace X] :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u} _

/-- **Stacks Project, Tag 0B8M, descent step, for the site of opens of a topological space.** A
sheaf of `𝒪`-modules invertible on every member of a covering of the whole space is invertible.

This is `Stacks.SheafOfModules.invertibleIsLocal`; all this adds is that the four
sheafification hypotheses of that theorem hold automatically here. -/
theorem invertibleIsLocal_opens {X : Type u} [TopologicalSpace X]
    (𝒪 : (Opens X)ᵒᵖ ⥤ CommRingCat.{u})
    (h𝒪 : Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (TensorSheafification.structureRingPresheaf 𝒪)) :
    Stacks.InvertibleLocallyFree.InvertibleIsLocal 𝒪 h𝒪 := by
  let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := hasSheafify_opens
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    wEqualsLocallyBijective_opens
  let : ∀ V : Opens X,
      HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u} := fun _ =>
    hasSheafifyEssentiallySmallSite.{u} _ _
  let : ∀ V : Opens X,
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _ => GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u} _
  exact invertibleIsLocal 𝒪 h𝒪

/-- **Stacks Project, Tag 0B8M, descent step, for a ringed space.** A sheaf of modules on a
ringed space invertible on every member of a covering of the whole space is invertible, with the
sheaf condition spelled as the determinant development spells it. -/
theorem invertibleIsLocal_ringedSpace (Y : RingedSpace.{u, u}) :
    Stacks.InvertibleLocallyFree.InvertibleIsLocal Y.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ Y.presheaf
        (forget₂ CommRingCat.{u} RingCat.{u}) Y.IsSheaf) :=
  invertibleIsLocal_opens Y.presheaf _

end Stacks.SheafOfModules

end
