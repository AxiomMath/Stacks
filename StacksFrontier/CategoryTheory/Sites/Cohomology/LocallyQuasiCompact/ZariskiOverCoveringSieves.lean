module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperBaseChange
public import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# From a pointwise open cover to a covering sieve of the localized Zariski site

Let `S` be a locally quasi-compact Zariski situation, `Y` an object of its site and `Z` an object
of the localized site `LC_Zar/Y`. Of the two Grothendieck topologies involved,

* `TopologicalSpace.Opens.grothendieckTopology Z.left` is **pointwise**: a sieve covers `V` as
  soon as every point of `V` lies in some member of it;
* `S.zariskiTopology.over Y` is `S.zariskiPrecoverage.toGrothendieck` localized, an inductive
  `CategoryTheory.Precoverage.Saturate` closure.

This file shows that a sieve on `Z` containing, around every point of `Z.left`, the open
immersion of some open subset is a covering sieve of `S.zariskiTopology.over Y`.

## Main definitions

All in the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`.

* `opensOverHom`: the open immersion of an open subset of `Z.left` into `Z`, as a morphism of
  `LC_Zar/Y`.

## Main results

In the same namespace:

* `mem_zariskiTopology_over_of_forall_exists_opens`: a sieve on `Z` containing, around every point
  of `Z.left`, the open immersion of some open neighbourhood, is a Zariski covering sieve.
* `mem_zariskiTopology_over_of_mem_opens_grothendieckTopology`: the same with the pointwise datum
  packaged as a covering sieve of `⊤` for `Opens.grothendieckTopology Z.left`.
* `equalizerSieve_mem_zariskiTopology_over_of_forall_exists_opens`: for a presheaf on `LC_Zar/Y`
  with values in a concrete category, two sections that agree after restriction to some open
  neighbourhood of every point of `Z.left` agree on a Zariski covering sieve of `Z`.

## Implementation notes

The points of `Z.left` serve as the index type of the open cover given to
`mem_zariskiTopology_over_of_opens_cover`, whose index type is a universe variable of its own.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u' v' w₀ u w

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- **The open immersion of an open subset of `Z.left` into `Z`**, as a morphism of the localized
Zariski site `LC_Zar/Y`. Its source is the open subobject `S.opensToSlice Z.left` cuts out,
regarded over `Y` through `Z`. -/
abbrev opensOverHom {Y : S.category} (Z : Over Y) (V : Opens Z.left.obj) :
    Over.mk ((((S.opensToSlice Z.left).1.obj V).hom) ≫ Z.hom) ⟶ Z :=
  Over.homMk (((S.opensToSlice Z.left).1.obj V).hom)

/-- **A sieve on `Z` that contains, around every point of `Z.left`, the open immersion of some
open neighbourhood of that point, is a Zariski covering sieve of `Z`.** -/
theorem mem_zariskiTopology_over_of_forall_exists_opens {Y : S.category} {Z : Over Y}
    (R : Sieve Z)
    (hR : ∀ z : Z.left.obj, ∃ V : Opens Z.left.obj, z ∈ V ∧ R.arrows (opensOverHom S Z V)) :
    R ∈ (S.zariskiTopology.over Y) Z := by
  choose V hmem harr using hR
  exact mem_zariskiTopology_over_of_opens_cover S V (fun z => ⟨z, hmem z⟩) R harr

/-- **A covering sieve of `⊤` for the pointwise topology of `Z.left` gives a Zariski covering
sieve of `Z`**, as soon as the open immersion of every member of the former lies in the latter.
-/
theorem mem_zariskiTopology_over_of_mem_opens_grothendieckTopology {Y : S.category} {Z : Over Y}
    (R : Sieve Z) (T : Sieve (⊤ : Opens Z.left.obj))
    (hT : T ∈ Opens.grothendieckTopology Z.left.obj ⊤)
    (hR : ∀ (V : Opens Z.left.obj) (g : V ⟶ (⊤ : Opens Z.left.obj)), T.arrows g →
      R.arrows (opensOverHom S Z V)) :
    R ∈ (S.zariskiTopology.over Y) Z :=
  mem_zariskiTopology_over_of_forall_exists_opens S R fun z =>
    let ⟨V, g, hg, hz⟩ := hT z (by trivial)
    ⟨V, hz, hR V g hg⟩

section Presheaf

variable {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w₀}
  [∀ A B, FunLike (FD A B) (CD A) (CD B)] [ConcreteCategory.{w₀} D FD]

/-- **Two sections of a presheaf on `LC_Zar/Y` that agree near every point of `Z.left` agree on a
Zariski covering sieve of `Z`.** -/
theorem equalizerSieve_mem_zariskiTopology_over_of_forall_exists_opens {Y : S.category}
    {Z : Over Y} {P : (Over Y)ᵒᵖ ⥤ D} (x y : ToType (P.obj (op Z)))
    (h : ∀ z : Z.left.obj, ∃ V : Opens Z.left.obj, z ∈ V ∧
      P.map (opensOverHom S Z V).op x = P.map (opensOverHom S Z V).op y) :
    Presheaf.equalizerSieve (X := op Z) x y ∈ (S.zariskiTopology.over Y) Z :=
  mem_zariskiTopology_over_of_forall_exists_opens S _ h

end Presheaf

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
