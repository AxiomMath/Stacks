module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheafFunctoriality
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct

/-!
# The ringed site of a representable category fibred in groupoids (Stacks 075I)

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf category of a scheme
`S` which is representable by an object `X` of `(Sch/S)`, and let `τ` be a topology on the
underlying category of schemes which is coarser than the fppf one. Then the associated site of
`𝒳` (Stacks 06TP) and the associated site of the slice `(Sch/S)/X` are equivalent as *ringed*
sites: the representing equivalence over the base is continuous and cocontinuous for the two
associated topologies, and it carries the structure sheaf (Stacks 06TV) of the slice to the
structure sheaf of `𝒳`.

The identification of structure sheaves is an equality, not merely an isomorphism, and it is
the case `F := e.hom.functor` of the functoriality of the structure sheaf (Stacks 06TW): the
representing equivalence is in particular a 1-morphism of categories fibred in groupoids,
because its target `Over.forget X` is fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.representableBy_isContinuous_and_isCocontinuous`: **Stacks 075I**,
  the representing equivalence is an equivalence of the two associated sites.
* `AlgebraicGeometry.Stack.structureSheaf_representableBy`: **Stacks 075I**, it identifies the
  two structure sheaves.
* `AlgebraicGeometry.Stack.structureSheaf_obj_representableBy`: the same identification on
  underlying presheaves of commutative rings.

## Main definitions

* `AlgebraicGeometry.Stack.structureSheafRepresentableByIso`: **Stacks 075I**, the comparison
  isomorphism of structure sheaves, which is the identity on sections.

## Implementation notes

`AlgebraicGeometry.RingedSite` has no bundled type of equivalences, so the equivalence of
ringed sites is recorded by its constituents: the two continuity statements for the underlying
equivalence of categories, and the identification of the structure sheaves.

## References

* [Stacks Project, Tag 075I](https://stacks.math.columbia.edu/tag/075I)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (X : BigFppfOver B S hS) (e : StacksRepresentableCFG.RepresentableBy p X)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

include hp

/-- **Stacks 075I.** The equivalence over the base representing `p` by `X` is continuous and
cocontinuous for the associated topologies (Stacks 06TP) of `𝒳` and of the slice `(Sch/S)/X`,
so it is an equivalence of the two sites. It is a 1-morphism of categories fibred in groupoids
because the slice is fibred in groupoids over the base, so this is Stacks 06NW. -/
@[stacks 075I "the equivalence of the underlying sites"]
theorem representableBy_isContinuous_and_isCocontinuous :
    e.hom.functor.IsContinuous (associatedTopology B S hS p τ)
        (associatedTopology B S hS (Over.forget X) τ) ∧
      e.hom.functor.IsCocontinuous (associatedTopology B S hS p τ)
        (associatedTopology B S hS (Over.forget X) τ) :=
  have : p.IsFibered := hp.isFibered
  have : (Over.forget X).IsFibered :=
    (Functor.IsFiberedInGroupoids.over_forget X).isFibered
  ((Functor.IsFiberedInGroupoids.over_forget X).isFibredOneMorphism e.hom.w
    (p𝒳 := p)).isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))

include hτ

/-- **Stacks 075I.** The representing equivalence carries the structure sheaf of the slice
`(Sch/S)/X` to the structure sheaf of `𝒳`: restriction along it of the one is the other, as
sheaves of commutative rings. -/
@[stacks 075I "the structure sheaves agree"]
theorem structureSheaf_representableBy
    [e.hom.functor.IsContinuous (associatedTopology B S hS p τ)
      (associatedTopology B S hS (Over.forget X) τ)] :
    (e.hom.functor.sheafPushforwardContinuous CommRingCat.{u}
          (associatedTopology B S hS p τ)
          (associatedTopology B S hS (Over.forget X) τ)).obj
        (structureSheaf B S hS (Over.forget X)
          (Functor.IsFiberedInGroupoids.over_forget X) τ hτ) =
      structureSheaf B S hS p hp τ hτ :=
  sheafPushforwardContinuous_structureSheaf B S hS p (Over.forget X) e.hom.functor hp
    (Functor.IsFiberedInGroupoids.over_forget X) τ hτ e.hom.w

/-- The underlying presheaf of commutative rings of the structure sheaf of `𝒳` is the
restriction along the representing equivalence of that of the slice `(Sch/S)/X`: the ring of
sections over an object of `𝒳` is the ring of sections over its image. -/
theorem structureSheaf_obj_representableBy :
    (structureSheaf B S hS p hp τ hτ).obj =
      e.hom.functor.op ⋙ (structureSheaf B S hS (Over.forget X)
        (Functor.IsFiberedInGroupoids.over_forget X) τ hτ).obj := by
  have h : p.op = e.hom.functor.op ⋙ (Over.forget X).op :=
    (congrArg (fun G : 𝒳 ⥤ BigFppfOver B S hS => G.op) e.hom.w).symm
  rw [structureSheaf_obj, structureSheaf_obj, h, Functor.assoc]

/-- **Stacks 075I.** The comparison isomorphism of structure sheaves under the representing
equivalence. It is the canonical isomorphism attached to the equality
`AlgebraicGeometry.Stack.structureSheaf_representableBy`, hence the identity on sections. -/
@[stacks 075I "the comparison of structure sheaves"]
noncomputable def structureSheafRepresentableByIso
    [e.hom.functor.IsContinuous (associatedTopology B S hS p τ)
      (associatedTopology B S hS (Over.forget X) τ)] :
    (e.hom.functor.sheafPushforwardContinuous CommRingCat.{u}
          (associatedTopology B S hS p τ)
          (associatedTopology B S hS (Over.forget X) τ)).obj
        (structureSheaf B S hS (Over.forget X)
          (Functor.IsFiberedInGroupoids.over_forget X) τ hτ) ≅
      structureSheaf B S hS p hp τ hτ :=
  eqToIso (structureSheaf_representableBy B S hS p hp X e τ hτ)

end AlgebraicGeometry.Stack

end
