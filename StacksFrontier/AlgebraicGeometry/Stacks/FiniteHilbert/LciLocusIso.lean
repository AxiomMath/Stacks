module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusBaseChange

/-!
# The local complete intersection locus is closed under isomorphism

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S` and
let `d` be a natural number. **Stacks 06CJ** cuts out the local complete intersection locus
`ℋ_{d,lci}(𝒳/𝒴)` inside the relative finite Hilbert category `ℋ_d(𝒳/𝒴)` by a condition on the
relative map `x_α : Z ⟶ X_y` of Stacks 06CK. This file proves that the condition is invariant
under isomorphism in `ℋ_d(𝒳/𝒴)`, so that the locus is a *strictly* full subcategory
(`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`).

An isomorphism `φ : Ξ ≅ Ξ'` of quintuples has in particular a base component which is an
isomorphism `ι : U ⟶ U'` of the site, so the two quintuples live over *different* slices of the
big fppf site and a set of data exhibiting the relative map of `Ξ'` has to be **transported**, not
merely reindexed. The transport is
`AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.ofHom`, which exists for every morphism of
quintuples, and the relative map of the transport is the restriction of the original one along
`ι` (`AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.map_hom_ofHom`).

What the isomorphism adds is that the restriction itself changes nothing: restriction along an
isomorphism of base objects leaves both conditions defining the locus unchanged
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeRestrict_iff`). The other comparison
appearing in the transported relative map is already invertible for every morphism of
quintuples, the cover component of such a morphism sitting in a cartesian square.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.holdsOnEveryEtaleChart_map_ofHom_iff`:
  an every-étale-chart condition on the relative map is unchanged by the transport along an
  isomorphism of quintuples.
* `AlgebraicGeometry.Stack.FiniteHilbert.isClosedUnderIsomorphisms_lciLocus`: the local complete
  intersection locus is closed under isomorphism.

## Implementation notes

Nothing below inverts a morphism of `𝒴` or of `𝒳`: the transport itself is built from the
universal property of strongly cartesian morphisms in
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusBaseChange`, and the only thing the
isomorphism of quintuples is used for is the `CategoryTheory.IsIso` instance on the underlying
morphism of schemes of its base component, which is what the invariance of an every-étale-chart
condition under restriction asks for.

## References

* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

variable {P Q : Object B S hS 𝒳 𝒴 F d}

/-! ### The components of an isomorphism of quintuples -/

/-- The base component of an isomorphism of quintuples is an isomorphism, composition in the
relative finite Hilbert category being componentwise. -/
instance isIso_iso_hom_f (φ : P ≅ Q) : IsIso φ.hom.f :=
  ⟨⟨φ.inv.f, congrArg Hom.f φ.hom_inv_id, congrArg Hom.f φ.inv_hom_id⟩⟩

/-- The underlying morphism of schemes of the base component of an isomorphism of quintuples is
an isomorphism: the forgetful functor of a slice sends isomorphisms to isomorphisms. -/
instance isIso_iso_hom_f_left (φ : P ≅ Q) : IsIso φ.hom.f.left :=
  inferInstanceAs (IsIso ((Over.forget (B.obj hS)).map φ.hom.f))

/-! ### Transport along an isomorphism -/

/-- **The two conditions cutting out the local complete intersection locus are unchanged by the
transport along an isomorphism of quintuples.** They are every-étale-chart conditions, which are
invariant under restriction along an isomorphism of base objects and under composition with an
isomorphism of presheaves. -/
theorem RelativeMapData.holdsOnEveryEtaleChart_map_ofHom_iff (φ : P ≅ Q)
    (D : RelativeMapData Q) (prop : MorphismProperty Scheme.{u}) :
    Space.HoldsOnEveryEtaleChart B P.U.left.1 P.U.left.2 prop (ofHom φ.hom D).map.hom ↔
      Space.HoldsOnEveryEtaleChart B Q.U.left.1 Q.U.left.2 prop D.map.hom := by
  have h1 : Space.HoldsOnEveryEtaleChart B P.U.left.1 P.U.left.2 prop (ofHom φ.hom D).map.hom ↔
      Space.HoldsOnEveryEtaleChart B P.U.left.1 P.U.left.2 prop
        ((OverShriek.relocalizeRestrict φ.hom.f.left).map D.map.hom) := by
    have _ := RelativeMapData.isIso_restrictYonedaHom_coverComparison φ.hom
    rw [map_hom_ofHom]
    exact Space.holdsOnEveryEtaleChart_iso_comp_iff B P.U.left.1 P.U.left.2 prop _ _
  exact h1.trans (Space.holdsOnEveryEtaleChart_relocalizeRestrict_iff B Q.U.left.1 P.U.left.1
    Q.U.left.2 P.U.left.2 φ.hom.f.left prop D.map.hom)

/-- **The local complete intersection locus is closed under isomorphism.** An isomorphism of
quintuples transports a set of data exhibiting the relative map of the target to one for the
source, and the relative map of the transport is the restriction of the original along an
isomorphism of the base, which changes neither of the two conditions cutting out the locus.

No Stacks tag attribute is placed: the section of Stacks 06CJ asserts that the locus is a full
subcategory, which holds of any object property, and nowhere states that it is closed under
isomorphism. The statement is a step in the proof of Stacks 06CL, where it is what identifies the
image of the first projection of a 2-fibre product with the locus. -/
instance isClosedUnderIsomorphisms_lciLocus :
    ObjectProperty.IsClosedUnderIsomorphisms
      (lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) := by
  refine ⟨fun {P Q} φ hP D => ?_⟩
  have h := hP (RelativeMapData.ofHom φ.hom D)
  exact ⟨(RelativeMapData.holdsOnEveryEtaleChart_map_ofHom_iff φ D _).mp h.1,
    (RelativeMapData.holdsOnEveryEtaleChart_map_ofHom_iff φ D _).mp h.2⟩

end FiniteHilbert

end AlgebraicGeometry.Stack

end
