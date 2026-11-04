module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Defs
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.LocalUnitBranches

/-!
# The local-unit map of an inverse-image sheaf of rings

The local-unit condition of Stacks 04ES is a condition on sections, and the sections of an
inverse image along a morphism of topoi are not describable. What is describable is the
*categorical* form of the condition — joint epimorphy of the two components of the local-unit
map — and a left adjoint carries a jointly epimorphic pair to a jointly epimorphic pair. This
file identifies the local-unit map of an inverse-image sheaf of rings with the inverse image of
the local-unit map, and deduces that the local-unit condition passes to an inverse image.

The identification is possible because
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf` leaves the underlying sheaf of sets untouched:
`CategoryTheory.Sheaf.ringSheaf (pullbackRingSheaf J Φ R)` *is* `Φ.obj (ringSheaf R)`, and the
ring operations of the inverse image are the ones transported along the sections functors of
`Φ`. So the only comparison map that intervenes is the product comparison of `Φ`, which is an
isomorphism because `Φ` is left exact.

## Main definitions

* `Stacks.Sheaves.LocalRingedness.pullbackRingSqIso`: the inverse image of the square of the
  underlying sheaf of sets of a sheaf of rings is the square of the underlying sheaf of sets of
  the inverse image.

## Main results

* `Stacks.Sheaves.LocalRingedness.map_localUnitBranch_pullback`: the local-unit map of the
  inverse image is the inverse image of the local-unit map.
* `Stacks.Sheaves.LocalRingedness.jointlyEpi_localUnitBranch_pullback`: joint epimorphy of the
  two components passes to an inverse image.
* `Stacks.Sheaves.LocalRingedness.locallyEitherUnit_inverseImage`: the local-unit condition
  passes to the inverse image of a sheaf of commutative rings along a morphism of topoi.

## Implementation notes

The section-level computation rules of
`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/LocalUnitBranches.lean` are stated
for the sections functors of the site; the ones here are for an arbitrary functor to types
preserving finite products, in the vocabulary of `CategoryTheory.Sheaf.ringMulObj` and its
siblings, because the computation has to be run both for the sections functor of the source
site and for its composition with `Φ`.

## References

* [Stacks Project, Tag 04ES](https://stacks.math.columbia.edu/tag/04ES)
* [Stacks Project, Tag 04H7](https://stacks.math.columbia.edu/tag/04H7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.LocalRingedness

universe t w v u w' v' u'

/-! ### The local-unit map under a functor to types preserving finite products -/

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] (R : Sheaf J RingCat.{w})
  (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

/-- The morphism `(f, c) ↦ 1 - f`, computed by a functor to types preserving finite products. -/
lemma map_oneSubFst (z : P.obj (ringSq R)) :
    P.map (oneSubFst R) z =
      Sheaf.ringAddObj R P (Sheaf.ringOneObj R P)
        (Sheaf.ringNegObj R P (P.map prod.fst z)) := by
  rw [oneSubFst, Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_comp_apply,
    Functor.map_terminalFrom_apply, Functor.map_comp_apply]
  rfl

/-- The multiplier of a component of the local-unit map, computed by a functor to types
preserving finite products. -/
lemma map_localUnitFactor (b : Bool) (z : P.obj (ringSq R)) :
    P.map (localUnitFactor R b) z =
      (if b then
          Sheaf.ringAddObj R P (Sheaf.ringOneObj R P)
            (Sheaf.ringNegObj R P (P.map prod.fst z))
        else P.map prod.fst z) := by
  cases b with
  | false => rw [localUnitFactor]; simp only [Bool.false_eq_true, ite_false]
  | true => rw [localUnitFactor]; simp only [ite_true]; exact map_oneSubFst R P z

/-- A component of the local-unit map, computed by a functor to types preserving finite
products. -/
lemma map_localUnitBranch (b : Bool) (z : P.obj (ringSq R)) :
    P.map (localUnitBranch R b) z =
      Functor.prodObjMk (P := P) (P.map prod.fst z)
        (Sheaf.ringMulObj R P (P.map prod.snd z) (P.map (localUnitFactor R b) z)) := by
  rw [localUnitBranch, Functor.map_lift_apply, Functor.map_comp_apply, Functor.map_lift_apply]
  rfl

end Transport

/-! ### The local-unit map of an inverse-image sheaf of rings -/

section Pullback

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  (R : Sheaf K RingCat.{w'})

/-- The inverse image of the square of the underlying sheaf of sets of a sheaf of rings is the
square of the underlying sheaf of sets of its inverse image. It is the product comparison of
`Φ`, the underlying sheaf of sets of the inverse image being the inverse image of the
underlying sheaf of sets on the nose. -/
noncomputable def pullbackRingSqIso :
    Φ.obj (ringSq R) ≅ ringSq (pullbackRingSheaf J Φ R) :=
  PreservesLimitPair.iso Φ (Sheaf.ringSheaf R) (Sheaf.ringSheaf R)

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [PreservesFiniteProducts Φ] in
/-- Sections of the image of a morphism under `Φ` are sections of the image under the
composition of `Φ` with the sections functor. -/
private lemma sectionsFunctor_map_map {A B : Sheaf K (Type w')} (m : A ⟶ B) (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor J X).obj (Φ.obj A)) :
    (Sheaf.sectionsFunctor J X).map (Φ.map m) z =
      (Φ ⋙ Sheaf.sectionsFunctor J X).map m z := rfl

/-- On sections over `X`, the isomorphism `pullbackRingSqIso` sends a section to the pair of its
images under the two projections. -/
@[simp]
lemma sectionsFunctor_map_pullbackRingSqIso_hom (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor J X).obj (Φ.obj (ringSq R))) :
    (Sheaf.sectionsFunctor J X).map (pullbackRingSqIso J Φ R).hom z =
      Functor.prodObjMk (P := Sheaf.sectionsFunctor J X)
        (A := Sheaf.ringSheaf (pullbackRingSheaf J Φ R))
        (B := Sheaf.ringSheaf (pullbackRingSheaf J Φ R))
        ((Φ ⋙ Sheaf.sectionsFunctor J X).map prod.fst z)
        ((Φ ⋙ Sheaf.sectionsFunctor J X).map prod.snd z) :=
  Functor.map_prodComparison_apply (P := Sheaf.sectionsFunctor J X) Φ
    (Sheaf.ringSheaf R) (Sheaf.ringSheaf R) z

/-- The first component of the image of a section under `pullbackRingSqIso` is the image of the
section under the first projection. -/
@[simp]
lemma sectionsFunctor_map_fst_pullbackRingSqIso_hom (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor J X).obj (Φ.obj (ringSq R))) :
    (Sheaf.sectionsFunctor J X).map prod.fst
        ((Sheaf.sectionsFunctor J X).map (pullbackRingSqIso J Φ R).hom z) =
      (Φ ⋙ Sheaf.sectionsFunctor J X).map prod.fst z := by
  rw [sectionsFunctor_map_pullbackRingSqIso_hom]
  exact Functor.map_fst_prodObjMk _ _

/-- The second component of the image of a section under `pullbackRingSqIso` is the image of the
section under the second projection. -/
@[simp]
lemma sectionsFunctor_map_snd_pullbackRingSqIso_hom (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor J X).obj (Φ.obj (ringSq R))) :
    (Sheaf.sectionsFunctor J X).map prod.snd
        ((Sheaf.sectionsFunctor J X).map (pullbackRingSqIso J Φ R).hom z) =
      (Φ ⋙ Sheaf.sectionsFunctor J X).map prod.snd z := by
  rw [sectionsFunctor_map_pullbackRingSqIso_hom]
  exact Functor.map_snd_prodObjMk _ _

/-- The sum of two sections of the inverse-image sheaf of rings is their sum computed by the
addition of the original sheaf of rings transported along `Φ`. -/
lemma ringAddObj_pullback (X : Cᵒᵖ)
    (y z : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf (pullbackRingSheaf J Φ R))) :
    Sheaf.ringAddObj (pullbackRingSheaf J Φ R) (Sheaf.sectionsFunctor J X) y z =
      Sheaf.ringAddObj R (Φ ⋙ Sheaf.sectionsFunctor J X) y z :=
  Sheaf.sectionsFunctor_map_ringAddHom (pullbackRingSheaf J Φ R) X y z

/-- The product of two sections of the inverse-image sheaf of rings is their product computed by
the multiplication of the original sheaf of rings transported along `Φ`. -/
lemma ringMulObj_pullback (X : Cᵒᵖ)
    (y z : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf (pullbackRingSheaf J Φ R))) :
    Sheaf.ringMulObj (pullbackRingSheaf J Φ R) (Sheaf.sectionsFunctor J X) y z =
      Sheaf.ringMulObj R (Φ ⋙ Sheaf.sectionsFunctor J X) y z :=
  Sheaf.sectionsFunctor_map_ringMulHom (pullbackRingSheaf J Φ R) X y z

/-- The negative of a section of the inverse-image sheaf of rings is its negative computed by the
negation of the original sheaf of rings transported along `Φ`. -/
lemma ringNegObj_pullback (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf (pullbackRingSheaf J Φ R))) :
    Sheaf.ringNegObj (pullbackRingSheaf J Φ R) (Sheaf.sectionsFunctor J X) z =
      Sheaf.ringNegObj R (Φ ⋙ Sheaf.sectionsFunctor J X) z :=
  Sheaf.sectionsFunctor_map_ringNegHom (pullbackRingSheaf J Φ R) X z

/-- The unit section of the inverse-image sheaf of rings is the unit of the original sheaf of
rings transported along `Φ`. -/
lemma ringOneObj_pullback (X : Cᵒᵖ) :
    Sheaf.ringOneObj (pullbackRingSheaf J Φ R) (Sheaf.sectionsFunctor J X) =
      Sheaf.ringOneObj R (Φ ⋙ Sheaf.sectionsFunctor J X) :=
  Sheaf.sectionsFunctor_map_ringOneHom (pullbackRingSheaf J Φ R) X default

/-- The product comparison applied to a pair of sections. -/
lemma sectionsFunctor_map_pullbackRingSqIso_hom_prodObjMk (X : Cᵒᵖ)
    (y z : (Φ ⋙ Sheaf.sectionsFunctor J X).obj (Sheaf.ringSheaf R)) :
    (Sheaf.sectionsFunctor J X).map (pullbackRingSqIso J Φ R).hom
        (Functor.prodObjMk (P := Φ ⋙ Sheaf.sectionsFunctor J X) y z) =
      Functor.prodObjMk (P := Sheaf.sectionsFunctor J X)
        (A := Sheaf.ringSheaf (pullbackRingSheaf J Φ R))
        (B := Sheaf.ringSheaf (pullbackRingSheaf J Φ R)) y z := by
  rw [sectionsFunctor_map_pullbackRingSqIso_hom, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk]

/-- The multiplier of a component of the local-unit map of the inverse image is the inverse
image of the multiplier. -/
lemma map_localUnitFactor_pullback (b : Bool) (X : Cᵒᵖ)
    (z : (Sheaf.sectionsFunctor J X).obj (Φ.obj (ringSq R))) :
    (Sheaf.sectionsFunctor J X).map (localUnitFactor (pullbackRingSheaf J Φ R) b)
        ((Sheaf.sectionsFunctor J X).map (pullbackRingSqIso J Φ R).hom z) =
      (Φ ⋙ Sheaf.sectionsFunctor J X).map (localUnitFactor R b) z := by
  refine (map_localUnitFactor (pullbackRingSheaf J Φ R) (Sheaf.sectionsFunctor J X) b _).trans
    (Eq.trans ?_ (map_localUnitFactor R (Φ ⋙ Sheaf.sectionsFunctor J X) b z).symm)
  have hfst := sectionsFunctor_map_fst_pullbackRingSqIso_hom J Φ R X z
  cases b with
  | false => simpa only [Bool.false_eq_true, ite_false] using hfst
  | true =>
      simp only [ite_true, ringNegObj_pullback, ringOneObj_pullback]
      rw [hfst]
      exact ringAddObj_pullback J Φ R X _ _

/-- **The inverse image of the local-unit map.** Each component of the local-unit map of an
inverse-image sheaf of rings is, under the product comparison of `Φ`, the inverse image of the
corresponding component of the local-unit map of the original. -/
lemma map_localUnitBranch_pullback (b : Bool) :
    Φ.map (localUnitBranch R b) ≫ (pullbackRingSqIso J Φ R).hom =
      (pullbackRingSqIso J Φ R).hom ≫ localUnitBranch (pullbackRingSheaf J Φ R) b := by
  refine Sheaf.hom_ext_sections fun X z ↦ ?_
  rw [Functor.map_comp_apply, Functor.map_comp_apply, sectionsFunctor_map_map,
    map_localUnitBranch R (Φ ⋙ Sheaf.sectionsFunctor J X) b z,
    sectionsFunctor_map_pullbackRingSqIso_hom_prodObjMk,
    map_localUnitBranch (pullbackRingSheaf J Φ R) (Sheaf.sectionsFunctor J X) b]
  refine congrArg₂ (Functor.prodObjMk (P := Sheaf.sectionsFunctor J X)
      (A := Sheaf.ringSheaf (pullbackRingSheaf J Φ R))
      (B := Sheaf.ringSheaf (pullbackRingSheaf J Φ R)))
    (sectionsFunctor_map_fst_pullbackRingSqIso_hom J Φ R X z).symm ?_
  exact ((ringMulObj_pullback J Φ R X _ _).trans
    (congrArg₂ (Sheaf.ringMulObj R (Φ ⋙ Sheaf.sectionsFunctor J X))
      (sectionsFunctor_map_snd_pullbackRingSqIso_hom J Φ R X z)
      (map_localUnitFactor_pullback J Φ R b X z))).symm

/-- Joint epimorphy of the two components of the local-unit map passes to an inverse image: a
left adjoint carries a jointly epimorphic pair to a jointly epimorphic pair, and the local-unit
map of the inverse image is the inverse image of the local-unit map. -/
lemma jointlyEpi_localUnitBranch_pullback
    {Ψ : Sheaf J (Type w) ⥤ Sheaf K (Type w')} (adj : Φ ⊣ Ψ)
    (h : JointlyEpi (localUnitBranch R false) (localUnitBranch R true)) :
    JointlyEpi (localUnitBranch (pullbackRingSheaf J Φ R) false)
      (localUnitBranch (pullbackRingSheaf J Φ R) true) :=
  (h.map adj).conj (pullbackRingSqIso J Φ R)
    (map_localUnitBranch_pullback J Φ R false) (map_localUnitBranch_pullback J Φ R true)

end Pullback

/-! ### The local-unit condition of a sheaf of commutative rings passes to an inverse image -/

section CommRing

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type v} [Category.{v} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type v)))
  (O : Sheaf K CommRingCat.{v})

/-- **Stacks 04ES, condition (3), under an inverse image.** -/
theorem condition3_inverseImage (h : Stacks.Sheaves.LocallyRingedSite.Condition3 O) :
    Stacks.Sheaves.LocallyRingedSite.Condition3 ((inverseImageCommRingFunctor f).obj O) := by
  have := f.preservesFiniteLimits
  refine (jointlyEpi_localUnitBranch_iff_condition3
    ((inverseImageCommRingFunctor f).obj O)).1 ?_
  exact jointlyEpi_localUnitBranch_pullback J f.inverseImage
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O) f.adj
    ((jointlyEpi_localUnitBranch_iff_condition3 O).2 h)

/-- **Stacks 04ES, condition (1), under an inverse image.** Every section of the inverse image
of a sheaf of commutative rings is locally either a unit or has unit complement, as soon as the
same holds for the original. -/
theorem locallyEitherUnit_inverseImage
    (h : AlgebraicGeometry.RingedSite.LocallyEitherUnit O) :
    AlgebraicGeometry.RingedSite.LocallyEitherUnit
      ((inverseImageCommRingFunctor f).obj O) :=
  (Stacks.Sheaves.LocallyRingedSite.condition1_iff_condition3 _).2
    (condition3_inverseImage f O ((Stacks.Sheaves.LocallyRingedSite.condition1_iff_condition3 O).1
      h))

end CommRing

end Stacks.Sheaves.LocalRingedness

end
