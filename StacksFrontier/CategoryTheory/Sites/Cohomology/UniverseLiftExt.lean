module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftSmallSite
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Sheaf cohomology across a universe lift of the coefficients

`CategoryTheory.Sheaf.H` is an `Ext`-group *in the category* `Sheaf J AddCommGrpCat.{t}`, so
raising the coefficient universe is not a transport along an equivalence: the universe lift on
abelian groups is fully faithful but not essentially surjective.  What does carry an `Ext`-group
across it is Mathlib's `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`,
which asks for an exact fully faithful functor preserving injective objects out of a category
with enough injectives.  All four are available for
`CategoryTheory.sheafCompose J AddCommGrpCat.uliftFunctor` once the site has a small dense
subsite; see `StacksFrontier/CategoryTheory/Sites/UniverseLiftSmallSite.lean`.

The remaining step is that the comparison is an `Ext` out of the *constant* sheaf on `ULift ℤ`,
and the object at the larger universe has to be recognised as the lift of the object at the
smaller one.  That is `Stacks.Sheaves.UniverseLift.constantSheafUliftIso`.

## Main results

* `Stacks.Sheaves.UniverseLift.subsingleton_H_uliftFunctor_of_subsingleton_H`: if the
  cohomology of an abelian sheaf vanishes in degree `n`, so does the cohomology of its
  coefficient-universe lift.
* `Stacks.Sheaves.UniverseLift.subsingleton_H_of_subsingleton_H_uliftFunctor`: the converse,
  which the same bijection gives.

## Implementation notes

The two `Ext` universes are unrelated, and so are the two coefficient universes beyond the
`max` that the lift itself forces; `CategoryTheory.Functor.mapExtAddHom` is already stated with
independent `Ext` universes on its two sides.

The exactness of the lift is supplied by `have` rather than by instance search: the three facts
`Additive`, `PreservesFiniteLimits` and `PreservesFiniteColimits` are not instances for
`CategoryTheory.sheafCompose`, so without them the *statement* of
`CategoryTheory.Functor.mapExtAddHom` does not elaborate.  They are therefore established inside
the proofs, and the statements below mention only `CategoryTheory.Sheaf.H`.

This file imports `StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/NoetherianSpaces.lean` for
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source`, which is where that
geometry-free transport of `Ext`-vanishing along an isomorphism of the source is proved.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe a b w z u v

namespace Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{a}] [HasSheafify J AddCommGrpCat.{max a b}]
  [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{b, a}]
  [(sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}).PreservesInjectiveObjects]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{a})]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{a})]
  [HasExt.{z} (Sheaf J AddCommGrpCat.{max a b})]

omit [(sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}).PreservesInjectiveObjects]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{a})] [HasExt.{w} (Sheaf J AddCommGrpCat.{a})]
  [HasExt.{z} (Sheaf J AddCommGrpCat.{max a b})] in
/-- The universe lift of the coefficients is exact, in the three senses
`CategoryTheory.Functor.mapExtAddHom` requires. -/
private lemma uliftFunctor_exact :
    (sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}).Additive ∧
      PreservesFiniteLimits (sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}) ∧
      PreservesFiniteColimits (sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}) :=
  ⟨⟨by intros; rfl⟩,
    ⟨fun K _ _ ↦
      have : HasWeakSheafify J AddCommGrpCat.{max a b} := inferInstance
      SheafOfModules.preservesLimitsOfShape_sheafCompose_uliftFunctor (J := J) K⟩,
    ⟨fun K _ _ ↦ preservesColimitsOfShape_sheafCompose J _ K⟩⟩

/-- Vanishing of sheaf cohomology in degree `n` is equivalent before and after the lift: the lift
is a bijection on the `Ext`-groups out of the constant sheaf on `ULift ℤ`. -/
private lemma subsingleton_H_uliftFunctor_iff (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ) :
    Subsingleton (Sheaf.H.{w} F n) ↔ Subsingleton (Sheaf.H.{z}
      ((sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}).obj F) n) := by
  obtain ⟨hadd, hlim, hcolim⟩ := uliftFunctor_exact.{a, b} J
  have := hadd
  have := hlim
  have := hcolim
  have hbij := Functor.mapExt_bijective_of_preservesInjectiveObjects.{w, z}
    (sheafCompose J AddCommGrpCat.uliftFunctor.{b, a})
    ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ))) F n
  exact (Equiv.ofBijective _ hbij).subsingleton_congr.trans
    ⟨fun h' ↦ Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
      (constantSheafUliftIso.{a, b} J).symm n h',
    fun h' ↦ Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
      (constantSheafUliftIso.{a, b} J) n h'⟩

/-- **Vanishing of sheaf cohomology is carried along a universe lift of the coefficients.**  The
lift is exact, fully faithful and preserves injective objects, so it is a bijection on
`Ext`-groups; the source of the `Ext` computing cohomology is the constant sheaf on `ULift ℤ`,
which is the lift of the constant sheaf on `ULift ℤ` at the smaller universe. -/
theorem subsingleton_H_uliftFunctor_of_subsingleton_H
    (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ) (h : Subsingleton (Sheaf.H.{w} F n)) :
    Subsingleton (Sheaf.H.{z}
      ((sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}).obj F) n) :=
  (subsingleton_H_uliftFunctor_iff.{a, b, w, z} J F n).1 h

/-- **Vanishing of sheaf cohomology descends along a universe lift of the coefficients.**  The
same bijection on `Ext`-groups, read the other way. -/
theorem subsingleton_H_of_subsingleton_H_uliftFunctor
    (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ)
    (h : Subsingleton (Sheaf.H.{z}
      ((sheafCompose J AddCommGrpCat.uliftFunctor.{b, a}).obj F) n)) :
    Subsingleton (Sheaf.H.{w} F n) :=
  (subsingleton_H_uliftFunctor_iff.{a, b, w, z} J F n).2 h

end Stacks.Sheaves.UniverseLift

end
