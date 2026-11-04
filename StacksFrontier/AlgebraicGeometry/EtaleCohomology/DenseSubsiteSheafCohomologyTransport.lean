module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport

/-!
# Transport of the vanishing of the cohomology of an arbitrary abelian sheaf between sites

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport` transports the
vanishing of sheaf cohomology across a dense subsite for a *constant* sheaf.  Nothing in that
argument uses constancy of the coefficients: the equivalence of sheaf categories of a dense
subsite carries one sheaf to another, and the only object that has to be recognised on both
sides is the constant sheaf on `ULift ℤ`, which is the first argument of the `Ext`-group that
`CategoryTheory.Sheaf.H` abbreviates.

This file therefore states the same transport for an arbitrary abelian sheaf, which is the form
a consumer with non-constant coefficients needs — for instance the first cohomology of an
internal hom on the small étale site of an affine scheme, which is what
[Stacks Project, Tag 061J] consumes through the hypothesis `h03DW` of
`AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_of_isLocallyProjective`.

## Main results

* `Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_of_isDenseSubsite` and
  `Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_of_isDenseSubsite'`: the transport, in
  both directions, for an arbitrary abelian sheaf.  The `Ext` universes on the two sides are
  unrelated.
* `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_boundedSmallEtale_of_smallEtale_sheaf`
  and its converse: the transport between the size-bounded small étale site of
  [Stacks Project, Tag 021B] cut out of a big étale site and Mathlib's
  `AlgebraicGeometry.Scheme.Etale`, for an arbitrary abelian sheaf with coefficients in the
  successor of the scheme universe.

## Implementation notes

`CategoryTheory.Sheaf.H` is an abbreviation for an `Ext`-group whose first argument is the
constant sheaf on `ULift ℤ`, so the hypothesis and the conclusion are `Ext`-groups on the nose
and the two steps of the proof are
`Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence`, which crosses the equivalence and
the two `Ext` universes at once, and
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source`, which moves the constant sheaf on
`ULift ℤ` to the spelling the other site gives it.  No step touches the sheaf whose cohomology
is being transported, which is why constancy was never needed.

## References

* [Stacks Project, Tag 061J](https://stacks.math.columbia.edu/tag/061J)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe w w' v₁ u₁ v₂ u₂ a u

namespace Stacks.Cohomology.DenseSubsiteConstant

/-- **The cohomology of an abelian sheaf does not change on a dense subsite.**  If `G : C ⥤ D`
exhibits `(C, J)` as a dense subsite of `(D, K)` and carries the terminal object `TC` of `C` to
a terminal object of `D`, then the vanishing on `(D, K)` of the cohomology of the sheaf
corresponding to `F` under the equivalence of sheaf categories gives the vanishing on `(C, J)`
of the cohomology of `F`.

This is `Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_constantSheaf_of_isDenseSubsite`
with the constancy of the coefficients dropped; the proof never looked at them.

The `Ext` universes on the two sides are unrelated. -/
public theorem subsingleton_H_of_isDenseSubsite
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [G.IsDenseSubsite J K]
    [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
    [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]
    {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))
    (F : Sheaf J AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w'}
      ((Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).functor.obj F) q)) :
    Subsingleton (Sheaf.H.{w} F q) := by
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : E.symm.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((equivCommuteConstant' J AddCommGrpCat.{a} K G hTC hTD).app
      (AddCommGrpCat.of (ULift.{a} ℤ))).symm q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E.symm
      ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ))) F q h)

/-- **The cohomology of an abelian sheaf does not change on a dense subsite**, read from the
subsite to the larger site: the vanishing on `(C, J)` of the cohomology of the sheaf
corresponding to `F` under the equivalence of sheaf categories gives the vanishing on `(D, K)`
of the cohomology of `F`.

The `Ext` universes on the two sides are unrelated. -/
public theorem subsingleton_H_of_isDenseSubsite'
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [G.IsDenseSubsite J K]
    [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
    [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]
    {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))
    (F : Sheaf K AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w}
      ((Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).inverse.obj F) q)) :
    Subsingleton (Sheaf.H.{w'} F q) := by
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((equivCommuteConstant J AddCommGrpCat.{a} K G hTC hTD).app
      (AddCommGrpCat.of (ULift.{a} ℤ))) q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E
      ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ))) F q h)

end Stacks.Cohomology.DenseSubsiteConstant

namespace Stacks.EtaleCohomology.ConstantTransport

open Stacks.Cohomology.DenseSubsiteConstant

variable (B : BigEtaleSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y)

/-- **The vanishing of the cohomology of an abelian sheaf passes from Mathlib's small étale site
to the size-bounded one**, for an arbitrary sheaf and not only a constant one. -/
public theorem subsingleton_H_boundedSmallEtale_of_smallEtale_sheaf
    [HasExt.{w} (Sheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1}
      ((Functor.IsDenseSubsite.sheafEquiv (SmallEtale.topology B Y hY) Y.smallEtaleTopology
        (SmallEtale.toEtaleSite B Y hY) AddCommGrpCat.{u + 1}).functor.obj F) q)) :
    Subsingleton (Sheaf.H.{w} F q) :=
  have := hasLimitsOfShape_structuredArrow_toEtaleSite_op B Y hY
  subsingleton_H_of_isDenseSubsite _ _ (SmallEtale.toEtaleSite B Y hY)
    (SmallEtale.finalIsTerminal B Y hY) (isTerminal_toEtaleSite_obj_final B Y hY) F q h

/-- **The vanishing of the cohomology of an abelian sheaf passes from the size-bounded small
étale site to Mathlib's**, for an arbitrary sheaf and not only a constant one. -/
public theorem subsingleton_H_smallEtale_of_boundedSmallEtale_sheaf
    [HasExt.{w} (Sheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1})]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w}
      ((Functor.IsDenseSubsite.sheafEquiv (SmallEtale.topology B Y hY) Y.smallEtaleTopology
        (SmallEtale.toEtaleSite B Y hY) AddCommGrpCat.{u + 1}).inverse.obj F) q)) :
    Subsingleton (Sheaf.H.{u + 1} F q) :=
  have := hasLimitsOfShape_structuredArrow_toEtaleSite_op B Y hY
  subsingleton_H_of_isDenseSubsite' _ _ (SmallEtale.toEtaleSite B Y hY)
    (SmallEtale.finalIsTerminal B Y hY) (isTerminal_toEtaleSite_obj_final B Y hY) F q h

end Stacks.EtaleCohomology.ConstantTransport

end
