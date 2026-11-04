module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Global cohomology travels across the inclusion of a dense subsite, at independent universes

Let `G : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)` and carry a terminal object of
`C` to a terminal object of `D`.  Restriction of abelian sheaves along `G` is then an equivalence
of sheaf categories which matches the two constant sheaves, so the global cohomology
`CategoryTheory.Sheaf.H` of a sheaf on `(D, K)` is the global cohomology of its restriction, and
in particular one vanishes exactly when the other does.

`Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_constantSheaf_of_isDenseSubsite` is this
statement for the *constant* coefficient sheaf; what is added here is the same transport for an
arbitrary abelian sheaf, which is what a comparison of two sites with quasi-coherent coefficients
needs.

The point of restating it rather than using
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence`, which is the
isomorphism of cohomology functors and therefore stronger, is the universes: that statement is
seated at `{C D : Type u}` with `[Category.{v} C] [Category.{v} D]`, one pair of universes for
both sites, and the comparison of the small étale site of an algebraic space with its
spaces-étale site has the two morphism universes `u` and `u + 1`.  Here the four universes of the
two sites, the coefficient universe and the two `Ext` universes are free and independent; this is
the seating of
`Stacks.Cohomology.DenseSubsiteConstant.subsingleton_H_constantSheaf_of_isDenseSubsite`, whose
proof is the one followed.

## Main results

* `Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_inverse`: the vanishing of the
  global cohomology of an abelian sheaf on the larger site gives the vanishing of the global
  cohomology of its restriction to the dense subsite.
* `Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_functor`: the vanishing of the
  global cohomology of an abelian sheaf on the dense subsite gives the vanishing of the global
  cohomology of the sheaf it corresponds to on the larger site.

## Implementation notes

The equivalence is Mathlib's `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, whose inverse is
restriction along `G`, and the identification of the two constant sheaves is Mathlib's
`CategoryTheory.equivCommuteConstant` and `CategoryTheory.equivCommuteConstant'`, both of which
need the terminal objects.  Vanishing is moved across the equivalence by
`Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence`, which crosses the two `Ext`
universes, and the two objects of the `Ext`-group are put in their intended spellings by
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source` and
`Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target`.

No Stacks tag is claimed: [Stacks, Tag 03YU] is registered on
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIso`, and this is that statement's
vanishing shadow at free universes.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 03CG](https://stacks.math.columbia.edu/tag/03CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' a v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DenseSubsiteVanishing

section DenseSubsiteInclusion

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]
  [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
  [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]

/-- Vanishing of global cohomology passes to the inverse of an equivalence of sheaf categories
which matches the constant sheaves. -/
private theorem subsingleton_sheafH_inverse_of_iso
    (E : Sheaf J AddCommGrpCat.{a} ≌ Sheaf K AddCommGrpCat.{a})
    (i : E.inverse.obj ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ))) ≅
      (constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
    (F : Sheaf K AddCommGrpCat.{a}) (q : ℕ) (h : Subsingleton (Sheaf.H.{w'} F q)) :
    Subsingleton (Sheaf.H.{w} (E.inverse.obj F) q) := by
  have : E.symm.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₀ : Subsingleton (Ext.{w'}
      ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      (E.functor.obj (E.inverse.obj F)) q) :=
    Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target (E.counitIso.app F).symm q h
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source i q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E.symm _ _ q h₀)

variable {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))

include hTC hTD in
/-- **The global cohomology of the restriction of an abelian sheaf to a dense subsite vanishes
when the global cohomology of the sheaf does.**

The `Ext` universes on the two sides are unrelated. -/
theorem subsingleton_sheafH_inverse (F : Sheaf K AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w'} F q)) :
    Subsingleton (Sheaf.H.{w}
      ((Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).inverse.obj F) q) :=
  subsingleton_sheafH_inverse_of_iso J K _
    ((equivCommuteConstant' J AddCommGrpCat.{a} K G hTC hTD).app
      (AddCommGrpCat.of (ULift.{a} ℤ))).symm F q h

include hTC hTD in
/-- **The global cohomology of the sheaf an abelian sheaf on a dense subsite corresponds to on
the larger site vanishes when its own global cohomology does.**

The `Ext` universes on the two sides are unrelated. -/
theorem subsingleton_sheafH_functor (F : Sheaf J AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w} F q)) :
    Subsingleton (Sheaf.H.{w'}
      ((Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).functor.obj F) q) :=
  subsingleton_sheafH_inverse_of_iso K J (Functor.IsDenseSubsite.sheafEquiv J K G _).symm
    ((equivCommuteConstant J AddCommGrpCat.{a} K G hTC hTD).app _) F q h

end DenseSubsiteInclusion

section SiteEquivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
  [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
  [e.inverse.IsDenseSubsite K J]
  [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
  {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (e.functor.obj TC))

/-- **Restriction along the functor of an equivalence of sites carries the constant sheaf to the
constant sheaf.**

Both sides are left adjoint to sections over the terminal object `TC`: the composite because its
right adjoint is restriction followed by sections over `e.functor.obj TC`, which is sections over
`e.inverse.obj (e.functor.obj TC)` on the nose and so is sections over `TC` up to the unit of the
equivalence; the constant sheaf by definition. -/
def constantSheafCongrInverseIso :
    constantSheaf K AddCommGrpCat.{a} ⋙ (e.sheafCongr J K AddCommGrpCat.{a}).inverse ≅
      constantSheaf J AddCommGrpCat.{a} :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight
      ((constantSheafAdj K AddCommGrpCat.{a} hTD).comp
        (e.sheafCongr J K AddCommGrpCat.{a}).symm.toAdjunction)
      ((sheafSections J AddCommGrpCat.{a}).mapIso ((e.unitIso.app TC).op)))
    (constantSheafAdj J AddCommGrpCat.{a} hTC)

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]

omit [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J] in
include hTC hTD in
/-- **The global cohomology of the restriction of an abelian sheaf along an equivalence of sites
vanishes when the global cohomology of the sheaf does.**

This is `Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_sheafH_inverse` for an equivalence
of sites rather than a dense subsite inclusion.  The two are not interchangeable: the equivalence
of sheaf categories used there is the one built from the right Kan extension along the inclusion,
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, which asks for limits of the shape of its
comma categories in the coefficients; for an equivalence of sites no Kan extension is needed and
`CategoryTheory.Equivalence.sheafCongr` asks for nothing, which is what coefficients smaller than
the morphisms of the sites require.

The `Ext` universes on the two sides are unrelated. -/
theorem subsingleton_sheafH_sheafCongr_inverse (F : Sheaf K AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w'} F q)) :
    Subsingleton (Sheaf.H.{w}
      ((e.sheafCongr J K AddCommGrpCat.{a}).inverse.obj F) q) :=
  subsingleton_sheafH_inverse_of_iso J K _
    ((constantSheafCongrInverseIso J K e hTC hTD).app (AddCommGrpCat.of (ULift.{a} ℤ))) F q h

end SiteEquivalence

end Stacks.Cohomology.DenseSubsiteVanishing

end
