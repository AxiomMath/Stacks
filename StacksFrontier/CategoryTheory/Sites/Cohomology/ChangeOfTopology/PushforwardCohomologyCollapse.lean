module

public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall

/-!
# Cohomology over an object is unchanged by restriction along a functor of sites

Let `u : C ⥤ D` be a continuous functor of sites and let `ε_* = u.sheafPushforwardContinuous` be
restriction of abelian sheaves along it. Sections of a restricted sheaf over `T : C` are sections
of the original over `u T`, by `Stacks.Cohomology.BiggerSite`'s
`sheafPushforwardContinuousCompSheafSectionsIso`, which is the identity; so the two
right-derived-sections functors differ only by the order in which `ε_*` and sections are derived.
The edge morphism of the pair measures that difference, and it is invertible in degree `i` as
soon as the higher direct images `R^q ε_* F` vanish for `1 ≤ q ≤ i`. Combining this with the
identification of right-derived sections with sheaf cohomology gives

  `H^i(T, ε_* F) ≅ H^i(u T, F)`,

cohomology over `T` on the smaller site agreeing with cohomology over `u T` on the larger one.

## Main definitions

All in the namespace `Stacks.Cohomology.BiggerSite`.

* `rightDerivedSectionsCollapseIso`: the collapse at the level of right-derived sections,
  `R^i Γ(T, ε_* F) ≅ R^i Γ(u T, F)`.
* `sheafCohomologyPushforwardIso`: the same read as sheaf cohomology,
  `H^i(T, ε_* F) ≅ H^i(u T, F)`.
* `sheafCohomologyPushforwardIsoOfEssentiallySmall`: the same with the `Ext`-universe and
  enough-injectives hypotheses discharged on both sites, which is the form a big `τ`-site
  consumes.

## Implementation notes

The vanishing of the higher direct images is an explicit hypothesis rather than something proved
here: it is the input the Čech machinery supplies for the specific sheaf of interest, and it is
false for a general abelian sheaf, so no form of this statement can discharge it. The hypothesis
is stated in the range `1 ≤ q ≤ i` rather than for all positive `q`, which is what
`Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app` needs and is strictly weaker than the
acyclicity `Stacks.RightDerivedComp.objIso` would require.

Additivity, left exactness and preservation of injective objects by `ε_*` are instance
hypotheses. All three hold in the situations of interest and none is proved here: the first two
are `CategoryTheory.Functor.additive_sheafPushforwardContinuous` and
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`, and the third is
`Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous`, which holds
when the smaller site has fibre products and equalizers that `u` preserves, so that the left
adjoint of `ε_*` is exact. Leaving them as hypotheses keeps this module independent of how a
consumer establishes them.

The two sites may have objects in different universes — which is the case of interest, a small
site mapping into a big one whose objects live one universe higher — but their morphisms share a
universe, because the coefficients of both cohomology theories are the abelian groups of that
universe.

The comparison of cohomology on a small site with cohomology on a big site, [Stacks, Tag 03P2],
needs the vanishing of the higher direct images as well; that vanishing is not proved here, so the
declarations below are the comparison granted it.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.BiggerSite

universe v u u'

noncomputable section

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).Additive]
  [PreservesFiniteLimits (u.sheafPushforwardContinuous AddCommGrpCat.{v} J K)]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).PreservesInjectiveObjects]

section Collapse

variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{v})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{v})]

/-- **The collapse of the derived functors of sections along a restriction.** For an abelian
sheaf `F` on the larger site whose higher direct images vanish in the degrees `1, …, i`, the
`i`-th right derived functor of sections over `T` applied to the restriction of `F` agrees with
the `i`-th right derived functor of sections over `u T` applied to `F`.

The comparison is the edge morphism of the pair `(ε_*, Γ(T, −))`, invertible in this range by
`Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app`, read through the identity
`sheafPushforwardContinuousCompSheafSectionsIso`. -/
def rightDerivedSectionsCollapseIso (F : Sheaf K AddCommGrpCat.{v}) (T : C) (i : ℕ)
    (hF : ∀ q, 1 ≤ q → q ≤ i →
      IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).rightDerived q).obj F)) :
    (((sheafSections J AddCommGrpCat.{v}).obj (op T)).rightDerived i).obj
        ((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj F) ≅
      (((sheafSections K AddCommGrpCat.{v}).obj (op (u.obj T))).rightDerived i).obj F :=
  RightDerivedEdgeIso.edgeAppIso (u.sheafPushforwardContinuous AddCommGrpCat.{v} J K)
      ((sheafSections J AddCommGrpCat.{v}).obj (op T)) F i hF ≪≫
    (CategoryTheory.Functor.rightDerivedIsoOfNatIso
      (sheafPushforwardContinuousCompSheafSectionsIso J K u AddCommGrpCat.{v} T) i).app F

end Collapse

section Cohomology

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{v})]

/-- **Cohomology over an object is unchanged by restriction along a functor of sites**, in the
degrees in which the higher direct images vanish: `H^i(T, ε_* F) ≅ H^i(u T, F)`.

This is `rightDerivedSectionsCollapseIso` read on both sides through
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections`, the identification
of sheaf cohomology over an object with right-derived sections. -/
def sheafCohomologyPushforwardIso (F : Sheaf K AddCommGrpCat.{v}) (T : C) (i : ℕ)
    (hF : ∀ q, 1 ≤ q → q ≤ i →
      IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).rightDerived q).obj F)) :
    Sheaf.H' ((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj F) i T ≅
      Sheaf.H' F i (u.obj T) :=
  FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{v} J
      ((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj F) i T ≪≫
    rightDerivedSectionsCollapseIso J K u F T i hF ≪≫
      (FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{v} K F i (u.obj T)).symm

end Cohomology

section EssentiallySmall

variable [EssentiallySmall.{v} C] [EssentiallySmall.{v} D]

attribute [local instance] FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **Cohomology over an object is unchanged by restriction along a functor of essentially small
sites**, in the degrees in which the higher direct images vanish. This is
`sheafCohomologyPushforwardIso` with the `Ext`-universe and enough-injectives hypotheses
discharged on both sites; it applies in particular when the larger site is a big `τ`-site of
schemes, whose objects live one universe above its morphisms. -/
def sheafCohomologyPushforwardIsoOfEssentiallySmall (F : Sheaf K AddCommGrpCat.{v}) (T : C)
    (i : ℕ) (hF : ∀ q, 1 ≤ q → q ≤ i →
      IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).rightDerived q).obj F)) :
    Sheaf.H' ((u.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj F) i T ≅
      Sheaf.H' F i (u.obj T) :=
  sheafCohomologyPushforwardIso J K u F T i hF

end EssentiallySmall

end

end Stacks.Cohomology.BiggerSite

end
