module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.ObjectAcyclicity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.GlobalSectionsAtTerminal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModuleRestrict
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.AbelianSheavesAsConstantModules
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedAlongEquivalence
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of a complex supported at closed points is detected by its hypercohomology

Let `K` be a separably closed field, `X` a scheme of finite type over `K` and `Q` an object of the
**unbounded** derived category `D(X_étale)` of abelian sheaves on the small étale site of `X`.
Assume the stalk `Q_x̄` is nonzero only at closed points `x` of `X`. Then

`Q = 0 ⟺ H^i(X, Q) = 0 for all i`.

This is [Stacks, Tag 0F1G]. The implication from left to right is formal. The reverse implication
is the content, and the source proves it from two inputs:

* [Stacks, Tag 0F1F]: an abelian sheaf on `X_étale` whose support consists of closed points has
  no higher cohomology and is **globally generated**; and
* [Stacks, Tag 0BKZ]: if the cohomology sheaves of an object of the unbounded derived category
  have no higher cohomology over the members of a family covering the site, then over each such
  member its degree-`q` hypercohomology is the group of sections of its degree-`q` cohomology
  sheaf.

With both of those, the argument is three lines. `Q` is zero exactly when every cohomology sheaf
`H^q(Q)` is zero (`DerivedCategory.isZero_iff_forall_isZero_homology`); the stalk hypothesis says
exactly that each `H^q(Q)` is supported at closed points, so Tag 0F1F makes it acyclic over every
quasi-compact object of `X_étale` — and those cover — so Tag 0BKZ identifies `H^q(X, Q)` with
`Γ(X, H^q(Q))`; and a globally generated sheaf with no global sections is zero, which is the
second clause of Tag 0F1F.

## Reading Tag 0BKZ on this site

Tag 0BKZ is proved in this repository for sheaves of **modules on a ringed site**
(`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`; no
boundedness is assumed there), and it is read over an **object** of the site, whereas the
hypercohomology of this file is the `CategoryTheory.Sheaf.Γ` one. Three bridges close the gap,
and they are what the bulk of this file is.

* Abelian sheaves on any site *are* the sheaves of modules over the constant sheaf of rings `ℤ`
  (`Stacks.Cohomology.ZModSheaf.toSheaf_isEquivalence`), with the group of sections over an
  object matching the module of sections (`Stacks.Cohomology.ZModSheaf.sectionsIso`). The
  unbounded derived functor of sections transports across that equivalence by
  `Stacks.Injectives.derivedPrecompObjIso`, and the forgetful functor from modules to abelian
  groups comes out of it by
  `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`, being exact.
* The final object `X / X` of `AlgebraicGeometry.SmallEtale` is terminal, so global sections are
  sections over it and the two unbounded derived functors — hence the two hypercohomologies —
  agree in every degree.
* The quasi-compact quasi-separated objects cover the small étale site
  (`AlgebraicGeometry.SmallEtale.hasEnoughObjects_isQCQSEtaleObject`) and Tag 0F1F makes a sheaf
  supported at closed points acyclic over each of them
  (`AlgebraicGeometry.isZero_rightDerived_sections_of_supportSheaf_subset_closedPoints`), which
  is the acyclicity Tag 0BKZ consumes.

## Main definitions

* `AlgebraicGeometry.smallEtaleDerivedSectionsAbAtFinal`: unbounded derived sections
  `RΓ(X / X, -)` over the final object of the small étale site.
* `AlgebraicGeometry.smallEtaleIntegerRingSheaf` and
  `AlgebraicGeometry.smallEtaleModulesToAbelianSheaf`: the constant sheaf of rings `ℤ` on the
  small étale site and the equivalence of its sheaves of modules with abelian sheaves.
* `AlgebraicGeometry.smallEtaleFinalModuleSections` and
  `AlgebraicGeometry.smallEtaleFinalForgetToAb`: sections of such a sheaf of modules over the
  final object `X / X`, and the underlying abelian group of a module over their ring of
  scalars.

## Main results

* `AlgebraicGeometry.isZero_iff_forall_isZero_etaleHypercohomology_of_closedPointSupport`:
  **[Stacks, Tag 0F1G]**, the statement above.
* `AlgebraicGeometry.isIso_natTransΓRes_smallEtaleFinal` and
  `AlgebraicGeometry.smallEtaleΓNatIsoSectionsAtFinal`: **global sections on the small étale site
  are sections over the final object `X / X`**, through the canonical restriction map.
* `AlgebraicGeometry.smallEtaleDerivedGlobalSectionsAbNatIsoSectionsAtFinal` and
  `AlgebraicGeometry.smallEtaleHypercohomologyAbIsoSectionsAtFinal`: the same identification for
  the unbounded derived functors, and degreewise for hypercohomology.
* `AlgebraicGeometry.nonempty_hypercohomologyAbIsoΓHomology_of_supportSheaf_subset_closedPoints`:
  **Tag 0BKZ on the small étale site, for abelian sheaves and in the `Sheaf.Γ` spelling**: for
  `Q` whose cohomology sheaves are supported at closed points, the degree-`q` hypercohomology of
  `Q` is the group of global sections of its degree-`q` cohomology sheaf.

## Implementation notes

Hypercohomology is the homology of total derived global sections: `CategoryTheory.Sheaf.Γ` on
the small étale site, derived on the localization of the homotopy category of cochain complexes at
the quasi-isomorphisms. Its comparison with derived sections over the final object is stated at an
arbitrary coefficient universe, as is `AlgebraicGeometry.supportSheaf`; the tag itself is at the
coefficient universe `u + 1`, which is the one the étale cohomology of this repository is written
in (`AlgebraicGeometry.SmallEtaleAbelianSheaf`) and the only one in which
the small étale site has a zero sheaf
(`AlgebraicGeometry.isZero_of_forall_isZero_etaleStalk`).

The stalk hypothesis is stated on the cohomology sheaves rather than on `Q` itself. The two are
the same condition: the stalk functor at a geometric point is exact, so it commutes with the
cohomology of a complex, and a complex of abelian groups is zero exactly when all its cohomology
vanishes.

`Sheaf.Γ` is additive — it is a right adjoint, so it preserves binary products — which is what
makes the formal implication formal.

Several declarations of the module-theoretic section carry their universe arguments explicitly.
The categories of sheaves of modules and of `ℤ`-modules involved have an abelian, Grothendieck
abelian and enough-injectives structure that the repository supplies at a module universe of the
form `max u v r w` with `w` free, and the universe unifier cannot solve `max (u + 1) ?w = u + 1`;
pinning the instances once, as local instances, is what lets the rest elaborate.

## References

* [Stacks Project, Tag 0F1G](https://stacks.math.columbia.edu/tag/0F1G)
* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

set_option synthInstance.maxHeartbeats 200000 in
-- instance search on the category of sheaves on the small étale site needs the larger budget
/-- Global sections of abelian sheaves on the small étale site form an additive functor: it is a
right adjoint, so it preserves binary products. -/
local instance additive_Γ_smallEtaleSite
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (SmallEtale.topology B X hX) AddCommGrpCat.{w}] :
    (Sheaf.Γ (SmallEtale.topology B X hX) AddCommGrpCat.{w}).Additive :=
  have : HasBinaryProducts (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w}) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
      (sheafToPresheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w})
  Functor.additive_of_preserves_binary_products _

/-- Global sections of complexes of abelian sheaves on the small étale site, regarded in the
homotopy category. -/
public abbrev smallEtaleHomotopyGlobalSectionsAb
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (SmallEtale.topology B X hX) AddCommGrpCat.{w}] :
    HomotopyCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w})
        (ComplexShape.up ℤ) ⥤ DerivedCategory AddCommGrpCat.{w} :=
  (Sheaf.Γ (SmallEtale.topology B X hX) AddCommGrpCat.{w}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Unbounded derived global sections `RΓ(X, -)` of abelian sheaves on the small étale site of
`X`: the total right derived functor of global sections. -/
public abbrev smallEtaleDerivedGlobalSectionsAb
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor (SmallEtale.topology B X hX) AddCommGrpCat.{w}]
    [(smallEtaleHomotopyGlobalSectionsAb.{u, w} B X hX).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w}) (ComplexShape.up ℤ))] :
    DerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w}) ⥤
      DerivedCategory AddCommGrpCat.{w} :=
  (smallEtaleHomotopyGlobalSectionsAb.{u, w} B X hX).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w}) (ComplexShape.up ℤ))

/-! ### Global sections are sections over the final object `X / X` -/

section Final

variable [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor (SmallEtale.topology B X hX) AddCommGrpCat.{w}]

/-- **Global sections on the small étale site of `X` are sections over its final object
`X / X`**, through the canonical restriction map: the final object is terminal
(`AlgebraicGeometry.SmallEtale.finalIsTerminal`), and global sections are the limit of the
sections over the objects of the site, which an initial index computes. -/
public theorem isIso_natTransΓRes_smallEtaleFinal :
    IsIso (Sheaf.natTransΓRes (SmallEtale.topology B X hX) AddCommGrpCat.{w}
      (Opposite.op (SmallEtale.final B X hX))) :=
  Stacks.Cohomology.isIso_natTransΓRes_of_isTerminal _ _ (SmallEtale.finalIsTerminal B X hX)

/-- The global sections functor of the small étale site of `X` is the functor of sections over
the final object `X / X`. -/
public def smallEtaleΓNatIsoSectionsAtFinal :
    Sheaf.Γ (SmallEtale.topology B X hX) AddCommGrpCat.{w} ≅
      (sheafSections (SmallEtale.topology B X hX) AddCommGrpCat.{w}).obj
        (Opposite.op (SmallEtale.final B X hX)) :=
  Stacks.Cohomology.ΓNatIsoSectionsAtTerminal _ _ (SmallEtale.finalIsTerminal B X hX)

variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{w}]
  [(smallEtaleHomotopyGlobalSectionsAb.{u, w} B X hX).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso
      (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w}) (ComplexShape.up ℤ))]

/-- Unbounded derived sections over the final object of the small étale site exist whenever
unbounded derived global sections do: the two functors being derived are isomorphic. -/
local instance hasRightDerivedFunctor_smallEtaleSectionsAtFinal :
    ((((sheafSections (SmallEtale.topology B X hX) AddCommGrpCat.{w}).obj
          (Opposite.op (SmallEtale.final B X hX))).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w}) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.hasRightDerivedFunctor_sectionsAtTerminal_of_globalSections _ _
    (SmallEtale.finalIsTerminal B X hX)

/-- **Unbounded derived sections `RΓ(X / X, -)` over the final object of the small étale site of
`X`**: the total right derived functor of sections over that object. This is the spelling in
which the theory of derived sections over an object of a site is stated, and
`AlgebraicGeometry.smallEtaleDerivedGlobalSectionsAbNatIsoSectionsAtFinal` identifies it with
unbounded derived global sections. -/
public abbrev smallEtaleDerivedSectionsAbAtFinal :
    DerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w}) ⥤
      DerivedCategory AddCommGrpCat.{w} :=
  (((sheafSections (SmallEtale.topology B X hX) AddCommGrpCat.{w}).obj
      (Opposite.op (SmallEtale.final B X hX))).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w}) (ComplexShape.up ℤ))

/-- **Unbounded derived global sections on the small étale site of `X` are unbounded derived
sections over its final object `X / X`.** Both are right derived functors of isomorphic
functors on the homotopy category of cochain complexes, so they agree. -/
public def smallEtaleDerivedGlobalSectionsAbNatIsoSectionsAtFinal :
    smallEtaleDerivedGlobalSectionsAb.{u, w} B X hX ≅
      smallEtaleDerivedSectionsAbAtFinal.{u, w} B X hX :=
  Stacks.Cohomology.derivedGlobalSectionsNatIsoSectionsAtTerminal _ _
    (SmallEtale.finalIsTerminal B X hX)

/-- **Hypercohomology on the small étale site is hypercohomology over the final object
`X / X`**, in every degree and at every object of the unbounded derived category. This is the
form in which a statement about derived sections over an object of the site becomes a statement
about the hypercohomology of `AlgebraicGeometry.smallEtaleDerivedGlobalSectionsAb`. -/
public def smallEtaleHypercohomologyAbIsoSectionsAtFinal (q : ℤ)
    (Q : DerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w})) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{w} q).obj
        ((smallEtaleDerivedGlobalSectionsAb.{u, w} B X hX).obj Q) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{w} q).obj
        ((smallEtaleDerivedSectionsAbAtFinal.{u, w} B X hX).obj Q) :=
  Stacks.Cohomology.hypercohomologyGlobalSectionsIsoAtTerminal _ _
    (SmallEtale.finalIsTerminal B X hX) q Q

end Final

/-! ### The support of a sheaf whose stalks vanish away from the closed points -/

/-- **A sheaf whose geometric stalks vanish away from the closed points is supported at closed
points.** The support of [Stacks, Tag 04FS] is computed from the stalks of the universe-lifted
sheaf, and lifting does not change vanishing of a stalk. -/
public theorem supportSheaf_subset_closedPoints_of_forall_isZero_etaleStalk
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{w}]
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{w})
    (hF : ∀ p : GeometricPoint X, ¬ IsClosed ({p.hom default} : Set X) →
      IsZero (etaleStalk B X hX p F.obj)) :
    supportSheaf B X hX F ⊆ {x : X | IsClosed ({x} : Set X)} := by
  rintro x ⟨p, hp, hne⟩
  by_contra hx
  exact hne ((isZero_etaleStalk_ulift_iff B X hX F p).2 (hF p (hp ▸ hx)))

/-! ### Tag 0F1F: global generation kills a sheaf with no global sections -/

/-- **An abelian étale sheaf supported at closed points with no global sections is zero.** This
is the global-generation clause of [Stacks, Tag 0F1F]: the constant sheaf on the group of global
sections surjects onto the sheaf, and a constant sheaf on a zero group is zero. -/
public theorem isZero_of_isZero_Γ_of_supportSheaf_subset_closedPoints
    (K : Type u) [Field K] [IsSepClosed K] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (hF : supportSheaf B X hX F ⊆ {x : X | IsClosed ({x} : Set X)})
    (hΓ : IsZero ((Sheaf.Γ (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj F)) :
    IsZero F := by
  have hepi := (subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints
    B K ⟨X, hX⟩ f F hF).2
  have := hepi
  exact ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).map_isZero
    hΓ).of_epi ((constantSheafΓAdj (SmallEtale.topology B X hX)
      AddCommGrpCat.{u + 1}).counit.app F)

/-! ### Abelian étale sheaves as modules over the constant sheaf of rings `ℤ` -/

section Modules

/-- The constant sheaf of rings `ℤ` on the small étale site of `X`. Its sheaves of modules are
the abelian étale sheaves, which is how [Stacks, Tag 0BKZ] — proved here for sheaves of modules
on a ringed site — is read for abelian sheaves. -/
@[sga "4 IV 11.1.5" "special case"]
public abbrev smallEtaleIntegerRingSheaf :
    Sheaf (SmallEtale.topology B X hX) RingCat.{u + 1} :=
  Stacks.Cohomology.ZModSheaf.zmodRingSheaf (SmallEtale.topology B X hX) 0

/-- **Sheaves of modules over the constant sheaf of rings `ℤ` on the small étale site are the
abelian étale sheaves**: the forgetful functor, which
`Stacks.Cohomology.ZModSheaf.toSheaf_isEquivalence` makes an equivalence. -/
public abbrev smallEtaleModulesToAbelianSheaf :
    SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX) ⥤
      Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf.{u + 1} (smallEtaleIntegerRingSheaf B X hX)

/-- Sections over the final object `X / X` of the small étale site, of a sheaf of modules over
the constant sheaf of rings `ℤ`. -/
public abbrev smallEtaleFinalModuleSections :
    SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX) ⥤
      ModuleCat.{u + 1} ((smallEtaleIntegerRingSheaf B X hX).obj.obj
        (Opposite.op (SmallEtale.final B X hX))) :=
  SheafOfModules.evaluation (smallEtaleIntegerRingSheaf B X hX)
    (Opposite.op (SmallEtale.final B X hX))

/-- The underlying abelian group of a module over the sections of the constant sheaf of rings
`ℤ` over the final object `X / X`. It is exact, so it comes out of a derived functor. -/
public abbrev smallEtaleFinalForgetToAb :
    ModuleCat.{u + 1} ((smallEtaleIntegerRingSheaf B X hX).obj.obj
        (Opposite.op (SmallEtale.final B X hX))) ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (ModuleCat.{u + 1} ((smallEtaleIntegerRingSheaf B X hX).obj.obj
    (Opposite.op (SmallEtale.final B X hX)))) AddCommGrpCat.{u + 1}

/-- Sheaves of modules over the constant sheaf of rings `ℤ` on the small étale site form an
abelian category. -/
local instance abelian_smallEtaleModules :
    Abelian (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u, u + 1, u + 1}
    (smallEtaleIntegerRingSheaf B X hX)

/-- Sheaves of modules over the constant sheaf of rings `ℤ` on the small étale site form a
Grothendieck abelian category. -/
local instance isGrothendieckAbelian_smallEtaleModules :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u + 1, u + 1}
    (smallEtaleIntegerRingSheaf B X hX)

/-- Sheaves of modules over the constant sheaf of rings `ℤ` on the small étale site have enough
injectives. -/
local instance enoughInjectives_smallEtaleModules :
    EnoughInjectives (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u + 1, u + 1}
    (smallEtaleIntegerRingSheaf B X hX)

/-- The forward functor of the equivalence `smallEtaleModulesToAbelianSheaf` is additive. -/
local instance additive_smallEtaleModulesToAbelianSheaf_functor :
    (smallEtaleModulesToAbelianSheaf B X hX).asEquivalence.functor.Additive :=
  inferInstanceAs ((smallEtaleModulesToAbelianSheaf B X hX).Additive)

/-- The forward functor of the equivalence `smallEtaleModulesToAbelianSheaf` preserves finite
limits. -/
local instance preservesFiniteLimits_smallEtaleModulesToAbelianSheaf_functor :
    PreservesFiniteLimits (smallEtaleModulesToAbelianSheaf B X hX).asEquivalence.functor :=
  inferInstanceAs (PreservesFiniteLimits (smallEtaleModulesToAbelianSheaf B X hX))

/-- The forward functor of the equivalence `smallEtaleModulesToAbelianSheaf` preserves finite
colimits. -/
local instance preservesFiniteColimits_smallEtaleModulesToAbelianSheaf_functor :
    PreservesFiniteColimits (smallEtaleModulesToAbelianSheaf B X hX).asEquivalence.functor :=
  inferInstanceAs (PreservesFiniteColimits (smallEtaleModulesToAbelianSheaf B X hX))

/-- The functor `smallEtaleModulesToAbelianSheaf` preserves injective objects. -/
local instance preservesInjectiveObjects_smallEtaleModulesToAbelianSheaf :
    (smallEtaleModulesToAbelianSheaf B X hX).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (smallEtaleModulesToAbelianSheaf B X hX).asEquivalence.symm.toAdjunction

/-- The functor induced by `smallEtaleModulesToAbelianSheaf` on derived categories is an
equivalence. -/
local instance isEquivalence_mapDerivedCategory_smallEtaleModulesToAbelianSheaf :
    (smallEtaleModulesToAbelianSheaf B X hX).mapDerivedCategory.IsEquivalence :=
  StacksDraft.DerivedRingIso.isEquivalence_mapDerivedCategory
    (smallEtaleModulesToAbelianSheaf B X hX)
    (smallEtaleModulesToAbelianSheaf B X hX).asEquivalence.inverse
    (smallEtaleModulesToAbelianSheaf B X hX).asEquivalence.unitIso
    (smallEtaleModulesToAbelianSheaf B X hX).asEquivalence.counitIso

/-- **The acyclicity over objects that Tag 0BKZ consumes, on the module side.** A sheaf of
modules over the constant sheaf of rings `ℤ` whose underlying abelian sheaf is supported at
closed points has no higher cohomology over a quasi-compact object of the small étale site.

Cohomology over an object is unchanged by forgetting the module structure, which is exact
(`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`), and by the equivalence with abelian
sheaves, which preserves injectives
(`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`); on the abelian side it is
`AlgebraicGeometry.isZero_rightDerived_sections_of_supportSheaf_subset_closedPoints`. -/
public theorem isZero_rightDerived_evaluation_of_supportSheaf_subset_closedPoints
    (K : Type u) [Field K] [IsSepClosed K] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (M : SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX))
    (hM : supportSheaf B X hX ((smallEtaleModulesToAbelianSheaf B X hX).obj M) ⊆
      {x : X | IsClosed ({x} : Set X)})
    (V : SmallEtale B X hX) (hV : CompactSpace V.obj.left.1) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation (smallEtaleIntegerRingSheaf B X hX)
      (Opposite.op V)).rightDerived p).obj M) := by
  have hstar : IsZero ((((sheafSections (SmallEtale.topology B X hX)
      AddCommGrpCat.{u + 1}).obj (Opposite.op V)).rightDerived p).obj
        ((smallEtaleModulesToAbelianSheaf B X hX).obj M)) :=
    isZero_rightDerived_sections_of_supportSheaf_subset_closedPoints B X hX V K f
      ((smallEtaleModulesToAbelianSheaf B X hX).obj M) hM hV p hp
  have h1 : IsZero (((((smallEtaleModulesToAbelianSheaf B X hX) ⋙
      (sheafSections (SmallEtale.topology B X hX)
        AddCommGrpCat.{u + 1}).obj (Opposite.op V)).rightDerived p)).obj M) :=
    hstar.of_iso ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (smallEtaleModulesToAbelianSheaf B X hX)
      ((sheafSections (SmallEtale.topology B X hX)
        AddCommGrpCat.{u + 1}).obj (Opposite.op V)) p).app M)
  have h2 : IsZero ((forget₂ (ModuleCat.{u + 1}
      ((smallEtaleIntegerRingSheaf B X hX).obj.obj (Opposite.op V)))
        AddCommGrpCat.{u + 1}).obj
      (((SheafOfModules.evaluation (smallEtaleIntegerRingSheaf B X hX)
        (Opposite.op V)).rightDerived p).obj M)) :=
    h1.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (SheafOfModules.evaluation (smallEtaleIntegerRingSheaf B X hX) (Opposite.op V))
      (forget₂ (ModuleCat.{u + 1}
        ((smallEtaleIntegerRingSheaf B X hX).obj.obj (Opposite.op V))) AddCommGrpCat.{u + 1}) _
      (Stacks.Cohomology.ZModSheaf.sectionsIso.{u + 1, u + 1}
        (SmallEtale.topology B X hX) 0 (Opposite.op V)) p).app M)
  rw [AddCommGrpCat.isZero_iff_subsingleton] at h2
  rw [ModuleCat.isZero_iff_subsingleton]
  exact h2

/-- Sections over the final object of the small étale site, read through the equivalence with
sheaves of modules and then degreewise on complexes: this is the comparison whose two unbounded
derivations the identification of the two hypercohomologies is taken between. -/
public def smallEtaleSectionsAtFinalModuleSourceIso :
    (((smallEtaleModulesToAbelianSheaf B X hX) ⋙
        (sheafSections (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj
          (Opposite.op (SmallEtale.final B X hX))).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) ≅
      (((smallEtaleFinalModuleSections B X hX) ⋙
          smallEtaleFinalForgetToAb B X hX).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) :=
  Functor.isoWhiskerRight (Stacks.Cohomology.mapHomotopyCategoryNatIso
    (Stacks.Cohomology.ZModSheaf.sectionsIso.{u + 1, u + 1} (SmallEtale.topology B X hX) 0
      (Opposite.op (SmallEtale.final B X hX))).symm
    (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- The unbounded derived functor of sections over the final object, computed through the
equivalence with sheaves of modules, is the unbounded derived functor of the underlying abelian
groups of the sections of a sheaf of modules: the two functors on the homotopy category are
isomorphic. -/
public def smallEtaleDerivedSectionsAtFinalModuleIso :
    (((smallEtaleModulesToAbelianSheaf B X hX) ⋙
        (sheafSections (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj
          (Opposite.op (SmallEtale.final B X hX))).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX))
          (ComplexShape.up ℤ)) ≅
      (((smallEtaleFinalModuleSections B X hX) ⋙
          smallEtaleFinalForgetToAb B X hX).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX))
            (ComplexShape.up ℤ)) :=
  Functor.rightDerivedNatIso _ _
    (Functor.totalRightDerivedUnit _ DerivedCategory.Qh _)
    (Functor.totalRightDerivedUnit _ DerivedCategory.Qh _)
    (HomotopyCategory.quasiIso (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX))
      (ComplexShape.up ℤ))
    (smallEtaleSectionsAtFinalModuleSourceIso B X hX)

/-- **Forgetting the module structure comes out of the unbounded derived functor of sections over
the final object**, the forgetful functor from modules to abelian groups being exact. -/
public def smallEtaleDerivedSectionsAtFinalForgetIso :
    (((smallEtaleFinalModuleSections B X hX) ⋙
          smallEtaleFinalForgetToAb B X hX).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX))
            (ComplexShape.up ℤ)) ≅
      (((smallEtaleFinalModuleSections B X hX).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX))
            (ComplexShape.up ℤ))) ⋙
        (smallEtaleFinalForgetToAb B X hX).mapDerivedCategory :=
  (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
    (smallEtaleFinalModuleSections B X hX) (smallEtaleFinalForgetToAb B X hX)).symm

/-- **[Stacks, Tag 0BKZ] on the small étale site, for abelian sheaves and in the `Sheaf.Γ`
spelling.** Let `K` be a separably closed field, `X` a scheme of finite type over `K` and `Q` an
object of the unbounded derived category of abelian sheaves on the small étale site of `X` whose
cohomology sheaves are supported at closed points. Then the degree-`q` hypercohomology of `Q` is
the group of global sections of its degree-`q` cohomology sheaf.

The cohomology sheaves are acyclic over the quasi-compact quasi-separated objects by
[Stacks, Tag 0F1F] and those cover the site, so Tag 0BKZ applies — on the module side, through
the equivalence of abelian sheaves with sheaves of modules over the constant sheaf of rings `ℤ`
— over the final object `X / X`, where sections are global sections. -/
public theorem nonempty_hypercohomologyAbIsoΓHomology_of_supportSheaf_subset_closedPoints
    (K : Type u) [Field K] [IsSepClosed K] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : DerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}))
    (hQ : ∀ m : ℤ, supportSheaf B X hX ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) m).obj Q) ⊆
        {x : X | IsClosed ({x} : Set X)})
    (q : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((smallEtaleDerivedGlobalSectionsAb.{u, u + 1} B X hX).obj Q) ≅
      (Sheaf.Γ (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) q).obj Q)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : QuasiSeparatedSpace X := IsLocallyNoetherian.quasiSeparatedSpace
  set P := (smallEtaleModulesToAbelianSheaf B X hX).mapDerivedCategory.objPreimage Q with hP
  have heq : (smallEtaleModulesToAbelianSheaf B X hX).mapDerivedCategory.obj P ≅ Q :=
    (smallEtaleModulesToAbelianSheaf B X hX).mapDerivedCategory.objObjPreimageIso Q
  have hsupp : ∀ m : ℤ, supportSheaf B X hX ((smallEtaleModulesToAbelianSheaf B X hX).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX)) m).obj P)) ⊆
        {x : X | IsClosed ({x} : Set X)} := fun m =>
    subset_trans (supportSheaf_subset_of_mono B X hX _ _
      (((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (smallEtaleModulesToAbelianSheaf B X hX) m).app P).symm.hom ≫
          ((DerivedCategory.homologyFunctor
            (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) m).mapIso heq).hom))
      (hQ m)
  have hvan : ∀ V : SmallEtale B X hX, IsQCQSEtaleObject B ⟨X, hX⟩ V → ∀ p : ℕ, 0 < p →
      ∀ m : ℤ, IsZero (((SheafOfModules.evaluation (smallEtaleIntegerRingSheaf B X hX)
        (Opposite.op V)).rightDerived p).obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u + 1} (smallEtaleIntegerRingSheaf B X hX)) m).obj P)) :=
    fun V hV p hp m =>
      isZero_rightDerived_evaluation_of_supportSheaf_subset_closedPoints B X hX K f _
        (hsupp m) V hV.1 p hp
  have hU : IsQCQSEtaleObject B ⟨X, hX⟩ (SmallEtale.final B X hX) :=
    ⟨inferInstanceAs (CompactSpace X), inferInstanceAs (QuasiSeparatedSpace X)⟩
  have : IsIso ((Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge.{u + 1, u, u + 1,
      u + 1, u + 1} (smallEtaleIntegerRingSheaf B X hX) (SmallEtale.final B X hX) q).app P) :=
    Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover.{u + 1,
      u, u + 1, u + 1, u + 1} (smallEtaleIntegerRingSheaf B X hX) (SmallEtale.final B X hX) P
      (IsQCQSEtaleObject B ⟨X, hX⟩)
      (SmallEtale.hasEnoughObjects_isQCQSEtaleObject B ⟨X, hX⟩) hvan hU q
  refine ⟨?_⟩
  refine smallEtaleHypercohomologyAbIsoSectionsAtFinal.{u, u + 1} B X hX q Q ≪≫ ?_
  refine (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
    ((smallEtaleDerivedSectionsAbAtFinal.{u, u + 1} B X hX).mapIso heq.symm) ≪≫ ?_
  refine (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
    (Stacks.Injectives.derivedPrecompObjIso (smallEtaleModulesToAbelianSheaf B X hX)
      ((sheafSections (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj
        (Opposite.op (SmallEtale.final B X hX))) P).symm ≪≫ ?_
  refine (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
    ((smallEtaleDerivedSectionsAtFinalModuleIso B X hX).app P) ≪≫ ?_
  refine (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
    ((smallEtaleDerivedSectionsAtFinalForgetIso B X hX).app P) ≪≫ ?_
  refine (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
    (smallEtaleFinalForgetToAb B X hX) q).app _ ≪≫ ?_
  refine (smallEtaleFinalForgetToAb B X hX).mapIso
    (asIso ((Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge.{u + 1, u, u + 1, u + 1,
      u + 1} (smallEtaleIntegerRingSheaf B X hX) (SmallEtale.final B X hX) q).app P)) ≪≫ ?_
  refine (Stacks.Cohomology.ZModSheaf.sectionsIso.{u + 1, u + 1}
    (SmallEtale.topology B X hX) 0 (Opposite.op (SmallEtale.final B X hX))).app _ ≪≫ ?_
  refine ((sheafSections (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj
    (Opposite.op (SmallEtale.final B X hX))).mapIso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (smallEtaleModulesToAbelianSheaf B X hX) q).app P).symm ≪≫ ?_
  refine ((sheafSections (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj
    (Opposite.op (SmallEtale.final B X hX))).mapIso
      ((DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) q).mapIso heq) ≪≫ ?_
  exact ((smallEtaleΓNatIsoSectionsAtFinal.{u, u + 1} B X hX).app _).symm

end Modules

/-- **[Stacks, Tag 0F1G].** Let `K` be a separably closed field, `X` a scheme of finite type over
`K` and `Q` an object of the unbounded derived category of abelian sheaves on the small étale
site of `X` whose stalks vanish away from the closed points of `X`. Then `Q` is zero if and only
if all of its hypercohomology groups vanish.

One direction is formal. For the other, `Q` is zero exactly when every cohomology sheaf `H^q(Q)`
is zero; the stalk hypothesis says that each `H^q(Q)` is supported at closed points, so
[Stacks, Tag 0BKZ] identifies `H^q(X, Q)` with `Γ(X, H^q(Q))`
(`AlgebraicGeometry.nonempty_hypercohomologyAbIsoΓHomology_of_supportSheaf_subset_closedPoints`),
and [Stacks, Tag 0F1F] makes a sheaf supported at closed points with no global sections zero
(`AlgebraicGeometry.isZero_of_isZero_Γ_of_supportSheaf_subset_closedPoints`). -/
@[stacks 0F1G]
public theorem isZero_iff_forall_isZero_etaleHypercohomology_of_closedPointSupport
    (K : Type u) [Field K] [IsSepClosed K] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : DerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}))
    (hQ : ∀ (p : GeometricPoint X) (q : ℤ), ¬ IsClosed ({p.hom default} : Set X) →
      IsZero (etaleStalk B X hX p
        ((DerivedCategory.homologyFunctor
          (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) q).obj Q).obj)) :
    IsZero Q ↔
      ∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((smallEtaleDerivedGlobalSectionsAb.{u, u + 1} B X hX).obj Q)) := by
  have hsupp : ∀ q : ℤ, supportSheaf B X hX ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) q).obj Q) ⊆
        {x : X | IsClosed ({x} : Set X)} := fun q =>
    supportSheaf_subset_closedPoints_of_forall_isZero_etaleStalk.{u, u + 1} B X hX _
      (fun p hp => hQ p q hp)
  have hedge := nonempty_hypercohomologyAbIsoΓHomology_of_supportSheaf_subset_closedPoints
    B X hX K f Q hsupp
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine ⟨fun h q ↦ (((hedge q).some.isZero_iff)).2 ?_, fun h q ↦ ?_⟩
  · exact (Sheaf.Γ (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).map_isZero (h q)
  · exact isZero_of_isZero_Γ_of_supportSheaf_subset_closedPoints B X hX K f _ (hsupp q)
      (((hedge q).some.isZero_iff).1 (h q))

end AlgebraicGeometry

end
