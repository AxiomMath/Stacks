module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Cohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransition
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE

/-!
# Etale cohomology of a base change along a directed system of algebras (Stacks 03Q6)

Let `A` be a ring, let `I` be a nonempty directed preorder, let `(B_i)` be a system of
`A`-algebras over `I` and let `B = colim_i B_i`. Let `X` be a scheme over `Spec A`, write
`Y_i = X ×_{Spec A} Spec B_i` and `Y = X ×_{Spec A} Spec B`, and let `F` be an abelian sheaf on
the small etale site of `X` with inverse images `G_i` on `Y_i` and `G` on `Y`. Stacks 03Q6 asserts

`H^p_etale(Y, G) = colim_i H^p_etale(Y_i, G_i)`

for a quasi-compact and quasi-separated `X`. **This file treats the case where `X` is affine**,
where every `Y_i` and `Y` is affine too, and where the small affine etale site of each of them
therefore has the scheme itself as its terminal object.

Two pieces are assembled. The *system* is the diagram of base changes together with its limit
cone: the geometric side of the source's remark that `Y = lim_i Y_i`, which is what turns 03Q6
into an instance of Stacks 09YQ. The *transport* is the cohomological content of Stacks 04HR: the
inclusion of the small affine etale site of a scheme into its small etale site is a special
cocontinuous functor, so restriction along it is an equivalence of abelian sheaf categories, and
an equivalence of sites does not change global cohomology.

## Main results

Everything lives in the namespace `Stacks.EtaleCohomology.BaseChangeAlgebraSystem`.

* `affineEtaleCohomologyFunctorIso` — **the cohomological form of Stacks 04HR.** For every scheme
  `S` of a big etale site and every degree `p`,
  `H^p(S_{affine,etale}, F|_{S_{affine,etale}}) ≅ H^p(S_etale, F)`, naturally in the abelian
  sheaf `F` on the small etale site. No affineness of `S` is needed. `affineEtaleCohomologyIso`
  is the same isomorphism at a fixed sheaf, and `etaleCohomologyFunctor_eq` identifies the
  right-hand side with the library's mainstream `Stacks.EtaleCohomology.etaleCohomologyFunctor`.
* `rightDerivedSectionsFinalIsoEtaleCohomology` — the same comparison in the shape its consumers
  have it, for an **affine** `S`: the right derived functors of sections over the terminal object
  `S / S` of the small affine etale site compute the etale cohomology of `S`.
* `baseChange`, `baseChangeCone`, `isLimitBaseChangeCone` — the system
  `Y_i = Spec B_i ×_{Spec A} X` of base changes of `X` and the fact that base change along
  `X ⟶ Spec A` carries a limit cone of the system `(Spec B_i)` over `Spec A` to a limit cone, so
  that `Y = lim_i Y_i`.
* `systemLimitCone`, `isLimitSystemLimitCone` — the limit of the system, built by lifting the
  limit cone `Spec (colim_i B_i) = lim_i Spec B_i` of Stacks 01YW to the category of schemes over
  `Spec A` and base changing it.
* `etaleCohomologyColimit_baseChange_isColimit` — **Stacks 03Q6 for affine `X`**, over any limit
  cone of the system of base changes: the canonical cohomology cocone is a colimit cocone.
* `etaleCohomologyColimit_baseChange_systemLimit_isColimit` — the same statement at the canonical
  limit `systemLimitCone`, so that the scheme the cohomology on the left is taken over is the
  honest `Y = (lim_i Spec B_i) ×_{Spec A} X = Spec B ×_{Spec A} X`.

## Implementation notes

**`X` is assumed affine, and this is not a cosmetic restriction.** For a general quasi-compact
and quasi-separated `X` the levels `Y_i` are quasi-compact and quasi-separated but not affine, so
`Y_i` is not an object of its own small *affine* etale site and
`AlgebraicGeometry.SmallAffineEtale.finalIsTerminal` — which carries the hypothesis `[IsAffine S]`
— does not apply. Passing from the affine charts of `Y_i` to `Y_i` itself is a Cech /
Mayer-Vietoris descent along a finite affine cover, and for a non-separated `Y_i` the
intersections of two affine opens need not be affine, so the `HasIntersectionsIn` hypotheses of
the Cech machinery of this library fail; see the discussion at
`StacksFrontier/AlgebraicGeometry/Morphisms/QuasiSeparated/AffineOneHypercover.lean`. That descent
theorem is not formalized here. The covering input for it is available as
`Stacks.EtaleCohomology.QcqsLimitCohomology.exists_finite_jointlySurjective_smallAffineEtale`.

The system is built over a *constant* base: `Spec A` lies below the whole system rather than
being one of its stages, so `AlgebraicGeometry.LimitDescent.bcDiagram`, whose base is the stage
`D i` of the diagram and whose index is `Over i`, is not the tool for it. What takes its place is
`CategoryTheory.Over.pullback`, a right adjoint and therefore limit preserving, together with
`CategoryTheory.Over.forget`, which creates limits of connected shape — and the opposite of a
nonempty directed preorder is cofiltered, hence connected. The pullbacks are written in the order
`pullback (Spec B_i ⟶ Spec A) (X ⟶ Spec A)`, which is the order `CategoryTheory.Over.pullback`
produces, so the levels read `Spec B_i ×_{Spec A} X` rather than `X ×_{Spec A} Spec B_i`.

The system of `A`-algebras appears here in its geometric form, as a diagram `Z` of affine schemes
over an affine base `T`; the dictionary is `T = Spec A`, `Z.obj i = Spec B_i`, and
`Spec B = Spec (colim_i B_i) = lim_i Spec B_i` by Stacks 01YW
(`AlgebraicGeometry.Scheme.affineLimitCone`), which is what `systemLimitCone` uses. The index,
the schemes and the big etale site all live in one universe `u`: Stacks 09YQ is stated for an
index in `Type v` and schemes in `Scheme.{max u v}`, and `AlgebraicGeometry.Scheme.affineLimitCone`
needs the index category to have objects and morphisms in the scheme universe, which forces the
two to agree.

The abelian sheaf system `F`, the sheaf `𝒢` presenting the colimit of its inverse images, the
legs `ι`, the presentation `hcolim` and the cocone `E` are hypotheses of the final statement,
exactly as they are in Stacks 09YP, in Stacks 09YQ and in the source of 03Q6, where
`G = colim_i f_i^{-1} G_i` is given data rather than a construction.

The cohomology of the final statement is the right derived `sheafSections` of Stacks 09YP on the
small *affine* etale sites, inherited from
`Stacks.EtaleCohomology.AffineLimitCohomology.etaleCohomologyColimit_isColimit_of_affine`, and
the identification of those groups with the library's mainstream etale cohomology is **not**
completed here. What is supplied towards it is the Stacks 04HR half,
`rightDerivedSectionsFinalIsoEtaleCohomology`: on the small affine etale site of an affine `S`,
with coefficients in `AddCommGrpCat.{u + 1}`, the right derived functors of sections over the
terminal object are the etale cohomology of `S`. The step still missing is the passage between
that site and the universe-raised site `AsSmall (SmallAffineEtale ...)` on which Stacks 09YP is
stated — `CategoryTheory.Sheaf.H'` has its coefficients in the morphism universe of the site, so
the terminal-object comparison `Stacks.Cohomology.TerminalCohomology.h'IsoH` is unavailable on
the unraised site, and the transport of cohomology across `CategoryTheory.AsSmall.equiv` is not
performed in this library.

## References

* [Stacks 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks 01YW](https://stacks.math.columbia.edu/tag/01YW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u

namespace Stacks.EtaleCohomology.BaseChangeAlgebraSystem

open AlgebraicGeometry

/-! ### Stacks 04HR on cohomology

The small affine etale site of a scheme computes its etale cohomology.
-/

section Transport

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04HR, cocontinuity.** The inclusion of the small affine etale site into the small
etale site is cocontinuous. -/
alias isCocontinuous_smallAffineEtaleInclusion :=
  AlgebraicGeometry.smallAffineEtale_inclusion_isCocontinuous

/-- **Stacks 04HR, dense subsite.** The small affine etale site is a dense subsite of the small
etale site. -/
theorem isDenseSubsite_smallAffineEtaleInclusion :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).IsDenseSubsite
      (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
      (AlgebraicGeometry.SmallEtale.topology B S hS) :=
  (AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2

attribute [local instance] isCocontinuous_smallAffineEtaleInclusion
  isDenseSubsite_smallAffineEtaleInclusion

/-- Abelian sheaves on the small affine etale site admit sheafification, with coefficients in the
universe of the objects of the site. -/
theorem hasSheafify_smallAffineEtale :
    HasSheafify (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- Abelian sheaves on the small etale site admit sheafification, with coefficients in the
universe of the objects of the site. -/
theorem hasSheafify_smallEtale :
    HasSheafify (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
  CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

attribute [local instance] hasSheafify_smallAffineEtale hasSheafify_smallEtale

/-- Abelian sheaves on the small affine etale site are locally `(u + 1)`-small. -/
theorem locallySmall_smallAffineEtale :
    LocallySmall.{u + 1}
      (Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{u + 1, u + 1, u, u + 1, u + 2}
    (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1}

/-- Abelian sheaves on the small etale site are locally `(u + 1)`-small. -/
theorem locallySmall_smallEtale :
    LocallySmall.{u + 1}
      (Sheaf (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.locallySmall_of_small.{u + 1, u + 1, u, u + 1, u + 2}
    (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}

attribute [local instance] locallySmall_smallAffineEtale locallySmall_smallEtale

/-- Abelian sheaves on the small affine etale site have enough injectives. -/
theorem enoughInjectives_smallAffineEtale :
    EnoughInjectives
      (Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2}
    (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1}

/-- Abelian sheaves on the small etale site have enough injectives. -/
theorem enoughInjectives_smallEtale :
    EnoughInjectives
      (Sheaf (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  CategoryTheory.Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2}
    (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}

attribute [local instance] enoughInjectives_smallAffineEtale enoughInjectives_smallEtale

/-- `Ext`-groups of abelian sheaves on the small affine etale site exist in `Type (u + 1)`. -/
theorem hasExt_smallAffineEtale :
    HasExt.{u + 1}
      (Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-- `Ext`-groups of abelian sheaves on the small etale site exist in `Type (u + 1)`. -/
theorem hasExt_smallEtale :
    HasExt.{u + 1}
      (Sheaf (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

attribute [local instance] hasExt_smallAffineEtale hasExt_smallEtale

/-- **The restriction `F ↦ F|_{S_{affine,etale}}`** of an abelian sheaf on the small etale site of
`S` to the small affine etale site. -/
abbrev restrictToAffineEtale :
    Sheaf (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} ⥤
      Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
  (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
    (AlgebraicGeometry.SmallEtale.topology B S hS)

/-- **Stacks 04HR on sheaves.** Restriction to the small affine etale site is an equivalence on
abelian sheaves, the affine objects forming a dense subsite. -/
theorem restrictToAffineEtale_isEquivalence :
    (restrictToAffineEtale B S hS).IsEquivalence :=
  inferInstance

attribute [local instance] restrictToAffineEtale_isEquivalence

/-- The `p`-th cohomology functor of abelian sheaves on the small affine etale site of `S`: the
`Ext`-groups out of the constant sheaf on `ℤ`. -/
abbrev affineEtaleCohomologyFunctor (p : ℕ) :
    Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u, u + 1}
    (AlgebraicGeometry.SmallAffineEtale.topology B S hS) p

/-- The `p`-th cohomology functor of abelian sheaves on the small etale site of `S`. -/
abbrev smallEtaleCohomologyFunctor (p : ℕ) :
    Sheaf (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u, u + 1} (AlgebraicGeometry.SmallEtale.topology B S hS) p

/-- The cohomology functor of the small etale site of `S` used here is the library's mainstream
etale cohomology functor of the scheme `S`. -/
theorem etaleCohomologyFunctor_eq (p : ℕ) :
    smallEtaleCohomologyFunctor B S hS p =
      Stacks.EtaleCohomology.etaleCohomologyFunctor B ⟨S, hS⟩ p :=
  rfl

/-- **The cohomological form of Stacks 04HR: restriction to the small affine etale site does not
change cohomology.** For every degree `p`,

`H^p(S_{affine,etale}, F|_{S_{affine,etale}}) ≅ H^p(S_etale, F)`

naturally in the abelian sheaf `F` on the small etale site of `S`. No affineness of `S` is needed:
the affine objects form a dense subsite of the small etale site (Stacks 04HR), so restriction to
them is an equivalence of abelian sheaf categories, and an equivalence of sites changes neither
the constant sheaf on `ℤ` nor the injective objects, hence not the `Ext`-groups out of the
constant sheaf.

This is `Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence` applied to the
inclusion; no terminal object of either site enters. -/
def affineEtaleCohomologyFunctorIso (p : ℕ) :
    restrictToAffineEtale B S hS ⋙ affineEtaleCohomologyFunctor B S hS p ≅
      smallEtaleCohomologyFunctor B S hS p :=
  Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence.{u + 1, u, u + 1}
    (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
    (AlgebraicGeometry.SmallEtale.topology B S hS)
    (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS) p

/-- The isomorphism of `affineEtaleCohomologyFunctorIso` at a fixed abelian sheaf on the small
etale site of `S`. -/
def affineEtaleCohomologyIso
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (affineEtaleCohomologyFunctor B S hS p).obj ((restrictToAffineEtale B S hS).obj F) ≅
      (smallEtaleCohomologyFunctor B S hS p).obj F :=
  (affineEtaleCohomologyFunctorIso B S hS p).app F

/-! ### The affine case: cohomology over the terminal object -/

section Affine

variable [IsAffine S]

/-- Global sections of abelian sheaves on the small affine etale site of an affine `S` exist: the
site has a terminal object, namely `S / S`. -/
theorem hasGlobalSectionsFunctor_smallAffineEtale :
    HasGlobalSectionsFunctor (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
      AddCommGrpCat.{u + 1} :=
  CategoryTheory.hasGlobalSectionsFunctor_of_hasTerminal _ _

attribute [local instance] hasGlobalSectionsFunctor_smallAffineEtale

/-- Global sections of abelian sheaves on the small affine etale site are additive, being a right
adjoint. -/
theorem additive_sheafΓ_smallAffineEtale :
    (Sheaf.Γ (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
      AddCommGrpCat.{u + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u, u + 1} _

attribute [local instance] additive_sheafΓ_smallAffineEtale

/-- Sections over the terminal object `S / S` of the small affine etale site of an affine `S` are
additive. -/
theorem additive_sectionsFinal_smallAffineEtale :
    (((sheafSections (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
      AddCommGrpCat.{u + 1}).obj (op (AlgebraicGeometry.SmallAffineEtale.final B S hS)))).Additive
    where
  map_add := by intros; rfl

attribute [local instance] additive_sectionsFinal_smallAffineEtale

/-- For an affine `S` the global sections of an abelian sheaf on the small affine etale site are
its sections over `S / S`, that object being terminal
(`AlgebraicGeometry.SmallAffineEtale.finalIsTerminal`). -/
def sheafΓIsoSectionsFinal :
    Sheaf.Γ (AlgebraicGeometry.SmallAffineEtale.topology B S hS) AddCommGrpCat.{u + 1} ≅
      (sheafSections (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
        AddCommGrpCat.{u + 1}).obj (op (AlgebraicGeometry.SmallAffineEtale.final B S hS)) :=
  Sheaf.ΓNatIsoSheafSections _ _ (AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B S hS)

/-- **Cohomology over the terminal object of the small affine etale site of an affine `S` is its
sheaf cohomology.** The right derived functors of sections over `S / S` are the `Ext`-groups out
of the constant sheaf on `ℤ`: sections over `S / S` are global sections
(`sheafΓIsoSectionsFinal`), whose right derived functors are sheaf cohomology
(`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`). -/
def rightDerivedSectionsFinalIso (p : ℕ) :
    (((sheafSections (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
          AddCommGrpCat.{u + 1}).obj
        (op (AlgebraicGeometry.SmallAffineEtale.final B S hS))).rightDerived p) ≅
      affineEtaleCohomologyFunctor B S hS p :=
  (Functor.rightDerivedIsoOfNatIso (sheafΓIsoSectionsFinal B S hS) p).symm ≪≫
    Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1}
      (AlgebraicGeometry.SmallAffineEtale.topology B S hS) p

/-- **The comparison of Stacks 04HR in the shape its consumers have it.** For an affine `S`, the
right derived functors of sections over the terminal object `S / S` of the small affine etale
site, applied to the restriction of an abelian sheaf `F` on the small etale site, are the etale
cohomology groups `H^p(S_etale, F)`. -/
def rightDerivedSectionsFinalIsoEtaleCohomology (p : ℕ) :
    restrictToAffineEtale B S hS ⋙
        (((sheafSections (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
            AddCommGrpCat.{u + 1}).obj
          (op (AlgebraicGeometry.SmallAffineEtale.final B S hS))).rightDerived p) ≅
      smallEtaleCohomologyFunctor B S hS p :=
  Functor.isoWhiskerLeft _ (rightDerivedSectionsFinalIso B S hS p) ≪≫
    affineEtaleCohomologyFunctorIso B S hS p

end Affine

end Transport

/-! ### The system of base changes and its limit -/

section System

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)

-- The opposite of a nonempty directed preorder is cofiltered, hence connected. This is what
-- makes `CategoryTheory.Over.forget` create the limits of the system.
attribute [local instance] IsCofiltered.isConnected

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The system of base changes.** For a diagram `Z` of schemes over `T` and a scheme `X` over
`T`, the diagram `i ↦ Z_i ×_T X`. With `T = Spec A`, `Z_i = Spec B_i` and `X ⟶ Spec A` this is
the system `Y_i` of Stacks 03Q6. -/
def baseChange : Iᵒᵖ ⥤ Scheme.{u} :=
  (Z ⋙ Over.pullback X.hom) ⋙ Over.forget X.left

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The level `i` of the system of base changes is the fibre product `Z_i ×_T X`. -/
theorem baseChange_obj (i : Iᵒᵖ) :
    (baseChange T X Z).obj i = Limits.pullback (Z.obj i).hom X.hom :=
  rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The cone on the system of base changes obtained from a cone on `Z` over `T` by base change
along `X ⟶ T`. Its apex is `(lim Z) ×_T X`. -/
def baseChangeCone (cZ : Cone Z) : Cone (baseChange T X Z) :=
  (Over.forget X.left).mapCone ((Over.pullback X.hom).mapCone cZ)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The apex of `baseChangeCone` is the base change of the apex of the given cone. -/
theorem baseChangeCone_pt (cZ : Cone Z) :
    (baseChangeCone T X Z cZ).pt = Limits.pullback cZ.pt.hom X.hom :=
  rfl

variable [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]

omit [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine X.left] in
/-- The diagram of schemes underlying `Z` consists of affine schemes. Stated as an instance so
that `AlgebraicGeometry.Scheme.affineLimitCone` applies to it: `Functor.comp` is not reducible, so
instance search does not see through `(Z ⋙ Over.forget T).obj i` on its own. -/
instance isAffine_compForget_obj (i : Iᵒᵖ) : IsAffine ((Z ⋙ Over.forget T).obj i) :=
  inferInstanceAs (IsAffine (Z.obj i).left)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Every level of the system of base changes is affine: it is a fibre product of affine schemes.
This is where the affineness of `X` is used. -/
instance isAffine_baseChange_obj (i : Iᵒᵖ) : IsAffine ((baseChange T X Z).obj i) :=
  inferInstanceAs (IsAffine (Limits.pullback (Z.obj i).hom X.hom))

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- Every transition morphism of the system of base changes is affine, being a morphism of affine
schemes. -/
instance isAffineHom_baseChange_map {i j : Iᵒᵖ} (a : i ⟶ j) :
    IsAffineHom ((baseChange T X Z).map a) :=
  inferInstance

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- The system of base changes has a limit: it is a diagram of affine schemes (Stacks 01YW). -/
theorem hasLimit_baseChange : HasLimit (baseChange T X Z) :=
  Scheme.hasLimit_of_isAffine _

/-- **Base change carries a limit of the system to the limit of the system of base changes.** If
`cZ` is a limit cone of the diagram `Z` of schemes over `T`, then
`(lim Z) ×_T X = lim_i (Z_i ×_T X)`.

`CategoryTheory.Over.pullback` is a right adjoint, hence preserves limits;
`CategoryTheory.Over.forget` creates limits of connected shape, and the index is connected by
`CategoryTheory.IsCofiltered.isConnected`, so it preserves them once the base-changed diagram has
a limit — which it does, being a diagram of affine schemes. -/
def isLimitBaseChangeCone (cZ : Cone Z) (hZ : IsLimit cZ) :
    IsLimit (baseChangeCone T X Z cZ) := by
  haveI : HasLimit ((Z ⋙ Over.pullback X.hom) ⋙ Over.forget X.left) :=
    hasLimit_baseChange T X Z
  exact isLimitOfPreserves (Over.forget X.left)
    (isLimitOfPreserves (Over.pullback X.hom) hZ)

omit [IsAffine X.left] in
/-- A limit cone of the diagram `Z` **in the category of schemes over `T`**, obtained by lifting
the limit cone of Stacks 01YW: the diagram of affine schemes underlying `Z` has the limit
`Spec (colim_i Γ(Z_i))`, and `CategoryTheory.Over.forget` creates that limit because the index is
connected. With `Z_i = Spec B_i` the apex is `Spec (colim_i B_i) = Spec B`. -/
def overLimitCone : Cone Z :=
  liftLimit (K := Z) (F := Over.forget T) (Scheme.affineLimitCone (Z ⋙ Over.forget T)).isLimit

omit [IsAffine X.left] in
/-- `overLimitCone` is a limit cone. -/
def isLimitOverLimitCone : IsLimit (overLimitCone T Z) :=
  liftedLimitIsLimit _

omit [IsAffine X.left] in
/-- The underlying scheme of the apex of `overLimitCone` is the apex of the limit cone of Stacks
01YW, that is `Spec` of the colimit of the rings of global sections of the `Z_i`. -/
def overLimitCone_pt_iso :
    (Over.forget T).obj (overLimitCone T Z).pt ≅
      (Scheme.affineLimitCone (Z ⋙ Over.forget T)).cone.pt :=
  haveI : HasLimit (Z ⋙ Over.forget T) := Scheme.hasLimit_of_isAffine _
  (isLimitOfPreserves (Over.forget T) (isLimitOverLimitCone T Z)).conePointUniqueUpToIso
    (Scheme.affineLimitCone (Z ⋙ Over.forget T)).isLimit

/-- **The limit of the system of base changes.** Its apex is `(lim_i Z_i) ×_T X`; with
`T = Spec A`, `Z_i = Spec B_i` and `B = colim_i B_i` this is `Y = Spec B ×_{Spec A} X`. -/
def systemLimitCone : Cone (baseChange T X Z) :=
  baseChangeCone T X Z (overLimitCone T Z)

/-- `systemLimitCone` is a limit cone: `Y = lim_i Y_i`. -/
def isLimitSystemLimitCone : IsLimit (systemLimitCone T X Z) :=
  isLimitBaseChangeCone T X Z _ (isLimitOverLimitCone T Z)

end System

/-! ### Stacks 03Q6 for an affine `X` -/

section Colimit

open Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-! The five definitions that follow are the data of Stacks 0EYL and Stacks 09YL for the system of
base changes, each wrapped in a definition of its own, and each carrying its binders explicitly.

They are deliberately not abbreviations. The statement of Stacks 03Q6 below mentions the system of
sites, the functors to the limit and the coverings a dozen times over, and re-elaborating each of
them at the concrete diagram `baseChange T X Z` — which means re-synthesizing its affineness
instances through the composite `(Z ⋙ Over.pullback X.hom) ⋙ Over.forget X.left` every time —
exhausts the elaborator's budget. Behind a definition each occurrence is an application of atoms,
and the single unfolding needed to discharge the statement happens once, in the proof. -/

/-- **The system of sites of Stacks 0EYL for the system of base changes**: the strict inverse
system of small sites equivalent to the small affine etale sites of the `Y_i`. -/
def bcSys (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt) :
    InverseSystemOfFiniteSites.{u, u, u + 1} :=
  sys.{u, u} (baseChange T X Z) cY B hD hY hcY

/-- The small affine etale site of the limit `Y`, raised to the universe of the levels of the
system. This is `Stacks.EtaleCohomology.AffineLimitCohomology.limitSite` written out. -/
abbrev bcLimitSite (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (_hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (_hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt) :
    Type (u + 1) :=
  AsSmall.{u + 1} (AlgebraicGeometry.SmallAffineEtale B cY.pt hY)

/-- The etale coverings of the raised site of `Y`, as a precoverage. -/
def bcPrecoverage (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt) :
    Precoverage (bcLimitSite T X Z cY hcY B hD hY) :=
  limitSitePrecoverage.{u, u} (baseChange T X Z) cY B hY

/-- The canonical functors from the levels of the system to the raised site of `Y`. -/
def bcToLimitSmall (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
    (i : (bcSys T X Z cY hcY B hD hY).I) :
    (bcSys T X Z cY hcY B hD hY).C i ⥤ bcLimitSite T X Z cY hcY B hD hY :=
  toLimitSmall.{u, u} (baseChange T X Z) cY B hD hY hcY i

/-- **The cocone identity of Stacks 09YL** for the system of base changes: the functors to the
site of `Y` are compatible with the transition functors of the system. -/
theorem bcToLimitSmall_transition (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
    {i j : (bcSys T X Z cY hcY B hD hY).I} (a : i ⟶ j) :
    (bcSys T X Z cY hcY B hD hY).u a ⋙ bcToLimitSmall T X Z cY hcY B hD hY i =
      bcToLimitSmall T X Z cY hcY B hD hY j :=
  toLimitSmall_transition.{u, u} (baseChange T X Z) cY B hD hY hcY a

/-- The terminal object of the level `i`, which is the scheme `Y_i` itself: every level of the
system of base changes is affine, so it is an object of its own small affine etale site and is the
terminal one. -/
def bcLevelTerminal (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
    (i : (bcSys T X Z cY hcY B hD hY).I) :
    (bcSys T X Z cY hcY B hD hY).C i :=
  levelTerminal.{u, u} (baseChange T X Z) cY B hD hY hcY i

/-- **Stacks 03Q6 for an affine `X`.** Let `I` be a nonempty directed preorder, let `T = Spec A`
be affine, let `Z_i = Spec B_i` be a diagram of affine schemes over `T` indexed by `Iᵒᵖ` and let
`X` be an *affine* scheme over `T`. Form the system `Y_i = Z_i ×_T X` of base changes
(`baseChange`) and let `cY` be a limit cone of it, with apex `Y`. Let `F` be a system of abelian
sheaves on the small affine etale sites of the `Y_i`, let `𝒢` on the small affine etale site of
`Y` present the colimit `colim_i f_i^{-1} F_i`, and let `p` be a degree. Then

`H^p(Y, 𝒢) = colim_i H^p(Y_i, F_i)`

is a filtered colimit: the canonical cohomology cocone is a colimit cocone.

Every level `Y_i` is affine, because `X` is (`isAffine_baseChange_obj`), and so is `Y`, being a
limit of affine schemes; each is therefore the terminal object of its own small affine etale site
(`bcLevelTerminal`), and the groups of the diagram and the vertex of the cocone are the cohomology
groups of the schemes of the system. This is
`Stacks.EtaleCohomology.AffineLimitCohomology.etaleCohomologyColimit_isColimit_of_affine`
instantiated at the system of base changes.

The limit cone is a hypothesis rather than a construction, as it is in Stacks 09YQ. The
instantiation this statement is for is `cY = systemLimitCone T X Z` with
`hcY = isLimitSystemLimitCone T X Z`, whose apex is `(lim_i Z_i) ×_T X`, that is
`Y = Spec B ×_{Spec A} X` with `B = colim_i B_i` by Stacks 01YW; `isLimitSystemLimitCone` is
exactly the datum this asks for, and
`etaleCohomologyColimit_baseChange_systemLimit_isColimit` is this statement with that datum
already supplied. -/
def etaleCohomologyColimit_baseChange_isColimit (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
      (bcSys T X Z cY hcY B hD hY))
    (𝒢 : Sheaf (bcPrecoverage T X Z cY hcY B hD hY).toGrothendieck Ab.{u + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (bcToLimitSmall T X Z cY hcY B hD hY j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{u, u, u + 1, u + 1} (bcSys T X Z cY hcY B hD hY)
      (bcToLimitSmall T X Z cY hcY B hD hY)
      (bcToLimitSmall_transition T X Z cY hcY B hD hY)
      (bcPrecoverage T X Z cY hcY B hD hY) F 𝒢 ι)
    (i : (bcSys T X Z cY hcY B hD hY).I) (p : ℕ)
    (E : CohomologyCocone.{u, u, u + 1, u + 1} (bcSys T X Z cY hcY B hD hY)
      (bcToLimitSmall T X Z cY hcY B hD hY)
      (bcToLimitSmall_transition T X Z cY hcY B hD hY)
      (bcPrecoverage T X Z cY hcY B hD hY) F 𝒢 ι i
      (bcLevelTerminal T X Z cY hcY B hD hY i) p) :
    IsColimit E.cocone :=
  etaleCohomologyColimit_isColimit_of_affine.{u, u} (baseChange T X Z) cY B hD hY hcY F 𝒢 ι
    hcolim i p E

/-- **Stacks 03Q6 for an affine `X`, at the canonical limit.** This is
`etaleCohomologyColimit_baseChange_isColimit`
instantiated at `cY = systemLimitCone T X Z`, so that the scheme the cohomology on the left is
taken over is the honest `Y = (lim_i Z_i) ×_T X`: with `T = Spec A`, `Z_i = Spec B_i` and
`B = colim_i B_i` this is `Spec B ×_{Spec A} X`, by Stacks 01YW
(`AlgebraicGeometry.Scheme.affineLimitCone`, through `overLimitCone_pt_iso`). -/
@[stacks 03Q6 "the case of an AFFINE `X`: the source allows `X ⟶ Spec(A)` quasi-compact and \
quasi-separated, and the passage from an affine `X` to a general qcqs one is the Cech descent \
along a finite affine cover, which this library does not carry. The system is geometric rather \
than ring-level: `T`, the `Z_i` and `X` are affine schemes over `T`, and `A`, `B_i`, \
`B = colim B_i` are reached through `Spec(colim B_i) = lim Spec B_i` of Stacks 01YW, no \
`CommRingCat`-level wrapper taking a ring and a functor `I ⟶ CommRingCat` being stated. The \
base change is written `Z_i ×_T X`. The cohomology is the right-derived `sheafSections` of \
Stacks 09YP on the small AFFINE etale sites, inherited from \
`etaleCohomologyColimit_isColimit_of_affine`, and is NOT yet identified with the mainstream \
`Stacks.EtaleCohomology.etaleCohomologyFunctor`: the 04HR half of that identification is \
supplied here by `affineEtaleCohomologyFunctorIso`, but transporting cohomology across \
`AsSmall.equiv` onto the universe-raised site Stacks 09YP is stated on does not exist in this \
library"]
def etaleCohomologyColimit_baseChange_systemLimit_isColimit
    (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
    [IsAffine T] [IsAffine X.left] [∀ i, IsAffine (Z.obj i).left]
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i))
    (hY : B.Contains (systemLimitCone T X Z).pt)
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
      (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY))
    (𝒢 : Sheaf (bcPrecoverage T X Z (systemLimitCone T X Z)
      (isLimitSystemLimitCone T X Z) B hD hY).toGrothendieck Ab.{u + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (bcToLimitSmall T X Z (systemLimitCone T X Z)
      (isLimitSystemLimitCone T X Z) B hD hY j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{u, u, u + 1, u + 1}
      (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall_transition T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY)
      (bcPrecoverage T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY) F 𝒢 ι)
    (i : (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY).I) (p : ℕ)
    (E : CohomologyCocone.{u, u, u + 1, u + 1}
      (bcSys T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY)
      (bcToLimitSmall_transition T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY)
      (bcPrecoverage T X Z (systemLimitCone T X Z) (isLimitSystemLimitCone T X Z) B hD hY) F 𝒢 ι i
      (bcLevelTerminal T X Z (systemLimitCone T X Z)
        (isLimitSystemLimitCone T X Z) B hD hY i) p) :
    IsColimit E.cocone :=
  etaleCohomologyColimit_baseChange_isColimit T X Z (systemLimitCone T X Z)
    (isLimitSystemLimitCone T X Z) B hD hY F 𝒢 ι hcolim i p E

end Colimit

end Stacks.EtaleCohomology.BaseChangeAlgebraSystem

end
