module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleStalkModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SiteEquivalenceGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.DerivedIndexing.Composite
import StacksCore.Tactic.StacksAttribute

/-!
# Étale cohomology over a field is Galois cohomology, in every degree

Let `K` be a field, let `sbar` be a geometric point of `Spec K` and let `G` be the absolute
Galois group at `sbar`. The stalk equivalence `AlgebraicGeometry.etaleContinuousGModuleEquivalence`
identifies abelian sheaves `F` on the small étale site of `Spec K` with discrete `G`-modules `M_F`,
and `AlgebraicGeometry.etaleGammaIsoContinuousGModuleInvariants` identifies global sections with
`G`-invariants. Consequently, in the derived category of abelian groups
`RΓ(Spec K, F) ≅ RΓ_G(M_F)`, and for every `q` and every abelian sheaf `F`

`H^q_étale(Spec K, F) = H^q(G, M_F)`.

The coefficients are `AddCommGrpCat.{u + 1}`, in the universe of the objects of the small étale
site of `Spec K` for `K : Type u`.

## Main results

* `AlgebraicGeometry.etaleDerivedGlobalSectionsIsoDerivedGaloisInvariants`: the derived global
  sections of `F` are the derived `G`-invariants of `M_F`.
* `AlgebraicGeometry.etaleRightDerivedGammaIsoContinuousGroupCohomologyFunctor`: the right derived
  functors of the global sections functor `CategoryTheory.Sheaf.Γ` are the stalk equivalence
  followed by the continuous group cohomology functors.
* `AlgebraicGeometry.etaleSheafCohomologyIsoContinuousGroupCohomologyFunctor`: Mathlib's sheaf
  cohomology functor on the small étale site of `Spec K` is the stalk equivalence followed by the
  continuous group cohomology functor.
* `AlgebraicGeometry.etaleSheafCohomologyAddEquivContinuousGroupCohomology`: the degree-`q` étale
  cohomology group of `Spec K` with coefficients in `F` is the degree-`q` continuous group
  cohomology of the Galois module of `F`.
* `AlgebraicGeometry.subsingleton_etaleSheafH_iff_isZero_continuousGroupCohomology`: the two sides
  vanish together.
* `AlgebraicGeometry.smallEtaleSheafCohomologyIsoContinuousGroupCohomologyFunctor`,
  `AlgebraicGeometry.smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology` and
  `AlgebraicGeometry.subsingleton_smallEtaleSheafH_iff_isZero_continuousGroupCohomology`: the same
  three statements on Mathlib's small étale site of `Spec K`.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-! ### Abelian sheaves and Galois modules at the coefficient universe `u + 1` -/

/-- Abelian sheaves on the small étale site `AlgebraicGeometry.SmallEtale.topology` of `Spec K`,
with coefficients in the universe of the objects of that site, form a Grothendieck abelian
category. -/
theorem isGrothendieckAbelian_etaleSheaf_objectUniverse :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- Abelian sheaves on the small étale site `AlgebraicGeometry.SmallEtale.topology` of `Spec K`,
with coefficients in the universe of the objects of that site, have enough injectives. -/
theorem enoughInjectives_etaleSheaf_objectUniverse :
    EnoughInjectives
      (Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}) :=
  have := isGrothendieckAbelian_etaleSheaf_objectUniverse B K hK
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- The `Ext`-groups of abelian sheaves on the small étale site
`AlgebraicGeometry.SmallEtale.topology` of `Spec K` lie in the universe of the objects of that
site. -/
theorem hasExt_etaleSheaf_objectUniverse :
    HasExt.{u + 1}
      (Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}) :=
  have := enoughInjectives_etaleSheaf_objectUniverse B K hK
  hasExt_of_enoughInjectives _

/-- Discrete continuous modules over the absolute Galois group, with coefficients in
`Type (u + 1)`, have enough injectives. -/
theorem enoughInjectives_continuousGModule_objectUniverse :
    EnoughInjectives
      (ContinuousGModule.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar)) :=
  continuousGModuleEnoughInjectives.{u, u + 1} _

/-- Global sections of abelian étale sheaves are additive, being a right adjoint. -/
theorem additive_etaleGlobalSectionsFunctor :
    (Sheaf.Γ (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The stalk equivalence `AlgebraicGeometry.etaleContinuousGModuleEquivalence` is additive. -/
theorem additive_etaleContinuousGModuleEquivalenceFunctor :
    ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance]
  enoughInjectives_etaleSheaf_objectUniverse
  hasExt_etaleSheaf_objectUniverse
  enoughInjectives_continuousGModule_objectUniverse
  additive_etaleGlobalSectionsFunctor
  additive_etaleContinuousGModuleEquivalenceFunctor

/-! ### Étale cohomology as continuous group cohomology -/

/-- In every degree `q`, the `q`-th right derived functor of the global sections functor
`CategoryTheory.Sheaf.Γ` of the small étale site of `Spec K` is the stalk equivalence
`AlgebraicGeometry.etaleContinuousGModuleEquivalence` followed by the `q`-th continuous group
cohomology functor of the absolute Galois group. -/
@[stacks 03QU "part (3), as an isomorphism of functors, with étale cohomology as the right \
derived functor of global sections"]
def etaleRightDerivedGammaIsoContinuousGroupCohomologyFunctor (q : ℕ) :
    (Sheaf.Γ (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}).rightDerived q ≅
      (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor ⋙
        continuousGroupCohomologyFunctor.{u, u + 1}
          (GeometricPoint.absoluteGaloisGroup sbar) q :=
  Functor.rightDerivedIsoOfNatIso
      (etaleGammaIsoContinuousGModuleInvariants.{u, u + 1} B K hK sbar) q ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
        (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor
        (continuousGModuleInvariants.{u, u + 1}
          (GeometricPoint.absoluteGaloisGroup sbar)) q ≪≫
      Functor.isoWhiskerLeft _
        (Stacks.DerivedIndexing.rightDerivedIso
          (continuousGModuleInvariants.{u, u + 1}
            (GeometricPoint.absoluteGaloisGroup sbar)) q)

/-- Let `K` be a field, let `sbar` be a geometric point of `Spec K` and let `G` be the absolute
Galois group at `sbar`. For every `q`, Mathlib's degree-`q` sheaf cohomology functor
`CategoryTheory.Sheaf.functorH` on the small étale site of `Spec K` is the stalk equivalence
`AlgebraicGeometry.etaleContinuousGModuleEquivalence` followed by the degree-`q` continuous group
cohomology functor of `G`. -/
@[stacks 03QU "part (3), in every degree, as a natural isomorphism of functors: sheaf \
cohomology on the small étale site of the spectrum of a field is the stalk equivalence of 04JQ \
followed by the continuous group cohomology functor of 04JR"]
def etaleSheafCohomologyIsoContinuousGroupCohomologyFunctor (q : ℕ) :
    Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        (SmallEtale.topology B (Spec (.of K)) hK) q ≅
      (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor ⋙
        continuousGroupCohomologyFunctor.{u, u + 1}
          (GeometricPoint.absoluteGaloisGroup sbar) q :=
  (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1} _ q).symm ≪≫
    etaleRightDerivedGammaIsoContinuousGroupCohomologyFunctor B K hK sbar q

/-- Let `K` be a field, let `sbar` be a geometric point of `Spec K` with absolute Galois group `G`,
and let `F` be an abelian sheaf on the small étale site of `Spec K`, corresponding to the
`G`-module `M` under `AlgebraicGeometry.etaleContinuousGModuleEquivalence`. Then for every `q`

`H^q_étale(Spec K, F) = H^q(G, M)`. -/
@[stacks 03QU "part (3): in every degree q, the degree-q étale cohomology of the spectrum of a \
field with coefficients in an abelian sheaf is the degree-q continuous group cohomology of the \
absolute Galois group with coefficients in the sheaf's module of 04JQ"]
def etaleSheafCohomologyAddEquivContinuousGroupCohomology
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H.{u + 1, u + 1} F q ≃+
      continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) q
        ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj F) :=
  ((etaleSheafCohomologyIsoContinuousGroupCohomologyFunctor B K hK sbar q).app
    F).addCommGroupIsoToAddEquiv

/-- An isomorphism of abelian groups `A ≅ B` shows that `A` is a subsingleton iff `B` is zero. -/
private theorem subsingleton_iff_isZero_of_iso {A B : AddCommGrpCat.{u + 1}} (e : A ≅ B) :
    Subsingleton A ↔ IsZero B :=
  AddCommGrpCat.isZero_iff_subsingleton.symm.trans e.isZero_iff

/-- The degree-`q` étale cohomology of `Spec K` with coefficients in `F` vanishes exactly when the
degree-`q` continuous group cohomology of the Galois module of `F` does. -/
theorem subsingleton_etaleSheafH_iff_isZero_continuousGroupCohomology
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) ↔
      IsZero (continuousGroupCohomology.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar) q
        ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj F)) :=
  subsingleton_iff_isZero_of_iso
    ((etaleSheafCohomologyIsoContinuousGroupCohomologyFunctor B K hK sbar q).app F)

/-! ### Derived global sections as derived Galois invariants -/

/-- Let `K` be a field, let `sbar` be a geometric point of `Spec K` with absolute Galois group `G`,
let `F` be an abelian sheaf on the small étale site of `Spec K` and let `M` be the discrete
`G`-module it corresponds to under `AlgebraicGeometry.etaleContinuousGModuleEquivalence`. Then in
the derived category of abelian groups there is a canonical isomorphism

`RΓ(Spec K, F) ≅ RΓ_G(M)`

between the derived global sections of `F` and the derived `G`-invariants of `M`, both computed
on bounded below derived categories and mapped to the unbounded one by `DerivedCategory.Plus.ι`. -/
@[stacks 03QU "part (1)"]
def etaleDerivedGlobalSectionsIsoDerivedGaloisInvariants
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}) :
    DerivedCategory.Plus.ι.obj
        ((Sheaf.Γ (SmallEtale.topology B (Spec (.of K)) hK)
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      DerivedCategory.Plus.ι.obj
        ((continuousGModuleInvariants.{u, u + 1}
          (GeometricPoint.absoluteGaloisGroup sbar)).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj F))) :=
  DerivedCategory.Plus.ι.mapIso
    ((Functor.rightDerivedFunctorPlusNatIso
        (etaleGammaIsoContinuousGModuleInvariants.{u, u + 1} B K hK sbar)).app _ ≪≫
      (Stacks.DerivedIndexing.rightDerivedPlusCompIso
        (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor
        (continuousGModuleInvariants.{u, u + 1}
          (GeometricPoint.absoluteGaloisGroup sbar))).app _ ≪≫
      (continuousGModuleInvariants.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar)).rightDerivedFunctorPlus.mapIso
        ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
            (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor).app _ ≪≫
          Functor.mapDerivedCategoryPlusObjSingleIso
            (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor F))

/-! ### On Mathlib's small étale site -/

/-- The `Ext`-groups of abelian sheaves on Mathlib's small étale site of a scheme lie in the
universe of the objects of that site. -/
theorem hasExt_smallEtaleSheaf_objectUniverse (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- Abelian groups in the universe of the objects of the small étale site have limits of the
shapes needed to restrict a sheaf along the embedding
`AlgebraicGeometry.SmallEtale.toEtaleSite`, those comma categories being essentially small. -/
local instance hasLimitsOfShape_structuredArrow_toEtaleSite
    (X : (((Spec (.of K) : Scheme.{u})).Etale)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (SmallEtale.toEtaleSite B (Spec (.of K)) hK).op)
      AddCommGrpCat.{u + 1} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

attribute [local instance] hasExt_smallEtaleSheaf_objectUniverse

/-- Restriction of abelian sheaves from Mathlib's small étale site of `Spec K` to the small étale
site `AlgebraicGeometry.SmallEtale.topology`, along the embedding
`AlgebraicGeometry.SmallEtale.toEtaleSite`; it is the quasi-inverse direction of the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
abbrev smallEtaleSheafRestriction :
    Sheaf ((Spec (.of K) : Scheme.{u})).smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1} :=
  (SmallEtale.toEtaleSite B (Spec (.of K)) hK).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B (Spec (.of K)) hK)
    ((Spec (.of K) : Scheme.{u})).smallEtaleTopology

/-- For every `q`, Mathlib's degree-`q` sheaf cohomology functor on its small étale site of
`Spec K` is the restriction `AlgebraicGeometry.smallEtaleSheafRestriction` to the site
`AlgebraicGeometry.SmallEtale.topology`, followed by the stalk equivalence
`AlgebraicGeometry.etaleContinuousGModuleEquivalence` and the degree-`q` continuous group
cohomology functor of the absolute Galois group. -/
@[stacks 03QU "part (3), in every degree, on Mathlib's small étale site of the spectrum of a \
field: sheaf cohomology there is restriction to the site of 021B followed by the stalk \
equivalence of 04JQ and the continuous group cohomology functor of 04JR"]
def smallEtaleSheafCohomologyIsoContinuousGroupCohomologyFunctor (q : ℕ) :
    Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        ((Spec (.of K) : Scheme.{u})).smallEtaleTopology q ≅
      smallEtaleSheafRestriction B K hK ⋙
        ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor ⋙
          continuousGroupCohomologyFunctor.{u, u + 1}
            (GeometricPoint.absoluteGaloisGroup sbar) q) :=
  (Stacks.Cohomology.SiteEquivalenceGlobal.sheafCohomologyIsoOfIsEquivalence.{u + 1}
      (SmallEtale.topology B (Spec (.of K)) hK)
      ((Spec (.of K) : Scheme.{u})).smallEtaleTopology
      (SmallEtale.toEtaleSite B (Spec (.of K)) hK) q).symm ≪≫
    Functor.isoWhiskerLeft _
      (etaleSheafCohomologyIsoContinuousGroupCohomologyFunctor B K hK sbar q)

/-- For every abelian sheaf `F` on Mathlib's small étale site of `Spec K` and every degree `q`,

`H^q_étale(Spec K, F) = H^q(G, M)`,

`M` being the Galois module of the restriction of `F` to the site
`AlgebraicGeometry.SmallEtale.topology`. -/
@[stacks 03QU "part (3) on Mathlib's small étale site, objectwise: the degree-q étale \
cohomology group of the spectrum of a field with coefficients in an abelian sheaf is the \
degree-q continuous group cohomology of the absolute Galois group with coefficients in the \
sheaf's Galois module"]
def smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology
    (F : Sheaf ((Spec (.of K) : Scheme.{u})).smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) :
    Sheaf.H.{u + 1, u + 1} F q ≃+
      continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) q
        ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
          ((smallEtaleSheafRestriction B K hK).obj F)) :=
  ((smallEtaleSheafCohomologyIsoContinuousGroupCohomologyFunctor B K hK sbar q).app
    F).addCommGroupIsoToAddEquiv

/-- On Mathlib's small étale site of `Spec K`, the degree-`q` étale cohomology with coefficients
in `F` vanishes exactly when the degree-`q` continuous group cohomology of the Galois module of
the restriction of `F` does. -/
theorem subsingleton_smallEtaleSheafH_iff_isZero_continuousGroupCohomology
    (F : Sheaf ((Spec (.of K) : Scheme.{u})).smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) ↔
      IsZero (continuousGroupCohomology.{u, u + 1}
        (GeometricPoint.absoluteGaloisGroup sbar) q
        ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj
          ((smallEtaleSheafRestriction B K hK).obj F))) :=
  subsingleton_iff_isZero_of_iso
    ((smallEtaleSheafCohomologyIsoContinuousGroupCohomologyFunctor B K hK sbar q).app F)

end AlgebraicGeometry

end
