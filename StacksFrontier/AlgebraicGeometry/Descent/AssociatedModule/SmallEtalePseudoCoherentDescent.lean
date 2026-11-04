module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentForward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceBoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.SliceApproximationBridge
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TopCohomologyFinitenessGeneral
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.CyclesLiftGeneral
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence along the comparison of the small étale and Zariski sites

Let `S` be a scheme, let `E` be an object of `D(𝒪_S)` and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)`
be the comparison of ringed sites. Then `E` is `m`-pseudo-coherent on the small Zariski site of
`S` if and only if `ε^*E` is `m`-pseudo-coherent on the small étale site of `S`. This module proves
the implication from the étale side to the Zariski side and assembles the equivalence.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sliceAssociatedModule`: `ε_V^*`, the associated-module functor
  of the small étale site of an open `V` of `S`.
* `AlgebraicGeometry.SmallEtale.sliceAssociatedModuleUnitIso`: `ε_V^*` carries the structure
  sheaf to the structure sheaf.
* `AlgebraicGeometry.SmallEtale.associatedModuleOverComplexIso`: restricting a complex to the slice
  over `V` and applying `ε_V^*` is applying `ε^*` and restricting to the slice over `ε(V)`.
* `AlgebraicGeometry.SmallEtale.opensExtendComplex`: the extension of a complex of
  `𝒪_S|_V`-modules to a complex of `𝒪_S`-modules, and `opensExtendComplexIso`: it restricts back
  to the original complex.
* `AlgebraicGeometry.SmallEtale.restrictComplexHomologyIso`: the cohomology of a restriction is
  the restriction of the cohomology.
* `AlgebraicGeometry.SmallEtale.SliceEtaleClause`: `ε_V^*K` is `m`-pseudo-coherent on the small
  étale site of an open `V` of `S`.

## Main results

* `AlgebraicGeometry.SmallEtale.isStrictlyPerfect_sliceAssociatedModule`: `ε_V^*` carries a
  strictly perfect complex to a strictly perfect complex.
* `AlgebraicGeometry.SmallEtale.isFiniteType_homology_over_of_sliceEtaleClause`: finite type of
  the top cohomology sheaf descends along `ε` on a Zariski slice.
* `AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_over_of_gap`: if `ε_W^*(𝒦|_W)` is
  `m`-pseudo-coherent for every open `W ≤ V` and the cohomology of `𝒦` vanishes on `V` above
  `m + k`, then `𝒦|_V` is `m`-pseudo-coherent.
* `AlgebraicGeometry.SmallEtale.sliceEtaleClause_of_isPseudoCoherentFromSmallEtale`: if `ε^*E` is
  `m`-pseudo-coherent, then so is `ε_W^*(𝒦|_W)` for every open `W` and every complex `𝒦`
  representing `E`.
* `AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent_of_slices`: if `ε^*E` is
  `m`-pseudo-coherent then so is `E`, for any derived-category models of the slices of the two
  sites.
* `AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent`: if `ε^*E` is
  `m`-pseudo-coherent then so is `E`.
* `AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule`: `E` is `m`-pseudo-coherent if
  and only if `ε^*E` is.
* `AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule_allDegrees`: `E` is
  pseudo-coherent if and only if `ε^*E` is.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08FX](https://stacks.math.columbia.edu/tag/08FX)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 09VA](https://stacks.math.columbia.edu/tag/09VA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

universe u d d' dz de

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sheafification on the slices of the small étale ringed site -/

/-- Abelian presheaves on a localization of the small étale ringed site have a left exact
sheafification. -/
public instance hasSheafify_smallEtaleRingedSiteOver (T : SmallEtale B S hS) :
    HasSheafify ((smallEtaleRingedSite B S hS).over T).J AddCommGrpCat.{u} :=
  hasSheafify_smallEtaleOver B S hS T

/-- Weak equivalences of abelian presheaves on a localization of the small étale ringed site are
the locally bijective maps. -/
public instance wEqualsLocallyBijective_smallEtaleRingedSiteOver (T : SmallEtale B S hS) :
    ((smallEtaleRingedSite B S hS).over T).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs (((topology B S hS).over T).WEqualsLocallyBijective AddCommGrpCat.{u})

/-- Abelian presheaves on a slice of a localization of the small étale ringed site have a left
exact sheafification. -/
public instance hasSheafify_smallEtaleRingedSiteOverOver (T : SmallEtale B S hS) :
    ∀ U : ((smallEtaleRingedSite B S hS).over T).C,
      HasSheafify (((smallEtaleRingedSite B S hS).over T).J.over U) AddCommGrpCat.{u} :=
  fun U => hasSheafify_smallEtaleOverOver B S hS T U

/-- Weak equivalences of abelian presheaves on a slice of a localization of the small étale
ringed site are the locally bijective maps. -/
public instance wEqualsLocallyBijective_smallEtaleRingedSiteOverOver (T : SmallEtale B S hS) :
    ∀ U : ((smallEtaleRingedSite B S hS).over T).C,
      (((smallEtaleRingedSite B S hS).over T).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  fun U => wEqualsLocallyBijective_smallEtaleOverOver B S hS T U

/-! ### The associated-module functor of the small étale site of an open -/

/-- `ε_V^*`, the associated-module functor of the small étale site of an open `V` of `S`: the
pullback along the localized comparison `AlgebraicGeometry.SmallEtale.sliceStructureMap`. -/
public noncomputable abbrev sliceAssociatedModule (V : S.Opens) :
    SheafOfModules.{u} (S.ringCatSheaf.over V) ⥤
      SheafOfModules.{u} ((structureSheaf B S hS).over ((opensToSmallEtale B S hS).obj V)) :=
  SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)

/-- `ε_V^*` is additive, being a left adjoint. -/
public instance additive_sliceAssociatedModule (V : S.Opens) :
    (sliceAssociatedModule B S hS V).Additive :=
  SheafOfModules.pullback_additive (sliceStructureMap B S hS V)

/-- `ε_V^*` is left exact. -/
public instance preservesFiniteLimits_sliceAssociatedModule (V : S.Opens) :
    PreservesFiniteLimits (sliceAssociatedModule B S hS V) :=
  preservesFiniteLimits_pullback_sliceStructureMap B S hS V

/-- `ε_V^*` is right exact, being a left adjoint. -/
public instance preservesFiniteColimits_sliceAssociatedModule (V : S.Opens) :
    PreservesFiniteColimits (sliceAssociatedModule B S hS V) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0}
    (F := sliceAssociatedModule B S hS V)

/-- `ε_V^*` carries the structure sheaf of the Zariski slice to the structure sheaf of the étale
slice. -/
public noncomputable def sliceAssociatedModuleUnitIso (V : S.Opens) :
    (sliceAssociatedModule B S hS V).obj (SheafOfModules.unit (S.ringCatSheaf.over V)) ≅
      SheafOfModules.unit ((structureSheaf B S hS).over ((opensToSmallEtale B S hS).obj V)) :=
  asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))

/-- `ε_V^*` carries a strictly perfect complex to a strictly perfect complex. -/
public theorem isStrictlyPerfect_sliceAssociatedModule (V : S.Opens)
    {P : CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over V)) ℤ}
    (hP : IsStrictlyPerfect (S.ringCatSheaf.over V) P) :
    IsStrictlyPerfect ((structureSheaf B S hS).over ((opensToSmallEtale B S hS).obj V))
      (((sliceAssociatedModule B S hS V).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  SheafOfModules.isStrictlyPerfect_map (sliceAssociatedModule B S hS V)
    (sliceAssociatedModuleUnitIso B S hS V) hP

/-- `ε^*`, as the pullback `SheafOfModules.pullback (structureMap B S hS)`, is additive. -/
public instance additive_pullback_structureMap :
    (SheafOfModules.pullback.{u} (structureMap B S hS)).Additive :=
  SheafOfModules.pullback_additive (structureMap B S hS)

/-- On cochain complexes, restricting a complex of `𝒪_S`-modules to the slice over an open `V`
and then applying `ε_V^*` is applying `ε^*` and restricting to the slice over `ε(V)`. -/
public noncomputable def associatedModuleOverComplexIso (V : S.Opens) :
    (SheafOfModules.overFunctor.{u} S.ringCatSheaf V).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (sliceAssociatedModule B S hS V).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (SheafOfModules.pullback.{u} (structureMap B S hS)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
          ((opensToSmallEtale B S hS).obj V)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (SheafOfModules.overFunctor.{u} S.ringCatSheaf V ⋙
        sliceAssociatedModule B S hS V)) (ComplexShape.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (associatedModuleOverIso B S hS V) (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (SheafOfModules.pullback.{u} (structureMap B S hS) ⋙
          SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
            ((opensToSmallEtale B S hS).obj V))) (ComplexShape.up ℤ)).symm

/-! ### Extending a complex from a Zariski slice to the whole of `S` -/

/-- The section `AlgebraicGeometry.SmallEtale.opensRestrictionSection` of restriction of
`𝒪_S`-modules to the slice over an open `V` is additive. -/
public instance additive_opensRestrictionSection (V : S.Opens) :
    (opensRestrictionSection S V).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The extension of a complex of `𝒪_S|_V`-modules to a complex of `𝒪_S`-modules: the
degreewise image under the section
`AlgebraicGeometry.SmallEtale.opensRestrictionSection` of restriction to the slice over `V`. -/
public noncomputable def opensExtendComplex (V : S.Opens)
    (K : CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over V)) ℤ) :
    CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ :=
  ((opensRestrictionSection S V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The extension `opensExtendComplex S V K` of a complex `K` of `𝒪_S|_V`-modules restricts back
to `K`. -/
public noncomputable def opensExtendComplexIso (V : S.Opens)
    (K : CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over V)) ℤ) :
    S.zariskiRingedSite.restrictComplex (opensExtendComplex S V K) V ≅ K :=
  (Functor.mapHomologicalComplexCompIso (opensRestrictionSectionIso S V)
      (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K

/-! ### Cohomology of a restriction -/

/-- The cohomology of the restriction of a complex to the slice over `V` is the restriction of
its cohomology. -/
public noncomputable def restrictComplexHomologyIso (V : S.Opens)
    (𝒦 : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ) (j : ℤ) :
    (S.zariskiRingedSite.restrictComplex 𝒦 V).homology j ≅ (𝒦.homology j).over V :=
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} S.ringCatSheaf V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have : PreservesFiniteColimits (SheafOfModules.overFunctor.{u} S.ringCatSheaf V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  have : (SheafOfModules.overFunctor.{u} S.ringCatSheaf V).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  ShortComplex.mapHomologyIso (𝒦.sc j) (SheafOfModules.overFunctor.{u} S.ringCatSheaf V)

/-- A functor `F` that is exact between abelian categories carries an isomorphism `Q K ≅ E` in the
derived category to an isomorphism `Q (F K) ≅ F E`. -/
private noncomputable def mapDerivedCategoryIso {C₁ : Type*} [Category C₁] [Abelian C₁]
    [HasDerivedCategory C₁] {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : CochainComplex C₁ ℤ} {E : DerivedCategory C₁} (e : DerivedCategory.Q.obj K ≅ E) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      F.mapDerivedCategory.obj E :=
  (F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso e

/-! ### Étale pseudo-coherence at an open of `S` -/

section Descent

variable [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]
  [hZar : ∀ W : S.Opens, HasDerivedCategory.{dz} (SheafOfModules.{u} (S.ringCatSheaf.over W))]
  [hEt : ∀ T : SmallEtale B S hS,
    HasDerivedCategory.{de} (SheafOfModules.{u} ((structureSheaf B S hS).over T))]

/-- The derived-category model of a Zariski slice, at the
`AlgebraicGeometry.RingedSite.ringSheaf` spelling of the localized ringed site. -/
local instance zariskiOverHasDerivedCategory (W : S.Opens) :
    HasDerivedCategory.{dz} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.zariskiRingedSite.over W).O)) :=
  hZar W

/-- The derived-category model of an étale slice, at the
`AlgebraicGeometry.RingedSite.ringSheaf` spelling of the localized ringed site. -/
local instance smallEtaleOverHasDerivedCategory (T : SmallEtale B S hS) :
    HasDerivedCategory.{de}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS).over T).O)) :=
  hEt T

/-- The derived-category models of the slices of the small étale ringed site, at the
`AlgebraicGeometry.RingedSite.ringSheaf` spelling of its structure sheaf. -/
local instance smallEtaleRingSheafOverHasDerivedCategory :
    ∀ T : (smallEtaleRingedSite B S hS).C, HasDerivedCategory.{de}
      (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).over T)) :=
  fun T => hEt T

/-- The derived-category models of the slices of the small Zariski ringed site, at the
`AlgebraicGeometry.RingedSite.ringSheaf` spelling of its structure sheaf. -/
local instance zariskiRingSheafOverHasDerivedCategory :
    ∀ V : S.zariskiRingedSite.C, HasDerivedCategory.{dz}
      (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O).over V)) :=
  fun V => hZar V

/-- The complex `ε_V^*K` of
`𝒪_{V,étale}`-modules is `m`-pseudo-coherent on the small étale site of `V`, that is on the
localization of the small étale ringed site of `S` at `ε(V)`. -/
public abbrev SliceEtaleClause (V : S.Opens)
    (K : CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over V)) ℤ) (m : ℤ) : Prop :=
  ((smallEtaleRingedSite B S hS).over ((opensToSmallEtale B S hS).obj V)).IsPseudoCoherentFrom
    (DerivedCategory.Q.obj
      (((sliceAssociatedModule B S hS V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) m

omit [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))] hZar in
/-- Let `𝒦` be a complex of `𝒪_S`-modules, let `V` be an open of `S` and let `m ≤ b`. If
`ε_V^*(𝒦|_V)` is `m`-pseudo-coherent on the small étale site of `V` and the cohomology of `𝒦`
vanishes on `V` above `b`, then `H^b(𝒦)|_V` is of finite type. -/
public theorem isFiniteType_homology_over_of_sliceEtaleClause (V : S.Opens)
    (𝒦 : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ) (m b : ℤ) (hmb : m ≤ b)
    (hét : SliceEtaleClause B S hS V (S.zariskiRingedSite.restrictComplex 𝒦 V) m)
    (hvanish : ∀ j : ℤ, b < j → IsZero ((𝒦.homology j).over V)) :
    SheafOfModules.IsFiniteType ((𝒦.homology b).over V) := by
  set F := sliceAssociatedModule B S hS V
  set L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (S.zariskiRingedSite.restrictComplex 𝒦 V)
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  have hLhom : ∀ j : ℤ, L.homology j ≅ F.obj ((𝒦.homology j).over V) := fun j =>
    @ShortComplex.mapHomologyIso _ _ _ _ _ _
      ((S.zariskiRingedSite.restrictComplex 𝒦 V :
        CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over V)) ℤ).sc j) F
      (Functor.preservesZeroMorphisms_of_additive F)
      inferInstance inferInstance
      (@Functor.PreservesHomology.preservesLeftHomologyOf _ _ _ _ _ _ F
        (Functor.preservesZeroMorphisms_of_additive F)
        ((S.zariskiRingedSite.restrictComplex 𝒦 V :
          CochainComplex (SheafOfModules.{u} (S.ringCatSheaf.over V)) ℤ).sc j)
        ‹F.PreservesHomology›) ≪≫
      F.mapIso (restrictComplexHomologyIso S V 𝒦 j)
  have hLb : ((smallEtaleRingedSite B S hS).over
      ((opensToSmallEtale B S hS).obj V)).IsPseudoCoherentFrom (DerivedCategory.Q.obj L) b :=
    RingedSite.isPseudoCoherentFrom_mono_general _ _ hét hmb
  have hvan : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS).over ((opensToSmallEtale B S hS).obj V)).O)) i).obj
            (DerivedCategory.Q.obj L)) := by
    intro i hi
    refine IsZero.of_iso (IsZero.of_iso (F.map_isZero (hvanish i hi)) (hLhom i)) ?_
    exact (DerivedCategory.homologyFunctorFactors _ i).app L
  have hftL := RingedSite.isFiniteType_homology_general
    ((smallEtaleRingedSite B S hS).over ((opensToSmallEtale B S hS).obj V))
    (DerivedCategory.Q.obj L) b hLb hvan
  refine isFiniteType_over_of_isFiniteType_over_associatedModule B S hS V (𝒦.homology b) ?_
  refine Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso ?_ hftL
  exact (DerivedCategory.homologyFunctorFactors _ b).app L ≪≫ hLhom b ≪≫
    (associatedModuleOverIso B S hS V).app (𝒦.homology b)

omit [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))] in
/-- Let `𝒦` be a complex of `𝒪_S`-modules, let `V` be an open of `S` and let `m : ℤ`. Suppose
that for every open `W ≤ V` the complex `ε_W^*(𝒦|_W)` is `m`-pseudo-coherent on the small étale
site of `W`, and that the cohomology of `𝒦` vanishes on `V` above `m + k`. Then `𝒦|_V` is
`m`-pseudo-coherent on the localized small Zariski ringed site over `V`. -/
public theorem isPseudoCoherentFrom_over_of_gap (k : ℕ) :
    ∀ (m : ℤ) (V : S.Opens) (𝒦 : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ),
      (∀ W : S.Opens, W ≤ V →
        SliceEtaleClause B S hS W (S.zariskiRingedSite.restrictComplex 𝒦 W) m) →
      (∀ j : ℤ, m + (k : ℤ) < j → IsZero ((𝒦.homology j).over V)) →
      (S.zariskiRingedSite.over V).IsPseudoCoherentFrom
        (DerivedCategory.Q.obj (S.zariskiRingedSite.restrictComplex 𝒦 V)) m := by
  have hpc : ∀ (V : S.Opens) (𝒦 : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ) (m b : ℤ),
      m ≤ b → SliceEtaleClause B S hS V (S.zariskiRingedSite.restrictComplex 𝒦 V) m →
      (∀ j : ℤ, b < j → IsZero ((𝒦.homology j).over V)) →
      (S.zariskiRingedSite.over V).IsPseudoCoherentComplexFrom
        (S.zariskiRingedSite.restrictComplex 𝒦 V) b := fun V 𝒦 m b hmb hét hv =>
    RingedSite.isPseudoCoherentComplexFrom_of_isFiniteType_homology_general
      (S.zariskiRingedSite.over V) (S.zariskiRingedSite.restrictComplex 𝒦 V) b
      (fun j hj => IsZero.of_iso (hv j hj) (restrictComplexHomologyIso S V 𝒦 j))
      (Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
        (restrictComplexHomologyIso S V 𝒦 b).symm
        (isFiniteType_homology_over_of_sliceEtaleClause B S hS V 𝒦 m b hmb hét hv))
  induction k with
  | zero =>
    intro m V 𝒦 hét hvan
    exact ⟨_, hpc V 𝒦 m m le_rfl (hét V le_rfl) fun j hj => hvan j (by push_cast; omega),
      ⟨Iso.refl _⟩⟩
  | succ k ih =>
    intro m V 𝒦 hét hvan
    have hpcb := hpc V 𝒦 m (m + (k : ℤ) + 1) (by omega) (hét V le_rfl)
      fun j hj => hvan j (by push_cast; omega)
    have hsieve :=
      RingedSite.approximationSieve_mem_of_isPseudoCoherentComplexFrom_over
        S.zariskiRingedSite 𝒦 (m + (k : ℤ) + 1) V hpcb
    refine RingedSite.isPseudoCoherentFrom_over_restrictComplex_of_locally
      S.zariskiRingedSite 𝒦 m V _ hsieve ?_
    intro W g hW
    obtain ⟨P, hP, α, hαiso, hαepi⟩ := hW
    obtain ⟨Cn, β, γ, hT⟩ := distinguished_cocone_triangle (DerivedCategory.Q.map α)
    have hCvan : ∀ j : ℤ, m + (k : ℤ) + 1 ≤ j →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.zariskiRingedSite.over W).O)) j).obj Cn) :=
      isZero_homology_obj₃_of_distinguished (m + (k : ℤ) + 1) _ hT
        (fun j hj => isIso_homologyFunctor_map_Q_map α j (hαiso j hj))
        (epi_homologyFunctor_map_Q_map α (m + (k : ℤ) + 1) hαepi)
    set Ccpx := DerivedCategory.Q.objPreimage Cn
    have eC : DerivedCategory.Q.obj Ccpx ≅ Cn := DerivedCategory.Q.objObjPreimageIso Cn
    set 𝒞 := opensExtendComplex S W Ccpx
    have e𝒞 : S.zariskiRingedSite.restrictComplex 𝒞 W ≅ Ccpx := opensExtendComplexIso S W Ccpx
    have hvanC : ∀ j : ℤ, m + (k : ℤ) < j → IsZero ((𝒞.homology j).over W) := by
      intro j hj
      refine IsZero.of_iso (hCvan j (by omega)) ?_
      refine (restrictComplexHomologyIso S W 𝒞 j).symm ≪≫ ?_
      refine (HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (S.ringCatSheaf.over W)) (ComplexShape.up ℤ) j).mapIso e𝒞 ≪≫ ?_
      exact ((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (S.ringCatSheaf.over W)) j).app Ccpx).symm ≪≫
          (DerivedCategory.homologyFunctor (SheafOfModules.{u} (S.ringCatSheaf.over W)) j).mapIso eC
    have hétC : ∀ W' : S.Opens, W' ≤ W →
        SliceEtaleClause B S hS W' (S.zariskiRingedSite.restrictComplex 𝒞 W') m := by
      intro W' hW'
      set h : W' ⟶ W := homOfLE hW'
      set R := SheafOfModules.overMap.{u} S.ringCatSheaf h
      set G := sliceAssociatedModule B S hS W'
      have : PreservesFiniteLimits R :=
        Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits h
      have : PreservesFiniteColimits R :=
        Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits h
      have : R.Additive := Functor.additive_of_preserves_binary_products R
      have hT₂ : (G.mapDerivedCategory.mapTriangle.obj
          (R.mapDerivedCategory.mapTriangle.obj (Triangle.mk (DerivedCategory.Q.map α) β γ))) ∈
          distinguishedTriangles :=
        G.mapDerivedCategory.map_distinguished _ (R.mapDerivedCategory.map_distinguished _ hT)
      have h₁ : ((smallEtaleRingedSite B S hS).over
          ((opensToSmallEtale B S hS).obj W')).IsPseudoCoherentFrom
          (G.mapDerivedCategory.obj (R.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
          (m + 1) := by
        refine RingedSite.isPseudoCoherentFrom_of_iso _ (m + 1) ?_
          (mapDerivedCategoryIso G (mapDerivedCategoryIso R (Iso.refl _))).symm
        refine RingedSite.isPseudoCoherentFrom_Q_of_isStrictlyPerfect_general
          ((smallEtaleRingedSite B S hS).over ((opensToSmallEtale B S hS).obj W')) _ ?_ (m + 1)
        exact isStrictlyPerfect_sliceAssociatedModule B S hS W'
          (RingedSite.isStrictlyPerfect_overMap S.ringCatSheaf h hP)
      have h₂ : ((smallEtaleRingedSite B S hS).over
          ((opensToSmallEtale B S hS).obj W')).IsPseudoCoherentFrom
          (G.mapDerivedCategory.obj (R.mapDerivedCategory.obj
            (DerivedCategory.Q.obj (S.zariskiRingedSite.restrictComplex 𝒦 W)))) m := by
        refine RingedSite.isPseudoCoherentFrom_of_iso _ m
          (hét W' (hW'.trans (leOfHom g))) ?_
        refine (mapDerivedCategoryIso G (mapDerivedCategoryIso R (Iso.refl _))).symm ≪≫ ?_
        exact DerivedCategory.Q.mapIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          ((Stacks.SheafOfModules.overFunctorMapComplexIso.{u} S.ringCatSheaf h).app 𝒦))
      refine RingedSite.isPseudoCoherentFrom_of_iso _ m
        (RingedSite.isPseudoCoherentFrom_of_distinguished_one_general
          _ m _ hT₂ h₁ h₂) ?_
      exact DerivedCategory.Q.mapIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          (((Stacks.SheafOfModules.overFunctorMapComplexIso.{u} S.ringCatSheaf h).app 𝒞).symm ≪≫
            (R.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e𝒞)) ≪≫
        mapDerivedCategoryIso G (mapDerivedCategoryIso R eC)
    have hCm : (S.zariskiRingedSite.over W).IsPseudoCoherentFrom
        (DerivedCategory.Q.obj (S.zariskiRingedSite.restrictComplex 𝒞 W)) m :=
      ih m W 𝒞 hétC hvanC
    refine RingedSite.isPseudoCoherentFrom_of_distinguished_two_general
      (S.zariskiRingedSite.over W) m _ hT
      (RingedSite.isPseudoCoherentFrom_Q_of_isStrictlyPerfect_general
        (S.zariskiRingedSite.over W) P hP m)
      ?_
    exact RingedSite.isPseudoCoherentFrom_of_iso _ m hCm
      (eC.symm ≪≫ DerivedCategory.Q.mapIso e𝒞.symm)

/-! ### Eliminating the induction variable -/

omit hZar in
/-- If `ε^*E` is
`m`-pseudo-coherent on the small étale site of `S`, then for every open `W` of `S` and every
complex `𝒦` representing `E` the complex `ε_W^*(𝒦|_W)` is `m`-pseudo-coherent on the small étale
site of `W`. -/
public theorem sliceEtaleClause_of_isPseudoCoherentFromSmallEtale
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS).IsPseudoCoherentFrom
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) m)
    (𝒦 : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (eK : DerivedCategory.Q.obj 𝒦 ≅ E) (W : S.Opens) :
    SliceEtaleClause B S hS W (S.zariskiRingedSite.restrictComplex 𝒦 W) m := by
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
      ((opensToSmallEtale B S hS).obj W)) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits _
  have : PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
      ((opensToSmallEtale B S hS).obj W)) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits _
  refine RingedSite.isPseudoCoherentFrom_of_iso _ m
    (RingedSite.isPseudoCoherentFrom_derivedRestriction_general
      (smallEtaleRingedSite B S hS)
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) m hE
      ((opensToSmallEtale B S hS).obj W)) ?_
  refine (DerivedCategory.Q.mapIso
    ((associatedModuleOverComplexIso B S hS W).app 𝒦)) ≪≫ ?_
  exact mapDerivedCategoryIso (SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
      ((opensToSmallEtale B S hS).obj W))
    (mapDerivedCategoryIso (associatedModuleOfSheaf B S hS) eK)

/-- Given derived-category models of the slices of the small Zariski and small étale sites of
`S`: if `ε^*E` is `m`-pseudo-coherent on the small étale site of `S`, then `E` is
`m`-pseudo-coherent on the small Zariski site. -/
public theorem associatedModuleToPseudoCoherent_of_slices
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS).IsPseudoCoherentFrom
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) m) :
    @RingedSite.IsPseudoCoherentFrom.{_, _, _, u, d} S.zariskiRingedSite
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (inferInstance : HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)) E m := by
  classical
  obtain ⟨𝒦, eK⟩ : Σ' 𝒦 : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ,
      DerivedCategory.Q.obj 𝒦 ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  have hétAll : ∀ W : S.Opens,
      SliceEtaleClause B S hS W (S.zariskiRingedSite.restrictComplex 𝒦 W) m := fun W =>
    sliceEtaleClause_of_isPseudoCoherentFromSmallEtale B S hS E m hE 𝒦 eK W
  have hhom : ∀ (j : ℤ) (V : S.Opens), ((𝒦.homology j).over V) ≅
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) j).obj E).over V) :=
    fun j V => (SheafOfModules.overFunctor.{u} S.ringCatSheaf V).mapIso
      (((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} S.ringCatSheaf) j).app 𝒦).symm ≪≫
          (DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) j).mapIso eK)
  have key : ∀ (V : S.Opens) (b : ℤ), (∀ j : ℤ, b < j →
        IsZero ((((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} S.ringCatSheaf) j).obj E)).over V)) →
      (S.zariskiRingedSite.over V).IsPseudoCoherentFrom
        (DerivedCategory.Q.obj (S.zariskiRingedSite.restrictComplex 𝒦 V)) m := by
    intro V b hb
    refine isPseudoCoherentFrom_over_of_gap B S hS (b - m).toNat m V 𝒦
      (fun W _ => hétAll W) fun j hj => ?_
    refine IsZero.of_iso (hb j ?_) (hhom j V)
    have := Int.self_le_toNat (b - m)
    omega
  refine @RingedSite.isPseudoCoherentFrom_of_locally_general.{_, _, _, d, dz}
    S.zariskiRingedSite inferInstance inferInstance inferInstance inferInstance
    (inferInstance : HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf))
    (fun openSet => hZar openSet) E m fun U => ?_
  refine ⟨(Sieve.ofObjects
    (Subtype.val : {V : S.Opens // ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} S.ringCatSheaf) j).obj E)).over V)} → S.Opens) U).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact boundedOpens_mem_grothendieckTopology B S hS E m hE U
  · intro V f hf
    obtain ⟨⟨V', b, hb⟩, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff _ f).mp hf
    refine RingedSite.isPseudoCoherentFrom_of_iso _ m
      (key V b fun j hj => Stacks.SheafOfModules.isZero_over_of_hom _ c (hb j hj)) ?_
    exact (mapDerivedCategoryIso (SheafOfModules.overFunctor.{u} S.ringCatSheaf V) eK).symm

end Descent

/-! ### Pseudo-coherence on the small Zariski and small étale sites -/

section Main

variable [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- A model of `D(𝒪_S)` at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling in which the
pseudo-coherence predicate asks for one. -/
local instance hasDerivedCategory_zariskiRingedSite :
    HasDerivedCategory.{d}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) :=
  inferInstanceAs (HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf))

/-- If `ε^*E` is `m`-pseudo-coherent on the small étale site of `S` then `E` is
`m`-pseudo-coherent on the small Zariski site of `S`, `ε` being the comparison of ringed sites and
the derived functor being `CategoryTheory.Functor.mapDerivedCategory` of the associated-module
functor. -/
@[stacks 08HE "clause (2) ⇒ (1): if `ε^*E` is `m`-pseudo-coherent on the small étale site of
  `S` then `E` is `m`-pseudo-coherent on the small Zariski site of `S`, `ε` being the
  comparison of ringed sites of Stacks 08H7."]
public theorem associatedModuleToPseudoCoherent
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (m : ℤ) :
    AssociatedModuleToPseudoCoherent B S hS E m := by
  intro hE
  have hZar : ∀ W : S.Opens, HasDerivedCategory (SheafOfModules.{u} (S.ringCatSheaf.over W)) :=
    fun _ => HasDerivedCategory.standard _
  have hEt : ∀ T : SmallEtale B S hS,
      HasDerivedCategory (SheafOfModules.{u} ((structureSheaf B S hS).over T)) :=
    fun _ => HasDerivedCategory.standard _
  exact associatedModuleToPseudoCoherent_of_slices B S hS E m hE

/-- Let `S` be a scheme, let `E` be an object of `D(𝒪_S)` and let `m` be an integer. Then `E` is
`m`-pseudo-coherent on the small Zariski site of `S` if and only if `ε^*E` is `m`-pseudo-coherent
on the small étale site of `S`, where `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` is the comparison of
ringed sites. -/
@[stacks 08HE]
public theorem pseudoCoherentIffAssociatedModule
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (m : ℤ) :
    PseudoCoherentIffAssociatedModule B S hS E m :=
  pseudoCoherentIff_of_imp B S hS E m
    (pseudoCoherentToAssociatedModule_of_slice_exact B S hS E m)
    (associatedModuleToPseudoCoherent B S hS E m)

/-- Let `S` be a scheme and let `E` be an object of `D(𝒪_S)`. Then `E` is pseudo-coherent on
the small Zariski site of `S` if and only if `ε^*E` is pseudo-coherent on the small étale site of
`S`. -/
public theorem pseudoCoherentIffAssociatedModule_allDegrees
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    S.zariskiRingedSite.IsPseudoCoherent E ↔
      (smallEtaleRingedSite B S hS).IsPseudoCoherent
        ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) :=
  (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom S.zariskiRingedSite E).trans
    ((forall_congr' fun m => pseudoCoherentIffAssociatedModule B S hS E m).trans
      (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom
        (smallEtaleRingedSite B S hS) _).symm)

end Main

end AlgebraicGeometry.SmallEtale

end
