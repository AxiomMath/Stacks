module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ConnectiveCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CohomologySheavesOfADerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedExtOnAnOpen
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageAffine.BasisVanishing

/-!
# Connectivity of a derived pushforward detected on a basis

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `ℬ` be a basis for the topology
of `Y`, and let `K` be an object of the unbounded derived category `D(𝒪_X)` whose hypercohomology
over the inverse images of the members of `ℬ` vanishes in negative degrees:
`H^i(f⁻¹ V, K) = 0` for `V ∈ ℬ` and `i < 0`. Then

* the cohomology sheaves of `Rf_* K` vanish in negative degrees,
* `H^i(f⁻¹ V, K) = 0` for `i < 0` and **every** open `V ⊆ Y`, and
* the rule `V ↦ H^0(f⁻¹ V, K)` is a sheaf on `Y`.

This is [Stacks, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66), part (1).

Part (2) is the same statement for a pair `K`, `L` of objects of `D(𝒪_X)`: if
`Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V}) = 0` for `V ∈ ℬ` and `i < 0`, then that vanishing holds for every
open `V ⊆ Y`, and the rule `V ↦ Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` is a sheaf on `Y`.

## Main definitions

All in the namespace `Stacks.Cohomology.UnboundedHigherDirectImage`:

* `preimageRestrict`: restriction `K ↦ K|_{f⁻¹ V}` to the inverse image of an open, on derived
  categories.
* `preimageSectionsHomologyEquivShiftedHom`: the identification
  `H^i(f⁻¹ V, RSheafHom(K, L)) ≃+ Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V})`.
* `derivedPreimageHomPresheafValueEquiv`: the value on `V` of the presheaf
  `V ↦ H^0(f⁻¹ V, RSheafHom(K, L))` is the group of morphisms `K|_{f⁻¹ V} ⟶ L|_{f⁻¹ V}`.

## Main results

All in the namespace `Stacks.Cohomology.UnboundedHigherDirectImage`:

* `isZero_homologyDerivedPushforward_of_isBasis`: vanishing of a cohomology sheaf of `Rf_* K` from
  vanishing of hypercohomology on a basis.
* `isZero_homologyDerivedPreimageSections_of_isBasis`: the extension of negative-degree vanishing
  from a basis to all opens.
* `isSheaf_zerothDerivedPreimageCohomologyPresheaf`: the rule `V ↦ H^0(f⁻¹ V, K)` is a sheaf.
* `subsingleton_shiftedHom_preimageRestrict_of_isBasis`: part (2), the extension of negative-`Ext`
  vanishing from a basis to all opens.
* `isSheaf_derivedPreimageHomPresheaf`: part (2), the rule `V ↦ Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` is a
  sheaf.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D5X](https://stacks.math.columbia.edu/tag/0D5X)
* [Stacks Project, Tag 0BKM](https://stacks.math.columbia.edu/tag/0BKM)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray (derivedPreimageSections preimageSections
  homotopyPreimageSections derivedPreimageSectionsUnit)
open scoped ZeroObject

namespace Stacks.Cohomology.UnboundedHigherDirectImage

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_moduleSheaves

/-! ### Vanishing on a basis kills the sheafification -/

/-- The sheafification of a presheaf of `𝒪_Y`-modules vanishing on a basis of the topology of `Y`
is zero. -/
private lemma isZero_sheafification_of_isBasis (Y : RingedSpace.{u, u})
    {B : Set (Opens Y.carrier)} (hB : Opens.IsBasis B)
    (Q : PresheafOfModules.{u} (structureSheafRing Y).obj)
    (hQ : ∀ V ∈ B,
      IsZero ((PresheafOfModules.evaluation (structureSheafRing Y).obj (op V)).obj Q)) :
    IsZero ((PresheafOfModules.sheafification (𝟙 (structureSheafRing Y).obj)).obj Q) :=
  Stacks.Topology.BasisVanishing.isZero_sheafification_of_isZero_on_basis
    (R := structureSheafRing Y) Q hB fun V hV => Functor.map_isZero
      (forget₂ (ModuleCat ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat) (hQ V hV)

/-! ### Tag 0D66, part (1) -/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {B : Set (Opens Y.carrier)}
  (hB : Opens.IsBasis B) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

include hB in
/-- **Vanishing of the cohomology sheaves of `Rf_* K`.** If the degree-`i` hypercohomology
`H^i(f⁻¹ V, K)` vanishes for every `V` in a basis of the topology of `Y`, then the degree-`i`
cohomology sheaf of `Rf_* K` vanishes. -/
@[stacks 0D66 "negative_sheaves"]
theorem isZero_homologyDerivedPushforward_of_isBasis (i : ℤ)
    (hK : ∀ V ∈ B, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
        ((derivedPreimageSections f V).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) i).obj
      ((derivedPushforward f).obj K)) :=
  (isZero_sheafification_of_isBasis Y hB (derivedPreimageCohomologyPresheaf f K i) fun V hV =>
    (hK V hV).of_iso ((preimageCohomologyEvaluationIso f V i).app K)).of_iso
      ((higherDirectImageIsoSheafifyPreimageCohomology f i).app K)

include hB in
/-- **Negative hypercohomology over every inverse image.** If `H^i(f⁻¹ V, K) = 0` for `i < 0` and
every `V` in a basis of the topology of `Y`, then `H^i(f⁻¹ V, K) = 0` for `i < 0` and *every* open
`V ⊆ Y`. -/
@[stacks 0D66 "negative_hypercohomology"]
theorem isZero_homologyDerivedPreimageSections_of_isBasis
    (hK : ∀ V ∈ B, ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
        ((derivedPreimageSections f V).obj K)))
    (V : Opens Y.carrier) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
        ((derivedPreimageSections f V).obj K)) :=
  (Stacks.Cohomology.Connective.isZero_homology_derivedSections_of_isZero_negative Y
    ((derivedPushforward f).obj K)
    (fun j hj => isZero_homologyDerivedPushforward_of_isBasis f hB K j
      fun W hW => hK W hW j hj) V i hi).of_iso ((preimageCohomologyIso f V i).app K)

include hB in
/-- **The rule `V ↦ H^0(f⁻¹ V, K)` is a sheaf.** If `H^i(f⁻¹ V, K) = 0` for `i < 0` and every `V`
in a basis of the topology of `Y`, then the presheaf of `𝒪_Y`-modules `V ↦ H^0(f⁻¹ V, K)` — that
is `derivedPreimageCohomologyPresheaf f K 0`, whose values are identified with `H^0(f⁻¹ V, K)` by
`preimageCohomologyEvaluationIso` — satisfies the sheaf condition. -/
@[stacks 0D66 "zeroth_sheaf"]
theorem isSheaf_zerothDerivedPreimageCohomologyPresheaf
    (hK : ∀ V ∈ B, ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
        ((derivedPreimageSections f V).obj K))) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y.carrier)
      (derivedPreimageCohomologyPresheaf f K 0).presheaf := by
  obtain ⟨e⟩ := Stacks.Cohomology.Connective.nonempty_zerothCohomologyPresheafIsoSections Y
    ((derivedPushforward f).obj K)
    (fun j hj => isZero_homologyDerivedPushforward_of_isBasis f hB K j
      fun W hW => hK W hW j hj)
  exact (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).mapIso e)).mpr
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
        ((derivedPushforward f).obj K)).isSheaf

/-! ### Tag 0D66, part (2) -/

section HomSheaf

open Stacks.SheafOfModules (homSheafComplex homSheafObject isKInjective_homSheafComplex
  homSheafComplexSectionHomologyEquiv isZero_homology_mapHomologicalComplex_iff
  homologyMapHomologicalComplexIso)

/-- **Restriction to the inverse image of an open**, as a functor on the unbounded derived
category: the functor induced on derived categories by restriction of sheaves of modules to the
slice site over `f⁻¹ V`, sending `K` to `K|_{f⁻¹ V}`. -/
abbrev preimageRestrict (f : X ⟶ Y) (V : Opens Y.carrier) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} ((structureSheafRing X).over ((opensMap f).obj V))) :=
  (SheafOfModules.overFunctor.{u} (structureSheafRing X) ((opensMap f).obj V)).mapDerivedCategory

/-- **Sections over an inverse image compute derived sections on a K-injective complex.** The
class of the complex of sections over `f⁻¹ V` of a K-injective complex `W`, taken as a module
over `Γ(V, 𝒪_Y)`, is `RΓ(f⁻¹ V, W)`. -/
def preimageSectionsKInjectiveIso (f : X ⟶ Y) (V : Opens Y.carrier)
    (W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hW : W.IsKInjective) :
    DerivedCategory.Q.obj
        (((preimageSections f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj W) ≅
      (derivedPreimageSections f V).obj (DerivedCategory.Q.obj W) :=
  letI := hW
  ((DerivedCategory.quotientCompQhIso
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))).app _).symm ≪≫
    DerivedCategory.Qh.mapIso
        (((preimageSections f V).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app W).symm ≪≫
      @asIso _ _ _ _ ((derivedPreimageSectionsUnit f V).app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
              (ComplexShape.up ℤ)).obj W))
          (Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
            (homotopyPreimageSections f V) (derivedPreimageSections f V)
            (derivedPreimageSectionsUnit f V) W) ≪≫
        (derivedPreimageSections f V).mapIso
          ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app W)

variable (f : X ⟶ Y) (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))

/-- **The hypercohomology of the internal Hom over an inverse image is an `Ext` group**
([Stacks, Tag 08DK], in every degree). For the complex `homSheafComplex` computing
`RSheafHom(K, L)`, the degree-`i` hypercohomology `H^i(f⁻¹ V, RSheafHom(K, L))` vanishes exactly
when `Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V})` does. -/
theorem isZero_homologyDerivedPreimageSections_homSheafObject_iff
    (V : Opens Y.carrier) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
          ((derivedPreimageSections f V).obj (homSheafObject X.sheaf K L))) ↔
      Subsingleton (ShiftedHom ((preimageRestrict f V).obj K)
        ((preimageRestrict f V).obj L) i) := by
  have e : (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
          ((derivedPreimageSections f V).obj (homSheafObject X.sheaf K L)) ≅
      (((preimageSections f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homSheafComplex X.sheaf K L)).homology i :=
    (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).mapIso
        (preimageSectionsKInjectiveIso f V (homSheafComplex X.sheaf K L)
          (isKInjective_homSheafComplex X.sheaf K L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors
          (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).app
        (((preimageSections f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (homSheafComplex X.sheaf K L))
  rw [e.isZero_iff,
    ← isZero_homology_mapHomologicalComplex_iff
      (forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u})
      (((preimageSections f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homSheafComplex X.sheaf K L)) i,
    AddCommGrpCat.isZero_iff_subsingleton]
  exact Equiv.subsingleton_congr
    (homSheafComplexSectionHomologyEquiv X.sheaf K L ((opensMap f).obj V) i).toEquiv

/-- **The hypercohomology of the internal Hom over an inverse image *is* the `Ext` group.** The
additive identification `H^i(f⁻¹ V, RSheafHom(K, L)) = Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V})` refining
`isZero_homologyDerivedPreimageSections_homSheafObject_iff`. -/
@[sga "7 VI 4.16" "more general"]
def preimageSectionsHomologyEquivShiftedHom (V : Opens Y.carrier) (i : ℤ) :
    ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).obj
          ((derivedPreimageSections f V).obj (homSheafObject X.sheaf K L)) : Type u) ≃+
      ShiftedHom ((preimageRestrict f V).obj K) ((preimageRestrict f V).obj L) i :=
  let G := forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}
  let P := ((preimageSections f V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (homSheafComplex X.sheaf K L)
  let e₁ := (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).mapIso
      (preimageSectionsKInjectiveIso f V (homSheafComplex X.sheaf K L)
        (isKInjective_homSheafComplex X.sheaf K L)).symm ≪≫
    (DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) i).app P
  let e₂ := G.mapIso e₁ ≪≫ (homologyMapHomologicalComplexIso G P i).symm
  e₂.addCommGroupIsoToAddEquiv.trans
    (homSheafComplexSectionHomologyEquiv X.sheaf K L ((opensMap f).obj V) i)

/-- **The value of the Hom presheaf on an open is the group of morphisms of the restrictions.**
The value on `V ⊆ Y` of the presheaf `derivedPreimageCohomologyPresheaf f (RSheafHom(K, L)) 0` is
the group of morphisms `K|_{f⁻¹ V} ⟶ L|_{f⁻¹ V}`. -/
def derivedPreimageHomPresheafValueEquiv (V : Opens Y.carrier) :
    ((derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L) 0).presheaf.obj
        (op V) : Type u) ≃+
      ((preimageRestrict f V).obj K ⟶ (preimageRestrict f V).obj L) :=
  (((forget₂ (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) AddCommGrpCat.{u}).mapIso
        ((preimageCohomologyEvaluationIso f V 0).app
          (homSheafObject X.sheaf K L))).addCommGroupIsoToAddEquiv).trans
    ((preimageSectionsHomologyEquivShiftedHom f K L V 0).trans
      (CategoryTheory.Linear.homCongr ℤ (Iso.refl _)
        ((shiftFunctorZero _ ℤ).app ((preimageRestrict f V).obj L))).toAddEquiv)

include hB in
/-- **Negative `Ext` over every inverse image.** If `Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V}) = 0` for
`i < 0` and every `V` in a basis of the topology of `Y`, then the same vanishing holds for `i < 0`
and *every* open `V ⊆ Y`. -/
@[stacks 0D66 "hom_negative_ext"]
theorem subsingleton_shiftedHom_preimageRestrict_of_isBasis
    (hExt : ∀ V ∈ B, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((preimageRestrict f V).obj K)
        ((preimageRestrict f V).obj L) i))
    (V : Opens Y.carrier) (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom ((preimageRestrict f V).obj K)
      ((preimageRestrict f V).obj L) i) :=
  (isZero_homologyDerivedPreimageSections_homSheafObject_iff f K L V i).mp
    (isZero_homologyDerivedPreimageSections_of_isBasis f hB (homSheafObject X.sheaf K L)
      (fun W hW j hj =>
        (isZero_homologyDerivedPreimageSections_homSheafObject_iff f K L W j).mpr
          (hExt W hW j hj)) V i hi)

include hB in
/-- **The rule `V ↦ Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` is a sheaf.** If
`Ext^i(K|_{f⁻¹ V}, L|_{f⁻¹ V}) = 0` for `i < 0` and every `V` in a basis of the topology of `Y`,
then the presheaf of `𝒪_Y`-modules `V ↦ Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` satisfies the sheaf
condition. Here the presheaf is `derivedPreimageCohomologyPresheaf f (RSheafHom(K, L)) 0`, whose
value on `V` is identified with `Hom(K|_{f⁻¹ V}, L|_{f⁻¹ V})` by
`derivedPreimageHomPresheafValueEquiv`. -/
@[stacks 0D66 "hom_sheaf"]
theorem isSheaf_derivedPreimageHomPresheaf
    (hExt : ∀ V ∈ B, ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((preimageRestrict f V).obj K)
        ((preimageRestrict f V).obj L) i)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y.carrier)
      (derivedPreimageCohomologyPresheaf f (homSheafObject X.sheaf K L) 0).presheaf :=
  isSheaf_zerothDerivedPreimageCohomologyPresheaf f hB (homSheafObject X.sheaf K L)
    fun W hW j hj =>
      (isZero_homologyDerivedPreimageSections_homSheafObject_iff f K L W j).mpr (hExt W hW j hj)

end HomSheaf

end Stacks.Cohomology.UnboundedHigherDirectImage

end
