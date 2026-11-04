module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ForgetComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjointAcyclicObjects
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.CellularMap
import StacksCore.Tactic.StacksAttribute

/-!
# The derived lower shriek of modules for the projection of a fibred category

Let `p : C ⥤ D` be a fibred category over a ringed site `(D, O_D)`, as in Stacks 08P8, with
`π : Sh(C) ⟶ Sh(D)`, `O_C = π⁻¹O_D`, `π_! ⊣ π^*` on sheaves of modules and `π_!^{Ab} ⊣ π⁻¹` on
abelian sheaves. Stacks 09CY reads off from Lemma 08PC the derived functors `Lπ_!` and
`Lπ_!^{Ab}`, left adjoint to `π^*` and `π⁻¹` on derived categories, with
`forget ∘ Lπ_! = Lπ_!^{Ab} ∘ forget`. This file proves the module half.

**Existence and adjunction.** By the criterion of Stacks 0794 (Stacks 07AC) the only input is
that `π_!` carries a bounded above acyclic complex of direct sums of the `j_{U!} O_U` to an
acyclic complex. The underlying abelian sheaf of `j_{U!} O_U` is `j_{U!} π_U⁻¹ O_{p(U)}`
(Stacks 08P4), which is the value of the left adjoint of the restriction along the cartesian lifts
at `U` (Stacks 08P9); that restriction is exact, preserves injectives and carries `π⁻¹ I` to the
injective `I|_{p(U)}`, so by dimension shifting `Ext^n(j_{U!} O_U, π⁻¹ I) = 0` for `n ≥ 1` — the
vanishing of Stacks 0D6X. Hence `π_!^{Ab}` keeps the underlying complex acyclic, and since
`forget ∘ π_! = π_!^{Ab} ∘ forget` (`isIso_moduleLowerShriekForgetComparison`) with `forget`
faithful and exact, so does `π_!`.

**The forgetful square.** The comparison `Lπ_!^{Ab} ∘ forget ⟶ forget ∘ Lπ_!` of Stacks 07AE is
the unique transformation compatible with the counits; it is an isomorphism as soon as
`Lπ_!^{Ab} ∘ forget` is a left derived functor of `π_!^{Ab} ∘ forget`. It is: `Lπ_!` is computed
on complexes cellular for the class of direct sums of the `j_{U!} O_U`, `forget` carries those
to complexes cellular for the class of `Ext`-acyclic abelian sheaves, and `Lπ_!^{Ab}` is
computed on the latter as well, the `Ext`-acyclic class satisfying the hypotheses of Stacks 0794.

## Main definitions

* `FibredCategorySituation.derivedModuleLowerShriekAtBaseModuleRing`: `Lπ_!`.
* `FibredCategorySituation.derivedModuleLowerShriekAdjunctionAtBaseModuleRing`:
  `Lπ_! ⊣ π^*` on the unbounded derived categories.
* `FibredCategorySituation.derivedModuleLowerShriekForgetComparison` and
  `FibredCategorySituation.derivedModuleLowerShriekForgetIso`: the comparison of Stacks 07AE and
  the isomorphism `forget ∘ Lπ_! ≅ Lπ_!^{Ab} ∘ forget`.

## Main results

* `Stacks.Cohomology.subsingleton_ext_leftAdjoint_obj`: dimension shifting against a left
  adjoint of an exact functor preserving injectives.
* `FibredCategorySituation.extAcyclic_toSheaf_extensionByZeroUnit_totalModuleRing`:
  Stacks 0D6X for `j_{U!} O_U`.
* `FibredCategorySituation.moduleLowerShriekAcyclic`: the acyclicity statement of Stacks 07AC for
  `π_!` on modules.
* `FibredCategorySituation.isIso_derivedModuleLowerShriekForgetComparison`:
  **`forget ∘ Lπ_! = Lπ_!^{Ab} ∘ forget`**.

## References

* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 08P9](https://stacks.math.columbia.edu/tag/08P9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology

universe t

/-- **Dimension shifting against a left adjoint.** Let `R : B ⥤ A` be an exact functor between
abelian categories which preserves injective objects and has a left adjoint `L`. Then
`Ext^n(L X, Y) = 0` for every `n ≥ 1`, every `X` and every `Y` with `R Y` injective. -/
theorem subsingleton_ext_leftAdjoint_obj {B : Type*} [Category* B] [Abelian B] [HasExt.{t} B]
    [EnoughInjectives B] {A : Type*} [Category* A] [Abelian A] (R : B ⥤ A)
    [R.PreservesZeroMorphisms] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [R.PreservesInjectiveObjects] {L : A ⥤ B} (adj : L ⊣ R) (X : A)
    (n : ℕ) (hn : 1 ≤ n) (Y : B) (hY : Injective (R.obj Y)) :
    Subsingleton (Abelian.Ext.{t} (L.obj X) Y n) := by
  refine subsingleton_ext_of_injective_map R (L.obj X) (fun Y Z g hg f => ?_) n hn Y hY
  refine ⟨(adj.homEquiv _ _).symm (adj.homEquiv _ _ f ≫ section_ (R.map g)), ?_⟩
  rw [← adj.homEquiv_naturality_right_symm, Category.assoc, IsSplitEpi.id, Category.comp_id,
    Equiv.symm_apply_apply]

end Stacks.Cohomology

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

universe uD vD uC vC w

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

section ExtAcyclic

variable (U : s.C)

/-- The adjunction whose right adjoint is the restriction along the cartesian lifts at `U`:
the inverse image along the localized projection `π_U`, followed by extension by zero along
`C/U ⥤ C`, is left adjoint to `s.cartesianLiftRestriction U`. -/
def cartesianLiftRestrictionAdjunction :
    (Over.post (X := U) s.p).sheafPushforwardContinuous AddCommGrpCat.{max w uD vD uC vC}
        (s.topology.over U) (s.base.J.over (s.p.obj U)) ⋙
      (Over.forget U).sheafPullback AddCommGrpCat.{max w uD vD uC vC} (s.topology.over U)
        s.topology ⊣
    s.cartesianLiftRestriction U :=
  letI := (localizedProjectionSection s U).cartesianSection_isContinuous
  ((localizedProjectionSection s U).cartesianSection_adjunction.sheafPushforwardContinuous
    (E := AddCommGrpCat.{max w uD vD uC vC}) (s.topology.over U)
    (s.base.J.over (s.p.obj U))).comp
    ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat.{max w uD vD uC vC}
      (s.topology.over U) s.topology)

/-- The restriction along the cartesian lifts at `U` preserves zero morphisms, being a composite
of two restrictions along functors of sites. -/
instance cartesianLiftRestriction_preservesZeroMorphisms :
    (s.cartesianLiftRestriction U).PreservesZeroMorphisms := by
  let := (localizedProjectionSection s U).cartesianSection_isContinuous
  have : (s.topology.overPullback AddCommGrpCat.{max w uD vD uC vC} U).Additive :=
    Functor.additive_sheafPushforwardContinuous (Over.forget U) (s.topology.over U) s.topology
      AddCommGrpCat.{max w uD vD uC vC}
  have : ((localizedProjectionSection s U).cartesianSectionFunctor.sheafPushforwardContinuous
      AddCommGrpCat.{max w uD vD uC vC} (s.base.J.over (s.p.obj U)) (s.topology.over U)).Additive :=
    Functor.additive_sheafPushforwardContinuous _ _ _ AddCommGrpCat.{max w uD vD uC vC}
  have : (s.cartesianLiftRestriction U).Additive := inferInstanceAs (Functor.Additive (_ ⋙ _))
  exact Functor.preservesZeroMorphisms_of_additive _

/-- **Stacks 0D6X for the projection of a fibred category, for the extension by zero of an
inverse image along the localized projection.** For an abelian sheaf `X` on the localized base
`D/p(U)`, the abelian sheaf `j_{U!} π_U⁻¹ X` on the total category has vanishing
`Ext^n(-, π⁻¹ I)` for `n ≥ 1` and `I` an injective abelian sheaf on the base. It is the value at
`X` of the left adjoint of the restriction along the cartesian lifts at `U`, which is exact,
preserves injectives and carries `π⁻¹ I` to the injective `I|_{p(U)}`. -/
theorem extAcyclic_extensionByZero_inverseImage (X : Sheaf (s.base.J.over (s.p.obj U))
      AddCommGrpCat.{max w uD vD uC vC}) :
    s.abelianLowerShriekAdjunction.extAcyclic
      (((Over.post (X := U) s.p).sheafPushforwardContinuous AddCommGrpCat.{max w uD vD uC vC}
        (s.topology.over U) (s.base.J.over (s.p.obj U)) ⋙
      (Over.forget U).sheafPullback AddCommGrpCat.{max w uD vD uC vC} (s.topology.over U)
        s.topology).obj X) := by
  intro I hI n hn
  obtain ⟨h₁, h₂, h₃⟩ := s.cartesianLiftRestriction_exact U
  have : (s.base.J.overPullback AddCommGrpCat.{max w uD vD uC vC}
      (s.p.obj U)).PreservesInjectiveObjects :=
    Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{vD, uD,
      max w uD vD uC vC} s.base.J (s.p.obj U)
  have hRI : Injective ((s.cartesianLiftRestriction U).obj (s.abelianInverseImage.obj I)) :=
    Injective.of_iso (s.cartesianLiftRestrictionInverseImageIso U I).symm
      ((s.base.J.overPullback AddCommGrpCat.{max w uD vD uC vC} (s.p.obj U)).injective_obj I)
  exact Stacks.Cohomology.subsingleton_ext_leftAdjoint_obj (s.cartesianLiftRestriction U)
    (s.cartesianLiftRestrictionAdjunction U) X n hn _ hRI

/-- **Stacks 08P4 for the extension by zero of the structure sheaf of a slice of the total
category.** The abelian sheaf underlying `j_{U!} O_U` is the extension by zero, along
`C/U ⥤ C`, of the abelian sheaf underlying `O_U`, and `O_U` is the restriction along the
localized projection of the structure sheaf of the base slice `D/p(U)`. -/
def toSheafExtensionByZeroUnitIso :
    (SheafOfModules.toSheaf s.totalModuleRing).obj
        (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnit s.totalModuleRing U) ≅
      ((Over.post (X := U) s.p).sheafPushforwardContinuous AddCommGrpCat.{max w uD vD uC vC}
          (s.topology.over U) (s.base.J.over (s.p.obj U)) ⋙
        (Over.forget U).sheafPullback AddCommGrpCat.{max w uD vD uC vC} (s.topology.over U)
          s.topology).obj
        ((SheafOfModules.toSheaf (s.baseModuleRing.over (s.p.obj U))).obj
          (SheafOfModules.unit _)) :=
  ((Stacks.SheafOfModules.lowerShriekForgetOverForgetIso s.topology s.totalModuleRing U).app
    (SheafOfModules.unit _)).symm

/-- The abelian sheaf underlying `j_{U!} O_U` has vanishing `Ext^n(-, π⁻¹ I)` for `n ≥ 1` and
`I` an injective abelian sheaf on the base. -/
theorem extAcyclic_toSheaf_extensionByZeroUnit_totalModuleRing :
    s.abelianLowerShriekAdjunction.extAcyclic
      ((SheafOfModules.toSheaf s.totalModuleRing).obj
        (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnit s.totalModuleRing U)) :=
  s.abelianLowerShriekAdjunction.extAcyclic_of_iso (s.toSheafExtensionByZeroUnitIso U).symm
    (s.extAcyclic_extensionByZero_inverseImage U _)

end ExtAcyclic

/-- Families of abelian sheaves on the total category, indexed by a type of the coefficient
universe, have a coproduct. -/
private instance hasCoproduct_sheafAb {ι : Type (max w uD vD uC vC)}
    (Y : ι → Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) : HasCoproduct Y :=
  (Stacks.Cohomology.DerivedLowerShriek.hasColimitsOfShape_discrete_sheafAb s.topology
    ι).has_colimit _

variable {s} in
/-- The abelian sheaf underlying a direct sum of the `j_{U!} O_U` is `Ext`-acyclic for
`π_! ⊣ π⁻¹`. -/
theorem extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits
    {M : SheafOfModules.{max w uD vD uC vC} s.totalModuleRing}
    (hM : Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits s.totalModuleRing M) :
    s.abelianLowerShriekAdjunction.extAcyclic
      ((SheafOfModules.toSheaf s.totalModuleRing).obj M) := by
  obtain ⟨ι, U, ⟨e⟩⟩ := hM
  have : PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.toSheaf.{max w uD vD uC vC} s.totalModuleRing) :=
    (inferInstance : PreservesColimitsOfSize.{max w uD vD uC vC, max w uD vD uC vC}
      (SheafOfModules.toSheaf.{max w uD vD uC vC} s.totalModuleRing)).preservesColimitsOfShape
  refine s.abelianLowerShriekAdjunction.extAcyclic_of_iso
    ((SheafOfModules.toSheaf s.totalModuleRing).mapIso e) ?_
  let X : ι → Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC} := fun i =>
    (SheafOfModules.toSheaf s.totalModuleRing).obj
      (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnit s.totalModuleRing (U i))
  refine s.abelianLowerShriekAdjunction.extAcyclic_of_iso
    (PreservesCoproduct.iso (SheafOfModules.toSheaf s.totalModuleRing) _).symm ?_
  exact s.abelianLowerShriekAdjunction.extAcyclic_coproduct X
    fun i => s.extAcyclic_toSheaf_extensionByZeroUnit_totalModuleRing (U i)

variable {s} in
/-- The `Ext`-acyclic abelian sheaves for `π_! ⊣ π⁻¹` are closed under binary direct sums. -/
theorem extAcyclic_biprod {X Y : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}}
    (hX : s.abelianLowerShriekAdjunction.extAcyclic X)
    (hY : s.abelianLowerShriekAdjunction.extAcyclic Y) :
    s.abelianLowerShriekAdjunction.extAcyclic (X ⊞ Y) := by
  have : HasCoproduct (pairFunction X Y) := (inferInstance : HasBinaryCoproduct X Y)
  exact s.abelianLowerShriekAdjunction.extAcyclic_of_iso (biprod.isoCoprod X Y).symm
    (s.abelianLowerShriekAdjunction.extAcyclic_coproduct (pairFunction X Y)
      (by rintro (_ | _) <;> assumption))

/-- The `Ext`-acyclic abelian sheaves for `π_! ⊣ π⁻¹` contain a zero object. -/
instance containsZero_extAcyclic :
    s.abelianLowerShriekAdjunction.extAcyclic.ContainsZero :=
  ⟨(HasZeroObject.zero (C := Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})).elim
    fun Z hZ => ⟨Z, hZ, s.abelianLowerShriekAdjunction.extAcyclic_of_isZero hZ⟩⟩

variable {s} in
/-- A direct sum of the free abelian sheaves `j_{U!} ℤ_U` is `Ext`-acyclic for `π_! ⊣ π⁻¹`: this
is Stacks 0D6X for `p`, `subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage`. -/
theorem extAcyclic_of_isSumOfExtensionByZeroUnitsAb
    {X : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}}
    (hX : Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w uD vD uC}
      s.topology X) :
    s.abelianLowerShriekAdjunction.extAcyclic X := by
  obtain ⟨ι, U, ⟨e⟩⟩ := hX
  let Y : ι → Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC} := fun i =>
    Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w uD vD uC} s.topology (U i)
  refine s.abelianLowerShriekAdjunction.extAcyclic_of_iso e ?_
  exact s.abelianLowerShriekAdjunction.extAcyclic_coproduct Y fun i I _ n hn =>
    s.subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage (U i) I n hn

/-- **The acyclicity statement of Stacks 07AC for `π_!` on sheaves of modules.** Lower shriek
of sheaves of modules carries a bounded above acyclic complex whose terms are direct sums of the
`j_{U!} O_U` to an acyclic complex.

The underlying abelian sheaves of such a complex are a bounded above acyclic complex whose terms
are `Ext`-acyclic for `π_!^{Ab} ⊣ π⁻¹` (`extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits`), so
`π_!^{Ab}` keeps it acyclic, and `forget ∘ π_! = π_!^{Ab} ∘ forget`
(`isIso_moduleLowerShriekForgetComparison`), `forget` being faithful and exact. -/
theorem moduleLowerShriekAcyclic (a : ℤ)
    (L : CochainComplex (SheafOfModules.{max w uD vD uC vC} s.totalModuleRing) ℤ)
    (hLE : L.IsStrictlyLE a)
    (hLP : ∀ n, Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnits
      s.totalModuleRing (L.X n))
    (hL : L.Acyclic) :
    ((s.moduleLowerShriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic := by
  have hiso := s.isIso_moduleLowerShriekForgetComparison
  have : s.abelianLowerShriek.Additive := s.abelianLowerShriek_additive
  have : PreservesFiniteColimits s.abelianLowerShriek :=
    s.abelianLowerShriek_preservesFiniteColimits
  let G := SheafOfModules.toSheaf.{max w uD vD uC vC} s.totalModuleRing
  let K : CochainComplex (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) ℤ :=
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hKLE : K.IsStrictlyLE a :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff L G a).2 hLE
  have hK : K.Acyclic := (HomologicalComplex.acyclic_map_iff_of_preservesHomology L G).2 hL
  have hA := s.abelianLowerShriekAdjunction.map_acyclic_of_extAcyclic K a hK
    fun n => extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits (hLP n)
  let c : SheafOfModules.toSheaf s.totalModuleRing ⋙ s.abelianLowerShriek ⟶
      s.moduleLowerShriek ⋙ SheafOfModules.toSheaf s.baseModuleRing :=
    s.moduleLowerShriekForgetComparison
  have : IsIso c := hiso
  have : (SheafOfModules.toSheaf s.totalModuleRing ⋙
      s.abelianLowerShriek).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : (s.moduleLowerShriek ⋙
      SheafOfModules.toSheaf s.baseModuleRing).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let e := (NatIso.mapHomologicalComplex (asIso c) (ComplexShape.up ℤ)).app L
  refine (HomologicalComplex.acyclic_map_iff_of_preservesHomology _
    (SheafOfModules.toSheaf.{max w uD vD uC vC} s.baseModuleRing)).1 fun i => ?_
  exact (exactAt_iff_of_quasiIsoAt e.hom i).1 (hA i)

section Derived

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedLowerShriek

/-- **Stacks 07AC for `π_!` on sheaves of modules, existence**: degreewise `π_!` has a pointwise
left derived functor along the quasi-isomorphisms of `Mod(O_C)`, the acyclicity statement being
`moduleLowerShriekAcyclic`. -/
instance hasPointwiseLeftDerivedFunctor_moduleLowerShriekOnHomotopy :
    (lowerShriekOnHomotopy s.topology s.base.J s.p s.baseModuleRing ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (sourceQuasiIso s.topology s.base.J s.p s.baseModuleRing) :=
  hasPointwiseLeftDerivedLowerShriek_of_acyclic s.topology s.base.J s.p s.baseModuleRing
    s.moduleLowerShriekAcyclic

/-- `Lπ_! : D(O_C) ⥤ D(O_D)`, the total left derived functor of `π_!` on sheaves of modules. -/
abbrev derivedModuleLowerShriekAtBaseModuleRing :
    DerivedCategory (SheafOfModules.{max w uD vD uC vC} s.totalModuleRing) ⥤
      DerivedCategory (SheafOfModules.{max w uD vD uC vC} s.baseModuleRing) :=
  derivedLowerShriek s.topology s.base.J s.p s.baseModuleRing

/-- `π^* : D(O_D) ⥤ D(O_C)`, induced degreewise because restriction of modules is exact. -/
abbrev derivedModuleRestriction :
    DerivedCategory (SheafOfModules.{max w uD vD uC vC} s.baseModuleRing) ⥤
      DerivedCategory (SheafOfModules.{max w uD vD uC vC} s.totalModuleRing) :=
  derivedRestriction s.topology s.base.J s.p s.baseModuleRing

/-- `Lπ_!` is absolute: it stays a left derived functor after composition with any functor out of
`D(O_D)`, being computed by resolutions. -/
instance isLeftDerivedFunctor_derivedModuleLowerShriek_comp (E : Type*) [Category E]
    (G : DerivedCategory (SheafOfModules.{max w uD vD uC vC} s.baseModuleRing) ⥤ E) :
    (s.derivedModuleLowerShriekAtBaseModuleRing ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh s.derivedModuleLowerShriekAtBaseModuleRing G).inv ≫
        Functor.whiskerRight (derivedLowerShriekComparison s.topology s.base.J s.p
          s.baseModuleRing) G)
      (sourceQuasiIso s.topology s.base.J s.p s.baseModuleRing) :=
  isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic s.topology s.base.J s.p
    s.baseModuleRing s.moduleLowerShriekAcyclic G

/-- **Stacks 09CY, the derived `Lπ_!` on sheaves of modules.** The unbounded left derived functor
`Lπ_! : D(O_C) ⥤ D(O_D)` of the lower-shriek functor on sheaves of modules exists and is left
adjoint to `π^* : D(O_D) ⥤ D(O_C)`. This is Stacks 08PC part (3) for modules in the situation of
the remark; the acyclicity statement of Stacks 07AC it rests on is `moduleLowerShriekAcyclic`. -/
@[stacks 09CY "the derived `Lπ_!` of Situation 08P8 on sheaves of modules and its adjunction \
`Lπ_! ⊣ π^*`"]
def derivedModuleLowerShriekAdjunctionAtBaseModuleRing :
    s.derivedModuleLowerShriekAtBaseModuleRing ⊣ s.derivedModuleRestriction :=
  derivedLowerShriekAdjunction s.topology s.base.J s.p s.baseModuleRing

/-- The canonical comparison `Lπ_!^{Ab} ∘ forget ⟶ forget ∘ Lπ_!` of Stacks 07AE: the unique
natural transformation compatible with the counits of the two left derived functors and the
comparison of Stacks 0798 (`existsUnique_derivedForgetComparison`). -/
def derivedModuleLowerShriekForgetComparison :
    (forgetSourceModules s.topology s.base.J s.p s.baseModuleRing).mapDerivedCategory ⋙
        derivedLowerShriekAbelian s.topology s.base.J s.p ⟶
      s.derivedModuleLowerShriekAtBaseModuleRing ⋙
        (forgetTargetModules s.base.J s.baseModuleRing).mapDerivedCategory :=
  Functor.leftDerivedLift _ (derivedLowerShriekForgetCounit s.topology s.base.J s.p
      s.baseModuleRing) (sourceQuasiIso s.topology s.base.J s.p s.baseModuleRing) _
    (derivedForgetComparisonCounit s.topology s.base.J s.p s.baseModuleRing)

/-- **Stacks 09CY, `forget ∘ Lπ_! = Lπ_!^{Ab} ∘ forget`.** The canonical comparison
`Lπ_!^{Ab} ∘ forget ⟶ forget ∘ Lπ_!` of Stacks 07AE is an isomorphism. This is Stacks 08PC
part (4) in the situation of the remark. -/
@[stacks 09CY "`forget ∘ Lπ_! = Lπ_!^{Ab} ∘ forget`: the canonical comparison of Stacks 07AE is \
an isomorphism"]
instance isIso_derivedModuleLowerShriekForgetComparison :
    IsIso s.derivedModuleLowerShriekForgetComparison := by
  let P := IsSumOfExtensionByZeroUnits s.totalModuleRing
  let P' := s.abelianLowerShriekAdjunction.extAcyclic
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{max w uD vD uC vC} s.totalModuleRing) :=
    hasExactColimitsOfShape_nat _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{max w uD vD uC vC} s.baseModuleRing) :=
    hasExactColimitsOfShape_nat _
  have := hasExactColimitsOfShape_nat_sheafAb.{max w uD vD uC vC} s.topology
  have := hasExactColimitsOfShape_nat_sheafAb.{max w uD vD uC vC} s.base.J
  have : PreservesColimitsOfShape ℕ s.abelianLowerShriek :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      s.abelianLowerShriekAdjunction).preservesColimitsOfShape
  have : PreservesColimitsOfShape ℕ s.moduleLowerShriek :=
    (Adjunction.leftAdjoint_preservesColimits.{0, 0}
      (adjunctionModules s.topology s.base.J s.p s.baseModuleRing)).preservesColimitsOfShape
  have : PreservesColimitsOfSize.{max w uD vD uC vC, max w uD vD uC vC}
      (SheafOfModules.toSheaf.{max w uD vD uC vC} s.totalModuleRing) := inferInstance
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.toSheaf.{max w uD vD uC vC} s.totalModuleRing) :=
    preservesColimitsOfSize_shrink _
  have : s.abelianLowerShriek.Additive := s.abelianLowerShriek_additive
  have : s.abelianLowerShriek.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have : PreservesFiniteColimits s.abelianLowerShriek :=
    s.abelianLowerShriek_preservesFiniteColimits
  have hsum : ∀ X Y, P X → P Y → P (X ⊞ Y) := fun _ _ => isSumOfExtensionByZeroUnits_biprod _
  have hP : ∀ X, ∃ (Y : _) (_ : P Y) (p : Y ⟶ X), Epi p := fun M =>
    exists_epi_isSumOfExtensionByZeroUnits _ M
  have hder := StacksDraft.UnboundedLeftDerivedFunctor.derives_cellularLocalizerMorphism
    s.moduleLowerShriek P hsum hP s.moduleLowerShriekAcyclic
  have hres := StacksDraft.UnboundedLeftDerivedFunctor.hasLeftResolutions_cellularLocalizerMorphism
    P hsum hP
  have hsum' : ∀ X Y, P' X → P' Y → P' (X ⊞ Y) := fun _ _ => extAcyclic_biprod
  have hP' : ∀ X, ∃ (Y : _) (_ : P' Y) (p : Y ⟶ X), Epi p := fun F => by
    obtain ⟨Y, hY, p, hp⟩ :=
      exists_epi_isSumOfExtensionByZeroUnitsAb.{max w uD vD uC} s.topology F
    exact ⟨Y, extAcyclic_of_isSumOfExtensionByZeroUnitsAb hY, p, hp⟩
  have hFP' : ∀ (a : ℤ) (L : CochainComplex (Sheaf s.topology
      AddCommGrpCat.{max w uD vD uC vC}) ℤ), L.IsStrictlyLE a → (∀ n, P' (L.X n)) →
      L.Acyclic → ((s.abelianLowerShriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        L).Acyclic := fun a L hLE hLP hL => by
    have := hLE
    exact s.abelianLowerShriekAdjunction.map_acyclic_of_extAcyclic L a hL hLP
  have hder' := StacksDraft.UnboundedLeftDerivedFunctor.derives_cellularLocalizerMorphism
    s.abelianLowerShriek P' hsum' hP' hFP'
  have hres' :=
    StacksDraft.UnboundedLeftDerivedFunctor.hasLeftResolutions_cellularLocalizerMorphism
      P' hsum' hP'
  have :=
    StacksDraft.UnboundedLeftDerivedFunctor.isLeftDerivabilityStructure_cellularLocalizerMorphism
      P' hres'
  have hc : IsIso (forgetComparisonOnHomotopy s.topology s.base.J s.p s.baseModuleRing) := by
    have := s.isIso_moduleLowerShriekForgetComparison
    have : IsIso (NatTrans.mapHomotopyCategory
        (forgetComparison s.topology s.base.J s.p s.baseModuleRing) (ComplexShape.up ℤ)) :=
      ⟨⟨NatTrans.mapHomotopyCategory
          (inv (forgetComparison s.topology s.base.J s.p s.baseModuleRing)) (ComplexShape.up ℤ),
        by rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id],
        by rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id]⟩⟩
    unfold forgetComparisonOnHomotopy
    infer_instance
  refine (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    (LF := s.derivedModuleLowerShriekAtBaseModuleRing ⋙
      (forgetTargetModules s.base.J s.baseModuleRing).mapDerivedCategory)
    (derivedLowerShriekForgetCounit s.topology s.base.J s.p s.baseModuleRing)
    (sourceQuasiIso s.topology s.base.J s.p s.baseModuleRing) _ _).1 ?_
  refine CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (sourceQuasiIso s.topology s.base.J s.p s.baseModuleRing)
    (StacksDraft.UnboundedLeftDerivedFunctor.cellular P) (fun X => ?_) _ (fun f hf hX hY => ?_)
    DerivedCategory.Qh _ _ (fun X hX => ?_)
  · obtain ⟨R⟩ := hres X
    exact ⟨R.X₁.obj, R.X₁.property, R.w, R.hw⟩
  · have : IsIso ((s.moduleLowerShriek.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).map f) :=
      hder (ObjectProperty.homMk (P := StacksDraft.UnboundedLeftDerivedFunctor.cellular P)
        (X := ⟨_, hX⟩) (Y := ⟨_, hY⟩) f) hf
    exact Functor.map_isIso
      (forgetTargetModules s.base.J s.baseModuleRing).mapDerivedCategory
      ((s.moduleLowerShriek.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map f)
  · obtain ⟨S, hS, ⟨e⟩⟩ := hX
    rw [NatTrans.isIso_app_iff_of_iso _ e]
    have hS' := StacksDraft.UnboundedLeftDerivedFunctor.IsPCellular.map
      (SheafOfModules.toSheaf.{max w uD vD uC vC} s.totalModuleRing) (P' := P')
      (fun _ hX => extAcyclic_toSheaf_of_isSumOfExtensionByZeroUnits hX) hS
    have h1 : IsIso ((derivedLowerShriekAbelianComparison s.topology s.base.J s.p).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((SheafOfModules.toSheaf.{max w uD vD uC vC} s.totalModuleRing).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj S))) :=
      CategoryTheory.LeftDerivedByResolutions.isIso_app_of_derives _ _ hder' DerivedCategory.Qh
        _ _ ⟨_, ⟨_, hS', ⟨Iso.refl _⟩⟩⟩
    have h1' : IsIso ((derivedLowerShriekAbelianComparison s.topology s.base.J s.p).app
        (((forgetSourceModules s.topology s.base.J s.p s.baseModuleRing).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj S))) :=
      (NatTrans.isIso_app_iff_of_iso _
        (((forgetSourceModules s.topology s.base.J s.p s.baseModuleRing).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app S)).2 h1
    simp only [derivedForgetComparisonCounit, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp]
    infer_instance

/-- The comparison of Stacks 07AE is compatible with the counits of the two left derived
functors and the comparison of Stacks 0798. -/
theorem derivedModuleLowerShriekForgetComparison_fac :
    Functor.whiskerLeft DerivedCategory.Qh s.derivedModuleLowerShriekForgetComparison ≫
        derivedLowerShriekForgetCounit s.topology s.base.J s.p s.baseModuleRing =
      derivedForgetComparisonCounit s.topology s.base.J s.p s.baseModuleRing :=
  Functor.leftDerived_fac _ _ _ _ _

/-- The isomorphism `forget ∘ Lπ_! ≅ Lπ_!^{Ab} ∘ forget`, inverse of the comparison of Stacks
07AE. -/
def derivedModuleLowerShriekForgetIso :
    s.derivedModuleLowerShriekAtBaseModuleRing ⋙
        (SheafOfModules.toSheaf s.baseModuleRing).mapDerivedCategory ≅
      (SheafOfModules.toSheaf s.totalModuleRing).mapDerivedCategory ⋙
        s.derivedAbelianLowerShriek :=
  (asIso s.derivedModuleLowerShriekForgetComparison).symm

end Derived

end Stacks.Sites.FibredCategory.FibredCategorySituation

end
