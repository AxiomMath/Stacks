module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ModuleDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Modules.PullbackOfExtensionByZeroUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfAdjointFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# The generators of `Mod(π^{-1}O)` are acyclic for abelian lower shriek

Let `p : C ⥤ D` be a fibred category over a site `D`, give `C` the inherited topology, let `O` be
a sheaf of rings on `D` and let `O_C = π^{-1}O`, as in Situation 08P8. Stacks 08PC part (4)
asserts that derived lower shriek of modules and of abelian sheaves agree after forgetting the
module structure, and its proof reduces this to the generators `j_{U!}O_U` of `Mod(O_C)`:
it suffices that `Lπ^{Ab}_!` of the underlying abelian sheaf of `j_{U!}O_U` is computed by
`π^{Ab}_!` itself. This file proves the `Ext` form of that input: the underlying abelian sheaf of
`j_{U!}O_U` is `Ext`-acyclic for the adjunction `π_!^{Ab} ⊣ π^{-1}`.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.forgetExtensionByZeroUnitCorepresentation`:
  morphisms of abelian sheaves out of the underlying abelian sheaf of `j_{U!}O_U` into `F` are
  morphisms out of the underlying abelian sheaf of `O_{p(U)}` into the restriction of `F` along
  the cartesian lifts at `U`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.extAcyclic_toSheaf_extensionByZeroUnit`:
  the underlying abelian sheaf of `j_{U!}O_U` is `Ext`-acyclic for `π_!^{Ab} ⊣ π^{-1}`.

## Implementation notes

The source computes `Hom_{D(C/U)}(Lπ_{U,!}^{Ab} O_U, E)` through the section `σ` of Lemma 08P9 and
the identities `π_U^{-1} O_V = O_U` and `σ^{-1} = π_{U,*}`. The same chain of identifications is
used here one level down, on `Hom` of abelian sheaves:

`Hom(j_{U!} O_U, F) = Hom(O_U, F|_U) = Hom(π_U^{-1} O_V, F|_U) = Hom(O_V, σ^{-1}(F|_U))`,

the first equality using that forgetting the module structure commutes with extension by zero
along a localization morphism (Stacks 0798 for `C/U ⥤ C`). Restriction along the cartesian lifts
`F ↦ σ^{-1}(F|_U)` is exact and preserves injectives, so this transports `Ext` out of
`j_{U!}O_U` to `Ext` out of `O_V` on `D/V`, and against `π^{-1} I` it is `Ext` into the
injective `I|_V`.

Everything lies in one universe `u`: the two sites are small, as the sites of the source are,
and the sheaf of rings and the module sections lie in the same universe.

## References

* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 08P9](https://stacks.math.columbia.edu/tag/08P9)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.DerivedLowerShriek

universe u

namespace Stacks.Sites.FibredCategory

namespace FibredCategorySituation

variable (s : FibredCategorySituation.{u, u, u, u, u}) (O : Sheaf s.base.J RingCat.{u})

/-- The sheaf of rings `O_C = π^{-1} O` on the total category. -/
abbrev totalRing : Sheaf s.topology RingCat.{u} :=
  inverseImageRing s.topology s.base.J s.p O

section Corepresentation

variable (U : s.C)

/-- The localized projection `π_U : C/U ⥤ D/p(U)`. -/
abbrev localizedProjection : Over U ⥤ Over (s.p.obj U) := Over.post s.p

/-- The underlying abelian sheaf of the structure sheaf of `D/p(U)`. -/
abbrev localizedBaseUnit : Sheaf (s.base.J.over (s.p.obj U)) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (O.over (s.p.obj U))).obj (SheafOfModules.unit _)

/-- The underlying abelian sheaf of the structure sheaf of `C/U` is the inverse image along the
localized projection of the underlying abelian sheaf of the structure sheaf of `D/p(U)`: both
have sections `O(p(V))` over `V ⟶ U`. -/
def localizedTotalUnitIso :
    letI := (localizedProjectionSection s U).isContinuous
    (SheafOfModules.toSheaf ((s.totalRing O).over U)).obj (SheafOfModules.unit _) ≅
      ((s.localizedProjection U).sheafPushforwardContinuous AddCommGrpCat.{u}
        (s.topology.over U) (s.base.J.over (s.p.obj U))).obj (s.localizedBaseUnit O U) :=
  Iso.refl _

/-- **Morphisms out of `j_{U!} O_U`, read on abelian sheaves.** For an abelian sheaf `F` on the
total category, morphisms of abelian sheaves from the underlying abelian sheaf of `j_{U!} O_U`
to `F` are morphisms from the underlying abelian sheaf of `O_{p(U)}` to the restriction of `F`
along the cartesian lifts at `U`, naturally in `F`. -/
def forgetExtensionByZeroUnitCorepresentation :
    preadditiveCoyoneda.obj (op ((SheafOfModules.toSheaf (s.totalRing O)).obj
        (extensionByZeroUnit (s.totalRing O) U))) ≅
      s.cartesianLiftRestriction U ⋙
        preadditiveCoyoneda.obj (op (s.localizedBaseUnit O U)) := by
  let σ := localizedProjectionSection s U
  letI := σ.isContinuous
  letI := σ.cartesianSection_isContinuous
  let A := AddCommGrpCat.{u}
  let JU := s.topology.over U
  let K := s.base.J.over (s.p.obj U)
  let adjσ := σ.cartesianSection_adjunction.sheafPushforwardContinuous (E := A) JU K
  let adjj := (Over.forget U).sheafAdjunctionContinuous A JU s.topology
  have : ((Over.forget U).sheafPushforwardContinuous A JU s.topology).Additive :=
    Functor.additive_sheafPushforwardContinuous _ _ _ A
  have : (σ.cartesianSectionFunctor.sheafPushforwardContinuous A K JU).Additive :=
    Functor.additive_sheafPushforwardContinuous _ _ _ A
  let X := (SheafOfModules.toSheaf ((s.totalRing O).over U)).obj (SheafOfModules.unit _)
  let eZ := (Stacks.SheafOfModules.lowerShriekForgetOverForgetIso.{u, u} s.topology
    (s.totalRing O) U).app
    (SheafOfModules.unit _)
  exact preadditiveCoyoneda.mapIso eZ.op ≪≫ adjj.coyonedaAddIso X ≪≫
    Functor.isoWhiskerLeft ((Over.forget U).sheafPushforwardContinuous A JU s.topology)
      (preadditiveCoyoneda.mapIso (s.localizedTotalUnitIso O U).symm.op ≪≫
        adjσ.coyonedaAddIso (s.localizedBaseUnit O U))

/-- **The underlying abelian sheaf of `j_{U!} O_U` is `Ext`-acyclic for `π_!^{Ab} ⊣ π^{-1}`**: for
an injective abelian sheaf `I` on the base, `Ext^n(j_{U!} O_U, π^{-1} I) = 0` for `n ≥ 1`.

Restriction along the cartesian lifts at `U` is exact and preserves injectives, and
`forgetExtensionByZeroUnitCorepresentation` identifies the functor it corepresents, so `Ext` out
of `j_{U!} O_U` is `Ext` out of `O_{p(U)}` after that restriction; it carries `π^{-1} I` to the
injective `I|_{p(U)}`. -/
theorem extAcyclic_toSheaf_extensionByZeroUnit :
    s.abelianLowerShriekAdjunction.extAcyclic
      ((SheafOfModules.toSheaf (s.totalRing O)).obj (extensionByZeroUnit (s.totalRing O) U)) := by
  intro I _ n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h₁, h₂, h₃⟩ := s.cartesianLiftRestriction_exact U
  have : (s.cartesianLiftRestriction U).Additive := by
    let := (localizedProjectionSection s U).cartesianSection_isContinuous
    have : (s.topology.overPullback AddCommGrpCat.{u} U).Additive :=
      Functor.additive_sheafPushforwardContinuous (Over.forget U) (s.topology.over U) s.topology _
    have : ((localizedProjectionSection s U).cartesianSectionFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u} (s.base.J.over (s.p.obj U)) (s.topology.over U)).Additive :=
      Functor.additive_sheafPushforwardContinuous _ _ _ _
    exact inferInstanceAs (Functor.Additive (_ ⋙ _))
  have e := (ModuleSheafCohomology.extComparisonIso (s.cartesianLiftRestriction U)
    (s.localizedBaseUnit O U)
    ((SheafOfModules.toSheaf (s.totalRing O)).obj (extensionByZeroUnit (s.totalRing O) U))
    (fun J _ n e => by
      have := (s.cartesianLiftRestriction U).injective_obj J
      exact Ext.eq_zero_of_injective e)
    (s.forgetExtensionByZeroUnitCorepresentation O U) (m + 1)).app (s.abelianInverseImage.obj I)
  have : (s.base.J.overPullback AddCommGrpCat.{u} (s.p.obj U)).PreservesInjectiveObjects :=
    Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u, u, u}
      s.base.J (s.p.obj U)
  have hI : Injective ((s.cartesianLiftRestriction U).obj (s.abelianInverseImage.obj I)) :=
    Injective.of_iso (s.cartesianLiftRestrictionInverseImageIso U I).symm
      ((s.base.J.overPullback AddCommGrpCat.{u} (s.p.obj U)).injective_obj I)
  exact e.addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
    (subsingleton_of_forall_eq 0 fun x => Ext.eq_zero_of_injective x)

end Corepresentation

section LowerShriekForget

/-- The localized projection `π_U : C/U ⥤ D/p(U)` is continuous for the localized topologies. -/
instance localizedProjection_isContinuous (U : s.C) :
    (Over.post (X := U) s.p).IsContinuous (s.topology.over U) (s.base.J.over (s.p.obj U)) :=
  (localizedProjectionSection s U).isContinuous

/-- **The inverse image along the localized projection is fully faithful.** Restriction of
abelian sheaves along `π_U : C/U ⥤ D/p(U)` has restriction along the cartesian section `σ` of
Lemma 08P9 as a right adjoint, and `σ` is fully faithful, being right adjoint to `π_U` with
`π_U ∘ σ = id`. -/
def localizedInverseImageFullyFaithful (U : s.C) :
    ((s.localizedProjection U).sheafPushforwardContinuous AddCommGrpCat.{u}
      (s.topology.over U) (s.base.J.over (s.p.obj U))).FullyFaithful :=
  let σ := localizedProjectionSection s U
  letI := σ.cartesianSection_isContinuous
  have := σ.cartesianSection_adjunction.isIso_counit_of_iso σ.cartesianSection_base
  let hσ := σ.cartesianSection_adjunction.fullyFaithfulROfIsIsoCounit
  have := hσ.full
  have := hσ.faithful
  Stacks.ChaoticSite.fullyFaithfulSheafPushforwardContinuous AddCommGrpCat.{u}
    (s.topology.over U) (s.base.J.over (s.p.obj U)) σ.cartesianSection_adjunction

/-- The canonical map `O_U ⟶ π_U^{-1} O_{p(U)}` of sheaves of modules over `O_U = π_U^{-1}O_{p(U)}`
is an isomorphism on underlying abelian sheaves: the structure morphism of rings is the
identity. -/
theorem isIso_toSheaf_unitToPushforwardObjUnit (U : s.C) :
    IsIso ((SheafOfModules.toSheaf _).map (SheafOfModules.unitToPushforwardObjUnit
      (Stacks.SheafOfModules.structureMap (s.topology.over U) (s.base.J.over (s.p.obj U))
        (Over.post (X := U) s.p) (O.over (s.p.obj U))))) := by
  refine (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)).mp ?_
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun X => (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b h => h, fun a => ⟨a, rfl⟩⟩

/-- **The canonical map `(π_U)_!^{Ab} O_U ⟶ O_{p(U)}` of Stacks 0798 is an isomorphism** for the
localized projection of a fibred category. Its transpose under `(π_U)_!^{Ab} ⊣ π_U^{-1}` is the
identity of the underlying abelian sheaf of `O_U = π_U^{-1} O_{p(U)}`, and the counit of that
adjunction is invertible, `π_U^{-1}` being fully faithful. -/
theorem isIso_localizedStructureSheafComparison (U : s.C) :
    IsIso (Stacks.SheafOfModules.localizedStructureSheafComparison
      s.topology s.base.J s.p O U) := by
  let adj := (Over.post (X := U) s.p).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (s.topology.over U) (s.base.J.over (s.p.obj U))
  let φ := Stacks.SheafOfModules.structureMap (s.topology.over U) (s.base.J.over (s.p.obj U))
    (Over.post (X := U) s.p) (O.over (s.p.obj U))
  have hff := s.localizedInverseImageFullyFaithful U
  have := hff.full
  have := hff.faithful
  set κ := Stacks.SheafOfModules.localizedStructureSheafComparison s.topology s.base.J s.p O U
  have hκ : adj.homEquiv _ _ κ = (SheafOfModules.toSheaf _).map
      (SheafOfModules.unitToPushforwardObjUnit φ) := by
    change adj.homEquiv _ _
      ((Stacks.SheafOfModules.lowerShriekForgetComparison (Over.post (X := U) s.p) φ).app _ ≫
        (SheafOfModules.toSheaf _).map (SheafOfModules.pullbackObjUnitToUnit φ)) = _
    rw [Adjunction.homEquiv_naturality_right]
    dsimp only [Functor.comp_obj]
    rw [Stacks.SheafOfModules.lowerShriekForgetComparison_homEquiv,
      ← SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ,
      Adjunction.homEquiv_unit]
    rfl
  have : IsIso (adj.homEquiv _ _ κ) := by
    rw [hκ]
    exact s.isIso_toSheaf_unitToPushforwardObjUnit O U
  have e : κ = ((Over.post (X := U) s.p).sheafPullback AddCommGrpCat.{u} (s.topology.over U)
      (s.base.J.over (s.p.obj U))).map (adj.homEquiv _ _ κ) ≫ adj.counit.app _ := by
    have h := adj.homEquiv_counit (g := adj.homEquiv _ _ κ)
    rwa [Equiv.symm_apply_apply] at h
  rw [e]
  infer_instance

/-- **Stacks 08PC part (2) for the projection of a fibred category.** Lower shriek of sheaves of
`O_C`-modules followed by forgetting the module structure is lower shriek of abelian sheaves
applied to the underlying abelian sheaf: the comparison transformation of Stacks 0798 is an
isomorphism. By the criterion of Stacks 0798 it suffices that every canonical map
`(π_U)_!^{Ab} O_U ⟶ O_{p(U)}` be an isomorphism, which is
`isIso_localizedStructureSheafComparison`. -/
theorem isIso_lowerShriekForgetComparison :
    IsIso (Stacks.SheafOfModules.lowerShriekForgetComparison s.p
      (Stacks.SheafOfModules.structureMap s.topology s.base.J s.p O)) :=
  Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_localizedStructureSheafComparison.{u}
    s.topology s.base.J s.p O (s.isIso_localizedStructureSheafComparison O)

end LowerShriekForget

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
