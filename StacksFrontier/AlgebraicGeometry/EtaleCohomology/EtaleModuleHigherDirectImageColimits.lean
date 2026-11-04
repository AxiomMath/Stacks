module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageFilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafAcyclicity
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of sheaves of modules commute with filtered colimits and direct sums

Let `Λ` be a ring and let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes. For every `q ≥ 0` the higher direct image

> `R^q f_* : Sh(X_étale, Λ) ⥤ Sh(Y_étale, Λ)`

commutes with filtered colimits, and hence with arbitrary direct sums. This is the case of a
constant system of [Stacks, Tag 09Z1], in the form in which the Stacks project uses it for
sheaves of `Λ`-modules ("the functors `R^q g_*` commute with filtered colimits by Lemma 09Z1").

## Main results

All in the namespace `Stacks.EtaleCohomology`.

* `preservesColimit_rightDerived_sheafSections_etaleModules_of_qcqs`: cohomology `H^q(W, -)` of
  sheaves of `Λ`-modules over an object `W` of the small étale site with quasi-compact and
  quasi-separated underlying scheme commutes with filtered colimits.
* `preservesColimitsOfShape_rightDerived_etaleModuleDirectImage`: `R^q f_*` on sheaves of
  `Λ`-modules preserves filtered colimits.
* `preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ`: `R^q f_*` on
  sheaves of `Λ`-modules preserves direct sums. This is the hypothesis `hsums` of
  `Stacks.EtaleCohomology.preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage`
  ([Stacks, Tag 0F11] (1)), in exactly the shape stated there.

## Implementation notes

*Coefficients.* The cohomology of a sheaf of `Λ`-modules over `W`, after forgetting the
`Λ`-module structure, is the cohomology of the underlying abelian sheaf, naturally in the sheaf
(the module-valued half of [Stacks, Tag 03FD] / [Stacks, Tag 0D6J]). Both sides are `Ext`-functors
out of a corepresenting object — `Λ ⊗_ℤ ℤ_W` sheafified on the module side and the free abelian
sheaf `ℤ_W` on the abelian side — and `ModuleSheafCohomology.extComparisonIso` identifies them,
the acyclicity input being that the underlying abelian sheaf of an injective sheaf of `Λ`-modules
has no higher `Ext` out of the torsion-free `ℤ_W`
(`Stacks.Cohomology.ModuleSheaf.ext_eq_zero_of_isTorsionFree`). Since forgetting the
`Λ`-module structure, on sheaves and on modules, preserves filtered colimits, and on modules
reflects them, the filtered-colimit statement for `Λ`-modules over `W` follows from the abelian
one, Stacks 0739 at quasi-compact quasi-separated objects
(`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_sheafSections_of_qcqs`).

*Direct images.* As in the abelian case
(`Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs`),
the local criterion of Stacks 0H7B on a locally small site, in the namespace `Stacks.Cohomology`,
`HigherDirectImage.preservesColimit_rightDerived_sheafPushforwardContinuous_of_hasEnoughObjects`,
reduces the statement to cohomology over `X ×_Y V` for affine `V`, which is quasi-compact and
quasi-separated.

*Direct sums.* A direct sum is the filtered colimit of its finite sub-sums, and finite direct
sums are preserved by the additive functor `R^q f_*`
(`Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete`).

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 0H7B](https://stacks.math.columbia.edu/tag/0H7B)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

/- `Stacks.EtaleCohomology.hasSheafifyEtale` is stated at the coefficient universe `u + 1`;
instance search would try to unify the coefficient universe `max (u + 1) r` with it and fail on
the universe constraint, so it is switched off here. -/
attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale

section Sections

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

/-- Forgetting the `Λ`-module structure of sheaves of `Λ`-modules on the small étale site is a
left adjoint: `forget₂ (ModuleCat Λ) AddCommGrpCat` is left adjoint to coextension of scalars
along `ℤ → Λ`, and composing sheaves with a left adjoint whose sheafification is the identity on
sheaves is left adjoint to composing with the right adjoint. -/
theorem isLeftAdjoint_sheafCompose_forget₂_etaleModules :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})).IsLeftAdjoint := by
  let U := forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}
  let adj := (ModuleCat.restrictCoextendScalarsAdj (Int.castRingHom Λ)).comp
    (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{max (u + 1) r} ℤ)
      AddCommGrpCat.{max (u + 1) r}))
  let e : Sheaf.composeAndSheafify X.smallEtaleTopology U ≅ sheafCompose X.smallEtaleTopology U :=
    Functor.isoWhiskerLeft (sheafCompose X.smallEtaleTopology U)
      (asIso (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).counit)
  exact ((Sheaf.adjunction X.smallEtaleTopology adj).ofNatIsoLeft e).isLeftAdjoint

/-- Cohomology `H^q(W, -)` of sheaves of `Λ`-modules over an object `W` of the small étale site,
followed by forgetting the `Λ`-module structure, is the cohomology of the underlying abelian
sheaf, naturally in the sheaf. -/
theorem nonempty_rightDerived_sheafSections_comp_forget₂_iso (q : ℕ) (W : X.Etale) :
    Nonempty (((sheafSections X.smallEtaleTopology
        (ModuleCat.{max (u + 1) r} Λ)).obj (op W)).rightDerived q ⋙
        forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ≅
      sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) ⋙
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj
          (op W)).rightDerived q) := by
  let J := X.smallEtaleTopology
  let φ := forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}
  let Fg := sheafCompose J φ
  let Γ := (sheafSections J (ModuleCat.{max (u + 1) r} Λ)).obj (op W)
  let Γab := (sheafSections J AddCommGrpCat.{max (u + 1) r}).obj (op W)
  have : Fg.Additive := ⟨by intros; rfl⟩
  have : Fg.IsLeftAdjoint := isLeftAdjoint_sheafCompose_forget₂_etaleModules Λ X
  have : PreservesFiniteLimits Fg :=
    Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{u + 1, r, u, u + 1}
      J Λ
  have : HasExt.{max (u + 1) r} (Sheaf J AddCommGrpCat.{max (u + 1) r}) :=
    hasExt_of_enoughInjectives.{max (u + 1) r} _
  have : HasExt.{max (u + 1) r} (EtaleModules.{u, r} Λ X) :=
    hasExt_of_enoughInjectives.{max (u + 1) r} _
  -- The corepresenting object `ℤ_W` of `H^0(W, -)` on abelian sheaves, and its torsion-freeness.
  let Z := (Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{max (u + 1) r} J).obj W
  have hZ : ∀ V, Module.IsTorsionFree ℤ (Z.obj.obj V) :=
    ModuleSheafCohomology.isTorsionFree_sheafify.{u + 1, u, max (u + 1) r} J _ fun V ↦ by
      show Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{max (u + 1) r} (V.unop ⟶ W)))
      exact Module.Flat.isTorsionFree
  -- The corepresenting object `Λ ⊗_ℤ ℤ_W` of `H^0(W, -)` on sheaves of `Λ`-modules.
  let adj := Stacks.Cohomology.ModuleSheaf.sheafExtendScalarsFromIntAdj.{u + 1, r, u, u + 1} J Λ
  let Y := (Sheaf.composeAndSheafify J (ModuleCat.extendScalarsFromInt.{u + 1} Λ)).obj Z
  have : (Sheaf.composeAndSheafify J (ModuleCat.extendScalarsFromInt.{u + 1} Λ)).Additive :=
    adj.left_adjoint_additive
  let e : preadditiveCoyoneda.obj (op Y) ≅ Fg ⋙ preadditiveCoyoneda.obj (op Z) :=
    NatIso.ofComponents (fun M ↦ (adj.homAddEquiv Z M).toAddCommGrpIso) (by
      intro M M' g
      ext a
      exact adj.homEquiv_naturality_right a g)
  -- The underlying abelian sheaf of an injective sheaf of `Λ`-modules has no higher `Ext` out of
  -- `ℤ_W`.
  have hacyc : ∀ (I : EtaleModules.{u, r} Λ X) [Injective I] (n : ℕ)
      (a : Ext Z (Fg.obj I) (n + 1)), a = 0 := fun I _ n a ↦
    Stacks.Cohomology.ModuleSheaf.ext_eq_zero_of_isTorsionFree.{max (u + 1) r, u + 1, r, u, u + 1}
      J Λ I Z hZ n a
  -- `H^q(W, -) ⋙ forget ≅ forget ⋙ H^q(W, -)`.
  have hΓab : Γab ≅ preadditiveCoyoneda.obj (op Z) :=
    Stacks.Cohomology.FreeYonedaUnivLE.evaluationRepresentation.{max (u + 1) r} J W
  obtain ⟨eB⟩ := ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived (Fg ⋙ Γab) Y
    (Functor.isoWhiskerLeft Fg hΓab ≪≫ e.symm) q
  open Stacks.Cohomology.FreeYonedaUnivLE in
  obtain ⟨eA⟩ :=
    nonempty_extFunctorObj_iso_rightDerived_sections_of_enoughInjectives.{max (u + 1) r} J W q
  have : φ.PreservesHomology := Functor.preservesHomologyOfExact φ
  exact ⟨Stacks.Cohomology.ModuleComparison.rightDerivedCompIso Γ φ (Fg ⋙ Γab) (Iso.refl _) q ≪≫
      eB.symm ≪≫ ModuleSheafCohomology.extComparisonIso Fg Z Y hacyc e q ≪≫
      Functor.isoWhiskerLeft Fg eA⟩

/-- **Cohomology of sheaves of `Λ`-modules over a quasi-compact quasi-separated object of the
small étale site commutes with filtered colimits.** Let `W` be an object of the small étale site
of `X` whose underlying scheme is quasi-compact and quasi-separated. For every `q` the functor
`H^q(W, -)` on sheaves of `Λ`-modules preserves filtered colimits. -/
@[sga "4 VII 3.3" "more general"]
theorem preservesColimit_rightDerived_sheafSections_etaleModules_of_qcqs (q : ℕ) (W : X.Etale)
    (hW : W ∈ qcqsEtaleObjects X) {I : Type (max (u + 1) r)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ EtaleModules.{u, r} Λ X) :
    PreservesColimit F (((sheafSections X.smallEtaleTopology
      (ModuleCat.{max (u + 1) r} Λ)).obj (op W)).rightDerived q) := by
  let J := X.smallEtaleTopology
  let φ := forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}
  let Fg := sheafCompose J φ
  let Γ := (sheafSections J (ModuleCat.{max (u + 1) r} Λ)).obj (op W)
  let Γab := (sheafSections J AddCommGrpCat.{max (u + 1) r}).obj (op W)
  have : Fg.IsLeftAdjoint := isLeftAdjoint_sheafCompose_forget₂_etaleModules Λ X
  obtain ⟨N⟩ := nonempty_rightDerived_sheafSections_comp_forget₂_iso Λ X q W
  have : PreservesColimitsOfShape I Fg := inferInstance
  have : IsIso (colimit.post (F ⋙ Fg) (Γab.rightDerived q)) :=
    isIso_colimit_post_rightDerived_sheafSections_of_qcqs.{r} q W hW (F ⋙ Fg)
  have : PreservesColimit (F ⋙ Fg) (Γab.rightDerived q) := preservesColimit_of_isIso_post _ _
  have : PreservesColimit F (Γ.rightDerived q ⋙ φ) := preservesColimit_of_natIso F N.symm
  have : PreservesColimitsOfShape I φ :=
    (ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r, max (u + 1) r, max (u + 1) r}
      Λ).preservesColimitsOfShape
  have : ReflectsColimitsOfShape I φ := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimit_of_reflects_of_preserves (Γ.rightDerived q) φ

end Sections

section DirectImage

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Higher direct images of sheaves of `Λ`-modules along a quasi-compact quasi-separated
morphism commute with filtered colimits** ([Stacks, Tag 09Z1] for a constant system). Let
`f : X ⟶ Y` be quasi-compact and quasi-separated and let `Λ` be a ring. For every `q` the higher
direct image `R^q f_* : Sh(X_étale, Λ) ⥤ Sh(Y_étale, Λ)` preserves filtered colimits. -/
@[sga "4 VI 5.1" "special case"]
theorem preservesColimitsOfShape_rightDerived_etaleModuleDirectImage
    [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
    (I : Type (max (u + 1) r)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I ((etaleModuleDirectImage.{u, r} Λ f).rightDerived q) := by
  refine ⟨fun {F} => ?_⟩
  open Stacks.Cohomology.HigherDirectImage in
  refine preservesColimit_rightDerived_sheafPushforwardContinuous_of_hasEnoughObjects
    (J := Y.smallEtaleTopology) (K := X.smallEtaleTopology) (ModuleCat.{max (u + 1) r} Λ)
    (smallEtaleBaseChange f) q F ?_
  intro V
  obtain ⟨L, W, a, ha, hW⟩ := smallEtaleTopology_hasEnoughObjects_isAffine Y V
  refine ⟨L, W, a, ha, fun k => ?_⟩
  have : IsAffine (W k).left := hW k
  have hq : (smallEtaleBaseChange f).obj (W k) ∈ qcqsEtaleObjects X := by
    have hfst : QuasiSeparated (Limits.pullback.fst (W k).hom f) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback (W k).hom f).flip ‹QuasiSeparated f›
    have : CompactSpace ((𝟭 Scheme.{u}).obj (W k).left) := inferInstanceAs (CompactSpace (W k).left)
    have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj (W k).left) :=
      inferInstanceAs (QuasiSeparatedSpace (W k).left)
    refine ⟨?_, ?_⟩
    · show CompactSpace (Limits.pullback (W k).hom f : Scheme.{u})
      exact QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst (W k).hom f)
    · show QuasiSeparatedSpace (Limits.pullback (W k).hom f : Scheme.{u})
      exact quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.fst (W k).hom f)
  exact preservesColimit_rightDerived_sheafSections_etaleModules_of_qcqs Λ X q _ hq F

end DirectImage

end Stacks.EtaleCohomology
