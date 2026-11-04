module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectiveQuasicoherentPushforward

/-!
# The associated module over a terminal affine chart is exact and lands in quasi-coherent modules

Let `Y` be an algebraic space with a terminal object `A` of its small étale site whose scheme is
affine, and let `Φ ⊣ Γ(A, -)` be `AlgebraicGeometry.Space.affineChartTildeAdjunction`.  This file
proves that `Φ` lands in the quasi-coherent modules, that the counit `Φ Γ(A, F) ⟶ F` is invertible
at every quasi-coherent `F`, and that `Φ` is exact (Stacks 01I9 at the affine chart).

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_affineChartTilde_obj`
* `AlgebraicGeometry.Space.isIso_affineChartTildeAdjunction_counit_app`
* `AlgebraicGeometry.Space.preservesFiniteLimits_affineChartTilde`

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Y : AlgebraicSpaces B S hS) {A : SmallEtale B S hS Y.1}

/-- The inverse of the equivalence `Over A ≌ C` at a terminal object is a dense subsite. -/
instance isDenseSubsite_equivalenceOfIsTerminal_inverse (hA : IsTerminal A) :
    (Over.equivalenceOfIsTerminal hA).inverse.IsDenseSubsite
      (SmallEtale.topology B S hS Y.1) ((SmallEtale.topology B S hS Y.1).over A) := by
  have : (Over.equivalenceOfIsTerminal hA).functor.IsCocontinuous
      ((SmallEtale.topology B S hS Y.1).over A) (SmallEtale.topology B S hS Y.1) :=
    inferInstanceAs ((Over.forget A).IsCocontinuous _ _)
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous
    ((SmallEtale.topology B S hS Y.1).over A) (SmallEtale.topology B S hS Y.1)
    (Over.equivalenceOfIsTerminal hA)

section Chart

variable (hA : IsTerminal A) [IsAffine (chartScheme A)]

omit [IsAffine (chartScheme A)] in
/-- The equivalence `Mod(Y) ≌ Mod(chart scheme, étale)` of a terminal chart carries
quasi-coherent modules to quasi-coherent modules, backwards. -/
theorem isQuasicoherentOnSite_terminalChartModuleEquivalence_inverse_obj
    (N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS Y A)))
    (hN : N.IsQuasicoherentOnSite) :
    ((terminalChartModuleEquivalence B S hS Y hA).inverse.obj N).IsQuasicoherentOnSite := by
  let E₁ := terminalChartOverEquivalence B S hS Y hA
  let E₂ := chartModuleReindexEquivalence B S hS Y A
  let E₃ := representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS Y A)
  have h₃ : (E₃.functor.obj N).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS _ N).2 hN
  have h₂ : (E₂.inverse.obj (E₃.functor.obj N)).IsQuasicoherentOnSite := by
    refine (@Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff _ _ _ _
      ((SmallEtale.topology B S hS Y.1).over A)
      (SmallEtale.topology B S hS (chartSpace B S hS Y A).1)
      (SmallEtale.chartLocalizationEquivalence B S hS Y.1 A)
      (isContinuous_chartLocalization_chartSpace B S hS Y A)
      ((structureRingSheaf B S hS Y).over A)
      (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS Y A) _).1 ?_
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso (E₂.counitIso.app _).symm h₃
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff
    (J := SmallEtale.topology B S hS Y.1) (J' := (SmallEtale.topology B S hS Y.1).over A)
    (Over.equivalenceOfIsTerminal hA) (structureRingSheaf B S hS Y) _).1 ?_
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso (E₁.counitIso.app _).symm h₂

/-- `chartTildeFunctor` lands in the quasi-coherent modules. -/
theorem isQuasicoherentOnSite_chartTildeFunctor_obj (M : ModuleCat.{u} Γ(chartScheme A, ⊤)) :
    ((chartTildeFunctor B S hS Y hA).obj M).IsQuasicoherentOnSite := by
  let G := (Scheme.Modules.restrictFunctor (chartScheme A).isoSpec.hom).obj
    ((tilde.functor Γ(chartScheme A, ⊤)).obj M)
  have hG : (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS Y A).left.property).obj G |>.IsQuasicoherentOnSite :=
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence' (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS Y A).left.property).functor.obj
        ⟨G, inferInstance⟩).property
  exact isQuasicoherentOnSite_terminalChartModuleEquivalence_inverse_obj B S hS Y hA _ hG

/-- **`Φ` lands in the quasi-coherent modules.** -/
theorem isQuasicoherentOnSite_affineChartTilde_obj
    (M : ModuleCat.{u} ((structureRingSheaf B S hS Y).obj.obj (op A))) :
    ((affineChartTilde B S hS Y hA).obj M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_chartTildeFunctor_obj B S hS Y hA _

/-- **The counit `Φ Γ(A, F) ⟶ F` is invertible at a quasi-coherent `F`.** -/
theorem isIso_affineChartTildeAdjunction_counit_app (F : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((affineChartTildeAdjunction B S hS Y hA).counit.app F) := by
  let adj := affineChartTildeAdjunction B S hS Y hA
  have hΓ : IsIso ((SheafOfModules.evaluation (structureRingSheaf B S hS Y) (op A)).map
      (adj.counit.app F)) := by
    have : IsIso (adj.unit.app ((SheafOfModules.evaluation (structureRingSheaf B S hS Y)
        (op A)).obj F) ≫ (SheafOfModules.evaluation (structureRingSheaf B S hS Y) (op A)).map
          (adj.counit.app F)) := by
      rw [adj.right_triangle_components F]
      infer_instance
    exact IsIso.of_isIso_comp_left (adj.unit.app _) _
  exact isIso_of_bijective_val_app_isTerminal B S hS Y
    (isQuasicoherentOnSite_affineChartTilde_obj B S hS Y hA _) hF _ hA ‹_›
    (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation (structureRingSheaf B S hS Y) (op A)).map (adj.counit.app F)))

/-- `Φ` is right exact, being a left adjoint. -/
instance preservesFiniteColimits_affineChartTilde :
    PreservesFiniteColimits (affineChartTilde B S hS Y hA) := by
  have := (affineChartTildeAdjunction B S hS Y hA).leftAdjoint_preservesColimits
  infer_instance

include hA in
/-- A quasi-coherent module with no sections over the terminal affine chart is zero. -/
theorem isZero_of_isZero_val_app_of_isQuasicoherentOnSite (K : Modules.{u, u} B S hS Y.1 Y.2)
    (hK : K.IsQuasicoherentOnSite)
    (h : IsZero ((SheafOfModules.evaluation (structureRingSheaf B S hS Y) (op A)).obj K)) :
    IsZero K := by
  have : IsIso (0 : K ⟶ K) := by
    refine isIso_of_bijective_val_app_isTerminal B S hS Y hK hK 0 hA ‹_› ?_
    have : Subsingleton (K.val.obj (op A)) := (ModuleCat.subsingleton_of_isZero h :)
    exact ⟨fun x y _ ↦ Subsingleton.elim x y, fun y ↦ ⟨y, Subsingleton.elim _ _⟩⟩
  exact (IsZero.iff_id_eq_zero K).2 (by rw [← IsIso.hom_inv_id (0 : K ⟶ K), zero_comp])

/-- **`Φ` preserves monomorphisms.** -/
theorem mono_affineChartTilde_map
    {M N : ModuleCat.{u} ((structureRingSheaf B S hS Y).obj.obj (op A))}
    (f : M ⟶ N) [Mono f] : Mono ((affineChartTilde B S hS Y hA).map f) := by
  let adj := affineChartTildeAdjunction B S hS Y hA
  let Γ : Modules.{u, u} B S hS Y.1 Y.2 ⥤ _ :=
    SheafOfModules.evaluation (structureRingSheaf B S hS Y) (op A)
  let Φf := (affineChartTilde B S hS Y hA).map f
  have hnat : adj.unit.app M ≫ Γ.map Φf = f ≫ adj.unit.app N := (adj.unit.naturality f).symm
  have hΓ : Mono (Γ.map Φf) := by
    have : Γ.map Φf = inv (adj.unit.app M) ≫ f ≫ adj.unit.app N := by
      rw [← hnat, IsIso.inv_hom_id_assoc]
    rw [this]
    have : Mono (adj.unit.app N) := IsIso.mono_of_iso _
    have : Mono (inv (adj.unit.app M)) := IsIso.mono_of_iso _
    have : Mono (f ≫ adj.unit.app N) := mono_comp _ _
    exact mono_comp _ _
  have hKq : (kernel Φf).IsQuasicoherentOnSite :=
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).prop_kernel
      Φf (isQuasicoherentOnSite_affineChartTilde_obj B S hS Y hA M)
      (isQuasicoherentOnSite_affineChartTilde_obj B S hS Y hA N)
  have : Γ.PreservesMonomorphisms := Functor.preservesMonomorphisms_of_adjunction adj
  have : Γ.IsRightAdjoint := adj.isRightAdjoint
  have : Γ.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isRightAdjoint Γ
  have h1 : Γ.map (kernel.ι Φf ≫ Φf) = 0 := by
    rw [kernel.condition]
    exact Γ.map_zero _ _
  have h0 : Γ.map (kernel.ι Φf) = 0 :=
    (cancel_mono (Γ.map Φf)).1 ((Γ.map_comp _ _).symm.trans (h1.trans zero_comp.symm))
  have hm : Mono (Γ.map (kernel.ι Φf)) := Γ.map_mono _
  have hz : IsZero (Γ.obj (kernel Φf)) := IsZero.of_mono_eq_zero _ h0
  exact Preadditive.mono_of_isZero_kernel _
    (isZero_of_isZero_val_app_of_isQuasicoherentOnSite B S hS Y hA _ hKq hz)

/-- **`Φ` is additive**, being a left adjoint. -/
instance additive_affineChartTilde : (affineChartTilde B S hS Y hA).Additive := by
  let adj := affineChartTildeAdjunction B S hS Y hA
  have : PreservesColimitsOfShape (Discrete WalkingPair) (affineChartTilde B S hS Y hA) := by
    have := adj.leftAdjoint_preservesColimits.{0, 0}
    infer_instance
  have : (affineChartTilde B S hS Y hA).IsLeftAdjoint := adj.isLeftAdjoint
  have : (affineChartTilde B S hS Y hA).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : PreservesBinaryBiproducts (affineChartTilde B S hS Y hA) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **`Φ` is exact.** -/
instance preservesFiniteLimits_affineChartTilde :
    PreservesFiniteLimits (affineChartTilde B S hS Y hA) := by
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun T hT => ?_
  have := hT.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1
    (preservesFiniteColimits_affineChartTilde B S hS Y hA) T hT).1,
    mono_affineChartTilde_map B S hS Y hA _⟩

end Chart

end AlgebraicGeometry.Space

end
