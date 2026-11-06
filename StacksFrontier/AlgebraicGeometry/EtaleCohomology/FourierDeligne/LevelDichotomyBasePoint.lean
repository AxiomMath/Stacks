module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCoefficientVanishing

/-!
# The level dichotomy of the monodromy modules does not depend on the base point

Let `X` be a connected scheme of a big étale site, `Λ` a finite commutative ring and `F` a locally
constant sheaf of finite type of `Λ`-modules on `X_étale`. If the monodromy module of `F` at one
geometric point `x₀` (Tag 0DV5 on Mathlib's small étale site) satisfies the level dichotomy at the
exponents `N, c₀` of `ℓ` (`Stacks.EtaleCohomology.ContinuousModuleLevelDichotomy`), then so does
its monodromy module at every geometric point `x`
(`Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_basePoint`).

Indeed a stable submodule `W` of the monodromy module at `x` with `ℓ^N W ≠ 0` is a finite
continuous module `M_W` with a monomorphism into it
(`Stacks.EtaleCohomology.finiteTypeContinuousModuleOfStable`), which the dictionary at `x` carries
to a subsheaf `K ↪ F` not killed by `ℓ^N`. The dictionary at `x₀` carries `K ↪ F` to a monomorphism
of monodromy modules at `x₀`, through which `ℓ^{c₀}` factors by the dichotomy at `x₀`; the
factorization comes from a morphism `F ⟶ K` (full faithfulness), which the dictionary at `x`
carries back to a factorization of `ℓ^{c₀}` through `W`.

## Main definitions

* `Stacks.EtaleCohomology.finiteTypeContinuousModuleOfStable`: a stable submodule as a finite
  continuous module, with its inclusion
  `Stacks.EtaleCohomology.finiteTypeContinuousModuleOfStableι`.

## Main results

* `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_basePoint`: for `X` connected, the
  level dichotomy of the monodromy module at one geometric point gives it at every geometric
  point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u v w

namespace Stacks.EtaleCohomology

section Module

variable {Λ : Type} [CommRing Λ] [Finite Λ] {H : Type v} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H]

/-- **A stable submodule of a finite continuous module, as a finite continuous module.** -/
def finiteTypeContinuousModuleOfStable (P : FiniteTypeContinuousModule.{0, v, w} Λ H)
    (W : Submodule Λ P.obj.obj.obj.V) (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).asHom.hom x ∈ W) :
    FiniteTypeContinuousModule.{0, v, w} Λ H :=
  haveI : Finite (ToType P.obj.obj.obj.V) := (moduleCat_isFG_iff_finite Λ _).mp P.property
  ⟨ofRepresentation (R := Λ) (M := W)
      { toFun := fun h => (P.obj.obj.obj.ρ h).asHom.hom.restrict (fun x hx => hW h x hx)
        map_one' := by
          ext ⟨x, hx⟩
          change (P.obj.obj.obj.ρ 1).asHom.hom x = x
          rw [map_one]
          rfl
        map_mul' := fun g g' => by
          ext ⟨x, hx⟩
          change (P.obj.obj.obj.ρ (g * g')).asHom.hom x =
            (P.obj.obj.obj.ρ g).asHom.hom ((P.obj.obj.obj.ρ g').asHom.hom x)
          rw [map_mul]
          rfl }
      ((isContinuous_actionOfRepresentation_iff _).2 fun x => by
        convert isOpen_stabilizer Λ H P.obj x.1 using 1
        ext g
        exact Subtype.ext_iff),
    (ModuleCat.isFG_iff _).2 (show Module.Finite Λ W from Module.Finite.of_finite)⟩

/-- The inclusion of `Stacks.EtaleCohomology.finiteTypeContinuousModuleOfStable`. -/
def finiteTypeContinuousModuleOfStableι (P : FiniteTypeContinuousModule.{0, v, w} Λ H)
    (W : Submodule Λ P.obj.obj.obj.V) (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).asHom.hom x ∈ W) :
    finiteTypeContinuousModuleOfStable P W hW ⟶ P :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    ⟨ModuleCat.ofHom W.subtype, fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)⟩))

/-- The inclusion `Stacks.EtaleCohomology.finiteTypeContinuousModuleOfStableι` sends an element of
`W` to itself. -/
theorem finiteTypeContinuousModuleOfStableι_apply (P : FiniteTypeContinuousModule.{0, v, w} Λ H)
    (W : Submodule Λ P.obj.obj.obj.V) (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).asHom.hom x ∈ W) (x : W) :
    (finiteTypeContinuousModuleOfStableι P W hW).hom.hom.hom.hom.hom x = x.1 := rfl

/-- The inclusion `Stacks.EtaleCohomology.finiteTypeContinuousModuleOfStableι` is a
monomorphism. -/
instance mono_finiteTypeContinuousModuleOfStableι (P : FiniteTypeContinuousModule.{0, v, w} Λ H)
    (W : Submodule Λ P.obj.obj.obj.V) (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).asHom.hom x ∈ W) :
    Mono (finiteTypeContinuousModuleOfStableι P W hW) := by
  let Uf : FiniteTypeContinuousModule.{0, v, w} Λ H ⥤ ModuleCat.{w} Λ :=
    finiteTypeContinuousModuleι Λ H ⋙ Stacks.Injectives.continuousModuleUnderlying Λ H
  refine ⟨fun {Z} a b hab => ?_⟩
  have h := congrArg Uf.map hab
  rw [Functor.map_comp, Functor.map_comp] at h
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext ?_))
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z

/-- The underlying module functor on finite continuous modules is additive. -/
private theorem additive_finiteTypeContinuousModuleι_comp_underlying (Λ : Type) [CommRing Λ]
    [Finite Λ] (H : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    (finiteTypeContinuousModuleι.{0, v, w} Λ H ⋙
      Stacks.Injectives.continuousModuleUnderlying Λ H).Additive := by
  have : (finiteTypeContinuousModuleι.{0, v, w} Λ H).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have := additive_continuousModuleToModuleCat.{0, v, w} Λ H
  infer_instance

/-- An integer not killing a stable submodule does not kill
`Stacks.EtaleCohomology.finiteTypeContinuousModuleOfStable`. -/
theorem nsmul_id_finiteTypeContinuousModuleOfStable_ne_zero
    (P : FiniteTypeContinuousModule.{0, v, w} Λ H) (W : Submodule Λ P.obj.obj.obj.V)
    (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).asHom.hom x ∈ W) {n : ℕ} (hne : ∃ x ∈ W, n • x ≠ 0) :
    n • 𝟙 (finiteTypeContinuousModuleOfStable P W hW) ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := hne
  intro h0
  apply hw0
  let Uf : FiniteTypeContinuousModule.{0, v, w} Λ H ⥤ ModuleCat.{w} Λ :=
    finiteTypeContinuousModuleι Λ H ⋙ Stacks.Injectives.continuousModuleUnderlying Λ H
  have : Uf.Additive := additive_finiteTypeContinuousModuleι_comp_underlying Λ H
  have h1 := congrArg Uf.map h0
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h1
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1) ⟨w, hw⟩
  change n • (⟨w, hw⟩ : W) = 0 at h2
  simpa using congrArg Subtype.val h2

/-- If `n • 𝟙` factors through the inclusion
`Stacks.EtaleCohomology.finiteTypeContinuousModuleOfStableι`, then `n` maps everything into the
stable submodule. -/
theorem nsmul_mem_of_comp_finiteTypeContinuousModuleOfStableι_eq
    (P : FiniteTypeContinuousModule.{0, v, w} Λ H) (W : Submodule Λ P.obj.obj.obj.V)
    (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).asHom.hom x ∈ W) {n : ℕ}
    (r : P ⟶ finiteTypeContinuousModuleOfStable P W hW)
    (hr : r ≫ finiteTypeContinuousModuleOfStableι P W hW = n • 𝟙 P) (y : P.obj.obj.obj.V) :
    n • y ∈ W := by
  let Uf : FiniteTypeContinuousModule.{0, v, w} Λ H ⥤ ModuleCat.{w} Λ :=
    finiteTypeContinuousModuleι Λ H ⋙ Stacks.Injectives.continuousModuleUnderlying Λ H
  have : Uf.Additive := additive_finiteTypeContinuousModuleι_comp_underlying Λ H
  have h1 := congrArg Uf.map hr
  rw [Functor.map_comp, Functor.map_nsmul, CategoryTheory.Functor.map_id] at h1
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1) y
  change (Uf.map (finiteTypeContinuousModuleOfStableι P W hW)).hom ((Uf.map r).hom y) =
    n • y at h2
  rw [← h2]
  exact Subtype.property ((Uf.map r).hom y)

end Module

section Sheaf

attribute [local instance] moduleCat_hasLimitsOfSize

variable {Λ : Type} [CommRing Λ] [Finite Λ]

/-- **An equivalence with the finite continuous modules is additive**, in both directions. -/
theorem additive_of_equivalence_finiteTypeContinuousModule {C : Type*} [Category* C]
    [Preadditive C] {G : Type v} [Group G] [TopologicalSpace G]
    (E : C ≌ FiniteTypeContinuousModule.{0, v, w} Λ G) :
    E.inverse.Additive ∧ E.functor.Additive := by
  have : PreservesLimitsOfShape (Discrete WalkingPair) E.inverse :=
    have := E.toAdjunction.rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  have : E.inverse.IsLeftAdjoint := ⟨_, ⟨E.symm.toAdjunction⟩⟩
  have : E.inverse.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hinv : E.inverse.Additive := additive_of_preservesBinaryProducts (F := E.inverse)
  have : E.symm.functor.Additive := hinv
  exact ⟨hinv, Equivalence.inverse_additive E.symm⟩

/-- **The level dichotomy of the monodromy modules is independent of the base point**: for `X`
connected and `F` locally constant of finite type, the dichotomy at one geometric point `x₀`
gives it at every geometric point `x`. -/
theorem continuousModuleLevelDichotomy_of_basePoint (B : BigEtaleSite.{u}) (X : B.Scheme)
    [ConnectedSpace X.1] (x₀ x : GeometricPoint X.1) {F : EtaleModules.{u, 0} Λ X.1}
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology F)
    {ℓ N c₀ : ℕ}
    (h₀ : ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x₀ Λ).functor.obj ⟨F, hF⟩)
      ℓ N c₀) :
    ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj ⟨F, hF⟩)
      ℓ N c₀ := by
  let E₀ := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x₀ Λ
  let E := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ
  let FX : ObjectProperty.FullSubcategory
      (fun F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F) :=
    ⟨F, hF⟩
  have : E₀.functor.Additive := (additive_of_equivalence_finiteTypeContinuousModule E₀).2
  have : E.functor.Additive := (additive_of_equivalence_finiteTypeContinuousModule E).2
  have : E.inverse.Additive := (additive_of_equivalence_finiteTypeContinuousModule E).1
  have : E.inverse.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction E.toAdjunction
  have : E₀.functor.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction E₀.symm.toAdjunction
  intro W hW hne y
  let MW := finiteTypeContinuousModuleOfStable (E.functor.obj FX) W hW
  let ι := finiteTypeContinuousModuleOfStableι (E.functor.obj FX) W hW
  let κ : E.inverse.obj MW ⟶ FX := E.inverse.map ι ≫ E.unitInv.app FX
  have : Mono κ := mono_comp _ _
  have hθ : E.functor.map κ = E.counit.app MW ≫ ι := by
    show E.functor.map (E.inverse.map ι ≫ E.unitInv.app FX) = _
    rw [Functor.map_comp, Equivalence.fun_inv_map, Category.assoc, Category.assoc,
      E.counitInv_functor_comp FX, Category.comp_id]
  have hMW : ℓ ^ N • 𝟙 MW ≠ 0 := nsmul_id_finiteTypeContinuousModuleOfStable_ne_zero _ W hW hne
  have hK₀ : ℓ ^ N • 𝟙 (E₀.functor.obj (E.inverse.obj MW)) ≠ 0 := fun h0 =>
    hMW <| E.inverse.map_injective <| by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
      exact E₀.functor.map_injective <| by
        rwa [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  have : Mono (show E₀.functor.obj (E.inverse.obj MW) ⟶ (finiteTypeContinuousModuleRes Λ
      (ContinuousMonoidHom.id (EtaleFundamentalGroup X.1 x₀))).obj (E₀.functor.obj FX) from
      E₀.functor.map κ) := E₀.functor.map_mono κ
  obtain ⟨r₀, hr₀⟩ := exists_comp_eq_nsmul_of_forall_submodule
    (ContinuousMonoidHom.id (EtaleFundamentalGroup X.1 x₀))
    Function.surjective_id (M := E₀.functor.obj FX) (E₀.functor.map κ) ℓ N c₀ h₀ hK₀
  obtain ⟨r, hr'⟩ : ∃ r : FX ⟶ E.inverse.obj MW, E₀.functor.map r = r₀ :=
    ⟨E₀.functor.preimage (X := FX) (Y := E.inverse.obj MW) r₀, E₀.functor.map_preimage _⟩
  have hr : r ≫ κ = ℓ ^ c₀ • 𝟙 FX := E₀.functor.map_injective <| by
    rwa [Functor.map_comp, hr', Functor.map_nsmul, CategoryTheory.Functor.map_id]
  refine nsmul_mem_of_comp_finiteTypeContinuousModuleOfStableι_eq _ W hW
    (E.functor.map r ≫ E.counit.app MW) ?_ y
  rw [Category.assoc, ← hθ, ← Functor.map_comp, hr, Functor.map_nsmul,
    CategoryTheory.Functor.map_id]

end Sheaf

end Stacks.EtaleCohomology

end
