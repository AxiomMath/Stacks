module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.Modules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.AbelianULiftIntConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.Annihilator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.PrimeToTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Embedding a constructible sheaf into finite direct images of constant sheaves (Stacks 09Z6)

Let `X` be a Noetherian scheme.

* A constructible sheaf of `Λ`-modules over a Noetherian ring `Λ` embeds into a finite direct sum
  `⨁ᵢ fᵢ_* M̲ᵢ` with `fᵢ : Yᵢ ⟶ X` finite and `Mᵢ` a finite `Λ`-module
  (`Stacks.EtaleCohomology.exists_mono_biproduct_etaleModuleDirectImage_constantSheaf`).
* A constructible abelian sheaf embeds into a finite direct sum `⨁ᵢ fᵢ_* M̲ᵢ` with `fᵢ` finite
  and `Mᵢ` a finite abelian group
  (`Stacks.EtaleCohomology.exists_mono_biproduct_etaleAbelianDirectImage_constantSheaf`). It is a
  constructible sheaf of `ULift ℤ`-modules, killed by an integer because `X` is quasi-compact,
  and the modules `Mᵢ` produced for it are killed by the same integer, hence finite.

The morphisms `fᵢ` are moreover of finite presentation, which is automatic over a Noetherian base,
and they satisfy the refinement of the last sentence of Stacks 09Z6: each `Yᵢ` is integral and
maps onto an integral closed subscheme `Zᵢ` of `X`, finite étale over a nonempty open of `Zᵢ`
(`AlgebraicGeometry.IsGenericallyFiniteEtaleOntoImage`).

## Implementation notes

The coefficient ring of the module case lives in `Type (u + 1)` and the abelian groups in
`AddCommGrpCat.{u + 1}`, the universe of the library's constructibility theory (Stacks 095R and
095N are proved there); this convention is used throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

attribute [local instance 3000] Abelian.hasFiniteBiproducts

section Modules

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 09Z6 (3), with the refinement of its last sentence.** Let `X` be a Noetherian scheme,
`Λ` a Noetherian ring and `ℱ` a constructible sheaf of `Λ`-modules on `X_étale`. There is an
injective map of sheaves of modules `ℱ ⟶ ⨁ᵢ fᵢ_* M̲ᵢ` into a finite direct sum, with
`fᵢ : Yᵢ ⟶ X` finite (and of finite presentation) and `Mᵢ` a finite `Λ`-module. Moreover each
`Yᵢ` is irreducible and reduced and maps onto an irreducible and reduced closed subscheme `Zᵢ` of
`X` such that `Yᵢ ⟶ Zᵢ` is finite étale over a nonempty open of `Zᵢ`
(`AlgebraicGeometry.IsGenericallyFiniteEtaleOntoImage`). In addition, every integer killing `ℱ`
kills the `Mᵢ`.

The ring `Λ` lives in `Type (u + 1)`, the universe of the library's constructibility theory. -/
@[stacks 09Z6 "(3)"]
theorem exists_mono_biproduct_etaleModuleDirectImage_constantSheaf_and_nsmul
    {X : Scheme.{u}} [IsNoetherian X] (F : EtaleModules.{u, u + 1} Λ X)
    (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ k, Y k ⟶ X) (_ : ∀ k, IsFinite (f k))
      (_ : ∀ k, FinitePresentation (f k)) (M : Fin n → ModuleCat.{u + 1} Λ)
      (_ : ∀ k, Module.Finite Λ (M k))
      (φ : F ⟶ ⨁ fun k => (etaleModuleDirectImage.{u, u + 1} Λ (f k)).obj
        ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M k))),
      Mono φ ∧ (∀ N : ℕ, N • 𝟙 F = 0 → ∀ k (m : M k), N • m = 0) ∧
        ∀ k, IsGenericallyFiniteEtaleOntoImage (f k) := by
  obtain ⟨n, Y, f, hf, hfp, M, hM, φ, hmono, htor, hgen⟩ :=
    exists_mono_biproduct_lift_locallyConstant Λ F hF
  let e : (⨁ fun k => (etaleModuleDirectImage.{u, u + 1} Λ (f k)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ (Y k) (M k))) ≅
      ⨁ fun k => (etaleModuleDirectImage.{u, u + 1} Λ (f k)).obj
        ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M k)) :=
    biproduct.mapIso fun k => (etaleModuleDirectImage.{u, u + 1} Λ (f k)).mapIso
      (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, u + 1} Λ (Y k) (M k)).symm
  exact ⟨n, Y, f, hf, hfp, M, hM, biproduct.lift φ ≫ e.hom, mono_comp _ _, htor, hgen⟩

end Modules

section Abelian

/-- A finitely generated `ULift ℤ`-module killed by a positive integer is finite. -/
theorem finite_of_moduleFinite_uliftInt_of_nsmul_eq_zero (M : ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    [Module.Finite (ULift.{u + 1} ℤ) M] {N : ℕ} (hN : 0 < N) (h : ∀ m : M, N • m = 0) :
    Finite M := by
  have : Module.Finite ℤ (ULift.{u + 1} ℤ) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := ℤ) (M := ℤ)).symm
  have : Module.Finite ℤ M := Module.Finite.trans (ULift.{u + 1} ℤ) M
  refine Module.finite_of_fg_torsion M fun m => ⟨⟨(N : ℤ), ?_⟩, ?_⟩
  · exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN.ne')
  · change (N : ℤ) • m = 0
    rw [natCast_zsmul]
    exact h m

/-- **Stacks 09Z6 (2), with the refinement of its last sentence.** Let `X` be a Noetherian
scheme and `ℱ` a constructible abelian sheaf on `X_étale`. There is an injective map of abelian
sheaves `ℱ ⟶ ⨁ᵢ fᵢ_* M̲ᵢ` into a finite direct sum, with `fᵢ : Yᵢ ⟶ X` finite (and of finite
presentation) and `Mᵢ` a finite abelian group. Moreover each `Yᵢ` is irreducible and reduced and
maps onto an irreducible and reduced closed subscheme `Zᵢ` of `X` such that `Yᵢ ⟶ Zᵢ` is finite
étale over a nonempty open of `Zᵢ` (`AlgebraicGeometry.IsGenericallyFiniteEtaleOntoImage`).

The abelian sheaves take values in `AddCommGrpCat.{u + 1}` (constructibility in the universe
`v = 0` of `_root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf`), the universe of
the library's constructibility theory; the proof views them as sheaves of `ULift ℤ`-modules. -/
@[stacks 09Z6 "(2)", sga "4 XIV 1.11" "special case", sga "4½ Arcata 4.3.2" "(i) ⇒ (ii)"]
theorem exists_mono_biproduct_etaleAbelianDirectImage_constantSheaf_isGenericallyFiniteEtale
    {X : Scheme.{u}}
    [IsNoetherian X] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    ∃ (J : Type) (_ : Finite J) (Y : J → Scheme.{u}) (f : ∀ j, Y j ⟶ X)
      (_ : ∀ j, IsFinite (f j)) (_ : ∀ j, FinitePresentation (f j))
      (M : J → AddCommGrpCat.{u + 1}) (_ : ∀ j, Finite (M j))
      (m : F ⟶ ⨁ fun j => (etaleAbelianDirectImage.{u, 0} (f j)).obj
        ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (M j))),
      Mono m ∧ ∀ j, IsGenericallyFiniteEtaleOntoImage (f j) := by
  let E := etaleModuleULiftIntEquivalence.{0} X
  let G := E.inverse.obj F
  have hG : IsConstructibleEtaleModule (ULift.{u + 1} ℤ) G :=
    isConstructibleEtaleModule_etaleModuleULiftIntEquivalence_inverse_obj F hF
  have hT : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology (E.functor.obj G) :=
    (Stacks.Torsion.torsionSheafProperty.{u + 1, u, u + 1} X.smallEtaleTopology).prop_of_iso
      (E.counitIso.app F).symm (torsionSheafProperty_of_isConstructibleEtaleAbelianSheaf F hF)
  have hTG : IsTorsionEtaleModule (ULift.{u + 1} ℤ) X G := hT
  obtain ⟨N, hN0, -, hN⟩ := exists_nsmul_id_eq_zero_of_isConstructibleEtaleModule
    (ULift.{u + 1} ℤ) 1 G hG ((isTorsionPrimeToEtaleModule_one_iff _ X G).2 hTG)
  obtain ⟨n, Y, f, hf, hfp, M, hM, φ, hmono, htor, hgen⟩ :=
    exists_mono_biproduct_etaleModuleDirectImage_constantSheaf_and_nsmul (ULift.{u + 1} ℤ) G hG
  refine ⟨Fin n, inferInstance, Y, f, hf, hfp,
    fun k => (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}).obj (M k),
    fun k => by
      have := hM k
      exact finite_of_moduleFinite_uliftInt_of_nsmul_eq_zero (M k) hN0 (htor N hN k),
    (E.counitIso.app F).inv ≫ E.functor.map φ ≫
      (etaleModuleForgetBiproductDirectImageConstantSheafIso (ULift.{u + 1} ℤ) f M).hom, ?_, hgen⟩
  have h₁ : Mono (E.functor.map φ) := inferInstance
  have h₂ :
      Mono (etaleModuleForgetBiproductDirectImageConstantSheafIso (ULift.{u + 1} ℤ) f M).hom :=
    @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)
  have h₀ : Mono (E.counitIso.app F).inv := @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  exact @mono_comp _ _ _ _ _ _ h₀ _ (@mono_comp _ _ _ _ _ _ h₁ _ h₂)

/-- **Stacks 09Z6 (2)**, without its last sentence: a constructible abelian sheaf on a Noetherian
scheme embeds into a finite direct sum `⨁ᵢ fᵢ_* M̲ᵢ`, `fᵢ` finite of finite presentation and `Mᵢ`
finite abelian groups. -/
@[sga "4 XIV 1.11" "special case", sga "4½ Arcata 4.3.2" "(i) ⇒ (ii)"]
theorem exists_mono_biproduct_etaleAbelianDirectImage_constantSheaf {X : Scheme.{u}}
    [IsNoetherian X] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    ∃ (J : Type) (_ : Finite J) (Y : J → Scheme.{u}) (f : ∀ j, Y j ⟶ X)
      (_ : ∀ j, IsFinite (f j)) (_ : ∀ j, FinitePresentation (f j))
      (M : J → AddCommGrpCat.{u + 1}) (_ : ∀ j, Finite (M j))
      (m : F ⟶ ⨁ fun j => (etaleAbelianDirectImage.{u, 0} (f j)).obj
        ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (M j))),
      Mono m := by
  obtain ⟨J, hJ, Y, f, hf, hfp, M, hM, m, hm, -⟩ :=
    exists_mono_biproduct_etaleAbelianDirectImage_constantSheaf_isGenericallyFiniteEtale F hF
  exact ⟨J, hJ, Y, f, hf, hfp, M, hM, m, hm⟩

end Abelian

end Stacks.EtaleCohomology

end
