module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FreeModuleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ResolutionBySumsOfExtensionsByZero

/-!
# Resolutions of simplicial modules by sums of free modules on representables

Every complex of simplicial `A_•`-modules is quasi-isomorphic to the colimit of a sequence of
bounded above complexes whose terms are free simplicial modules on sums of representable
presheaves of `Δ × C`; these terms are flat.

## Main definitions

* `Stacks.SimplicialModules.IsFreeSumModule`: being isomorphic to `A_•⟨∐_i h_{X_i}⟩`.

## Main results

* `Stacks.SimplicialModules.isFlat_of_isFreeSumModule`.
* `Stacks.SimplicialModules.exists_freeSumResolution`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SimplicialModules

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : SimplicialObject (Sheaf J CommRingCat.{u}))

/-- A simplicial module isomorphic to the free simplicial module on a sum of representables. -/
def IsFreeSumModule : ObjectProperty (Modules J A) := fun M =>
  ∃ (ι : Type u) (X : ι → SimplexCategory × C),
    Nonempty (M ≅ (freeModule J A).obj (∐ fun i => yoneda.obj (X i)))

/-- The zero module is the free module on the empty sum. -/
theorem containsZero_isFreeSumModule : (IsFreeSumModule J A).ContainsZero := by
  let X₀ : PEmpty.{u + 1} → SimplexCategory × C := fun i ↦ nomatch i
  have := (freeModuleAdjunction J A).leftAdjoint_preservesColimits
  exact ⟨_, (IsInitial.isInitialObj (freeModule J A) _
    (Stacks.Cohomology.isInitial_coproduct_of_isEmpty fun i ↦ yoneda.obj (X₀ i))).isZero,
    PEmpty.{u + 1}, X₀, ⟨Iso.refl _⟩⟩

/-- A biproduct of free modules on sums of representables is again one. -/
theorem isFreeSumModule_biprod (M N : Modules J A) (hM : IsFreeSumModule J A M)
    (hN : IsFreeSumModule J A N) : IsFreeSumModule J A (M ⊞ N) := by
  obtain ⟨ι, X, ⟨eM⟩⟩ := hM
  obtain ⟨κ, Y, ⟨eN⟩⟩ := hN
  have := (freeModuleAdjunction J A).leftAdjoint_preservesColimits
  exact ⟨ι ⊕ κ, Sum.elim X Y, ⟨biprod.mapIso (eM ≪≫ PreservesCoproduct.iso (freeModule J A) _)
      (eN ≪≫ PreservesCoproduct.iso (freeModule J A) _) ≪≫
    (Stacks.Cohomology.coproductSumIso
      (fun i ↦ (freeModule J A).obj (yoneda.obj (Sum.elim X Y i)))).symm ≪≫
    (PreservesCoproduct.iso (freeModule J A) _).symm⟩⟩

/-- Being a free module on a sum of representables is invariant under isomorphism. -/
theorem isFreeSumModule_of_iso (M N : Modules J A) (e : M ≅ N) (hM : IsFreeSumModule J A M) :
    IsFreeSumModule J A N := by
  obtain ⟨ι, X, ⟨eM⟩⟩ := hM
  exact ⟨ι, X, ⟨e.symm ≪≫ eM⟩⟩

/-- **Every simplicial module is a quotient of a free module on a sum of representables**:
index the sum by the pairs `(X, x)` of an object `X` and a section `x` over it. -/
theorem exists_epi_isFreeSumModule (M : Modules J A) :
    ∃ (N : Modules J A) (_ : IsFreeSumModule J A N) (p : N ⟶ M), Epi p := by
  let adj := freeModuleAdjunction J A
  let G := freeModuleRightAdjoint J A
  let ι := Σ X : SimplexCategory × C, (G.obj M).obj (op X)
  let X : ι → SimplexCategory × C := fun i ↦ i.1
  let s : (∐ fun i ↦ yoneda.obj (X i)) ⟶ G.obj M :=
    Sigma.desc fun i ↦ yonedaEquiv.symm i.2
  have hs : Epi s := by
    have (Y : (SimplexCategory × C)ᵒᵖ) : Epi (s.app Y) := by
      refine (epi_iff_surjective _).2 fun x ↦ ?_
      refine ⟨(Sigma.ι (fun i ↦ yoneda.obj (X i)) ⟨Y.unop, x⟩).app Y (𝟙 Y.unop), ?_⟩
      change (Sigma.ι (fun i ↦ yoneda.obj (X i)) ⟨Y.unop, x⟩ ≫ s).app Y (𝟙 Y.unop) = x
      simp only [s, Sigma.ι_desc]
      exact (yonedaEquiv (F := G.obj M) (X := Y.unop)).apply_symm_apply x
    exact NatTrans.epi_of_epi_app s
  refine ⟨_, ⟨ι, X, ⟨Iso.refl _⟩⟩, (adj.homEquiv _ _).symm s, ?_⟩
  rw [Adjunction.homEquiv_counit]
  have : (freeModule J A).PreservesEpimorphisms := Functor.preservesEpimorphisms_of_adjunction adj
  exact epi_comp _ _

/-- Free simplicial modules on sums of representables are flat. -/
theorem isFlat_of_isFreeSumModule {M : Modules J A} (hM : IsFreeSumModule J A M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := commRingSheaf J A) M := by
  obtain ⟨ι, X, ⟨e⟩⟩ := hM
  refine Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize (commRingSheaf J A) e.symm ?_
  let a : (commRingSheaf J A).obj ⋙ forget₂ CommRingCat RingCat ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (commRingSheaf J A)).obj := 𝟙 _
  have : Presheaf.IsLocallyInjective (simplicialProjectionTopology J) a :=
    Presheaf.isLocallyInjective_of_injective _ a fun _ _ _ h ↦ h
  have : Presheaf.IsLocallySurjective (simplicialProjectionTopology J) a :=
    Presheaf.isLocallySurjective_of_surjective _ a fun _ x ↦ ⟨x, rfl⟩
  exact Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification
    (simplicialProjectionTopology J)
    a _ (Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeObj _ _)

/-- **Every complex of simplicial modules is quasi-isomorphic to the colimit of a sequence of
bounded above complexes of free simplicial modules on sums of representables.** -/
theorem exists_freeSumResolution (K : CochainComplex (Modules J A) ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex (Modules J A) ℤ) (α : colimit D ⟶ K), QuasiIso α ∧
      (∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b) ∧
      (∀ (n : ℕ) (i : ℤ), IsFreeSumModule J A ((D.obj n).X i)) := by
  have := containsZero_isFreeSumModule J A
  obtain ⟨D, -, α, -, -, -, hLE, hterm, -, -, -, hα⟩ :=
    Stacks.DerivedTensor.ResolutionByExtensionsByZero.exists_shiftedLadder (IsFreeSumModule J A)
      (isFreeSumModule_biprod J A) (isFreeSumModule_of_iso J A) (exists_epi_isFreeSumModule J A) K
  exact ⟨D, α, hα, hLE, hterm⟩

end Stacks.SimplicialModules
