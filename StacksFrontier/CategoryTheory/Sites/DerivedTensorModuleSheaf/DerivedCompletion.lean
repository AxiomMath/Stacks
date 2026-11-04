module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.KoszulReduction
public import StacksFrontier.Homology.DerivedComplete.DerivedLimitLeftAdjoint

/-!
# Derived completion in the constant Noetherian case

Let `(C, J)` be a site, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. The inclusion of the derived
complete objects of `D(C, Λ)` has a left adjoint, sending `K` to the derived limit
`K^∧ = R lim (K ⊗_Λ^L \underline{Λ/Iⁿ})`, with unit the reduction maps; in particular `K` is
derived complete exactly when `K = R lim (K ⊗_Λ^L \underline{Λ/Iⁿ})`.

Derived completeness of `K ∈ D(C, Λ)` is `IsDerivedComplete I K`: `T(K, f) = 0` for every
`f ∈ I`, the derived limit `T(K, f)` of `⋯ →f K →f K` being formed in `D(C, Λ)`. For the
constant ring `Λ` this is the definition by local sections of the ideal sheaf, the local
sections of `\underline{I}` being locally `Λ`-linear combinations of generators of `I`
([Stacks, Tag 0999]).

## Main results

* `Stacks.ModuleSheaf.exists_leftAdjoint_isDerivedLimitWithProjections_derivedReductionTower`:
  the left adjoint `K ↦ R lim (K ⊗^L \underline{Λ/Iⁿ})`.
* `Stacks.ModuleSheaf.isDerivedComplete_iff_isDerivedLimitWithProjections_derivedReductionTower`:
  `K` is derived complete if and only if `K = R lim (K ⊗^L \underline{Λ/Iⁿ})`.
* `Stacks.ModuleSheaf.isIso_whiskerRight_of_isDerivedLimitWithProjections_derivedReductionTower`:
  the map `K → R lim (K ⊗^L \underline{Λ/Iⁿ})` becomes an isomorphism after tensoring with an
  object on which `I` acts by zero.
* `Stacks.ModuleSheaf.derivedReductionTowerConstantSheafIso`: the derived reductions of
  `\underline{Λ}` are the constant sheaves `\underline{Λ/Iⁿ}`.

## References

* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open NoetherianAdicCompletion

universe t w v u

namespace Stacks.ModuleSheaf

open AlgebraicGeometry.ProEtale (adicQuotientCone)

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] [IsNoetherianRing Λ] (I : Ideal Λ)

/-- **Derived limits of the reductions are reflections onto the derived complete objects.** For
every `K ∈ D(C, Λ)`, every derived limit `L` of `n ↦ K ⊗^L \underline{Λ/Iⁿ}` and every map
`η : K → L` compatible with the reductions, every map from `K` to a derived complete object
factors uniquely through `η`. -/
theorem bijective_comp_of_isDerivedLimitWithProjections_derivedReductionTower
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (π : ∀ n : ℕ, L ⟶ (derivedReductionTower J Λ I K).obj ⟨n⟩)
    (hL : IsDerivedLimitWithProjections (derivedReductionTower J Λ I K) L π)
    (η : K ⟶ L) (hη : ∀ n : ℕ, η ≫ π n = (derivedReductionMap J Λ I K).app ⟨n⟩)
    (E : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (hE : IsDerivedComplete I E) :
    Function.Bijective fun ψ : L ⟶ E ↦ η ≫ ψ := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I : I.FG)
  have hI : I = Ideal.span (Set.range f) := hf.symm
  let Y := DerivedCategory.Q.obj (koszulComplex J Λ f)
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorRight J Λ Y
  have := preservesLimitsOfShape_tensorRight_koszulComplex (J := J) f
  exact (DerivedComplete.isDerivedComplete_and_bijective_of_derivedLimit f I hI
    (MonoidalCategory.tensorRight Y) (fun X ↦ exists_cone_chain_tensor_koszulComplex f X)
    (derivedReductionMap J Λ I K) (fun n ↦ isDerivedComplete_derivedReductionTower_obj J Λ I K ⟨n⟩)
    (hasEventualInverses_tensorRight_derivedReductionMap I f 1 (by rw [pow_one, hI]) K)
    hL η hη).2 E hE

/-- **The derived completion functor in the constant Noetherian case.** The inclusion of the
derived complete objects of `D(C, Λ)` has a left adjoint `K ↦ K^∧`, where `K^∧` is a derived limit
`R lim (K ⊗_Λ^L \underline{Λ/Iⁿ})` with projections natural in `K`, whose composites with the
unit `K → K^∧` are the reductions `K → K ⊗_Λ^L \underline{Λ/Iⁿ}`. -/
@[stacks 099M "the left adjoint is `K ↦ R lim (K ⊗^L Λ/Iⁿ)`"]
theorem exists_leftAdjoint_isDerivedLimitWithProjections_derivedReductionTower :
    let P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :=
      fun K ↦ IsDerivedComplete I K
    ∃ (Lf : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) ⥤ P.FullSubcategory) (adj : Lf ⊣ P.ι)
      (π : ∀ n : ℕ, Lf ⋙ P.ι ⟶
        derivedReductionTowerFunctor J Λ I ⋙ (evaluation ℕᵒᵖ _).obj ⟨n⟩),
      (∀ K, IsDerivedLimitWithProjections (derivedReductionTower J Λ I K) ((Lf ⋙ P.ι).obj K)
        fun n ↦ (π n).app K) ∧
      ∀ K (n : ℕ), adj.unit.app K ≫ (π n).app K = (derivedReductionMap J Λ I K).app ⟨n⟩ :=
  DerivedComplete.exists_leftAdjoint_isDerivedLimitWithProjections I
    (derivedReductionTowerFunctor J Λ I) (derivedReductionNatTrans J Λ I)
    (fun K n ↦ isDerivedComplete_derivedReductionTower_obj J Λ I K ⟨n⟩)
    (bijective_comp_of_isDerivedLimitWithProjections_derivedReductionTower J Λ I)

/-- **`K` is derived complete if and only if `K = R lim (K ⊗_Λ^L \underline{Λ/Iⁿ})`**, i.e.
`K`, with the reductions `K → K ⊗_Λ^L \underline{Λ/Iⁿ}`, is a derived limit of the reductions. -/
@[stacks 099M "in particular: `K` is complete iff `K = R lim (K ⊗^L Λ/Iⁿ)`"]
theorem isDerivedComplete_iff_isDerivedLimitWithProjections_derivedReductionTower
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    IsDerivedComplete I K ↔ IsDerivedLimitWithProjections (derivedReductionTower J Λ I K) K
      fun n ↦ (derivedReductionMap J Λ I K).app ⟨n⟩ :=
  DerivedComplete.isDerivedComplete_iff_isDerivedLimitWithProjections I
    (derivedReductionTowerFunctor J Λ I) (derivedReductionNatTrans J Λ I)
    (fun K n ↦ isDerivedComplete_derivedReductionTower_obj J Λ I K ⟨n⟩)
    (bijective_comp_of_isDerivedLimitWithProjections_derivedReductionTower J Λ I) K

omit [IsNoetherianRing Λ] in
/-- **The derived reductions of `\underline{Λ}`** are the constant sheaves `\underline{Λ/Iⁿ}`:
the tower `n ↦ \underline{Λ}[0] ⊗_Λ^L \underline{Λ/Iⁿ}[0]` is `n ↦ \underline{Λ/Iⁿ}[0]`, through
the identification of `\underline{Λ}[0]` with the unit object and the left unitor. -/
def derivedReductionTowerConstantSheafIso :
    derivedReductionTower J Λ I ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf J (ModuleCat.{w} Λ)).obj (ModuleCat.of Λ Λ))) ≅ quotientPowerTower J Λ I :=
  NatIso.ofComponents (fun n ↦ whiskerRightIso (derivedTensorUnitIso J Λ).symm
      ((quotientPowerTower J Λ I).obj n) ≪≫ λ_ ((quotientPowerTower J Λ I).obj n))
    (fun g ↦ by
      simp only [Functor.comp_map, curriedTensor_obj_map, Iso.trans_hom, whiskerRightIso_hom,
        Iso.symm_hom, Category.assoc]
      rw [whisker_exchange_assoc, leftUnitor_naturality])

omit [IsNoetherianRing Λ] in
/-- Under `derivedReductionTowerConstantSheafIso`, the reductions of `\underline{Λ}` are the maps
`\underline{Λ} → \underline{Λ/Iⁿ}` induced by the quotient maps `Λ → Λ/Iⁿ`. -/
@[reassoc]
theorem derivedReductionMap_app_derivedReductionTowerConstantSheafIso_hom_app (n : ℕᵒᵖ) :
    (derivedReductionMap J Λ I ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf J (ModuleCat.{w} Λ)).obj (ModuleCat.of Λ Λ)))).app n ≫
      (derivedReductionTowerConstantSheafIso J Λ I).hom.app n =
    (DerivedCategory.singleFunctor _ 0).map ((constantSheaf J (ModuleCat.{w} Λ)).map
      ((adicQuotientCone Λ I (ModuleCat.of Λ Λ)).app n)) := by
  rw [derivedReductionMap_app, unitToQuotientPowerTower_app]
  simp only [derivedReductionTowerConstantSheafIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    whiskerRightIso_hom, Iso.symm_hom, Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality, unitors_equal, rightUnitor_naturality_assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]

omit [IsNoetherianRing Λ] in
/-- The reductions of `\underline{Λ}` are the maps `\underline{Λ} → \underline{Λ/Iⁿ}` induced by
the quotient maps `Λ → Λ/Iⁿ`, read through `derivedReductionTowerConstantSheafIso`. -/
theorem derivedReductionMap_app_constantSheaf (n : ℕᵒᵖ) :
    (derivedReductionMap J Λ I ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf J (ModuleCat.{w} Λ)).obj (ModuleCat.of Λ Λ)))).app n =
    (DerivedCategory.singleFunctor _ 0).map ((constantSheaf J (ModuleCat.{w} Λ)).map
      ((adicQuotientCone Λ I (ModuleCat.of Λ Λ)).app n)) ≫
        (derivedReductionTowerConstantSheafIso J Λ I).inv.app n := by
  rw [← derivedReductionMap_app_derivedReductionTowerConstantSheafIso_hom_app_assoc,
    Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

omit [IsNoetherianRing Λ] in
open Pretriangulated in
/-- **An object killed by `Kos(f)` is killed by every object on which `I` acts by zero.** Let
`f₁, …, f_r` generate `I`. If `Z ⊗_Λ^L Kos(f) = 0`, then `Z ⊗_Λ^L N = 0` for every `N` on which
every `x ∈ I` acts by zero. -/
theorem isZero_tensor_of_isZero_tensor_koszulComplex {r : ℕ} (f : Fin r → Λ)
    (hI : I = Ideal.span (Set.range f)) {Z N : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))}
    (hZ : IsZero (Z ⊗ DerivedCategory.Q.obj (koszulComplex J Λ f)))
    (hN : ∀ x ∈ I, x • 𝟙 N = 0) : IsZero (Z ⊗ N) := by
  obtain ⟨M, _, _, hM, ⟨e₀⟩, ⟨e⟩⟩ := exists_cone_chain_tensor_koszulComplex f Z
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorRight J Λ N
  have h : ∀ i : Fin (r + 1), IsZero (M i ⊗ N) := by
    refine Fin.reverseInduction ((MonoidalCategory.tensorRight N).map_isZero (hZ.of_iso e))
      (fun i hi ↦ ?_)
    have hT := (MonoidalCategory.tensorRight N).map_distinguished _ (hM i)
    have h₁ : IsIso ((f i • 𝟙 (M i.castSucc)) ▷ N) :=
      (Triangle.isZero₃_iff_isIso₁ _ hT).1 hi
    have h₀ : (f i • 𝟙 (M i.castSucc)) ▷ N = 0 := by
      rw [derived_smul_id_whiskerRight, ← derived_whiskerLeft_smul_id,
        hN (f i) (hI ▸ Ideal.subset_span ⟨i, rfl⟩), ← zero_smul Λ (𝟙 N),
        derived_whiskerLeft_smul_id, zero_smul]
    rw [h₀] at h₁
    exact IsZero.of_mono_zero _ (M i.castSucc ⊗ N)
  exact (h 0).of_iso ((MonoidalCategory.tensorRight N).mapIso e₀.symm)

open Pretriangulated in
/-- **The derived completion becomes an isomorphism after tensoring with an `I`-torsion object.**
Let `L` be a derived limit of `n ↦ K ⊗_Λ^L \underline{Λ/Iⁿ}` and `η : K → L` compatible with the
reductions. For every `N` on which every `x ∈ I` acts by zero, `η ⊗ N : K ⊗_Λ^L N → L ⊗_Λ^L N`
is an isomorphism. -/
theorem isIso_whiskerRight_of_isDerivedLimitWithProjections_derivedReductionTower
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (π : ∀ n : ℕ, L ⟶ (derivedReductionTower J Λ I K).obj ⟨n⟩)
    (hL : IsDerivedLimitWithProjections (derivedReductionTower J Λ I K) L π)
    (η : K ⟶ L) (hη : ∀ n : ℕ, η ≫ π n = (derivedReductionMap J Λ I K).app ⟨n⟩)
    (N : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (hN : ∀ x ∈ I, x • 𝟙 N = 0) :
    IsIso (η ▷ N) := by
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I : I.FG)
  have hI : I = Ideal.span (Set.range f) := hf.symm
  let Y := DerivedCategory.Q.obj (koszulComplex J Λ f)
  obtain ⟨s, hs⟩ := exists_commShift_isTriangulated_tensorRight J Λ Y
  have := preservesLimitsOfShape_tensorRight_koszulComplex (J := J) f
  have hY : IsIso (η ▷ Y) :=
    isIso_of_comp_eq_of_hasEventualInverses_const _
      (hasEventualInverses_tensorRight_derivedReductionMap I f 1 (by rw [pow_one, hI]) K)
      (hL.map (MonoidalCategory.tensorRight Y)) ((MonoidalCategory.tensorRight Y).map η)
      (fun n ↦ by simp [Y, ← hη n])
  obtain ⟨Z, _, _, hT⟩ := distinguished_cocone_triangle η
  have hZ : IsZero (Z ⊗ Y) :=
    (Triangle.isZero₃_iff_isIso₁ _ ((MonoidalCategory.tensorRight Y).map_distinguished _ hT)).2 hY
  obtain ⟨s', hs'⟩ := exists_commShift_isTriangulated_tensorRight J Λ N
  exact (Triangle.isZero₃_iff_isIso₁ _ ((MonoidalCategory.tensorRight N).map_distinguished _ hT)).1
    (isZero_tensor_of_isZero_tensor_koszulComplex J Λ I f hI hZ hN)

end Stacks.ModuleSheaf
