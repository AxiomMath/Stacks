module

public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionLeftDerived
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedModuleMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedModuleNullity

/-!
# Maps out of a cartesian object of `D(O)`, without flatness

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of commutative rings on its
total site and `K, K'` objects of `D(O)` with `K` cartesian. Stacks 0D9R says that a map
`K ⟶ K'` vanishing in degree zero vanishes, provided `Hom(K_i[i], K'_i) = 0` for `i > 0` and
`Hom(K_i[i + 1], K'_i) = 0` for `i ≥ 0`; Stacks 0D9S says that a morphism of the associated
simplicial systems comes from a morphism `K ⟶ K'`, provided `Hom(K_i[i - 1], K'_i) = 0` for
`i > 1`. The source assumes the structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m` flat, and the
library's statements
`CategoryTheory.SimplicialSiteSituation.eq_zero_of_derivedComponentModuleRestriction_map_eq_zero`
and `CategoryTheory.SimplicialSiteSituation.exists_hom_of_cartesian` carry that hypothesis.

Flatness enters the source's proofs only to make lower shriek `g_{n!}` exact, so that the
Postnikov term `X_n = g_{n!}O_n ⊗^L_O K` of Stacks 0D9Q is `g_{n!}K_n` (Stacks 0D9E (2)). With the
left derived lower shriek `Lg_{n!}` in place of `g_{n!}`, that identification holds for every
cartesian `K` (`CategoryTheory.SimplicialSiteSituation.isIso_moduleProjectionLeftDerived`), and the
source's arguments go through verbatim. This file proves both statements with **no flatness
hypothesis**. This matters for the small étale site of an fppf hypercovering, whose degeneracy
transitions are not flat in general.

## Main results

* `SimplicialSiteSituation.eq_zero_of_isCartesian_of_derivedComponentModuleRestriction_map_eq_zero`:
  the conclusion of Stacks 0D9R without its flatness hypothesis.
* `CategoryTheory.SimplicialSiteSituation.exists_hom_of_isCartesianDerivedModule`: the conclusion of
  Stacks 0D9S without its flatness hypothesis.

## References

* [Stacks Project, Tag 0D9R](https://stacks.math.columbia.edu/tag/0D9R)
* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open StacksDraft.BrutalPostnikov
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- Comparing two maps out of a direct sum on one summand, whose inclusion is a two-step leg:
both maps are known after the leg. Over abstract morphisms. -/
private theorem leg_comp_eq_leg_comp {D : Type*} [Category D] {P R Q K' Kn W : D}
    (l₁ : P ⟶ R) (l₂ : R ⟶ Q) (x : Q ⟶ K') (y : Q ⟶ Kn) (fn : Kn ⟶ K') (a : P ⟶ W)
    (c' : W ⟶ K') (c : P ⟶ Kn) (hl : l₁ ≫ l₂ ≫ x = a ≫ c') (hc : l₁ ≫ l₂ ≫ y = c)
    (hn : c ≫ fn = a ≫ c') :
    (l₁ ≫ l₂) ≫ x = (l₁ ≫ l₂) ≫ y ≫ fn := by
  rw [Category.assoc, hl, ← hn, ← hc]
  simp only [Category.assoc]

/-- Cancelling an isomorphism through which a map factors. Over abstract morphisms. -/
private theorem comp_eq_of_eq_comp_of_isIso {D : Type*} [Category D] {P C K K' : D}
    {c : P ⟶ K} (s : P ⟶ C) [IsIso s] (h : C ⟶ K) {γ : K ⟶ K'} {β : C ⟶ K'}
    (hc : c = s ≫ h) (hγ : c ≫ γ = s ≫ β) : h ≫ γ = β := by
  subst hc
  rw [Category.assoc] at hγ
  exact (cancel_epi s).1 hγ

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
  derivedComponentModuleRestriction_additive

-- No global `HasDerivedCategory` instance exists for these module categories (`#synth` finds
-- none), so the standard model of the tower this file extends is installed locally.
attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- Maps out of a shift of an object isomorphic to a tensor term vanish when the corresponding
component maps do, for cartesian `K`. -/
private theorem hom_shift_eq_zero_of_iso_tensorTerm
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules) (hK : S.IsCartesianDerivedModule O K)
    (i : ℕ) (j : ℤ)
    (h : ∀ v : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules)) j).obj
        ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
      (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', v = 0)
    {X : DerivedCategory (S.totalRingedTopos O).Modules}
    (e : X ≅ S.componentModuleLowerShriekDerivedTensorTerm O K i) :
    ∀ g : (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) j).obj X ⟶ K',
      g = 0 :=
  hom_eq_zero_of_iso
    ((shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) j).mapIso e) (Iso.refl K')
    (S.hom_componentModuleLowerShriekDerivedTensorTerm_eq_zero_of_isCartesian O K K' hK i j h)

/-- **The conclusion of Stacks 0D9R without its flatness hypothesis.** In a simplicial-site
situation (Stacks 09WE, either case) let `O` be a sheaf of rings on the total site and `K, K'`
objects of `D(O)` with `K` cartesian, `Hom(K_i[i], K'_i) = 0` for `i > 0` and
`Hom(K_i[i + 1], K'_i) = 0` for `i ≥ 0`. Then a map `K ⟶ K'` inducing the zero map
`K_0 ⟶ K'_0` is zero.

The proof is the source's, through the Postnikov presentation of Stacks 0D9Q, with the terms
identified with `Lg_{i!}K_i` by
`CategoryTheory.SimplicialSiteSituation.isIso_moduleProjectionLeftDerived`. -/
theorem eq_zero_of_isCartesian_of_derivedComponentModuleRestriction_map_eq_zero
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hK : S.IsCartesianDerivedModule O K)
    (hHom : ∀ i : ℕ, 0 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules)) (i : ℤ)).obj
          ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
        (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (hHomSucc : ∀ i : ℕ,
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
            ((i : ℤ) + 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
        (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (f : K ⟶ K')
    (hf : (S.derivedComponentModuleRestriction O ⦋0⦌).map f = 0) :
    f = 0 := by
  obtain ⟨D⟩ := nonempty_simplicialModuleResolution S
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)
  let T := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O
  let : (derivedTensorRight O T K).CommShift ℤ := T.commShift_left K
  let : (derivedTensorRight O T K).IsTriangulated :=
    isTriangulated_derivedTensorRight O T K
  refine eq_zero_of_isHomotopyColimit_mapTruncTowerSystem (moduleResolutionComplex D)
    (derivedTensorRight O T K)
    (isHomotopyColimit_moduleResolutionTensorSystem O T D K) (fun i hi => ?_) (fun i => ?_)
    (fun c => ?_)
  · exact hom_shift_eq_zero_of_iso_tensorTerm S O K K' hK i (i : ℤ) (hHom i hi)
      (moduleResolutionTensorTermIso O T D K i)
  · exact hom_shift_eq_zero_of_iso_tensorTerm S O K K' hK i ((i : ℤ) + 1) (hHomSucc i)
      (moduleResolutionTensorTermIso O T D K i)
  · exact zero_of_epi_comp (moduleResolutionTensorTermIso O T D K 0).inv
      ((Category.assoc _ _ _).symm.trans
        (S.comp_eq_zero_of_isCartesian_of_derivedComponentModule_map_eq_zero O K K' hK 0
          ((moduleResolutionTensorTermIso O T D K 0).inv ≫ c) f hf))

/-- **The restriction to a component of the transpose of a morphism of simplicial systems, along
the left derived lower shriek.** For a morphism `f : {K_n} ⟶ {K'_n}` of the simplicial systems of
Stacks 0D9P attached to `K, K'`, the restriction to degree `n` of the transpose
`Lg_{m!}K_m ⟶ K'` of `f_m` is the restriction of the counit `Lg_{m!}K_m ⟶ K` followed by `f_n`.
No flatness is needed: the derived direct-sum formula presents `g_n^*Lg_{m!}K_m` as a direct sum
with the canonical legs as inclusions. -/
theorem derivedComponentModuleRestriction_map_leftDerived_homEquiv_symm
    {K K' : DerivedCategory (S.totalRingedTopos O).Modules}
    (f : SimplicialDerivedModuleSystem.Hom (S.derivedModuleSystem O K)
      (S.derivedModuleSystem O K')) (m n : SimplexCategory) :
    (S.derivedComponentModuleRestriction O n).map
        (((S.componentModuleLowerShriekLeftDerivedAdjunction O m).homEquiv _ K').symm
          (f.app m)) =
      (S.derivedComponentModuleRestriction O n).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O m).counit.app K) ≫
        f.app n := by
  let : Fintype (m ⟶ n) := Fintype.ofFinite (m ⟶ n)
  have := S.isIso_derivedModuleSumComparison O m n
    ((S.derivedComponentModuleRestriction O m).obj K)
  refine (cancel_epi (S.derivedModuleSumComparison O m n
    ((S.derivedComponentModuleRestriction O m).obj K))).1 ?_
  refine biproduct.hom_ext' _ _ fun ψ => ?_
  have hs := S.ι_derivedModuleSumComparison O ψ ((S.derivedComponentModuleRestriction O m).obj K)
  have hcounit := S.derivedTransitionPullback_map_leftDerivedUnit_comp_map_homEquiv_symm O
    (𝟙 ((S.derivedComponentModuleRestriction O m).obj K)) ψ
  rw [Adjunction.homEquiv_symm_id, Functor.map_id, Category.id_comp] at hcounit
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ _) hs).trans
    ((leg_comp_eq_leg_comp _ _ _ _ _ _ _ _
      (S.derivedTransitionPullback_map_leftDerivedUnit_comp_map_homEquiv_symm O (f.app m) ψ)
      hcounit (f.naturality ψ)).trans
    ((congrArg (fun k => k ≫ _) hs.symm).trans (Category.assoc _ _ _))))

/-- **Hypothesis (3) of Stacks 0D9S is the vanishing the tower step consumes, for cartesian
`K`.** The Postnikov term `X_{i+1}` of Stacks 0D9Q is `Lg_{i+1!}K_{i+1}`, so the vanishing of
`Hom(X_{i+1}[i], K')` for `i > 0` is the vanishing of `Hom(K_{i+1}[i], K'_{i+1})`. -/
theorem hom_moduleResolutionTensorTerm_shift_eq_zero_of_isCartesian
    (D : SimplicialModuleResolutionActual S
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O))
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules) (hK : S.IsCartesianDerivedModule O K)
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
          ((i : ℤ) - 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
          (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0) :
    ∀ i : ℕ, 0 < i →
      ∀ g : (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) (i : ℤ)).obj
        ((S.moduleResolutionTensorFunctor O K).obj
          (moduleResolutionTerm D (i + 1))) ⟶ K', g = 0 := by
  intro i hi
  exact hom_shift_eq_zero_of_iso_tensorTerm S O K K' hK (i + 1) (i : ℤ)
    ((show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) by push_cast; ring) ▸ hHom (i + 1) (by omega))
    (S.moduleResolutionTensorTermCanonicalIso O D K (i + 1))

/-- **The first half of the proof of Stacks 0D9S, without flatness: a morphism `K ⟶ K'` agreeing
with a given morphism of simplicial systems in degree zero.** For a cartesian `K` with
`Hom(K_i[i - 1], K'_i) = 0` for `i > 1`, every morphism `f` of the associated simplicial systems
is realised in degree zero by some `γ : K ⟶ K'`. The construction is the source's, through the
Postnikov system of Stacks 0D9Q for `- ⊗^L_O K`, with `Lg_{n!}` in place of `g_{n!}`. -/
theorem exists_hom_derivedComponentModuleRestriction_zero_eq_of_isCartesian
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hK : S.IsCartesianDerivedModule O K)
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
          ((i : ℤ) - 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
          (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (f : SimplicialDerivedModuleSystem.Hom (S.derivedModuleSystem O K)
      (S.derivedModuleSystem O K')) :
    ∃ γ : K ⟶ K', (S.derivedComponentModuleRestriction O ⦋0⦌).map γ = f.app ⦋0⦌ := by
  obtain ⟨D, hD⟩ := exists_simplicialModuleResolutionActual_homEquiv_augmentation S
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)
  let : (S.moduleResolutionTensorFunctor O K).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).commShift_left K
  let : (S.moduleResolutionTensorFunctor O K).IsTriangulated :=
    isTriangulated_derivedTensorRight O
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O) K
  let adj₀ := S.componentModuleLowerShriekLeftDerivedAdjunction O ⦋0⦌
  let adj₁ := S.componentModuleLowerShriekLeftDerivedAdjunction O ⦋1⦌
  let e₀ := @asIso _ _ _ _ (S.moduleProjectionLeftDerived O ⦋0⦌ K)
    (S.isIso_moduleProjectionLeftDerived O K hK ⦋0⦌)
  let e₁ : (S.componentModuleLowerShriekLeftDerived O ⦋1⦌).obj
      ((S.derivedComponentModuleRestriction O ⦋1⦌).obj K) ≅
      (show DerivedCategory (S.totalRingedTopos O).Modules from
        (S.moduleResolutionTensorFunctor O K).obj (moduleResolutionTerm D 1)) :=
    @asIso _ _ _ _ (S.moduleProjectionLeftDerived O ⦋1⦌ K)
        (S.isIso_moduleProjectionLeftDerived O K hK ⦋1⦌) ≪≫
      (S.moduleResolutionTensorTermCanonicalIso O D K 1).symm
  let h := S.moduleResolutionTensorAugmentation O D K
  let θ := (adj₀.homEquiv _ K) (e₀.hom ≫ h)
  have hθ : IsIso θ :=
    S.isIso_homEquiv_moduleProjectionLeftDerived_comp_of_homEquiv_eq_id O ⦋0⦌
      (moduleResolutionLowerShriekAugmentation D) hD K
  let b := e₀.inv ≫ (adj₀.homEquiv _ K').symm (θ ≫ f.app ⦋0⦌)
  -- The first omitted computation: `X₁ ⟶ X₀ ⟶ K'` vanishes.
  have hb : (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTermDiff D 0) ≫
      (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫ b =
      (0 : (show DerivedCategory (S.totalRingedTopos O).Modules from
        (S.moduleResolutionTensorFunctor O K).obj (moduleResolutionTerm D 1)) ⟶ K') := by
    have hcounit : (S.componentModuleLowerShriekLeftDerived O ⦋0⦌).map θ ≫
        adj₀.counit.app K = e₀.hom ≫ h :=
      (adj₀.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
    let E : (show DerivedCategory (S.totalRingedTopos O).Modules from
        (S.moduleResolutionTensorFunctor O K).obj (moduleResolutionTerm D 1)) ⟶
        (S.componentModuleLowerShriekLeftDerived O ⦋0⦌).obj
          ((S.derivedComponentModuleRestriction O ⦋0⦌).obj K) :=
      (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTermDiff D 0) ≫
        (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫ e₀.inv ≫
          (S.componentModuleLowerShriekLeftDerived O ⦋0⦌).map θ
    have hE : E ≫ adj₀.counit.app K = 0 :=
      (Category.assoc _ _ _).trans ((congrArg (fun k => _ ≫ k) ((Category.assoc _ _ _).trans
        (congrArg (fun k => _ ≫ k) ((Category.assoc _ _ _).trans
          (congrArg (fun k => e₀.inv ≫ k) hcounit))))).trans
        ((congrArg (fun k => _ ≫ _ ≫ k) (e₀.inv_hom_id_assoc h)).trans
          (S.termDiff_comp_moduleResolutionTensorAugmentation O D K)))
    have hE' : (e₁.hom ≫ E) ≫ (adj₀.homEquiv _ K').symm (f.app ⦋0⦌) = 0 := by
      refine (adj₁.homEquiv _ K').injective ?_
      refine (adj₁.homEquiv_naturality_right _ _).trans ?_
      refine (congrArg (fun k => (adj₁.homEquiv _ _) (e₁.hom ≫ E) ≫ k)
        (S.derivedComponentModuleRestriction_map_leftDerived_homEquiv_symm O f ⦋0⦌ ⦋1⦌)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun k => k ≫ f.app ⦋1⦌)
        (adj₁.homEquiv_naturality_right (e₁.hom ≫ E) (adj₀.counit.app K)).symm).trans ?_
      refine (congrArg (fun k => (adj₁.homEquiv _ _) k ≫ f.app ⦋1⦌)
        ((Category.assoc _ _ _).trans ((congrArg (fun k => e₁.hom ≫ k) hE).trans
          comp_zero))).trans ?_
      have hz : ∀ {X : DerivedCategory (S.componentRingedTopos O ⦋1⦌).Modules}
          {Y : DerivedCategory (S.totalRingedTopos O).Modules},
          adj₁.homEquiv X Y 0 = 0 := fun {X Y} => by
        rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
      exact (congrArg (fun k => k ≫ f.app ⦋1⦌) hz).trans (zero_comp.trans hz.symm)
    have hE'' : E ≫ (adj₀.homEquiv _ K').symm (f.app ⦋0⦌) = 0 :=
      (e₁.cancel_iso_hom_left _ _).1 ((Category.assoc _ _ _).symm.trans (hE'.trans comp_zero.symm))
    refine (congrArg (fun k => (S.moduleResolutionTensorFunctor O K).map
        (moduleResolutionTermDiff D 0) ≫ (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫
          e₀.inv ≫ k) (adj₀.homEquiv_naturality_left_symm θ (f.app ⦋0⦌))).trans ?_
    exact ((Category.assoc _ _ _).trans (congrArg (fun k => _ ≫ k) ((Category.assoc _ _ _).trans
      (congrArg (fun k => _ ≫ k) (Category.assoc _ _ _))))).symm.trans hE''
  obtain ⟨γ, hγ⟩ := exists_hom_of_termDiff_comp_eq_zero (moduleResolutionComplex D)
    (S.moduleResolutionTensorFunctor O K)
    (S.isHomotopyColimitWith_moduleResolutionTensorSystem O D K)
    ((S.moduleResolutionTensorTermCanonicalIso O D K 0).hom ≫ b) hb
    (S.hom_moduleResolutionTensorTerm_shift_eq_zero_of_isCartesian O D K K' hK hHom)
  refine ⟨γ, ?_⟩
  -- The second omitted computation: the bottom coprojection is the augmentation.
  have hi₂ := Iso.isIso_hom ((S.moduleResolutionTensorFunctor O K).mapIso
    (@asIso _ _ _ _ (moduleResolutionTotProj D 0)
      (StacksDraft.BrutalPostnikov.isIso_totProj_zero (moduleResolutionComplex D))))
  have hγ' : h ≫ γ = b :=
    @comp_eq_of_eq_comp_of_isIso _ _ _ _ _ _ _
      ((S.moduleResolutionTensorFunctor O K).map (StacksDraft.BrutalPostnikov.totAtTowerIso
          (moduleResolutionComplex D) (-((1 : ℕ) : ℤ)) (by simp)).inv ≫
        (S.moduleResolutionTensorFunctor O K).map (moduleResolutionTotProj D 0) ≫
          (S.moduleResolutionTensorTermCanonicalIso O D K 0).hom)
      (IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hi₂ inferInstance)) h _ _
      ((S.moduleResolutionTensorCoprojection_zero O D K).trans
        ((congrArg (fun k => _ ≫ k) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm))
      (hγ.trans ((congrArg (fun k => _ ≫ k) (Category.assoc _ _ _).symm).trans
        (Category.assoc _ _ _).symm))
  exact (cancel_epi θ).1 (((adj₀.homEquiv_naturality_right (e₀.hom ≫ h) γ).symm.trans
    (congrArg (adj₀.homEquiv _ K') ((Category.assoc _ _ _).trans
      ((congrArg (fun k => e₀.hom ≫ k) hγ').trans (e₀.hom_inv_id_assoc _))))).trans
    (Equiv.apply_symm_apply _ _))

/-- **The conclusion of Stacks 0D9S without its flatness hypothesis.** In Situation 09WE, let `O`
be a sheaf of rings on the total site and let `K`, `K'` be objects of `D(O)` with `K` cartesian
and `Hom(K_i[i - 1], K'_i) = 0` for `i > 1`. Then any morphism `{K_n ⟶ K'_n}` between the
associated simplicial systems of the derived category of modules comes from a morphism
`K ⟶ K'` in `D(O)`. -/
theorem exists_hom_of_isCartesianDerivedModule
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hK : S.IsCartesianDerivedModule O K)
    (hHom : ∀ i : ℕ, 1 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
          ((i : ℤ) - 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
          (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (f : SimplicialDerivedModuleSystem.Hom (S.derivedModuleSystem O K)
      (S.derivedModuleSystem O K')) :
    ∃ γ : K ⟶ K', ∀ i : SimplexCategory,
      (S.derivedComponentModuleRestriction O i).map γ = f.app i := by
  obtain ⟨γ, hγ⟩ :=
    S.exists_hom_derivedComponentModuleRestriction_zero_eq_of_isCartesian O K K' hK hHom f
  exact ⟨γ, fun i => SimplicialDerivedModuleSystem.Hom.app_eq_of_cartesian S O
    (S.derivedModuleSystem_cartesian O K hK) (S.derivedModuleSystemMap O γ) f hγ i⟩

end CategoryTheory.SimplicialSiteSituation

end
