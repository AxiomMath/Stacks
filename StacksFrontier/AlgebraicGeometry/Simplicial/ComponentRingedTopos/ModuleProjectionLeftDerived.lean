module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleProjectionVanishing
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionAdjunctSquareDerived
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionAugmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealizationLeftDerived
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionUnitor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedLiftedTransitionSquareComparison

/-!
# The projection map of Stacks 0D9E (2) through the left derived lower shriek

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. Stacks 0D9E (2) compares, for an object `K` of `D(O)`, the lower shriek of its
degree-`n` restriction with `g_{n!}O_n ⊗^L_O K`. The source assumes the structure-sheaf
transitions `f_φ^{-1}O_n ⟶ O_m` flat, which makes `g_{n!}` exact. This file states the
comparison with the left derived lower shriek `Lg_{n!}` of
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekLeftDerived` in place of
`g_{n!}`, and proves with **no flatness hypothesis** that it is an isomorphism for every
cartesian `K`.

The argument is the source's: restricted to a degree `m`, both sides are direct sums over the
simplex maps `[n] ⟶ [m]` — the source by the derived direct-sum formula
`CategoryTheory.SimplicialSiteSituation.isIso_derivedModuleSumComparison`, the target by
`CategoryTheory.SimplicialSiteSituation.moduleProjectionTargetIso` — and the comparison becomes the
direct sum of the derived transitions of `K`. The one square this needs,
`CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare`, is proved here for every
`K` through `CategoryTheory.liftedTransition_square_of_comparison`, which needs no exactness of the
transition pullbacks.

The two consequences the proofs of Stacks 0D9R and 0D9S consume — the transfer of the vanishing
of `Hom(K_i[j], K'_i)` to `Hom(X_i[j], K')` for `X_i = g_{i!}O_i ⊗^L_O K`, and the vanishing of
`a ≫ b` for `a : X_i ⟶ K` and `b` with vanishing degree-`i` restriction — follow for cartesian `K`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleProjectionAdjunctSquare`: the residual square of
  Stacks 0D9E (2), for every object, without flatness.
* `CategoryTheory.SimplicialSiteSituation.moduleProjectionLeftDerived`: the projection map
  `Lg_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K`.
* `CategoryTheory.SimplicialSiteSituation.isIso_moduleProjectionLeftDerived`: it is an
  isomorphism for cartesian `K`.
* `hom_componentModuleLowerShriekDerivedTensorTerm_eq_zero_of_isCartesian` and
  `comp_eq_zero_of_isCartesian_of_derivedComponentModule_map_eq_zero` (both in the namespace
  `CategoryTheory.SimplicialSiteSituation`): the two vanishing statements above, for cartesian `K`.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules.Tensor
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- The assembly of the residual square: a functor applied to a threefold composite, split after
its second factor, the naturality of the transition at the third factor, the square through the
first two, the description of the summand inclusion of the target, and the invertibility of the
target identification. Over abstract morphisms. -/
private theorem map_comp_comp_square_assemble {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {c₀ c₁ c₂ c₃ : C} {tX tY tK bip tC : D}
    (x : c₀ ⟶ c₁) (y : c₁ ⟶ c₂) (z : c₂ ⟶ c₃) (dY : F.obj c₃ ⟶ tY) (tgt : tY ⟶ bip)
    (dX : F.obj c₂ ⟶ tX) (mu : tX ⟶ tY) (dK : F.obj c₀ ⟶ tK) (cd₁ : tK ⟶ tC) (cd₂ : tC ⟶ tX)
    (iota : tK ⟶ bip) (tinv : bip ⟶ tY)
    (hnat : F.map z ≫ dY = dX ≫ mu) (hstar : F.map (x ≫ y) ≫ dX = dK ≫ cd₁ ≫ cd₂)
    (hiota : iota ≫ tinv = cd₁ ≫ cd₂ ≫ mu) (hinv : tinv ≫ tgt = 𝟙 bip) :
    F.map (x ≫ y ≫ z) ≫ dY ≫ tgt = dK ≫ iota := by
  rw [← Category.assoc x y z, F.map_comp, Category.assoc, reassoc_of% hnat, reassoc_of% hstar,
    ← reassoc_of% hiota, hinv, Category.comp_id]

/-- Two composites through a unit, a transition and a transpose, followed by a further map, over
abstract morphisms. -/
private theorem comp_comp_eq_of_eq_of_eq {D : Type*} [Category D] {P Q R E T W : D}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ E) (d : E ⟶ W) (a' : P ⟶ T) (b' : T ⟶ E) (e : P ⟶ W)
    (h₁ : a ≫ b ≫ c = a' ≫ b') (h₂ : a' ≫ b' ≫ d = e) : (a ≫ b) ≫ c ≫ d = e := by
  rw [Category.assoc, reassoc_of% h₁, h₂]

/-- Invertibility of the derived adjunct followed by the augmentation, assembled from the
naturality of the flat-tensor identification, the naturality of the compositor and the
functoriality of the derived transformation. Over abstract morphisms. -/
private theorem isIso_comp_map_comp_of_naturality {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {A₁ A₂ E₁ E₂ F' : C} {P Q Z : D}
    (eL : A₁ ≅ A₂) (eU : E₁ ≅ E₂) (x : A₁ ⟶ E₁) (y : A₂ ⟶ E₂) (z : E₁ ⟶ F')
    (hA : x ≫ eU.hom = eL.hom ≫ y)
    (a : P ⟶ Q) (c : Q ⟶ G.obj A₂) (w : Q ⟶ Z) (c' : Z ⟶ G.obj E₂) (θ : P ⟶ Z)
    (h₃ : c ≫ G.map y = w ≫ c') (h₄ : a ≫ w = θ) (hθ : IsIso θ) (hc' : IsIso c')
    (hz : IsIso z) :
    IsIso ((a ≫ c ≫ G.map eL.inv) ≫ G.map (x ≫ z)) := by
  have hA' : eL.inv ≫ x = y ≫ eU.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, hA, Iso.inv_hom_id_assoc]
  have h : (a ≫ c ≫ G.map eL.inv) ≫ G.map (x ≫ z) =
      θ ≫ c' ≫ G.map eU.inv ≫ G.map z := by
    calc (a ≫ c ≫ G.map eL.inv) ≫ G.map (x ≫ z) = a ≫ c ≫ G.map ((eL.inv ≫ x) ≫ z) := by
          simp only [Functor.map_comp, Category.assoc]
      _ = a ≫ c ≫ G.map y ≫ G.map eU.inv ≫ G.map z := by
          rw [hA']
          simp only [Functor.map_comp, Category.assoc]
      _ = (a ≫ w) ≫ c' ≫ G.map eU.inv ≫ G.map z := by
          rw [reassoc_of% h₃, Category.assoc]
      _ = θ ≫ c' ≫ G.map eU.inv ≫ G.map z := by rw [h₄]
  rw [h]
  infer_instance

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The residual square of Stacks 0D9E (2), for every object and without flatness.** For every
simplex map `φ : [n] ⟶ [m]`, the derived adjunct of the projection map carried along `Lf_φ^*`,
followed by the derived transition and the identification of the target with `⨁_φ K_m`, is the
derived transition of `K` followed by the `φ`th summand inclusion.

The derived transition of Stacks 0D9P is a transition lifted along the localization of the
homotopy category through the canonical comparison of `Lf_φ^*`, so
`CategoryTheory.liftedTransition_square_of_comparison` carries the sheaf-level square
`…transitionPullbackModules_map_componentModuleProjectionAdjunct_comp` to it with no exactness of
`f_φ^*`; the identification of the target cancels as in the flat case. -/
theorem moduleProjectionAdjunctSquare (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.ModuleProjectionAdjunctSquare O K := by
  intro n m φ
  have hstar := liftedTransition_square_of_comparison (S.componentModuleLowerShriekUnitTensor O n)
    (S.componentModulesRestriction O n) (S.componentModulesRestriction O m)
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    (S.componentModuleProjectionAdjunct O n)
    (S.componentModuleTransition O φ)
    ((S.restrictionTensorWhiskeredUnitIso O m).inv ≫
      (S.restrictionTensorWhiskered O m).map
          ((pullbackModulesObjUnitIso
                (S.transitionRingedToposHom O φ).toModulesHom).hom ≫
            (S.moduleSumFormulaLeg O φ).app
              (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))) ≫
        (S.componentRestrictionLowerShriekUnitTensorIso O n m).hom)
    (fun M => S.transitionPullbackModules_map_componentModuleProjectionAdjunct_comp O
      (S.transitionTensorCoherence O) (S.transitionUnitorCoherence O) φ M)
    (S.derivedTransitionComparison O φ) (S.derivedComponentModuleTransition O φ) rfl K
  exact map_comp_comp_square_assemble _ _ _ _ _ _ _ _ _ _ _ _ _
    ((S.derivedComponentModuleTransition O φ).naturality _) hstar
    (S.biproduct_ι_moduleProjectionTargetIso_inv_leg O n m (S.moduleSumFormulaLegEq O) K φ)
    (Iso.inv_hom_id _)

/-- **The projection map of Stacks 0D9E (2) through the left derived lower shriek**,
`Lg_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K`: the transpose along `Lg_{n!} ⊣ g_n^*` of the derived adjunct
`CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunctDerived`. -/
def moduleProjectionLeftDerived (n : SimplexCategory)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    (S.componentModuleLowerShriekLeftDerived O n).obj
        ((S.derivedComponentModuleRestriction O n).obj K) ⟶
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).obj
          (S.componentModuleLowerShriekUnit O n))).obj K :=
  ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv _ _).symm
    (S.componentModuleProjectionAdjunctDerived O n K)

/-- **The unit of `Lg_{m!} ⊣ g_m^*` carried along a transition, against a transpose.** For
`a : X ⟶ K'_m`, the map `Lf_ψ^*X ⟶ Lf_ψ^*(Lg_{m!}X)_m ⟶ (Lg_{m!}X)_n` followed by the
restriction of the transpose `Lg_{m!}X ⟶ K'` of `a` is `Lf_ψ^*(a)` followed by the derived
transition of `K'`: the naturality of the derived transition and the triangle identity. -/
theorem derivedTransitionPullback_map_leftDerivedUnit_comp_map_homEquiv_symm
    {m n : SimplexCategory} {X : DerivedCategory (S.componentRingedTopos O m).Modules}
    {K' : DerivedCategory (S.totalRingedTopos O).Modules}
    (a : X ⟶ (S.derivedComponentModuleRestriction O m).obj K') (ψ : m ⟶ n) :
    (S.derivedTransitionPullback O ψ).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O m).unit.app X) ≫
        (S.derivedComponentModuleTransition O ψ).app
            ((S.componentModuleLowerShriekLeftDerived O m).obj X) ≫
          (S.derivedComponentModuleRestriction O n).map
            (((S.componentModuleLowerShriekLeftDerivedAdjunction O m).homEquiv X K').symm a) =
      (S.derivedTransitionPullback O ψ).map a ≫
        (S.derivedComponentModuleTransition O ψ).app K' :=
  (congrArg (fun k => (S.derivedTransitionPullback O ψ).map
      ((S.componentModuleLowerShriekLeftDerivedAdjunction O m).unit.app X) ≫ k)
    ((S.derivedComponentModuleTransition O ψ).naturality
      (((S.componentModuleLowerShriekLeftDerivedAdjunction O m).homEquiv X K').symm
        a)).symm).trans
  ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (S.derivedComponentModuleTransition O ψ).app K')
      (((S.derivedTransitionPullback O ψ).map_comp _ _).symm.trans
        (congrArg (S.derivedTransitionPullback O ψ).map
          (((S.componentModuleLowerShriekLeftDerivedAdjunction O m).homEquiv_unit _ _
            _).symm.trans
            (Equiv.apply_symm_apply _ _))))))

/-- **The restriction to a degree `m` of the projection map is the direct sum of the derived
transitions.** Under the derived direct-sum formula `⨁_φ Lf_φ^*K_n ≅ g_m^*Lg_{n!}K_n` and the
identification of the target with `⨁_φ K_m`, the restriction of the projection map is the direct
sum of the derived transitions `K(φ) : Lf_φ^*K_n ⟶ K_m`. No flatness is needed. -/
theorem derivedModuleSumComparison_comp_moduleProjectionLeftDerived
    (K : DerivedCategory (S.totalRingedTopos O).Modules) (n m : SimplexCategory) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    S.derivedModuleSumComparison O n m ((S.derivedComponentModuleRestriction O n).obj K) ≫
        (S.derivedComponentModuleRestriction O m).map (S.moduleProjectionLeftDerived O n K) ≫
          (S.moduleProjectionTargetIso O n m K).hom =
      biproduct.map fun φ : n ⟶ m => (S.derivedComponentModuleTransition O φ).app K := by
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  refine biproduct.hom_ext' _ _ fun φ => ?_
  rw [← Category.assoc, ι_derivedModuleSumComparison, biproduct.ι_map]
  exact comp_comp_eq_of_eq_of_eq _ _ _ _ _ _ _
    (S.derivedTransitionPullback_map_leftDerivedUnit_comp_map_homEquiv_symm O
      (S.componentModuleProjectionAdjunctDerived O n K) φ)
    (S.moduleProjectionAdjunctSquare O K n m φ)

/-- **Stacks 0D9E (2), the direct implication, without flatness.** For a cartesian object `K` of
`D(O)` the projection map `Lg_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism in every degree: its
restriction to each degree is, up to isomorphisms, the direct sum of the derived transitions of
`K`, and the restrictions to the degrees detect isomorphisms. -/
theorem isIso_moduleProjectionLeftDerived (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (hK : S.IsCartesianDerivedModule O K) (n : SimplexCategory) :
    IsIso (S.moduleProjectionLeftDerived O n K) := by
  refine isIso_of_forall_isIso_derivedComponentModuleRestriction_map S O _ fun m => ?_
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  have h := S.derivedModuleSumComparison_comp_moduleProjectionLeftDerived O K n m
  have := S.isIso_derivedModuleSumComparison O n m
    ((S.derivedComponentModuleRestriction O n).obj K)
  have hmap :
      IsIso (biproduct.map fun φ : n ⟶ m => (S.derivedComponentModuleTransition O φ).app K) :=
    (Limits.isIso_biproduct_map_iff _).2 fun φ => hK φ
  rw [← h] at hmap
  have := IsIso.of_isIso_comp_left
    (S.derivedModuleSumComparison O n m ((S.derivedComponentModuleRestriction O n).obj K))
    ((S.derivedComponentModuleRestriction O m).map (S.moduleProjectionLeftDerived O n K) ≫
      (S.moduleProjectionTargetIso O n m K).hom)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (S.moduleProjectionTargetIso O n m K).hom
    (Iso.isIso_hom _) this

/-- **`Hom(X_i[j], K')` vanishes as soon as `Hom(K_i[j], K'_i)` does, for cartesian `K`**, where
`X_i = g_{i!}O_i ⊗^L_O K`. The projection map identifies `X_i` with `Lg_{i!}K_i`, which commutes
with the shift, and `Lg_{i!} ⊣ g_i^*` transposes the group. No flatness is needed. -/
theorem hom_componentModuleLowerShriekDerivedTensorTerm_eq_zero_of_isCartesian
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules) (hK : S.IsCartesianDerivedModule O K)
    (i : ℕ) (j : ℤ)
    (h : ∀ v : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules)) j).obj
        ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
      (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', v = 0) :
    ∀ g : (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) j).obj
      (S.componentModuleLowerShriekDerivedTensorTerm O K i) ⟶ K', g = 0 := by
  have := S.isIso_moduleProjectionLeftDerived O K hK ⦋i⦌
  refine hom_eq_zero_of_iso
    (((shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) j).mapIso
      (asIso (S.moduleProjectionLeftDerived O ⦋i⦌ K))).symm) (Iso.refl K') ?_
  exact hom_eq_zero_of_shifted_leftAdjoint
    (S.componentModuleLowerShriekLeftDerivedAdjunction O ⦋i⦌)
    ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) j
    (((S.componentModuleLowerShriekLeftDerived O ⦋i⦌).commShiftIso j).symm.app _) h

/-- **For cartesian `K`, a map `X_i ⟶ K` followed by a map `K ⟶ K'` whose degree-`i` restriction
vanishes is zero**, where `X_i = g_{i!}O_i ⊗^L_O K`. The projection map out of `Lg_{i!}K_i` is
invertible, hence epi, and the transpose of the composite after it factors through the
restriction of the second map. No flatness is needed. -/
theorem comp_eq_zero_of_isCartesian_of_derivedComponentModule_map_eq_zero
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules) (hK : S.IsCartesianDerivedModule O K)
    (i : ℕ) (a : S.componentModuleLowerShriekDerivedTensorTerm O K i ⟶ K) (b : K ⟶ K')
    (hb : (S.derivedComponentModuleRestriction O ⦋i⦌).map b = 0) : a ≫ b = 0 := by
  let : (S.derivedComponentModuleRestriction O ⦋i⦌).Additive :=
    inferInstanceAs ((S.componentModulesRestriction O ⦋i⦌).mapDerivedCategory).Additive
  have : Epi (S.moduleProjectionLeftDerived O ⦋i⦌ K) :=
    @IsIso.epi_of_iso _ _ _ _ _ (S.isIso_moduleProjectionLeftDerived O K hK ⦋i⦌)
  refine zero_of_epi_comp (S.moduleProjectionLeftDerived O ⦋i⦌ K) ?_
  exact (Category.assoc _ _ _).symm.trans
    (comp_eq_zero_of_leftAdjoint (S.componentModuleLowerShriekLeftDerivedAdjunction O ⦋i⦌)
      (S.moduleProjectionLeftDerived O ⦋i⦌ K ≫ a) hb)

/-- **The derived adjunct of the projection map, followed by the augmentation, is an
isomorphism**, without flatness: the endomorphism
`K_n ⟶ (g_{n!}O_n ⊗^L_O K)_n ⟶ (O ⊗^L_O K)_n ≅ K_n` is the derived functor of an isomorphism of
sheaf-level functors (`…isIso_componentModuleProjectionAdjunct_comp_whiskerRight`), read through
the compositor of derived functors and the identification of the tensor product with a flat
module with its derived functor. -/
theorem isIso_componentModuleProjectionAdjunctDerived_comp_augmentation (n : SimplexCategory)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    IsIso (S.componentModuleProjectionAdjunctDerived O n K ≫
      (S.derivedComponentModuleRestriction O n).map
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
              (S.componentModuleLowerShriekUnitAugmentation O n))).app K ≫
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).leftUnitIso
            (totalRingedSite O) K).hom)) := by
  have hU : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (S.totalRingedTopos O).O)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) :=
    Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := totalRingedSite O)
  let := Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.preservesFiniteLimits_sheafTensorObj
    (S.totalRingedTopos O).O _ hU
  let :=
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.preservesFiniteColimits_sheafTensorObj
      (S.totalRingedTopos O).O _ hU
  let : ((sheafTensor (S.totalRingedTopos O).O).obj (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O))).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hA := NatTrans.congr_app
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso_naturality
      (S.totalRingedTopos O).O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
      (S.isFlat_componentModuleLowerShriek_unit O n) hU
      (S.componentModuleLowerShriekUnitAugmentation O n)) K
  simp only [NatTrans.comp_app] at hA
  have hC := NatTrans.congr_app (derivedCompIso_refl_hom_whiskerRight
    (S.componentModuleLowerShriekUnitTensor O n)
    ((sheafTensor (S.totalRingedTopos O).O).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)))
    (S.componentModulesRestriction O n)
    ((sheafTensor (S.totalRingedTopos O).O).map
      (S.componentModuleLowerShriekUnitAugmentation O n))) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hC
  have hD := NatTrans.congr_app (derivedNatTrans_comp (S.componentModulesRestriction O n)
    (S.componentModuleLowerShriekUnitTensor O n ⋙ S.componentModulesRestriction O n)
    ((sheafTensor (S.totalRingedTopos O).O).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) ⋙
      S.componentModulesRestriction O n)
    (S.componentModuleProjectionAdjunct O n)
    (Functor.whiskerRight ((sheafTensor (S.totalRingedTopos O).O).map
      (S.componentModuleLowerShriekUnitAugmentation O n)) (S.componentModulesRestriction O n))) K
  simp only [NatTrans.comp_app] at hD
  have : IsIso (derivedNatTrans (S.componentModulesRestriction O n)
      ((sheafTensor (S.totalRingedTopos O).O).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) ⋙
        S.componentModulesRestriction O n)
      (S.componentModuleProjectionAdjunct O n ≫
        Functor.whiskerRight ((sheafTensor (S.totalRingedTopos O).O).map
          (S.componentModuleLowerShriekUnitAugmentation O n))
          (S.componentModulesRestriction O n))) :=
    isIso_derivedNatTrans _ _ _
      (hα := S.isIso_componentModuleProjectionAdjunct_comp_whiskerRight O n)
  exact isIso_comp_map_comp_of_naturality (S.derivedComponentModuleRestriction O n)
    ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso
      (S.totalRingedTopos O).O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
      _ (S.isFlat_componentModuleLowerShriek_unit O n)).app K)
    ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso
      (S.totalRingedTopos O).O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
      _ hU).app K) _ _ _ hA _ _ _ _ _ hC.symm hD.symm
    (NatIso.isIso_app_of_isIso _ K) (NatIso.isIso_app_of_isIso _ K) (Iso.isIso_hom _)

/-- **The transpose of the projection map followed by the augmentation is an isomorphism**, for
any map `a : g_{n!}O_n ⟶ O` whose transpose along `g_{n!} ⊣ g_n^*` is the identity, with the left
derived lower shriek and without flatness. -/
theorem isIso_homEquiv_moduleProjectionLeftDerived_comp_of_homEquiv_eq_id (n : SimplexCategory)
    (a : S.componentModuleLowerShriekUnit O n ⟶ SheafOfModules.unit (S.totalRingSheaf O))
    (ha : (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).homEquiv _ _ a = 𝟙 _)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    IsIso (((S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv _ K)
      (S.moduleProjectionLeftDerived O n K ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
              a)).app K ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).leftUnitIso
          (totalRingedSite O) K).hom)) := by
  obtain rfl : a = S.componentModuleLowerShriekUnitAugmentation O n :=
    (((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).homEquiv _
        _).symm_apply_apply a).symm.trans
      ((congrArg ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).homEquiv
        _ _).symm ha).trans
      (((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).homEquiv_counit _ _ _).trans
        ((congrArg (fun k => k ≫ _) (Functor.map_id _ _)).trans (Category.id_comp _))))
  convert S.isIso_componentModuleProjectionAdjunctDerived_comp_augmentation O n K using 1
  exact ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv_naturality_right _
    _).trans (congrArg (fun k => k ≫ _) (Equiv.apply_symm_apply _ _))

end CategoryTheory.SimplicialSiteSituation

end
