module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PullbackComposition
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction

/-!
# Étale cohomology of a finite disjoint union

Let `Y` be a scheme and `j_k : U_k ⟶ Y` (`k` in a finite type) open immersions with pairwise
disjoint images covering `Y`. Then for every abelian sheaf `F` on `Y_étale` restriction is an
isomorphism

`H^q(Y, F) ≅ ∏_k H^q(U_k, F|_{U_k})`,

and likewise `H^q(Y, μ_n) ≅ ∏_k H^q(U_k, μ_n)` for the pullbacks
`Stacks.EtaleCohomology.rootsOfUnityPullbackMap` when `n` is invertible on `Y`.

The proof stays inside `Ext` on `Y`. The counits `j_{k!} j_k^{-1} ℤ ⟶ ℤ` of the extensions by
zero exhibit the constant sheaf `ℤ` as the direct sum of the `j_{k!} ℤ` (checked after inverse
image to each `U_m`: the summands with `k ≠ m` vanish there and the counit for `m` becomes
invertible), so `Ext^q(ℤ, F) = ∏_k Ext^q(j_{k!} ℤ, F)`; and `Ext^q(j_{k!} ℤ, F) =
Ext^q(ℤ, j_k^{-1} F)` by the adjunction `j_{k!} ⊣ j_k^{-1}` of exact functors, under which the
`k`-th component is restriction along `j_k`.

## Main results

* `Stacks.ExtFunctorial.bijective_mk₀_comp_pi_of_isIso_biproduct_desc`: `Ext` out of a finite
  direct sum.
* `Stacks.EtaleCohomology.isIso_biproduct_desc_extensionByZero_counit`:
  `F = ⊕_k j_{k!} j_k^{-1} F`.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_pi`: the decomposition of
  cohomology.
* `Stacks.EtaleCohomology.bijective_rootsOfUnityPullbackMap_pi`: the same for `μ_n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry

universe w u v

namespace Stacks.ExtFunctorial

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] [HasFiniteBiproducts C]

omit [HasFiniteBiproducts C] in
/-- `Ext.mk₀` commutes with finite sums. -/
theorem mk₀_sum {X Y : C} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    Ext.mk₀ (∑ k ∈ s, f k) = ∑ k ∈ s, Ext.mk₀.{w} (f k) :=
  map_sum (AddMonoidHom.mk' (fun g : X ⟶ Y => Ext.mk₀.{w} g) Ext.mk₀_add) f s

/-- **`Ext` out of a finite direct sum.** If morphisms `g_k : P_k ⟶ Z` (`k` in a finite type)
induce an isomorphism `⊕_k P_k ≅ Z`, then `x ↦ (x ∘ g_k)_k` is a bijection
`Ext^n(Z, M) ≅ ∏_k Ext^n(P_k, M)`. -/
theorem bijective_mk₀_comp_pi_of_isIso_biproduct_desc {ι : Type*} [Finite ι]
    {P : ι → C} {Z M : C} (g : ∀ k, P k ⟶ Z) [IsIso (biproduct.desc g)] (n : ℕ) :
    Function.Bijective
      (fun (x : Ext.{w} Z M n) (k : ι) => (Ext.mk₀ (g k)).comp x (zero_add n)) := by
  classical
  cases nonempty_fintype ι
  let s : ∀ k, Z ⟶ P k := fun k => inv (biproduct.desc g) ≫ biproduct.π P k
  have hdesc : biproduct.desc g = ∑ k, biproduct.π P k ≫ g k := by
    apply biproduct.hom_ext'
    intro m
    rw [biproduct.ι_desc, Preadditive.comp_sum]
    simp only [biproduct.ι_π_assoc]
    rw [Finset.sum_eq_single m (fun k _ hk => by rw [dite_eq_right (Ne.symm hk), Limits.zero_comp])
      (fun h => absurd (Finset.mem_univ m) h), dite_eq_left rfl, eqToHom_refl, Category.id_comp]
  have hsg : ∑ k, s k ≫ g k = 𝟙 Z := by
    simp only [s, Category.assoc, ← Preadditive.comp_sum]
    rw [← hdesc, IsIso.inv_hom_id]
  have hgs : ∀ m k, g m ≫ s k = if h : m = k then eqToHom (congrArg P h) else 0 := by
    intro m k
    simp only [s, ← Category.assoc]
    rw [← biproduct.ι_desc g m, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc,
      biproduct.ι_π]
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => ∑ k, (Ext.mk₀ (s k)).comp (y k) (zero_add n), fun x => ?_, fun y => ?_⟩
  · change ∑ k, (Ext.mk₀ (s k)).comp ((Ext.mk₀ (g k)).comp x (zero_add n)) (zero_add n) = x
    simp only [Ext.mk₀_comp_mk₀_assoc]
    rw [← Ext.sum_comp, ← Ext.mk₀_sum, hsg]
    exact Ext.mk₀_id_comp x
  · funext m
    change (Ext.mk₀ (g m)).comp (∑ k, (Ext.mk₀ (s k)).comp (y k) (zero_add n)) (zero_add n) = y m
    rw [Ext.comp_sum]
    simp only [Ext.mk₀_comp_mk₀_assoc, hgs]
    rw [Finset.sum_eq_single m]
    · simp only [dite_true, eqToHom_refl]
      exact Ext.mk₀_id_comp (y m)
    · intro k _ hk
      rw [dite_eq_right (Ne.symm hk), Ext.mk₀_zero, Ext.zero_comp]
    · intro h
      exact absurd (Finset.mem_univ m) h

/-- **The adjunction map on a restricted class.** Let `L ⊣ R` be an adjunction of exact
functors, `G ≅ R` an exact functor isomorphic to `R`, and `κ : G Z_D ≅ Z_C`. For
`x : Ext^q(Z_D, F)`, the adjunction map `Ext^q(Z_C, R F) ⟶ Ext^q(L Z_C, F)` carries the class
`κ^{-1} ∘ G(x)` (read in `R F`) to `x ∘ ε` for the morphism `ε : L Z_C ⟶ L R Z_D ⟶ Z_D`. -/
theorem extMap_mk₀_comp_mapExactFunctor
    {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
    [HasExt.{w} C] [HasExt.{w} D] [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (G : D ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (ρ : G ≅ R) {ZD : D} {ZC : C} (κ : G.obj ZD ≅ ZC) {F : D} {q : ℕ} (x : Ext.{w} ZD F q) :
    Stacks.ExtAdjunction.extMap adj ZC F q
        (((Ext.mk₀ κ.inv).comp (x.mapExactFunctor G) (zero_add q)).comp
          (Ext.mk₀ (ρ.hom.app F)) (add_zero q)) =
      (Ext.mk₀ (L.map (κ.inv ≫ ρ.hom.app ZD) ≫ adj.counit.app ZD)).comp x (zero_add q) := by
  rw [Stacks.ExtAdjunction.extMap_apply, Ext.comp_assoc_of_third_deg_zero,
    ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor ρ.hom, Ext.mk₀_comp_mk₀_assoc,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Stacks.ExtFunctorial.mapExactFunctor_comp_functor, Ext.comp_assoc_of_third_deg_zero,
    ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor adj.counit,
    Stacks.ExtFunctorial.mapExactFunctor_id, Ext.mk₀_comp_mk₀_assoc]

end Stacks.ExtFunctorial

namespace CategoryTheory.Limits

/-- A morphism out of a finite biproduct all of whose summands but one are zero is an
isomorphism as soon as its component at the remaining summand is. -/
theorem isIso_biproduct_desc_of_isZero {C : Type*} [Category* C] [Preadditive C]
    {ι : Type*} {P : ι → C} [HasBiproduct P] {Z : C}
    (f : ∀ k, P k ⟶ Z) (m : ι) (hz : ∀ k, k ≠ m → IsZero (P k)) [IsIso (f m)] :
    IsIso (biproduct.desc f) := by
  classical
  refine ⟨⟨inv (f m) ≫ biproduct.ι P m, ?_, ?_⟩⟩
  · refine biproduct.hom_ext' _ _ fun k => ?_
    rw [biproduct.ι_desc_assoc, Category.comp_id]
    obtain rfl | hk := eq_or_ne k m
    · simp
    · exact (hz k hk).eq_of_src _ _
  · simp

end CategoryTheory.Limits

namespace Stacks.EtaleCohomology

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {Y : Scheme.{u}} {ι : Type} [Fintype ι] [DecidableEq ι] {U : ι → Scheme.{u}}
  (j : ∀ k, U k ⟶ Y) [∀ k, IsOpenImmersion (j k)]
  (hdisj : Pairwise fun k m => Disjoint (Set.range (j k).base) (Set.range (j m).base))
  (hcov : ⋃ k, Set.range (j k).base = Set.univ)

omit [Fintype ι] [DecidableEq ι] in
/-- Inverse image along `g` of a morphism out of a finite biproduct, through the comparison of
the inverse image of a biproduct with the biproduct of the inverse images. -/
theorem etaleAbelianInverseImage_map_biproduct_desc [Finite ι] {T : Scheme.{u}} (g : T ⟶ Y)
    {P : ι → Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (f : ∀ k, P k ⟶ F) :
    (etaleAbelianInverseImage.{u, v} g).map (biproduct.desc f) =
      ((etaleAbelianInverseImage.{u, v} g).mapBiproduct P).hom ≫
        biproduct.desc (fun k => (etaleAbelianInverseImage.{u, v} g).map (f k)) := by
  rw [← Iso.inv_comp_eq]
  refine biproduct.hom_ext' _ _ fun k => ?_
  rw [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, ← Functor.map_comp, biproduct.ι_desc,
    biproduct.ι_desc]

omit [Fintype ι] [DecidableEq ι] in
include hdisj hcov in
/-- **A sheaf on a finite disjoint union of opens is the direct sum of its extensions by zero**:
the counits `j_{k!} j_k^{-1} F ⟶ F` induce an isomorphism `⊕_k j_{k!} j_k^{-1} F ≅ F`. -/
theorem isIso_biproduct_desc_extensionByZero_counit [Finite ι]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (biproduct.desc fun k => (extensionByZeroAdj.{u, v} (j k)).counit.app F) := by
  refine isIso_of_isIso_etaleAbelianInverseImage_family.{u, v} (fun a : ULift.{u} ι => j a.down)
    (by
      rw [← hcov]
      ext y
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨a, ha⟩ => ⟨a.down, ha⟩, fun ⟨a, ha⟩ => ⟨ULift.up a, ha⟩⟩) _
    fun a => ?_
  obtain ⟨m⟩ := a
  dsimp only
  rw [etaleAbelianInverseImage_map_biproduct_desc]
  have : IsIso ((etaleAbelianInverseImage.{u, v} (j m)).map
      ((extensionByZeroAdj.{u, v} (j m)).counit.app F)) :=
    isIso_etaleAbelianInverseImage_map_counit_of_factors (j m) (j m) (𝟙 _) (Category.id_comp _) F
  have h2 : IsIso (biproduct.desc fun k => (etaleAbelianInverseImage.{u, v} (j m)).map
      ((extensionByZeroAdj.{u, v} (j k)).counit.app F)) :=
    isIso_biproduct_desc_of_isZero _ m fun k hk =>
      isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint (j m) (j k)
        (hdisj (Ne.symm hk)) _
  exact IsIso.comp_isIso' inferInstance h2

variable [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [∀ k, HasExt.{w} (Sheaf (U k).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

section OneOpen

variable {V : Scheme.{u}} (i : V ⟶ Y) [IsOpenImmersion i]
  [HasExt.{w} (Sheaf V.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- The adjunction map of `i_! ⊣ i^{-1}` on `Ext` out of the constant sheaf of `V`, read on
`H^q(V, i^{-1} F)` through `i^{-1} ≅ (restriction to V)`. -/
abbrev restrictionExtMap (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (y : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj F) q) :
    Ext.{w} ((extensionByZero.{u, v} i).obj ((constantSheaf V.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift ℤ)))) F q :=
  Stacks.ExtAdjunction.extMap (extensionByZeroAdj.{u, v} i) _ F q
    (y.comp (Ext.mk₀ ((etaleAbelianInverseImageRestrictionIso.{u, v} i).hom.app F)) (add_zero q))

/-- The map `restrictionExtMap i F q : H^q(V, i^{-1} F) ⟶ Ext^q(i_! ℤ_V, F)` is bijective. -/
theorem bijective_restrictionExtMap
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (restrictionExtMap.{w} i F q) :=
  (Stacks.ExtAdjunction.extMap_bijective (extensionByZeroAdj.{u, v} i) _ F q).comp
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso _ q)

/-- On a restricted class the adjunction map is precomposition with
`i_! ℤ_V ≅ i_! i^{-1} ℤ_Y ⟶ ℤ_Y`. -/
theorem restrictionExtMap_etaleCohomologyRestrictionMap
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    restrictionExtMap.{w} i F q (etaleCohomologyRestrictionMap.{u, v, w} i F q x) =
      (Ext.mk₀ ((extensionByZero.{u, v} i).mapIso
        (((etaleAbelianInverseImageConstantIso.{u, v} i).app (AddCommGrpCat.of (ULift ℤ))).symm ≪≫
          (etaleAbelianInverseImageRestrictionIso.{u, v} i).app _)).hom).comp
        ((Ext.mk₀ ((extensionByZeroAdj.{u, v} i).counit.app
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift ℤ))))).comp x (zero_add q))
        (zero_add q) := by
  rw [Ext.mk₀_comp_mk₀_assoc]
  exact Stacks.ExtFunctorial.extMap_mk₀_comp_mapExactFunctor
    (extensionByZeroAdj.{u, v} i) (etaleAbelianInverseImage.{u, v} i)
    (etaleAbelianInverseImageRestrictionIso.{u, v} i)
    ((etaleAbelianInverseImageConstantIso.{u, v} i).app (AddCommGrpCat.of (ULift ℤ))) x

end OneOpen

omit [Fintype ι] [DecidableEq ι] in
include hdisj hcov in
/-- **Étale cohomology of a finite disjoint union of opens**: restriction
`H^q(Y, F) ⟶ ∏_k H^q(U_k, F|_{U_k})` is bijective. -/
theorem bijective_etaleCohomologyRestrictionMap_pi [Finite ι]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (fun (x : Sheaf.H.{w} F q) (k : ι) =>
      etaleCohomologyRestrictionMap.{u, v, w} (j k) F q x) := by
  have hε := isIso_biproduct_desc_extensionByZero_counit j hdisj hcov
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (AddCommGrpCat.of (ULift ℤ)))
  have hΨ := (Function.Bijective.piMap fun k =>
      Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := F)
        ((extensionByZero.{u, v} (j k)).mapIso
          (((etaleAbelianInverseImageConstantIso.{u, v} (j k)).app
              (AddCommGrpCat.of (ULift ℤ))).symm ≪≫
            (etaleAbelianInverseImageRestrictionIso.{u, v} (j k)).app _)).hom q).comp
    (Stacks.ExtFunctorial.bijective_mk₀_comp_pi_of_isIso_biproduct_desc (M := F)
      (fun k => (extensionByZeroAdj.{u, v} (j k)).counit.app
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift ℤ)))) q)
  refine (Function.Bijective.of_comp_iff' (Function.Bijective.piMap fun k =>
    bijective_restrictionExtMap.{w} (j k) F q) _).1 ?_
  convert hΨ using 1
  funext x k
  exact restrictionExtMap_etaleCohomologyRestrictionMap.{w} (j k) F q x

omit [Fintype ι] [DecidableEq ι] in
include hdisj hcov in
/-- **`H^q(Y, μ_n) ≅ ∏_k H^q(U_k, μ_n)`** for a finite disjoint union of opens and `n`
invertible on `Y`, through the pullbacks `Stacks.EtaleCohomology.rootsOfUnityPullbackMap`. -/
theorem bijective_rootsOfUnityPullbackMap_pi [Finite ι] {n : ℕ} (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    (q : ℕ) :
    Function.Bijective (fun (x : Sheaf.H.{w} (Stacks.Kummer.rootsOfUnitySheaf.{u, v} Y n) q)
      (k : ι) => rootsOfUnityPullbackMap.{u, v, w} (j k) n q x) := by
  have hb : ∀ k, Function.Bijective
      (Sheaf.H.map (Stacks.Kummer.rootsOfUnityInverseImageComparison.{u, v} (j k) n) q) :=
    fun k => by
      have := Stacks.Kummer.isIso_rootsOfUnityInverseImageComparison.{u, v} (j k) n hn
      exact Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso _ q
  exact (Function.Bijective.piMap hb).comp
    (bijective_etaleCohomologyRestrictionMap_pi j hdisj hcov _ q)

end Stacks.EtaleCohomology

end
