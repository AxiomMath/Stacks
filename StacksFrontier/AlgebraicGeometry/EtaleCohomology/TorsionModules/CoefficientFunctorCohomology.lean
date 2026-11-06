module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology

/-!
# Finiteness of cohomology through a coefficient functor and its underlying abelian functor

Let `Λ` be a commutative ring and `X` a quasi-compact and quasi-separated scheme. Suppose given a
functor `T^Λ` from `Λ`-modules to sheaves of `Λ`-modules on `X_étale` and a functor `T` from
abelian groups to abelian sheaves on `X_étale`, such that forgetting the module structure of
`T^Λ(M)` gives `T` of the underlying abelian group of `M`, `T` is additive and commutes with
filtered colimits, and multiplication by `a ∈ Λ` on `M` induces multiplication by `a` on `T^Λ(M)`.
The model is `T^Λ(M) = j_!(M̲)` for an étale morphism `j : U ⟶ X`, and also the constant sheaf
`M̲` itself (`j = id`).

This file proves the `𝔽_ℓ`-basis trick of the proof of [Stacks, Tag 0GJC] in that generality: if
`H^q(X, T(ℤ/ℓ))` is finite for a prime `ℓ`, then `H^q(X, T^Λ(M))` is a finite `Λ`-module for every
finite `Λ`-module `M` killed by `ℓ`; and, when `T^Λ` is exact and `Λ` Noetherian, the dévissage
from an integer `n > 0` killing `M` to its prime divisors. The argument is word for word that of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TorsionModules/ConstantCoefficientsCohomology.lean`,
which is the case of the constant sheaf; only the properties of the constant sheaf functor listed
above are used there.

## Main definitions

* `Stacks.EtaleCohomology.coefficientCohomologyMap`: the map `H^q(X, T(A)) ⟶ H^q(X, T^Λ(M))`
  induced by an additive map `A ⟶ M`.

## Main results

* `Stacks.EtaleCohomology.module_finite_coefficientCohomology_of_prime`: the `𝔽_ℓ`-basis trick.
* `Stacks.EtaleCohomology.module_finite_coefficientCohomology_of_nsmul_eq_zero`: the dévissage.

## References

* [Stacks Project, Tag 0GJC](https://stacks.math.columbia.edu/tag/0GJC)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable {Λ : Type r} [CommRing Λ] {X : Scheme.{u}}
  {T : AddCommGrpCat.{max (u + 1) r} ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}}
  {TΛ : ModuleCat.{max (u + 1) r} Λ ⥤ EtaleModules.{u, r} Λ X}
  (e : TΛ ⋙ etaleModuleForgetAb.{u, r} Λ X ≅
    forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ⋙ T)

/-- The global sections functor on abelian sheaves on `X_étale` is additive. -/
local instance : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The map `H^q(X, T(A)) ⟶ H^q(X, T^Λ(M))` induced by an additive map `φ : A ⟶ M`**, read on
underlying abelian groups through `Stacks.EtaleCohomology.etaleModuleCohomologyForgetIso`. -/
def coefficientCohomologyMap (q : ℕ) {A : AddCommGrpCat.{max (u + 1) r}}
    {M : ModuleCat.{max (u + 1) r} Λ}
    (φ : A ⟶ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj M) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).obj (T.obj A) ⟶
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj
        (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (TΛ.obj M)) :=
  ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).map
      (T.map φ ≫ (e.app M).inv) ≫
    ((etaleModuleCohomologyForgetIso.{u, r} Λ X q).app _).inv

variable [T.Additive]

/-- The map induced by a finite sum `∑ i ∈ s, φ i` is the sum of the maps induced by the `φ i`. -/
theorem coefficientCohomologyMap_sum (q : ℕ) {A : AddCommGrpCat.{max (u + 1) r}}
    {M : ModuleCat.{max (u + 1) r} Λ} {ι : Type*} (s : Finset ι)
    (φ : ι → (A ⟶ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj M)) :
    coefficientCohomologyMap e q (∑ i ∈ s, φ i) =
      ∑ i ∈ s, coefficientCohomologyMap e q (φ i) := by
  unfold coefficientCohomologyMap
  rw [T.map_sum, Preadditive.sum_comp,
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).map_sum,
    Preadditive.sum_comp]

/-- The map induced by `g ≫ φ` is the map `H^q(X, T(A)) ⟶ H^q(X, T(B))` induced by `T(g)` followed
by the map induced by `φ`. -/
theorem coefficientCohomologyMap_comp (q : ℕ) {A B : AddCommGrpCat.{max (u + 1) r}}
    {M : ModuleCat.{max (u + 1) r} Λ} (g : A ⟶ B)
    (φ : B ⟶ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj M) :
    coefficientCohomologyMap e q (g ≫ φ) =
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).map
          (T.map g) ≫ coefficientCohomologyMap e q φ := by
  simp only [coefficientCohomologyMap, Functor.map_comp, Category.assoc]

/-- **Multiplication by a scalar after `φ` multiplies the induced map by that scalar**, as soon as
multiplication by `a` on `M` induces multiplication by `a` on `T^Λ(M)`. -/
theorem coefficientCohomologyMap_smul
    (hlin : ∀ (M : ModuleCat.{max (u + 1) r} Λ) (a : Λ), TΛ.map (a • 𝟙 M) = a • 𝟙 (TΛ.obj M))
    (q : ℕ) {A : AddCommGrpCat.{max (u + 1) r}} {M : ModuleCat.{max (u + 1) r} Λ}
    (φ : A ⟶ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj M)
    (a : Λ) :
    coefficientCohomologyMap e q
        (φ ≫ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).map
          (a • 𝟙 M)) =
      coefficientCohomologyMap e q φ ≫
        (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).map
          (a • 𝟙 (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (TΛ.obj M))) := by
  have := Stacks.DerivedLinear.rightDerived_linear (R := Λ)
    (etaleModuleGlobalSections.{u, r} Λ X) q
  let F := TΛ.obj M
  have hθ : T.map ((forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).map
        (a • 𝟙 M)) ≫ e.inv.app M =
      e.inv.app M ≫ (etaleModuleForgetAb.{u, r} Λ X).map (a • 𝟙 F) := by
    have h := e.inv.naturality (a • 𝟙 M)
    simp only [Functor.comp_map] at h
    rw [h, hlin M a]
  have hψ := (etaleModuleCohomologyForgetIso.{u, r} Λ X q).inv.naturality (a • 𝟙 F)
  simp only [Functor.comp_map, Functor.map_smul, CategoryTheory.Functor.map_id] at hψ
  unfold coefficientCohomologyMap
  rw [T.map_comp φ, Category.assoc, Iso.app_inv, hθ, ← Category.assoc, Functor.map_comp,
    Category.assoc, Iso.app_inv, hψ]
  simp only [Category.assoc, Iso.app_inv]
  rfl

section Colimit

/-- **On a quasi-compact quasi-separated scheme, every class of `H^q(X, T^Λ(M))` comes from a
stage of a filtered colimit presentation of `M`**, `T` commuting with filtered colimits and étale
cohomology of `X` commuting with filtered colimits (Stacks 03Q5). -/
theorem exists_coefficientCohomologyMap_eq_of_isColimit [CompactSpace X] [QuasiSeparatedSpace X]
    {J : Type (max (u + 1) r)} [SmallCategory J] [IsFiltered J] [PreservesColimitsOfShape J T]
    {D : J ⥤ AddCommGrpCat.{max (u + 1) r}} {M : ModuleCat.{max (u + 1) r} Λ}
    (ι : D ⟶ (Functor.const J).obj
      ((forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj M))
    (hc : IsColimit (Cocone.mk _ ι)) (q : ℕ)
    (x : ((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (TΛ.obj M)) :
    ∃ (j : J) (y : ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived
        q).obj (T.obj (D.obj j))),
      coefficientCohomologyMap e q (ι.app j) y = x := by
  let G := T ⋙ (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q
  have : PreservesColimitsOfShape J
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q) :=
    preservesColimitsOfShape_rightDerived_Γ_smallEtale.{r} X q J
  have hG := isColimitOfPreserves G hc
  let eH := (etaleModuleCohomologyForgetIso.{u, r} Λ X q).app (TΛ.obj M) ≪≫
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).mapIso
      (e.app M)
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _ hG (eH.hom x)
  refine ⟨j, y, ?_⟩
  have h : coefficientCohomologyMap e q (ι.app j) =
      (G.mapCocone (Cocone.mk _ ι)).ι.app j ≫ eH.inv := by
    rw [Functor.mapCocone_ι_app, Functor.comp_map]
    simp only [eH, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
    unfold coefficientCohomologyMap
    rw [Functor.map_comp, Category.assoc]
    simp only [Iso.app_inv]
  rw [h, ConcreteCategory.comp_apply, hy, ← ConcreteCategory.comp_apply, Iso.hom_inv_id,
    ConcreteCategory.id_apply]

end Colimit

section Prime

include e in
/-- **The `𝔽_ℓ`-basis trick of [Stacks, Tag 0GJC] for a coefficient functor.** Let `X` be
quasi-compact and quasi-separated, `ℓ` a prime such that `H^q(X, T(ℤ/ℓ))` is finite, and `M` a
finite `Λ`-module killed by `ℓ`. Then `H^q(X, T^Λ(M))` is a finite `Λ`-module.

Every class of `H^q(X, T^Λ(M))` comes from `H^q(X, T(W))` for a finitely generated subgroup `W` of
`M` (Stacks 03Q5), which is a finite dimensional `𝔽_ℓ`-vector space; writing the inclusion
`W ⟶ M` through coordinates and generators `s_j` of `M`, the class lies in the `Λ`-submodule
generated by the images of the finite group `H^q(X, T(ℤ/ℓ))` under the maps induced by
`1 ↦ s_j`. -/
theorem module_finite_coefficientCohomology_of_prime [CompactSpace X] [QuasiSeparatedSpace X]
    (hcol : ∀ (J : Type (max (u + 1) r)) [SmallCategory J] [IsFiltered J],
      PreservesColimitsOfShape J T)
    (hlin : ∀ (M : ModuleCat.{max (u + 1) r} Λ) (a : Λ), TΛ.map (a • 𝟙 M) = a • 𝟙 (TΛ.obj M))
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℕ)
    (hfin : Finite (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived
      q).obj (T.obj (AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ))))))
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] (hM : ∀ m : M, ℓ • m = 0) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (TΛ.obj M)) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' Λ M
  let s : Fin n → M := fun j => f (fun i => if j = i then 1 else 0)
  let Z := AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ))
  let Mab := (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj M
  have hMZ : ∀ m : M, zmultiplesHom M m ℓ = 0 := fun m => by
    rw [zmultiplesHom_apply, natCast_zsmul, hM m]
  let ιm : M → (Z ⟶ (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj M) :=
    fun m => AddCommGrpCat.ofHom
    ((ZMod.lift ℓ ⟨zmultiplesHom M m, hMZ m⟩).comp AddEquiv.ulift.toAddMonoidHom)
  have hιm : ∀ (m : M) (a : ZMod ℓ), ιm m (ULift.up a) = a.val • m := fun m a => by
    show ZMod.lift ℓ ⟨zmultiplesHom M m, hMZ m⟩ a = a.val • m
    have ha : a = ((a.val : ℤ) : ZMod ℓ) := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    calc ZMod.lift ℓ ⟨zmultiplesHom M m, hMZ m⟩ a
        = ZMod.lift ℓ ⟨zmultiplesHom M m, hMZ m⟩ ((a.val : ℤ) : ZMod ℓ) := congrArg _ ha
      _ = a.val • m := by rw [ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]
  let H := ((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (TΛ.obj M)
  let gens : Set H := ⋃ j, Set.range (coefficientCohomologyMap e q (ιm (s j)))
  have hgens : gens.Finite := Set.finite_iUnion (fun j => Set.finite_range _)
  suffices hspan : Submodule.span Λ gens = ⊤ from
    ⟨Submodule.fg_def.2 ⟨gens, hgens, hspan⟩⟩
  refine eq_top_iff.2 fun x _ => ?_
  have := hcol (Finset Mab)
  obtain ⟨S, y, rfl⟩ := exists_coefficientCohomologyMap_eq_of_isColimit e
    (finsetClosureCocone Mab).ι (finsetClosureCoconeIsColimit Mab) q x
  let W := AddSubgroup.closure (S : Set Mab)
  have hW : ∀ w : W, ℓ • w = 0 := fun w => Subtype.ext (hM w.1)
  have : Module.Finite ℤ W :=
    Module.Finite.iff_addGroup_fg.2 (AddSubgroup.isAddFG_iff.2 ⟨S, rfl⟩)
  obtain ⟨d, e', v, hv⟩ := exists_zmod_coordinates ℓ W hW
  have hc : ∀ k, ∃ c : Fin n → Λ, ((v k : W) : M) = ∑ j, c j • s j := fun k => by
    obtain ⟨c, hc⟩ := hf ((v k : W) : M)
    exact ⟨c, by rw [← hc, LinearMap.pi_apply_eq_sum_univ]⟩
  choose c hc using hc
  let coord : Fin d → ((finsetClosureDiagram Mab).obj S ⟶ Z) := fun k =>
    show AddCommGrpCat.of W ⟶ Z from
      AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp (e' k))
  have hsum : ∀ {A B : AddCommGrpCat.{max (u + 1) r}} {κ : Type} (G : Finset κ)
      (g : κ → (A ⟶ B)) (a : A), (∑ i ∈ G, g i) a = ∑ i ∈ G, g i a := by
    intro A B κ G g a
    induction G using Finset.induction with
    | empty => rfl
    | insert i G hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, AddCommGrpCat.hom_add_apply, ih]
  let φS : (finsetClosureDiagram Mab).obj S ⟶
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj M :=
    show AddCommGrpCat.of W ⟶ Mab from AddCommGrpCat.ofHom W.subtype
  have hφS : (finsetClosureCocone Mab).ι.app S = φS := rfl
  have key : φS = ∑ k, ∑ j, coord k ≫ ιm (s j) ≫
        (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).map
          (c k j • 𝟙 M) := by
    refine AddCommGrpCat.ext fun w => ?_
    rw [hsum]
    simp_rw [hsum]
    show (w.1 : M) = ∑ k, ∑ j, c k j • (show M from ιm (s j) (ULift.up (e' k w)))
    simp_rw [hιm, smul_comm (c _ _) ((e' _ w).val), ← Finset.smul_sum, ← hc]
    conv_lhs => rw [hv w]
    rw [AddSubgroup.val_finset_sum]
    rfl
  rw [hφS, key, coefficientCohomologyMap_sum, hsum]
  refine Submodule.sum_mem (p := Submodule.span Λ gens) fun k _ => ?_
  rw [coefficientCohomologyMap_sum, hsum]
  refine Submodule.sum_mem (p := Submodule.span Λ gens) fun j _ => ?_
  rw [← Category.assoc, coefficientCohomologyMap_smul e hlin, coefficientCohomologyMap_comp]
  refine Submodule.smul_mem _ (c k j) (Submodule.subset_span ?_)
  exact Set.mem_iUnion.2 ⟨j, ⟨_, rfl⟩⟩

end Prime

section Devissage

attribute [local instance] HasDerivedCategory.standard

include e in
/-- **[Stacks, Tag 0GJC], the dévissage to a prime, for a coefficient functor.** Let `Λ` be
Noetherian, `X` quasi-compact and quasi-separated, `T^Λ` exact, and `n > 0` an integer such that
`H^q(X, T(ℤ/ℓ))` is finite for every prime `ℓ` dividing `n` and every `q`. Then for every finite
`Λ`-module `M` killed by `n` and every `q`, the `Λ`-module `H^q(X, T^Λ(M))` is finite.

For `n = ℓ n'` with `ℓ` prime, the short exact sequence `0 ⟶ M[ℓ] ⟶ M ⟶ M/M[ℓ] ⟶ 0` gives an
exact sequence `H^q(X, T^Λ(M[ℓ])) ⟶ H^q(X, T^Λ(M)) ⟶ H^q(X, T^Λ(M/M[ℓ]))`; the left term is finite
by the `𝔽_ℓ`-basis trick and the right one by induction on `n`. -/
theorem module_finite_coefficientCohomology_of_nsmul_eq_zero [IsNoetherianRing Λ] [CompactSpace X]
    [QuasiSeparatedSpace X]
    (hcol : ∀ (J : Type (max (u + 1) r)) [SmallCategory J] [IsFiltered J],
      PreservesColimitsOfShape J T)
    [PreservesFiniteLimits TΛ] [PreservesFiniteColimits TΛ]
    (hlin : ∀ (M : ModuleCat.{max (u + 1) r} Λ) (a : Λ), TΛ.map (a • 𝟙 M) = a • 𝟙 (TΛ.obj M))
    (n : ℕ) (hn : 0 < n)
    (hfin : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ∀ q : ℕ,
      Finite (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).obj
        (T.obj (AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ))))))
    (M : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ M] (hM : ∀ m : M, n • m = 0) (q : ℕ) :
    Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj (TΛ.obj M)) := by
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  by_cases h1 : n = 1
  · subst h1
    have hM0 : IsZero M := by
      refine @ModuleCat.isZero_of_subsingleton _ _ M ⟨fun a b => ?_⟩
      rw [← one_nsmul a, ← one_nsmul b, hM a, hM b]
    have := ModuleCat.subsingleton_of_isZero
      (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).map_isZero (TΛ.map_isZero hM0))
    infer_instance
  · let ℓ := n.minFac
    have hℓ : ℓ.Prime := Nat.minFac_prime h1
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓn : ℓ ∣ n := Nat.minFac_dvd n
    obtain ⟨n', hn'⟩ := hℓn
    have hn'0 : 0 < n' := Nat.pos_of_ne_zero fun h => by
      rw [h, mul_zero] at hn'
      omega
    have hn'lt : n' < n := by
      rw [hn']
      exact lt_mul_left hn'0 hℓ.one_lt
    let K : Submodule Λ M := LinearMap.ker ((ℓ : ℕ) • LinearMap.id)
    let g : M →ₗ[Λ] M ⧸ K := K.mkQ
    let S := g.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer K.mkQ_surjective
    have : TΛ.Additive := Functor.additive_of_preserves_binary_products _
    have hS' := hS.map_of_exact TΛ
    have hex : ((S.map TΛ).map ((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q)).Exact :=
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (etaleModuleGlobalSections.{u, r} Λ X)).exact_map hS' q
    have hex' := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hex
    have h₁ : Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
        (TΛ.obj S.X₁)) := by
      have : Module.Finite Λ S.X₁ := inferInstanceAs (Module.Finite Λ (LinearMap.ker g))
      refine module_finite_coefficientCohomology_of_prime e hcol hlin ℓ q
        (hfin ℓ hℓ ⟨n', hn'⟩ q) S.X₁ ?_
      intro x
      have hx : (x : M) ∈ K := by
        have h : g x = 0 := x.2
        exact (Submodule.Quotient.mk_eq_zero K).1 h
      apply Subtype.ext
      show ℓ • (x : M) = 0
      simpa [K] using hx
    have h₃ : Module.Finite Λ (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj
        (TΛ.obj S.X₃)) := by
      have : Module.Finite Λ S.X₃ := inferInstanceAs (Module.Finite Λ (M ⧸ K))
      refine ih n' hn'lt hn'0 (fun l hl hln => hfin l hl (hln.trans ⟨ℓ, by rw [hn', mul_comm]⟩))
        S.X₃ ?_
      intro x
      obtain ⟨m, rfl⟩ := K.mkQ_surjective x
      show n' • K.mkQ m = 0
      rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
      show ℓ • n' • m = 0
      rw [smul_smul, ← hn', hM m]
    let F := (etaleModuleGlobalSections.{u, r} Λ X).rightDerived q
    let φ := (F.map (TΛ.map S.f)).hom
    let ψ := (F.map (TΛ.map S.g)).hom
    have : IsNoetherian Λ (F.obj (TΛ.obj S.X₃)) := isNoetherian_of_isNoetherianRing_of_finite _ _
    have : Module.Finite Λ (LinearMap.range ψ) :=
      Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
    have hexr : Function.Exact φ ψ.rangeRestrict := fun x => by
      have hx := hex' x
      exact ⟨fun h => hx.1 (congrArg Subtype.val h), fun h => Subtype.ext (hx.2 h)⟩
    exact Module.Finite.of_exact hexr ψ.surjective_rangeRestrict

end Devissage

end Stacks.EtaleCohomology

end
