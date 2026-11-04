module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctionsAdicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyAdicBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentUniverseDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# The theorem on formal functions for algebraic spaces, unconditionally

[Stacks, Tag 08AZ] is registered on the base in the vocabulary of
`AlgebraicGeometry.Space.FormalFunctionsSituation` — module universe `max (u + 1) w`, the
cohomology `AlgebraicGeometry.Space.cohomologyOverBase`, the quotients
`AlgebraicGeometry.Space.SiteAdicCohomology.adicQuotient` — granted the bounds of
[Stacks, Tag 08AY] as the hypothesis `Is08AYBound`.  This file proves those bounds, so that the
theorem holds outright.

The bounds are proved at the module universe `u` of the structure rings in
`AlgebraicGeometry.Space.exists_adicCohomology_bounds`.  They are transported here along the
universe lift `SheafOfModules.uliftForPresentation` of the sections: a coherent module of
Situation 08AV is the lift of a coherent module `M` with sections in `Type u`
(`AlgebraicGeometry.Space.exists_iso_uliftForPresentation_of_isCoherent`); the lift of
`M / Iⁿ M` is the quotient of the lift by `Iⁿ`, both being the universal quotient killed by the
functions `φ(a)`, `a ∈ Iⁿ` (`AlgebraicGeometry.Space.SiteAdicCohomology.exists_adicQuotient_iso`);
and the cohomology of a lift is the lift of the cohomology, naturally
(`Stacks.Cohomology.SiteModules.rightDerivedGlobalSectionsUliftIso`).

## Main results

* `AlgebraicGeometry.Space.FormalFunctionsSituation.exists_is08AYBound` — **Stacks 08AY**,
  clauses (1) and (3), in Situation 08AV.
* `AlgebraicGeometry.Space.FormalFunctionsSituation.formalFunctionsEquivOfIsProper` —
  **Stacks 08AZ** (the isomorphism of `A`-modules), unconditionally.
* `AlgebraicGeometry.Space.FormalFunctionsSituation.formalFunctionsEquivOfIsProper_proj_of` — it
  is the isomorphism defined by the system of quotient maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe u w s t r v a

namespace AlgebraicGeometry.Space

/-! ### Transport of the bounds along equivalences of towers -/

section Transport

variable {A : Type*} [CommRing A] (I : Ideal A) {M M' : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup M'] [Module A M'] {P P' : ℕ → Type*} [∀ n, AddCommGroup (P n)]
  [∀ n, Module A (P n)] [∀ n, AddCommGroup (P' n)] [∀ n, Module A (P' n)]
  (π : ∀ n, M →ₗ[A] P n) (T : ∀ m n : ℕ, m ≤ n → P n →ₗ[A] P m)
  (π' : ∀ n, M' →ₗ[A] P' n) (T' : ∀ m n : ℕ, m ≤ n → P' n →ₗ[A] P' m)
  (α : M ≃ₗ[A] M') (β : ∀ n, P n ≃ₗ[A] P' n)
  (hπ : ∀ n x, β n (π n x) = π' n (α x))
  (hT : ∀ m n h x, β m (T m n h x) = T' m n h (β n x))

include hπ in
/-- Clause (1) of [Stacks, Tag 08AY] transfers along equivalences of towers. -/
theorem ker_le_pow_smul_top_of_linearEquiv (c : ℕ)
    (h : ∀ n, c ≤ n → LinearMap.ker (π' n) ≤ I ^ (n - c) • (⊤ : Submodule A M')) :
    ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A M) := by
  intro n hn x hx
  have hx' : α x ∈ LinearMap.ker (π' n) := by
    rw [LinearMap.mem_ker, ← hπ, LinearMap.mem_ker.1 hx, map_zero]
  have hmem := Submodule.mem_map_of_mem (f := α.symm.toLinearMap) (h n hn hx')
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at hmem
  simpa using hmem

include hπ hT in
/-- Clause (3) of [Stacks, Tag 08AY] transfers along equivalences of towers. -/
theorem range_eq_of_linearEquiv
    (h : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (hnk : n ≤ k), c₂ ≤ k →
      LinearMap.range (T' n k hnk) = LinearMap.range (π' n)) :
    ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (hnk : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k hnk) = LinearMap.range (π n) := by
  intro n
  obtain ⟨c₂, hc₂, hr⟩ := h n
  refine ⟨c₂, hc₂, fun k hnk hk => ?_⟩
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ : β n (T n k hnk z) ∈ LinearMap.range (π' n) := by
      rw [hT, ← hr k hnk hk]
      exact ⟨_, rfl⟩
    refine ⟨α.symm w, (β n).injective ?_⟩
    rw [hπ, LinearEquiv.apply_symm_apply, hw]
  · rintro ⟨x, rfl⟩
    obtain ⟨w, hw⟩ : β n (π n x) ∈ LinearMap.range (T' n k hnk) := by
      rw [hπ, hr k hnk hk]
      exact ⟨_, rfl⟩
    refine ⟨(β k).symm w, (β n).injective ?_⟩
    rw [hT, LinearEquiv.apply_symm_apply, hw]

end Transport

/-- The sections of the structure sheaf of a ringed site commute. -/
local instance isMulCommutative_ringSheaf' (X : RingedSite.{s, t, r}) :
    ∀ U, IsMulCommutative (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U) :=
  fun U => ⟨⟨fun a b => RingedSite.mul_comm_ringSheaf X U a b⟩⟩

namespace SiteAdicCohomology

variable {C : Type s} [Category.{t} C] {J : GrothendieckTopology C} (O : Sheaf J RingCat.{r})
  [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)] {A : Type a} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing O)) (I : Ideal A)

/-- Multiplication by a function in the ideal of global functions generated by `φ(J)` is killed
by a morphism which kills multiplication by the functions `φ(a)`, `a ∈ J`. -/
theorem globalSmul_comp_eq_zero_of_mem_map {G T : SheafOfModules.{v} O} (h : G ⟶ T) (K : Ideal A)
    (hh : ∀ a ∈ K, globalSmul O (φ a) G ≫ h = 0) {b : ↥(GlobalSectionRing O)}
    (hb : b ∈ Ideal.map φ K) : globalSmul O b G ≫ h = 0 := by
  refine Submodule.span_induction (p := fun b _ => globalSmul O b G ≫ h = 0) ?_ ?_ ?_ ?_ hb
  · rintro _ ⟨a, ha, rfl⟩
    exact hh a ha
  · rw [globalSmul_zero, zero_comp]
  · intro x y _ _ hx hy
    rw [globalSmul_add, Preadditive.add_comp, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_eq_mul, globalSmul_mul, Category.assoc, hx, comp_zero]

variable (F : SheafOfModules.{max s t r v} O)

/-- The quotient map `F ⟶ F / Iⁿ F` is an epimorphism. -/
instance epi_adicProj (n : ℕ) : Epi (adicProj O φ I F n) :=
  inferInstanceAs (Epi (cokernel.π (idealSmulHom O (mapIdealPow O φ I n) F)))

/-- **`F / Iⁿ F` is the universal quotient of `F` killed by the functions `φ(a)`, `a ∈ Iⁿ`**: an
epimorphism out of `F` with that universal property is `adicProj` up to a unique isomorphism. -/
theorem exists_adicQuotient_iso (n : ℕ) {Q : SheafOfModules.{max s t r v} O} (q : F ⟶ Q) [Epi q]
    (hq : ∀ a ∈ I ^ n, globalSmul O (φ a) F ≫ q = 0)
    (hfac : ∀ (T : SheafOfModules.{max s t r v} O) (h : F ⟶ T),
      (∀ a ∈ I ^ n, globalSmul O (φ a) F ≫ h = 0) → ∃ k : Q ⟶ T, q ≫ k = h) :
    ∃ ψ : adicQuotient O φ I F n ≅ Q, adicProj O φ I F n ≫ ψ.hom = q := by
  have h1 : idealSmulHom O (mapIdealPow O φ I n) F ≫ q = 0 := by
    refine Sigma.hom_ext _ _ fun b => ?_
    rw [← Category.assoc, comp_zero]
    show (Sigma.ι _ b ≫ Sigma.desc fun a => globalSmul O a.down.1 F) ≫ q = 0
    rw [Sigma.ι_desc]
    exact globalSmul_comp_eq_zero_of_mem_map O φ q (I ^ n) hq b.down.2
  let k₁ : adicQuotient O φ I F n ⟶ Q := cokernel.desc _ q h1
  have hk₁ : adicProj O φ I F n ≫ k₁ = q := cokernel.π_desc _ _ _
  obtain ⟨k₂, hk₂⟩ := hfac _ (adicProj O φ I F n) fun a ha =>
    globalSmul_comp_cokernelπ O (mapIdealPow O φ I n) F (mem_mapIdealPow O φ I n ha)
  refine ⟨⟨k₁, k₂, ?_, ?_⟩, hk₁⟩
  · refine (cancel_epi (adicProj O φ I F n)).1 ?_
    rw [← Category.assoc, hk₁, hk₂, Category.comp_id]
  · refine (cancel_epi q).1 ?_
    rw [← Category.assoc, hk₂, hk₁, Category.comp_id]

/-! ### Transport along the universe lift of the sections -/

section Lift

attribute [local instance 5000] SheafOfModules.instAbelian

variable [HasSheafify J AddCommGrpCat.{max t r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max t r}]
  [HasSeparator (SheafOfModules.{max t r} O)] [HasInjectiveResolutions (SheafOfModules.{max t r} O)]
  [HasSheafify J AddCommGrpCat.{max s t r v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max s t r v}]
  [HasInjectiveResolutions (SheafOfModules.{max s t r v} O)]

/-- **The bounds of [Stacks, Tag 08AY] pass to the universe lift.**  Let `M` be a sheaf of
`O`-modules with sections in `Type (max t r)`, with a tower of quotients `π n : M ⟶ Q n` whose
lifts are the universal quotients of the lift of `M` killed by the functions `φ(a)`, `a ∈ Iⁿ`, and
let `F` be isomorphic to the lift of `M`.  If clauses (1) and (3) hold for the cohomology of the
tower `Q`, they hold for the tower `n ↦ Hᵖ(C, F / Iⁿ F)`. -/
theorem isAdicCohomologyBound_of_uliftForPresentation (p c : ℕ)
    (M : SheafOfModules.{max t r} O) (Q : ℕ → SheafOfModules.{max t r} O) (π : ∀ n, M ⟶ Q n)
    (tr : ∀ m n : ℕ, m ≤ n → (Q n ⟶ Q m)) (hπtr : ∀ m n h, π n ≫ tr m n h = π m)
    (e : (SheafOfModules.uliftForPresentationFunctor.{s, t, r, max t r, max s t r v}
      (R := O)).obj M ≅ F)
    (hepi : ∀ n, Epi ((SheafOfModules.uliftForPresentationFunctor.{s, t, r, max t r,
      max s t r v} (R := O)).map (π n)))
    (hkill : ∀ n, ∀ a ∈ I ^ n, globalSmul O (φ a)
        ((SheafOfModules.uliftForPresentationFunctor.{s, t, r, max t r, max s t r v}
          (R := O)).obj M) ≫
      (SheafOfModules.uliftForPresentationFunctor.{s, t, r, max t r, max s t r v}
        (R := O)).map (π n) = 0)
    (hfac : ∀ n (T : SheafOfModules.{max s t r v} O)
      (h : (SheafOfModules.uliftForPresentationFunctor.{s, t, r, max t r, max s t r v}
        (R := O)).obj M ⟶ T),
      (∀ a ∈ I ^ n, globalSmul O (φ a)
        ((SheafOfModules.uliftForPresentationFunctor.{s, t, r, max t r, max s t r v}
          (R := O)).obj M) ≫ h = 0) →
      ∃ k, (SheafOfModules.uliftForPresentationFunctor.{s, t, r, max t r, max s t r v}
        (R := O)).map (π n) ≫ k = h)
    (hlow1 : ∀ n, c ≤ n → LinearMap.ker ((ModuleCat.restrictScalars φ).map
        (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).map (π n))).hom ≤
      I ^ (n - c) • (⊤ : Submodule A ((ModuleCat.restrictScalars φ).obj
        (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).obj M))))
    (hlow3 : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range ((ModuleCat.restrictScalars φ).map
          (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).map (tr n k h))).hom =
        LinearMap.range ((ModuleCat.restrictScalars φ).map
          (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).map (π n))).hom) :
    IsAdicCohomologyBound O φ I F p c := by
  let L := SheafOfModules.uliftForPresentationFunctor.{s, t, r, max t r, max s t r v} (R := O)
  have hψ : ∀ n, ∃ ψ : adicQuotient O φ I F n ≅ L.obj (Q n),
      adicProj O φ I F n ≫ ψ.hom = e.inv ≫ L.map (π n) := fun n => by
    have := hepi n
    refine exists_adicQuotient_iso O φ I F n (e.inv ≫ L.map (π n)) ?_ ?_
    · intro a ha
      rw [← Category.assoc, ← comp_globalSmul, Category.assoc, hkill n a ha, comp_zero]
    · intro T h hh
      obtain ⟨k, hk⟩ := hfac n T (e.hom ≫ h) fun a ha => by
        rw [← Category.assoc, ← comp_globalSmul, Category.assoc, hh a ha, comp_zero]
      exact ⟨k, by rw [Category.assoc, hk, Iso.inv_hom_id_assoc]⟩
  choose ψ hψ using hψ
  have hdrop : ∀ m n (h : m ≤ n),
      adicDrop O φ I F h ≫ (ψ m).hom = (ψ n).hom ≫ L.map (tr m n h) := fun m n h => by
    refine (cancel_epi (adicProj O φ I F n)).1 ?_
    rw [adicProj_comp_adicDrop_assoc, hψ, ← Category.assoc, hψ, Category.assoc,
      ← Functor.map_comp, hπtr]
  let nat := rightDerivedGlobalSectionsUliftIso.{v, s, t, r} O p
  let down : ∀ N : SheafOfModules.{max t r} O,
      (ModuleCat.restrictScalars φ).obj ((ModuleCat.uliftFunctor.{max s t r v} _).obj
        (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).obj N)) ≃ₗ[A]
      (ModuleCat.restrictScalars φ).obj
        (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).obj N) := fun N =>
    { toFun := fun y => ULift.down y, invFun := fun y => ULift.up y, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let ε : ∀ N : SheafOfModules.{max t r} O,
      (ModuleCat.restrictScalars φ).obj ((globalModuleCohomology.{s, t, r, v} O p).obj (L.obj N))
        ≃ₗ[A] (ModuleCat.restrictScalars φ).obj
          (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).obj N) := fun N =>
    ((ModuleCat.restrictScalars φ).mapIso (nat.app N).symm).toLinearEquiv.trans (down N)
  have hε : ∀ {N N' : SheafOfModules.{max t r} O} (g : N ⟶ N') (y),
      ε N' (((ModuleCat.restrictScalars φ).map
        ((globalModuleCohomology.{s, t, r, v} O p).map (L.map g))).hom y) =
      ((ModuleCat.restrictScalars φ).map
        (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).map g)).hom (ε N y) :=
    fun g y => congrArg (fun k => ULift.down (k.hom y)) (nat.inv.naturality g)
  let α : cohomologyBase O φ F p ≃ₗ[A] (ModuleCat.restrictScalars φ).obj
      (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).obj M) :=
    ((ModuleCat.restrictScalars φ).mapIso
      ((globalModuleCohomology.{s, t, r, v} O p).mapIso e.symm)).toLinearEquiv.trans (ε M)
  let β : ∀ n, cohomologyAdicTower O φ I F p n ≃ₗ[A] (ModuleCat.restrictScalars φ).obj
      (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).obj (Q n)) := fun n =>
    ((ModuleCat.restrictScalars φ).mapIso
      ((globalModuleCohomology.{s, t, r, v} O p).mapIso (ψ n))).toLinearEquiv.trans (ε (Q n))
  have hmap : ∀ {N₁ N₂ N₃ : SheafOfModules.{max s t r v} O} (g₁ : N₁ ⟶ N₂) (g₂ : N₂ ⟶ N₃) (y),
      (cohomologyResMap O φ p g₂).hom ((cohomologyResMap O φ p g₁).hom y) =
        (cohomologyResMap O φ p (g₁ ≫ g₂)).hom y := by
    intro N₁ N₂ N₃ g₁ g₂ y
    simp only [cohomologyResMap, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hπ' : ∀ n x, β n (cohomologyAdicProj O φ I F p n x) =
      ((ModuleCat.restrictScalars φ).map
        (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).map (π n))).hom (α x) := by
    intro n x
    show ε (Q n) ((cohomologyResMap O φ p (ψ n).hom).hom
      ((cohomologyResMap O φ p (adicProj O φ I F n)).hom x)) = _
    rw [hmap, hψ, ← hmap]
    exact hε (π n) _
  have hT' : ∀ m n (h : m ≤ n) x, β m (cohomologyAdicTowerMap O φ I F p m n h x) =
      ((ModuleCat.restrictScalars φ).map
        (((globalSectionsFunctor.{s, t, r, max t r} O).rightDerived p).map (tr m n h))).hom
        (β n x) := fun m n h x => by
    show ε (Q m) ((cohomologyResMap O φ p (ψ m).hom).hom
      ((cohomologyResMap O φ p (adicDrop O φ I F h)).hom x)) = _
    rw [hmap, hdrop, ← hmap]
    exact hε (tr m n h) _
  exact ⟨ker_le_pow_smul_top_of_linearEquiv I _ _ α β hπ' c hlow1,
    range_eq_of_linearEquiv _ _ _ _ α β hπ' hT' hlow3⟩

end Lift

end SiteAdicCohomology

/-! ### The quotients `M / Iⁿ M` of the module universe of the structure rings, lifted -/

section SpaceLift

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA)

/-- The universe lift of the sections, `Modules.{u, u} ⥤ Modules.{u, max (u + 1) w}`. -/
abbrev moduleLiftFunctor :=
  SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, max (u + 1) w}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)

/-- The universe lift commutes with multiplication by global functions. -/
theorem moduleLiftFunctor_map_globalSmul
    (a : ↥(GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)))
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    (moduleLiftFunctor.{u, w} X).map (globalSmul _ a M) =
      globalSmul _ a ((moduleLiftFunctor.{u, w} X).obj M) := by
  ext U x
  rfl

variable (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (J : Ideal A)

/-- After the universe lift, multiplication by `φ(a)` with `a ∈ J` composed with the lift of the
quotient map `M ⟶ M / J M` is zero. -/
theorem moduleLiftFunctor_globalSmul_comp_idealQuotientπ {a : A} (ha : a ∈ J) :
    globalSmul _ (baseRingHom A B hA X.1 X.2 a) ((moduleLiftFunctor.{u, w} X).obj M) ≫
      (moduleLiftFunctor.{u, w} X).map (idealQuotientπ (baseRingHom A B hA X.1 X.2) M J) = 0 := by
  rw [← moduleLiftFunctor_map_globalSmul, ← Functor.map_comp,
    ← idealMultipleFactor_ι (baseRingHom A B hA X.1 X.2) M J ha, Category.assoc,
    idealMultipleι_idealQuotientπ, comp_zero, Functor.map_zero]

/-- The universe lift of the sections preserves colimits of shapes in `Type u`. -/
theorem preservesColimitsOfSize_moduleLiftFunctor :
    PreservesColimitsOfSize.{u, u} (moduleLiftFunctor.{u, w} X) := by
  have := site_hasSheafify_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).J)
  exact SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor.{u + 1, u, u, u,
    max (u + 1) w}

/-- The universe lift of the sections preserves finite colimits. -/
theorem preservesFiniteColimits_moduleLiftFunctor :
    PreservesFiniteColimits (moduleLiftFunctor.{u, w} X) :=
  have := preservesColimitsOfSize_moduleLiftFunctor.{u, w} X
  PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _

/-- The universe lift of the quotient map `M ⟶ M / J M` is an epimorphism. -/
theorem epi_moduleLiftFunctor_map_idealQuotientπ :
    Epi ((moduleLiftFunctor.{u, w} X).map (idealQuotientπ (baseRingHom A B hA X.1 X.2) M J)) := by
  have := preservesFiniteColimits_moduleLiftFunctor.{u, w} X
  infer_instance

/-- A morphism out of the universe lift of `M` which kills multiplication by the functions `φ(a)`,
`a ∈ J`, factors through the universe lift of the quotient map `M ⟶ M / J M`. -/
theorem exists_moduleLiftFunctor_map_idealQuotientπ_comp
    {T : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X.1 X.2}
    (h : (moduleLiftFunctor.{u, w} X).obj M ⟶ T)
    (hh : ∀ a ∈ J, globalSmul _ (baseRingHom A B hA X.1 X.2 a)
      ((moduleLiftFunctor.{u, w} X).obj M) ≫ h = 0) :
    ∃ k, (moduleLiftFunctor.{u, w} X).map (idealQuotientπ (baseRingHom A B hA X.1 X.2) M J) ≫ k =
      h := by
  let L := moduleLiftFunctor.{u, w} X
  let φ := baseRingHom A B hA X.1 X.2
  have := preservesFiniteColimits_moduleLiftFunctor.{u, w} X
  have := preservesColimitsOfSize_moduleLiftFunctor.{u, w} X
  have h1 : L.map (idealMultipleHom φ M J) ≫ h = 0 := by
    have hc := isColimitOfPreserves L (coproductIsCoproduct fun _ : ↥J => M)
    refine hc.hom_ext fun j => ?_
    rcases j with ⟨a⟩
    show L.map (Sigma.ι (fun _ : ↥J => M) a) ≫ L.map (idealMultipleHom φ M J) ≫ h =
      L.map (Sigma.ι (fun _ : ↥J => M) a) ≫ 0
    rw [← Category.assoc, ← Functor.map_comp, ι_idealMultipleHom, moduleLiftFunctor_map_globalSmul,
      hh a.1 a.2, comp_zero]
  have h2 : L.map (idealMultipleι φ M J) ≫ h = 0 := by
    refine (cancel_epi (L.map (Abelian.factorThruImage (idealMultipleHom φ M J)))).1 ?_
    rw [comp_zero, ← Category.assoc, ← Functor.map_comp]
    exact (congrArg (fun g => L.map g ≫ h) (Abelian.image.fac (idealMultipleHom φ M J))).trans h1
  exact ⟨_, (CokernelCofork.IsColimit.desc' (CokernelCofork.mapIsColimit _
    (cokernelIsCokernel (idealMultipleι φ M J)) L) h (by simpa using h2)).2⟩

/-- **Stacks 08AY, clauses (1) and (3), for a module that is the universe lift of one at the
universe of the structure rings**, transported from the bounds of the latter. -/
theorem isAdicCohomologyBound_of_moduleLift
    (F : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X.1 X.2)
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (e : (moduleLiftFunctor.{u, w} X).obj M ≅ F) (I : Ideal A) (p c : ℕ)
    (h1 : ∀ n : ℕ, c ≤ n → LinearMap.ker (adicCohomologyProj (baseRingHom A B hA X.1 X.2) M I p n) ≤
        I ^ (n - c) • (⊤ : Submodule A (cohomologyRes (baseRingHom A B hA X.1 X.2) p M)))
    (h3 : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
        LinearMap.range (adicCohomologyMap (baseRingHom A B hA X.1 X.2) M I p n k h) =
          LinearMap.range (adicCohomologyProj (baseRingHom A B hA X.1 X.2) M I p n)) :
    SiteAdicCohomology.IsAdicCohomologyBound.{u + 1, u, u, max (u + 1) w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
      (baseRingHom A B hA X.1 X.2) I F p c := by
  have := enoughInjectives_modules B (Spec (.of A)) hA X.1 X.2
  have := hasSeparator_modules_ringUniverse B (Spec (.of A)) hA X.1 X.2
  have := site_hasSheafify_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).J)
  have := moduleSheavesEnoughInjectives.{u + 1, u, u, w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  exact SiteAdicCohomology.isAdicCohomologyBound_of_uliftForPresentation _
    (baseRingHom A B hA X.1 X.2) I F p c M
    (fun n => idealQuotient (baseRingHom A B hA X.1 X.2) M (I ^ n))
    (fun n => idealQuotientπ (baseRingHom A B hA X.1 X.2) M (I ^ n))
    (fun m n h => idealQuotientMap (baseRingHom A B hA X.1 X.2) M (Ideal.pow_le_pow_right h))
    (fun m n h => idealQuotientπ_idealQuotientMap (baseRingHom A B hA X.1 X.2) M
      (Ideal.pow_le_pow_right h)) e
    (fun n => epi_moduleLiftFunctor_map_idealQuotientπ.{u, w} X M (I ^ n))
    (fun n a ha => moduleLiftFunctor_globalSmul_comp_idealQuotientπ.{u, w} X M (I ^ n) ha)
    (fun n T h hh => exists_moduleLiftFunctor_map_idealQuotientπ_comp.{u, w} X M (I ^ n) h hh)
    h1 h3

end SpaceLift

/-! ### Stacks 08AY and 08AZ in Situation 08AV -/

namespace FormalFunctionsSituation

open SiteAdicCohomology

/-- The structure morphism of Situation 08AV is the morphism to the terminal object, so it is
proper in the form [Stacks, Tag 08AX] and the bounds of this file take. -/
theorem isProper_toBase (S : FormalFunctionsSituation.{u, max (u + 1) w}) :
    IsProper S.site (Spec (.of S.ring)) S.containsBase
      ((isTerminal_yoneda_obj_base S.site _ S.containsBase).from S.space.1) := by
  have h : (isTerminal_yoneda_obj_base S.site _ S.containsBase).from S.space.1 =
      S.structureMorphism := (isTerminal_yoneda_obj_base _ _ _).hom_ext _ _
  rw [h]
  exact S.proper

attribute [local instance 5000] SheafOfModules.instAbelian in
/-- **Stacks 08AY**, clauses (1) and (3), in Situation 08AV: the hypothesis `Is08AYBound` of
`AlgebraicGeometry.Space.FormalFunctionsSituation.formalFunctionsEquiv` holds for some `c`.

The bounds are `AlgebraicGeometry.Space.exists_adicCohomology_bounds` for a coherent module with
sections in the universe of the structure rings whose universe lift is the module of the
situation, transported by
`AlgebraicGeometry.Space.SiteAdicCohomology.isAdicCohomologyBound_of_uliftForPresentation`. -/
theorem exists_is08AYBound (S : FormalFunctionsSituation.{u, max (u + 1) w}) (p : ℕ) :
    ∃ c, Is08AYBound S p c := by
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_iso_uliftForPresentation_of_isCoherent.{u, w} S.site
    (Spec (.of S.ring)) S.containsBase S.space.1 S.space.2 S.coefficients
  have := hM
  obtain ⟨c, h1, h3⟩ := exists_adicCohomology_bounds S.space (isProper_toBase S) M S.ideal p
  exact ⟨c, isAdicCohomologyBound_of_moduleLift.{u, w} S.space S.coefficients M e S.ideal p c h1 h3⟩

/-- **Stacks 08AZ** in Situation 08AV, the isomorphism of `A`-modules, unconditionally:
`Hᵖ(X, ℱ)^∧_I ≅ limₙ Hᵖ(X, ℱ / Iⁿ ℱ)`.  It is
`AlgebraicGeometry.Space.FormalFunctionsSituation.formalFunctionsEquiv` with the bounds of
[Stacks, Tag 08AY] supplied by `exists_is08AYBound`.  The claim of the tag that the isomorphism
is a homeomorphism for the limit topologies is not asserted. -/
def formalFunctionsEquivOfIsProper (S : FormalFunctionsSituation.{u, max (u + 1) w}) (p : ℕ) :
    Comparison S p := by
  have e := formalFunctionsEquiv S p _ (exists_is08AYBound S p).choose_spec
  exact e

/-- **The isomorphism of Stacks 08AZ is the one defined by the system of projections**, in
Situation 08AV and unconditionally: its `n`-th component carries the image of a class
`x ∈ Hᵖ(X, ℱ)` to the image of `x` in `Hᵖ(X, ℱ / Iⁿ ℱ)`. -/
theorem formalFunctionsEquivOfIsProper_proj_of (S : FormalFunctionsSituation.{u, max (u + 1) w})
    (p n : ℕ) :
    IsDefinedBy08AZProjections S p _ (exists_is08AYBound S p).choose_spec n := by
  have h := formalFunctionsEquiv_proj_of S p _ (exists_is08AYBound S p).choose_spec n
  exact h

end FormalFunctionsSituation

end AlgebraicGeometry.Space

end
