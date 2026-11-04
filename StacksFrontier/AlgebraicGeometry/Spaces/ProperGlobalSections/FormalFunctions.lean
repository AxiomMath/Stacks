module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.AdicCompletionSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.ArtinReesProper
public import StacksFrontier.Topology.Algebra.AdicLimitTopology

/-!
# The theorem on formal functions in degree zero

Let `X` be an algebraic space over `Spec A`, let `I ⊆ A` be an ideal and let `M` be a module on
`X`. This file constructs the comparison map `Γ(X, M)^∧ ⟶ limₙ Γ(X, M / Iⁿ⁺¹ M)` from the `I`-adic
completion of the global sections to the limit of the global sections of the quotients, proves
that it is natural and additive in `M`, and studies its injectivity and surjectivity.

## Main definitions

* `formalTower`: The tower `n ↦ Γ(X, M / Iⁿ⁺¹ M)`.
* `formalFunctionsMap`: The comparison map `Γ(X, M)^∧ ⟶ limₙ Γ(X, M / Iⁿ⁺¹ M)`.
* `formalTowerLimitMap`: The map induced on the limits of the towers by a morphism of modules.

## Main results

* `injective_formalFunctionsMap`: The comparison map is injective when the global sections
  have the Artin-Rees property.
* `surjective_formalFunctionsMap_of_mono`: For a monomorphism `F ⟶ E` of coherent modules on a
  proper algebraic space over a Noetherian ring, surjectivity for `E` and injectivity for the
  cokernel imply surjectivity for `F`.
* `surjective_formalFunctionsMap_of_sum`: Surjectivity for two summands implies surjectivity for
  their direct sum.
* `surjective_formalFunctionsMap_of_iso`: Surjectivity is invariant under isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.AdicLimit

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)

/-- The `n`-th term `Γ(X, M / (I · 𝒪_X)ⁿ⁺¹ M)` of the tower of the theorem on formal functions. -/
abbrev formalTower (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (n : ℕ) : Type (u + 1) :=
  (sectionsOverBase A B hA X.1 X.2).obj
    (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1) M)

/-- The transition maps of the tower. -/
def formalTowerMap (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (n : ℕ) :
    formalTower A X I M (n + 1) →ₗ[A] formalTower A X I M n :=
  ((sectionsOverBase A B hA X.1 X.2).map
    (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (Nat.le_succ (n + 1)) M)).hom

/-- The projections of `Γ(X, M)` to the terms of the tower. -/
def formalTowerProj (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (n : ℕ) :
    (sectionsOverBase A B hA X.1 X.2).obj M →ₗ[A] formalTower A X I M n :=
  ((sectionsOverBase A B hA X.1 X.2).map
    (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (n + 1) M).ι)).hom

/-- The projections to the tower are compatible with its transition maps. -/
theorem formalTowerMap_comp_proj (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (n : ℕ) :
    (formalTowerMap A X I M n).comp (formalTowerProj A X I M (n + 1)) =
      formalTowerProj A X I M n := by
  rw [formalTowerMap, formalTowerProj, formalTowerProj, ← ModuleCat.hom_comp, ← Functor.map_comp,
    π_comp_idealPowerQuotientMapOfLE]

/-- The kernel of the `n`-th projection `Γ(X, M) ⟶ Γ(X, M / Iⁿ⁺¹ M)` is `sectionsKer` at level
`n + 1`. -/
theorem ker_formalTowerProj (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (n : ℕ) :
    LinearMap.ker (formalTowerProj A X I M n) = sectionsKer A X (baseIdealSheaf A X I) (n + 1) M :=
  rfl

/-- The submodule `Iⁿ⁺¹ Γ(X, M)` lies in the kernel of the `n`-th projection. -/
theorem pow_smul_top_le_ker_formalTowerProj (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (n : ℕ) : I ^ (n + 1) • (⊤ : Submodule A ((sectionsOverBase A B hA X.1 X.2).obj M)) ≤
      LinearMap.ker (formalTowerProj A X I M n) :=
  pow_smul_top_le_sectionsKer A X _ (fun U _ ha => chartBaseRingHom_mem_baseIdealSheaf A X ha U)
    (n + 1) M

/-- The component at `n` of the comparison map. -/
def formalFunctionsComp (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (x : AdicCompletion I ((sectionsOverBase A B hA X.1 X.2).obj M)) (n : ℕ) :
    formalTower A X I M n :=
  (I ^ (n + 1) • ⊤ : Submodule A _).liftQ (formalTowerProj A X I M n)
    (pow_smul_top_le_ker_formalTowerProj A X I M n) (x.val (n + 1))

/-- If the level-`n + 1` component of `x` is the class of `a`, then the `n`-th component of the
comparison map at `x` is the projection of `a`. -/
theorem formalFunctionsComp_mk (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (x : AdicCompletion I ((sectionsOverBase A B hA X.1 X.2).obj M)) (n : ℕ)
    (a : (sectionsOverBase A B hA X.1 X.2).obj M)
    (ha : x.val (n + 1) = Submodule.Quotient.mk a) :
    formalFunctionsComp A X I M x n = formalTowerProj A X I M n a := by
  rw [formalFunctionsComp, ha]
  rfl

/-- The components of the comparison map are compatible with the transition maps of the tower. -/
theorem formalTowerMap_formalFunctionsComp (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (x : AdicCompletion I ((sectionsOverBase A B hA X.1 X.2).obj M)) (n : ℕ) :
    formalTowerMap A X I M n (formalFunctionsComp A X I M x (n + 1)) =
      formalFunctionsComp A X I M x n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1 + 1))
  have ha' : x.val (n + 1) = Submodule.Quotient.mk a := by
    rw [← x.property (Nat.le_succ (n + 1)), ← ha]
    rfl
  rw [formalFunctionsComp_mk A X I M x (n + 1) a ha.symm, formalFunctionsComp_mk A X I M x n a ha',
    ← LinearMap.comp_apply, formalTowerMap_comp_proj]

/-- **The comparison map of the theorem on formal functions in degree zero**,
`Γ(X, M)^∧ ⟶ limₙ Γ(X, M / Iⁿ⁺¹ M)`. -/
def formalFunctionsMap (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    AdicCompletion I ((sectionsOverBase A B hA X.1 X.2).obj M) →ₗ[A]
      towerLimit (formalTower A X I M) (formalTowerMap A X I M) where
  toFun x := ⟨formalFunctionsComp A X I M x, formalTowerMap_formalFunctionsComp A X I M x⟩
  map_add' x y := Subtype.ext (funext fun n => map_add _ (x.val (n + 1)) (y.val (n + 1)))
  map_smul' a x := Subtype.ext (funext fun n => map_smul _ a (x.val (n + 1)))

/-- The `n`-th component of the comparison map is `formalFunctionsComp`. -/
theorem formalFunctionsMap_apply (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (x : AdicCompletion I ((sectionsOverBase A B hA X.1 X.2).obj M)) (n : ℕ) :
    (formalFunctionsMap A X I M x).1 n = formalFunctionsComp A X I M x n :=
  rfl

/-- **Injectivity of the comparison map**, from the Artin-Rees property of the global sections. -/
theorem injective_formalFunctionsMap (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (h : HasSectionsArtinRees A X (baseIdealSheaf A X I) I M) :
    Function.Injective (formalFunctionsMap A X I M) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine AdicCompletion.ext fun m => ?_
  obtain ⟨n, hn⟩ := h m
  have hxn : formalFunctionsComp A X I M x (n + m) = 0 :=
    congrArg (fun y : towerLimit (formalTower A X I M) (formalTowerMap A X I M) => y.1 (n + m)) hx
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + m + 1))
  rw [formalFunctionsComp_mk A X I M x (n + m) a ha.symm] at hxn
  rw [AdicCompletion.val_zero_apply, ← x.property (show m ≤ n + m + 1 by omega), ← ha]
  exact (Submodule.Quotient.mk_eq_zero _).2 (hn (sectionsKer_antitone A X _ (by omega) M hxn))

section Naturality

variable {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : M ⟶ N)

/-- The map induced on the terms of the towers by a morphism of modules. -/
def formalTowerHom (n : ℕ) : formalTower A X I M n →ₗ[A] formalTower A X I N n :=
  ((sectionsOverBase A B hA X.1 X.2).map
    (idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1) g)).hom

/-- The maps induced by a morphism of modules commute with the projections to the towers. -/
theorem formalTowerHom_comp_proj (n : ℕ) :
    (formalTowerHom A X I g n).comp (formalTowerProj A X I M n) =
      (formalTowerProj A X I N n).comp ((sectionsOverBase A B hA X.1 X.2).map g).hom := by
  rw [formalTowerHom, formalTowerProj, formalTowerProj, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
    ← Functor.map_comp, ← Functor.map_comp, π_comp_idealPowerQuotientMapOfHom]

/-- The map `M / I^l M ⟶ N / I^l N` induced by a morphism `M ⟶ N` commutes with the transition
maps `M / I^l M ⟶ M / I^k M` for `k ≤ l`. -/
theorem idealPowerQuotientMapOfHom_comp_mapOfLE {k l : ℕ} (h : k ≤ l) :
    idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) l g ≫
        idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) h N =
      idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) h M ≫
        idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) k g := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2
    (baseIdealSheaf A X I) l M).ι)).1 ?_
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfHom, Category.assoc,
    π_comp_idealPowerQuotientMapOfLE, ← Category.assoc, π_comp_idealPowerQuotientMapOfLE,
    π_comp_idealPowerQuotientMapOfHom]

/-- The maps induced by a morphism of modules commute with the transition maps of the towers. -/
theorem formalTowerMap_comp_hom (n : ℕ) :
    (formalTowerMap A X I N n).comp (formalTowerHom A X I g (n + 1)) =
      (formalTowerHom A X I g n).comp (formalTowerMap A X I M n) := by
  rw [formalTowerMap, formalTowerMap, formalTowerHom, formalTowerHom, ← ModuleCat.hom_comp,
    ← ModuleCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp,
    idealPowerQuotientMapOfHom_comp_mapOfLE]

/-- The map induced on the limits of the towers. -/
def formalTowerLimitMap :
    towerLimit (formalTower A X I M) (formalTowerMap A X I M) →ₗ[A]
      towerLimit (formalTower A X I N) (formalTowerMap A X I N) where
  toFun y := ⟨fun n => formalTowerHom A X I g n (y.1 n), fun n => by
    rw [← LinearMap.comp_apply, formalTowerMap_comp_hom, LinearMap.comp_apply, y.2 n]⟩
  map_add' y z := Subtype.ext (funext fun n => map_add _ (y.1 n) (z.1 n))
  map_smul' a y := Subtype.ext (funext fun n => map_smul _ a (y.1 n))

/-- **Naturality of the comparison map** in the module. -/
theorem formalFunctionsMap_naturality
    (x : AdicCompletion I ((sectionsOverBase A B hA X.1 X.2).obj M)) :
    formalFunctionsMap A X I N
        (AdicCompletion.map I ((sectionsOverBase A B hA X.1 X.2).map g).hom x) =
      formalTowerLimitMap A X I g (formalFunctionsMap A X I M x) := by
  refine Subtype.ext (funext fun n => ?_)
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
  show formalFunctionsComp A X I N _ n =
    formalTowerHom A X I g n (formalFunctionsComp A X I M x n)
  rw [formalFunctionsComp_mk A X I M x n a ha.symm,
    formalFunctionsComp_mk A X I N _ n (((sectionsOverBase A B hA X.1 X.2).map g).hom a) (by
      rw [AdicCompletion.map_val_apply, ← ha]
      rfl),
    ← LinearMap.comp_apply, ← formalTowerHom_comp_proj, LinearMap.comp_apply]

end Naturality

/-- The transition map of the tower between two levels. -/
def formalTowerMapOfLE (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) {m n : ℕ} (h : m ≤ n) :
    formalTower A X I M n →ₗ[A] formalTower A X I M m :=
  ((sectionsOverBase A B hA X.1 X.2).map
    (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (Nat.succ_le_succ h) M)).hom

/-- The transition map from level `n` to level `m` carries the `n`-th component of a point of the
limit of the tower to its `m`-th component. -/
theorem formalTowerMapOfLE_apply_towerLimit (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (y : towerLimit (formalTower A X I M) (formalTowerMap A X I M)) {m n : ℕ} (h : m ≤ n) :
    formalTowerMapOfLE A X I M h (y.1 n) = y.1 m := by
  induction n, h using Nat.le_induction with
  | base =>
    show ((sectionsOverBase A B hA X.1 X.2).map (idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1
      X.2 (baseIdealSheaf A X I) le_rfl M)).hom (y.1 m) = y.1 m
    rw [idealPowerQuotientMapOfLE_refl, CategoryTheory.Functor.map_id]
    rfl
  | succ k hk ih =>
    rw [← ih, ← y.2 k]
    show ((sectionsOverBase A B hA X.1 X.2).map _).hom (y.1 (k + 1)) =
      ((sectionsOverBase A B hA X.1 X.2).map _ ≫ (sectionsOverBase A B hA X.1 X.2).map _).hom
        (y.1 (k + 1))
    rw [← Functor.map_comp, idealPowerQuotientMapOfLE_comp]

attribute [local instance 5000] SheafOfModules.instAbelian in
/-- **Artin-Rees along a monomorphism, on the terms of the towers** ([Stacks, Tag 07UL]): a global
section of `F / Iⁿ⁺ᶜ⁺¹ F` whose image in `E / Iⁿ⁺ᶜ⁺¹ E` vanishes already vanishes in
`F / Iⁿ⁺¹ F`. -/
theorem exists_formalTowerMapOfLE_eq_zero_of_mono
    (hN : IsNoetherian B (Spec (.of A)) hA B.contains_terminal X.1)
    {F E : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hF : IsCoherent B (Spec (.of A)) hA X.1 X.2 F) (hE : IsCoherent B (Spec (.of A)) hA X.1 X.2 E)
    (f : F ⟶ E) [Mono f] :
    ∃ c : ℕ, ∀ (n : ℕ) (z : formalTower A X I F (n + c)), formalTowerHom A X I f (n + c) z = 0 →
      formalTowerMapOfLE A X I F (Nat.le_add_right n c) z = 0 := by
  have : Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  have hI := isQuasicoherentOnSite_baseIdealSheaf A X I
  let F' : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 := ⟨F, hF⟩
  let E' : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 := ⟨E, hE⟩
  let f' : F' ⟶ E' := ObjectProperty.homMk f
  have : Mono f' := (ObjectProperty.ι _).mono_of_mono_map (by exact (inferInstance : Mono f))
  obtain ⟨c, hc⟩ := exists_comp_completionTermProjection_eq_zero_of_mono B (Spec (.of A)) hA X.1
    X.2 (baseIdealSheaf A X I) hI B.contains_terminal hN f'
  refine ⟨c, fun n z hz => ?_⟩
  let z' : (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
    (n + c + 1) F).sections := z
  let α := (SheafOfModules.unitHomEquiv _).symm z'
  have hα : α ≫ ((completionFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) hI).map
      f').hom.app (op (n + c)) = 0 := by
    show α ≫ idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I)
      (n + c + 1) f = 0
    rw [SheafOfModules.unitHomEquiv_symm_comp]
    exact (Equiv.symm_apply_eq _).2 hz
  have key := comp_eq_zero_of_epi_of_comp_eq_zero
    (completionTermProjection B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) hI F' (n + c))
    (((completionFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) hI).map f').hom.app
      (op (n + c)))
    (((completionFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) hI).obj F').obj.map
      (homOfLE (Nat.le_add_right n c)).op) α hα (fun W t ht => by
        rw [Category.assoc, completionTermProjection_naturality] at ht
        rw [Category.assoc, completionTermProjection_transition]
        exact hc n t ht)
  have e := SheafOfModules.unitHomEquiv_comp_apply α
    (((completionFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) hI).obj F').obj.map
      (homOfLE (Nat.le_add_right n c)).op)
  have hz' : (SheafOfModules.unitHomEquiv _) α = z' := Equiv.apply_symm_apply _ _
  rw [hz'] at e
  exact e.symm.trans ((congrArg (SheafOfModules.unitHomEquiv _) key).trans rfl)

section Functoriality

/-- A point of the limit of the towers of `N` is the image of `y` if this holds termwise. -/
private theorem formalTowerLimitMap_eq_of_forall {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (g : M ⟶ N) {y : towerLimit (formalTower A X I M) (formalTowerMap A X I M)}
    {z : towerLimit (formalTower A X I N) (formalTowerMap A X I N)}
    (h : ∀ n, formalTowerHom A X I g n (y.1 n) = z.1 n) : formalTowerLimitMap A X I g y = z :=
  Subtype.ext (funext h)

/-- The maps induced on the towers respect composition of morphisms. -/
theorem formalTowerHom_comp {M N P : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : M ⟶ N)
    (h : N ⟶ P) (n : ℕ) :
    formalTowerHom A X I (g ≫ h) n =
      (formalTowerHom A X I h n).comp (formalTowerHom A X I g n) := by
  rw [formalTowerHom, formalTowerHom, formalTowerHom, idealPowerQuotientMapOfHom_comp,
    Functor.map_comp, ModuleCat.hom_comp]

/-- The maps induced on the limits of the towers respect composition of morphisms. -/
theorem formalTowerLimitMap_comp {M N P : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : M ⟶ N)
    (h : N ⟶ P) (y : towerLimit (formalTower A X I M) (formalTowerMap A X I M)) :
    formalTowerLimitMap A X I (g ≫ h) y =
      formalTowerLimitMap A X I h (formalTowerLimitMap A X I g y) :=
  formalTowerLimitMap_eq_of_forall A X I _ fun n => by rw [formalTowerHom_comp]; rfl

/-- The zero morphism induces the zero map on the terms of the towers. -/
theorem formalTowerHom_zero {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (n : ℕ) :
    formalTowerHom A X I (0 : M ⟶ N) n = 0 := by
  have h : idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSheaf A X I) (n + 1)
      (0 : M ⟶ N) = 0 := by
    refine (cancel_epi (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2
      (baseIdealSheaf A X I) (n + 1) M).ι)).1 ?_
    rw [π_comp_idealPowerQuotientMapOfHom, Limits.zero_comp, Limits.comp_zero]
  rw [formalTowerHom, h, Functor.map_zero]
  rfl

/-- The zero morphism induces the zero map on the limits of the towers. -/
theorem formalTowerLimitMap_zero {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (y : towerLimit (formalTower A X I M) (formalTowerMap A X I M)) :
    formalTowerLimitMap A X I (0 : M ⟶ N) y = 0 :=
  formalTowerLimitMap_eq_of_forall A X I _ fun n => by rw [formalTowerHom_zero]; rfl

end Functoriality

attribute [local instance 5000] SheafOfModules.instAbelian in
/-- Global sections over the base carry a monomorphism followed by its cokernel to a left exact
sequence of `A`-modules. -/
theorem exact_sectionsOverBase_map_cokernel_π {F E : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (f : F ⟶ E) [Mono f] :
    Function.Exact ((sectionsOverBase A B hA X.1 X.2).map f).hom
      ((sectionsOverBase A B hA X.1 X.2).map (cokernel.π f)).hom := by
  have h := (ShortComplex.exact_cokernel f).map_of_mono_of_preservesKernel
    (sectionsOverBase A B hA X.1 X.2) (inferInstanceAs (Mono f)) inferInstance
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact LinearMap.exact_iff.2 h.symm

/-- Global sections over the base carry a monomorphism to an injective linear map. -/
theorem injective_sectionsOverBase_map_of_mono {F E : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (f : F ⟶ E) [Mono f] : Function.Injective ((sectionsOverBase A B hA X.1 X.2).map f).hom :=
  (ModuleCat.mono_iff_injective _).1 (Functor.map_mono _ f)

attribute [local instance 5000] SheafOfModules.instAbelian in
/-- **Surjectivity of the comparison map along a monomorphism.** Let `f : F ⟶ E` be a monomorphism
of coherent modules on a proper algebraic space over a Noetherian ring. If the comparison map of
`E` is surjective and that of the cokernel of `f` is injective, then the comparison map of `F` is
surjective. -/
theorem surjective_formalFunctionsMap_of_mono [IsNoetherianRing A]
    (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
    {F E : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (hF : IsCoherent B (Spec (.of A)) hA X.1 X.2 F) (hE : IsCoherent B (Spec (.of A)) hA X.1 X.2 E)
    (f : F ⟶ E) [Mono f] (hsurj : Function.Surjective (formalFunctionsMap A X I E))
    (hinj : Function.Injective (formalFunctionsMap A X I (cokernel f))) :
    Function.Surjective (formalFunctionsMap A X I F) := by
  have hN := isNoetherian_of_isProper_toBase A X hX
  have hQ := isCoherent_cokernel B (Spec (.of A)) hA X.1 X.2 hF hE f
  have := moduleFinite_sectionsOverBase_of_isProper A X hX E hE
  have := moduleFinite_sectionsOverBase_of_isProper A X hX _ hQ
  intro y
  obtain ⟨d, hd⟩ := hsurj (formalTowerLimitMap A X I f y)
  have hd0 : AdicCompletion.map I ((sectionsOverBase A B hA X.1 X.2).map (cokernel.π f)).hom d =
      0 := by
    refine hinj ?_
    rw [formalFunctionsMap_naturality, hd, ← formalTowerLimitMap_comp, cokernel.condition,
      formalTowerLimitMap_zero, map_zero]
  obtain ⟨r, hr⟩ := ((AdicCompletion.map_exact_of_finite_of_injective I
    (injective_sectionsOverBase_map_of_mono A X f)
    (exact_sectionsOverBase_map_cokernel_π A X f)) d).1 hd0
  refine ⟨r, ?_⟩
  obtain ⟨c, hc⟩ := exists_formalTowerMapOfLE_eq_zero_of_mono A X I hN hF hE f
  have hw : formalTowerLimitMap A X I f (formalFunctionsMap A X I F r - y) = 0 := by
    rw [map_sub, ← formalFunctionsMap_naturality, hr, hd, sub_self]
  rw [← sub_eq_zero]
  refine Subtype.ext (funext fun n => ?_)
  have hz : formalTowerHom A X I f (n + c) ((formalFunctionsMap A X I F r - y).1 (n + c)) = 0 :=
    congrArg (fun z : towerLimit (formalTower A X I E) (formalTowerMap A X I E) => z.1 (n + c)) hw
  have := hc n _ hz
  rw [formalTowerMapOfLE_apply_towerLimit] at this
  exact this

section Biproducts

/-- The functor of global sections over the base is additive. -/
instance : (sectionsOverBase A B hA X.1 X.2).Additive :=
  ⟨fun {_ _ _ _} => by ext; rfl⟩

/-- The identity morphism induces the identity on the terms of the tower. -/
theorem formalTowerHom_id (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (n : ℕ) :
    formalTowerHom A X I (𝟙 M) n = LinearMap.id := by
  rw [formalTowerHom, idealPowerQuotientMapOfHom_id, CategoryTheory.Functor.map_id]
  rfl

/-- The maps induced on the towers are additive in the morphism. -/
theorem formalTowerHom_add {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g h : M ⟶ N)
    (n : ℕ) :
    formalTowerHom A X I (g + h) n = formalTowerHom A X I g n + formalTowerHom A X I h n := by
  rw [formalTowerHom, formalTowerHom, formalTowerHom, idealPowerQuotientMapOfHom_add,
    Functor.map_add]
  rfl

/-- The identity morphism induces the identity on the limit of the tower. -/
theorem formalTowerLimitMap_id (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (y : towerLimit (formalTower A X I M) (formalTowerMap A X I M)) :
    formalTowerLimitMap A X I (𝟙 M) y = y :=
  formalTowerLimitMap_eq_of_forall A X I _ fun n => by rw [formalTowerHom_id]; rfl

/-- The maps induced on the limits of the towers are additive in the morphism. -/
theorem formalTowerLimitMap_add {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g h : M ⟶ N)
    (y : towerLimit (formalTower A X I M) (formalTowerMap A X I M)) :
    formalTowerLimitMap A X I (g + h) y =
      formalTowerLimitMap A X I g y + formalTowerLimitMap A X I h y :=
  formalTowerLimitMap_eq_of_forall A X I _ fun n => by rw [formalTowerHom_add]; rfl

/-- **Surjectivity of the comparison map for a direct sum**, presented by its two projections and
two inclusions. -/
theorem surjective_formalFunctionsMap_of_sum {E₁ E₂ E : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (i₁ : E₁ ⟶ E) (i₂ : E₂ ⟶ E) (p₁ : E ⟶ E₁) (p₂ : E ⟶ E₂) (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 E)
    (h₁ : Function.Surjective (formalFunctionsMap A X I E₁))
    (h₂ : Function.Surjective (formalFunctionsMap A X I E₂)) :
    Function.Surjective (formalFunctionsMap A X I E) := by
  intro y
  obtain ⟨x₁, hx₁⟩ := h₁ (formalTowerLimitMap A X I p₁ y)
  obtain ⟨x₂, hx₂⟩ := h₂ (formalTowerLimitMap A X I p₂ y)
  refine ⟨AdicCompletion.map I ((sectionsOverBase A B hA X.1 X.2).map i₁).hom x₁ +
    AdicCompletion.map I ((sectionsOverBase A B hA X.1 X.2).map i₂).hom x₂, ?_⟩
  rw [map_add, formalFunctionsMap_naturality, formalFunctionsMap_naturality, hx₁, hx₂,
    ← formalTowerLimitMap_comp, ← formalTowerLimitMap_comp, ← formalTowerLimitMap_add,
    htot, formalTowerLimitMap_id]

/-- **Surjectivity of the comparison map is invariant under isomorphism.** -/
theorem surjective_formalFunctionsMap_of_iso {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (e : M ≅ N) (h : Function.Surjective (formalFunctionsMap A X I M)) :
    Function.Surjective (formalFunctionsMap A X I N) := by
  intro y
  obtain ⟨x, hx⟩ := h (formalTowerLimitMap A X I e.inv y)
  refine ⟨AdicCompletion.map I ((sectionsOverBase A B hA X.1 X.2).map e.hom).hom x, ?_⟩
  rw [formalFunctionsMap_naturality, hx, ← formalTowerLimitMap_comp, e.inv_hom_id,
    formalTowerLimitMap_id]

end Biproducts

end AlgebraicGeometry.Space
