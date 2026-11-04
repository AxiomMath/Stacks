module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.BaseIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModuleCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ImageSubsheafUniversal

/-!
# The adic system of quotients by a tower of ideals

Let `X` be an algebraic space over `Spec A` and `I ⊆ A` an ideal. The `k`-th power of the sheaf
of ideals `I 𝒪_X` acting on `𝒪_X` is `I^k 𝒪_X`
(`AlgebraicGeometry.Space.idealPowerMultiple_baseIdealSubmodule`). Consequently a decreasing
family of quasi-coherent sheaves of ideals `𝒥_n ⊆ 𝒪_X` with `𝒥_n = 𝒥_{n+1} + I^{n+1} 𝒪_X` gives
a coherent `I 𝒪_X`-adic system `(𝒪_X / 𝒥_n)_n` on a locally Noetherian `X`
(`AlgebraicGeometry.Space.isCoherentAdicSystem_structureQuotientTower`): this is the system of
structure sheaves of a compatible tower of closed subspaces cut out from the adic fibres of `X`,
the input of the algebraization of closed subspaces, Stacks 08BG.

## Main definitions

* `AlgebraicGeometry.Space.structureQuotientTower`: the inverse system `(𝒪_X / 𝒥_n)_n`.

## Main results

* `AlgebraicGeometry.Space.cokernel_π_app_eq_zero_iff_mem_imageSubmodule`: a section dies in the
  cokernel of a morphism exactly when it lies in its image subsheaf.
* `AlgebraicGeometry.Space.idealPowerMultiple_baseIdealSubmodule`: `(I 𝒪_X)^k 𝒪_X = I^k 𝒪_X`.
* `AlgebraicGeometry.Space.isCoherentAdicSystem_structureQuotientTower`: the quotients form a
  coherent adic system.

## References

* [Stacks Project, Tag 08BG](https://stacks.math.columbia.edu/tag/08BG)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A section dies in the cokernel of a morphism exactly when it lies in the image subsheaf.** -/
theorem cokernel_π_app_eq_zero_iff_mem_imageSubmodule {M N : Modules.{u, u} B S hS F hF}
    (f : M ⟶ N) (U : (SmallEtale B S hS F)ᵒᵖ) (x : N.val.obj U) :
    (cokernel.π f).val.app U x = 0 ↔
      x ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule f).obj U := by
  set P := Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule f
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hf : f ≫ cokernel.π P.ι = 0 := by
      rw [← Stacks.SheafOfModules.ImageSubsheaf.toImage_ι f, Category.assoc, cokernel.condition,
        comp_zero]
    refine (cokernel_π_app_eq_zero_iff B S hS F hF P U x).1 ?_
    rw [← cokernel.π_desc f (cokernel.π P.ι) hf]
    show (cokernel.desc f (cokernel.π P.ι) hf).val.app U ((cokernel.π f).val.app U x) = 0
    rw [hx, map_zero]
  · have hle : P ≤ SheafOfModules.Submodule.ker (cokernel.π f) :=
      Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_le _ fun V m =>
        (SheafOfModules.Submodule.mem_ker _ V _).2 (by
          show (f ≫ cokernel.π f).val.app V m = 0
          rw [cokernel.condition]
          rfl)
    exact hle U hx

section BaseIdeal

variable {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B _ hA X}

/-- **`(I 𝒪_X)^k 𝒪_X = I^k 𝒪_X`.** Both are the kernel of the projection of `𝒪_X` onto
`𝒪_X / I^k 𝒪_X`, the two quotients being identified by
`AlgebraicGeometry.Space.C1573.baseIdealQuotientIso`. -/
theorem idealPowerMultiple_baseIdealSubmodule (I : Ideal A) (k : ℕ) :
    idealPowerMultiple B _ hA X hX (C1573.baseIdealSubmodule X hX I) k (SheafOfModules.unit _) =
      C1573.baseIdealSubmodule X hX (I ^ k) := by
  set O := SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B _ hA X hX).O)
  set Q := idealPowerSubsheaf B _ hA X hX (C1573.baseIdealSubmodule X hX I) k O
  set e := C1573.baseIdealQuotientIso O I k (X := X) (hX := hX)
  have h : cokernel.π Q.ι ≫ e.hom = idealQuotientπ (baseRingHom A B hA X hX) O (I ^ k) :=
    C1573.smallEtaleAdicQuotientProjection_baseIdealQuotientIso_hom O I k
  rw [← idealPowerSubsheaf_eq_idealPowerMultiple]
  refine le_antisymm (fun U x hx => ?_) (fun U x hx => ?_)
  · have h2 : (idealQuotientπ (baseRingHom A B hA X hX) O (I ^ k)).val.app U x = 0 := by
      rw [← h]
      show e.hom.val.app U ((cokernel.π Q.ι).val.app U x) = 0
      rw [(cokernel_π_app_eq_zero_iff B _ hA X hX Q U x).2 hx, map_zero]
    exact (cokernel_π_app_eq_zero_iff_mem_imageSubmodule _ U x).1 h2
  · have h3 : cokernel.π Q.ι = idealQuotientπ (baseRingHom A B hA X hX) O (I ^ k) ≫ e.inv := by
      rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have h2 : (cokernel.π Q.ι).val.app U x = 0 := by
      rw [h3]
      show e.inv.val.app U ((idealQuotientπ (baseRingHom A B hA X hX) O (I ^ k)).val.app U x) = 0
      rw [(cokernel_π_app_eq_zero_iff_mem_imageSubmodule _ U x).2 hx, map_zero]
    exact (cokernel_π_app_eq_zero_iff B _ hA X hX Q U x).1 h2

/-- A submodule whose inclusion vanishes is zero. -/
theorem eq_bot_of_ι_eq_zero {M : Modules.{u, u} B _ hA X hX} (P : M.Submodule) (h : P.ι = 0) :
    P = ⊥ := by
  refine le_antisymm (fun U x hx => ?_) bot_le
  have hx0 : x = 0 := congrArg (fun k => k.val.app U ⟨x, hx⟩) h
  rw [hx0]
  exact Submodule.zero_mem _

/-- `I^{n+1} 𝒪_X` dies in `𝒪_X / 𝒥_n` when `𝒥_n = 𝒥_{n+1} + I^{n+1} 𝒪_X`. -/
private theorem idealPowerMultiple_ι_comp_cokernel_π_eq_zero (I : Ideal A)
    (𝒥 : ℕ → (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B _ hA X hX).O)).Submodule)
    (h : ∀ n, 𝒥 n = 𝒥 (n + 1) ⊔ C1573.baseIdealSubmodule X hX (I ^ (n + 1))) (n : ℕ) :
    (idealPowerMultiple B _ hA X hX (C1573.baseIdealSubmodule X hX I) (n + 1)
      (SheafOfModules.unit _)).ι ≫ cokernel.π (𝒥 n).ι = 0 := by
  have hle : idealPowerMultiple B _ hA X hX (C1573.baseIdealSubmodule X hX I) (n + 1)
      (SheafOfModules.unit _) ≤ 𝒥 n := by
    rw [idealPowerMultiple_baseIdealSubmodule, h n]
    exact le_sup_right
  ext U x
  exact (cokernel_π_app_eq_zero_iff B _ hA X hX (𝒥 n) U x.1).2 (hle U x.2)

section Tower

variable (I : Ideal A)
  (𝒥 : ℕ → (SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B _ hA X hX).O)).Submodule)
  (h𝒥 : ∀ n, 𝒥 (n + 1) ≤ 𝒥 n)

/-- The projection `𝒪_X / 𝒥_{n+1} ⟶ 𝒪_X / 𝒥_n`. -/
def structureQuotientTowerTransition (n : ℕ) : cokernel (𝒥 (n + 1)).ι ⟶ cokernel (𝒥 n).ι :=
  cokernel.desc _ (cokernel.π (𝒥 n).ι) (by
    ext U x
    exact (cokernel_π_app_eq_zero_iff B _ hA X hX (𝒥 n) U x.1).2 (h𝒥 n U x.2))

/-- The projection `𝒪_X ⟶ 𝒪_X / 𝒥_{n+1}` followed by the transition map to `𝒪_X / 𝒥_n` is the
projection `𝒪_X ⟶ 𝒪_X / 𝒥_n`. -/
@[reassoc (attr := simp)]
theorem π_structureQuotientTowerTransition (n : ℕ) :
    cokernel.π (𝒥 (n + 1)).ι ≫ structureQuotientTowerTransition 𝒥 h𝒥 n = cokernel.π (𝒥 n).ι :=
  cokernel.π_desc _ _ _

/-- **The inverse system `(𝒪_X / 𝒥_n)_n`.** -/
def structureQuotientTower : ℕᵒᵖ ⥤ Modules.{u, u} B _ hA X hX :=
  Functor.ofOpSequence (X := fun n => cokernel (𝒥 n).ι) (structureQuotientTowerTransition 𝒥 h𝒥)

/-- The `n`-th term of the inverse system `(𝒪_X / 𝒥_n)_n` is `𝒪_X / 𝒥_n`. -/
theorem structureQuotientTower_obj (n : ℕ) :
    (structureQuotientTower 𝒥 h𝒥).obj (op n) = cokernel (𝒥 n).ι := rfl

/-- The map from the `(n+1)`-st to the `n`-th term of the inverse system `(𝒪_X / 𝒥_n)_n` is the
projection `𝒪_X / 𝒥_{n+1} ⟶ 𝒪_X / 𝒥_n`. -/
@[simp]
theorem structureQuotientTower_map_succ (n : ℕ) :
    (structureQuotientTower 𝒥 h𝒥).map (homOfLE (Nat.le_add_right n 1)).op =
      structureQuotientTowerTransition 𝒥 h𝒥 n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The quotient of `𝒪_X / 𝒥_{n+1}` by `I^{n+1}` is `𝒪_X / 𝒥_n` when
`𝒥_n = 𝒥_{n+1} + I^{n+1} 𝒪_X`, through the transition map. -/
theorem exists_iso_idealPowerQuotient_idealQuotient
    (h : ∀ n, 𝒥 n = 𝒥 (n + 1) ⊔ C1573.baseIdealSubmodule X hX (I ^ (n + 1))) (n : ℕ) :
    ∃ e : idealPowerQuotient B _ hA X hX (C1573.baseIdealSubmodule X hX I) (n + 1)
        (cokernel (𝒥 (n + 1)).ι) ≅ cokernel (𝒥 n).ι,
      cokernel.π (idealPowerMultiple B _ hA X hX (C1573.baseIdealSubmodule X hX I) (n + 1)
          (cokernel (𝒥 (n + 1)).ι)).ι ≫ e.hom =
        structureQuotientTowerTransition 𝒥 (fun n => (h n).symm ▸ le_sup_left) n := by
  have h𝒥 : ∀ n, 𝒥 (n + 1) ≤ 𝒥 n := fun n => (h n).symm ▸ le_sup_left
  have hk := idealPowerMultiple_ι_comp_cokernel_π_eq_zero I 𝒥 h
  set t := structureQuotientTowerTransition 𝒥 h𝒥 n
  set ρ := cokernel.π (idealPowerMultiple B _ hA X hX (C1573.baseIdealSubmodule X hX I) (n + 1)
    (cokernel (𝒥 (n + 1)).ι)).ι
  have ht : (idealPowerMultiple B _ hA X hX (C1573.baseIdealSubmodule X hX I) (n + 1)
      (cokernel (𝒥 (n + 1)).ι)).ι ≫ t = 0 :=
    idealPowerMultiple_ι_comp_eq_zero_of_epi B _ hA X hX (C1573.baseIdealSubmodule X hX I) (n + 1)
      (cokernel.π (𝒥 (n + 1)).ι) t (by rw [π_structureQuotientTowerTransition]; exact hk n)
  have hK : 𝒥 n ≤ SheafOfModules.Submodule.ker (cokernel.π (𝒥 (n + 1)).ι ≫ ρ) := by
    rw [h n]
    refine sup_le (fun U x hx => ?_) ?_
    · show ρ.val.app U ((cokernel.π (𝒥 (n + 1)).ι).val.app U x) = 0
      rw [(cokernel_π_app_eq_zero_iff B _ hA X hX (𝒥 (n + 1)) U x).2 hx, map_zero]
    · rw [← idealPowerMultiple_baseIdealSubmodule]
      intro U x hx
      have := idealPowerMultiple_ι_comp_comp_eq_zero B _ hA X hX (C1573.baseIdealSubmodule X hX I)
        (n + 1) (cokernel.π (𝒥 (n + 1)).ι) ρ (cokernel.condition _)
      exact congrArg (fun k => k.val.app U ⟨x, hx⟩) this
  have hinv : (𝒥 n).ι ≫ cokernel.π (𝒥 (n + 1)).ι ≫ ρ = 0 := by
    ext U x
    exact hK U x.2
  refine ⟨{ hom := cokernel.desc _ t ht
            inv := cokernel.desc _ (cokernel.π (𝒥 (n + 1)).ι ≫ ρ) hinv
            hom_inv_id := ?_
            inv_hom_id := ?_ }, cokernel.π_desc _ _ _⟩
  · refine (cancel_epi ρ).1 ?_
    refine (cancel_epi (cokernel.π (𝒥 (n + 1)).ι)).1 ?_
    rw [Category.comp_id, cokernel.π_desc_assoc, π_structureQuotientTowerTransition_assoc,
      cokernel.π_desc]
  · refine (cancel_epi (cokernel.π (𝒥 n).ι)).1 ?_
    rw [Category.comp_id, cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc,
      π_structureQuotientTowerTransition]

/-- **The quotients by a tower of ideals with `𝒥_n = 𝒥_{n+1} + I^{n+1} 𝒪_X` form a coherent
`I 𝒪_X`-adic system.** -/
theorem isCoherentAdicSystem_structureQuotientTower
    [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X
      (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hq : ∀ n, (𝒥 n).toSheafOfModules.IsQuasicoherentOnSite)
    (h : ∀ n, 𝒥 n = 𝒥 (n + 1) ⊔ C1573.baseIdealSubmodule X hX (I ^ (n + 1))) :
    IsCoherentAdicSystem B _ hA X hX (C1573.baseIdealSubmodule X hX I)
      (structureQuotientTower 𝒥 (fun n => (h n).symm ▸ le_sup_left)) := by
  -- `I^{n+1} 𝒪_X` dies in `𝒪_X / 𝒥_n`
  have hk := idealPowerMultiple_ι_comp_cokernel_π_eq_zero I 𝒥 h
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact isCoherent_cokernel B _ hA X hX
      (isCoherent_idealSheaf B _ hA X hX (𝒥 n) (hq n)) (isCoherent_structureSheaf B _ hA X hX) _
  · refine eq_bot_of_ι_eq_zero _ ?_
    have := idealPowerMultiple_ι_comp_eq_zero_of_epi B _ hA X hX (C1573.baseIdealSubmodule X hX I)
      (n + 1) (cokernel.π (𝒥 n).ι) (𝟙 _) (by rw [Category.comp_id]; exact hk n)
    rwa [Category.comp_id] at this
  · obtain ⟨e, he⟩ := exists_iso_idealPowerQuotient_idealQuotient I 𝒥 h n
    refine ⟨e, ?_⟩
    rw [structureQuotientTower_map_succ]
    exact he

end Tower

end BaseIdeal

end AlgebraicGeometry.Space

end
