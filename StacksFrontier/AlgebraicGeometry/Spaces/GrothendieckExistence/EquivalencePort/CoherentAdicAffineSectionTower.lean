module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit

/-!
# The tower of sections of a coherent adic system over an affine chart

Let `(E_n)` be a coherent `𝓘`-adic system on an algebraic space whose étale charts are locally
Noetherian, with `𝓘` quasi-coherent, and let `V` be an affine étale chart. The sections `E_n(V)`
form a tower of finite `𝒪(V)`-modules in which each transition map `E_(n+1)(V) ⟶ E_n(V)` is
surjective with kernel `𝓘(V)^(n+1) E_(n+1)(V)`.

The tower is indexed as `Stacks.AdicCompletion.InverseLimit.InverseSystem` requires: the zero
module in degree `0` and `E_k(V)` in degree `k + 1`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.adicSectionTower`: the shifted tower of sections over `V`.
* `AlgebraicGeometry.Space.C1573.adicSectionTransition`: the transition maps of that tower.
* `AlgebraicGeometry.Space.C1573.adicSectionInverseSystem`: over an affine chart, the tower as an
  inverse system for the ideal `𝓘(V)`.

## Main results

* `AlgebraicGeometry.Space.C1573.surjective_and_ker_transition_of_isCoherentAdicSystem`: over an
  affine chart, `E_(k+1)(V) ⟶ E_k(V)` is surjective with kernel `𝓘(V)^(k+1) E_(k+1)(V)`.
-/

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The tower of sections of a coherent adic system over an affine chart

Let `(E_n)` be a coherent `𝓘`-adic system on an algebraic space whose étale charts are locally
Noetherian, with `𝓘` quasi-coherent, and let `V` be an affine étale chart.  The sections
`E_n(V)` form a tower of finite `𝒪(V)`-modules in which `E_(n+1)(V) ⟶ E_n(V)` is surjective with
kernel `𝓘(V)^(n+1) E_(n+1)(V)`: the transition map is the projection onto
`E_(n+1) / 𝓘^(n+1) E_(n+1) ≅ E_n`, and over an affine chart that projection is surjective on
sections with kernel `𝓘(V)^(n+1) · E_(n+1)(V)`.  So the inverse limit `N = lim_n E_n(V)` has
surjective projections onto the `E_n(V)` with kernels `𝓘(V)^(n+1) N` (Stacks 09B8), the
space-level form of the affine description of Stacks 087W.

The tower is indexed as `Stacks.AdicCompletion.InverseLimit.InverseSystem` requires: the zero
module in degree `0` and `E_k(V)` in degree `k + 1`
(`AlgebraicGeometry.Space.C1573.adicSectionTower`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) (V : (smallEtaleRingedSite B S hS F hF).C)

/-- The tower of sections of an inverse system over a chart, shifted by one: the zero module in
degree `0` and `E_k(V)` in degree `k + 1`. -/
def C1573.adicSectionTower (k : ℕ) : Type u :=
  Nat.rec (Fin 0 → chartRing B S hS F hF V) (fun k _ ↦ (E.obj (op k)).val.obj (op V)) k

/-- The additive group structure on each module of the shifted tower of sections. -/
instance C1573.adicSectionTowerAddCommGroup (k : ℕ) :
    AddCommGroup (adicSectionTower B S hS F hF E V k) := by
  cases k with
  | zero => exact inferInstanceAs (AddCommGroup (Fin 0 → chartRing B S hS F hF V))
  | succ k => exact inferInstanceAs (AddCommGroup ((E.obj (op k)).val.obj (op V)))

/-- The `𝒪(V)`-module structure on each module of the shifted tower of sections. -/
instance C1573.adicSectionTowerModule (k : ℕ) :
    Module (chartRing B S hS F hF V) (adicSectionTower B S hS F hF E V k) := by
  cases k with
  | zero => exact inferInstanceAs (Module _ (Fin 0 → chartRing B S hS F hF V))
  | succ k => exact inferInstanceAs (Module _ ((E.obj (op k)).val.obj (op V)))

/-- The transition maps of the shifted tower of sections. -/
def C1573.adicSectionTransition (k : ℕ) :
    adicSectionTower B S hS F hF E V (k + 1) →ₗ[chartRing B S hS F hF V]
      adicSectionTower B S hS F hF E V k :=
  match k with
  | 0 => 0
  | k + 1 => ((E.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V)).hom

variable {B S hS F hF 𝓘 E} in
/-- Over an affine chart `V`, the transition map `E_(k+1)(V) ⟶ E_k(V)` of a coherent adic system is
surjective with kernel `𝓘(V)^(k+1) E_(k+1)(V)`. -/
theorem C1573.surjective_and_ker_transition_of_isCoherentAdicSystem
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) (k : ℕ) :
    Function.Surjective ((E.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V)) ∧
      LinearMap.ker ((E.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V)).hom =
        chartSectionIdeal B S hS F hF 𝓘 V ^ (k + 1) •
          (⊤ : Submodule (chartRing B S hS F hF V) ((E.obj (op (k + 1))).val.obj (op V))) := by
  have hIcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ hI
  have hEcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _
    (hE.1 (k + 1)).toIsQuasicoherentOnSite
  obtain ⟨e, he⟩ := hE.2.2 k
  have hsplit : (E.map (homOfLE (Nat.le_add_right k 1)).op).val.app (op V) =
      (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (k + 1) (E.obj (op (k + 1)))).ι).val.app
        (op V) ≫ e.hom.val.app (op V) := by
    rw [← he]
    rfl
  have hbij : Function.Bijective (e.hom.val.app (op V)) :=
    ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation _ (op V)).map e.hom)
  constructor
  · rw [hsplit]
    exact hbij.2.comp (surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart _ hEcart
      (k + 1) hV)
  · rw [hsplit, ModuleCat.hom_comp, LinearMap.ker_comp,
      LinearMap.ker_eq_bot.2 hbij.1, Submodule.comap_bot]
    exact ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart _ hEcart (k + 1) hV

variable {B S hS F hF 𝓘 E} in
/-- Over an affine chart `V`, the shifted tower of sections `M` of a coherent adic system as an
inverse system for the ideal `𝓘(V)`: each `M (k + 1) ⟶ M k` is surjective with kernel
`𝓘(V)^k M (k + 1)`. -/
def C1573.adicSectionInverseSystem (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) {V : (smallEtaleRingedSite B S hS F hF).C}
    (hV : IsAffine (chartScheme V)) :
    Stacks.AdicCompletion.InverseLimit.InverseSystem (chartSectionIdeal B S hS F hF 𝓘 V) where
  M := adicSectionTower B S hS F hF E V
  π := adicSectionTransition B S hS F hF E V
  surjective
    | 0 => fun _ ↦ ⟨0, funext fun i ↦ i.elim0⟩
    | k + 1 => (surjective_and_ker_transition_of_isCoherentAdicSystem hI hE hV k).1
  ker_π
    | 0 => by
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact LinearMap.ker_zero
    | k + 1 => (surjective_and_ker_transition_of_isCoherentAdicSystem hI hE hV k).2

end AlgebraicGeometry.Space

end
