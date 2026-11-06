module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.CategoryTheory.Abelian.CokernelPowFiltration
public import StacksFrontier.LinearAlgebra.FinsuppPermutationInvariants
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleStalkDecomposition

/-!
# The filtration of the free sheaf on the torsor of an extension

Let `Λ = ℤ/ℓ` with `ℓ` prime and `0 → Λ_X → E → Λ_X → 0` an extension on the small étale site of a
scheme `X`, with torsor `P = ε⁻¹(1)` and translation `τ`
(`Stacks.EtaleCohomology.ExtensionTorsor`). On the free sheaf of modules `Λ[P]` let
`s = Λ[τ] - 1`. At every point of the site the fibre of `Λ[P]` is the free module on the fibre
of `P`, a torsor under `ℤ/ℓ` for the translation; so it has dimension `ℓ`, `s` acts nilpotently
there with one-dimensional kernel, and the cokernels of the powers of `s` form short exact
sequences `0 → coker s → coker s^{j+1} → coker s^j → 0` for `j < ℓ`
(`Stacks.Abelian.cokernelPowShortComplex_shortExact`).

## Main results

* `Stacks.EtaleCohomology.ExtensionTorsor.natCast_self_eq_zero`: `ℓ = 0` in the endomorphism ring
  of a sheaf of `ℤ/ℓ`-modules.
* `Stacks.EtaleCohomology.ExtensionTorsor.shift_pow_self`: `s^ℓ = 0`.
* `Stacks.EtaleCohomology.ExtensionTorsor.finrank_sheafFiber_freeTorsor`,
  `Stacks.EtaleCohomology.ExtensionTorsor.finrank_ker_sheafFiber_map_shift`: at every point the
  fibre of `Λ[P]` has dimension `ℓ` and the kernel of `s` on it is a line.
* `Stacks.EtaleCohomology.ExtensionTorsor.cokernelPowShortComplex_shift_shortExact`: the
  filtration by the cokernels of the powers of `s`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.ExtensionTorsor

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : EtaleModules.{u, 0} (ZMod ℓ) X}
  {i : unitSheaf ℓ ⟶ E} {ε : E ⟶ unitSheaf ℓ} {w : i ≫ ε = 0}
  (hS : (ShortComplex.mk i ε w).ShortExact)

/-- The free sheaf of `ℤ/ℓ`-modules on the torsor of the extension. -/
abbrev freeTorsor : EtaleModules.{u, 0} (ZMod ℓ) X :=
  (etaleModuleFree (ZMod ℓ) X).obj (torsor i ε w)

/-- The endomorphism `s = Λ[τ] - 1` of the free sheaf on the torsor. -/
def shift : End (freeTorsor (i := i) (ε := ε) (w := w)) :=
  Functor.mapEnd (torsor i ε w) (etaleModuleFree (ZMod ℓ) X) (translation hS) - 1

/-- In the endomorphism ring of a sheaf of `ℤ/ℓ`-modules, `ℓ = 0`. -/
theorem natCast_self_eq_zero (M : EtaleModules.{u, 0} (ZMod ℓ) X) : ((ℓ : ℕ) : End M) = 0 := by
  rw [← nsmul_one]
  apply End.ext
  apply Sheaf.hom_ext
  ext U x
  show (ℓ : ℕ) • x = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]

/-- **`s^ℓ = 0`**: `(Λ[τ] - 1)^ℓ = Λ[τ]^ℓ - 1 = Λ[τ^ℓ] - 1 = 0` in characteristic `ℓ`. -/
theorem shift_pow_self : shift hS ^ ℓ = 0 := by
  have hp : ℓ.Prime := Fact.out
  set x : End (freeTorsor (i := i) (ε := ε) (w := w)) :=
    Functor.mapEnd (torsor i ε w) (etaleModuleFree (ZMod ℓ) X) (translation hS)
  have hx : x ^ ℓ = 1 := by
    rw [← map_pow, translation_pow_self]
    exact (Functor.mapEnd (torsor i ε w) (etaleModuleFree (ZMod ℓ) X)).map_one
  have h := (Commute.one_right x).neg_right.add_pow_prime_eq' hp
  rw [shift, sub_eq_add_neg, h, hx, natCast_self_eq_zero, zero_mul, add_zero]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [neg_one_sq, ← two_mul]
    exact_mod_cast natCast_self_eq_zero _
  · rw [hodd.neg_one_pow, add_neg_cancel]

section Fibre

variable (Φ : X.smallEtaleTopology.Point.{u + 1})

/-- The action of the translation on the fibre of the torsor. -/
abbrev fiberShift : (Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj →
    (Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj :=
  (Φ.presheafFiber (A := Type (u + 1))).map (translation hS).asHom.hom

/-- `τ^ℓ = 1` on the fibre of the torsor. -/
theorem fiberShift_iterate_self :
    (fiberShift hS Φ)^[ℓ] = id := by
  funext t
  rw [← presheafFiber_map_pow_apply, translation_pow_self]
  show (Φ.presheafFiber (A := Type (u + 1))).map (𝟙 _) t = t
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- `τᵏ = τ^(k mod ℓ)` on the fibre of the torsor. -/
theorem fiberShift_iterate_mod (k : ℕ) (t : (Φ.presheafFiber (A := Type (u + 1))).obj
    (torsor i ε w).obj) : (fiberShift hS Φ)^[k] t = (fiberShift hS Φ)^[k % ℓ] t := by
  conv_lhs => rw [← Nat.mod_add_div k ℓ, Function.iterate_add_apply]
  congr 1
  induction k / ℓ with
  | zero => rfl
  | succ m ih => rw [Nat.mul_succ, Function.iterate_add_apply, fiberShift_iterate_self, id, ih]

/-- **The fibre of the torsor is a torsor under `ℤ/ℓ`**: `k ↦ τᵏ t₀` is a bijection. -/
theorem bijective_fiberShift_iterate (t₀ : (Φ.presheafFiber (A := Type (u + 1))).obj
    (torsor i ε w).obj) :
    Function.Bijective (fun k : ZMod ℓ => (fiberShift hS Φ)^[k.val] t₀) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · wlog hle : a.val ≤ b.val generalizing a b
    · exact (this b a hab.symm (by omega)).symm
    have h : (fiberShift hS Φ)^[b.val - a.val] ((fiberShift hS Φ)^[a.val] t₀) =
        (fiberShift hS Φ)^[a.val] t₀ := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
      exact hab.symm
    have h0 := natCast_eq_zero_of_iterate_eq hS Φ _ _ h
    rw [ZMod.natCast_eq_zero_iff] at h0
    have : b.val - a.val = 0 :=
      Nat.eq_zero_of_dvd_of_lt h0 ((Nat.sub_le _ _).trans_lt (ZMod.val_lt b))
    exact ZMod.val_injective ℓ (by omega)
  · obtain ⟨k, rfl⟩ := exists_iterate_eq hS Φ t₀ t
    refine ⟨(k : ZMod ℓ), ?_⟩
    simp only
    rw [ZMod.val_natCast, ← fiberShift_iterate_mod]

include hS in
/-- **The fibre of the torsor has `ℓ` elements.** -/
theorem natCard_fiber_torsor :
    Nat.card ((Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj) = ℓ := by
  obtain ⟨t₀⟩ := nonempty_presheafFiber_torsor hS Φ
  rw [← Nat.card_congr (Equiv.ofBijective _ (bijective_fiberShift_iterate hS Φ t₀)),
    Nat.card_zmod]

end Fibre

section FibreDimension

/-- `ZMod ℓ`-modules in universe `u + 1` have colimits of size `u + 1`. -/
local instance : HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} (ZMod ℓ)

/-- `ZMod ℓ`-modules in universe `u + 1` have limits of size `u + 1`. -/
local instance : HasLimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
  ModuleCat.instHasLimitsOfSize.{u + 1, u + 1, 0}

/-- The forgetful functor on `ZMod ℓ`-modules preserves filtered colimits of size `u + 1`. -/
local instance : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
    (forget (ModuleCat.{u + 1, 0} (ZMod ℓ))) :=
  comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1})
    (forget AddCommGrpCat.{u + 1})

variable (Φ : X.smallEtaleTopology.Point.{u + 1})

/-- The fibre of `Λ[P]` is the free module on the fibre of `P`. -/
def fiberFreeTorsorIso :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).obj (freeTorsor (i := i) (ε := ε) (w := w)) ≅
      (ModuleCat.freeSplit.{u + 1, 0} (ZMod ℓ)).obj
        ((Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj) :=
  (Φ.freeSheafFiberIso (ZMod ℓ)).app (torsor i ε w)

/-- On the fibre, `s` is `σ_* - 1` for the translation `σ` of the fibre of the torsor. -/
theorem sheafFiber_map_shift_comp :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map (shift hS).asHom ≫
        (fiberFreeTorsorIso (i := i) (ε := ε) (w := w) Φ).hom =
      (fiberFreeTorsorIso Φ).hom ≫
        ((ModuleCat.freeSplit.{u + 1, 0} (ZMod ℓ)).map (TypeCat.ofHom (fiberShift hS Φ)) -
          𝟙 _) := by
  have h := (Φ.freeSheafFiberIso (ZMod ℓ)).hom.naturality (translation hS).asHom
  rw [shift, End.sub_asHom, Functor.mapEnd_apply_asHom, End.one_asHom, Functor.map_sub, CategoryTheory.Functor.map_id, Preadditive.sub_comp, Category.id_comp,
    Preadditive.comp_sub, Category.comp_id]
  congr 1

/-- The translation of the fibre of the torsor, as a permutation (`τ^ℓ = 1`). -/
def fiberShiftEquiv : (Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj ≃
    (Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj where
  toFun := fiberShift hS Φ
  invFun := (fiberShift hS Φ)^[ℓ - 1]
  left_inv t := by
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one,
      Nat.sub_add_cancel (Fact.out : ℓ.Prime).one_lt.le, fiberShift_iterate_self, id]
  right_inv t := by
    rw [← Function.iterate_succ_apply' (fiberShift hS Φ), Nat.succ_eq_add_one,
      Nat.sub_add_cancel (Fact.out : ℓ.Prime).one_lt.le, fiberShift_iterate_self, id]

include hS in
/-- The fibre of the torsor is finite. -/
theorem finite_fiber_torsor :
    Finite ((Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj) :=
  Nat.finite_of_card_ne_zero
    (by rw [natCard_fiber_torsor hS Φ]; exact (Fact.out : ℓ.Prime).ne_zero)

include hS in
/-- **The fibre of `Λ[P]` has dimension `ℓ`.** -/
theorem finrank_sheafFiber_freeTorsor :
    Module.finrank (ZMod ℓ) ((Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).obj
      (freeTorsor (i := i) (ε := ε) (w := w))) = ℓ := by
  have := finite_fiber_torsor hS Φ
  have := Fintype.ofFinite ((Φ.presheafFiber (A := Type (u + 1))).obj (torsor i ε w).obj)
  rw [(fiberFreeTorsorIso Φ).toLinearEquiv.finrank_eq]
  show Module.finrank (ZMod ℓ) (_ →₀ ZMod ℓ) = ℓ
  rw [Module.finrank_finsupp_self, Fintype.card_eq_nat_card, natCard_fiber_torsor hS Φ]

include hS in
/-- The fibre of `Λ[P]` is finite-dimensional. -/
theorem finiteDimensional_sheafFiber_freeTorsor :
    FiniteDimensional (ZMod ℓ) ((Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).obj
      (freeTorsor (i := i) (ε := ε) (w := w))) :=
  Module.finite_of_finrank_pos
    (by rw [finrank_sheafFiber_freeTorsor hS Φ]; exact (Fact.out : ℓ.Prime).pos)

/-- **The kernel of `s` on the fibre of `Λ[P]` is a line**: the invariants of the transitive
translation. -/
theorem finrank_ker_sheafFiber_map_shift :
    Module.finrank (ZMod ℓ) (LinearMap.ker
      ((Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map (shift hS).asHom).hom) = 1 := by
  have := finite_fiber_torsor hS Φ
  have hne := nonempty_presheafFiber_torsor hS Φ
  let e := (fiberFreeTorsorIso (i := i) (ε := ε) (w := w) Φ).toLinearEquiv
  let g := ((ModuleCat.freeSplit.{u + 1, 0} (ZMod ℓ)).map (TypeCat.ofHom (fiberShift hS Φ)) -
    𝟙 _).hom
  have hsq : ((Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map (shift hS).asHom).hom =
      e.symm.toLinearMap ∘ₗ g ∘ₗ e.toLinearMap := by
    ext x
    apply e.injective
    have h := ConcreteCategory.congr_hom (sheafFiber_map_shift_comp hS Φ) x
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    exact h
  have hker : LinearMap.ker ((Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map (shift hS).asHom).hom =
      (LinearMap.ker g).map e.symm.toLinearMap := by
    rw [hsq, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, LinearMap.ker_comp,
      Submodule.comap_equiv_eq_map_symm]
  rw [hker, LinearEquiv.finrank_map_eq]
  exact Finsupp.finrank_ker_lmapDomain_sub_id_eq_one (K := ZMod ℓ) (fiberShiftEquiv hS Φ)
    (exists_iterate_eq hS Φ)

/-- **The cokernels of the powers of `s` on `Λ[P]` form a filtration with steps `coker s`**: for
`j < ℓ` the sequence `0 → coker s --s^j--> coker s^{j+1} → coker s^j → 0` is short exact. -/
theorem cokernelPowShortComplex_shift_shortExact {j : ℕ} (hj : j < ℓ) :
    (Stacks.Abelian.cokernelPowShortComplex (shift hS) j).ShortExact := by
  have := etaleModules_AB5OfSize.{u} (ZMod ℓ)
  have : GrothendieckTopology.HasEnoughPoints.{u + 1} X.smallEtaleTopology :=
    Scheme.hasEnoughPoints_smallEtaleTopology.{0, u} X
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty X.smallEtaleTopology
  let Φ : P.FullSubcategory → EtaleModules.{u, 0} (ZMod ℓ) X ⥤ ModuleCat.{u + 1} (ZMod ℓ) :=
    fun q => q.obj.sheafFiber
  have hΦ := hP.jointlyFaithful (ModuleCat.{u + 1} (ZMod ℓ))
  refine Stacks.Abelian.cokernelPowShortComplex_shortExact Φ
    (fun f g h => hΦ.map_injective h) _ j ?_
  have : ∀ q, FiniteDimensional (ZMod ℓ) ((Φ q).obj (freeTorsor (i := i) (ε := ε) (w := w))) :=
    fun q => finiteDimensional_sheafFiber_freeTorsor hS q.obj
  exact Stacks.Abelian.exists_map_eq_of_finrank Φ (shift hS) (n := ℓ)
    (fun q => finrank_sheafFiber_freeTorsor hS q.obj) (shift_pow_self hS)
    (fun q => finrank_ker_sheafFiber_map_shift hS q.obj) hj

end FibreDimension

end Stacks.EtaleCohomology.ExtensionTorsor

end
