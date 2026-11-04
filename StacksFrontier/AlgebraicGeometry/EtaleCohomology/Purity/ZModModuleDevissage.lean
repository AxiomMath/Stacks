module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.LocallyConstantCoefficients

/-!
# Dévissage of finite `ℤ/N`-modules

A natural transformation `η : F ⟶ G` between additive functors out of the category of
`ℤ/N`-modules is invertible at every finite `ℤ/N`-module as soon as it is invertible at the
cyclic modules `ℤ/n`, `n ∣ N` (regarded as `ℤ/N`-modules by restriction of scalars)
(`Stacks.EtaleCohomology.Purity.isIso_app_of_finite_zmodModule`): a finite abelian group is a
finite direct sum of cyclic groups, an additive map between `ℤ/N`-modules is `ℤ/N`-linear, and a
natural transformation of additive functors is invertible at a biproduct as soon as it is at the
summands (`Stacks.EtaleCohomology.Purity.isIso_natTrans_app_biprod`). This is the form of
`Stacks.TorsionDevissage.isIso_app_of_finite_of_dvd` for sheaves of `ℤ/N`-modules.

## Main results

* `Stacks.EtaleCohomology.Purity.isIso_natTrans_app_biprod`.
* `Stacks.EtaleCohomology.Purity.isIso_app_of_finite_zmodModule`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace Stacks.EtaleCohomology.Purity

/-- **A natural transformation of additive functors is invertible at a binary biproduct** as soon
as it is invertible at the two summands. -/
theorem isIso_natTrans_app_biprod {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [Preadditive 𝒞]
    [Preadditive 𝒟] [HasBinaryBiproducts 𝒞] [HasBinaryBiproducts 𝒟] {Φ Ψ : 𝒞 ⥤ 𝒟}
    [Φ.Additive] [Ψ.Additive] (τ : Φ ⟶ Ψ) (X Y : 𝒞)
    (hX : IsIso (τ.app X)) (hY : IsIso (τ.app Y)) : IsIso (τ.app (X ⊞ Y)) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts Φ
  have := preservesBinaryBiproducts_of_preservesBiproducts Ψ
  have h : τ.app (X ⊞ Y) = (Φ.mapBiprod X Y).hom ≫ biprod.map (τ.app X) (τ.app Y) ≫
      (Ψ.mapBiprod X Y).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    ext
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc]
      exact (τ.naturality biprod.fst).symm
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc]
      exact (τ.naturality biprod.snd).symm
  have : IsIso (biprod.map (τ.app X) (τ.app Y)) :=
    ⟨biprod.map (inv (τ.app X)) (inv (τ.app Y)), by ext <;> simp, by ext <;> simp⟩
  rw [h]
  infer_instance

/-- A natural transformation invertible at an object is invertible at every isomorphic one. -/
theorem isIso_natTrans_app_of_iso {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] {Φ Ψ : 𝒞 ⥤ 𝒟}
    (τ : Φ ⟶ Ψ) {X Y : 𝒞} (e : X ≅ Y) (hX : IsIso (τ.app X)) : IsIso (τ.app Y) := by
  have h : τ.app Y = Φ.map e.inv ≫ τ.app X ≫ Ψ.map e.hom := by
    rw [← τ.naturality, ← Category.assoc, ← Φ.map_comp, e.inv_hom_id, Φ.map_id,
      Category.id_comp]
  rw [h]
  infer_instance

variable (N : ℕ)

/-- An additive equivalence between `ℤ/N`-modules is `ℤ/N`-linear. -/
def zmodLinearEquivOfAddEquiv {M M₁ : Type*} [AddCommGroup M] [AddCommGroup M₁]
    [Module (ZMod N) M] [Module (ZMod N) M₁] (e : M ≃+ M₁) : M ≃ₗ[ZMod N] M₁ :=
  { e.toAddMonoidHom.toZModLinearMap N with
    invFun := e.symm
    left_inv := e.symm_apply_apply
    right_inv := e.apply_symm_apply }

/-- `ℤ/n`, regarded as a `ℤ/N`-module for `n ∣ N`. -/
abbrev zmodCyclicModule {n : ℕ} (hn : n ∣ N) : ModuleCat.{w} (ZMod N) :=
  (ModuleCat.restrictScalars (ZMod.castHom hn (ZMod n))).obj
    (ModuleCat.of (ZMod n) (ULift.{w} (ZMod n)))

variable {N} {𝒟 : Type*} [Category* 𝒟] [Preadditive 𝒟] [HasBinaryBiproducts 𝒟]
  {F G : ModuleCat.{w} (ZMod N) ⥤ 𝒟} [F.Additive] [G.Additive] (η : F ⟶ G)

/-- `η` is invertible at every finite product of cyclic modules `ℤ/q` with `q ∣ N`, as soon as it
is invertible at the cyclic modules `ℤ/n` with `n ∣ N`. -/
theorem isIso_app_piFin_zmodModule
    (hcyc : ∀ (n : ℕ) (hn : n ∣ N), 0 < n → IsIso (η.app (zmodCyclicModule.{w} N hn))) :
    ∀ (k : ℕ) (q : Fin k → ℕ) (hq : ∀ j, q j ∣ N), (∀ j, 0 < q j) →
      IsIso (η.app (ModuleCat.of (ZMod N) (∀ j : Fin k, (zmodCyclicModule.{w} N (hq j))))) := by
  intro k
  induction k with
  | zero =>
      intro q hq _
      refine isIso_natTrans_app_of_iso η ?_ (hcyc 1 (one_dvd N) Nat.one_pos)
      let e0 : (zmodCyclicModule.{w} N (one_dvd N) : Type w) ≃+
          (∀ j : Fin 0, (zmodCyclicModule.{w} N (hq j) : Type w)) :=
        { toFun := fun _ => 0
          invFun := fun _ => 0
          left_inv := fun a => ULift.ext _ _ (Subsingleton.elim (α := ZMod 1) _ _)
          right_inv := fun b => funext fun j => Fin.elim0 j
          map_add' := fun _ _ => (add_zero _).symm }
      exact (zmodLinearEquivOfAddEquiv N e0).toModuleIso
  | succ k ih =>
      intro q hq hpos
      have h0 := hcyc (q 0) (hq 0) (hpos 0)
      have htail := ih (fun j => q j.succ) (fun j => hq j.succ) (fun j => hpos j.succ)
      refine isIso_natTrans_app_of_iso η ?_ (isIso_natTrans_app_biprod η _ _ h0 htail)
      exact ModuleCat.biprodIsoProd _ _ ≪≫ (zmodLinearEquivOfAddEquiv N
        (Stacks.TorsionDevissage.piFinSuccAddEquiv k
          fun j => zmodCyclicModule.{w} N (hq j))).toModuleIso

/-- **`η` is invertible at every finite `ℤ/N`-module**, as soon as it is invertible at the cyclic
modules `ℤ/n` with `n ∣ N`. -/
theorem isIso_app_of_finite_zmodModule [NeZero N]
    (hcyc : ∀ (n : ℕ) (hn : n ∣ N), 0 < n → IsIso (η.app (zmodCyclicModule.{w} N hn)))
    (M : ModuleCat.{w} (ZMod N)) [Finite M] : IsIso (η.app M) := by
  classical
  obtain ⟨ι, _, m, hm, ⟨f0⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' (M : Type w)
  have f : (M : Type w) ≃+ ∀ i, ZMod (m i) := f0.trans (DirectSum.addEquivProd _)
  have hdvd : ∀ i, m i ∣ N := by
    intro i
    have hns : N • (Pi.single (M := fun i => ZMod (m i)) i (1 : ZMod (m i))) = 0 := by
      have hx : N • f.symm (Pi.single (M := fun i => ZMod (m i)) i (1 : ZMod (m i))) = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]
      simpa [AddEquiv.apply_symm_apply] using congrArg f hx
    have h1 : N • (1 : ZMod (m i)) = 0 := by simpa using congrFun hns i
    simpa using addOrderOf_dvd_of_nsmul_eq_zero h1
  have key := isIso_app_piFin_zmodModule η hcyc (Fintype.card ι)
    (fun j => m ((Fintype.equivFin ι).symm j)) (fun j => hdvd _)
    (fun j => lt_trans Nat.one_pos (hm _))
  refine isIso_natTrans_app_of_iso η ?_ key
  refine (zmodLinearEquivOfAddEquiv N ?_).toModuleIso
  exact (AddEquiv.piCongrRight (fun j => AddEquiv.ulift)).trans
    ((Stacks.TorsionDevissage.piCongrLeftAddEquiv (fun i => ZMod (m i))
      (Fintype.equivFin ι)).symm.trans f.symm)

end Stacks.EtaleCohomology.Purity

end
