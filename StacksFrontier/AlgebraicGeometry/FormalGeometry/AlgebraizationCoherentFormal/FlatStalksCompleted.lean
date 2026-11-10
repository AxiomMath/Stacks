module

public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel

/-!
# Flatness of the formal stalks of a coherent adic system flat over the powers of an ideal

Let `(R, J)` be a Noetherian ring with an ideal and let `(F_n)` be a coherent adic system on a
locally Noetherian scheme `Y` whose ideal sheaf is generated, at a point `y`, by the image of `J`
under a ring map `θ : R → 𝒪_{Y,y}`. If each stalk `F_{n,y}` is flat over `R ⧸ Jⁿ⁺¹`, then the
formal stalk `F_y^∧ = lim F_{n,y}` is flat over `R`. This is the passage from the hypothesis of
Stacks 0EJV, that `F_n` is flat over `R/𝔪ⁿ`, to hypothesis (2) of Stacks 0EJU, that the formal
stalks are `R`-flat. It is Stacks 0912 applied to the tower of truncations of the formal stalk,
which is `J`-adically complete and has the stalks `F_{n,y}` as its truncations.

## Main definitions

* `Stacks.Algebraization.StalksFlatOverQuotient` — the stalks of a module are flat over `R ⧸ J`,
  for an `R`-module structure on the stalks given by ring maps `R → 𝒪_{Y,y}`.

## Main results

* `Stacks.Algebraization.flat_of_isAdicComplete_of_flat_quotient` — an adically complete module
  with flat truncations is flat.
* `Stacks.Algebraization.flat_completedStalk` — the formal stalk is flat.
* `Stacks.Algebraization.StalksFlatOverQuotient.restrict` — the flatness of the stalks restricts
  along an open immersion.

## Implementation notes

Flatness of a stalk `M_y` over `R ⧸ J` is phrased as flatness of `R ⧸ J ⊗_R M_y` over `R ⧸ J`. This
avoids putting an `R ⧸ J`-module structure on `M_y` in a statement; for a module annihilated by
`J`, which is the case of the terms `F_n` with `J = 𝔪ⁿ⁺¹`, the natural map `M_y → R ⧸ J ⊗_R M_y` is
an isomorphism of `R ⧸ J`-modules, so the two notions agree.

## References

* [Stacks Project, Tag 0912](https://stacks.math.columbia.edu/tag/0912)
* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 0EJV](https://stacks.math.columbia.edu/tag/0EJV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace Stacks.Algebraization

/-- **An adically complete module whose truncations are flat over the truncations of the ring is
flat.** -/
theorem flat_of_isAdicComplete_of_flat_quotient {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [IsAdicComplete I M]
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  let F := quotientTower I M
  let qmod : ∀ n : ℕ, Module (R ⧸ I ^ n) (F.obj (.op n)) :=
    fun n => Module.instQuotientIdealSubmoduleHSMulTop M (I ^ n)
  have hscalar : ∀ n : ℕ, let := qmod n
      IsScalarTower R (R ⧸ I ^ n) (F.obj (.op n)) := by
    intro n
    change IsScalarTower R (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M)))
    infer_instance
  have hflat' : ∀ n : ℕ, let := qmod n
      Module.Flat (R ⧸ I ^ n) (F.obj (.op n)) := by
    intro n
    cases n with
    | zero =>
      change Module.Flat (R ⧸ I ^ 0) (M ⧸ (I ^ 0 • (⊤ : Submodule R M)))
      have : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) := by
        rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        infer_instance
      infer_instance
    | succ n => exact hflat n
  have hsurj : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op) :=
    fun n => Submodule.factor_surjective (Submodule.pow_smul_top_le I M (Nat.le_succ n))
  have : Module.Flat R (limit.cone F).pt :=
    (flat_limit_and_tensor_limit_of_flat_quotients I F qmod hscalar hflat' hsurj).1
  let e := ((limit.isLimit F).conePointUniqueUpToIso (adicCompletionIsLimit I M)).toLinearEquiv
  have : Module.Flat R (AdicCompletion I M) := Module.Flat.of_linearEquiv e.symm
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (AdicCompletion.of I M)
    (AdicCompletion.of_bijective I M))

/-- **The stalks of `M` are flat over `R ⧸ J`.** The stalk `M_y` is an `R`-module through the
ring map `θ y : R →+* 𝒪_{Y,y}`, and the condition is that `R ⧸ J ⊗_R M_y` is a flat
`R ⧸ J`-module. For a module annihilated by `J` this is flatness of `M_y` itself over `R ⧸ J`. -/
def StalksFlatOverQuotient {Y : Scheme.{u}} (R : Type u) [CommRing R]
    (θ : ∀ y : Y, R →+* Y.presheaf.stalk y) (J : Ideal R) (M : Y.Modules) : Prop :=
  ∀ y : Y, letI := Module.compHom ((stalkModuleFunctor y).obj M) (θ y)
    Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] ((stalkModuleFunctor y).obj M))

/-- Adic completeness descends along a ring map whose image generates the ideal. -/
theorem isAdicComplete_of_map {R O : Type u} [CommRing R] [CommRing O] [Algebra R O]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
    [h : IsAdicComplete (I.map (algebraMap R O)) M] : IsAdicComplete I M := by
  have hset : ∀ n : ℕ, ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M) =
      ((I.map (algebraMap R O) ^ n • (⊤ : Submodule O M) : Submodule O M) : Set M) := by
    intro n
    rw [← Ideal.map_pow, ← Submodule.restrictScalars_top R O M, ← Ideal.smul_restrictScalars]
    rfl
  have hmod : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • (⊤ : Submodule R M))] ↔
      x ≡ y [SMOD (I.map (algebraMap R O) ^ n • (⊤ : Submodule O M))] := by
    intro n x y
    rw [SModEq.sub_mem, SModEq.sub_mem, ← SetLike.mem_coe, hset n, SetLike.mem_coe]
  have h1 : IsHausdorff I M :=
    ⟨fun x hx => h.toIsHausdorff.haus' x fun n => (hmod n x 0).mp (hx n)⟩
  have h2 : IsPrecomplete I M := ⟨fun f hf => by
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' f fun hmn => (hmod _ _ _).mp (hf hmn)
    exact ⟨L, fun n => (hmod _ _ _).mpr (hL n)⟩⟩
  exact { toIsHausdorff := h1, toIsPrecomplete := h2 }

/-- If `M ⧸ I M` is `R`-linearly equivalent to `N` and `R ⧸ I ⊗_R N` is flat over `R ⧸ I`, then
`M ⧸ I M` is flat over `R ⧸ I`. -/
private theorem flat_quotient_smul_top_of_linearEquiv {R : Type u} [CommRing R] (I : Ideal R)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R] N) [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] N)] :
    Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  let Q := M ⧸ (I • (⊤ : Submodule R M))
  have hbot : (I • (⊤ : Submodule R Q)) = ⊥ := by
    refine le_bot_iff.mp (Submodule.smul_le.mpr fun r hr x _ => ?_)
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [Submodule.mem_bot, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hr trivial
  exact Module.Flat.of_linearEquiv
    ((LinearEquiv.baseChange R (R ⧸ I) N Q e.symm).trans
      (((TensorProduct.quotTensorEquivQuotSMul Q I).trans
        (Submodule.quotEquivOfEqBot _ hbot)).extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective)).symm

/-- **The formal stalk of a coherent adic system flat over the powers of an ideal is flat.** Let
`(G_n)` be a coherent `K`-adic system on a locally Noetherian scheme, `y` a point and
`θ : R →+* 𝒪_{Y,y}` a ring map from a Noetherian ring such that the stalk `K_y` is generated by the
image of an ideal `J ⊆ R`. If each stalk `G_{n,y}` is flat over `R ⧸ J ⁿ⁺¹`, then the completed
stalk `G_y^∧` is flat over `R`. -/
theorem flat_completedStalk {Y : Scheme.{u}} [IsLocallyNoetherian Y] (K : Y.IdealSheafData)
    (G : Stacks.Coherent.CoherentAdicSystems K) (y : Y) (R : Type u) [CommRing R]
    [IsNoetherianRing R] (J : Ideal R) (θ : R →+* Y.presheaf.stalk y)
    (hK : IdealSheafData.stalk K y = J.map θ)
    (hflat : ∀ n : ℕ, letI := Module.compHom ((stalkModuleFunctor y).obj (G.obj.obj (op n))) θ
      Module.Flat (R ⧸ J ^ (n + 1)) ((R ⧸ J ^ (n + 1)) ⊗[R]
        ((stalkModuleFunctor y).obj (G.obj.obj (op n))))) :
    letI := Module.compHom (completedStalk K G y)
      ((algebraMap (Y.presheaf.stalk y) (completedLocalRing K y)).comp θ)
    Module.Flat R (completedStalk K G y) := by
  let : Algebra R (Y.presheaf.stalk y) := θ.toAlgebra
  let M := formalStalk G y
  let : Module R M := Module.compHom M θ
  have : IsScalarTower R (Y.presheaf.stalk y) M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hK' : IdealSheafData.stalk K y = J.map (algebraMap R (Y.presheaf.stalk y)) := hK
  have : IsAdicComplete (J.map (algebraMap R (Y.presheaf.stalk y))) M := by
    rw [← hK']
    exact isAdicComplete_formalStalk G y
  have : IsAdicComplete J M := isAdicComplete_of_map (O := Y.presheaf.stalk y) J M
  have hq : ∀ n : ℕ,
      Module.Flat (R ⧸ J ^ (n + 1)) (M ⧸ (J ^ (n + 1) • (⊤ : Submodule R M))) := by
    intro n
    let N := (stalkModuleFunctor y).obj (G.obj.obj (op n))
    let : Module R N := Module.compHom N θ
    have : IsScalarTower R (Y.presheaf.stalk y) N :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hsub : (IdealSheafData.stalk K y ^ (n + 1) •
        (⊤ : Submodule (Y.presheaf.stalk y) M)).restrictScalars R =
          J ^ (n + 1) • (⊤ : Submodule R M) := by
      rw [hK', ← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
    let N' := (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).obj (G.obj.obj (op n))
    let : Module R N' := Module.compHom N' θ
    have : IsScalarTower R (Y.presheaf.stalk y) N' :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let e₀ : N' ≃ₗ[Y.presheaf.stalk y] N :=
      ((AlgebraicGeometry.restrictScalarsStalkFunctorIso y).app
        (G.obj.obj (op n))).symm.toLinearEquiv
    let e₁ : (M ⧸ (J ^ (n + 1) • (⊤ : Submodule R M))) ≃ₗ[R] N :=
      (Submodule.quotEquivOfEq _ _ hsub.symm).trans
        ((Submodule.Quotient.restrictScalarsEquiv R _).trans
          (((formalStalkQuotientEquivStalk G y n).trans e₀).restrictScalars R))
    have hN : Module.Flat (R ⧸ J ^ (n + 1)) ((R ⧸ J ^ (n + 1)) ⊗[R] N) := hflat n
    exact flat_quotient_smul_top_of_linearEquiv (J ^ (n + 1)) e₁
  have : Module.Flat R M := flat_of_isAdicComplete_of_flat_quotient J M hq
  let : Module R (completedStalk K G y) := Module.compHom (completedStalk K G y)
    ((algebraMap (Y.presheaf.stalk y) (completedLocalRing K y)).comp θ)
  let e₄ := formalStalkEquivCompletedStalk G y
  let e₅ : completedStalk K G y ≃ₗ[R] M :=
    { e₄.symm.toAddEquiv with
      map_smul' := fun r c => by
        change e₄.symm (algebraMap (Y.presheaf.stalk y) (completedLocalRing K y) (θ r) • c) =
          θ r • e₄.symm c
        rw [algebraMap_smul, map_smul] }
  exact Module.Flat.of_linearEquiv e₅

/-- **Flatness of the stalks over `R ⧸ J` restricts along open immersions.** -/
theorem StalksFlatOverQuotient.restrict {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) [IsOpenImmersion f]
    {R : Type u} [CommRing R] {θ : ∀ y : Y, R →+* Y.presheaf.stalk y} {J : Ideal R}
    {M : Y.Modules} (h : StalksFlatOverQuotient R θ J M) :
    StalksFlatOverQuotient R (fun y => (f.stalkMap y).hom.comp (θ (f y))) J
      ((Scheme.Modules.restrictFunctor f).obj M) := by
  intro y
  let N' := (stalkModuleFunctor y).obj ((Scheme.Modules.restrictFunctor f).obj M)
  let N := (stalkModuleFunctor (f y)).obj M
  let : Module R N' := Module.compHom N' ((f.stalkMap y).hom.comp (θ (f y)))
  let : Module R N := Module.compHom N (θ (f y))
  let e₀ := (Stacks.Duality.restrictStalkModuleIso f y M).toLinearEquiv
  let e : N' ≃ₗ[R] N :=
    { e₀.toAddEquiv with
      map_smul' := fun r m => e₀.map_smul (θ (f y) r) m }
  have hN : Module.Flat (R ⧸ J) ((R ⧸ J) ⊗[R] N) := h (f y)
  exact Module.Flat.of_linearEquiv (LinearEquiv.baseChange R (R ⧸ J) N' N e)

end Stacks.Algebraization

end
