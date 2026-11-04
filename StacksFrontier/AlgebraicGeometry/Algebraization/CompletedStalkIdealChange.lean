module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkDepthSpecialization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.IdealChange
public import StacksFrontier.AlgebraicGeometry.Scheme.AffineOpenNeighborhood
public import StacksFrontier.RingTheory.AdicCompletion.Comparison
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe

/-!
# Completed stalks under a change of the ideal

Let `X` be a Noetherian scheme and let `𝒥 ⊆ ℐ` be quasi-coherent ideal sheaves with `ℐ ᵃ ⊆ 𝒥`, so
that they cut out the same closed subset. [Stacks, Tag 0EHR] transfers an object `(ℱₙ)` of
`Coh(X, ℐ)` to the object `(ℱ_{a(n+1)} / 𝒥 ⁿ⁺¹ ℱ_{a(n+1)})` of `Coh(X, 𝒥)`
(`Stacks.Coherent.transferFunctor`). This file shows that the local data the chapter on
algebraization states its conditions with do not change under that transfer: at every point `x`
the `𝒥`-adic and the `ℐ`-adic completions of `𝒪_{X,x}` are isomorphic `𝒪_{X,x}`-algebras, and the
completed stalks of `(ℱₙ)` and of its transfer are isomorphic, semilinearly over that ring
isomorphism. Consequently the depths `depth((ℱ_x^∧)_𝔭)`, the dimensions `dim(𝒪_{X,x}^∧/𝔭)`, the
condition `𝔭 ∉ V(ℐ𝒪_{X,x}^∧)` and the condition `V(𝔭) ∩ V(ℐ𝒪_{X,x}^∧) = {𝔪_x^∧}` agree at
corresponding primes.

## Main results

* `Stacks.Algebraization.exists_linearEquiv_limit_of_isAdicComplete` — a module complete for an
  ideal `J` and mapping onto a tower with kernels `Jⁿ⁺¹` is the limit of the tower.
* `Stacks.Algebraization.map_smul_of_isHausdorff` — an `A`-linear map from a module over the
  `J`-adic completion to an `I`-adically Hausdorff module over the `I`-adic completion is
  semilinear over any `A`-algebra map of the completions, when `J ≤ I` is finitely generated.
* `Stacks.Algebraization.completedLocalRingTransferEquiv` and
  `Stacks.Algebraization.completedStalkTransferEquiv` — the two comparisons, and
  `Stacks.Algebraization.completedStalkTransferEquiv_smul` their compatibility.
* `Stacks.Algebraization.completedStalkDepth_transfer`,
  `Stacks.Algebraization.ringKrullDim_quotient_transfer`,
  `Stacks.Algebraization.completedLocalIdeal_le_transfer_iff` and
  `Stacks.Algebraization.adicClosedFibreThrough_transfer_eq_singleton_iff` — the consequences for
  the quantities in the `(a, b)`-inequalities of [Stacks, Tag 0EJ3].

## References

* [Stacks Project, Tag 0EHR](https://stacks.math.columbia.edu/tag/0EHR)
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3)
* [Stacks Project, Tag 0EJN](https://stacks.math.columbia.edu/tag/0EJN), whose proof begins
  "we may assume `I = (f₁, …, f_d)`".
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

/-! ### Two facts of commutative algebra -/

section Algebra

variable {A : Type u} [CommRing A]

/-- **A complete module mapping onto a tower with the right kernels is its limit.** Let `L` be
`J`-adically complete and let `πₙ : L → Pₙ` be compatible surjections onto the terms of a tower
`P` with `ker πₙ = Jⁿ⁺¹ L`. Then the induced map `L → lim P` is an isomorphism. -/
public theorem exists_linearEquiv_limit_of_isAdicComplete {J : Ideal A} {L : Type u}
    [AddCommGroup L] [Module A L] [IsAdicComplete J L] (P : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (π : ∀ n : ℕ, L →ₗ[A] P.obj (op n))
    (hπ : ∀ (n : ℕ) (l : L), (P.map (homOfLE (Nat.le_succ n)).op).hom (π (n + 1) l) = π n l)
    (hsurj : ∀ n, Function.Surjective (π n))
    (hker : ∀ n, LinearMap.ker (π n) = J ^ (n + 1) • (⊤ : Submodule A L)) :
    ∃ ψ : L ≃ₗ[A] (limit P : ModuleCat.{u} A),
      ∀ (n : ℕ) (l : L), (limit.π P (op n)).hom (ψ l) = π n l := by
  let T : ℕ → Type u := fun n => P.obj (op n)
  let t : ∀ n, T (n + 1) →ₗ[A] T n := fun n => (P.map (homOfLE (Nat.le_succ n)).op).hom
  let ψ₀ : L →ₗ[A] Stacks.Coherent.moduleTowerLimit T t :=
    { toFun := fun l => ⟨fun n => π n l, fun n => hπ n l⟩
      map_add' := fun l l' => Subtype.ext (funext fun n => (π n).map_add l l')
      map_smul' := fun c l => Subtype.ext (funext fun n => (π n).map_smul c l) }
  have hinj : Function.Injective ψ₀ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro l hl
    refine IsHausdorff.haus (inferInstance : IsHausdorff J L) l fun n => ?_
    rw [SModEq.zero]
    cases n with
    | zero => simp
    | succ n =>
      rw [← hker n]
      exact congrArg (fun z => z.1 n) hl
  have hsurj' : Function.Surjective ψ₀ := by
    intro y
    choose l hl using fun n => hsurj n (y.1 n)
    have hstep : ∀ n, π n (l (n + 1)) = y.1 n := fun n => by
      rw [← hπ n, hl (n + 1)]
      exact y.2 n
    have hdiff : ∀ n, l n ≡ l (n + 1) [SMOD (J ^ n • (⊤ : Submodule A L))] := fun n => by
      have hk : l (n + 1) - l n ∈ J ^ (n + 1) • (⊤ : Submodule A L) := by
        rw [← hker n, LinearMap.mem_ker, map_sub, hstep, hl, sub_self]
      exact (SModEq.sub_mem.mpr
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) hk)).symm
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → l m ≡ l n [SMOD (J ^ m • (⊤ : Submodule A L))] := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => rfl
      | succ n hmn ih =>
        exact ih.trans ((hdiff n).mono
          (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)))
    obtain ⟨l₀, hl₀⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete J L) hcauchy
    refine ⟨l₀, Subtype.ext (funext fun n => ?_)⟩
    show π n l₀ = y.1 n
    have hmem : l (n + 1) - l₀ ∈ LinearMap.ker (π n) := by
      rw [hker n]
      exact SModEq.sub_mem.mp (hl₀ (n + 1))
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem
    rw [← hmem, hstep]
  refine ⟨(LinearEquiv.ofBijective ψ₀ ⟨hinj, hsurj'⟩).trans
    (Stacks.Coherent.moduleLimitTowerEquiv P).symm, fun n l => ?_⟩
  rw [← Stacks.Coherent.moduleLimitTowerEquiv_apply_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rfl

/-- An element of `K·B` acts on a `B`-module `N` into `K • ⊤`, with `N` viewed as an `A`-module. -/
private theorem smul_mem_smul_top_of_mem_map {B N : Type*} [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {K : Ideal A} {c : B}
    (hc : c ∈ K.map (algebraMap A B)) (m : N) : c • m ∈ K • (⊤ : Submodule A N) := by
  have h : c • m ∈ (K.map (algebraMap A B) • (⊤ : Submodule B N)).restrictScalars A :=
    (Submodule.restrictScalars_mem A _ _).mpr (Submodule.smul_mem_smul hc Submodule.mem_top)
  rwa [Ideal.smul_restrictScalars, Submodule.restrictScalars_top] at h

/-- **Linear maps between completions are semilinear.** Let `J ≤ I` be ideals of `A` with `J`
finitely generated, let `N₁` be a module over the `J`-adic completion of `A` and `N₂` an
`I`-adically Hausdorff module over the `I`-adic completion, both viewed as `A`-modules. Then an
`A`-linear map `φ : N₁ → N₂` is semilinear over every `A`-algebra map `e` of the completions:
every element of the completion agrees with an element of `A` modulo `Jⁿ`, and `φ` moves the
difference into `Iⁿ N₂`. -/
public theorem map_smul_of_isHausdorff {I J : Ideal A} (hJ : J.FG) (hJI : J ≤ I)
    {N₁ N₂ : Type*} [AddCommGroup N₁] [Module A N₁] [Module (AdicCompletion J A) N₁]
    [IsScalarTower A (AdicCompletion J A) N₁]
    [AddCommGroup N₂] [Module A N₂] [Module (AdicCompletion I A) N₂]
    [IsScalarTower A (AdicCompletion I A) N₂] [IsHausdorff I N₂]
    (e : AdicCompletion J A →ₐ[A] AdicCompletion I A) (φ : N₁ →ₗ[A] N₂)
    (r : AdicCompletion J A) (m : N₁) :
    φ (r • m) = e r • φ m := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I N₂) _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨p, hp⟩ := AdicCompletion.exists_sub_mem_map_pow J hJ n r
  set c := r - algebraMap A (AdicCompletion J A) p with hc
  have hr : r = algebraMap A (AdicCompletion J A) p + c := by rw [hc]; ring
  have h1 : c • m ∈ J ^ n • (⊤ : Submodule A N₁) := smul_mem_smul_top_of_mem_map hp m
  have hec : e c ∈ (J ^ n).map (algebraMap A (AdicCompletion I A)) := by
    have := Ideal.mem_map_of_mem (e : AdicCompletion J A →+* AdicCompletion I A) hp
    rwa [Ideal.map_map, show ((e : AdicCompletion J A →+* AdicCompletion I A).comp
      (algebraMap A (AdicCompletion J A))) = algebraMap A (AdicCompletion I A) from
        e.comp_algebraMap] at this
  have h2 : e c • φ m ∈ J ^ n • (⊤ : Submodule A N₂) := smul_mem_smul_top_of_mem_map hec _
  have hφ1 : φ (c • m) ∈ J ^ n • (⊤ : Submodule A N₂) := by
    have := Submodule.mem_map_of_mem (f := φ) h1
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have key : φ (r • m) - e r • φ m = φ (c • m) - e c • φ m := by
    rw [hr, add_smul, map_add, map_add, add_smul, e.commutes, algebraMap_smul, algebraMap_smul,
      φ.map_smul]
    abel
  rw [key]
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hJI n) (Submodule.sub_mem _ hφ1 h2)

/-- A ring isomorphism is an order isomorphism on ideals. -/
public theorem map_le_map_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {q q' : Ideal R} : q.map (e : R →+* S) ≤ q'.map (e : R →+* S) ↔ q ≤ q' := by
  refine ⟨fun h => ?_, fun h => Ideal.map_mono h⟩
  have := Ideal.comap_mono (f := (e : R →+* S)) h
  rwa [Ideal.comap_map_of_bijective (e : R →+* S) e.bijective,
    Ideal.comap_map_of_bijective (e : R →+* S) e.bijective] at this

end Algebra

/-! ### The stalks of two comparable ideal sheaves -/

section Stalks

variable {X : Scheme.{u}} {ℐ 𝒥 : X.IdealSheafData}

/-- The stalk of an ideal sheaf is monotone in the ideal sheaf. -/
public theorem IdealSheafData.stalk_mono (h : 𝒥 ≤ ℐ) (x : X) :
    IdealSheafData.stalk 𝒥 x ≤ IdealSheafData.stalk ℐ x :=
  iSup₂_mono fun U _ => Ideal.map_mono (h U)

/-- A power containment of ideal sheaves holds on stalks. -/
public theorem IdealSheafData.stalk_pow_le {a : ℕ} (h : ℐ ^ a ≤ 𝒥) (x : X) :
    IdealSheafData.stalk ℐ x ^ a ≤ IdealSheafData.stalk 𝒥 x := by
  obtain ⟨U, hxU, -⟩ := exists_affineOpen_mem_le x ⊤ trivial
  rw [IdealSheafData.stalk_eq_map_germ ℐ x U hxU, IdealSheafData.stalk_eq_map_germ 𝒥 x U hxU,
    ← Ideal.map_pow]
  exact Ideal.map_mono (h U)

end Stalks

/-! ### The comparison along the transfer of [Stacks, Tag 0EHR] -/

section Transfer

variable {X : Scheme.{u}} [IsNoetherian X] {ℐ 𝒥 : X.IdealSheafData} {a : ℕ}
  (hpow : ℐ ^ a ≤ 𝒥) (hle : 𝒥 ≤ ℐ) (F : Stacks.Coherent.CoherentAdicSystems ℐ) (x : X)

/-- The projection from the limit of the stalk tower of `(ℱₙ)` onto the `n`-th stalk of its
transfer: the projection to `ℱ_{a(n+1),x}` followed by the stalk of the quotient map. -/
public def transferStalkProjection (𝒥 : X.IdealSheafData) (a : ℕ)
    (F : Stacks.Coherent.CoherentAdicSystems ℐ) (x : X) (n : ℕ) :
    (limit (F.obj ⋙ modulesStalkFunctor X x) :
        ModuleCat.{u} (X.presheaf.stalk x)) →ₗ[X.presheaf.stalk x]
      (modulesStalkFunctor X x).obj (Stacks.Coherent.transferTerm 𝒥 a F.obj n) :=
  (limit.π (F.obj ⋙ modulesStalkFunctor X x) (op (Stacks.Coherent.transferIndex a n)) ≫
    (modulesStalkFunctor X x).map (Stacks.Coherent.transferProjection 𝒥 a F.obj n)).hom

include hpow hle in
/-- **The transferred system has the same formal stalk.** The limit of the stalk tower of
`(ℱₙ)` maps isomorphically onto the limit of the stalk tower of its transfer, by the projections
`transferStalkProjection`. -/
public theorem exists_linearEquiv_limit_transfer :
    ∃ ψ : (limit (F.obj ⋙ modulesStalkFunctor X x) :
        ModuleCat.{u} (X.presheaf.stalk x)) ≃ₗ[X.presheaf.stalk x]
        (limit (((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F).obj ⋙
          modulesStalkFunctor X x) : ModuleCat.{u} (X.presheaf.stalk x)),
      ∀ (n : ℕ) l, (limit.π (((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F).obj ⋙
          modulesStalkFunctor X x) (op n)).hom (ψ l) = transferStalkProjection 𝒥 a F x n l := by
  have hsurjF := fun k => surjective_stalk_coherentAdicTransition F x k
  have hkerF := fun k => ker_stalk_coherentAdicTransition F x k
  have hIfg : (IdealSheafData.stalk ℐ x).FG := Ideal.fg_of_isNoetherianRing _
  have hJfg : (IdealSheafData.stalk 𝒥 x).FG := Ideal.fg_of_isNoetherianRing _
  have hcI : IsAdicComplete (IdealSheafData.stalk ℐ x)
      (limit (F.obj ⋙ modulesStalkFunctor X x) : ModuleCat.{u} (X.presheaf.stalk x)) :=
    Stacks.Coherent.moduleLimit_isAdicComplete (F.obj ⋙ modulesStalkFunctor X x) hsurjF hkerF hIfg
  have : IsAdicComplete (IdealSheafData.stalk 𝒥 x)
      (limit (F.obj ⋙ modulesStalkFunctor X x) : ModuleCat.{u} (X.presheaf.stalk x)) :=
    isAdicComplete_of_le_of_fg_of_isAdicComplete (IdealSheafData.stalk_mono hle x) hcI hJfg
  refine exists_linearEquiv_limit_of_isAdicComplete (J := IdealSheafData.stalk 𝒥 x)
    (((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F).obj ⋙ modulesStalkFunctor X x)
    (transferStalkProjection 𝒥 a F x) ?_ ?_ ?_
  · intro n l
    have h := Stacks.Coherent.transferProjection_map 𝒥 a F.obj (Nat.le_succ n)
    have hw := limit.w (F.obj ⋙ modulesStalkFunctor X x)
      (homOfLE (Stacks.Coherent.transferIndex_mono a (Nat.le_succ n))).op
    have key : limit.π (F.obj ⋙ modulesStalkFunctor X x)
          (op (Stacks.Coherent.transferIndex a (n + 1))) ≫
        (modulesStalkFunctor X x).map (Stacks.Coherent.transferProjection 𝒥 a F.obj (n + 1)) ≫
          (modulesStalkFunctor X x).map
            (Stacks.Coherent.transferTransition 𝒥 a F.obj (Nat.le_succ n)) =
        limit.π (F.obj ⋙ modulesStalkFunctor X x) (op (Stacks.Coherent.transferIndex a n)) ≫
          (modulesStalkFunctor X x).map (Stacks.Coherent.transferProjection 𝒥 a F.obj n) := by
      rw [← Functor.map_comp, h, Functor.map_comp, ← Category.assoc]
      exact congrArg (· ≫ (modulesStalkFunctor X x).map
        (Stacks.Coherent.transferProjection 𝒥 a F.obj n)) hw
    exact congrArg (fun f => f.hom l) key
  · intro n y
    obtain ⟨z, hz⟩ := surjective_stalk_cokernel_π
      (idealPowerMultiple 𝒥 (n + 1) (F.obj.obj (op (Stacks.Coherent.transferIndex a n)))) x y
    obtain ⟨w, rfl⟩ := Stacks.Coherent.moduleLimit_projection_surjective
      (F.obj ⋙ modulesStalkFunctor X x) hsurjF (Stacks.Coherent.transferIndex a n) z
    exact ⟨w, hz⟩
  · intro n
    have hqc : (F.obj.obj (op (Stacks.Coherent.transferIndex a n))).IsQuasicoherent :=
      (F.property : Stacks.Coherent.IsCoherentAdicSystem ℐ F.obj).isQuasicoherent _
    have hπsurj := Stacks.Coherent.moduleLimit_projection_surjective
      (F.obj ⋙ modulesStalkFunctor X x) hsurjF (Stacks.Coherent.transferIndex a n)
    have hπker := Stacks.Coherent.moduleLimit_projection_ker (I := IdealSheafData.stalk ℐ x)
      (F.obj ⋙ modulesStalkFunctor X x) hsurjF hkerF hIfg (Stacks.Coherent.transferIndex a n)
    have hqker : LinearMap.ker ((modulesStalkFunctor X x).map
        (Stacks.Coherent.transferProjection 𝒥 a F.obj n)).hom =
        IdealSheafData.stalk 𝒥 x ^ (n + 1) • ⊤ := by
      rw [← range_stalk_submodule_ι_eq_ker_stalk_cokernel_π, stalk_idealPowerMultiple]
    set p := (limit.π (F.obj ⋙ modulesStalkFunctor X x)
      (op (Stacks.Coherent.transferIndex a n))).hom
    have hIJ : IdealSheafData.stalk ℐ x ^ (Stacks.Coherent.transferIndex a n + 1) ≤
        IdealSheafData.stalk 𝒥 x ^ (n + 1) := by
      calc IdealSheafData.stalk ℐ x ^ (Stacks.Coherent.transferIndex a n + 1)
          ≤ IdealSheafData.stalk ℐ x ^ Stacks.Coherent.transferIndex a n :=
            Ideal.pow_le_pow_right (Nat.le_succ _)
        _ = (IdealSheafData.stalk ℐ x ^ a) ^ (n + 1) := by
            rw [Stacks.Coherent.transferIndex, pow_mul]
        _ ≤ IdealSheafData.stalk 𝒥 x ^ (n + 1) :=
            pow_le_pow_left' (IdealSheafData.stalk_pow_le hpow x) (n + 1)
    show LinearMap.ker (((modulesStalkFunctor X x).map
      (Stacks.Coherent.transferProjection 𝒥 a F.obj n)).hom.comp p) = _
    have hmap : (IdealSheafData.stalk 𝒥 x ^ (n + 1) •
          (⊤ : Submodule (X.presheaf.stalk x) ((modulesStalkFunctor X x).obj
            (F.obj.obj (op (Stacks.Coherent.transferIndex a n)))))) =
        Submodule.map p (IdealSheafData.stalk 𝒥 x ^ (n + 1) • ⊤) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hπsurj]
    rw [LinearMap.ker_comp, hqker, hmap, Submodule.comap_map_eq, hπker,
      sup_eq_left.mpr (Submodule.smul_mono_left hIJ)]

/-- **The two completed local rings agree.** For `𝒥 ⊆ ℐ` with `ℐ ᵃ ⊆ 𝒥` the `𝒥`-adic and the
`ℐ`-adic completions of `𝒪_{X,x}` are isomorphic `𝒪_{X,x}`-algebras. -/
public def completedLocalRingTransferEquiv :
    completedLocalRing 𝒥 x ≃ₐ[X.presheaf.stalk x] completedLocalRing ℐ x :=
  AdicCompletion.compareAlgEquiv (X.presheaf.stalk x) (a := 1) (b := a)
    (by rw [pow_one]; exact IdealSheafData.stalk_mono hle x) (IdealSheafData.stalk_pow_le hpow x)

/-- **The completed stalk of the transfer is the completed stalk of `(ℱₙ)`**, as
`𝒪_{X,x}`-modules: both are the formal stalks, and those agree by
`Stacks.Algebraization.exists_linearEquiv_limit_transfer`. -/
public def completedStalkTransferEquiv :
    completedStalk 𝒥 ((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F) x ≃ₗ[X.presheaf.stalk x]
      completedStalk ℐ F x :=
  (formalStalkEquivCompletedStalk ((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F) x).symm ≪≫ₗ
    formalStalkEquivModuleStalkLimit ((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F) x ≪≫ₗ
    (exists_linearEquiv_limit_transfer hpow hle F x).choose.symm ≪≫ₗ
    (formalStalkEquivModuleStalkLimit F x).symm ≪≫ₗ formalStalkEquivCompletedStalk F x

/-- The comparison of completed stalks lies over the comparison of completed local rings. -/
public theorem completedStalkTransferEquiv_smul (r : completedLocalRing 𝒥 x)
    (m : completedStalk 𝒥 ((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F) x) :
    completedStalkTransferEquiv hpow hle F x (r • m) =
      completedLocalRingTransferEquiv hpow hle x r • completedStalkTransferEquiv hpow hle F x m :=
  map_smul_of_isHausdorff (I := IdealSheafData.stalk ℐ x) (J := IdealSheafData.stalk 𝒥 x)
    (Ideal.fg_of_isNoetherianRing _) (IdealSheafData.stalk_mono hle x)
    (completedLocalRingTransferEquiv hpow hle x).toAlgHom
    (completedStalkTransferEquiv hpow hle F x).toLinearMap r m

/-- `Stacks.Algebraization.completedStalkTransferEquiv_smul` for the underlying additive and ring
isomorphisms. -/
public theorem completedStalkTransferEquiv_toAddEquiv_smul (r : completedLocalRing 𝒥 x)
    (m : completedStalk 𝒥 ((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F) x) :
    (completedStalkTransferEquiv hpow hle F x).toAddEquiv (r • m) =
      (completedLocalRingTransferEquiv hpow hle x).toRingEquiv r •
        (completedStalkTransferEquiv hpow hle F x).toAddEquiv m :=
  completedStalkTransferEquiv_smul hpow hle F x r m

/-- The comparison of completed local rings, as a ring isomorphism. -/
public abbrev completedLocalRingTransferRingEquiv :
    completedLocalRing 𝒥 x ≃+* completedLocalRing ℐ x :=
  (completedLocalRingTransferEquiv hpow hle x).toRingEquiv

/-- The prime of `𝒪_{X,x}^∧` (`ℐ`-adic) corresponding to a prime of the `𝒥`-adic completion. -/
public abbrev transferPrime (p : PrimeSpectrum (completedLocalRing 𝒥 x)) :
    PrimeSpectrum (completedLocalRing ℐ x) :=
  PrimeSpectrum.comap ((completedLocalRingTransferRingEquiv hpow hle x).symm :
    completedLocalRing ℐ x →+* completedLocalRing 𝒥 x) p

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The ideal of the corresponding prime is the image of the prime. -/
public theorem transferPrime_asIdeal (p : PrimeSpectrum (completedLocalRing 𝒥 x)) :
    (transferPrime hpow hle x p).asIdeal =
      p.asIdeal.map ((completedLocalRingTransferRingEquiv hpow hle x :
        completedLocalRing 𝒥 x →+* completedLocalRing ℐ x)) := by
  rw [PrimeSpectrum.comap_asIdeal]
  exact (Ideal.map_comap_of_equiv (completedLocalRingTransferRingEquiv hpow hle x)).symm

/-- **Depth at corresponding primes agrees**: `depth((ℱ'_x^∧)_𝔭) = depth((ℱ_x^∧)_𝔓)`. -/
public theorem completedStalkDepth_transfer (p : PrimeSpectrum (completedLocalRing 𝒥 x)) :
    completedStalkDepth 𝒥 ((Stacks.Coherent.transferFunctor ℐ 𝒥 a hpow).obj F) x p =
      completedStalkDepth ℐ F x (transferPrime hpow hle x p) := by
  have hP : p.asIdeal.primeCompl.map ((completedLocalRingTransferRingEquiv hpow hle x :
      completedLocalRing 𝒥 x →* completedLocalRing ℐ x)) =
      (transferPrime hpow hle x p).asIdeal.primeCompl := by
    ext t
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, PrimeSpectrum.comap_asIdeal,
      Ideal.mem_comap]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro ht
      exact ⟨(completedLocalRingTransferRingEquiv hpow hle x).symm t, ht, by simp⟩
  -- Transport of the depth of a localization along a semilinear isomorphism; the argument of
  -- the (private) `depth_localizedModule_eq_of_semilinearEquiv` of
  -- `CompletedStalkDepthSpecialization.lean`, specialised here.
  have hsmulLoc : ∀ {A D : Type u} [CommRing A] [CommRing D] (e : A ≃+* D)
      (S : Submonoid A) (T : Submonoid D) (_hST : S.map (e : A →* D) = T)
      {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂] [Algebra A A₁] [Algebra D A₂]
      [IsLocalization S A₁] [IsLocalization T A₂]
      {W₁ W₂ : Type u} [AddCommGroup W₁] [Module A W₁] [Module A₁ W₁] [IsScalarTower A A₁ W₁]
      [AddCommGroup W₂] [Module D W₂] [Module A₂ W₂] [IsScalarTower D A₂ W₂]
      (ε : A₁ ≃+* A₂) (_hε : ∀ a : A, ε (algebraMap A A₁ a) = algebraMap D A₂ (e a))
      (Φ : W₁ ≃+ W₂) (_hΦ : ∀ (a : A) (w : W₁), Φ (a • w) = e a • Φ w)
      (x : A₁) (z : W₁), Φ (x • z) = ε x • Φ z := by
    intro A D _ _ e S T hST A₁ A₂ _ _ _ _ _ _ W₁ W₂ _ _ _ _ _ _ _ _ ε hε Φ hΦ x z
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
    have hes : e (s : A) ∈ T := hST ▸ ⟨(s : A), s.2, rfl⟩
    have hunit : IsUnit (algebraMap D A₂ (e (s : A))) :=
      IsLocalization.map_units A₂ ⟨e (s : A), hes⟩
    refine (hunit.smul_left_cancel (α := A₂)).1 ?_
    have hmul : algebraMap A A₁ (s : A) * IsLocalization.mk' A₁ a s = algebraMap A A₁ a :=
      IsLocalization.mk'_spec' A₁ a s
    calc algebraMap D A₂ (e (s : A)) • Φ (IsLocalization.mk' A₁ a s • z)
        = e (s : A) • Φ (IsLocalization.mk' A₁ a s • z) := by rw [algebraMap_smul]
      _ = Φ ((s : A) • (IsLocalization.mk' A₁ a s • z)) := (hΦ _ _).symm
      _ = Φ ((algebraMap A A₁ (s : A) * IsLocalization.mk' A₁ a s) • z) := by
          rw [mul_smul, algebraMap_smul]
      _ = Φ (a • z) := by rw [hmul, algebraMap_smul]
      _ = e a • Φ z := hΦ a z
      _ = algebraMap D A₂ (e a) • Φ z := by rw [algebraMap_smul]
      _ = (ε (algebraMap A A₁ (s : A)) * ε (IsLocalization.mk' A₁ a s)) • Φ z := by
          rw [← map_mul, hmul, hε]
      _ = algebraMap D A₂ (e (s : A)) • ε (IsLocalization.mk' A₁ a s) • Φ z := by
          rw [mul_smul, hε]
  have key : ∀ {A D : Type u} [CommRing A] [CommRing D] (e : A ≃+* D)
      {M : Type u} [AddCommGroup M] [Module A M] {N : Type u} [AddCommGroup N] [Module D N]
      (φ : M ≃+ N) (hφ : ∀ (a : A) (m : M), φ (a • m) = e a • φ m)
      (p : Ideal A) [p.IsPrime] (P : Ideal D) [P.IsPrime]
      (hP : p.primeCompl.map (e : A →* D) = P.primeCompl),
      Module.depth (Localization.AtPrime p) (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl M) =
        Module.depth (Localization.AtPrime P) (IsLocalRing.maximalIdeal (Localization.AtPrime P))
          (LocalizedModule P.primeCompl N) := by
    intro A D _ _ e M _ _ N _ _ φ hφ p _ P _ hP
    have hmem : ∀ s : p.primeCompl, e (s : A) ∈ P.primeCompl := fun s =>
      hP ▸ ⟨(s : A), s.2, rfl⟩
    have hsurj : ∀ t : P.primeCompl, ∃ s : A, s ∈ p.primeCompl ∧ e s = (t : D) := fun t => by
      have ht : (t : D) ∈ Submonoid.map (e : A →* D) p.primeCompl := by
        rw [hP]; exact t.2
      obtain ⟨s, hs, hst⟩ := ht
      exact ⟨s, hs, hst⟩
    let : Algebra A D := (e : A →+* D).toAlgebra
    let : Module A N := Module.compHom N (e : A →+* D)
    let : Module A (LocalizedModule P.primeCompl N) :=
      Module.compHom (LocalizedModule P.primeCompl N) (e : A →+* D)
    let φ' : M ≃ₗ[A] N := { __ := φ, map_smul' := hφ }
    let mkA : N →ₗ[A] LocalizedModule P.primeCompl N :=
      { toFun := fun n => LocalizedModule.mk n 1
        map_add' := fun x y => (LocalizedModule.mkLinearMap P.primeCompl N).map_add x y
        map_smul' := fun a n => (LocalizedModule.mkLinearMap P.primeCompl N).map_smul (e a) n }
    let g : M →ₗ[A] LocalizedModule P.primeCompl N := mkA ∘ₗ (φ' : M →ₗ[A] N)
    have hgval : ∀ m : M, g m = LocalizedModule.mk (φ m) 1 := fun _ => rfl
    have hg : IsLocalizedModule p.primeCompl g := by
      refine ⟨fun s => ?_, fun y => ?_, fun {m₁ m₂} hm => ?_⟩
      · rw [Module.End.isUnit_iff]
        have hu := IsLocalizedModule.map_units
          (LocalizedModule.mkLinearMap P.primeCompl N) ⟨e (s : A), hmem s⟩
        rw [Module.End.isUnit_iff] at hu
        exact hu
      · obtain ⟨⟨n, t⟩, ht⟩ := IsLocalizedModule.surj P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl N) y
        obtain ⟨s, hs, hst⟩ := hsurj t
        refine ⟨⟨φ.symm n, ⟨s, hs⟩⟩, ?_⟩
        have hy : e s • y = LocalizedModule.mk n 1 := by
          rw [hst]; exact ht
        rw [hgval, φ.apply_symm_apply]
        exact hy
      · have h1 : LocalizedModule.mk (φ m₁) (1 : P.primeCompl) = LocalizedModule.mk (φ m₂) 1 := hm
        obtain ⟨t, hts⟩ := IsLocalizedModule.exists_of_eq
          (S := P.primeCompl) (f := LocalizedModule.mkLinearMap P.primeCompl N) h1
        obtain ⟨s, hs, hst⟩ := hsurj t
        have h2 : e s • φ m₁ = e s • φ m₂ := by
          rw [hst]; exact hts
        have h3 : s • m₁ = s • m₂ := by
          refine φ.injective ?_
          rw [hφ, hφ]
          exact h2
        exact ⟨⟨s, hs⟩, h3⟩
    let Φ₀ : LocalizedModule p.primeCompl M ≃ₗ[A] LocalizedModule P.primeCompl N :=
      IsLocalizedModule.iso p.primeCompl g
    let ε : Localization.AtPrime p ≃+* Localization.AtPrime P :=
      IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p) (Localization.AtPrime P) e hP
    have hε : ∀ a : A, ε (algebraMap A (Localization.AtPrime p) a) =
        algebraMap D (Localization.AtPrime P) (e a) := fun a =>
      IsLocalization.ringEquivOfRingEquiv_eq _ a
    have hΦ : ∀ (a : A) (w : LocalizedModule p.primeCompl M),
        Φ₀.toAddEquiv (a • w) = e a • Φ₀.toAddEquiv w := fun a w => Φ₀.map_smul a w
    have hsemi := hsmulLoc e p.primeCompl P.primeCompl hP ε hε
      Φ₀.toAddEquiv hΦ
    have h := Module.depth_eq_of_semilinearEquiv ε
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) Φ₀.toAddEquiv hsemi
    rw [h]
    congr 1
    exact IsLocalRing.map_ringEquiv_maximalIdeal ε
  exact key (completedLocalRingTransferRingEquiv hpow hle x)
    (completedStalkTransferEquiv hpow hle F x).toAddEquiv
    (completedStalkTransferEquiv_toAddEquiv_smul hpow hle F x) p.asIdeal
    (transferPrime hpow hle x p).asIdeal hP

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **Dimension at corresponding primes agrees**: `dim(𝒪^∧/𝔭) = dim(𝒪^∧/𝔓)`. -/
public theorem ringKrullDim_quotient_transfer (p : PrimeSpectrum (completedLocalRing 𝒥 x)) :
    ringKrullDim (completedLocalRing 𝒥 x ⧸ p.asIdeal) =
      ringKrullDim (completedLocalRing ℐ x ⧸ (transferPrime hpow hle x p).asIdeal) :=
  ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _
    (completedLocalRingTransferRingEquiv hpow hle x) (transferPrime_asIdeal hpow hle x p))

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The comparison commutes with the structure maps from `𝒪_{X,x}`. -/
theorem completedLocalRingTransferRingEquiv_comp_algebraMap :
    ((completedLocalRingTransferRingEquiv hpow hle x : completedLocalRing 𝒥 x →+*
        completedLocalRing ℐ x)).comp (algebraMap (X.presheaf.stalk x) (completedLocalRing 𝒥 x)) =
      algebraMap (X.presheaf.stalk x) (completedLocalRing ℐ x) :=
  RingHom.ext fun r => (completedLocalRingTransferEquiv hpow hle x).commutes r

omit [AlgebraicGeometry.IsNoetherian X] in
include hpow hle in
/-- A prime of the `ℐ`-adic completion contains `𝒥_x` exactly when it contains `ℐ𝒪_{X,x}^∧`. -/
theorem map_stalk_le_iff_completedLocalIdeal_le (Q : Ideal (completedLocalRing ℐ x))
    [Q.IsPrime] :
    (IdealSheafData.stalk 𝒥 x).map (algebraMap (X.presheaf.stalk x) (completedLocalRing ℐ x)) ≤ Q ↔
      completedLocalIdeal ℐ x ≤ Q := by
  refine ⟨fun h => Ideal.IsPrime.le_of_pow_le (n := a) (le_trans ?_ h),
    le_trans (Ideal.map_mono (IdealSheafData.stalk_mono hle x))⟩
  rw [completedLocalIdeal, ← Ideal.map_pow]
  exact Ideal.map_mono (IdealSheafData.stalk_pow_le hpow x)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- An ideal contains `𝒥𝒪_{X,x}^∧` exactly when its image contains `𝒥_x`. -/
theorem completedLocalIdeal_le_iff_map_le (q : Ideal (completedLocalRing 𝒥 x)) :
    completedLocalIdeal 𝒥 x ≤ q ↔
      (IdealSheafData.stalk 𝒥 x).map (algebraMap (X.presheaf.stalk x) (completedLocalRing ℐ x)) ≤
        q.map ((completedLocalRingTransferRingEquiv hpow hle x : completedLocalRing 𝒥 x →+*
          completedLocalRing ℐ x)) := by
  rw [← completedLocalRingTransferRingEquiv_comp_algebraMap hpow hle x, ← Ideal.map_map,
    map_le_map_iff_of_ringEquiv]

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **`𝔭 ∉ V(𝒥𝒪_{X,x}^∧)` exactly when `𝔓 ∉ V(ℐ𝒪_{X,x}^∧)`.** -/
public theorem completedLocalIdeal_le_transfer_iff (p : PrimeSpectrum (completedLocalRing 𝒥 x)) :
    completedLocalIdeal 𝒥 x ≤ p.asIdeal ↔
      completedLocalIdeal ℐ x ≤ (transferPrime hpow hle x p).asIdeal := by
  rw [completedLocalIdeal_le_iff_map_le hpow hle x, ← transferPrime_asIdeal hpow hle x p]
  exact map_stalk_le_iff_completedLocalIdeal_le hpow hle x _

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The comparison carries `𝔪_x^∧` to `𝔪_x^∧`. -/
theorem map_completedMaximalIdeal_transfer :
    (completedMaximalIdeal 𝒥 x).map ((completedLocalRingTransferRingEquiv hpow hle x :
        completedLocalRing 𝒥 x →+* completedLocalRing ℐ x)) = completedMaximalIdeal ℐ x := by
  rw [completedMaximalIdeal, Ideal.map_map, completedLocalRingTransferRingEquiv_comp_algebraMap]

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **`V(𝔭) ∩ V(𝒥𝒪_{X,x}^∧) = {𝔪_x^∧}` exactly when `V(𝔓) ∩ V(ℐ𝒪_{X,x}^∧) = {𝔪_x^∧}`.** -/
public theorem adicClosedFibreThrough_transfer_eq_singleton_iff
    (p : PrimeSpectrum (completedLocalRing 𝒥 x)) :
    adicClosedFibreThrough 𝒥 x p = {completedMaximalIdeal 𝒥 x} ↔
      adicClosedFibreThrough ℐ x (transferPrime hpow hle x p) = {completedMaximalIdeal ℐ x} := by
  set e := completedLocalRingTransferRingEquiv hpow hle x
  let f : Ideal (completedLocalRing 𝒥 x) → Ideal (completedLocalRing ℐ x) :=
    fun q => q.map (e : completedLocalRing 𝒥 x →+* completedLocalRing ℐ x)
  have hfinj : Function.Injective f := fun q q' h =>
    le_antisymm ((map_le_map_iff_of_ringEquiv e).mp h.le) ((map_le_map_iff_of_ringEquiv e).mp h.ge)
  have hfsurj : Function.Surjective f := fun Q =>
    ⟨Q.comap (e : completedLocalRing 𝒥 x →+* completedLocalRing ℐ x),
      Ideal.map_comap_of_surjective _ e.surjective Q⟩
  have hprime : ∀ q : Ideal (completedLocalRing 𝒥 x), (f q).IsPrime ↔ q.IsPrime := fun q => by
    simp only [f]
    rw [Ideal.map_comap_of_equiv]
    refine ⟨fun h => ?_, fun h => Ideal.IsPrime.comap _⟩
    have := Ideal.IsPrime.comap (e : completedLocalRing 𝒥 x →+* completedLocalRing ℐ x) (hK := h)
    have heq : Ideal.comap (e : completedLocalRing 𝒥 x →+* completedLocalRing ℐ x)
        (Ideal.comap e.symm q) = q := by
      ext t
      simp
    rwa [heq] at this
  have himage : adicClosedFibreThrough ℐ x (transferPrime hpow hle x p) =
      f '' adicClosedFibreThrough 𝒥 x p := by
    ext Q
    obtain ⟨q, rfl⟩ := hfsurj Q
    rw [hfinj.mem_set_image]
    simp only [adicClosedFibreThrough, Set.mem_setOf_eq, transferPrime_asIdeal]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hq := (hprime q).mp h1
      have := h1
      exact ⟨hq, (map_le_map_iff_of_ringEquiv e).mp h2,
        (completedLocalIdeal_le_iff_map_le hpow hle x q).mpr
          ((map_stalk_le_iff_completedLocalIdeal_le hpow hle x (f q)).mpr h3)⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' := (hprime q).mpr h1
      exact ⟨h1', (map_le_map_iff_of_ringEquiv e).mpr h2,
        (map_stalk_le_iff_completedLocalIdeal_le hpow hle x (f q)).mp
          ((completedLocalIdeal_le_iff_map_le hpow hle x q).mp h3)⟩
  rw [himage, ← map_completedMaximalIdeal_transfer hpow hle x]
  show _ ↔ f '' _ = {f (completedMaximalIdeal 𝒥 x)}
  rw [← Set.image_singleton (f := f)]
  exact (Set.image_injective.mpr hfinj).eq_iff.symm

end Transfer

end Stacks.Algebraization

end
