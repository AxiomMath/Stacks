module

public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteFlatTensor
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# Maps from the adic completion of a flat module into a derived complete module

Let `A` be a Noetherian ring, `I ⊂ A` an ideal and `P` a flat `A`-module. The canonical map
`P ⟶ P^∧` into the `I`-adic completion is a derived completion of `P`: every `A`-linear map from
`P` into a derived complete `A`-module `M` extends uniquely along it to `P^∧`. In other words,
precomposition with `P ⟶ P^∧` is a bijection
`Hom_A(P^∧, M) ≃ Hom_A(P, M)`
whenever `M` is derived complete with respect to `I`.

## Main results

* `AdicCompletionFlatTensor.isDerivedCompleteModule_of_pow_smul_eq_bot`: a module killed by a
  power of `I` is derived complete.
* `AdicCompletionFlatTensor.exists_bijective_comp_of_flat`: some map `P ⟶ P^∧` has the universal
  property.
* `AdicCompletionFlatTensor.bijective_comp_adicCompletionOf`: the canonical map `P ⟶ P^∧` has
  the universal property.

## Implementation notes

The first step is the derived completion of `P`. By [Stacks, Tag 0EET] there is a left adjoint
`L` to the inclusion of the derived complete objects of `D(A)`, and by [Stacks, Tag 0EEU] its
value on `P[0]` is `P^∧[0]` up to an isomorphism. This produces a map `j : P ⟶ P^∧` with the
universal property, but the isomorphism of [Stacks, Tag 0EEU] is not asserted to be compatible
with the canonical map, so `j` is a priori unrelated to `AdicCompletion.of`.

The second step compares the two. The universal property of `j`, applied to the derived complete
module `P^∧`, gives `g : P^∧ ⟶ P^∧` with `g ∘ j = of`. Modules killed by `Iⁿ` are derived
complete, so the universal property of `j` also applies to `P/IⁿP` and to `P^∧/IⁿP^∧`; this
shows that the composite of `g` with the projection `P^∧ ⟶ P/IⁿP` has kernel exactly `IⁿP^∧`,
for every `n`. Since `P^∧` is the limit of the `P/IⁿP` and is `I`-adically complete, `g` is
bijective, and the universal property passes from `j` to `of`.

The ring and the modules lie in one universe, which is where [Stacks, Tag 0EEU] is available.

## References

* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
* [Stacks Project, Tag 0EET](https://stacks.math.columbia.edu/tag/0EET)
* [Stacks Project, Tag 091R](https://stacks.math.columbia.edu/tag/091R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AdicCompletionFlatTensor

variable {A : Type u} [CommRing A] (I : Ideal A)

attribute [local instance] KoszulCompletion.derivedCountableProducts

/-- A module killed by a power of `I` is derived complete with respect to `I`. -/
theorem isDerivedCompleteModule_of_pow_smul_eq_bot {M : Type u} [AddCommGroup M] [Module A M]
    (n : ℕ) (h : I ^ n • (⊤ : Submodule A M) = ⊥) :
    IsDerivedCompleteModule I (ModuleCat.of A M) := by
  rw [DerivedCompleteRecurrence.isDerivedCompleteModule_iff_forall_bijective_recurrence]
  intro f hf
  apply (DerivedCompleteRecurrence.isIso_oneSubSmulShift_moduleCat_iff (ModuleCat.of A M) f).mp
  rw [← isDerivedCompleteAt_iff_isIso]
  apply isDerivedCompleteAt_of_isNilpotent
  refine ⟨n, ?_⟩
  ext1
  rw [smul_id_pow, End.zero_asHom]
  apply ModuleCat.hom_ext
  ext m
  change f ^ n • m = 0
  have hm : f ^ n • m ∈ I ^ n • (⊤ : Submodule A M) :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow hf n) Submodule.mem_top
  rwa [h, Submodule.mem_bot] at hm

/-- The quotient of a module by `Iⁿ` times it is killed by `Iⁿ`. -/
theorem pow_smul_top_quotient_eq_bot (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ) :
    I ^ n • (⊤ : Submodule A (M ⧸ (I ^ n • ⊤ : Submodule A M))) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
  · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [Submodule.mem_bot, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · exact Submodule.add_mem _ hy hz

/-- A linear map into a module killed by `Iⁿ` kills `Iⁿ` times its source. -/
theorem pow_smul_top_le_ker {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (n : ℕ) (hN : I ^ n • (⊤ : Submodule A N) = ⊥) (φ : M →ₗ[A] N) :
    I ^ n • (⊤ : Submodule A M) ≤ LinearMap.ker φ := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
  · rw [LinearMap.mem_ker, map_smul]
    have : a • φ y ∈ I ^ n • (⊤ : Submodule A N) :=
      Submodule.smul_mem_smul ha Submodule.mem_top
    rwa [hN] at this
  · exact Submodule.add_mem _ hy hz

/-- An endomorphism `g` of `P^∧` is bijective when, for every `n`, its composite with the
projection `P^∧ ⟶ P/IⁿP` is surjective with kernel `Iⁿ P^∧`. -/
private theorem bijective_of_ker_eval_comp (hfg : I.FG) {P : Type u} [AddCommGroup P] [Module A P]
    (g : AdicCompletion I P →ₗ[A] AdicCompletion I P)
    (hker : ∀ n x, AdicCompletion.eval I P n (g x) = 0 ↔
      x ∈ (I ^ n • ⊤ : Submodule A (AdicCompletion I P)))
    (hsurj : ∀ n, Function.Surjective (AdicCompletion.eval I P n ∘ₗ g)) :
    Function.Bijective g := by
  refine ⟨?_, fun y => ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine AdicCompletion.ext fun n => ?_
    have := (hker n x).1 (by rw [LinearMap.mem_ker.mp hx, map_zero])
    rwa [AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker] at this
  have hp : ∀ n, ∃ x, AdicCompletion.eval I P n (g x) = AdicCompletion.eval I P n y :=
    fun n => hsurj n _
  choose x hp using hp
  have hstep : ∀ n, x n - x (n + 1) ∈ (I ^ n • ⊤ : Submodule A (AdicCompletion I P)) := by
    intro n
    refine (hker n _).1 ?_
    have key : ∀ z, AdicCompletion.eval I P n z =
        AdicCompletion.transitionMap I P (Nat.le_succ n) (AdicCompletion.eval I P (n + 1) z) :=
      fun z => (AdicCompletion.transitionMap_comp_eval_apply I P (Nat.le_succ n) z).symm
    rw [map_sub, map_sub, hp n, key (g (x (n + 1))), hp (n + 1), ← key y, sub_self]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      x m ≡ x n [SMOD (I ^ m • ⊤ : Submodule A (AdicCompletion I P))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem]
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) (hstep n)
  obtain ⟨L, hL⟩ := (AdicCompletion.isAdicComplete hfg).toIsPrecomplete.prec hcauchy
  refine ⟨L, AdicCompletion.ext fun n => ?_⟩
  change AdicCompletion.eval I P n (g L) = AdicCompletion.eval I P n y
  rw [← hp n]
  have := (hker n _).2 ((SModEq.sub_mem).mp (hL n))
  rw [map_sub, map_sub, sub_eq_zero] at this
  exact this.symm

variable [IsNoetherianRing A]

/-- **The derived completion of a flat module, as a module map.** For a flat module `P` over a
Noetherian ring there is an `A`-linear map `j : P ⟶ P^∧` through which every `A`-linear map
from `P` to a derived complete module factors uniquely. -/
theorem exists_bijective_comp_of_flat (P : Type u) [AddCommGroup P] [Module A P]
    [Module.Flat A P] :
    ∃ j : P →ₗ[A] AdicCompletion I P, ∀ (M : Type u) [AddCommGroup M] [Module A M],
      IsDerivedCompleteModule I (ModuleCat.of A M) →
        Function.Bijective (fun g : AdicCompletion I P →ₗ[A] M => g ∘ₗ j) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨L, ⟨adj⟩, hLim, -, -⟩ := AdicCompletionTor.derivedCompletion_homology_shortExact A I T
  obtain ⟨θ⟩ := ((derivedCompletion_iso_adicCompletion_of_finite_tensor_flat_and_localization
    A I T) L ⟨adj⟩ hLim).1 A P
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let Pc : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) := fun K ↦ IsDerivedComplete I K
  let e : TensorProduct A A P ≃ₗ[A] P := TensorProduct.lid A P
  let θ' : (L ⋙ Pc.ι).obj (S.obj (ModuleCat.of A P)) ≅
      S.obj (ModuleCat.of A (AdicCompletion I P)) :=
    (L ⋙ Pc.ι).mapIso (S.mapIso e.symm.toModuleIso) ≪≫ θ ≪≫
      S.mapIso ((AdicCompletion.congr I e).restrictScalars A).toModuleIso
  let jD : S.obj (ModuleCat.of A P) ⟶ S.obj (ModuleCat.of A (AdicCompletion I P)) :=
    adj.unit.app _ ≫ θ'.hom
  refine ⟨(S.preimage jD).hom, fun M _ _ hM => ?_⟩
  let Y : Pc.FullSubcategory := ⟨S.obj (ModuleCat.of A M), hM⟩
  refine ⟨fun g₁ g₂ h => ?_, fun ψ => ?_⟩
  · have hS : ∀ g : AdicCompletion I P →ₗ[A] M,
        S.map (ModuleCat.ofHom (g ∘ₗ (S.preimage jD).hom)) = jD ≫ S.map (ModuleCat.ofHom g) :=
      fun g => by
        rw [show ModuleCat.ofHom (g ∘ₗ (S.preimage jD).hom) = S.preimage jD ≫ ModuleCat.ofHom g
          from rfl, S.map_comp, Functor.map_preimage]
    have h' : jD ≫ S.map (ModuleCat.ofHom g₁) = jD ≫ S.map (ModuleCat.ofHom g₂) := by
      rw [← hS, ← hS]
      exact congrArg (fun k => S.map (ModuleCat.ofHom k)) h
    let k : ∀ g : AdicCompletion I P →ₗ[A] M, L.obj (S.obj (ModuleCat.of A P)) ⟶ Y :=
      fun g => Pc.ι.preimage (θ'.hom ≫ S.map (ModuleCat.ofHom g))
    have hk : ∀ g, adj.homEquiv _ Y (k g) = jD ≫ S.map (ModuleCat.ofHom g) := fun g => by
      rw [Adjunction.homEquiv_unit]
      exact (congrArg (fun q => adj.unit.app _ ≫ q)
        (Pc.ι.map_preimage (Y := Y) (θ'.hom ≫ S.map (ModuleCat.ofHom g)))).trans
          (Category.assoc _ _ _).symm
    have hkk : k g₁ = k g₂ := (adj.homEquiv _ Y).injective (by rw [hk, hk, h'])
    exact congrArg ModuleCat.Hom.hom (S.map_injective ((cancel_epi θ'.hom).mp
      (by simpa only [k, Functor.map_preimage] using congrArg Pc.ι.map hkk)))
  · let ψD : S.obj (ModuleCat.of A P) ⟶ Pc.ι.obj Y := S.map (ModuleCat.ofHom ψ)
    let g₀ := (adj.homEquiv _ Y).symm ψD
    have hg₀ : adj.unit.app _ ≫ Pc.ι.map g₀ = ψD :=
      (Adjunction.homEquiv_unit adj _ Y g₀).symm.trans (Equiv.apply_symm_apply _ _)
    let gD : S.obj (ModuleCat.of A (AdicCompletion I P)) ⟶ S.obj (ModuleCat.of A M) :=
      θ'.inv ≫ Pc.ι.map g₀
    refine ⟨(S.preimage gD).hom, ?_⟩
    have : S.map (ModuleCat.ofHom ((S.preimage gD).hom ∘ₗ (S.preimage jD).hom)) =
        S.map (ModuleCat.ofHom ψ) := by
      change S.map (S.preimage jD ≫ S.preimage gD) = ψD
      rw [S.map_comp, Functor.map_preimage, Functor.map_preimage]
      simp only [jD, gD, Category.assoc, Iso.hom_inv_id_assoc]
      exact hg₀
    exact congrArg ModuleCat.Hom.hom (S.map_injective this)

/-- **Maps from the adic completion of a flat module.** Let `A` be a Noetherian ring, `I ⊂ A` an
ideal, `P` a flat `A`-module and `M` an `A`-module derived complete with respect to `I`. Then
every `A`-linear map `P ⟶ M` extends uniquely along the canonical map `P ⟶ P^∧` to the
`I`-adic completion. -/
theorem bijective_comp_adicCompletionOf (P : Type u) [AddCommGroup P] [Module A P]
    [Module.Flat A P] (M : Type u) [AddCommGroup M] [Module A M]
    (hM : IsDerivedCompleteModule I (ModuleCat.of A M)) :
    Function.Bijective
      (fun g : AdicCompletion I P →ₗ[A] M => g ∘ₗ AdicCompletion.of I P) := by
  have hfg : I.FG := I.fg_of_isNoetherianRing
  obtain ⟨j, hj⟩ := exists_bijective_comp_of_flat I P
  let Pc := AdicCompletion I P
  obtain ⟨g, hg⟩ := (hj Pc ((isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective
    A I Pc).1 (AdicCompletion.isAdicComplete hfg))).2 (AdicCompletion.of I P)
  change g ∘ₗ j = AdicCompletion.of I P at hg
  have hegj : ∀ n, (AdicCompletion.eval I P n ∘ₗ g) ∘ₗ j = (I ^ n • ⊤ : Submodule A P).mkQ :=
    fun n => by rw [LinearMap.comp_assoc, hg, AdicCompletion.eval_comp_of]
  have hbij : Function.Bijective g := by
    refine bijective_of_ker_eval_comp I hfg g (fun n x => ⟨fun hx => ?_, fun hx => ?_⟩)
      fun n z => (Submodule.mkQ_surjective _ z).elim fun p hp =>
        ⟨j p, (LinearMap.congr_fun (hegj n) p).trans hp⟩
    · let N := Pc ⧸ (I ^ n • ⊤ : Submodule A Pc)
      let q : Pc →ₗ[A] N := (I ^ n • ⊤ : Submodule A Pc).mkQ
      let d : P ⧸ (I ^ n • ⊤ : Submodule A P) →ₗ[A] N :=
        (I ^ n • ⊤ : Submodule A P).liftQ (q ∘ₗ j)
          (pow_smul_top_le_ker I n (pow_smul_top_quotient_eq_bot I Pc n) _)
      have hdq : d ∘ₗ (AdicCompletion.eval I P n ∘ₗ g) = q := by
        apply (hj N (isDerivedCompleteModule_of_pow_smul_eq_bot I n
          (pow_smul_top_quotient_eq_bot I Pc n))).1
        change (d ∘ₗ (AdicCompletion.eval I P n ∘ₗ g)) ∘ₗ j = q ∘ₗ j
        rw [LinearMap.comp_assoc, hegj n]
        exact Submodule.liftQ_mkQ _ _ _
      have : q x = 0 := by
        rw [← hdq]
        change d (AdicCompletion.eval I P n (g x)) = 0
        rw [hx, map_zero]
      exact (Submodule.Quotient.mk_eq_zero _).mp this
    · exact pow_smul_top_le_ker I n (pow_smul_top_quotient_eq_bot I P n)
        (AdicCompletion.eval I P n ∘ₗ g) hx
  let gE : Pc ≃ₗ[A] Pc := LinearEquiv.ofBijective g hbij
  have hcomp : (fun φ : Pc →ₗ[A] M => φ ∘ₗ AdicCompletion.of I P) =
      (fun φ : Pc →ₗ[A] M => φ ∘ₗ j) ∘ (fun φ : Pc →ₗ[A] M => φ ∘ₗ g) := by
    funext φ
    simp only [Function.comp_apply, LinearMap.comp_assoc, hg]
  rw [hcomp]
  refine (hj M hM).comp ⟨fun φ₁ φ₂ h => ?_, fun φ => ⟨φ ∘ₗ gE.symm.toLinearMap, ?_⟩⟩
  · have hid : g ∘ₗ gE.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun z => gE.apply_symm_apply z
    have := congrArg (fun φ : Pc →ₗ[A] M => φ ∘ₗ gE.symm.toLinearMap) h
    simpa only [LinearMap.comp_assoc, hid, LinearMap.comp_id] using this
  · exact LinearMap.ext fun z => congrArg φ (gE.symm_apply_apply z)

end AdicCompletionFlatTensor
