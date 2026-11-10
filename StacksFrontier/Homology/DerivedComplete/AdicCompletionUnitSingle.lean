module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.RingTheory.AdicCompletion.Flat

/-!
# The derived completion unit at a module, normalized against the ordinary completion

Let `I` be a finitely generated ideal of a commutative ring `A` and let `M` be an `A`-module.
Derived `I`-adic completion is a reflection of `D(A)` onto the derived `I`-complete objects,
with unit `η`; the question answered here is what `η` does at the object `M[0]`.

Suppose one knows — by whatever means, typically [Stacks, Tag 0EEU] — that `M[0]^∧` is
*isomorphic* to `N[0]` for some `I`-adically complete module `N`, with no compatibility between
that isomorphism and `η`.  Then the composite `M ⟶ N` obtained from `η` through the
isomorphism, `M[0] ⟶ M[0]^∧ ≅ N[0]`, read back across the fully faithful functor
`DerivedCategory.singleFunctor _ 0`, is universal among maps of `M` into `I`-adically complete
modules: that is exactly the universal property of `η` restricted to the objects `P[0]` with `P`
adically complete, each of which is derived complete by [Stacks, Tag 091R].  A map with that
universal property identifies its target with Mathlib's `AdicCompletion I M` compatibly with
`AdicCompletion.of I M`, so the isomorphism can be *normalized*: there is an isomorphism
`M[0]^∧ ≅ (AdicCompletion I M)[0]` whose composite with `η` is the ordinary completion map.

The consequence that the consumers want is that derived completion **inverts** the ordinary
completion map `M ⟶ AdicCompletion I M`, and more generally inverts any map `u : P ⟶ Q` which
is the ordinary completion map up to an isomorphism of its target.

## Main results

* `Stacks.Algebraization.bijective_comp_adicCompletion_of` — the universal property of the
  ordinary `I`-adic completion among `I`-adically complete modules.
* `Stacks.Algebraization.adicCompletionEquivOfUniversal` — a map with that universal property
  identifies its target with `AdicCompletion I M`, compatibly with `AdicCompletion.of I M`.
* `Stacks.Algebraization.exists_iso_adicCompletionFunctor_single_normalized` — the normalized
  identification of `M[0]^∧`.
* `Stacks.Algebraization.isIso_adicCompletionFunctor_map_single_map` — derived completion
  inverts a map of modules which is the ordinary completion map up to an isomorphism.

## References

* [Stacks Project, Tag 091R](https://stacks.math.columbia.edu/tag/091R)
* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Algebraization

section ModuleUniversal

variable {A : Type u} [CommRing A]

/-- **Precomposition with the completion map is injective on maps into a Hausdorff module.**
Two maps out of `AdicCompletion I M` agreeing on the image of `M` agree modulo `Iⁿ` for every
`n`, because every element of the completion agrees modulo `Iⁿ` with an element of that image. -/
theorem injective_comp_adicCompletion_of (I : Ideal A) (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] [IsHausdorff I N] :
    Function.Injective
      (fun f : AdicCompletion I M →ₗ[A] N ↦ f.comp (AdicCompletion.of I M)) := by
  intro f g h
  refine LinearMap.ext fun x ↦ sub_eq_zero.mp (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)
  rw [SModEq.sub_mem, sub_zero]
  obtain ⟨m, hm⟩ := (I ^ n • (⊤ : Submodule A M)).mkQ_surjective
    (AdicCompletion.eval I M n x)
  have hx : x - AdicCompletion.of I M m ∈
      I ^ n • (⊤ : Submodule A (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker,
      map_sub, AdicCompletion.eval_of, hm, sub_self]
  have hq : (f - g) (AdicCompletion.of I M m) = 0 :=
    sub_eq_zero.mpr (LinearMap.congr_fun h m)
  have hmem : (f - g) (x - AdicCompletion.of I M m) ∈ I ^ n • (⊤ : Submodule A N) := by
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      rw [(f - g).map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro y z hy hz
      rw [(f - g).map_add]
      exact Submodule.add_mem _ hy hz
  change (f - g) x ∈ I ^ n • (⊤ : Submodule A N)
  simpa only [map_sub, hq, sub_zero] using hmem

/-- **The universal property of the ordinary `I`-adic completion.** For `I` finitely generated,
precomposition with `AdicCompletion.of I M` identifies the maps `AdicCompletion I M →ₗ N` with
the maps `M →ₗ N`, for every `I`-adically complete `N`. -/
theorem bijective_comp_adicCompletion_of (I : Ideal A) (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] [IsAdicComplete I N] :
    Function.Bijective
      (fun f : AdicCompletion I M →ₗ[A] N ↦ f.comp (AdicCompletion.of I M)) := by
  refine ⟨injective_comp_adicCompletion_of I hI M N, fun f ↦ ?_⟩
  refine ⟨(AdicCompletion.ofLinearEquiv I N).symm.toLinearMap.comp
    ((AdicCompletion.map I f).restrictScalars A), ?_⟩
  ext x
  change (AdicCompletion.ofLinearEquiv I N).symm
    (AdicCompletion.map I f (AdicCompletion.of I M x)) = f x
  rw [AdicCompletion.map_of]
  exact (AdicCompletion.ofLinearEquiv I N).symm_apply_apply (f x)

/-- **A universal map into an adically complete module is the completion map.** If
`φ : M →ₗ N` with `N` `I`-adically complete is universal among maps of `M` into `I`-adically
complete modules, then `N` is the `I`-adic completion of `M` over `φ`. -/
def adicCompletionEquivOfUniversal (I : Ideal A) (hI : I.FG)
    (M N : Type v) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [IsAdicComplete I N] (φ : M →ₗ[A] N)
    (hφ : ∀ (P : Type v) [AddCommGroup P] [Module A P] [IsAdicComplete I P],
      Function.Bijective (fun f : N →ₗ[A] P ↦ f.comp φ)) :
    {e : N ≃ₗ[A] AdicCompletion I M //
      e.toLinearMap.comp φ = AdicCompletion.of I M} := by
  letI : IsAdicComplete I (AdicCompletion I M) := AdicCompletion.isAdicComplete hI
  apply Classical.choice
  obtain ⟨f, hf⟩ := (hφ (AdicCompletion I M)).surjective (AdicCompletion.of I M)
  obtain ⟨g, hg⟩ := (bijective_comp_adicCompletion_of I hI M N).surjective φ
  change f.comp φ = AdicCompletion.of I M at hf
  change g.comp (AdicCompletion.of I M) = φ at hg
  have hgf : g.comp f = LinearMap.id := by
    refine (hφ N).injective ?_
    rw [LinearMap.comp_assoc, hf, hg, LinearMap.id_comp]
  have hfg : f.comp g = LinearMap.id := by
    refine injective_comp_adicCompletion_of I hI M (AdicCompletion I M) ?_
    change (f.comp g).comp (AdicCompletion.of I M) = LinearMap.id.comp (AdicCompletion.of I M)
    rw [LinearMap.comp_assoc, hg, hf, LinearMap.id_comp]
  exact ⟨⟨LinearEquiv.ofLinearMap f g hfg hgf, hf⟩⟩

end ModuleUniversal

section Normalized

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

/-- **Normalizing an identification of the derived completion of a module.** An isomorphism
`M[0]^∧ ≅ N[0]` with `N` `I`-adically complete can be replaced by one onto
`(AdicCompletion I M)[0]` whose composite with the completion unit is the ordinary completion
map `M ⟶ AdicCompletion I M`. -/
theorem exists_iso_adicCompletionFunctor_single_normalized (I : Ideal A) (hI : I.FG)
    (M N : ModuleCat.{u} A) [IsAdicComplete I (N : Type u)]
    (e : (adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) :
    ∃ e' : (adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I (M : Type u))),
      (adicCompletionUnit A I hI).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫ e'.hom =
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          (ModuleCat.ofHom (AdicCompletion.of I (M : Type u))) := by
  set S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  set η := (adicCompletionUnit A I hI).app (S.obj M)
  set φ : M ⟶ N := S.preimage (η ≫ e.hom)
  have hφ : S.map φ = η ≫ e.hom := S.map_preimage _
  have hu : ∀ (P : Type u) [AddCommGroup P] [Module A P] [IsAdicComplete I P],
      Function.Bijective (fun g : (N : Type u) →ₗ[A] P ↦ g.comp φ.hom) := by
    intro P _ _ _
    have hP : IsDerivedComplete I (S.obj (ModuleCat.of A P)) :=
      (isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective
        A I P).1 inferInstance
    have hb := completionUnit_comp_bijective I hI (S.obj M) (S.obj (ModuleCat.of A P)) hP
    constructor
    · intro g h he
      have he' : φ ≫ ModuleCat.ofHom g = φ ≫ ModuleCat.ofHom h := ModuleCat.hom_ext he
      have hgh : e.hom ≫ S.map (ModuleCat.ofHom g) = e.hom ≫ S.map (ModuleCat.ofHom h) :=
        hb.injective (by
          change η ≫ _ = η ≫ _
          simpa only [Functor.map_comp, hφ, Category.assoc] using congrArg S.map he')
      exact congrArg ModuleCat.Hom.hom (S.map_injective ((cancel_epi e.hom).mp hgh))
    · intro g
      obtain ⟨k, hk⟩ := hb.surjective (S.map (ModuleCat.ofHom g))
      refine ⟨(S.preimage (e.inv ≫ k) : N ⟶ ModuleCat.of A P).hom, ?_⟩
      change (φ ≫ S.preimage (e.inv ≫ k)).hom = (ModuleCat.ofHom g).hom
      refine congrArg ModuleCat.Hom.hom (S.map_injective ?_)
      rw [Functor.map_comp, hφ, S.map_preimage]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hk
  set a := adicCompletionEquivOfUniversal I hI (M : Type u) (N : Type u) φ.hom hu
  refine ⟨e ≪≫ S.mapIso a.1.toModuleIso, ?_⟩
  change η ≫ e.hom ≫ S.map a.1.toModuleIso.hom = _
  rw [← Category.assoc, ← hφ, ← S.map_comp]
  exact congrArg S.map (ModuleCat.hom_ext a.2)

/-- **Derived completion inverts the ordinary completion map**, as soon as the derived
completion of the module is known to be a single adically complete module. -/
theorem isIso_adicCompletionFunctor_map_single_adicCompletion_of (I : Ideal A) (hI : I.FG)
    (M N : ModuleCat.{u} A) [IsAdicComplete I (N : Type u)]
    (hiso : Nonempty ((adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) :
    IsIso ((adicCompletionFunctor A I hI).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (AdicCompletion.of I (M : Type u))))) := by
  obtain ⟨e⟩ := hiso
  obtain ⟨e', he'⟩ := exists_iso_adicCompletionFunctor_single_normalized I hI M N e
  rw [← he', Functor.map_comp]
  have h₁ : IsIso ((adicCompletionFunctor A I hI).map
      ((adicCompletionUnit A I hI).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) :=
    isIso_completionFunctor_map_completionUnit I hI _
  infer_instance

/-- **Derived completion inverts any map of modules which is the ordinary completion map up to
an isomorphism of its target.** -/
theorem isIso_adicCompletionFunctor_map_single_map (I : Ideal A) (hI : I.FG)
    (P Q N : ModuleCat.{u} A) [IsAdicComplete I (N : Type u)] (u : P ⟶ Q)
    (ε : (Q : Type u) ≃ₗ[A] AdicCompletion I (P : Type u))
    (hε : ε.toLinearMap.comp u.hom = AdicCompletion.of I (P : Type u))
    (hiso : Nonempty ((adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj P) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) :
    IsIso ((adicCompletionFunctor A I hI).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map u)) := by
  have hu : u = ModuleCat.ofHom (AdicCompletion.of I (P : Type u)) ≫
      ModuleCat.ofHom ε.symm.toLinearMap := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    change u.hom x = ε.symm (AdicCompletion.of I (P : Type u) x)
    rw [← LinearMap.congr_fun hε x]
    exact (ε.symm_apply_apply (u.hom x)).symm
  rw [hu, Functor.map_comp, Functor.map_comp]
  have h₁ := isIso_adicCompletionFunctor_map_single_adicCompletion_of I hI P N hiso
  have h₂ : IsIso ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
      (ModuleCat.ofHom ε.symm.toLinearMap)) := by
    have : IsIso (ModuleCat.ofHom ε.symm.toLinearMap :
        ModuleCat.of A (AdicCompletion I (P : Type u)) ⟶ Q) :=
      ⟨ModuleCat.ofHom ε.toLinearMap, by
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
        exact ε.apply_symm_apply x, by
        refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
        exact ε.symm_apply_apply x⟩
    infer_instance
  infer_instance

end Normalized

section AdicTower

variable {A : Type u} [CommRing A]

open Opposite

/-- **A tower of surjections out of `P` with kernels the ideal powers is the tower of adic
quotients of `P`.** The identification is the one induced by the maps `c n` on the quotients. -/
def adicQuotientTowerIso (I : Ideal A) (P : ModuleCat.{u} A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (c : ∀ n : ℕ, P ⟶ T.obj (op n))
    (hc : ∀ (m n : ℕ) (h : m ≤ n), c n ≫ T.map (homOfLE h).op = c m)
    (hsurj : ∀ n, Function.Surjective (c n).hom)
    (hker : ∀ n, LinearMap.ker (c n).hom = I ^ n • (⊤ : Submodule A (P : Type u))) :
    quotientTower I (P : Type u) ≅ T := by
  refine NatIso.ofComponents (fun n ↦
    (LinearEquiv.ofBijective
      (Submodule.liftQ (I ^ n.unop • (⊤ : Submodule A (P : Type u))) (c n.unop).hom
        (hker n.unop).ge) ⟨?_, ?_⟩).toModuleIso) ?_
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (hker n.unop).le
  · intro y
    obtain ⟨x, hx⟩ := hsurj n.unop y
    exact ⟨Submodule.Quotient.mk x, hx⟩
  · intro j k f
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    refine Submodule.Quotient.induction_on _ y fun x ↦ ?_
    have hle : k.unop ≤ j.unop := leOfHom f.unop
    have hcc := congrArg (fun g : P ⟶ T.obj (op k.unop) ↦ g.hom x) (hc k.unop j.unop hle)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hcc
    change (c k.unop).hom x = (T.map f).hom ((c j.unop).hom x)
    exact hcc.symm

/-- The identification of `adicQuotientTowerIso` transforms the quotient map into `c n`. -/
theorem mkQ_comp_adicQuotientTowerIso_hom_app (I : Ideal A) (P : ModuleCat.{u} A)
    (T : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c : ∀ n : ℕ, P ⟶ T.obj (op n))
    (hc : ∀ (m n : ℕ) (h : m ≤ n), c n ≫ T.map (homOfLE h).op = c m)
    (hsurj : ∀ n, Function.Surjective (c n).hom)
    (hker : ∀ n, LinearMap.ker (c n).hom = I ^ n • (⊤ : Submodule A (P : Type u))) (n : ℕ) :
    ModuleCat.ofHom (Submodule.mkQ (I ^ n • (⊤ : Submodule A (P : Type u)))) ≫
        (adicQuotientTowerIso I P T c hc hsurj hker).hom.app (op n) = c n :=
  ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

/-- **Derived completion inverts the canonical map from a module into the limit of its adic
quotients**, presented as a tower of surjections with kernels the ideal powers, as soon as the
derived completion of the module is known to be a single adically complete module. -/
theorem isIso_adicCompletionFunctor_map_single_map_of_adicTower (I : Ideal A) (hI : I.FG)
    (P : ModuleCat.{u} A) (T : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (c : ∀ n : ℕ, P ⟶ T.obj (op n))
    (hc : ∀ (m n : ℕ) (h : m ≤ n), c n ≫ T.map (homOfLE h).op = c m)
    (hsurj : ∀ n, Function.Surjective (c n).hom)
    (hker : ∀ n, LinearMap.ker (c n).hom = I ^ n • (⊤ : Submodule A (P : Type u)))
    (Qc : Cone T) (hQc : IsLimit Qc) (u : P ⟶ Qc.pt)
    (hu : ∀ n : ℕ, u ≫ Qc.π.app (op n) = c n)
    (N : ModuleCat.{u} A) [IsAdicComplete I (N : Type u)]
    (hiso : Nonempty ((adicCompletionFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj P) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) :
    IsIso ((adicCompletionFunctor A I hI).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map u)) := by
  set τ := adicQuotientTowerIso I P T c hc hsurj hker
  set cone' : Cone T := (Cone.postcompose τ.hom).obj (adicCompletionCone I (P : Type u))
  have hcone' : IsLimit cone' :=
    (IsLimit.postcomposeHomEquiv τ _).symm (adicCompletionIsLimit I (P : Type u))
  set ι : Qc.pt ≅ cone'.pt := hQc.conePointUniqueUpToIso hcone'
  have hι : ∀ n : ℕ, ι.hom ≫ cone'.π.app (op n) = Qc.π.app (op n) := fun n ↦
    IsLimit.conePointUniqueUpToIso_hom_comp hQc hcone' (op n)
  have hmain : u ≫ ι.hom =
      (ModuleCat.ofHom (AdicCompletion.of I (P : Type u)) : P ⟶ cone'.pt) := by
    refine (adicCompletionIsLimit I (P : Type u)).hom_ext ?_
    rintro ⟨n⟩
    refine (cancel_mono (τ.hom.app (op n))).1 ?_
    have hcomp : (adicCompletionCone I (P : Type u)).π.app (op n) ≫ τ.hom.app (op n) =
        cone'.π.app (op n) := rfl
    have e1 : ((u ≫ ι.hom) ≫ (adicCompletionCone I (P : Type u)).π.app (op n)) ≫
        τ.hom.app (op n) = c n := by
      rw [Category.assoc, Category.assoc, hcomp, hι n, hu n]
    have h0 : (ModuleCat.ofHom (AdicCompletion.of I (P : Type u)) : P ⟶ cone'.pt) ≫
        (adicCompletionCone I (P : Type u)).π.app (op n) =
        ModuleCat.ofHom (Submodule.mkQ (I ^ n • (⊤ : Submodule A (P : Type u)))) :=
      ModuleCat.hom_ext (LinearMap.ext fun x ↦ AdicCompletion.eval_of I (P : Type u) n x)
    have e2 : ((ModuleCat.ofHom (AdicCompletion.of I (P : Type u)) : P ⟶ cone'.pt) ≫
        (adicCompletionCone I (P : Type u)).π.app (op n)) ≫ τ.hom.app (op n) = c n := by
      rw [h0]
      exact mkQ_comp_adicQuotientTowerIso_hom_app I P T c hc hsurj hker n
    exact e1.trans e2.symm
  exact isIso_adicCompletionFunctor_map_single_map I hI P Qc.pt N u ι.toLinearEquiv
    (LinearMap.ext fun x ↦ congrArg (fun g : P ⟶ cone'.pt ↦ g.hom x) hmain) hiso

end AdicTower

end Stacks.Algebraization

end
