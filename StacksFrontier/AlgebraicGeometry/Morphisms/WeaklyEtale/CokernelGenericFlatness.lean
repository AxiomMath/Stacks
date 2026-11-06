module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.RingHom.FiniteType
public import StacksFrontier.RingTheory.Flat.GenericFlatness
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Generic flatness of a cokernel

For finite type algebras `R → A → B` over a Noetherian domain, the cokernel of an `A`-linear
map from a finite `A`-module to a finite `B`-module becomes flat over the base after inverting
one nonzero element of `R`.

## Main results

* `Module.exists_flat_localizedModule_coker` gives the required principal localization of the
  cokernel.

## Implementation notes

The cokernel of the underlying `R`-linear map is its target modulo the range. Localization of
this quotient at `f` is canonically the cokernel of the localized map `M_f → N_f`. The
scalar-tower hypotheses express the given actions induced by the chain of ring maps.

The argument is organised around the auxiliary notion of being *generically flat*: admitting a
nonzero element of the base after inverting which the module stays flat along every further flat
base change. That notion is stable under short exact sequences and under quotienting by a
submodule, which is what lets a prime filtration reduce the statement to the case of domains.

## References

* [Stacks Project, Tag 0H40](https://stacks.math.columbia.edu/tag/0H40)
-/

@[expose] public section

open TensorProduct

universe uR uA uB uM uN

/-- A finite module over a finite type algebra is flat after a principal localization. This is
the localized-module form of generic freeness, used for the finite pieces in the filtration
argument. -/
@[sga "1 IV 6.7"]
private theorem exists_flat_localizedModule_of_finite
    {R : Type uR} {A : Type uA} {M : Type uM}
    [CommRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [Module.Finite A M] :
    ∃ f : R, f ≠ 0 ∧
      Module.Flat (Localization.Away f) (LocalizedModule.Away f M) := by
  obtain ⟨f, hf, hfree⟩ :=
    Module.exists_ne_zero_free_localizedModule_away (R := R) (S := A) (M := M)
  refine ⟨f, hf, ?_⟩
  let : Module.Free (Localization.Away f) (LocalizedModule.Away f M) :=
    hfree (Localization.Away f) (LocalizedModule.Away f M)
      (LocalizedModule.mkLinearMap _ _)
  infer_instance

/-- Flatness after inverting an element persists under any further base change on which that
 element is invertible. -/
private theorem flat_tensor_of_flat_away
    {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (f : R) [Module.Flat (Localization.Away f) (LocalizedModule.Away f V)]
    (T : Type*) [CommRing T] [Algebra R T] (hf : IsUnit (algebraMap R T f)) :
    Module.Flat T (T ⊗[R] V) := by
  let : Algebra (Localization.Away f) T :=
    (IsLocalization.Away.lift (S := Localization.Away f) f hf).toAlgebra
  have : IsScalarTower R (Localization.Away f) T :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq f hf r).symm
  have h := IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) V)
  have : Module.Flat (Localization.Away f) (Localization.Away f ⊗[R] V) :=
    Module.Flat.of_linearEquiv h.equiv
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away f) T T V).symm

/-- The generic flatness element can be chosen before the further base change. -/
private theorem exists_flat_tensor_of_finite
    {R A V : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
    [Module.Finite A V] :
    ∃ f : R, f ≠ 0 ∧ ∀ (T : Type uB) [CommRing T] [Algebra R T],
      IsUnit (algebraMap R T f) → Module.Flat T (T ⊗[R] V) := by
  obtain ⟨f, hf, h⟩ := exists_flat_localizedModule_of_finite (R := R) (A := A) (M := V)
  exact ⟨f, hf, fun T _ _ hu => @flat_tensor_of_flat_away R _ V _ _ f h T _ _ hu⟩

/-- Injectivity after tensoring a base changed map can be checked over the original ring. -/
private theorem lTensor_baseChange_injective_iff
    {R S M N X : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    (i : M →ₗ[R] N) :
    Function.Injective ((i.baseChange S).lTensor X) ↔ Function.Injective (i.lTensor X) := by
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S X M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S X N
  have comm (z) : i.lTensor X (eM z) = eN ((i.baseChange S).lTensor X z) :=
    LinearMap.congr_fun
      (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S i) z
  refine ⟨fun h x y hxy => ?_, fun h x y hxy => ?_⟩
  · apply eM.symm.injective
    apply h
    apply eN.injective
    rw [← comm, ← comm, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hxy
  · apply eM.injective
    apply h
    rw [comm, comm, hxy]

/-- Tensoring an injection stays injective over a base change on which its cokernel is flat. -/
private theorem rTensor_injective_of_flat_tensor_coker
    {R A S M N X : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
    [Module.Flat R S] [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
    (u : M →ₗ[A] N) (hu : Function.Injective u)
    [Module.Flat S (S ⊗[R] (N ⧸ LinearMap.range u))] :
    Function.Injective ((u.restrictScalars R).rTensor X) := by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, ← lTensor_baseChange_injective_iff (S := S)]
  have hex := LinearMap.exact_map_mkQ_range u
  exact LinearMap.lTensor_injective_of_exact_of_flat
    (((LinearMap.range u).mkQ.restrictScalars R).baseChange S)
    (LinearMap.lTensor_surjective S (LinearMap.range u).mkQ_surjective)
    ((u.restrictScalars R).baseChange S)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hu)
    (Module.Flat.lTensor_exact S hex) X

/-- A principal localization remains injective after tensoring whenever multiplication by its
 denominator remains injective. -/
private theorem rTensor_injective_localizationAway
    {R A V W X : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]
    [AddCommGroup W] [Module A W] [Module R W] [IsScalarTower R A W]
    [AddCommGroup X] [Module R X]
    (g : A) (l : V →ₗ[A] W) [IsLocalizedModule (Submonoid.powers g) l]
    (hg : IsSMulRegular (V ⊗[R] X) g) :
    Function.Injective ((l.restrictScalars R).rTensor X) := by
  show Function.Injective (TensorProduct.AlgebraTensorModule.rTensor R X l)
  apply (IsLocalizedModule.injective_iff_isRegular (Submonoid.powers g) _).mpr
  rintro ⟨a, ⟨n, rfl⟩⟩
  exact hg.pow n

/-- The image of a finite module in a direct sum uses only finitely many coordinates. -/
private theorem exists_finite_support_of_finite
    {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (ψ : M →ₗ[A] ι →₀ A) :
    ∃ t : Finset ι, ∀ m, (ψ m).support ⊆ t := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite A M)
  let t := s.biUnion fun m => (ψ m).support
  refine ⟨t, fun m => ?_⟩
  have ht : LinearMap.range ψ ≤ Finsupp.supported A A (t : Set ι) := by
    rw [← Submodule.map_top, ← hs, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact fun i hi => Finset.mem_biUnion.mpr ⟨m, hm, hi⟩
  exact ht ⟨m, rfl⟩

/-- A map to a free module over a principal localization comes, after multiplication by a
 denominator, from a map to a finite free module over the original ring. -/
private theorem exists_finite_free_lift
    {A : Type uA} {M : Type uM} {W : Type uN} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (g : A)
    [AddCommGroup W] [Module A W] [Module (Localization.Away g) W]
    [IsScalarTower A (Localization.Away g) W] [Module.Free (Localization.Away g) W]
    (φ : M →ₗ[A] W) :
    ∃ (ι : Type uN) (_ : Fintype ι) (ψ : M →ₗ[A] ι →₀ A)
      (j : (ι →₀ Localization.Away g) →ₗ[A] W)
      (k : W →ₗ[A] ι →₀ Localization.Away g) (s : Submonoid.powers g),
      k.comp j = LinearMap.id ∧
      j.comp ((Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.Away g))).comp ψ)
        = s • φ := by
  classical
  let b := Module.Free.chooseBasis (Localization.Away g) W
  let l := Finsupp.mapRange.linearMap (α := Module.Free.ChooseBasisIndex (Localization.Away g) W)
    (Algebra.linearMap A (Localization.Away g))
  obtain ⟨ψ, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers g) l ((b.repr.toLinearMap.restrictScalars A).comp φ)
  obtain ⟨t, ht⟩ := exists_finite_support_of_finite ψ
  let ψ' : M →ₗ[A] (t : Set (Module.Free.ChooseBasisIndex (Localization.Away g) W)) →₀ A :=
    (Finsupp.lsubtypeDomain
      (t : Set (Module.Free.ChooseBasisIndex (Localization.Away g) W))).comp ψ
  let j : ((t : Set (Module.Free.ChooseBasisIndex (Localization.Away g) W)) →₀
      Localization.Away g) →ₗ[A] W :=
    (b.repr.symm.toLinearMap.restrictScalars A).comp
      (Finsupp.lmapDomain _ A Subtype.val)
  let k : W →ₗ[A] (t : Set (Module.Free.ChooseBasisIndex (Localization.Away g) W)) →₀
      Localization.Away g :=
    (Finsupp.lsubtypeDomain
      (t : Set (Module.Free.ChooseBasisIndex (Localization.Away g) W))).comp
        (b.repr.toLinearMap.restrictScalars A)
  refine ⟨_, inferInstance, ψ', j, k, s, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    show Finsupp.subtypeDomain _ (b.repr (b.repr.symm (Finsupp.mapDomain Subtype.val v))) = v
    rw [LinearEquiv.apply_symm_apply]
    ext i
    exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective v i
  · apply LinearMap.ext
    intro m
    apply b.repr.injective
    have hsm := LinearMap.congr_fun hs m
    simp only [l, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, Submonoid.smul_def] at hsm
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submonoid.smul_def]
    show _ = (b.repr.toLinearMap.restrictScalars A) ((s : A) • φ m)
    rw [map_smul]
    show _ = (s : A) • b.repr (φ m)
    rw [← hsm]
    simp only [j, ψ', LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Finsupp.lmapDomain_apply]
    show Finsupp.mapDomain Subtype.val
      (Finsupp.mapRange _ (map_zero _) (Finsupp.subtypeDomain _ (ψ m))) =
      Finsupp.mapRange _ (map_zero _) (ψ m)
    rw [Finsupp.mapDomain_mapRange _ _ _ _ (map_add _)]
    congr 1
    simpa only [Finsupp.extendDomain_eq_embDomain_subtype, Finsupp.embDomain_eq_mapDomain,
      Function.Embedding.coe_subtype, Finset.mem_coe]
      using Finsupp.extendDomain_subtypeDomain
        (P := fun i => i ∈ (t : Set (Module.Free.ChooseBasisIndex (Localization.Away g) W)))
        (ψ m) (fun i hi => ht m hi)

/-- A finite module embedded in a free module over a principal localization becomes universally
 injective over the base after inverting one element of the base. -/
private theorem exists_rTensor_injective_of_free_localization
    {R A M W : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [Module.FinitePresentation A M] (g : A) (hg : g ≠ 0)
    [AddCommGroup W] [Module A W] [Module R W] [IsScalarTower R A W]
    [Module (Localization.Away g) W] [IsScalarTower A (Localization.Away g) W]
    [Module.Free (Localization.Away g) W]
    (φ : M →ₗ[A] W) (hφ : Function.Injective φ) :
    ∃ f : R, f ≠ 0 ∧ ∀ (T : Type uB) [CommRing T] [Algebra R T] [Module.Flat R T],
      IsUnit (algebraMap R T f) → ∀ (X : Type uN) [AddCommGroup X] [Module T X]
        [Module R X] [IsScalarTower R T X],
        Function.Injective ((φ.restrictScalars R).rTensor X) := by
  obtain ⟨ι, hι, ψ, j, k, s, hkj, hψ⟩ := exists_finite_free_lift g φ
  let F := ι →₀ A
  let l : F →ₗ[A] ι →₀ Localization.Away g :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.Away g))
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply hφ
    apply (IsLocalization.map_units (Localization.Away g) s).smul_left_cancel.mp
    simp only [algebraMap_smul]
    have hx := LinearMap.congr_fun hψ x
    have hy := LinearMap.congr_fun hψ y
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Submonoid.smul_def] using
      hx.symm.trans ((congrArg (j ∘ l) hxy).trans hy)
  let d : F →ₗ[A] F := g • LinearMap.id
  have hd : Function.Injective d := by
    intro x y h
    exact smul_right_injective F hg h
  obtain ⟨f₁, hf₁, h₁⟩ := exists_flat_tensor_of_finite (R := R) (A := A)
    (V := F ⧸ LinearMap.range ψ)
  obtain ⟨f₂, hf₂, h₂⟩ := exists_flat_tensor_of_finite (R := R) (A := A)
    (V := F ⧸ LinearMap.range d)
  refine ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂, fun T _ _ _ hf X _ _ _ _ => ?_⟩
  simp only [map_mul, IsUnit.mul_iff] at hf
  have := h₁ T hf.1
  have := h₂ T hf.2
  have hinjψ := rTensor_injective_of_flat_tensor_coker (R := R) (S := T) (X := X) ψ hψinj
  have hinjd := rTensor_injective_of_flat_tensor_coker (R := R) (S := T) (X := X) d hd
  have hdX : IsSMulRegular (F ⊗[R] X) g := by
    have he : (d.restrictScalars R).rTensor X = g • (LinearMap.id : F ⊗[R] X →ₗ[R] F ⊗[R] X) := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp [d, TensorProduct.smul_tmul']
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [he] at hinjd
    exact hinjd
  have hinjl := rTensor_injective_localizationAway g l hdX
  have hinjj : Function.Injective ((j.restrictScalars R).rTensor X) := by
    intro x y hxy
    have h := congrArg ((k.restrictScalars R).rTensor X) hxy
    simpa only [← LinearMap.rTensor_comp_apply, ← LinearMap.restrictScalars_comp, hkj,
      LinearMap.restrictScalars_id, LinearMap.rTensor_id, LinearMap.id_apply] using h
  have heq : ((j.restrictScalars R).rTensor X).comp
      (((l.restrictScalars R).rTensor X).comp ((ψ.restrictScalars R).rTensor X)) =
      ((s • φ).restrictScalars R).rTensor X := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp,
      ← LinearMap.restrictScalars_comp, ← LinearMap.restrictScalars_comp, hψ]
  have hinj : Function.Injective (((s • φ).restrictScalars R).rTensor X) := by
    rw [← heq]
    exact hinjj.comp (hinjl.comp hinjψ)
  have he : ((s • φ).restrictScalars R).rTensor X =
      (s : A) • ((φ.restrictScalars R).rTensor X) := by
    ext m x
    simp [TensorProduct.smul_tmul', Submonoid.smul_def]
  intro x y hxy
  apply hinj
  simpa only [he, LinearMap.smul_apply] using congrArg (fun z => (s : A) • z) hxy

/-- A quotient with flat middle term is flat if the kernel stays injective under tensoring. -/
private theorem flat_of_rTensor_injective
    {R : Type uR} {P N C : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [AddCommGroup C] [Module R C] [Module.Flat R N]
    (i : P →ₗ[R] N) (p : N →ₗ[R] C) (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    (hi : ∀ (X : Type uR) [AddCommGroup X] [Module R X], Function.Injective (i.rTensor X)) :
    Module.Flat R C := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{uR, uR, _}]
  intro X Y _ _ _ _ g hg
  let q := (LinearMap.range g).mkQ
  have hgq : Function.Exact g q := LinearMap.exact_map_mkQ_range g
  have hq := (LinearMap.range g).mkQ_surjective
  have hpg : q.comp g = 0 := by ext x; exact hgq.apply_apply_eq_zero x
  have hrowX := rTensor_exact X hex hp
  have hrowY := rTensor_exact Y hex hp
  have hcol := lTensor_exact P hgq hq
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective X hp x
  have hnat (u : X →ₗ[R] Y) :
      p.rTensor Y ∘ₗ u.lTensor N = u.lTensor C ∘ₗ p.rTensor X := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hz : p.rTensor Y (g.lTensor N y) = 0 := by
    rw [← LinearMap.comp_apply, hnat, LinearMap.comp_apply]
    exact hx
  obtain ⟨z, hz⟩ := (hrowY _).mp hz
  have hnati : i.rTensor (Y ⧸ LinearMap.range g) ∘ₗ q.lTensor P =
      q.lTensor N ∘ₗ i.rTensor Y := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hzq : q.lTensor P z = 0 := by
    apply hi (Y ⧸ LinearMap.range g)
    rw [map_zero, ← LinearMap.comp_apply, hnati, LinearMap.comp_apply, hz,
      ← LinearMap.lTensor_comp_apply, hpg]
    simp
  obtain ⟨w, hw⟩ := (hcol _).mp hzq
  have hnati' : i.rTensor Y ∘ₗ g.lTensor P = g.lTensor N ∘ₗ i.rTensor X := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hy : y = i.rTensor X w := by
    apply Module.Flat.lTensor_preserves_injective_linearMap g hg
    rw [← hz, ← hw, ← LinearMap.comp_apply, hnati', LinearMap.comp_apply]
  rw [hy]
  exact hrowX.apply_apply_eq_zero w

/-- Universal injectivity over a flat base change and flatness of the target give flatness of
 the base changed cokernel. -/
private theorem flat_tensor_of_rTensor_injective
    {R : Type*} {S : Type uB} {P N C : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S]
    [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [AddCommGroup C] [Module R C] [Module.Flat S (S ⊗[R] N)]
    (i : P →ₗ[R] N) (p : N →ₗ[R] C) (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    (hi : ∀ (X : Type uB) [AddCommGroup X] [Module S X] [Module R X]
      [IsScalarTower R S X], Function.Injective (i.rTensor X)) :
    Module.Flat S (S ⊗[R] C) := by
  apply flat_of_rTensor_injective (i.baseChange S) (p.baseChange S)
    (LinearMap.lTensor_surjective S hp) (Module.Flat.lTensor_exact S hex)
  intro X _ _
  let : Module R X := Module.compHom X (algebraMap R S)
  have : IsScalarTower R S X := IsScalarTower.of_compHom R S X
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  exact (lTensor_baseChange_injective_iff i).mpr
    ((LinearMap.lTensor_inj_iff_rTensor_inj X i).mpr (hi X))

/-- The domain case, with the intermediate algebra embedded in the target. -/
private theorem exists_flat_tensor_coker_of_domains
    {R A B M : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    [Algebra R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [Module.Finite A M] (φ : M →ₗ[A] B) (hφ : Function.Injective φ)
    (hAB : Function.Injective (algebraMap A B)) :
    ∃ f : R, f ≠ 0 ∧ ∀ (T : Type uB) [CommRing T] [Algebra R T] [Module.Flat R T],
      IsUnit (algebraMap R T f) →
      Module.Flat T (T ⊗[R] (B ⧸ LinearMap.range (φ.restrictScalars R))) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have : Algebra.FiniteType R B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  obtain ⟨g, hg, hfree⟩ :=
    Module.exists_ne_zero_free_localizedModule_away (R := A) (S := B) (M := B)
  let W := LocalizedModule.Away g B
  let l : B →ₗ[A] W := LocalizedModule.mkLinearMap (Submonoid.powers g) B
  have : Module.Free (Localization.Away g) W := hfree _ W l
  have hl : Function.Injective l := by
    apply (IsLocalizedModule.injective_iff_isRegular (Submonoid.powers g) l).mpr
    rintro ⟨a, ⟨n, rfl⟩⟩ x y hxy
    simp only [Submonoid.smul_def, Algebra.smul_def] at hxy
    exact mul_left_cancel₀ (fun h => pow_ne_zero n hg (hAB (h.trans (map_zero _).symm))) hxy
  obtain ⟨f₁, hf₁, h₁⟩ := exists_rTensor_injective_of_free_localization
    (R := R) g hg (l.comp φ) (hl.comp hφ)
  obtain ⟨f₂, hf₂, h₂⟩ := exists_flat_tensor_of_finite (R := R) (A := B) (V := B)
  refine ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂, fun T _ _ _ hf => ?_⟩
  simp only [map_mul, IsUnit.mul_iff] at hf
  have := h₂ T hf.2
  apply flat_tensor_of_rTensor_injective (φ.restrictScalars R)
    (LinearMap.range (φ.restrictScalars R)).mkQ (Submodule.mkQ_surjective _)
    (LinearMap.exact_map_mkQ_range _)
  intro X _ _ _ _
  have h := h₁ T hf.1 X
  rw [LinearMap.restrictScalars_comp, LinearMap.rTensor_comp] at h
  intro x y hxy
  apply h
  exact congrArg ((l.restrictScalars R).rTensor X) hxy

private abbrev GenericallyFlat (R : Type uR) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V] : Prop :=
  ∃ f : R, f ≠ 0 ∧ ∀ (T : Type uR) [CommRing T] [Algebra R T] [Module.Flat R T],
    IsUnit (algebraMap R T f) → Module.Flat T (T ⊗[R] V)

private theorem genericallyFlat_of_equiv
    {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W)
    (h : GenericallyFlat R V) : GenericallyFlat R W := by
  obtain ⟨f, hf, h⟩ := h
  refine ⟨f, hf, fun T _ _ _ hu => ?_⟩
  have := h T hu
  exact Module.Flat.of_linearEquiv (e.symm.baseChange R T)

private theorem genericallyFlat_of_exact
    {R P N C : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [AddCommGroup C] [Module R C]
    (i : P →ₗ[R] N) (p : N →ₗ[R] C) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hP : GenericallyFlat R P) (hC : GenericallyFlat R C) : GenericallyFlat R N := by
  obtain ⟨f, hf, hP⟩ := hP
  obtain ⟨g, hg, hC⟩ := hC
  refine ⟨f * g, mul_ne_zero hf hg, fun T _ _ _ hu => ?_⟩
  simp only [map_mul, IsUnit.mul_iff] at hu
  have := hP T hu.1
  have := hC T hu.2
  exact flat_of_flat_of_flat (i.baseChange T) (p.baseChange T)
    (Module.Flat.lTensor_preserves_injective_linearMap i hi)
    (Module.Flat.lTensor_exact T hex) (LinearMap.lTensor_surjective T hp)

/-- Quotienting an exact sequence by a submodule of its middle term gives an exact sequence
 with intersection on the left and image on the right. -/
private theorem genericallyFlat_quotient_of_exact
    {R A P N C : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [AddCommGroup C] [Module A C] [Module R C] [IsScalarTower R A C]
    (i : P →ₗ[A] N) (p : N →ₗ[A] C)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (L : Submodule A N)
    (hP : GenericallyFlat R (P ⧸ L.comap i))
    (hC : GenericallyFlat R (C ⧸ L.map p)) : GenericallyFlat R (N ⧸ L) := by
  let i' := (L.comap i).mapQ L i le_rfl
  let p' := L.mapQ (L.map p) p (Submodule.le_comap_map _ _)
  apply genericallyFlat_of_exact (i'.restrictScalars R) (p'.restrictScalars R) ?_ ?_ ?_ hP hC
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        ((Submodule.Quotient.mk_eq_zero L).mp hx)
  · intro x
    obtain ⟨x, rfl⟩ := (L.map p).mkQ_surjective x
    obtain ⟨y, rfl⟩ := hp x
    exact ⟨L.mkQ y, rfl⟩
  · exact (hex.exact_mapQ_iff le_rfl (Submodule.le_comap_map _ _)).mpr inf_le_right

/-- Passing to the image of the intermediate algebra reduces the domain case to embedded
 domains. -/
private theorem genericallyFlat_quotient_domain
    {R A B : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    [Algebra R B] [IsScalarTower R A B]
    (P : Submodule A B) [Module.Finite A P] : GenericallyFlat R (B ⧸ P) := by
  let h := IsScalarTower.toAlgHom R A B
  let D := h.range
  let : Algebra A D := h.rangeRestrict.toRingHom.toAlgebra
  have : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq fun r =>
    (h.rangeRestrict.commutes r).symm
  have : IsScalarTower A D B := IsScalarTower.of_algebraMap_eq fun a => rfl
  have : Algebra.FiniteType R D :=
    Algebra.FiniteType.of_surjective h.rangeRestrict h.rangeRestrict_surjective
  have : Algebra.FiniteType D B := Algebra.FiniteType.of_restrictScalars_finiteType A D B
  let P' : Submodule D B :=
    { carrier := P
      zero_mem' := P.zero_mem
      add_mem' := P.add_mem
      smul_mem' := by
        intro a x hx
        obtain ⟨b, hb⟩ := a.property
        show (a : B) * x ∈ P
        rw [← hb]
        show algebraMap A B b * x ∈ P
        simpa only [Algebra.smul_def] using P.smul_mem b hx }
  have : Module.Finite A P' := show Module.Finite A P from inferInstance
  have : Module.Finite D P' := Module.Finite.of_restrictScalars_finite A D P'
  have H : GenericallyFlat R (B ⧸ LinearMap.range (P'.subtype.restrictScalars R)) :=
    exists_flat_tensor_coker_of_domains P'.subtype P'.injective_subtype Subtype.val_injective
  rw [LinearMap.range_restrictScalars, Submodule.range_subtype] at H
  have he : P'.restrictScalars R = P.restrictScalars R := by ext x; rfl
  rw [he] at H
  exact genericallyFlat_of_equiv (Submodule.Quotient.restrictScalarsEquiv R P) H

/-- Prime filtration reduces the assertion for a finite module to the domain case. -/
private theorem genericallyFlat_quotient_of_finite
    {R A B : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [Algebra R B] [IsScalarTower R A B]
    {N : Type uN} [AddCommGroup N] [Module B N] [Module.Finite B N]
    [Module A N] [IsScalarTower A B N] [Module R N] [IsScalarTower R A N]
    (P : Submodule A N) [Module.Finite A P] : GenericallyFlat R (N ⧸ P) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have H : ∀ (V : Type uN) [AddCommGroup V] [Module B V] [Module.Finite B V],
      ∀ [Module A V] [IsScalarTower A B V] [Module R V] [IsScalarTower R A V],
        ∀ (L : Submodule A V) [Module.Finite A L], GenericallyFlat R (V ⧸ L) := by
    intro V _ _ hV
    induction hV using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime with
    | subsingleton V =>
      intro _ _ _ _ L _
      exact ⟨1, one_ne_zero, fun T _ _ _ _ => inferInstance⟩
    | quotient V q e =>
      intro _ _ _ _ L _
      have : q.asIdeal.IsPrime := q.isPrime
      have : Algebra.FiniteType A (B ⧸ q.asIdeal) :=
        Algebra.FiniteType.trans (S := B) inferInstance inferInstance
      let eA := e.restrictScalars A
      have h := genericallyFlat_quotient_domain (R := R) (L.map eA.toLinearMap)
      exact genericallyFlat_of_equiv
        ((Submodule.Quotient.equiv L _ eA rfl).symm.restrictScalars R) h
    | exact V₁ V₂ V₃ i p hi hp hex h₁ h₃ =>
      intro _ _ _ _ L _
      let : Module A V₁ := Module.compHom V₁ (algebraMap A B)
      have : IsScalarTower A B V₁ := IsScalarTower.of_compHom A B V₁
      let : Module R V₁ := Module.compHom V₁ (algebraMap R A)
      have : IsScalarTower R A V₁ := IsScalarTower.of_compHom R A V₁
      let : Module A V₃ := Module.compHom V₃ (algebraMap A B)
      have : IsScalarTower A B V₃ := IsScalarTower.of_compHom A B V₃
      let : Module R V₃ := Module.compHom V₃ (algebraMap R A)
      have : IsScalarTower R A V₃ := IsScalarTower.of_compHom R A V₃
      let iA := i.restrictScalars A
      let pA := p.restrictScalars A
      let j : L.comap iA →ₗ[A] L :=
        (iA.comp (L.comap iA).subtype).codRestrict L (fun x => x.property)
      have hj : Function.Injective j := by
        intro x y hxy
        exact Subtype.ext (hi (congrArg Subtype.val hxy))
      have : Module.Finite A (L.comap iA) := Module.Finite.of_injective j hj
      exact genericallyFlat_quotient_of_exact iA pA hp hex L
        (h₁ (L.comap iA)) (h₃ (L.map pA))
  exact H N P

/-- **Stacks Project, Tag 0H40.** A map from a finite `A`-module to a finite
`B`-module, for finite type algebras `R → A → B` over a Noetherian domain,
has flat cokernel over `R` after a suitable principal localization. -/
@[stacks 0H40, sga "1 IV 6.7" "flatness clause"]
theorem Module.exists_flat_localizedModule_coker
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [Algebra R B] [IsScalarTower R A B]
    {M : Type uM} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module R M] [IsScalarTower R A M]
    {N : Type uN} [AddCommGroup N] [Module B N] [Module.Finite B N]
    [Module A N] [IsScalarTower A B N]
    [Module R N] [IsScalarTower R A N]
    (φ : M →ₗ[A] N) :
    ∃ f : R, f ≠ 0 ∧
      Module.Flat (Localization.Away f)
        (LocalizedModule.Away f (N ⧸ LinearMap.range (φ.restrictScalars R))) := by
  have H := genericallyFlat_quotient_of_finite (R := R) (B := B) (LinearMap.range φ)
  have he : (LinearMap.range φ).restrictScalars R = LinearMap.range (φ.restrictScalars R) :=
    by symm; exact LinearMap.range_restrictScalars φ
  have H' := genericallyFlat_of_equiv
    (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range φ)).symm H
  rw [he] at H'
  obtain ⟨f, hf, h⟩ := H'
  refine ⟨f, hf, ?_⟩
  have := h (Localization.Away f) (IsLocalization.Away.algebraMap_isUnit f)
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f)
        (N ⧸ LinearMap.range (φ.restrictScalars R)))).equiv.symm
