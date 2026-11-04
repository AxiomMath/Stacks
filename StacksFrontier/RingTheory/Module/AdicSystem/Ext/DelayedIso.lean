module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.Category
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.RingTheory.Module.ReduceModIdealExact

/-!
# Ext over adic quotients: the delayed isomorphism (Tag 0EGY)

The positive-indexed inverse systems `n ↦ Ext^i_A(M, N) ⧸ I ^ n Ext^i_A(M, N)` and
`n ↦ Ext^i_{Aₙ}(Mₙ, Nₙ)`, the almost-bijection and reduction-mod-`I ^ n` machinery comparing
them degree by degree, and the isomorphism of the two systems in the delayed-morphism category
of tag 0EGY.
-/

@[expose] public section

/-! ## Tag 0EGY -/

section

open CategoryTheory CategoryTheory.Abelian

universe u v

namespace Stacks.AdicSystem.ExtDelayedIso

open Stacks.Modules.AdicSystem

noncomputable section


variable {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]
  {M N : Type v}
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- The positive-indexed system whose `n`th term is
`Ext_A^i(M, N) / I^n Ext_A^i(M, N)`. -/
public noncomputable abbrev extAdicQuotientSystem (I : Ideal A) (M N : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (i : ℕ) :
    AdicModuleSystem.{u, v} A I where
  module n := FGModuleCat.of (A ⧸ I ^ (n : ℕ))
    (Ext (ModuleCat.of A M) (ModuleCat.of A N) i ⧸
      I ^ (n : ℕ) • (⊤ : Submodule A (Ext (ModuleCat.of A M) (ModuleCat.of A N) i)))

/-- The positive-indexed system whose `n`th term is
`Ext_{A/I^n}^i(M/I^n M, N/I^n N)`. -/
public noncomputable abbrev extOfAdicQuotientsSystem (I : Ideal A) (M N : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (i : ℕ) :
    AdicModuleSystem.{u, v} A I where
  module n := by
    letI : IsNoetherianRing (A ⧸ I ^ (n : ℕ)) :=
      isNoetherian_of_tower A inferInstance
    exact FGModuleCat.of (A ⧸ I ^ (n : ℕ))
      (Ext
        (ModuleCat.of (A ⧸ I ^ (n : ℕ))
          (M ⧸ I ^ (n : ℕ) • (⊤ : Submodule A M)))
        (ModuleCat.of (A ⧸ I ^ (n : ℕ))
          (N ⧸ I ^ (n : ℕ) • (⊤ : Submodule A N))) i)

end
end Stacks.AdicSystem.ExtDelayedIso

end

section

open CategoryTheory Abelian Stacks.Modules.AdicSystem Stacks.Modules.AdicSystem.AdicModuleSystem
  TensorProduct

universe u v

noncomputable section

namespace Stacks.AdicSystem.ExtDelayedIso
section Generic

variable {S : Type*} [CommRing S]

/-- `f` is injective and surjective up to multiplication by `𝔞`. -/
private def AlmostBij (𝔞 : Ideal S) {X Y : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y]
    [Module S Y] (f : X →ₗ[S] Y) : Prop :=
  (∀ x, f x = 0 → ∀ a ∈ 𝔞, a • x = 0) ∧ ∀ y, ∀ a ∈ 𝔞, ∃ x, f x = a • y

variable {X Y Z : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup Z] [Module S Z]

private theorem AlmostBij.mono {𝔞 𝔟 : Ideal S} (h : 𝔟 ≤ 𝔞) {f : X →ₗ[S] Y} (hf : AlmostBij 𝔞 f) :
    AlmostBij 𝔟 f :=
  ⟨fun x hx a ha => hf.1 x hx a (h ha), fun y a ha => hf.2 y a (h ha)⟩

private theorem almostBij_of_equiv (𝔞 : Ideal S) (e : X ≃ₗ[S] Y) : AlmostBij 𝔞 (e : X →ₗ[S] Y) :=
  ⟨fun x hx a _ => by simp [(e.map_eq_zero_iff).1 hx],
    fun y a _ => ⟨e.symm (a • y), by simp⟩⟩

private theorem AlmostBij.comp_equiv {𝔞 : Ideal S} {f : Y →ₗ[S] Z} (hf : AlmostBij 𝔞 f)
    (e : X ≃ₗ[S] Y) : AlmostBij 𝔞 (f ∘ₗ (e : X →ₗ[S] Y)) := by
  refine ⟨fun x hx a ha => ?_, fun z a ha => ?_⟩
  · have := hf.1 (e x) hx a ha
    rw [← map_smul] at this
    exact (e.map_eq_zero_iff).1 this
  · obtain ⟨y, hy⟩ := hf.2 z a ha
    exact ⟨e.symm y, by simpa using hy⟩

private theorem AlmostBij.equiv_comp {𝔞 : Ideal S} {f : X →ₗ[S] Y} (hf : AlmostBij 𝔞 f)
    (e : Y ≃ₗ[S] Z) : AlmostBij 𝔞 ((e : Y →ₗ[S] Z) ∘ₗ f) := by
  refine ⟨fun x hx a ha => hf.1 x (by simpa using hx) a ha, fun z a ha => ?_⟩
  obtain ⟨x, hx⟩ := hf.2 (e.symm z) a ha
  exact ⟨x, by simp [hx]⟩

private theorem smul_mem_of_mul {𝔞 𝔟 : Ideal S} (P : Submodule S X) (x : X)
    (h : ∀ a ∈ 𝔞, ∀ b ∈ 𝔟, (a * b) • x ∈ P) : ∀ r ∈ 𝔞 * 𝔟, r • x ∈ P := by
  intro r hr
  refine Submodule.mul_induction_on hr h ?_
  intro r s hr hs
  rw [add_smul]
  exact P.add_mem hr hs

/-- The induced map on cokernels of two exact rows is almost bijective. -/
private theorem almostBij_cokernel {𝔞 : Ideal S}
    {X' Y' Z' : Type*} [AddCommGroup X'] [Module S X'] [AddCommGroup Y'] [Module S Y']
    [AddCommGroup Z'] [Module S Z']
    (f : X →ₗ[S] Y) (p : Y →ₗ[S] Z) (f' : X' →ₗ[S] Y') (p' : Y' →ₗ[S] Z')
    (α : X →ₗ[S] X') (β : Y →ₗ[S] Y') (γ : Z →ₗ[S] Z')
    (hp : Function.Surjective p) (hfp : ∀ x, p (f x) = 0)
    (hp' : Function.Surjective p') (hpf' : ∀ y, p' y = 0 → ∃ x, f' x = y)
    (hsq : ∀ x, β (f x) = f' (α x)) (hγ : ∀ y, γ (p y) = p' (β y))
    (hα : ∀ x', ∀ a ∈ 𝔞, ∃ x, α x = a • x') (hβ : AlmostBij 𝔞 β) :
    AlmostBij (𝔞 * 𝔞) γ := by
  refine ⟨fun z hz r hr => ?_, fun z' r hr => ?_⟩
  · obtain ⟨y, rfl⟩ := hp z
    have key : ∀ a ∈ 𝔞, ∀ b ∈ 𝔞, (b * a) • p y ∈ (⊥ : Submodule S Z) := by
      intro a ha b hb
      rw [hγ] at hz
      obtain ⟨x', hx'⟩ := hpf' _ hz
      obtain ⟨x, hx⟩ := hα x' a ha
      have h0 : β (a • y - f x) = 0 := by
        rw [map_sub, map_smul, hsq, hx, ← hx', map_smul, sub_self]
      have h1 := hβ.1 _ h0 b hb
      rw [Submodule.mem_bot, mul_smul, ← map_smul, ← map_smul]
      rw [smul_sub, sub_eq_zero] at h1
      rw [h1, ← map_smul, hfp]
    have := smul_mem_of_mul (𝔞 := 𝔞) (𝔟 := 𝔞) ⊥ (p y) (fun a ha b hb => key b hb a ha) r hr
    simpa using this
  · have hr' : r ∈ 𝔞 := Ideal.mul_le_left hr
    obtain ⟨y', rfl⟩ := hp' z'
    obtain ⟨y, hy⟩ := hβ.2 y' r hr'
    exact ⟨p y, by rw [hγ, hy, map_smul]⟩

/-- Existence of the induced map on cokernels. -/
private theorem exists_cokernel_map
    {X' Y' Z' : Type*} [AddCommGroup X'] [Module S X'] [AddCommGroup Y'] [Module S Y']
    [AddCommGroup Z'] [Module S Z']
    (f : X →ₗ[S] Y) (p : Y →ₗ[S] Z) (f' : X' →ₗ[S] Y') (p' : Y' →ₗ[S] Z')
    (α : X →ₗ[S] X') (β : Y →ₗ[S] Y')
    (hp : Function.Surjective p) (hpf : ∀ y, p y = 0 → ∃ x, f x = y)
    (hfp' : ∀ x, p' (f' x) = 0) (hsq : ∀ x, β (f x) = f' (α x)) :
    ∃ γ : Z →ₗ[S] Z', ∀ y, γ (p y) = p' (β y) := by
  refine ⟨((LinearMap.ker p).liftQ (p' ∘ₗ β) ?_) ∘ₗ
    ((p.quotKerEquivOfSurjective hp).symm : Z →ₗ[S] _), ?_⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := hpf y hy
    simp [hsq, hfp']
  · intro y
    have : (p.quotKerEquivOfSurjective hp).symm (p y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [this]

variable {R : Type*} [CommRing R] [Algebra R S]

private theorem AlmostBij.extendScalars {𝔟 : Ideal R} [Module R X] [IsScalarTower R S X]
    [Module R Y] [IsScalarTower R S Y] {f : X →ₗ[R] Y} (hf : AlmostBij 𝔟 f)
    (h : Function.Surjective (algebraMap R S)) :
    AlmostBij (𝔟.map (algebraMap R S)) (f.extendScalarsOfSurjective h) := by
  refine ⟨fun x hx s hs => ?_, fun y s hs => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ h).1 hs
    rw [algebraMap_smul]
    exact hf.1 x hx a ha
  · obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ h).1 hs
    obtain ⟨x, hx⟩ := hf.2 y a ha
    exact ⟨x, by rw [algebraMap_smul]; exact hx⟩

end Generic

section Sys
variable {A : Type u} [CommRing A] {I : Ideal A}
private theorem nonempty_iso_of_almostBij (E F : AdicModuleSystem.{u, v} A I)
    (c : ℕ) (φ : ∀ n : ℕ+, (E.module n).obj →ₗ[A ⧸ I ^ (n : ℕ)] (F.module n).obj)
    (hφ : ∀ n : ℕ+, AlmostBij ((I ^ c).map (Ideal.Quotient.mk (I ^ (n : ℕ)))) (φ n)) :
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    Nonempty (E ≅ F) := by
  let := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
  let r : HomRepresentative E F :=
    { delay := 0
      map := fun n _ => (torsionPart F n 0).mkQ ∘ₗ
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n : ℕ)))).map
          (ModuleCat.ofHom (φ n))).hom ∘ₗ (powerPart E n 0).subtype }
  have hr : ∀ n h x, r.map n h x = (torsionPart F n 0).mkQ (φ n x.1) := fun _ _ _ => rfl
  have key := (Stacks.AdicModuleSystem.IsomorphismCriterion.isIso_homOfRepresentative_iff r).2 ?_
  · exact ⟨@asIso _ _ _ _ _ key⟩
  have hmem : ∀ (n : ℕ+) a, a ∈ I ^ c →
      Ideal.Quotient.mk (I ^ (n : ℕ)) a ∈ (I ^ c).map (Ideal.Quotient.mk (I ^ (n : ℕ))) :=
    fun n a ha => Ideal.mem_map_of_mem _ ha
  refine ⟨c, Filter.Eventually.of_forall fun n _ => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx⟩ ⟨a, ha⟩
    have hx' : φ n x.1 = 0 := by
      have := LinearMap.mem_ker.1 hx
      rw [hr, torsionPart_zero_eq_bot] at this
      exact (Submodule.Quotient.mk_eq_zero _).1 this
    exact Subtype.ext (Subtype.ext ((hφ n).1 x.1 hx' _ (hmem n a ha)))
  · rintro y ⟨a, ha⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
    obtain ⟨x, hx⟩ := (hφ n).2 y _ (hmem n a ha)
    show a • (Submodule.Quotient.mk (Submodule.Quotient.mk y) : _ ⧸ LinearMap.range (r.map n _)) =
      0
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨x, by
      show x ∈ I ^ 0 • ⊤
      simp only [FGModuleCat.obj_carrier, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      trivial⟩, ?_⟩
    rw [hr]
    exact congrArg _ hx

end Sys
section ExtLemmas
variable {R : Type u} [CommRing R] [Small.{v} R]
private theorem ext_smul_eq_zero {T Y : ModuleCat.{v} R} (a : R) (h : ∀ t : T, a • t = 0) {j : ℕ}
    (e : Ext T Y j) : a • e = 0 := by
  have h0 : a • 𝟙 T = 0 := by ext t; exact h t
  rw [← Ext.mk₀_id_comp e, ← Ext.smul_comp, ← Ext.mk₀_smul, h0, Ext.mk₀_zero, Ext.zero_comp]

private theorem precomp_apply {X Y Z : ModuleCat.{v} R} {n : ℕ} (α : Ext X Y n) {a b : ℕ} (h : n + a
  = b)
    (x : Ext Y Z a) : α.precompOfLinear R Z h x = α.comp x h := rfl

/-- If `𝔞` kills `S.X₁`, then `a • x` lies in the image of `precomp g` for `a ∈ 𝔞`. -/
private theorem exists_precomp_g_eq_smul {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    {𝔞 : Ideal R} (h𝔞 : ∀ a ∈ 𝔞, ∀ t : S.X₁, a • t = 0) (Z : ModuleCat.{v} R) {n : ℕ}
    (x : Ext S.X₂ Z n) {a : R} (ha : a ∈ 𝔞) :
    ∃ y, (Ext.mk₀ S.g).precompOfLinear R Z (zero_add n) y = a • x := by
  have : (Ext.mk₀ S.f).comp (a • x) (zero_add _) = 0 := by
    rw [Ext.comp_smul, ext_smul_eq_zero a (h𝔞 a ha)]
  exact Ext.contravariant_sequence_exact₂ hS Z _ this

private theorem almostBij_precomp_g {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (𝔞 : Ideal R) (h𝔞 : ∀ a ∈ 𝔞, ∀ t : S.X₁, a • t = 0) (Z : ModuleCat.{v} R) (j : ℕ) :
    AlmostBij 𝔞 ((Ext.mk₀ S.g).precompOfLinear R Z (zero_add (j + 1))) := by
  refine ⟨fun y hy a ha => ?_, fun x a ha => ?_⟩
  · rw [precomp_apply] at hy
    obtain ⟨x₁, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Z y hy (add_comm 1 j)
    rw [← Ext.comp_smul, ext_smul_eq_zero a (h𝔞 a ha), Ext.comp_zero]
  · exact exists_precomp_g_eq_smul hS h𝔞 Z x ha

private theorem bijective_precomp_extClass {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    [Projective S.X₂] (Z : ModuleCat.{v} R) (j : ℕ) :
    Function.Bijective (hS.extClass.precompOfLinear R Z (add_comm 1 (j + 1))) := by
  refine ⟨fun x y hxy => ?_, precomp_extClass_surjective_of_projective_X₂ Z hS (j + 1)⟩
  rw [← sub_eq_zero] at hxy ⊢
  rw [← map_sub, precomp_apply] at hxy
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS Z (x - y) (add_comm 1 (j + 1)) hxy
  rw [← hx₂, Ext.eq_zero_of_projective x₂, Ext.comp_zero]

private theorem exact_precomp_extClass_zero {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    [Projective S.X₂] (Z : ModuleCat.{v} R) :
    Function.Surjective (hS.extClass.precompOfLinear R Z (add_comm 1 0)) ∧
    (∀ y, hS.extClass.precompOfLinear R Z (add_comm 1 0) y = 0 →
      ∃ x, (Ext.mk₀ S.f).precompOfLinear R Z (zero_add 0) x = y) ∧
    (∀ x, hS.extClass.precompOfLinear R Z (add_comm 1 0)
      ((Ext.mk₀ S.f).precompOfLinear R Z (zero_add 0) x) = 0) := by
  refine ⟨precomp_extClass_surjective_of_projective_X₂ Z hS 0, fun y hy => ?_, fun x => ?_⟩
  · exact Ext.contravariant_sequence_exact₁ hS Z y (add_comm 1 0) hy
  · rw [precomp_apply, precomp_apply, ← Ext.comp_assoc_of_second_deg_zero, hS.extClass_comp,
      Ext.zero_comp]

end ExtLemmas
section Red
variable {A : Type u} [CommRing A] (J : Ideal A)
private abbrev red (X : Type*) [AddCommGroup X] [Module A X] := X ⧸ J • (⊤ : Submodule A X)

variable {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
  [AddCommGroup Z] [Module A Z]

private noncomputable def redMap (u : X →ₗ[A] Y) : red J X →ₗ[A ⧸ J] red J Y :=
  (Submodule.mapQ _ _ u (Submodule.smul_top_le_comap_smul_top J u)).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

@[simp] private theorem redMap_mk (u : X →ₗ[A] Y) (x : X) :
    redMap J u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u x) := rfl

private noncomputable def redEquiv (e : X ≃ₗ[A] Y) : red J X ≃ₗ[A ⧸ J] red J Y :=
  (Submodule.Quotient.equiv _ _ e (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

@[simp] private theorem redEquiv_mk (e : X ≃ₗ[A] Y) (x : X) :
    redEquiv J e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := rfl

private theorem redMap_surjective {v : Y →ₗ[A] Z} (hv : Function.Surjective v) :
    Function.Surjective (redMap J v) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨y, rfl⟩ := hv z
    exact ⟨_, redMap_mk J v y⟩

private theorem redMap_exact {u : X →ₗ[A] Y} {v : Y →ₗ[A] Z} (hv : Function.Surjective v)
    (huv : ∀ y, v y = 0 → ∃ x, u x = y) (y : red J Y) (hy : redMap J v y = 0) :
    ∃ x, redMap J u x = y := by
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    rw [redMap_mk, Submodule.Quotient.mk_eq_zero] at hy
    have : J • (⊤ : Submodule A Z) = (J • (⊤ : Submodule A Y)).map v := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hv]
    rw [this] at hy
    obtain ⟨y', hy', hvy⟩ := hy
    obtain ⟨x, hx⟩ := huv (y - y') (by rw [map_sub, hvy, sub_self])
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [redMap_mk, hx, Submodule.Quotient.eq]
    simpa using hy'

private theorem redMap_comp (u : X →ₗ[A] Y) (v : Y →ₗ[A] Z) (x : red J X) :
    redMap J v (redMap J u x) = redMap J (v ∘ₗ u) x := by
  induction x using Submodule.Quotient.induction_on with
  | H x => rfl

/-- A reduction of a free module is projective. -/
private theorem projective_red [Module.Free A X] : Module.Projective (A ⧸ J) (red J X) := by
  let e : ((A ⧸ J) ⊗[A] X) ≃ₗ[A ⧸ J] red J X :=
    (TensorProduct.quotTensorEquivQuotSMul X J).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  exact Module.Projective.of_equiv e


/-- Artin–Rees: the kernel of `K/JK → P/JP` is killed by a fixed power of `I`. -/
private theorem exists_pow_smul_ker_redMap_subtype [IsNoetherianRing A] (I : Ideal A) [Module.Finite
  A Y]
    (K : Submodule A Y) :
    ∃ c, ∀ n : ℕ, ∀ x : red (I ^ n) K, redMap (I ^ n) K.subtype x = 0 → ∀ a ∈ I ^ c, a • x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I K
  refine ⟨k, fun n x hx a ha => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  rw [redMap_mk, Submodule.Quotient.mk_eq_zero] at hx
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  rw [Submodule.mem_smul_top_iff]
  rcases le_or_gt k n with hkn | hkn
  · have hmem : (x : Y) ∈ I ^ n • (⊤ : Submodule A Y) ⊓ K := ⟨hx, x.2⟩
    rw [hk n hkn] at hmem
    have h1 : (x : Y) ∈ I ^ (n - k) • K :=
      Submodule.smul_mono le_rfl inf_le_right hmem
    have h2 := Submodule.smul_mem_smul ha h1
    rw [← Submodule.smul_assoc, smul_eq_mul, ← pow_add, Nat.add_sub_cancel' hkn] at h2
    exact h2
  · exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right hkn.le ha) x.2
/-- reduction of homs, A-linear -/
private noncomputable def redHomAux : (X →ₗ[A] Y) →ₗ[A] (red J X →ₗ[A ⧸ J] red J Y) where
  toFun h := redMap J h
  map_add' _ _ := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  map_smul' _ _ := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

private theorem redHomAux_le : J • (⊤ : Submodule A (X →ₗ[A] Y)) ≤ LinearMap.ker (redHomAux J) := by
  rw [Submodule.smul_le]
  intro a ha h _
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  show (Submodule.Quotient.mk (a • h x) : red J Y) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha trivial

private noncomputable def redHom : red J (X →ₗ[A] Y) →ₗ[A ⧸ J] (red J X →ₗ[A ⧸ J] red J Y) :=
  LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    ((J • (⊤ : Submodule A (X →ₗ[A] Y))).liftQ (redHomAux J) (redHomAux_le J))

@[simp] private theorem redHom_mk (h : X →ₗ[A] Y) :
    redHom J (Submodule.Quotient.mk h) = redMap J h := rfl

/-- If `𝔟` kills `ker φ`, then `𝔟` mod `J` kills `ker φ` as an `A ⧸ J`-module. -/
private theorem smul_eq_zero_of_map_ker {X' Y' : Type*} [AddCommGroup X'] [Module A X']
    [Module (A ⧸ J) X'] [IsScalarTower A (A ⧸ J) X'] [AddCommGroup Y'] [Module (A ⧸ J) Y']
    {φ : X' →ₗ[A ⧸ J] Y'} (𝔟 : Ideal A) (h : ∀ x, φ x = 0 → ∀ a ∈ 𝔟, a • x = 0) :
    ∀ s ∈ 𝔟.map (Ideal.Quotient.mk J), ∀ t : LinearMap.ker φ, s • t = 0 := by
  intro s hs t
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hs
  exact Subtype.ext ((algebraMap_smul (A ⧸ J) a t.1).trans (h t.1 t.2 a ha))

section Transport
variable {S : Type*} [CommRing S] {R : Type*} [CommRing R]

/-- Transport. -/
private theorem AlmostBij.transport (σ : R →+* S) (hσ : Function.Surjective σ) (𝔟 : Ideal R)
    {X' Y' : Type*} [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
    {X Y : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
    {g : X' →ₗ[R] Y'} (hg : AlmostBij 𝔟 g) (f : X →ₗ[S] Y) (e₁ : X ≃ X') (e₂ : Y ≃ Y')
    (he₁ : ∀ r x, e₁ (σ r • x) = r • e₁ x) (he₂ : ∀ r y, e₂ (σ r • y) = r • e₂ y)
    (hf : ∀ x, e₂ (f x) = g (e₁ x)) :
    AlmostBij (𝔟.map σ) f := by
  refine ⟨fun x hx s hs => ?_, fun y s hs => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective σ hσ).1 hs
    apply e₁.injective
    have h0 : e₂ (f x) = e₂ 0 := by rw [hx]
    have h00 : e₂ 0 = 0 := by simpa using he₂ 0 0
    have h10 : e₁ 0 = 0 := by simpa using he₁ 0 0
    rw [hf, h00] at h0
    rw [he₁, hg.1 _ h0 r hr, h10]
  · obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective σ hσ).1 hs
    obtain ⟨x', hx'⟩ := hg.2 (e₂ y) r hr
    refine ⟨e₁.symm x', e₂.injective ?_⟩
    rw [hf, he₂, Equiv.apply_symm_apply, hx']

end Transport

variable [IsNoetherianRing A] (I : Ideal A) in
private theorem exists_almostBij_redHom (X Y : Type*) [AddCommGroup X] [Module A X] [Module.Finite A
  X]
    [AddCommGroup Y] [Module A Y] [Module.Finite A Y] :
    ∃ c, ∀ n : ℕ, AlmostBij ((I ^ c).map (Ideal.Quotient.mk (I ^ n))) (redHom (I ^ n) : red (I ^ n)
      (X →ₗ[A] Y) →ₗ[A ⧸ I ^ n] _) := by
  obtain ⟨_, _, comparison, -, -, hcomp, -, -, ⟨c, hc⟩, -⟩ :=
    Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion (M := X)
      (N := Y) I
  refine ⟨c, fun n => ?_⟩
  have hg : AlmostBij (I ^ c) (comparison n) := by
    refine ⟨fun x hx a ha => ?_, fun y a ha => ?_⟩
    · have := (Module.mem_annihilator.1 ((hc n).1 ha)) ⟨x, hx⟩
      exact congrArg Subtype.val this
    · have := (Module.mem_annihilator.1 ((hc n).2 ha)) (Submodule.Quotient.mk y)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
      exact this
  refine hg.transport (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective _ _ (Equiv.refl _)
    (LinearMap.extendScalarsOfSurjectiveEquiv (R := A) Ideal.Quotient.mk_surjective).symm.toEquiv
    (fun _ _ => rfl) (fun r y => ?_) (fun x => ?_)
  · ext z; rfl
  · induction x using Submodule.Quotient.induction_on with
    | H h =>
    ext z
    exact (hcomp n h z).symm

end Red
section Steps
variable {A : Type u} [CommRing A] {I : Ideal A}

private theorem nonempty_iso_of_equiv (E F : AdicModuleSystem.{u, v} A I)
    (φ : ∀ n : ℕ+, (E.module n).obj ≃ₗ[A ⧸ I ^ (n : ℕ)] (F.module n).obj) :
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    Nonempty (E ≅ F) :=
  nonempty_iso_of_almostBij E F 0 (fun n => φ n) (fun n => almostBij_of_equiv _ (φ n))

variable [IsNoetherianRing A] [Small.{v} A]

/-- The syzygy data. -/
private structure Pres (M : Type v) [AddCommGroup M] [Module A M] where
  P : Type v
  [acg : AddCommGroup P]
  [mod : Module A P]
  [free : Module.Free A P]
  [fin : Module.Finite A P]
  f : P →ₗ[A] M
  surj : Function.Surjective f

attribute [local instance] Pres.acg Pres.mod Pres.free Pres.fin

omit [IsNoetherianRing A] in
private theorem nonempty_pres (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Nonempty (Pres (A := A) M) := by
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation A M
  exact ⟨⟨P, f, hf⟩⟩

variable {M N : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- Dimension shifting over `A`. -/
private theorem iso_shift_base (p : Pres (A := A) M) (i : ℕ) :
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    Nonempty (extAdicQuotientSystem I (LinearMap.ker p.f) N (i + 1) ≅
      extAdicQuotientSystem I M N (i + 2)) := by
  have hS := LinearMap.shortExact_shortComplexKer p.surj
  let e := LinearEquiv.ofBijective _ (bijective_precomp_extClass hS (ModuleCat.of A N) i)
  exact nonempty_iso_of_equiv _ _ fun n => redEquiv (I ^ (n : ℕ)) e

end Steps

section Quot
variable {A : Type u} [CommRing A] [Small.{v} A] (J : Ideal A)
variable {P M : Type v} [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M]
  (N : Type v) [AddCommGroup N] [Module A N]

/-- `ker (Pₙ → Mₙ)` -/
private abbrev kerRed (f : P →ₗ[A] M) : Submodule (A ⧸ J) (red J P) := LinearMap.ker (redMap J f)

/-- `Kₙ → K(n)` -/
private def toKerRed (f : P →ₗ[A] M) : red J (LinearMap.ker f) →ₗ[A ⧸ J] kerRed J f :=
  (redMap J (LinearMap.ker f).subtype).codRestrict _ fun x => by
    rw [LinearMap.mem_ker, redMap_comp]
    have : f ∘ₗ (LinearMap.ker f).subtype = 0 := by ext x; exact x.2
    rw [this]
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

omit [Small.{v, u} A] in
private theorem toKerRed_surjective {f : P →ₗ[A] M} (hf : Function.Surjective f) :
    Function.Surjective (toKerRed J f) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := redMap_exact J hf (u := (LinearMap.ker f).subtype)
    (fun y hy => ⟨⟨y, hy⟩, rfl⟩) y hy
  exact ⟨x, Subtype.ext hx⟩

private theorem shift_quot [Module.Free A P] {f : P →ₗ[A] M} (hf : Function.Surjective f) (i : ℕ) :
    Nonempty (Ext (ModuleCat.of (A ⧸ J) (kerRed J f)) (ModuleCat.of (A ⧸ J) (red J N)) (i + 1) ≃ₗ[A
      ⧸ J]
      Ext (ModuleCat.of (A ⧸ J) (red J M)) (ModuleCat.of (A ⧸ J) (red J N)) (i + 2)) := by
  have hS := LinearMap.shortExact_shortComplexKer (redMap_surjective J hf)
  have := projective_red J (X := P)
  exact ⟨LinearEquiv.ofBijective _ (bijective_precomp_extClass hS _ i)⟩

private theorem almostBij_toKerRed_precomp {f : P →ₗ[A] M} (hf : Function.Surjective f) (𝔟 : Ideal
  A)
    (hAR : ∀ x : red J (LinearMap.ker f), redMap J (LinearMap.ker f).subtype x = 0 →
      ∀ a ∈ 𝔟, a • x = 0) (i : ℕ) :
    AlmostBij (𝔟.map (Ideal.Quotient.mk J))
      ((Ext.mk₀ (ModuleCat.ofHom (toKerRed J f))).precompOfLinear (A ⧸ J)
        (ModuleCat.of (A ⧸ J) (red J N)) (zero_add (i + 1))) := by
  have hS := LinearMap.shortExact_shortComplexKer (toKerRed_surjective J hf)
  exact almostBij_precomp_g hS _
    (smul_eq_zero_of_map_ker J 𝔟 fun x hx => hAR x (congrArg Subtype.val hx)) _ i

end Quot

section Zero
section
variable {R : Type u} [CommRing R] [Small.{v} R]

private noncomputable def ext0Equiv (X Y : Type v) [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] : Ext (ModuleCat.of R X) (ModuleCat.of R Y) 0 ≃ₗ[R] (X →ₗ[R] Y) :=
  Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv

private theorem ext0Equiv_symm_apply (X Y : Type v) [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (h : X →ₗ[R] Y) :
    (ext0Equiv X Y).symm h = Ext.mk₀ (ModuleCat.ofHom h) := rfl

private theorem precomp_mk₀_ext0Equiv_symm {X Y Z : Type v} [AddCommGroup X] [Module R X]
  [AddCommGroup Y]
    [Module R Y] [AddCommGroup Z] [Module R Z] (u : X →ₗ[R] Y) (h : Y →ₗ[R] Z) :
    (Ext.mk₀ (ModuleCat.ofHom u)).precompOfLinear R (ModuleCat.of R Z) (zero_add 0)
      ((ext0Equiv Y Z).symm h) = (ext0Equiv X Z).symm (h ∘ₗ u) := by
  rw [ext0Equiv_symm_apply, ext0Equiv_symm_apply]
  exact Ext.mk₀_comp_mk₀ _ _
end

section
variable {R : Type u} [CommRing R] [Small.{v} R]
private theorem almostBij_precomp_g_zero {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    (𝔞 : Ideal R) (h𝔞 : ∀ a ∈ 𝔞, ∀ t : S.X₁, a • t = 0) (Z : ModuleCat.{v} R) :
    AlmostBij 𝔞 ((Ext.mk₀ S.g).precompOfLinear R Z (zero_add 0)) := by
  have := hS.epi_g
  refine ⟨fun y hy a _ => ?_, fun x a ha => ?_⟩
  · have : y = 0 := Ext.precomp_mk₀_injective_of_epi Z S.g (by
      rw [map_zero]; exact hy)
    rw [this, smul_zero]
  · exact exists_precomp_g_eq_smul hS h𝔞 Z x ha
end

variable {A : Type u} [CommRing A] [Small.{v} A] (J : Ideal A)
variable {P M : Type v} [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M]
  (N : Type v) [AddCommGroup N] [Module A N]

/-- the degree zero comparison map -/
private def ext0Comparison (X : Type v) [AddCommGroup X] [Module A X] :
    red J (Ext (ModuleCat.of A X) (ModuleCat.of A N) 0) →ₗ[A ⧸ J]
      Ext (ModuleCat.of (A ⧸ J) (red J X)) (ModuleCat.of (A ⧸ J) (red J N)) 0 :=
  ((ext0Equiv (R := A ⧸ J) (red J X) (red J N)).symm : _ →ₗ[A ⧸ J] _) ∘ₗ
    (redHom J : red J (X →ₗ[A] N) →ₗ[A ⧸ J] _) ∘ₗ
    (redEquiv J (ext0Equiv (R := A) X N) : _ →ₗ[A ⧸ J] red J (X →ₗ[A] N))

private theorem ext0Comparison_mk (X : Type v) [AddCommGroup X] [Module A X] (h : X →ₗ[A] N) :
    ext0Comparison J N X (Submodule.Quotient.mk ((ext0Equiv X N).symm h)) =
      (ext0Equiv (R := A ⧸ J) (red J X) (red J N)).symm (redMap J h) := by
  simp only [ext0Comparison, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    redEquiv_mk, LinearEquiv.apply_symm_apply, redHom_mk]

variable [IsNoetherianRing A] [Module.Finite A N]

private theorem exists_almostBij_ext0Comparison (I : Ideal A) (X : Type v) [AddCommGroup X] [Module
  A X]
    [Module.Finite A X] :
    ∃ c, ∀ n : ℕ, AlmostBij ((I ^ c).map (Ideal.Quotient.mk (I ^ n)))
      (ext0Comparison (I ^ n) N X) := by
  obtain ⟨c, hc⟩ := exists_almostBij_redHom I X N
  exact ⟨c, fun n => ((hc n).comp_equiv (redEquiv (I ^ n) (ext0Equiv X N))).equiv_comp
    (ext0Equiv (red (I ^ n) X) (red (I ^ n) N)).symm⟩

end Zero

section One
variable {A : Type u} [CommRing A] [Small.{v} A] (J : Ideal A)
variable {P M : Type v} [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M]
  (N : Type v) [AddCommGroup N] [Module A N]

/-- `Hom(Pₙ, Nₙ) → Hom(Kₙ, Nₙ)` -/
private abbrev restrictKer (f : P →ₗ[A] M) :=
  (Ext.mk₀ (ModuleCat.ofHom (redMap J (LinearMap.ker f).subtype))).precompOfLinear (A ⧸ J)
    (ModuleCat.of (A ⧸ J) (red J N)) (zero_add 0)

/-- The cokernel of `Hom(Pₙ, Nₙ) → Hom(Kₙ, Nₙ)`. -/
private abbrev cokerRestrictKer (f : P →ₗ[A] M) :=
  Ext (ModuleCat.of (A ⧸ J) (red J (LinearMap.ker f))) (ModuleCat.of (A ⧸ J) (red J N)) 0 ⧸
    LinearMap.range (restrictKer J N f)

omit [Small.{v, u} A] in
private theorem redMap_comp_eq {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [AddCommGroup Z] [Module A Z] (u : X →ₗ[A] Y) (v : Y →ₗ[A] Z) :
    redMap J (v ∘ₗ u) = redMap J v ∘ₗ redMap J u :=
  LinearMap.ext fun x => (redMap_comp J u v x).symm

private theorem ext0Comparison_naturality (X Y : Type v) [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (g : X →ₗ[A] Y) (x) :
    ext0Comparison J N X (redMap J ((Ext.mk₀ (ModuleCat.ofHom g)).precompOfLinear A
      (ModuleCat.of A N) (zero_add 0)) x) =
    (Ext.mk₀ (ModuleCat.ofHom (redMap J g))).precompOfLinear (A ⧸ J)
      (ModuleCat.of (A ⧸ J) (red J N)) (zero_add 0) (ext0Comparison J N Y x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  obtain ⟨h, rfl⟩ := (ext0Equiv Y N).symm.surjective x
  rw [redMap_mk, precomp_mk₀_ext0Equiv_symm, ext0Comparison_mk, ext0Comparison_mk,
    precomp_mk₀_ext0Equiv_symm]
  rw [redMap_comp_eq]

private theorem exists_almostBij_top [Module.Free A P] {f : P →ₗ[A] M} (hf : Function.Surjective f)
    (𝔞 : Ideal (A ⧸ J)) (hP : AlmostBij 𝔞 (ext0Comparison J N P))
    (hK : AlmostBij 𝔞 (ext0Comparison J N (LinearMap.ker f))) :
    ∃ γ : red J (Ext (ModuleCat.of A M) (ModuleCat.of A N) 1) →ₗ[A ⧸ J] cokerRestrictKer J N f,
      AlmostBij (𝔞 * 𝔞) γ := by
  have hS := LinearMap.shortExact_shortComplexKer hf
  obtain ⟨hsurj, hex, hzero⟩ := exact_precomp_extClass_zero hS (ModuleCat.of A N)
  have hsurj' := redMap_surjective J hsurj
  obtain ⟨γ, hγ⟩ := exists_cokernel_map _ _ (restrictKer J N f)
    (LinearMap.range (restrictKer J N f)).mkQ (ext0Comparison J N P)
    (ext0Comparison J N (LinearMap.ker f)) hsurj' (redMap_exact J hsurj hex)
    (fun x => by simp) (fun x => ext0Comparison_naturality J N _ _ _ x)
  refine ⟨γ, almostBij_cokernel _ _ (restrictKer J N f) (LinearMap.range (restrictKer J N f)).mkQ
    (ext0Comparison J N P) (ext0Comparison J N (LinearMap.ker f)) γ hsurj' ?_
    (Submodule.mkQ_surjective _) ?_ (fun x => ext0Comparison_naturality J N _ _ _ x) hγ
    hP.2 hK⟩
  · intro x
    rw [redMap_comp]
    have : hS.extClass.precompOfLinear A (ModuleCat.of A N) (add_comm 1 0) ∘ₗ
        (Ext.mk₀ (LinearMap.shortComplexKer f).f).precompOfLinear A (ModuleCat.of A N) (zero_add 0)
          = 0 :=
      LinearMap.ext hzero
    rw [this]
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  · intro y hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    exact hy

end One

section Bottom
variable {A : Type u} [CommRing A] [Small.{v} A] (J : Ideal A)
variable {P M : Type v} [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M]
  (N : Type v) [AddCommGroup N] [Module A N]

omit [Small.{v} A] in
private theorem subtype_comp_toKerRed (f : P →ₗ[A] M) :
    (kerRed J f).subtype ∘ₗ toKerRed J f = redMap J (LinearMap.ker f).subtype := rfl

private theorem exists_almostBij_bottom [Module.Free A P] {f : P →ₗ[A] M} (hf : Function.Surjective
  f)
    (𝔟 : Ideal A)
    (hAR : ∀ x : red J (LinearMap.ker f), redMap J (LinearMap.ker f).subtype x = 0 →
      ∀ a ∈ 𝔟, a • x = 0) :
    ∃ γ : Ext (ModuleCat.of (A ⧸ J) (red J M)) (ModuleCat.of (A ⧸ J) (red J N)) 1 →ₗ[A ⧸ J]
        cokerRestrictKer J N f,
      AlmostBij (𝔟.map (Ideal.Quotient.mk J) * 𝔟.map (Ideal.Quotient.mk J)) γ := by
  have := projective_red J (X := P)
  have hS := LinearMap.shortExact_shortComplexKer (redMap_surjective J hf)
  have hT := LinearMap.shortExact_shortComplexKer (toKerRed_surjective J hf)
  obtain ⟨hsurj, hex, hzero⟩ := exact_precomp_extClass_zero hS (ModuleCat.of (A ⧸ J) (red J N))
  have hβ : AlmostBij (𝔟.map (Ideal.Quotient.mk J))
      ((Ext.mk₀ (ModuleCat.ofHom (toKerRed J f))).precompOfLinear (A ⧸ J)
        (ModuleCat.of (A ⧸ J) (red J N)) (zero_add 0)) := by
    exact almostBij_precomp_g_zero hT _
      (smul_eq_zero_of_map_ker J 𝔟 fun x hx => hAR x (congrArg Subtype.val hx)) _
  have hsq : ∀ x, (Ext.mk₀ (ModuleCat.ofHom (toKerRed J f))).precompOfLinear (A ⧸ J)
        (ModuleCat.of (A ⧸ J) (red J N)) (zero_add 0)
        ((Ext.mk₀ (LinearMap.shortComplexKer (redMap J f)).f).precompOfLinear (A ⧸ J)
          (ModuleCat.of (A ⧸ J) (red J N)) (zero_add 0) x) =
      restrictKer J N f (LinearMap.id (R := A ⧸ J) x) := by
    intro x
    rw [precomp_apply, precomp_apply, precomp_apply, Ext.mk₀_comp_mk₀_assoc, LinearMap.id_apply]
    rfl
  obtain ⟨γ, hγ⟩ := exists_cokernel_map _ _ (restrictKer J N f)
    (LinearMap.range (restrictKer J N f)).mkQ LinearMap.id _ hsurj hex
    (fun x => by simp) hsq
  refine ⟨γ, almostBij_cokernel _ _ (restrictKer J N f) (LinearMap.range (restrictKer J N f)).mkQ
    LinearMap.id _ γ hsurj hzero
    (Submodule.mkQ_surjective _) ?_ hsq hγ (fun x a _ => ⟨a • x, rfl⟩) hβ⟩
  intro y hy
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  exact hy

end Bottom

section Main
attribute [local instance] Pres.acg Pres.mod Pres.free Pres.fin
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A] {I : Ideal A}
  {M N : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
  [AddCommGroup N] [Module A N] [Module.Finite A N]

omit [IsNoetherianRing A] [Small.{v} A] in
private theorem ideal_map_pow_mul (c : ℕ) (n : ℕ) :
    (I ^ c).map (Ideal.Quotient.mk (I ^ n)) * (I ^ c).map (Ideal.Quotient.mk (I ^ n)) =
      (I ^ (c + c)).map (Ideal.Quotient.mk (I ^ n)) := by
  rw [pow_add, Ideal.map_mul]

private theorem iso_zero (I : Ideal A) :
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    Nonempty (extAdicQuotientSystem I M N 0 ≅ extOfAdicQuotientsSystem I M N 0) := by
  obtain ⟨c, hc⟩ := exists_almostBij_ext0Comparison N I M
  exact nonempty_iso_of_almostBij _ _ c (fun n => ext0Comparison (I ^ (n : ℕ)) N M)
    (fun n => hc n)

private theorem iso_one (I : Ideal A) :
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    Nonempty (extAdicQuotientSystem I M N 1 ≅ extOfAdicQuotientsSystem I M N 1) := by
  let := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
  obtain ⟨p⟩ := nonempty_pres (A := A) M
  obtain ⟨c₁, hc₁⟩ := exists_almostBij_ext0Comparison N I p.P
  obtain ⟨c₂, hc₂⟩ := exists_almostBij_ext0Comparison N I (LinearMap.ker p.f)
  obtain ⟨c₃, hc₃⟩ := exists_pow_smul_ker_redMap_subtype I (LinearMap.ker p.f)
  let c := c₁ + c₂ + c₃
  have hle : ∀ (n : ℕ) (d : ℕ), d ≤ c →
      (I ^ c).map (Ideal.Quotient.mk (I ^ n)) ≤ (I ^ d).map (Ideal.Quotient.mk (I ^ n)) :=
    fun n d hd => Ideal.map_mono (Ideal.pow_le_pow_right hd)
  have hfin : ∀ n : ℕ+, Module.Finite (A ⧸ I ^ (n : ℕ))
      (cokerRestrictKer (I ^ (n : ℕ)) N p.f) := by
    intro n
    let : IsNoetherianRing (A ⧸ I ^ (n : ℕ)) := isNoetherian_of_tower A inferInstance
    have : Module.Finite (A ⧸ I ^ (n : ℕ)) (Ext (ModuleCat.of (A ⧸ I ^ (n : ℕ))
        (red (I ^ (n : ℕ)) (LinearMap.ker p.f)))
        (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (red (I ^ (n : ℕ)) N)) 0) :=
      ModuleCat.finite_ext _ _ _ 0
    exact Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)
  let C : AdicModuleSystem.{u, v} A I :=
    ⟨fun n => @FGModuleCat.of _ _ (cokerRestrictKer (I ^ (n : ℕ)) N p.f) _ _ (hfin n)⟩
  have top : ∀ n : ℕ+, ∃ γ : red (I ^ (n : ℕ)) (Ext (ModuleCat.of A M) (ModuleCat.of A N) 1)
      →ₗ[A ⧸ I ^ (n : ℕ)] cokerRestrictKer (I ^ (n : ℕ)) N p.f,
      AlmostBij ((I ^ (c + c)).map (Ideal.Quotient.mk (I ^ (n : ℕ)))) γ := by
    intro n
    obtain ⟨γ, hγ⟩ := exists_almostBij_top (I ^ (n : ℕ)) N p.surj _
      ((hc₁ n).mono (hle n c₁ (by omega))) ((hc₂ n).mono (hle n c₂ (by omega)))
    exact ⟨γ, by rw [← ideal_map_pow_mul]; exact hγ⟩
  have bot : ∀ n : ℕ+, ∃ γ : Ext (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (red (I ^ (n : ℕ)) M))
        (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (red (I ^ (n : ℕ)) N)) 1
      →ₗ[A ⧸ I ^ (n : ℕ)] cokerRestrictKer (I ^ (n : ℕ)) N p.f,
      AlmostBij ((I ^ (c + c)).map (Ideal.Quotient.mk (I ^ (n : ℕ)))) γ := by
    intro n
    obtain ⟨γ, hγ⟩ := exists_almostBij_bottom (I ^ (n : ℕ)) N p.surj (I ^ c)
      (fun x hx a ha => hc₃ n x hx a (Ideal.pow_le_pow_right (by omega) ha))
    exact ⟨γ, by rw [← ideal_map_pow_mul]; exact hγ⟩
  choose γ₁ hγ₁ using top
  choose γ₂ hγ₂ using bot
  obtain ⟨e₁⟩ := nonempty_iso_of_almostBij (extAdicQuotientSystem I M N 1) C (c + c) (fun n => γ₁ n)
    hγ₁
  obtain ⟨e₂⟩ := nonempty_iso_of_almostBij (extOfAdicQuotientsSystem I M N 1) C (c + c) (fun n => γ₂
    n) hγ₂
  exact ⟨e₁.trans e₂.symm⟩


private theorem iso_shift_quot (I : Ideal A) (p : Pres (A := A) M) (i : ℕ) :
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    Nonempty (extOfAdicQuotientsSystem I (LinearMap.ker p.f) N (i + 1) ≅
      extOfAdicQuotientsSystem I M N (i + 2)) := by
  let := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
  obtain ⟨c, hc⟩ := exists_pow_smul_ker_redMap_subtype I (LinearMap.ker p.f)
  have hfin : ∀ n : ℕ+, Module.Finite (A ⧸ I ^ (n : ℕ))
      (Ext (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (kerRed (I ^ (n : ℕ)) p.f))
        (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (red (I ^ (n : ℕ)) N)) (i + 1)) := by
    intro n
    let : IsNoetherianRing (A ⧸ I ^ (n : ℕ)) := isNoetherian_of_tower A inferInstance
    exact ModuleCat.finite_ext _ _ _ _
  let D : AdicModuleSystem.{u, v} A I :=
    ⟨fun n => @FGModuleCat.of _ _ (Ext (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (kerRed (I ^ (n : ℕ)) p.f))
        (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (red (I ^ (n : ℕ)) N)) (i + 1)) _ _ (hfin n)⟩
  obtain ⟨e₁⟩ := nonempty_iso_of_almostBij D (extOfAdicQuotientsSystem I (LinearMap.ker p.f) N (i +
    1))
    c (fun n => (Ext.mk₀ (ModuleCat.ofHom (toKerRed (I ^ (n : ℕ)) p.f))).precompOfLinear
      (A ⧸ I ^ (n : ℕ)) (ModuleCat.of (A ⧸ I ^ (n : ℕ)) (red (I ^ (n : ℕ)) N)) (zero_add (i + 1)))
    (fun n => almostBij_toKerRed_precomp (I ^ (n : ℕ)) N p.surj (I ^ c) (hc n) i)
  have hsh : ∀ n : ℕ+, Nonempty ((D.module n).obj ≃ₗ[A ⧸ I ^ (n : ℕ)]
      ((extOfAdicQuotientsSystem I M N (i + 2)).module n).obj) :=
    fun n => shift_quot (I ^ (n : ℕ)) N p.surj i
  obtain ⟨e₂⟩ := nonempty_iso_of_equiv D (extOfAdicQuotientsSystem I M N (i + 2))
    (fun n => (hsh n).some)
  exact ⟨e₁.symm.trans e₂⟩

private theorem iso_all (I : Ideal A) (i : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M],
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    Nonempty (extAdicQuotientSystem I M N i ≅ extOfAdicQuotientsSystem I M N i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro M _ _ _
  let := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
  match i, ih with
  | 0, _ => exact iso_zero I
  | 1, _ => exact iso_one I
  | j + 2, ih =>
    obtain ⟨p⟩ := nonempty_pres (A := A) M
    obtain ⟨e₁⟩ := iso_shift_base (I := I) (N := N) p j
    obtain ⟨e₂⟩ := ih (j + 1) (by omega) (LinearMap.ker p.f)
    obtain ⟨e₃⟩ := iso_shift_quot (N := N) I p j
    exact ⟨e₁.symm.trans (e₂.trans e₃)⟩
end Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]

/-- **Stacks 0EGY.** For finite modules over a Noetherian ring, the system of adic
quotients of `Ext` is isomorphic, in the category of delayed morphisms, to the system of
`Ext` groups over the corresponding quotient rings. -/
@[stacks 0EGY]
public theorem extAdicQuotientSystem_iso_extOfAdicQuotientsSystem
    (I : Ideal A) (M N : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (i : ℕ) :
    letI := (AdicModuleSystem.delayedCategory (A := A) (I := I)).toCategory
    Nonempty (extAdicQuotientSystem I M N i ≅ extOfAdicQuotientsSystem I M N i) :=
  iso_all (N := N) I i M

end Stacks.AdicSystem.ExtDelayedIso

end

end

end
