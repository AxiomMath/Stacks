module

public import Mathlib.RingTheory.Etale.Kaehler
public import StacksFrontier.RingTheory.Unramified.Thickening

/-!
# Extending derivations along a universal first order thickening

Let `A → B' → B` be ring maps with `B' → B` the universal first order thickening of `B` over
`A`.  Stacks 04EF says that `B'` is formally unramified over `A` and that the canonical map
`Ω_{A} ⊗_A B → Ω_{B'} ⊗_{B'} B` is an isomorphism.  Read through the universal property of the
modules of differentials this is a statement about derivations: every derivation of `A` with
values in a `B'`-module on which the kernel of `B' → B` acts by zero extends uniquely to a
derivation of `B'`.  This file records that reading, together with the elementary fact behind
the uniqueness: a derivation of a formally unramified `A`-algebra is determined by its values on
the image of `A`.

Derivations are written here as additive maps satisfying the Leibniz rule for the scalar action
of the source ring, rather than as `Derivation`s: the consumers of these statements are
derivations of sheaves of rings read on the sections over one object, where the module over the
smaller ring is only available through the ring map.

## Main definitions

* `RingHom.IsUniversalFirstOrderThickening`: a ring map `φ : A →+* B'` together with an ideal
  `I` of `B'` exhibits `B'` as the universal first order thickening of `B'/I` over `A`.

## Main results

* `Algebra.FormallyUnramified.eq_of_leibniz`: two Leibniz maps out of a formally unramified
  `A`-algebra which agree on the image of `A` are equal.
* `Algebra.FormallyEtale.existsUnique_leibniz`: a Leibniz map out of `A` extends uniquely to a
  Leibniz map out of a formally étale `A`-algebra.
* `Algebra.Extension.IsUniversalFirstOrderThickening.existsUnique_leibniz_of_base`: a Leibniz
  map out of `A` vanishing on a base ring `R`, with values in a `B'`-module killed by the kernel of
  `B' → B`, extends uniquely to a Leibniz map out of `B'`.
* `RingHom.IsUniversalFirstOrderThickening.leibniz_ext` and
  `RingHom.IsUniversalFirstOrderThickening.existsUnique_leibniz`: the same two statements for a
  ring map `φ : A →+* B'` exhibiting `B'` as the universal first order thickening of `B'/I`.

## References

* [Stacks Project, Tag 04EF](https://stacks.math.columbia.edu/tag/04EF)
* [Stacks Project, Tag 00UO](https://stacks.math.columbia.edu/tag/00UO)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

section Unique

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module B N]

/-- **A derivation of a formally unramified algebra is determined by its values on the base.**
Two additive maps `B → N` satisfying the Leibniz rule, `B` being formally unramified over `A`,
which agree on the image of `A` are equal: their difference is an `A`-derivation, and the
`A`-derivations of `B` are the linear maps out of `Ω_{B/A} = 0`. -/
theorem FormallyUnramified.eq_of_leibniz [FormallyUnramified A B] (d₁ d₂ : B →+ N)
    (h₁ : ∀ x y, d₁ (x * y) = x • d₁ y + y • d₁ x)
    (h₂ : ∀ x y, d₂ (x * y) = x • d₂ y + y • d₂ x)
    (h : ∀ a : A, d₁ (algebraMap A B a) = d₂ (algebraMap A B a)) : d₁ = d₂ := by
  let : Module A N := Module.compHom N (algebraMap A B)
  have : IsScalarTower A B N := .of_algebraMap_smul fun _ _ => rfl
  have hd0 : ∀ a : A, (d₁ - d₂) (algebraMap A B a) = 0 := fun a => by
    rw [AddMonoidHom.sub_apply, h a, sub_self]
  have hleib : ∀ x y, (d₁ - d₂) (x * y) = x • (d₁ - d₂) y + y • (d₁ - d₂) x := by
    intro x y
    simp only [AddMonoidHom.sub_apply, h₁, h₂, smul_sub]
    abel
  let L : B →ₗ[A] N :=
    { toFun := d₁ - d₂
      map_add' := fun x y => map_add (d₁ - d₂) x y
      map_smul' := fun a x => by
        change (d₁ - d₂) (a • x) = a • (d₁ - d₂) x
        rw [Algebra.smul_def, hleib, hd0, smul_zero, add_zero]
        rfl }
  let D : Derivation A B N := Derivation.mk' L hleib
  have hD : D = 0 := by
    have hlin : (KaehlerDifferential.linearMapEquivDerivation A B).symm D = 0 :=
      LinearMap.ext fun ω => by
        rw [Subsingleton.elim ω 0, map_zero, LinearMap.zero_apply]
    have := congrArg (KaehlerDifferential.linearMapEquivDerivation A B) hlin
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  ext x
  exact sub_eq_zero.mp (DFunLike.congr_fun hD x)

/-- Uniqueness from existence of a Leibniz extension along a formally unramified algebra. -/
private theorem existsUnique_leibniz_of_exists [FormallyUnramified A B] {δ : A →+ N}
    (h : ∃ d : B →+ N, (∀ x y, d (x * y) = x • d y + y • d x) ∧
      ∀ a, d (algebraMap A B a) = δ a) :
    ∃! d : B →+ N, (∀ x y, d (x * y) = x • d y + y • d x) ∧
      ∀ a, d (algebraMap A B a) = δ a :=
  existsUnique_of_exists_of_unique h fun d₁ d₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ =>
    FormallyUnramified.eq_of_leibniz d₁ d₂ h₁ h₂ fun a => (h₁' a).trans (h₂' a).symm

/-- A linear map out of `Ω_{S/R}` gives a Leibniz map `S → N` with the prescribed values on the
image of `A`. -/
private theorem exists_leibniz_of_kaehler (R : Type*) {A S N : Type*} [CommRing R] [CommRing A]
    [CommRing S] [Algebra R S] [Algebra A S] [AddCommGroup N] [Module S N]
    (g : Ω[S⁄R] →ₗ[S] N) (δ : A →+ N)
    (h : ∀ a, g (KaehlerDifferential.D R S (algebraMap A S a)) = δ a) :
    ∃ d : S →+ N, (∀ x y, d (x * y) = x • d y + y • d x) ∧ ∀ a, d (algebraMap A S a) = δ a :=
  ⟨AddMonoidHom.mk' (fun x => g (KaehlerDifferential.D R S x)) fun x y => by rw [map_add, map_add],
    fun x y => by
      change g (KaehlerDifferential.D R S (x * y)) =
        x • g (KaehlerDifferential.D R S y) + y • g (KaehlerDifferential.D R S x)
      rw [(KaehlerDifferential.D R S).leibniz x y, map_add, map_smul, map_smul], h⟩

/-- A Leibniz `R`-linear map out of `A` factors through `Ω_{A/R}`. -/
private theorem exists_linearMap_kaehler_of_leibniz (R : Type*) {A N : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (δ : A →ₗ[R] N) (hδ : ∀ a b, δ (a * b) = a • δ b + b • δ a) :
    ∃ f : Ω[A⁄R] →ₗ[A] N, ∀ a, f (KaehlerDifferential.D R A a) = δ a :=
  ⟨(Derivation.mk' δ hδ).liftKaehlerDifferential,
    fun a => Derivation.liftKaehlerDifferential_comp_D _ a⟩

end Unique

section Etale

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module B N]

/-- **A derivation extends uniquely along a formally étale algebra.**  Let `B` be a formally
étale `A`-algebra and `N` a `B`-module.  Every additive map `δ : A → N` satisfying the Leibniz
rule for the action of `A` through `A → B` extends uniquely to an additive map `B → N`
satisfying the Leibniz rule.

Existence is the isomorphism `B ⊗_A Ω_A ≅ Ω_B` of
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`; uniqueness is
`Algebra.FormallyUnramified.eq_of_leibniz`. -/
theorem FormallyEtale.existsUnique_leibniz [FormallyEtale A B] (δ : A →+ N)
    (hδ : ∀ a b, δ (a * b) = algebraMap A B a • δ b + algebraMap A B b • δ a) :
    ∃! d : B →+ N, (∀ x y, d (x * y) = x • d y + y • d x) ∧
      ∀ a, d (algebraMap A B a) = δ a := by
  refine existsUnique_leibniz_of_exists ?_
  let : Module A N := Module.compHom N (algebraMap A B)
  have : IsScalarTower A B N := .of_algebraMap_smul fun _ _ => rfl
  obtain ⟨f, hf⟩ := exists_linearMap_kaehler_of_leibniz ℤ δ.toIntLinearMap hδ
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B
  refine exists_leibniz_of_kaehler ℤ ((f.liftBaseChange B).comp e.symm.toLinearMap) δ fun a => ?_
  change (f.liftBaseChange B) (e.symm (KaehlerDifferential.D ℤ B (algebraMap A B a))) = δ a
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul]
  exact hf a

end Etale


namespace Extension.IsUniversalFirstOrderThickening

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Stacks 04EF, read on derivations.**  Let `P.Ring → B` be the universal first order
thickening of `B` over `A`, and let `N` be a `P.Ring`-module on which the kernel of
`P.Ring → B` acts by zero.  Then every additive map `δ : A → N` satisfying the Leibniz rule for
the action of `A` through `A → P.Ring` extends uniquely to an additive map `P.Ring → N`
satisfying the Leibniz rule.

Existence is the bijectivity of `Ω_{A} ⊗_A B → Ω_{P.Ring} ⊗_{P.Ring} B`, the module `N` being a
`B`-module; uniqueness is the formal unramifiedness of `P.Ring` over `A`, through
`Algebra.FormallyUnramified.eq_of_leibniz`. -/
theorem existsUnique_leibniz_of_base (R : Type*) [CommRing R] [Algebra R A] [Algebra R B]
    [IsScalarTower R A B] {P : Extension.{u} A B} (hP : P.IsUniversalFirstOrderThickening)
    {N : Type*} [AddCommGroup N] [Module P.Ring N]
    (hN : ∀ x : P.Ring, algebraMap P.Ring B x = 0 → ∀ n : N, x • n = 0)
    (δ : A →+ N)
    (hδ : ∀ a b, δ (a * b) = algebraMap A P.Ring a • δ b + algebraMap A P.Ring b • δ a)
    (hδR : ∀ r : R, δ (algebraMap R A r) = 0) :
    ∃! d : P.Ring →+ N, (∀ x y, d (x * y) = x • d y + y • d x) ∧
      ∀ a, d (algebraMap A P.Ring a) = δ a := by
  obtain ⟨hfu, hbij⟩ := formallyUnramified_ring_and_bijective_map R hP
  have : FormallyUnramified A P.Ring := hfu
  refine existsUnique_leibniz_of_exists ?_
  have hq : Function.Surjective (algebraMap P.Ring B) := P.algebraMap_surjective
  -- The `B`-module structure on `N`.
  have hsmul0 : ∀ (c c' : P.Ring), algebraMap P.Ring B c = algebraMap P.Ring B c' →
      ∀ n : N, c • n = c' • n := by
    intro c c' hcc' n
    have h0 := hN (c - c') (by rw [map_sub, hcc', sub_self]) n
    rwa [sub_smul, sub_eq_zero] at h0
  let : SMul B N := ⟨fun b n => Function.surjInv hq b • n⟩
  have hsmul : ∀ (c : P.Ring) (n : N), algebraMap P.Ring B c • n = c • n := fun c n =>
    hsmul0 _ _ (Function.surjInv_eq hq _) n
  let : Module B N := Function.Surjective.moduleLeft (algebraMap P.Ring B) hq hsmul
  have : IsScalarTower P.Ring B N := ⟨fun c b n => by
    rw [Algebra.smul_def, mul_smul, hsmul]⟩
  let : Module A N := Module.compHom N (algebraMap A P.Ring)
  have : IsScalarTower A B N := ⟨fun a b n => by
    change (a • b) • n = algebraMap A P.Ring a • (b • n)
    rw [Algebra.smul_def, mul_smul, IsScalarTower.algebraMap_apply A P.Ring B, hsmul]⟩
  -- `δ` as a derivation, and the linear map out of `Ω_A` it induces.
  let : Module R N := Module.compHom N (algebraMap R A)
  have : IsScalarTower R A N := .of_algebraMap_smul fun _ _ => rfl
  obtain ⟨f, hf⟩ := exists_linearMap_kaehler_of_leibniz R
    { toFun := δ
      map_add' := map_add δ
      map_smul' := fun r a => by
        change δ (r • a) = algebraMap R A r • δ a
        rw [Algebra.smul_def, hδ, hδR, smul_zero, add_zero]
        rfl } hδ
  let ψ := LinearEquiv.ofBijective _ hbij
  let g' : B ⊗[P.Ring] Ω[P.Ring⁄R] →ₗ[B] N := (f.liftBaseChange B).comp ψ.symm.toLinearMap
  refine exists_leibniz_of_kaehler R
    ((g'.restrictScalars P.Ring).comp (TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1)) δ fun a => ?_
  have hψ : ψ (1 ⊗ₜ KaehlerDifferential.D R A a) =
      1 ⊗ₜ KaehlerDifferential.D R P.Ring (algebraMap A P.Ring a) := by
    change ((((TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1).restrictScalars A).comp
      (KaehlerDifferential.map R R A P.Ring)).liftBaseChange B) _ = _
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    simp
  change g' (1 ⊗ₜ KaehlerDifferential.D R P.Ring (algebraMap A P.Ring a)) = δ a
  rw [← hψ]
  change (f.liftBaseChange B) (ψ.symm (ψ _)) = δ a
  rw [LinearEquiv.symm_apply_apply, LinearMap.liftBaseChange_tmul, one_smul]
  exact hf a

end Extension.IsUniversalFirstOrderThickening

end Algebra

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- A ring map `φ : A → B` together with an ideal `I ⊆ B` **is a universal first order
thickening** when `B → B ⧸ I` is the universal first order thickening of the `A`-algebra
`B ⧸ I`, the `A`-algebra structures being those of `φ`. -/
def IsUniversalFirstOrderThickening (φ : A →+* B) (I : Ideal B) : Prop :=
  letI := φ.toAlgebra
  (Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ A I)
    Ideal.Quotient.mk_surjective).IsUniversalFirstOrderThickening

namespace IsUniversalFirstOrderThickening

variable {φ : A →+* B} {I : Ideal B}

/-- **A derivation of the thickening is determined by its values on the base.** -/
theorem leibniz_ext (h : φ.IsUniversalFirstOrderThickening I) {N : Type*} [AddCommGroup N]
    [Module B N] (d₁ d₂ : B →+ N)
    (h₁ : ∀ x y, d₁ (x * y) = x • d₁ y + y • d₁ x)
    (h₂ : ∀ x y, d₂ (x * y) = x • d₂ y + y • d₂ x)
    (he : ∀ a : A, d₁ (φ a) = d₂ (φ a)) : d₁ = d₂ := by
  let := φ.toAlgebra
  have : Algebra.FormallyUnramified A B :=
    (Algebra.Extension.IsUniversalFirstOrderThickening.formallyUnramified_ring_and_bijective_map
      ℤ h).1
  exact Algebra.FormallyUnramified.eq_of_leibniz d₁ d₂ h₁ h₂ he

/-- **A derivation of the base extends uniquely to the thickening**, with values in a module on
which `I` acts by zero. -/
theorem existsUnique_leibniz (h : φ.IsUniversalFirstOrderThickening I) {N : Type*}
    [AddCommGroup N] [Module B N] (hN : ∀ x ∈ I, ∀ n : N, x • n = 0) (δ : A →+ N)
    (hδ : ∀ a b, δ (a * b) = φ a • δ b + φ b • δ a) :
    ∃! d : B →+ N, (∀ x y, d (x * y) = x • d y + y • d x) ∧ ∀ a, d (φ a) = δ a := by
  let := φ.toAlgebra
  have h1 : δ 1 = 0 := by
    have := hδ 1 1
    rw [mul_one, φ.map_one, one_smul] at this
    exact left_eq_add.mp this
  let : Module (Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ A I)
    Ideal.Quotient.mk_surjective).Ring N := (inferInstance : Module B N)
  refine Algebra.Extension.IsUniversalFirstOrderThickening.existsUnique_leibniz_of_base ℤ h
    (N := N) (fun x hx n => hN x (Ideal.Quotient.eq_zero_iff_mem.mp hx) n) δ hδ fun n => ?_
  rw [show algebraMap ℤ A n = n • (1 : A) by simp, map_zsmul, h1, smul_zero]

/-- A universal first order thickening of rings may be recognised on any surjection with kernel
`I`, rather than on the quotient map by `I`. -/
theorem of_ofSurjective [Algebra A B] (hφ : algebraMap A B = φ) {C : Type u} [CommRing C]
    [Algebra A C] (q : B →ₐ[A] C) (hq : Function.Surjective q) (hker : RingHom.ker q = I)
    (h : (Algebra.Extension.ofSurjective q hq).IsUniversalFirstOrderThickening) :
    φ.IsUniversalFirstOrderThickening I := by
  subst hφ hker
  have halg : (algebraMap A B).toAlgebra = ‹Algebra A B› :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold IsUniversalFirstOrderThickening
  rw [halg]
  let e : C ≃ₐ[A] B ⧸ RingHom.ker q := (Ideal.quotientKerAlgEquivOfSurjective hq).symm
  refine ⟨?_, ?_⟩
  · change (RingHom.ker (Ideal.Quotient.mk (RingHom.ker q))) ^ 2 = ⊥
    rw [Ideal.mk_ker]
    exact h.ker_sq_eq_bot
  · intro T _ _ J hJ a
    have he : ∀ x : B, e (q x) = Ideal.Quotient.mk (RingHom.ker q) x := fun x => by
      rw [← Ideal.quotientKerAlgEquivOfSurjective_mk hq x]
      exact e.apply_symm_apply _
    obtain ⟨a', ha', hu⟩ := h.existsUnique_lift J hJ (a.comp e.toAlgHom)
    refine ⟨a', ?_, fun b hb => hu b ?_⟩
    · exact AlgHom.ext fun x =>
        (congrArg (fun F : B →ₐ[A] T ⧸ J => F x) ha').trans (congrArg a (he x))
    · exact AlgHom.ext fun x =>
        (congrArg (fun F : B →ₐ[A] T ⧸ J => F x) hb).trans (congrArg a (he x).symm)

end IsUniversalFirstOrderThickening

end RingHom
