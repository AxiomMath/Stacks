module

public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# Splitting a square-zero object of `𝒞_Λ` along a derivation

Let `A` be an object of `𝒞_Λ` whose maximal ideal has square zero, let `q : A → k` be its
augmentation and let `D : A → k` be a `Λ`-derivation over `q` which does not vanish on the
maximal ideal, say `D t = 1` with `t ∈ m_A`. Then

* `A' = {a ∈ A | D a = 0}` is a subalgebra over which `A` splits: the map
  `ψ : a ↦ a - D(a) t` is a retraction of `A` onto `A'` in `𝒞_Λ`, and
* `A` is the fibre product `A' ×_k k[ε]` over `k`: for every `a' ∈ A'` and every `c ∈ k`
  there is exactly one `a ∈ A` with `ψ a = a'` and `D a = c`.

This is the ring-theoretic step of the proof of Stacks 06T8, where `A = R/m_R²` for the
complete local algebra `R` underlying a minimal versal formal object: the identity
`m_R/m_R² = m_{R'}/m_R² + k·t̄` and the isomorphism `R'/m_R² ×_k k[ε] ≅ R/m_R²` sending `ε`
to `t̄`. The last conclusion is the one the contradiction uses: no section of `ψ` is
surjective, because `ψ t = 0` while `t ≠ 0`, so `t` is in the image of no section.

## Main results

* `Deformation.exists_derivationSplitting`: the splitting, the fibre-product property in
  element form, and the non-surjectivity of every section.

## Implementation notes

The derivation is taken as a `Λ`-linear map together with the Leibniz rule over an
explicitly supplied augmentation `q`, rather than as a `Derivation`, so that no module
structure on `k` through `A` has to be installed; `Deformation.Derivations` bakes in a
different one and reconciling them is pure friction here. The augmentation is supplied with
the hypothesis that it induces the object's chosen residue-field identification, which is
what makes the morphisms below morphisms of `𝒞_Λ`.

The fibre-product property is stated in element form — "for every `a'` and `c` there is
exactly one `a`" — rather than as an `IsPullback` square against the dual numbers. The two
are equivalent, since a point of `A' ×_k k[ε]` is a pair `(a', c)` with the `k`-component of
the dual number forced by `a'`; the element form avoids the dual-number object and its
universe lift entirely, and the square is one short step from it.

`ψ` is `a ↦ a - s(D a) t` for a chosen set-theoretic section `s` of `q`. It is independent of
the choice because multiplication by `t` only sees residues: `x - y ∈ m_A` implies
`(x - y) t ∈ m_A² = 0`. That single cancellation is what makes `ψ` multiplicative.

## References

* [Stacks Project, Tag 06T8](https://stacks.math.columbia.edu/tag/06T8)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

universe u v w

namespace DerivationSplitting

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {A : ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- An element of an object of `𝒞_Λ` is in the maximal ideal exactly when the augmentation
kills it. -/
public theorem aug_eq_zero_iff (q : A →ₐ[Λ] k)
    (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) (a : A) :
    q a = 0 ↔ a ∈ maximalIdeal A := by
  rw [← residue_eq_zero_iff]
  exact ⟨fun h => A.residueEquiv.injective (by rw [map_zero, hq, h]),
    fun h => by rw [← hq, h, map_zero]⟩

/-- The augmentation of an object of `𝒞_Λ` is surjective. -/
public theorem aug_surjective (q : A →ₐ[Λ] k)
    (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) : Function.Surjective q := by
  intro c
  obtain ⟨a, ha⟩ := residue_surjective (A.residueEquiv.symm c)
  exact ⟨a, by rw [← hq, ha, A.residueEquiv.apply_symm_apply]⟩

/-- A product of two elements of a square-zero maximal ideal vanishes. -/
public theorem mul_eq_zero_of_mem (hA : maximalIdeal A ^ 2 = ⊥) {t : A}
    (ht : t ∈ maximalIdeal A) {z : A} (hz : z ∈ maximalIdeal A) : z * t = 0 := by
  have h : z * t ∈ maximalIdeal A ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hz ht
  rw [hA] at h
  simpa using h

/-- A derivation over the augmentation kills `1`. -/
public theorem map_one_eq_zero (q : A →ₐ[Λ] k) (D : A →ₗ[Λ] k)
    (hD : ∀ a b : A, D (a * b) = q a * D b + q b * D a) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, map_one q, one_mul] at h
  linear_combination -h

/-- A derivation over the augmentation kills the structure map. -/
public theorem map_algebraMap_eq_zero (q : A →ₐ[Λ] k) (D : A →ₗ[Λ] k)
    (hD : ∀ a b : A, D (a * b) = q a * D b + q b * D a) (r : Λ) :
    D (algebraMap Λ A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one_eq_zero q D hD, smul_zero]

/-- A chosen set-theoretic section of the augmentation. -/
public noncomputable def sec (q : A →ₐ[Λ] k)
    (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) : k → A :=
  Function.surjInv (aug_surjective q hq)

/-- The chosen section is a section. -/
public theorem aug_sec (q : A →ₐ[Λ] k)
    (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) (c : k) : q (sec q hq c) = c :=
  Function.surjInv_eq (aug_surjective q hq) c

/-- Multiplication by an element of a square-zero maximal ideal only sees residues. -/
public theorem mul_congr (hA : maximalIdeal A ^ 2 = ⊥) (q : A →ₐ[Λ] k)
    (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) {t : A} (ht : t ∈ maximalIdeal A)
    {x y : A} (hxy : q x = q y) : x * t = y * t := by
  have hz : x - y ∈ maximalIdeal A := by
    rw [← aug_eq_zero_iff q hq, map_sub, hxy, sub_self]
  have h0 := mul_eq_zero_of_mem hA ht hz
  have h2 : (x - y) * t = x * t - y * t := by ring
  rw [h2, sub_eq_zero] at h0
  exact h0

/-- A lift of `0` multiplies to `0` against a square-zero element. -/
public theorem sec_zero_mul (hA : maximalIdeal A ^ 2 = ⊥) (q : A →ₐ[Λ] k)
    (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) {t : A} (ht : t ∈ maximalIdeal A) :
    sec q hq 0 * t = 0 := by
  refine mul_eq_zero_of_mem hA ht ?_
  rw [← aug_eq_zero_iff q hq, aug_sec]

/-- The retraction `a ↦ a - D(a) t` of a square-zero object of `𝒞_Λ` onto the kernel of a
derivation, as an algebra homomorphism. -/
public noncomputable def retraction (hA : maximalIdeal A ^ 2 = ⊥) (q : A →ₐ[Λ] k)
    (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) (D : A →ₗ[Λ] k)
    (hD : ∀ a b : A, D (a * b) = q a * D b + q b * D a)
    {t : A} (ht : t ∈ maximalIdeal A) : A →ₐ[Λ] A where
  toFun a := a - sec q hq (D a) * t
  map_one' := by
    rw [map_one_eq_zero q D hD, sec_zero_mul hA q hq ht, sub_zero]
  map_mul' a b := by
    have ht2 : t * t = 0 := mul_eq_zero_of_mem hA ht ht
    have e1 : (a * sec q hq (D b)) * t = sec q hq (q a * D b) * t :=
      mul_congr hA q hq ht (by rw [map_mul, aug_sec, aug_sec])
    have e2 : (b * sec q hq (D a)) * t = sec q hq (q b * D a) * t :=
      mul_congr hA q hq ht (by rw [map_mul, aug_sec, aug_sec])
    have e3 : sec q hq (D (a * b)) * t =
        (sec q hq (q a * D b) + sec q hq (q b * D a)) * t :=
      mul_congr hA q hq ht (by rw [hD a b, map_add, aug_sec, aug_sec, aug_sec])
    have hmul : (a - sec q hq (D a) * t) * (b - sec q hq (D b) * t)
        = a * b - (a * sec q hq (D b)) * t - (b * sec q hq (D a)) * t
          + (sec q hq (D a) * sec q hq (D b)) * (t * t) := by ring
    rw [hmul, ht2, mul_zero, add_zero, e1, e2, e3]
    ring
  map_zero' := by
    rw [map_zero, sec_zero_mul hA q hq ht, sub_zero]
  map_add' a b := by
    have e : sec q hq (D (a + b)) * t = (sec q hq (D a) + sec q hq (D b)) * t :=
      mul_congr hA q hq ht (by rw [map_add, map_add, aug_sec, aug_sec, aug_sec])
    rw [e]
    ring
  commutes' r := by
    rw [map_algebraMap_eq_zero q D hD, sec_zero_mul hA q hq ht, sub_zero]

section

variable (hA : maximalIdeal A ^ 2 = ⊥) (q : A →ₐ[Λ] k)
  (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) (D : A →ₗ[Λ] k)
  (hD : ∀ a b : A, D (a * b) = q a * D b + q b * D a)
  {t : A} (ht : t ∈ maximalIdeal A) (hDt : D t = 1)

include hq ht in
/-- The distinguished element lies in the kernel of the augmentation. -/
public theorem aug_eq_zero : q t = 0 := (aug_eq_zero_iff q hq t).mpr ht

/-- The defining formula for the retraction. -/
public theorem retraction_apply (a : A) :
    retraction hA q hq D hD ht a = a - sec q hq (D a) * t := rfl

include hDt in
/-- The retraction lands in the kernel of the derivation. -/
public theorem map_retraction (a : A) : D (retraction hA q hq D hD ht a) = 0 := by
  rw [retraction_apply, map_sub, hD, aug_sec, aug_eq_zero q hq ht, hDt]
  ring

/-- The retraction does not change residues. -/
public theorem aug_retraction (a : A) : q (retraction hA q hq D hD ht a) = q a := by
  rw [retraction_apply, map_sub, map_mul, aug_sec, aug_eq_zero q hq ht]
  ring

/-- The retraction fixes the kernel of the derivation. -/
public theorem retraction_eq_self (a : A) (ha : D a = 0) :
    retraction hA q hq D hD ht a = a := by
  rw [retraction_apply, ha, sec_zero_mul hA q hq ht, sub_zero]

include hDt in
/-- The retraction kills the distinguished element. -/
public theorem retraction_eq_zero : retraction hA q hq D hD ht t = 0 := by
  rw [retraction_apply, hDt]
  have h : sec q hq 1 * t = (1 : A) * t := mul_congr hA q hq ht (by rw [aug_sec, map_one])
  rw [h, one_mul, sub_self]

/-- The kernel of a derivation over the augmentation, as a subalgebra. -/
public def kernelSubalgebra : Subalgebra Λ A where
  carrier := {a : A | D a = 0}
  mul_mem' := by
    intro a b ha hb
    change D a = 0 at ha
    change D b = 0 at hb
    change D (a * b) = 0
    rw [hD, ha, hb]
    ring
  add_mem' := by
    intro a b ha hb
    change D a = 0 at ha
    change D b = 0 at hb
    change D (a + b) = 0
    rw [map_add, ha, hb]
    ring
  algebraMap_mem' := fun r => map_algebraMap_eq_zero q D hD r

/-- Membership in the kernel subalgebra is the vanishing of the derivation. -/
public theorem mem_kernelSubalgebra {a : A} : a ∈ kernelSubalgebra q D hD ↔ D a = 0 :=
  Iff.rfl

include hDt in
/-- The retraction, with target the kernel subalgebra. -/
public noncomputable def retractionRestrict : A →ₐ[Λ] kernelSubalgebra q D hD :=
  (retraction hA q hq D hD ht).codRestrict (kernelSubalgebra q D hD)
    (fun a => map_retraction hA q hq D hD ht hDt a)

include hDt in
/-- The restricted retraction computes the retraction. -/
public theorem retractionRestrict_coe (a : A) :
    ((retractionRestrict hA q hq D hD ht hDt a : kernelSubalgebra q D hD) : A) =
      retraction hA q hq D hD ht a := rfl

include hDt in
/-- The restricted retraction is surjective. -/
public theorem retractionRestrict_surjective :
    Function.Surjective (retractionRestrict hA q hq D hD ht hDt) := fun a' =>
  ⟨(a' : A), Subtype.ext (retraction_eq_self hA q hq D hD ht (a' : A) a'.2)⟩

/-- The augmentation of the kernel subalgebra. -/
public noncomputable def kernelAug : kernelSubalgebra q D hD →ₐ[Λ] k :=
  q.comp (kernelSubalgebra q D hD).val

include hA hq ht hDt in
/-- The kernel subalgebra still surjects onto the residue field. -/
public theorem kernelAug_surjective : Function.Surjective (kernelAug q D hD) := by
  intro c
  refine ⟨retractionRestrict hA q hq D hD ht hDt (sec q hq c), ?_⟩
  show q (retraction hA q hq D hD ht (sec q hq c)) = c
  rw [aug_retraction hA q hq D hD ht, aug_sec]

end

end DerivationSplitting

open DerivationSplitting in
/-- The ring-theoretic step of **Stacks Project, Tag 06T8**. Let `A` be an object of `𝒞_Λ`
whose maximal ideal has square zero, with augmentation `q`, and let `D` be a `Λ`-derivation
of `A` into `k` over `q` with `D t = 1` for some `t` in the maximal ideal. Then `A` splits
over the subobject `A'` cut out by `D`: there is a retraction `ψ : A ⟶ A'` of the inclusion,
`A` is the fibre product of `A'` and the dual numbers over `k` — for every `a' : A'` and
every `c : k` exactly one `a : A` has `ψ a = a'` and `D a = c` — and no section of `ψ` is
surjective. -/
public theorem exists_derivationSplitting {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hA : maximalIdeal A ^ 2 = ⊥) (q : A →ₐ[Λ] k)
    (hq : ∀ a : A, A.residueEquiv (residue A a) = q a) (D : A →ₗ[Λ] k)
    (hD : ∀ a b : A, D (a * b) = q a * D b + q b * D a)
    {t : A} (ht : t ∈ maximalIdeal A) (hDt : D t = 1) :
    ∃ (A' : ArtinianLocalAlgCat.{u, v, w} Λ k) (ψ : A ⟶ A') (j : A' ⟶ A),
      j ≫ ψ = 𝟙 A' ∧
      Function.Surjective ψ.hom ∧ Function.Injective j.hom ∧
      (∀ a' : A', D (j.hom a') = 0) ∧
      (∀ (a' : A') (c : k), ∃! a : A, ψ.hom a = a' ∧ D a = c) ∧
      (∀ σ : A' ⟶ A, σ ≫ ψ = 𝟙 A' →
        ¬ Function.Surjective σ.hom) := by
  classical
  let S := kernelSubalgebra q D hD
  let ρ : A →ₐ[Λ] S := retractionRestrict hA q hq D hD ht hDt
  have hρ : Function.Surjective ρ := retractionRestrict_surjective hA q hq D hD ht hDt
  let : IsArtinianRing S := hρ.isArtinianRing
  let : Nontrivial S := (kernelSubalgebra q D hD).toSubsemiring.nontrivial
  let : IsLocalRing S := IsLocalRing.of_surjective' ρ.toRingHom hρ
  let A' : ArtinianLocalAlgCat.{u, v, w} Λ k :=
    { carrier := S
      residueEquiv := residueEquivOfAugmentation (kernelAug q D hD)
        (kernelAug_surjective hA q hq D hD ht hDt) }
  have hres : ∀ a' : S, A'.residueEquiv (residue A' a') = q (a' : A) :=
    fun a' => residueEquivOfAugmentation_residue _ _ a'
  -- the retraction as a morphism of `𝒞_Λ`
  let ψ : A ⟶ A' :=
    { hom := ρ
      isLocal := IsLocalHom.of_surjective ρ.toRingHom hρ
      residue_comm := fun a => by
        rw [hres (ρ a), hq a]
        exact aug_retraction hA q hq D hD ht a }
  -- the inclusion as a morphism of `𝒞_Λ`
  let j : A' ⟶ A :=
    { hom := (kernelSubalgebra q D hD).val
      isLocal := ⟨fun a' ha' => by
        refine (residue_ne_zero_iff_isUnit a').mp ?_
        intro hz
        have h0 : q ((kernelSubalgebra q D hD).val a') = 0 :=
          (hres a').symm.trans (by rw [hz, map_zero])
        exact (IsLocalRing.mem_maximalIdeal _).mp
          ((aug_eq_zero_iff q hq _).mp h0) ha'⟩
      residue_comm := fun a' => by
        rw [hq]
        exact (hres a').symm }
  have hρS : ∀ a' : S, ρ a' = a' := fun a' =>
    Subtype.ext (retraction_eq_self hA q hq D hD ht (a' : A) a'.2)
  have hDprod : ∀ c : k, D (sec q hq c * t) = c := fun c => by
    rw [hD, aug_sec, aug_eq_zero q hq ht, hDt]
    ring
  refine ⟨A', ψ, j, ?_, hρ, Subtype.val_injective, fun a' => a'.2, ?_, ?_⟩
  · apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro a'
    exact hρS a'
  · intro a' c
    refine ⟨(a' : A) + sec q hq c * t, ⟨?_, ?_⟩, ?_⟩
    · have h3 : ρ (sec q hq c * t) = 0 := by
        refine Subtype.ext ?_
        show retraction hA q hq D hD ht (sec q hq c * t) = 0
        rw [retraction_apply, hDprod, sub_self]
      show ρ ((a' : A) + sec q hq c * t) = a'
      rw [map_add, hρS, h3, add_zero]
    · rw [map_add, hDprod, a'.2, zero_add]
    · intro b hb
      have hb1 : retraction hA q hq D hD ht b = ((a' : S) : A) :=
        congrArg (fun z : S => (z : A)) hb.1
      rw [retraction_apply, hb.2] at hb1
      rw [← hb1]
      ring
  · intro σ hσ hsurj
    obtain ⟨a', ha'⟩ := hsurj t
    have hψσ : ∀ x : A', ψ.hom (σ.hom x) = x := by
      intro x
      have h := congrArg (fun f : A' ⟶ A' => f.hom x) hσ
      simpa only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply,
        ArtinianLocalAlgCat.id_hom, AlgHom.id_apply] using h
    have ht0 : ρ t = 0 := by
      refine Subtype.ext ?_
      show retraction hA q hq D hD ht t = 0
      exact retraction_eq_zero hA q hq D hD ht hDt
    have ha'0 : a' = 0 := by
      have h := hψσ a'
      change ρ (σ.hom a') = a' at h
      rw [ha', ht0] at h
      exact h.symm
    have htzero : t = 0 := by
      rw [← ha', ha'0, map_zero]
    have : (1 : k) = 0 := by rw [← hDt, htzero, map_zero]
    exact one_ne_zero this

end Deformation

end
