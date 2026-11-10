module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.IsBaseChange
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Algebra.Module.IPowerTorsion.Resolution
public import StacksFrontier.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingKoszulRelations
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion
public import StacksFrontier.RingTheory.Localization.Glueing.Functions

/-!
# Flat ring maps inducing an isomorphism modulo an ideal

Let `R → S` be a map of commutative rings and let `I ⊆ R` be an ideal. This file studies the
situation in which `R → S` is flat and induces an isomorphism `R / I ≅ S / IS`, which is the
hypothesis under which formal glueing of module categories works.

Three groups of consequences are recorded. First, faithful flatness along the closed subset cut
out by `I` is characterized in terms of the prime spectrum and of faithfulness of base change on
modules annihilated by `I` or by powers of `I`. Second, the unit `M → M ⊗_R S` of base change is
an isomorphism on every `I`-power torsion module exactly when `R / I → S / IS` is an isomorphism.
Third, under that hypothesis base change identifies `I`-primary components, is fully faithful as
soon as one of the two modules is `I`-power torsion, and induces an equivalence between the
categories of `I`-power torsion modules over `R` and over `S`; moreover a short exact sequence
over `S` ending in the base change of an `I`-power torsion module is dominated by a short exact
sequence over `R`.

## Main results

* `FormalGlueing.flat_and_faithful_on_ideal_torsion_tfae`: four equivalent forms of faithful
  flatness along the closed subset cut out by `I`.
* `FormalGlueing.exists_shortExactSequence_lift_of_flat_baseChange`: the short exact sequence
  over `R` and the commuting map to a given sequence over `S`.

## Implementation notes

Faithfulness on either class of modules is stated directly as injectivity on morphisms after
tensoring with `S`. Isomorphisms of rings and modules are expressed as bijectivity of the
canonical maps, and the induced map on quotients is the canonical `Ideal.quotientMap`. The
primary component is Mathlib's `Ideal.primaryComponent`. Extension of scalars uses Mathlib's
convention `S ⊗[R] M`, canonically isomorphic to the source's `M ⊗[R] S`; in `ModuleCat` it is
`ModuleCat.extendScalars`. Compatibility of the categorical equivalence with base change is
recorded by a natural isomorphism after inclusion into the ambient module category. Short exact
sequences are represented by injectivity of the first map, exactness of the two maps, and
surjectivity of the second map; the outer vertical arrows of the lifting diagram are the
canonical tensor maps and the middle one is linear after restriction of scalars from `S` to `R`.

## References

* [Stacks Project, Tag 05E7](https://stacks.math.columbia.edu/tag/05E7)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 05EG](https://stacks.math.columbia.edu/tag/05EG)
-/

/-! ### Flat base change on ideal-power torsion modules -/

section

@[expose] public section

namespace FormalGlueing

universe u v

private lemma isIdealPowerTorsion_of_le_annihilator
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (h : I ≤ Module.annihilator R M) :
    IsIPowerTorsion R M I := by
  intro m
  exact ⟨1, one_pos, fun a ha ↦ Module.mem_annihilator.1 (h (by simpa using ha)) m⟩

private lemma one_tmul_injective_of_quotient_faithfullyFlat
    {R : Type u} {S : Type v} {M : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hM : I ≤ Module.annihilator R M)
    (hff : RingHom.FaithfullyFlat
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    Function.Injective (TensorProduct.mk R S M 1) := by
  let Q := S ⧸ I.map (algebraMap R S)
  let q : R ⧸ I →+* Q :=
    Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map
  let hMI : Module.IsTorsionBySet R M I := (Module.isTorsionBySet_iff_subset_annihilator ..).2 hM
  let : Module (R ⧸ I) M := hMI.module
  let : Algebra (R ⧸ I) Q := q.toAlgebra
  have : Module.FaithfullyFlat (R ⧸ I) Q :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := R ⧸ I) (S := Q)).mp (by
      change q.FaithfullyFlat
      exact hff)
  let p : S →ₛₗ[Ideal.Quotient.mk I] Q :=
    { toFun := Ideal.Quotient.mk _
      map_add' := map_add _
      map_smul' := by
        intro r s
        simp only [Algebra.smul_def]
        change Ideal.Quotient.mk _ (algebraMap R S r * s) = _
        rfl }
  let e := TensorProduct.map p hMI.semilinearMap
  intro x y hxy
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R ⧸ I) (B := Q) M
  change (1 : Q) ⊗ₜ[R ⧸ I] x = (1 : Q) ⊗ₜ[R ⧸ I] y
  have he := congrArg e hxy
  change p 1 ⊗ₜ[R ⧸ I] x = p 1 ⊗ₜ[R ⧸ I] y at he
  simpa [p] using he

private lemma eq_zero_of_annihilated_of_quotient_faithfullyFlat
    {R : Type u} {S : Type v} {N : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module.Flat R S] (I : Ideal R)
    (hff : RingHom.FaithfullyFlat
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (x : N) (hxI : ∀ r ∈ I, r • x = 0) (hx : x ⊗ₜ[R] (1 : S) = 0) : x = 0 := by
  let P := Submodule.span R {x}
  have hP : I ≤ Module.annihilator R P := by
    intro r hr
    change Module.toAddMonoidEnd R P r = 0
    ext y
    change r • (y : N) = 0
    refine Submodule.span_induction (p := fun y _ ↦ r • y = 0) ?_ ?_ ?_ ?_ y.property
    · rintro y (rfl : y = x)
      exact hxI r hr
    · simp
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro a y _ hy
      simpa [smul_smul, mul_comm] using congrArg (a • ·) hy
  have hsub : Function.Injective (P.subtype.rTensor S) :=
    Module.Flat.rTensor_preserves_injective_linearMap P.subtype Subtype.val_injective
  have hz : (⟨x, Submodule.subset_span (Set.mem_singleton x)⟩ : P) ⊗ₜ[R] (1 : S) = 0 := by
    apply hsub (a₁ :=
      (⟨x, Submodule.subset_span (Set.mem_singleton x)⟩ : P) ⊗ₜ[R] (1 : S)) (a₂ := 0)
    simpa using hx
  have hzero := one_tmul_injective_of_quotient_faithfullyFlat (S := S) I hP hff
    (show (TensorProduct.mk R S P 1)
        (⟨x, Submodule.subset_span (Set.mem_singleton x)⟩ : P) =
      (TensorProduct.mk R S P 1) 0 by
        apply (TensorProduct.comm R S P).injective
        simpa using hz)
  have := congrArg Subtype.val hzero
  exact this

private lemma rTensor_injective_of_annihilator
    {R : Type u} {S : Type v} {M N : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (hN : I ≤ Module.annihilator R N)
    (hff : RingHom.FaithfullyFlat
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    Function.Injective fun f : M →ₗ[R] N ↦ LinearMap.rTensor S f := by
  intro f g h
  ext x
  apply one_tmul_injective_of_quotient_faithfullyFlat I hN hff
  have hx := DFunLike.congr_fun h (x ⊗ₜ[R] (1 : S))
  exact (TensorProduct.comm R S N).injective (by simpa using hx)

private lemma rTensor_injective_of_powerTorsion
    {R : Type u} {S : Type v} {M N : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Flat R S]
    (I : Ideal R) (hM : IsIPowerTorsion R M I)
    (hff : RingHom.FaithfullyFlat
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    Function.Injective fun f : M →ₗ[R] N ↦ LinearMap.rTensor S f := by
  intro f g hfg
  let d := f - g
  have hd : LinearMap.rTensor S d = 0 := by
    rw [show LinearMap.rTensor S d = LinearMap.rTensor S f - LinearMap.rTensor S g by
      ext; simp [d]]
    exact sub_eq_zero.mpr hfg
  have vanish (n : ℕ) (x : M) (hn : 0 < n) (hx : ∀ a ∈ I ^ n, a • x = 0) : d x = 0 := by
    induction n generalizing x with
    | zero => simp at hn
    | succ n ih =>
      apply eq_zero_of_annihilated_of_quotient_faithfullyFlat I hff (d x)
      · intro r hr
        rw [← d.map_smul]
        by_cases hn0 : n = 0
        · subst n
          rw [hx r (by simpa using hr), d.map_zero]
        · apply ih (r • x) (Nat.pos_of_ne_zero hn0)
          intro a ha
          rw [smul_smul]
          apply hx (a * r)
          rw [pow_succ]
          exact Ideal.mul_mem_mul ha hr
      · have := DFunLike.congr_fun hd (x ⊗ₜ[R] (1 : S))
        rw [LinearMap.rTensor_tmul] at this
        simpa [d, TensorProduct.sub_tmul] using this
  ext x
  obtain ⟨n, hn, hx⟩ := hM x
  exact sub_eq_zero.mp (vanish n x hn hx)

private noncomputable def quotientTensorEquiv
    {R : Type u} {S : Type v} {M : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    (TensorProduct (R ⧸ I) (S ⧸ I.map (algebraMap R S)) M) ≃ₗ[R ⧸ I]
      (TensorProduct R M S) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv.rTensor M ≪≫ₗ
    TensorProduct.comm (R ⧸ I) (TensorProduct R (R ⧸ I) S) M ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) (R ⧸ I) M S

/-- An `R`-module structure making an `R ⧸ I`-module a scalar tower is killed by `I`. -/
private lemma le_annihilator_of_isScalarTower_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] : I ≤ Module.annihilator R M := fun r hr ↦
  Module.mem_annihilator.2 fun x ↦ by
    rw [← algebraMap_smul (R ⧸ I)]
    simp [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hr]

private lemma quotient_faithfullyFlat_of_rTensor_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (h : ∀ (M N : Type (max u v)) [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N],
      I ≤ Module.annihilator R M → I ≤ Module.annihilator R N →
        Function.Injective fun f : M →ₗ[R] N ↦ LinearMap.rTensor S f) :
    RingHom.FaithfullyFlat
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map) := by
  let Q := S ⧸ I.map (algebraMap R S)
  let q : R ⧸ I →+* Q :=
    Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map
  have : Module.Flat R S := hflat
  have hqflat : Module.Flat (R ⧸ I) Q :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  change (algebraMap (R ⧸ I) Q).FaithfullyFlat
  rw [RingHom.faithfullyFlat_algebraMap_iff,
    Module.FaithfullyFlat.iff_zero_iff_rTensor_zero]
  refine ⟨hqflat, ?_⟩
  intro M _ mM N _ mN f
  constructor
  · intro hf
    let mMR : Module R M := Module.compHom M (Ideal.Quotient.mk I)
    let mNR : Module R N := Module.compHom N (Ideal.Quotient.mk I)
    let : Module R M := mMR
    let : Module R N := mNR
    let : IsScalarTower R (R ⧸ I) M :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let : IsScalarTower R (R ⧸ I) N :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    have hz : LinearMap.rTensor S (f.restrictScalars R) = 0 := by
      ext x s
      have hs := DFunLike.congr_fun hf (x ⊗ₜ[R ⧸ I] (Ideal.Quotient.mk _ s))
      have hs' := congrArg (quotientTensorEquiv I (M := N))
        (congrArg (TensorProduct.comm (R ⧸ I) N Q) hs)
      simpa [quotientTensorEquiv] using hs'
    have hfR : f.restrictScalars R = 0 := (h M N (le_annihilator_of_isScalarTower_quotient I)
      (le_annihilator_of_isScalarTower_quotient I)) (by simpa using hz)
    ext x
    exact DFunLike.congr_fun hfR x
  · intro hf
    simp [hf]

/-- Let `R → S` be a ring map and `I` an ideal of `R`. The following are equivalent:

1. `S` is flat over `R` and `R/I → S/IS` is faithfully flat;
2. `S` is flat over `R` and `Spec(S/IS) → Spec(R/I)` is surjective;
3. `S` is flat over `R` and tensoring with `S` is faithful on modules annihilated by `I`;
4. `S` is flat over `R` and tensoring with `S` is faithful on `I`-power torsion modules. -/
@[stacks 05E7]
public theorem flat_and_faithful_on_ideal_torsion_tfae
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    let q : R ⧸ I →+* S ⧸ I.map (algebraMap R S) :=
      Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map
    List.TFAE
      [ Module.Flat R S ∧ RingHom.FaithfullyFlat q,
        Module.Flat R S ∧ Function.Surjective (PrimeSpectrum.comap q),
        Module.Flat R S ∧
          ∀ (M N : Type (max u v)) [AddCommGroup M] [Module R M]
            [AddCommGroup N] [Module R N],
            I ≤ Module.annihilator R M → I ≤ Module.annihilator R N →
              Function.Injective fun f : M →ₗ[R] N ↦ LinearMap.rTensor S f,
        Module.Flat R S ∧
          ∀ (M N : Type (max u v)) [AddCommGroup M] [Module R M]
            [AddCommGroup N] [Module R N],
            IsIPowerTorsion R M I → IsIPowerTorsion R N I →
              Function.Injective fun f : M →ₗ[R] N ↦ LinearMap.rTensor S f ] := by
  let q : R ⧸ I →+* S ⧸ I.map (algebraMap R S) :=
    Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map
  change List.TFAE
    [ Module.Flat R S ∧ RingHom.FaithfullyFlat q,
      Module.Flat R S ∧ Function.Surjective (PrimeSpectrum.comap q),
      Module.Flat R S ∧
        ∀ (M N : Type (max u v)) [AddCommGroup M] [Module R M]
          [AddCommGroup N] [Module R N],
          I ≤ Module.annihilator R M → I ≤ Module.annihilator R N →
            Function.Injective fun f : M →ₗ[R] N ↦ LinearMap.rTensor S f,
      Module.Flat R S ∧
        ∀ (M N : Type (max u v)) [AddCommGroup M] [Module R M]
          [AddCommGroup N] [Module R N],
          IsIPowerTorsion R M I → IsIPowerTorsion R N I →
            Function.Injective fun f : M →ₗ[R] N ↦ LinearMap.rTensor S f ]
  tfae_have h12 : 1 → 2 := by
    rintro ⟨hflat, hff⟩
    exact ⟨hflat, (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff).2⟩
  tfae_have h21 : 2 → 1 := by
    rintro ⟨hflat, hsurj⟩
    have : Module.Flat R S := hflat
    have hqflat : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
      Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
    have hf : RingHom.Flat q := by
      change RingHom.Flat (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
      exact (RingHom.flat_algebraMap_iff).mpr hqflat
    exact ⟨hflat, RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hf, hsurj⟩⟩
  tfae_have h13 : 1 → 3 := by
    rintro ⟨hflat, hff⟩
    exact ⟨hflat, fun M N _ _ _ _ _ hN =>
      rTensor_injective_of_annihilator I hN hff⟩
  tfae_have h31 : 3 → 1 := by
    rintro ⟨hflat, hfaith⟩
    exact ⟨hflat, quotient_faithfullyFlat_of_rTensor_injective I hflat hfaith⟩
  tfae_have h14 : 1 → 4 := by
    rintro ⟨hflat, hff⟩
    let : Module.Flat R S := hflat
    exact ⟨hflat, fun M N _ _ _ _ hM _ =>
      rTensor_injective_of_powerTorsion I hM hff⟩
  tfae_have h43 : 4 → 3 := by
    rintro ⟨hflat, hfaith⟩
    exact ⟨hflat, fun M N _ _ _ _ hM hN =>
      hfaith M N (isIdealPowerTorsion_of_le_annihilator hM)
        (isIdealPowerTorsion_of_le_annihilator hN)⟩
  tfae_finish

end FormalGlueing

end

end

/-! ### Base change of ideal-power torsion modules -/

section

@[expose] public section

namespace FormalGlueing

universe u v w

open _root_.IPowerTorsion (unitMap)

add_to_stacks 05E9 "the base-change criterion on ideal-power torsion modules"
  IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective

end FormalGlueing

end

end

/-! ### Flat base change equivalence for ideal-power torsion modules -/

section

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings

namespace FormalGlueing

universe u v w

/-- If `R → S` is flat and induces an isomorphism `R / I ≅ S / IS`, then for every
`IS`-power torsion `S`-module `M` the counit `S ⊗[R] M → M` of the adjunction between extension
and restriction of scalars is bijective. -/
public alias counit_bijective := IPowerTorsion.extendRestrictScalarsAdj_counit_app_bijective

add_to_stacks 05EC "the torsion-submodule isomorphism and the equivalence of subcategories"
  IPowerTorsion.baseChange_equiv_of_quotientMap_bijective

end FormalGlueing

end

end

/-! ### Lifting extensions across flat base change -/

section

@[expose] public section

namespace FormalGlueing

universe u v w x y z

private theorem isIdealPowerTorsion_of_injective
    {R : Type u} [CommSemiring R] {M : Type v} {N : Type w}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Injective f)
    (hN : IsIPowerTorsion R N I) :
    IsIPowerTorsion R M I := by
  intro m
  obtain ⟨k, hk, hm⟩ := hN (f m)
  refine ⟨k, hk, fun a ha ↦ hf ?_⟩
  rw [map_smul, hm a ha, map_zero]

private theorem bijective_tensorUnit_of_idealPowerTorsion
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M]
    (hM : IsIPowerTorsion R M I) :
    Function.Bijective ((TensorProduct.mk R S M) 1) := by
  let e : ULift.{max u v} M ≃ₗ[R] M := ULift.moduleEquiv
  have ht : IsIPowerTorsion R (ULift.{max u v} M) I :=
    isIdealPowerTorsion_of_injective I e.toLinearMap e.injective hM
  have h :=
    (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
      R S I hflat).2 hq (ULift.{max u v} M) ht
  let t := (TensorProduct.congr e (LinearEquiv.refl R S)).trans
    (TensorProduct.comm R M S)
  convert t.bijective.comp (h.comp e.symm.bijective) using 1
  ext m
  simp [t, e]

private theorem eq_zero_of_tensorUnit_eq_zero_of_annihilated
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (N : Type w) [AddCommGroup N] [Module R N] (x : N)
    {k : ℕ} (hk : 0 < k) (hx : ∀ a ∈ I ^ k, a • x = 0)
    (h : (1 : S) ⊗ₜ[R] x = 0) : x = 0 := by
  have := hflat
  let P := Submodule.torsionBySet R N ((I ^ k : Ideal R) : Set R)
  have hP : IsIPowerTorsion R P I := by
    intro y
    refine ⟨k, hk, fun a ha ↦ ?_⟩
    exact Subtype.ext ((Submodule.mem_torsionBySet_iff _ _).1 y.property ⟨a, ha⟩)
  let y : P := ⟨x, (Submodule.mem_torsionBySet_iff _ _).2 (fun a ↦ hx a.1 a.2)⟩
  have he := bijective_tensorUnit_of_idealPowerTorsion R S I hflat hq P hP
  have hm := Module.Flat.lTensor_preserves_injective_linearMap
    (M := S) P.subtype P.subtype_injective
  have hy : (1 : S) ⊗ₜ[R] y = 0 := hm (by simpa using h)
  have hy' : y = 0 := he.injective (by simpa using hy)
  exact congrArg Subtype.val hy'

section RelationHomology

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {n : ℕ} (f : Fin n → R)
  (N : Type w) [AddCommGroup N] [Module R N]
  (N' : Type x) [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']

private abbrev relationDifferential : (Fin n → N) →ₗ[R] (Fin n × Fin n → N) :=
  LinearMap.pi fun ij ↦ f ij.1 • LinearMap.proj ij.2 - f ij.2 • LinearMap.proj ij.1

private theorem exact_firstRelationCycles_subtype :
    Function.Exact (FormalGlueing.firstRelationCycles f N).subtype
      (relationDifferential f N) := by
  intro a
  change (fun ij : Fin n × Fin n ↦ f ij.1 • a ij.2 - f ij.2 • a ij.1) = 0 ↔ _
  constructor
  · intro h
    refine ⟨⟨a, ?_⟩, rfl⟩
    intro i j
    exact sub_eq_zero.mp (congrFun h (i, j))
  · rintro ⟨a, rfl⟩
    exact funext fun ij ↦ sub_eq_zero.mpr (a.property ij.1 ij.2)

private def firstRelationCyclesMap (g : N →ₗ[R] N') :
    FormalGlueing.firstRelationCycles f N →ₗ[R]
      FormalGlueing.firstRelationCycles (fun i ↦ algebraMap R S (f i)) N' where
  toFun a := ⟨fun i ↦ g (a.1 i), by
    intro i j
    simpa only [algebraMap_smul, ← map_smul] using congrArg g (a.property i j)⟩
  map_add' a b := by ext i; exact g.map_add _ _
  map_smul' r a := by ext i; exact g.map_smul r _

private theorem firstRelationCyclesMap_apply (g : N →ₗ[R] N')
    (a : FormalGlueing.firstRelationCycles f N) (i : Fin n) :
    (firstRelationCyclesMap (S := S) f N N' g a).1 i = g (a.1 i) := rfl

private theorem isBaseChange_firstRelationCyclesMap [Module.Flat R S]
    (g : N →ₗ[R] N') (hg : IsBaseChange S g) :
    IsBaseChange S (firstRelationCyclesMap (S := S) f N N' g) := by
  apply IsBaseChange.of_left_exact S
    (firstRelationCyclesMap (S := S) f N N' g) (g.compLeft (Fin n))
    (g.compLeft (Fin n × Fin n))
    (f := (FormalGlueing.firstRelationCycles f N).subtype)
    (g := relationDifferential f N)
    (f' := (FormalGlueing.firstRelationCycles (fun i ↦ algebraMap R S (f i)) N').subtype)
    (g' := relationDifferential (fun i ↦ algebraMap R S (f i)) N')
  · rfl
  · apply LinearMap.ext
    intro a
    apply funext
    intro ij
    change g (f ij.1 • a ij.2 - f ij.2 • a ij.1) =
      algebraMap R S (f ij.1) • g (a ij.2) - algebraMap R S (f ij.2) • g (a ij.1)
    simp only [map_sub, map_smul, algebraMap_smul]
  · exact hg.finitePow _
  · exact hg.finitePow _
  · exact exact_firstRelationCycles_subtype f N
  · exact Subtype.val_injective
  · exact exact_firstRelationCycles_subtype _ N'
  · exact Subtype.val_injective

private noncomputable def firstRelationHomologyMap (g : N →ₗ[R] N') :
    FormalGlueing.firstRelationHomology f N →ₗ[R]
      FormalGlueing.firstRelationHomology (fun i ↦ algebraMap R S (f i)) N' :=
  (LinearMap.range (FormalGlueing.firstRelationBoundaries f N)).liftQ
    (((LinearMap.range (FormalGlueing.firstRelationBoundaries
      (fun i ↦ algebraMap R S (f i)) N')).mkQ.restrictScalars R).comp
        (firstRelationCyclesMap (S := S) f N N' g)) (by
      rintro a ⟨z, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).2
      refine ⟨g z, ?_⟩
      ext i
      exact (algebraMap_smul S (f i) (g z)).trans (g.map_smul (f i) z).symm)

private theorem firstRelationHomologyMap_mk (g : N →ₗ[R] N')
    (a : FormalGlueing.firstRelationCycles f N) :
    firstRelationHomologyMap (S := S) f N N' g
        ((LinearMap.range (FormalGlueing.firstRelationBoundaries f N)).mkQ a) =
      (LinearMap.range (FormalGlueing.firstRelationBoundaries
        (fun i ↦ algebraMap R S (f i)) N')).mkQ
          (firstRelationCyclesMap (S := S) f N N' g a) := rfl

private theorem isBaseChange_firstRelationHomologyMap [Module.Flat R S]
    (g : N →ₗ[R] N') (hg : IsBaseChange S g) :
    IsBaseChange S (firstRelationHomologyMap (S := S) f N N' g) := by
  apply IsBaseChange.of_right_exact S g (firstRelationCyclesMap (S := S) f N N' g)
    (firstRelationHomologyMap (S := S) f N N' g)
    (f := FormalGlueing.firstRelationBoundaries f N)
    (g := (LinearMap.range (FormalGlueing.firstRelationBoundaries f N)).mkQ)
    (f' := FormalGlueing.firstRelationBoundaries (fun i ↦ algebraMap R S (f i)) N')
    (g' := (LinearMap.range (FormalGlueing.firstRelationBoundaries
      (fun i ↦ algebraMap R S (f i)) N')).mkQ)
  · ext z i
    exact (g.map_smul (f i) z).trans (algebraMap_smul S (f i) (g z)).symm
  · rfl
  · exact hg
  · exact isBaseChange_firstRelationCyclesMap (S := S) f N N' g hg
  · exact LinearMap.exact_map_mkQ_range _
  · exact Submodule.mkQ_surjective _
  · exact LinearMap.exact_map_mkQ_range _
  · exact Submodule.mkQ_surjective _

end RelationHomology

private theorem bijective_firstRelationHomologyMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {n k : ℕ} (f : Fin n → R) (hk : 0 < k) (hf : I ^ k = Stacks.RelationsOfSequence.idealI f)
    (N : Type w) [AddCommGroup N] [Module R N] :
    Function.Bijective (firstRelationHomologyMap (S := S) f N (TensorProduct R S N)
      ((TensorProduct.mk R S N) 1)) := by
  have := hflat
  have ht : IsIPowerTorsion R (FormalGlueing.firstRelationHomology f N) I := by
    intro z
    refine ⟨k, hk, fun a ha ↦ ?_⟩
    exact Module.mem_annihilator.mp
      (FormalGlueing.idealI_le_annihilator_firstRelationHomology f N (hf ▸ ha)) z
  have hb : IsBaseChange S ((TensorProduct.mk R S N) 1) :=
    IsBaseChange.of_equiv (LinearEquiv.refl S _) (fun _ ↦ rfl)
  have hh := isBaseChange_firstRelationHomologyMap f N (TensorProduct R S N) _ hb
  have he := bijective_tensorUnit_of_idealPowerTorsion R S I hflat hq
    (FormalGlueing.firstRelationHomology f N) ht
  convert hh.equiv.bijective.comp he using 1
  ext z
  simp [IsBaseChange.equiv_tmul]

/-- A cycle over the flat algebra comes from a cycle over the base, up to a boundary. -/
private theorem exists_firstRelationCycle_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {n k : ℕ} (f : Fin n → R) (hk : 0 < k) (hf : I ^ k = Stacks.RelationsOfSequence.idealI f)
    (N : Type w) [AddCommGroup N] [Module R N]
    (z : FormalGlueing.firstRelationCycles (fun i ↦ algebraMap R S (f i))
      (TensorProduct R S N)) :
    ∃ (a : FormalGlueing.firstRelationCycles f N) (b : TensorProduct R S N),
      ∀ j, z.1 j = (1 : S) ⊗ₜ[R] a.1 j + algebraMap R S (f j) • b := by
  obtain ⟨a, ha⟩ := (bijective_firstRelationHomologyMap I hflat hq f hk hf N).surjective
    (Submodule.Quotient.mk z)
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (FormalGlueing.firstRelationBoundaries f N)) a
  change Submodule.Quotient.mk (firstRelationCyclesMap (S := S) f N (TensorProduct R S N)
    ((TensorProduct.mk R S N) 1) a) = Submodule.Quotient.mk z at ha
  have hd : z - firstRelationCyclesMap (S := S) f N (TensorProduct R S N)
      ((TensorProduct.mk R S N) 1) a ∈ LinearMap.range
      (FormalGlueing.firstRelationBoundaries (fun i ↦ algebraMap R S (f i))
        (TensorProduct R S N)) :=
    (Submodule.Quotient.eq _).1 ha.symm
  obtain ⟨b, hb⟩ := hd
  refine ⟨a, b, fun j ↦ ?_⟩
  have h := congrArg (fun t ↦ t.1 j) hb
  change algebraMap R S (f j) • b = z.1 j - (1 : S) ⊗ₜ[R] a.1 j at h
  rw [h]
  abel

private theorem firstRelationPresentedModuleHom_ext
    {R : Type u} [CommRing R] {n : ℕ} (f : Fin n → R)
    {N : Type v} [AddCommGroup N] [Module R N]
    (g h : Stacks.RelationsOfSequence.relQuotient f →ₗ[R] N)
    (he : ∀ j, g (Submodule.Quotient.mk (Stacks.RelationsOfSequence.e j)) =
      h (Submodule.Quotient.mk (Stacks.RelationsOfSequence.e j))) : g = h := by
  have hc : g.comp (Stacks.RelationsOfSequence.relSubmodule f).mkQ =
      h.comp (Stacks.RelationsOfSequence.relSubmodule f).mkQ := by
    apply (Pi.basisFun R (Fin n)).ext
    intro j
    simpa [Stacks.RelationsOfSequence.e, Pi.basisFun_apply] using he j
  exact Submodule.linearMap_qext _ hc

private theorem exists_factor_of_ker_le
    {R : Type u} [Ring R] {A : Type v} {B : Type w} {C : Type x}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : A →ₗ[R] C) (hf : Function.Surjective f)
    (hfg : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ h : B →ₗ[R] C, h.comp f = g := by
  refine ⟨((LinearMap.ker f).liftQ g hfg).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap, ?_⟩
  ext a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- A map from a power of the ideal descends, modulo a map extending to the ring. -/
private theorem exists_idealHom_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {n k : ℕ} (f : Fin n → R) (hk : 0 < k) (hf : I ^ k = Stacks.RelationsOfSequence.idealI f)
    (N : Type w) [AddCommGroup N] [Module R N]
    (g : Stacks.RelationsOfSequence.idealI f →ₗ[R] TensorProduct R S N) :
    ∃ (h : Stacks.RelationsOfSequence.idealI f →ₗ[R] N) (b : TensorProduct R S N),
      ∀ a, (1 : S) ⊗ₜ[R] h a + a.1 • b = g a := by
  let z : FormalGlueing.firstRelationCycles (fun i ↦ algebraMap R S (f i))
      (TensorProduct R S N) :=
    ⟨(FormalGlueing.idealHomToFirstRelationCycles f (TensorProduct R S N) g).1,
      fun i j ↦ by
        simpa only [algebraMap_smul] using
          (FormalGlueing.idealHomToFirstRelationCycles f (TensorProduct R S N) g).property i j⟩
  obtain ⟨a, b, hab⟩ := exists_firstRelationCycle_lift I hflat hq f hk hf N z
  let l := FormalGlueing.cycleToPresentedModuleHom f N a
  let p : Stacks.RelationsOfSequence.relQuotient f →ₗ[R] Stacks.RelationsOfSequence.idealI f :=
    (Stacks.RelationsOfSequence.phi f).codRestrict _ (fun x ↦ by
      have h := LinearMap.mem_range_self (Stacks.RelationsOfSequence.phi f) x
      rw [Stacks.RelationsOfSequence.range_phi] at h
      exact h)
  have hp : Function.Surjective p := by
    intro x
    have hx : x.1 ∈ LinearMap.range (Stacks.RelationsOfSequence.phi f) := by
      rw [Stacks.RelationsOfSequence.range_phi]
      exact x.2
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  have hpj (j : Fin n) : p (Submodule.Quotient.mk (Stacks.RelationsOfSequence.e j)) =
      ⟨f j, Submodule.subset_span ⟨j, rfl⟩⟩ :=
    Subtype.ext (Stacks.RelationsOfSequence.baseMap_e f j)
  have hl : ((TensorProduct.mk R S N) 1).comp l +
      (LinearMap.toSpanSingleton R (TensorProduct R S N) b).comp (Stacks.RelationsOfSequence.phi f)
        =
        g.comp p := by
    apply firstRelationPresentedModuleHom_ext f
    intro j
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hpj]
    change (1 : S) ⊗ₜ[R] l (Submodule.Quotient.mk (Stacks.RelationsOfSequence.e j)) +
      Stacks.RelationsOfSequence.phi f (Submodule.Quotient.mk (Stacks.RelationsOfSequence.e j)) • b
        = _
    have hlj : l (Submodule.Quotient.mk (Stacks.RelationsOfSequence.e j)) = a.1 j := by
      simp [l, FormalGlueing.cycleToPresentedModuleHom, Stacks.RelationsOfSequence.e,
        Fintype.linearCombination_apply_single]
    rw [hlj]
    change (1 : S) ⊗ₜ[R] a.1 j + Stacks.RelationsOfSequence.baseMap f (Stacks.RelationsOfSequence.e
      j) • b = _
    rw [Stacks.RelationsOfSequence.baseMap_e]
    simpa [algebraMap_smul, z, FormalGlueing.idealHomToFirstRelationCycles] using (hab j).symm
  have hker : LinearMap.ker p ≤ LinearMap.ker l := by
    intro x hx
    have hpx : p x = 0 := hx
    have hx' : Stacks.RelationsOfSequence.phi f x = 0 := congrArg Subtype.val hpx
    apply eq_zero_of_tensorUnit_eq_zero_of_annihilated R S I hflat hq N (l x) hk
    · intro c hc
      rw [← map_smul, Stacks.RelationsOfSequence.K_annihilated f c (hf ▸ hc) x hx', map_zero]
    · have h := DFunLike.congr_fun hl x
      change (1 : S) ⊗ₜ[R] l x + Stacks.RelationsOfSequence.phi f x • b = g (p x) at h
      simpa only [hx', hpx, zero_smul, add_zero, map_zero] using h
  obtain ⟨h, hh⟩ := exists_factor_of_ker_le p l hp hker
  refine ⟨h, b, fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hp x
  have heq := DFunLike.congr_fun hl y
  change (1 : S) ⊗ₜ[R] l y + Stacks.RelationsOfSequence.phi f y • b = g (p y) at heq
  change (1 : S) ⊗ₜ[R] h (p y) + Stacks.RelationsOfSequence.phi f y • b = g (p y)
  rw [← LinearMap.comp_apply, hh]
  exact heq

private theorem exists_extension_of_presentation
    {R : Type u} [Ring R]
    {F : Type v} {M : Type w} {N : Type x} {P : Type y}
    [AddCommGroup F] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R F] [Module R M] [Module R N] [Module R P]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (d : LinearMap.ker q →ₗ[R] N)
    (j : N →ₗ[R] P) (t : F →ₗ[R] P)
    (hdt : j.comp d = t.comp (LinearMap.ker q).subtype) :
    ∃ (E : Type (max x v)) (_ : AddCommGroup E) (_ : Module R E)
      (a : N →ₗ[R] E) (b : E →ₗ[R] M) (c : E →ₗ[R] P),
      Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
      c.comp a = j ∧
      ∃ e : F →ₗ[R] E, b.comp e = q ∧ c.comp e = t ∧
        Function.Surjective (a.coprod e) := by
  let r : LinearMap.ker q →ₗ[R] N × F := (-d).prod (LinearMap.ker q).subtype
  let L := LinearMap.range r
  let a := L.mkQ.comp (LinearMap.inl R N F)
  let b₀ : N × F →ₗ[R] M := q.comp (LinearMap.snd R N F)
  have hb₀ : L ≤ LinearMap.ker b₀ := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  let b := L.liftQ b₀ hb₀
  let c₀ := j.coprod t
  have hc₀ : L ≤ LinearMap.ker c₀ := by
    rintro _ ⟨x, rfl⟩
    have h := DFunLike.congr_fun hdt x
    change j (-d x) + t x.1 = 0
    change j (d x) = t x.1 at h
    rw [map_neg, h, neg_add_cancel]
  let c := L.liftQ c₀ hc₀
  refine ⟨(N × F) ⧸ L, inferInstance, inferInstance, a, b, c, ?_, ?_, ?_, ?_,
    L.mkQ.comp (LinearMap.inr R N F), ?_, ?_, ?_⟩
  · apply (LinearMap.ker_eq_bot).1
    apply le_antisymm ?_ bot_le
    intro x hx
    have hx' : (x, (0 : F)) ∈ L := (Submodule.Quotient.mk_eq_zero L).1 hx
    obtain ⟨y, hy⟩ := hx'
    have hy₀ : y.1 = 0 := congrArg Prod.snd hy
    have hy' : y = 0 := Subtype.ext hy₀
    have hx₀ : -d y = x := congrArg Prod.fst hy
    simpa only [hy', map_zero, neg_zero, eq_comm, Submodule.mem_bot] using hx₀
  · intro x
    obtain ⟨⟨n, f⟩, rfl⟩ := L.mkQ_surjective x
    constructor
    · intro hx
      have hf : q f = 0 := hx
      refine ⟨n + d ⟨f, hf⟩, ?_⟩
      apply (Submodule.Quotient.eq L).2
      refine ⟨-⟨f, hf⟩, ?_⟩
      ext <;> simp [r]
    · rintro ⟨n', hn'⟩
      change b (L.mkQ (n, f)) = 0
      rw [← hn']
      simp [a, b, b₀]
  · intro m
    obtain ⟨f, rfl⟩ := hq m
    exact ⟨L.mkQ (0, f), rfl⟩
  · ext n
    simp [a, c, c₀]
  · ext f
    rfl
  · ext f
    simp [c, c₀]
  · intro x
    obtain ⟨⟨n, f⟩, rfl⟩ := L.mkQ_surjective x
    refine ⟨(n, f), ?_⟩
    simp [a]

private theorem exists_lift_of_injective_of_range_le
    {R : Type u} [Ring R] {A : Type v} {B : Type w} {C : Type x}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (hi : Function.Injective i) (g : C →ₗ[R] B)
    (hg : LinearMap.range g ≤ LinearMap.range i) :
    ∃ h : C →ₗ[R] A, i.comp h = g := by
  let e := LinearEquiv.ofInjective i hi
  let g' := g.codRestrict (LinearMap.range i) (fun c ↦ hg (LinearMap.mem_range_self g c))
  refine ⟨e.symm.toLinearMap.comp g', ?_⟩
  ext c
  exact congrArg Subtype.val (e.apply_symm_apply (g' c))

/-- Two maps out of the middle of an extension agree once they agree on the image of the
subobject and on the range of a map `e` such that `a.coprod e` is surjective. -/
private theorem comp_eq_of_surjective_coprod
    {R : Type u} [Ring R] {N : Type v} {E : Type w} {M : Type x} {P : Type y} {Q : Type z}
    {F : Type*} [AddCommGroup N] [AddCommGroup E] [AddCommGroup M] [AddCommGroup P]
    [AddCommGroup Q] [AddCommGroup F] [Module R N] [Module R E] [Module R M] [Module R P]
    [Module R Q] [Module R F]
    (a : N →ₗ[R] E) (b : E →ₗ[R] M) (c : E →ₗ[R] P) (e : F →ₗ[R] E)
    (κ : M →ₗ[R] Q) (p : P →ₗ[R] Q) (hab : Function.Exact a b)
    (hsurj : Function.Surjective (a.coprod e)) (hpca : ∀ n, p (c (a n)) = 0)
    (he : ∀ f, κ (b (e f)) = p (c (e f))) : κ.comp b = p.comp c := by
  ext x
  obtain ⟨⟨n, f⟩, rfl⟩ := hsurj x
  simp only [LinearMap.coprod_apply, LinearMap.comp_apply, map_add, hab.apply_apply_eq_zero,
    map_zero, hpca, zero_add, he]

private theorem exists_extension_lift_quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {n k : ℕ} (f : Fin n → R) (hk : 0 < k) (hf : I ^ k = Stacks.RelationsOfSequence.idealI f)
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P]
    (i : TensorProduct R S N →ₗ[R] P)
    (p : P →ₗ[R] TensorProduct R S (R ⧸ Stacks.RelationsOfSequence.idealI f))
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) :
    ∃ (E : Type (max w u)) (_ : AddCommGroup E) (_ : Module R E)
      (a : N →ₗ[R] E) (b : E →ₗ[R] (R ⧸ Stacks.RelationsOfSequence.idealI f)) (c : E →ₗ[R] P),
      Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
      c.comp a = i.comp ((TensorProduct.mk R S N) 1) ∧
      ((TensorProduct.mk R S (R ⧸ Stacks.RelationsOfSequence.idealI f)) 1).comp b = p.comp c := by
  let J := Stacks.RelationsOfSequence.idealI f
  let q := J.mkQ
  let η := (TensorProduct.mk R S N) 1
  let ηQ := (TensorProduct.mk R S (R ⧸ J)) 1
  obtain ⟨e, he⟩ := hp (ηQ (q 1))
  let t₀ := LinearMap.toSpanSingleton R P e
  have hrel (r : J) : p (t₀ r.1) = 0 := by
    change p (r.1 • e) = 0
    rw [map_smul, he, ← map_smul, ← map_smul]
    change ηQ (q (r.1 * 1)) = 0
    rw [mul_one]
    have hr : q r.1 = 0 := (Submodule.Quotient.mk_eq_zero J).2 r.2
    rw [hr, map_zero]
  obtain ⟨g, hg⟩ := exists_lift_of_injective_of_range_le i hi (t₀.comp J.subtype) (by
    rintro _ ⟨r, rfl⟩
    exact (hex (t₀ r.1)).1 (hrel r))
  obtain ⟨d, z, hdz⟩ := exists_idealHom_lift I hflat hq f hk hf N g
  let t := LinearMap.toSpanSingleton R P (e - i z)
  have hdt : (i.comp η).comp d = t.comp J.subtype := by
    ext r
    have h := congrArg i (hdz r)
    have h' := DFunLike.congr_fun hg r
    change i (η (d r) + r.1 • z) = i (g r) at h
    change i (g r) = r.1 • e at h'
    rw [map_add, map_smul, h'] at h
    change i (η (d r)) = r.1 • (e - i z)
    rw [smul_sub]
    exact eq_sub_of_add_eq h
  let d' : LinearMap.ker q →ₗ[R] N := d.comp
    (Submodule.inclusion (by simpa only [q, Submodule.ker_mkQ] using (le_refl J)))
  have hd' : (i.comp η).comp d' = t.comp (LinearMap.ker q).subtype := by
    ext r
    exact DFunLike.congr_fun hdt ⟨r.1, (Submodule.Quotient.mk_eq_zero J).1 r.2⟩
  obtain ⟨E, hE, mE, a, b, c, ha, hab, hb, hca, e', hbe', hce', he'⟩ :=
    exists_extension_of_presentation q J.mkQ_surjective d' (i.comp η) t hd'
  refine ⟨E, hE, mE, a, b, c, ha, hab, hb, hca, ?_⟩
  have hpi (x : TensorProduct R S N) : p (i x) = 0 := (hex (i x)).2 ⟨x, rfl⟩
  refine comp_eq_of_surjective_coprod a b c e' ηQ p hab he' (fun r ↦ ?_) (fun s ↦ ?_)
  · rw [show c (a r) = i (η r) from DFunLike.congr_fun hca r, hpi]
  · rw [show b (e' s) = q s from DFunLike.congr_fun hbe' s,
      show c (e' s) = s • (e - i z) from DFunLike.congr_fun hce' s,
      map_smul, map_sub, he, hpi, sub_zero, ← map_smul, ← map_smul]
    congr 2
    exact (mul_one s).symm

private theorem exact_directSum_lmap
    {R : Type u} [Ring R] {α : Type v} {A : α → Type w} {B : α → Type x}
    {C : α → Type y} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (A i)] [∀ i, Module R (B i)]
    [∀ i, Module R (C i)] (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] C i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  rw [LinearMap.exact_iff, DirectSum.lmap, DirectSum.lmap,
    DFinsupp.range_mapRangeLinearMap, DFinsupp.ker_mapRangeLinearMap]
  congr 2
  funext i
  exact (LinearMap.exact_iff).1 (h i)

private theorem exists_extension_directSum
    {R : Type u} [Ring R] {α : Type v} [DecidableEq α]
    (F : α → Type w) (M : α → Type x) (N : Type y) (P : Type z)
    [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (M i)]
    [AddCommGroup N] [AddCommGroup P]
    [∀ i, Module R (F i)] [∀ i, Module R (M i)] [Module R N] [Module R P]
    (a : ∀ i, N →ₗ[R] F i) (b : ∀ i, F i →ₗ[R] M i)
    (c : ∀ i, F i →ₗ[R] P) (j : N →ₗ[R] P)
    (ha : ∀ i, Function.Injective (a i)) (hb : ∀ i, Function.Surjective (b i))
    (hab : ∀ i, Function.Exact (a i) (b i)) (hc : ∀ i, (c i).comp (a i) = j) :
    ∃ (E : Type (max y (max v w))) (_ : AddCommGroup E) (_ : Module R E)
      (a' : N →ₗ[R] E) (b' : E →ₗ[R] DirectSum α M) (c' : E →ₗ[R] P),
      Function.Injective a' ∧ Function.Exact a' b' ∧ Function.Surjective b' ∧
      c'.comp a' = j ∧
      ∃ e : DirectSum α F →ₗ[R] E,
        b'.comp e = DirectSum.lmap b ∧ c'.comp e = DirectSum.toModule R α P c ∧
        Function.Surjective (a'.coprod e) := by
  classical
  let A := DirectSum.lmap a
  let B := DirectSum.lmap b
  let C := DirectSum.toModule R α P c
  let σ : DirectSum α (fun _ ↦ N) →ₗ[R] N :=
    DirectSum.toModule R α N (fun _ ↦ LinearMap.id)
  have hA : Function.Injective A := (DirectSum.lmap_injective a).2 ha
  have hB : Function.Surjective B := (DirectSum.lmap_surjective b).2 hb
  have hAB : LinearMap.range A = LinearMap.ker B :=
    ((LinearMap.exact_iff).1 (exact_directSum_lmap a b hab)).symm
  obtain ⟨d, hd⟩ := exists_lift_of_injective_of_range_le A hA (LinearMap.ker B).subtype (by
    rintro _ ⟨x, rfl⟩
    rw [hAB]
    exact x.2)
  have hC : C.comp A = j.comp σ := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro n
    simpa [C, A, σ] using DFunLike.congr_fun (hc i) n
  apply exists_extension_of_presentation B hB (σ.comp d) j C
  rw [← LinearMap.comp_assoc, ← hC, LinearMap.comp_assoc, hd]

/-- A comparison of extensions which is an isomorphism on their kernels identifies the
kernel of its middle map with the kernel of its quotient map. -/
private theorem exists_kernel_lift_of_exact
    {R : Type u} [Ring R] {N : Type v} {E : Type w} {P : Type x}
    {E' : Type y} {M : Type z}
    [AddCommGroup N] [AddCommGroup E] [AddCommGroup P]
    [AddCommGroup E'] [AddCommGroup M]
    [Module R N] [Module R E] [Module R P] [Module R E'] [Module R M]
    (a : N →ₗ[R] E) (b : E →ₗ[R] P) (i : N →ₗ[R] E') (p : E' →ₗ[R] M)
    (c : E →ₗ[R] E') (q : P →ₗ[R] M)
    (hab : Function.Exact a b) (hb : Function.Surjective b)
    (hip : Function.Exact i p) (hi : Function.Injective i)
    (hca : c.comp a = i) (hpc : p.comp c = q.comp b) :
    ∃ d : LinearMap.ker q →ₗ[R] E,
      b.comp d = (LinearMap.ker q).subtype ∧ c.comp d = 0 := by
  let f : LinearMap.ker c →ₗ[R] LinearMap.ker q :=
    (b.comp (LinearMap.ker c).subtype).codRestrict _ (by
      intro x
      have h := DFunLike.congr_fun hpc x.1
      change q (b x.1) = 0
      change p (c x.1) = q (b x.1) at h
      rw [← h, x.2, map_zero])
  have hf : Function.Bijective f := by
    constructor
    · apply (LinearMap.ker_eq_bot).1
      apply le_antisymm ?_ bot_le
      intro x hx
      have hx' : b x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨n, hn⟩ := (hab x.1).1 hx'
      have hin : i n = 0 := by
        rw [← DFunLike.congr_fun hca n]
        change c (a n) = 0
        rw [hn]
        exact x.2
      have hn₀ : n = 0 := hi (hin.trans i.map_zero.symm)
      apply Subtype.ext
      change x.1 = 0
      simpa only [hn₀, map_zero] using hn.symm
    · intro x
      obtain ⟨e, he⟩ := hb x.1
      have hce : p (c e) = 0 := by
        change (p.comp c) e = 0
        rw [hpc]
        change q (b e) = 0
        rw [he]
        exact x.2
      obtain ⟨n, hn⟩ := (hip (c e)).1 hce
      have hy : c (e - a n) = 0 := by
        rw [map_sub]
        change c e - (c.comp a) n = 0
        rw [hca, hn, sub_self]
      refine ⟨⟨e - a n, hy⟩, Subtype.ext ?_⟩
      change b (e - a n) = x.1
      rw [map_sub, hab.apply_apply_eq_zero, sub_zero, he]
  let e := LinearEquiv.ofBijective f hf
  refine ⟨(LinearMap.ker c).subtype.comp e.symm.toLinearMap, ?_, ?_⟩
  · ext x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  · ext x
    exact (e.symm x).2

private theorem exists_extension_descend
    {R : Type u} [Ring R] {N : Type v} {E : Type w} {P : Type x}
    {M : Type y} {Q : Type z}
    [AddCommGroup N] [AddCommGroup E] [AddCommGroup P]
    [AddCommGroup M] [AddCommGroup Q]
    [Module R N] [Module R E] [Module R P] [Module R M] [Module R Q]
    (a : N →ₗ[R] E) (b : E →ₗ[R] P) (c : E →ₗ[R] Q) (q : P →ₗ[R] M)
    (ha : Function.Injective a) (hb : Function.Surjective b)
    (hab : Function.Exact a b) (hq : Function.Surjective q)
    (d : LinearMap.ker q →ₗ[R] E)
    (hbd : b.comp d = (LinearMap.ker q).subtype) (hcd : c.comp d = 0) :
    ∃ (E' : Type (max v w)) (_ : AddCommGroup E') (_ : Module R E')
      (a' : N →ₗ[R] E') (b' : E' →ₗ[R] M) (c' : E' →ₗ[R] Q),
      Function.Injective a' ∧ Function.Exact a' b' ∧ Function.Surjective b' ∧
      c'.comp a' = c.comp a ∧
      ∃ e : E →ₗ[R] E', b'.comp e = q.comp b ∧ c'.comp e = c ∧
        Function.Surjective (a'.coprod e) := by
  let q₀ := q.comp b
  let k : LinearMap.ker q₀ →ₗ[R] LinearMap.ker q :=
    (b.comp (LinearMap.ker q₀).subtype).codRestrict _ (fun x ↦ x.2)
  let r := (LinearMap.ker q₀).subtype - d.comp k
  have hr : LinearMap.range r ≤ LinearMap.range a := by
    rintro _ ⟨x, rfl⟩
    apply (hab (r x)).1
    change b (x.1 - d (k x)) = 0
    rw [map_sub]
    have h := DFunLike.congr_fun hbd (k x)
    change b (d (k x)) = b x.1 at h
    rw [h, sub_self]
  obtain ⟨s, hs⟩ := exists_lift_of_injective_of_range_le a ha r hr
  apply exists_extension_of_presentation q₀ (hq.comp hb) s (c.comp a) c
  rw [LinearMap.comp_assoc, hs]
  ext x
  change c (x.1 - d (k x)) = c x.1
  rw [map_sub]
  have h := DFunLike.congr_fun hcd (k x)
  change c (d (k x)) = 0 at h
  rw [h, sub_zero]

/-- In an exact sequence, the middle module fits in any universe containing both ends. -/
private theorem small_of_exact_of_surjective
    {R : Type u} [Ring R] {N : Type v} {E : Type w} {M : Type x}
    [AddCommGroup N] [AddCommGroup E] [AddCommGroup M]
    [Module R N] [Module R E] [Module R M] [Small.{y} N] [Small.{y} M]
    (a : N →ₗ[R] E) (b : E →ₗ[R] M)
    (hab : Function.Exact a b) (hb : Function.Surjective b) : Small.{y} E := by
  classical
  choose s hs using hb
  apply small_of_surjective (f := fun nm : N × M ↦ a nm.1 + s nm.2)
  intro e
  have h : b (e - s (b e)) = 0 := by rw [map_sub, hs, sub_self]
  obtain ⟨n, hn⟩ := (hab (e - s (b e))).1 h
  refine ⟨(n, b e), ?_⟩
  change a n + s (b e) = e
  rw [hn, sub_add_cancel]

/-- Pulling back an extension preserves its kernel and surjectivity. -/
private theorem exists_extension_pullback
    {R : Type u} [Ring R] {N : Type v} {E : Type w} {M : Type x} {P : Type y}
    [AddCommGroup N] [AddCommGroup E] [AddCommGroup M] [AddCommGroup P]
    [Module R N] [Module R E] [Module R M] [Module R P]
    (i : N →ₗ[R] E) (p : E →ₗ[R] M) (q : P →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) :
    ∃ (F : Type (max w y)) (_ : AddCommGroup F) (_ : Module R F)
      (a : N →ₗ[R] F) (b : F →ₗ[R] P) (c : F →ₗ[R] E),
      Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
      c.comp a = i ∧ q.comp b = p.comp c := by
  let L := LinearMap.ker (p.comp (LinearMap.fst R E P) -
    q.comp (LinearMap.snd R E P))
  let a : N →ₗ[R] L := (i.prod 0).codRestrict L (by
    intro n
    change p (i n) - q 0 = 0
    rw [hex.apply_apply_eq_zero, map_zero, sub_zero])
  let b := (LinearMap.snd R E P).comp L.subtype
  let c := (LinearMap.fst R E P).comp L.subtype
  refine ⟨L, inferInstance, inferInstance, a, b, c, ?_, ?_, ?_, rfl, ?_⟩
  · intro n m h
    exact hi (congrArg (fun z : L ↦ z.1.1) h)
  · intro z
    constructor
    · intro hz
      have hz' : z.1.2 = 0 := hz
      have h : p z.1.1 = 0 := by
        have h := z.2
        change p z.1.1 - q z.1.2 = 0 at h
        simpa only [hz', map_zero, sub_zero] using h
      obtain ⟨n, hn⟩ := (hex z.1.1).1 h
      exact ⟨n, Subtype.ext (Prod.ext hn hz'.symm)⟩
    · rintro ⟨n, rfl⟩
      rfl
  · intro x
    obtain ⟨e, he⟩ := hp (q x)
    exact ⟨⟨(e, x), sub_eq_zero.mpr he⟩, rfl⟩
  · ext z
    exact (sub_eq_zero.mp z.2).symm

/-- Maps out of an ideal-power torsion module descend through the tensor unit. -/
private theorem exists_tensorUnit_factor_of_idealPowerTorsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M : Type w} {N : Type x} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (hM : IsIPowerTorsion R M I)
    (g : M →ₗ[R] TensorProduct R S N) :
    ∃ f : M →ₗ[R] N, ((TensorProduct.mk R S N) 1).comp f = g := by
  let N' := ULift.{max u v} N
  let e : N' ≃ₗ[R] N := ULift.moduleEquiv
  let g' := (e.symm.toLinearMap.baseChange S).restrictScalars R |>.comp g
  obtain ⟨d, hd⟩ :=
    (IPowerTorsion.baseChange_equiv_of_quotientMap_bijective.{u, v, x} R S I hI hflat hq).1 N'
  have hg' (m : M) : g' m ∈
      Ideal.primaryComponent (TensorProduct R S N') (I.map (algebraMap R S)) := by
    obtain ⟨n, _, hn⟩ := hM m
    rw [Ideal.primaryComponent_mem]
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    have hle : (I ^ n).map (algebraMap R S) ≤
        LinearMap.ker (LinearMap.toSpanSingleton S (TensorProduct R S N') (g' m)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change algebraMap R S r • g' m = 0
      rw [algebraMap_smul, ← map_smul, hn r hr, map_zero]
    rintro ⟨s, hs⟩
    exact hle (by rwa [Ideal.map_pow])
  let f' : M →ₗ[R] N' := (Ideal.primaryComponent N' I).subtype.comp
    (d.symm.toLinearMap.comp (g'.codRestrict
      ((Ideal.primaryComponent (TensorProduct R S N')
        (I.map (algebraMap R S))).restrictScalars R) hg'))
  refine ⟨e.toLinearMap.comp f', ?_⟩
  ext m
  have h := hd (d.symm ⟨g' m, hg' m⟩)
  have hh : (1 : S) ⊗ₜ[R] f' m = g' m := by
    change (1 : S) ⊗ₜ[R] (d.symm ⟨g' m, hg' m⟩).1 = g' m
    simpa only [LinearEquiv.apply_symm_apply] using h.symm
  have ht := congrArg (e.toLinearMap.baseChange S) hh
  have he : (e.toLinearMap.baseChange S).comp (e.symm.toLinearMap.baseChange S) =
      LinearMap.id := by
    rw [← LinearMap.baseChange_comp]
    simp
  change (1 : S) ⊗ₜ[R] e (f' m) =
    ((e.toLinearMap.baseChange S).comp (e.symm.toLinearMap.baseChange S)) (g m) at ht
  rw [he, LinearMap.id_apply] at ht
  exact ht

private theorem isIdealPowerTorsion_directSum_quotient
    {R : Type u} [CommRing R] (I : Ideal R) {α : Type v}
    (n : α → ℕ) :
    IsIPowerTorsion R (DirectSum α (fun i ↦ R ⧸ I ^ n i)) I := by
  classical
  intro x
  let k := 1 + x.support.sum n
  refine ⟨k, by simp [k], fun r hr ↦ ?_⟩
  ext j
  by_cases hj : j ∈ x.support
  · have hjle : n j ≤ k := (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hj).trans
      (Nat.le_add_left _ 1)
    have hrj : r ∈ I ^ n j := Ideal.pow_le_pow_right hjle hr
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (x j)
    change r • x j = 0
    rw [← hs]
    change Ideal.Quotient.mk (I ^ n j) (r * s) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).2 ((I ^ n j).mul_mem_right s hrj)
  · have hxj : x j = 0 := by simpa only [DFinsupp.mem_support_iff, not_not] using hj
    change r • x j = 0
    rw [hxj, smul_zero]

private theorem exists_extension_lift_idealPow_quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (k : ℕ) (hk : 0 < k)
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type x) [AddCommGroup P] [Module R P]
    (i : TensorProduct R S N →ₗ[R] P)
    (p : P →ₗ[R] TensorProduct R S (R ⧸ I ^ k))
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) :
    ∃ (E : Type (max w u)) (_ : AddCommGroup E) (_ : Module R E)
      (a : N →ₗ[R] E) (b : E →ₗ[R] (R ⧸ I ^ k)) (c : E →ₗ[R] P),
      Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
      c.comp a = i.comp ((TensorProduct.mk R S N) 1) ∧
      ((TensorProduct.mk R S (R ⧸ I ^ k)) 1).comp b = p.comp c := by
  obtain ⟨t, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (hI.pow (n := k))
  change Stacks.RelationsOfSequence.idealI f = I ^ k at hf
  revert p
  rw [← hf]
  intro p hp hex
  exact exists_extension_lift_quotient I hflat hq f hk hf.symm N P i p hi hp hex

private theorem exists_extension_lift_directSum_quotient
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {α : Type w} (n : α → ℕ) (hn : ∀ j, 0 < n j)
    {M : Type x} {N : Type y} {P : Type z}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (q : DirectSum α (fun j ↦ R ⧸ I ^ n j) →ₗ[R] M)
    (i : TensorProduct R S N →ₗ[R] P) (p : P →ₗ[R] TensorProduct R S M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p) :
    ∃ (E : Type (max y (max w u))) (_ : AddCommGroup E) (_ : Module R E)
      (a : N →ₗ[R] E) (b : E →ₗ[R] DirectSum α (fun j ↦ R ⧸ I ^ n j))
      (c : E →ₗ[R] P),
      Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
      c.comp a = i.comp ((TensorProduct.mk R S N) 1) ∧
      ((TensorProduct.mk R S M) 1).comp (q.comp b) = p.comp c := by
  classical
  let Q := fun j ↦ R ⧸ I ^ n j
  let qj := fun j ↦ q.comp (DirectSum.lof R α Q j)
  have hlocal (j : α) :
      ∃ (F : Type (max y u)) (_ : AddCommGroup F) (_ : Module R F)
        (a : N →ₗ[R] F) (b : F →ₗ[R] Q j) (c : F →ₗ[R] P),
        Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
        c.comp a = i.comp ((TensorProduct.mk R S N) 1) ∧
        ((TensorProduct.mk R S M) 1).comp ((qj j).comp b) = p.comp c := by
    obtain ⟨Pj, hPj, mPj, ij, pj, cj, hij, hexj, hpj, hcij, hpcj⟩ :=
      exists_extension_pullback i p ((qj j).baseChange S |>.restrictScalars R) hi hp hex
    obtain ⟨F, hF, mF, a, b, c, ha, hab, hb, hca, hbc⟩ :=
      exists_extension_lift_idealPow_quotient I hI hflat hq (n j) (hn j) N Pj
        ij pj hij hpj hexj
    refine ⟨F, hF, mF, a, b, cj.comp c, ha, hab, hb, ?_, ?_⟩
    · rw [LinearMap.comp_assoc, hca, ← LinearMap.comp_assoc, hcij]
    · ext x
      have h := DFunLike.congr_fun hpcj (c x)
      have h' := DFunLike.congr_fun hbc x
      change (qj j).baseChange S (pj (c x)) = p (cj (c x)) at h
      change (1 : S) ⊗ₜ[R] b x = pj (c x) at h'
      rw [← h', LinearMap.baseChange_tmul] at h
      exact h
  choose F hF mF a b c ha hab hb hca hbc using hlocal
  obtain ⟨E, hE, mE, a', b', c', ha', hab', hb', hca', e, hbe, hce, he⟩ :=
    exists_extension_directSum F Q N P a b c (i.comp ((TensorProduct.mk R S N) 1))
      ha hb hab hca
  refine ⟨E, hE, mE, a', b', c', ha', hab', hb', hca', ?_⟩
  have hsum : ((TensorProduct.mk R S M) 1).comp (q.comp (DirectSum.lmap b)) =
      p.comp (DirectSum.toModule R α P c) := by
    apply DirectSum.linearMap_ext
    intro j
    ext x
    simpa [qj] using DFunLike.congr_fun (hbc j) x
  refine comp_eq_of_surjective_coprod a' b' c' e (((TensorProduct.mk R S M) 1).comp q) p hab' he
    (fun n ↦ ?_) (fun f ↦ ?_)
  · rw [show c' (a' n) = i ((1 : S) ⊗ₜ[R] n) from DFunLike.congr_fun hca' n,
      hex.apply_apply_eq_zero]
  · rw [show b' (e f) = DirectSum.lmap b f from DFunLike.congr_fun hbe f,
      show c' (e f) = DirectSum.toModule R α P c f from DFunLike.congr_fun hce f]
    exact DFunLike.congr_fun hsum f

/-- A splitting over the relations descends along flat base change. -/
private theorem exists_extension_descend_of_flat_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {N : Type w} {E : Type x} {P : Type y} {M : Type z} {E' : Type*}
    [AddCommGroup N] [AddCommGroup E] [AddCommGroup P]
    [AddCommGroup M] [AddCommGroup E']
    [Module R N] [Module R E] [Module R P] [Module R M]
    [Module R E'] [Module S E'] [IsScalarTower R S E']
    (a : N →ₗ[R] E) (b : E →ₗ[R] P) (q : P →ₗ[R] M)
    (i : TensorProduct R S N →ₗ[S] E') (p : E' →ₗ[S] TensorProduct R S M)
    (c : E →ₗ[R] E')
    (ha : Function.Injective a) (hab : Function.Exact a b) (hb : Function.Surjective b)
    (hqs : Function.Surjective q) (hP : IsIPowerTorsion R P I)
    (hi : Function.Injective i) (hex : Function.Exact i p)
    (hca : c.comp a = (i.restrictScalars R).comp ((TensorProduct.mk R S N) 1))
    (hpc : ((TensorProduct.mk R S M) 1).comp (q.comp b) =
      (p.restrictScalars R).comp c) :
    ∃ (F : Type (max w x)) (_ : AddCommGroup F) (_ : Module R F)
      (a' : N →ₗ[R] F) (b' : F →ₗ[R] M) (c' : F →ₗ[R] E'),
      Function.Injective a' ∧ Function.Exact a' b' ∧ Function.Surjective b' ∧
      c'.comp a' = (i.restrictScalars R).comp ((TensorProduct.mk R S N) 1) ∧
      ((TensorProduct.mk R S M) 1).comp b' = (p.restrictScalars R).comp c' := by
  have := hflat
  let cS := c.liftBaseChange S
  have hcaS : cS.comp (a.baseChange S) = i := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s n
    have h := DFunLike.congr_fun hca n
    change c (a n) = i ((1 : S) ⊗ₜ[R] n) at h
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      LinearMap.liftBaseChange_tmul, cS, h, ← map_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hpcS : p.comp cS = (q.baseChange S).comp (b.baseChange S) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s e
    have h := DFunLike.congr_fun hpc e
    change (1 : S) ⊗ₜ[R] q (b e) = p (c e) at h
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      LinearMap.liftBaseChange_tmul, cS, map_smul, ← h,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨dS, hbdS, hcdS⟩ := exists_kernel_lift_of_exact
    (a.baseChange S) (b.baseChange S) i p cS (q.baseChange S)
    (Module.Flat.lTensor_exact S hab) (LinearMap.baseChange_surjective S hb)
    hex hi hcaS hpcS
  let k : LinearMap.ker q →ₗ[R] LinearMap.ker (q.baseChange S) :=
    (((TensorProduct.mk R S P) 1).comp (LinearMap.ker q).subtype).codRestrict
      ((LinearMap.ker (q.baseChange S)).restrictScalars R) (by
        intro x
        change q.baseChange S ((1 : S) ⊗ₜ[R] x.1) = 0
        rw [LinearMap.baseChange_tmul, x.2, TensorProduct.tmul_zero])
  have hK := isIdealPowerTorsion_of_injective I (LinearMap.ker q).subtype
    (LinearMap.ker q).subtype_injective hP
  obtain ⟨d, hd⟩ := exists_tensorUnit_factor_of_idealPowerTorsion I hI hflat hq hK
    ((dS.restrictScalars R).comp k)
  have hd' (x : LinearMap.ker q) : (1 : S) ⊗ₜ[R] d x = dS (k x) := DFunLike.congr_fun hd x
  have hbd : b.comp d = (LinearMap.ker q).subtype := by
    ext x
    apply (bijective_tensorUnit_of_idealPowerTorsion R S I hflat hq P hP).injective
    have h := DFunLike.congr_fun hbdS (k x)
    change b.baseChange S (dS (k x)) = (1 : S) ⊗ₜ[R] x.1 at h
    rw [← hd', LinearMap.baseChange_tmul] at h
    exact h
  have hcd : c.comp d = 0 := by
    ext x
    have h := DFunLike.congr_fun hcdS (k x)
    change cS (dS (k x)) = 0 at h
    rw [← hd', LinearMap.liftBaseChange_one_tmul] at h
    exact h
  obtain ⟨F, hF, mF, a', b', c', ha', hab', hb', hca', e, hbe, hce, he⟩ :=
    exists_extension_descend a b c q ha hb hab hqs d hbd hcd
  refine ⟨F, hF, mF, a', b', c', ha', hab', hb', hca'.trans hca, ?_⟩
  refine comp_eq_of_surjective_coprod a' b' c' e _ (p.restrictScalars R) hab' he
    (fun n ↦ ?_) (fun f ↦ ?_)
  · rw [show c' (a' n) = i ((1 : S) ⊗ₜ[R] n) from DFunLike.congr_fun (hca'.trans hca) n]
    exact hex.apply_apply_eq_zero _
  · rw [show b' (e f) = q (b f) from DFunLike.congr_fun hbe f,
      show c' (e f) = c f from DFunLike.congr_fun hce f]
    exact DFunLike.congr_fun hpc f

/-- A short exact sequence over `S` ending in the base change of an
`I`-power torsion module fits below a short exact sequence over `R`, provided `R → S` is flat
and induces an isomorphism modulo the finitely generated ideal `I`. -/
@[stacks 05EG]
public theorem exists_shortExactSequence_lift_of_flat_baseChange
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type x) [AddCommGroup N] [Module R N]
    (hM : IsIPowerTorsion R M I)
    (E' : Type y) [AddCommGroup E'] [Module R E'] [Module S E'] [IsScalarTower R S E']
    (i : TensorProduct R S N →ₗ[S] E')
    (p : E' →ₗ[S] TensorProduct R S M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : Function.Exact i p) :
    ∃ (E : Type (max x (max w y))) (_ : AddCommGroup E) (_ : Module R E)
      (a : N →ₗ[R] E) (b : E →ₗ[R] M) (c : E →ₗ[R] E'),
      Function.Injective a ∧ Function.Exact a b ∧ Function.Surjective b ∧
        c.comp a = (i.restrictScalars R).comp ((TensorProduct.mk R S N) 1) ∧
        ((TensorProduct.mk R S M) 1).comp b = (p.restrictScalars R).comp c := by
  classical
  obtain ⟨α, n, hn, _, q, hqs, _, _⟩ :=
    exists_directSum_quotient_resolution R I M hM
  obtain ⟨F, hF, mF, a, b, c, ha, hab, hb, hca, hpc⟩ :=
    exists_extension_lift_directSum_quotient I hI hflat hq (n 0) (hn 0)
      q (i.restrictScalars R) (p.restrictScalars R) hi hp hexact
  obtain ⟨E, hE, mE, a', b', c', ha', hab', hb', hca', hpc'⟩ :=
    exists_extension_descend_of_flat_baseChange I hI hflat hq a b q i p c ha hab hb hqs
      (isIdealPowerTorsion_directSum_quotient I (n 0)) hi hexact hca hpc
  have : Small.{max x (max w y)} E := small_of_exact_of_surjective a' b' hab' hb'
  let e : Shrink.{max x (max w y)} E ≃ₗ[R] E := Shrink.linearEquiv R E
  refine ⟨Shrink.{max x (max w y)} E, inferInstance, inferInstance,
    e.symm.toLinearMap.comp a', b'.comp e.toLinearMap, c'.comp e.toLinearMap,
    e.symm.injective.comp ha', ?_, hb'.comp e.surjective, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := (hab' (e z)).1 hz
      refine ⟨n, ?_⟩
      change e.symm (a' n) = z
      rw [hn, e.symm_apply_apply]
    · rintro ⟨n, hn⟩
      change b' (e z) = 0
      change e.symm (a' n) = z at hn
      rw [← hn, e.apply_symm_apply]
      exact hab'.apply_apply_eq_zero n
  · ext n
    change c' (e (e.symm (a' n))) = i ((1 : S) ⊗ₜ[R] n)
    rw [e.apply_symm_apply]
    exact DFunLike.congr_fun hca' n
  · ext z
    exact DFunLike.congr_fun hpc' (e z)

end FormalGlueing

end

end
