module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.Blowup.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex

/-!
# Néron's desingularization: the standing situation and the blowup

Fix an extension `R → Λ` of discrete valuation rings of ramification index one, together with a
factorization `R → A → Λ` in which `A` is flat and of finite type over `R`. The two ideals
used throughout are the kernel `𝔮 = Ker(A → Λ)` and the preimage
`𝔭 = (A → Λ)^{-1}(𝔪_Λ)`.

Two facts about the affine blowup `A' = A[𝔭/π]` at a uniformizer `π` of `R` are proved here:
it commutes with localizing `A` away from an element outside `𝔭`, and if `A` is presented as a
quotient of a flat finite-type `R`-algebra `B` then `A'` is the blowup of `B` modulo the
extended kernel, after removing the `π`-power torsion.

## Main definitions

* `Stacks.Smoothing.NeronSituation`: the standing data — the two discrete valuation rings, the
  intermediate algebra, and the flat finite-type factorization.
* `Stacks.Smoothing.NeronSituation.kernelIdeal`,
  `Stacks.Smoothing.NeronSituation.maximalIdealPreimage`: the ideals `𝔮` and `𝔭`.

## Main results

* `Stacks.Smoothing.neron_affineBlowup_localization`: the affine blowup commutes with
  localization away from an element outside `𝔭`.
* `Stacks.Smoothing.blowup_quotient_by_surjection`: a surjection `B → A` of flat finite-type
  `R`-algebras presents the blowup of `A` as the blowup of `B`, modulo the extended kernel and
  its `π`-power torsion.

## Implementation notes

An extension of discrete valuation rings is an injective local structure map, stated directly;
the ramification index is `Stacks.DiscreteValuationRing.Ramification.ramificationIdx`. The
  factorization is given by algebra
structures together with an `IsScalarTower R A Λ`, so `R → Λ` is the composite.

The affine blowup is `affineBlowupAlgebra`, which is `affineBlowup0BIP` once the denominator is
known to lie in the ideal; `affineBlowupAlgebra_eq_affineBlowup0BIP` is that identification.
The `π`-power torsion ideal is `torsionIdeal`.

In `blowup_quotient_by_surjection`, "uniformizer" is the equivalent condition that `π`
generates the maximal ideal of the discrete valuation ring `R`.

## References

* [Stacks Project, Tag 0BJ2](https://stacks.math.columbia.edu/tag/0BJ2)
* [Stacks Project, Tag 0BJ3](https://stacks.math.columbia.edu/tag/0BJ3)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u v w

/-- The standing data and hypotheses of Stacks 0BJ2: an extension `R → Λ` of discrete
valuation rings of ramification index one, factored as `R → A → Λ` with `A` flat and of finite
type over `R`. -/
-- Stacks 0BJ2 is a Situation: its content is the conjunction of its standing hypotheses, and
-- a structure bundling exactly those is its faithful formalization. The fields below are the
-- source's data and nothing more: two discrete valuation rings, the intermediate algebra, the
-- extension being injective and local, ramification index one, and the flat finite-type
-- factorization. No extra hypothesis, so the tag is not weakened. The lemmas below take the
-- data as a hypothesis, which is the ordinary way to consume a Situation.
@[stacks 0BJ2]
structure NeronSituation where
  /-- The first discrete valuation ring. -/
  R : Type u
  /-- The second discrete valuation ring. -/
  Λ : Type v
  /-- The intermediate algebra in the factorization. -/
  A : Type w
  /-- The commutative-ring structure on `R`. -/
  [commRingR : CommRing R]
  /-- The domain structure on `R`. -/
  [isDomainR : IsDomain R]
  /-- The discrete valuation ring structure on `R`. -/
  [isDiscreteValuationRingR : IsDiscreteValuationRing R]
  /-- The commutative-ring structure on `Λ`. -/
  [commRingΛ : CommRing Λ]
  /-- The domain structure on `Λ`. -/
  [isDomainΛ : IsDomain Λ]
  /-- The discrete valuation ring structure on `Λ`. -/
  [isDiscreteValuationRingΛ : IsDiscreteValuationRing Λ]
  /-- The commutative-ring structure on `A`. -/
  [commRingA : CommRing A]
  /-- The map from `R` to `Λ`. -/
  [algebraRΛ : Algebra R Λ]
  /-- The map `R → Λ` is an extension of discrete valuation rings: injective and local. -/
  extension : Function.Injective (algebraMap R Λ) ∧ IsLocalHom (algebraMap R Λ)
  /-- The ramification index of `Λ` over `R` is one. -/
  ramificationIndex_one : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R Λ = 1
  /-- The first map in the factorization. -/
  [algebraRA : Algebra R A]
  /-- The second map in the factorization. -/
  [algebraAΛ : Algebra A Λ]
  /-- The displayed maps form a factorization of `R → Λ`. -/
  [isScalarTower : IsScalarTower R A Λ]
  /-- `A` is flat over `R`. -/
  [flat : Module.Flat R A]
  /-- `A` is of finite type over `R`. -/
  [finiteType : Algebra.FiniteType R A]

attribute [instance] NeronSituation.commRingR NeronSituation.isDomainR
  NeronSituation.isDiscreteValuationRingR NeronSituation.commRingΛ NeronSituation.isDomainΛ
  NeronSituation.isDiscreteValuationRingΛ NeronSituation.commRingA NeronSituation.algebraRΛ
  NeronSituation.algebraRA NeronSituation.algebraAΛ NeronSituation.isScalarTower
  NeronSituation.flat NeronSituation.finiteType

/-- The kernel ideal `𝔮 = Ker(A → Λ)`. -/
def NeronSituation.kernelIdeal (S : NeronSituation) : Ideal S.A :=
  RingHom.ker (algebraMap S.A S.Λ)

/-- The ideal `𝔭 = (A → Λ)^{-1}(𝔪_Λ)`. -/
def NeronSituation.maximalIdealPreimage (S : NeronSituation) : Ideal S.A :=
  Ideal.comap (algebraMap S.A S.Λ) (IsLocalRing.maximalIdeal S.Λ)

/-- The affine blowup algebra formed inside `Localization.Away b` is the subalgebra of
fractions `x / b^n` with `x ∈ I^n`, when `b ∈ I`. -/
private theorem affineBlowupAlgebra_eq_affineBlowup0BIP
    {R : Type*} [CommRing R] (I : Ideal R) (b : R) (hb : b ∈ I) :
    affineBlowupAlgebra I b (Localization.Away b) = affineBlowup0BIP I b hb := by
  ext z
  rw [← affineBlowup_eq_affineBlowupAlgebra I b, affineBlowup_mem_iff I b hb,
    mem_affineBlowup_iff0BIP]
  constructor <;> rintro ⟨n, x, hx, rfl⟩ <;>
    exact ⟨n, x, hx, by unfold frac; rw [Localization.mk_eq_mk']⟩

/-- A non-zero-divisor has no power torsion. -/
private theorem torsionIdeal_eq_bot_of_mem_nonZeroDivisors
    {R : Type*} [CommRing R] (b : R) (hb : b ∈ nonZeroDivisors R) : torsionIdeal R b = ⊥ :=
  le_bot_iff.mp fun x ⟨n, hn⟩ => (Submonoid.pow_mem _ hb n).1 x hn

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The two base-change maps into `S ⊗[R] A` agree on the image of `R`. -/
private theorem algebraMap_tensor_comm {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] (x : R) :
    algebraMap S (TensorProduct R S A) (algebraMap R S x) =
      algebraMap A (TensorProduct R S A) (algebraMap R A x) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- The image of the uniformizer is a non-zero-divisor in the localized blowup. -/
private theorem algebraMap_mem_nonZeroDivisors_tensor
    (S : NeronSituation) (b : S.A) (hb : b ∈ S.maximalIdealPreimage) (a : S.A) :
    letI A' := affineBlowup0BIP S.maximalIdealPreimage b hb
    algebraMap (Localization.Away a) (TensorProduct S.A (Localization.Away a) A')
        (algebraMap S.A (Localization.Away a) b) ∈
      nonZeroDivisors (TensorProduct S.A (Localization.Away a) A') := by
  let A' := affineBlowup0BIP S.maximalIdealPreimage b hb
  have eLoc : TensorProduct S.A (Localization.Away a) A' ≃ₐ[A']
      Localization.Away (algebraMap S.A A' a) :=
    IsLocalization.Away.tensorRightEquiv (R := S.A) (r := a)
      (A := Localization.Away a) A'
  have hbLoc : algebraMap A' (Localization.Away (algebraMap S.A A' a))
      (algebraMap S.A A' b) ∈
      nonZeroDivisors (Localization.Away (algebraMap S.A A' a)) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers (algebraMap S.A A' a)) _
      (mem_nonZeroDivisors_of_injective A'.subtype_injective
        (IsUnit.mem_nonZeroDivisors (IsLocalization.Away.algebraMap_isUnit b)))
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply eLoc.injective
  rw [map_zero]
  apply hbLoc.2 (eLoc x)
  rw [← eLoc.commutes (algebraMap S.A A' b), ← map_mul, ← algebraMap_tensor_comm, hx, map_zero]

/-- **Stacks 0BJ3.** The affine blowup at `𝔭` commutes with localizing away from an element
outside `𝔭`: if `A' = A[𝔭/π]`, then the affine blowup of `A_a` is `A'_a`. -/
@[stacks 0BJ3 "neron_localization"]
theorem neron_affineBlowup_localization
    (S : NeronSituation) (π : S.R)
    (_hπ : Irreducible π)
    (a : S.A)
    (_ha : a ∉ S.maximalIdealPreimage)
    (hπA : algebraMap S.R S.A π ∈ S.maximalIdealPreimage) :
    let A' : Type _ := affineBlowupAlgebra S.maximalIdealPreimage
      (algebraMap S.R S.A π) (Localization.Away (algebraMap S.R S.A π))
    let Aa := Localization.Away a
    let L := Localization.Away (algebraMap S.A A' a)
    let B : Type _ := affineBlowupAlgebra
      (S.maximalIdealPreimage.map (algebraMap S.A Aa))
      (algebraMap S.A Aa (algebraMap S.R S.A π))
      (Localization.Away (algebraMap S.A Aa (algebraMap S.R S.A π)))
    ∃ e : L ≃+* B,
      (∀ x : S.A, e (algebraMap A' L (algebraMap S.A A' x)) =
        algebraMap Aa B (algebraMap S.A Aa x)) ∧
      (∀ x : Aa, e (Localization.awayMap (algebraMap S.A A') a x) =
        algebraMap Aa B x) := by
  dsimp only
  let b : S.A := algebraMap S.R S.A π
  let A' := affineBlowup0BIP S.maximalIdealPreimage b hπA
  let Sa := Localization.Away a
  let T := TensorProduct S.A Sa A'
  rw [affineBlowupAlgebra_eq_affineBlowup0BIP
    (S.maximalIdealPreimage.map (algebraMap S.A Sa)) _ (Ideal.mem_map_of_mem _ hπA),
    affineBlowupAlgebra_eq_affineBlowup0BIP S.maximalIdealPreimage b hπA]
  obtain ⟨e⟩ := affineBlowup_baseChange_iso (S := Sa) S.maximalIdealPreimage b hπA
  let eLoc : T ≃ₐ[A'] Localization.Away (algebraMap S.A A' a) :=
    IsLocalization.Away.tensorRightEquiv (R := S.A) (r := a) (A := Sa) A'
  rw [torsionIdeal_eq_bot_of_mem_nonZeroDivisors _
    (algebraMap_mem_nonZeroDivisors_tensor S b hπA a)] at e
  let B' : Type _ := affineBlowup0BIP
    (S.maximalIdealPreimage.map (algebraMap S.A Sa)) (algebraMap S.A Sa b)
    (Ideal.mem_map_of_mem _ hπA)
  let f : T ≃ₐ[Sa] B' := (AlgEquiv.quotientBot Sa T).symm.trans e
  let e' : Localization.Away (algebraMap S.A A' a) ≃+* B' :=
    eLoc.symm.toRingEquiv.trans f.toRingEquiv
  have hA (x : S.A) :
      e' (algebraMap A' (Localization.Away (algebraMap S.A A' a)) (algebraMap S.A A' x)) =
      algebraMap Sa B' (algebraMap S.A Sa x) := by
    show f (eLoc.symm (algebraMap A' _ (algebraMap S.A A' x))) = _
    rw [eLoc.symm.commutes]
    rw [← algebraMap_tensor_comm, f.commutes]
  refine ⟨e', hA, ?_⟩
  have hlocalized : e'.toRingHom.comp
      (Localization.awayMap (algebraMap S.A A') a) = algebraMap Sa B' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun x => ?_)
    show e' (Localization.awayMap (algebraMap S.A A') a (algebraMap S.A Sa x)) = _
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    exact hA x
  exact RingHom.congr_fun hlocalized

/-- An algebra equivalence over an intermediate ring, tensored with one over the base. -/
private noncomputable def tensorProductMapAlgEquiv
    {R S A B C D : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [Semiring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Semiring B] [Algebra R B]
    [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
    [Semiring D] [Algebra R D]
    (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) :
    TensorProduct R A B ≃ₐ[S] TensorProduct R C D :=
  AlgEquiv.ofBijective
    (Algebra.TensorProduct.map f.toAlgHom g.toAlgHom)
    (by
      have h := Algebra.TensorProduct.map_bijective
        (f := f.toAlgHom.restrictScalars R) (g := g.toAlgHom)
        f.bijective g.bijective
      convert h using 1
      rfl)

/-- An algebra equivalence carries the power-torsion ideal of a base element to the
power-torsion ideal of the same element. -/
private lemma map_torsionIdeal_algEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (a : R) :
    Ideal.map e.toRingEquiv (torsionIdeal A (algebraMap R A a)) =
      torsionIdeal B (algebraMap R B a) := by
  have hc : Ideal.comap e.toRingEquiv (torsionIdeal B (algebraMap R B a)) =
      torsionIdeal A (algebraMap R A a) := by
    ext x
    show (∃ n : ℕ, algebraMap R B a ^ n * e x = 0) ↔ ∃ n : ℕ, algebraMap R A a ^ n * x = 0
    refine exists_congr fun n => ?_
    rw [← e.commutes a, ← map_pow, ← map_mul, map_eq_zero_iff _ e.injective]
  rw [← hc, Ideal.map_comap_of_surjective e.toRingEquiv e.surjective]

/-- Transport of the affine blowup along an equality of denominators. -/
private noncomputable def affineBlowup0BIP_algEquiv_of_denominator_eq
    {R : Type*} [CommRing R] (J : Ideal R) (b c : R)
    (hb : b ∈ J) (hc : c ∈ J) (h : b = c) :
    affineBlowup0BIP J b hb ≃ₐ[R] affineBlowup0BIP J c hc := by
  cases h
  exact Subalgebra.equivOfEq _ _ rfl

/-- **Stacks 0BJ3.** The base change of the blowup of `B` to `A`, modulo `π`-power torsion, is
the blowup of `A`. -/
private theorem nonempty_blowupBaseChangeAlgEquiv (S : NeronSituation) (π : S.R)
    (B : Type*) [CommRing B] [Algebra S.R B] (f : B →ₐ[S.R] S.A)
    (hf : Function.Surjective f)
    (ha : algebraMap S.R B π ∈ Ideal.comap f.toRingHom S.maximalIdealPreimage) :
    letI : Algebra B S.A := f.toRingHom.toAlgebra
    Nonempty <|
    (TensorProduct B S.A (affineBlowupAlgebra (Ideal.comap f.toRingHom S.maximalIdealPreimage)
        (algebraMap S.R B π) (Localization.Away (algebraMap S.R B π))) ⧸
      torsionIdeal (TensorProduct B S.A
        (affineBlowupAlgebra (Ideal.comap f.toRingHom S.maximalIdealPreimage)
          (algebraMap S.R B π) (Localization.Away (algebraMap S.R B π))))
        (algebraMap S.R _ π)) ≃ₐ[S.A]
      affineBlowupAlgebra S.maximalIdealPreimage (algebraMap S.R S.A π)
        (Localization.Away (algebraMap S.R S.A π)) := by
  let : Algebra B S.A := f.toRingHom.toAlgebra
  let pB : Ideal B := Ideal.comap f.toRingHom S.maximalIdealPreimage
  let B' := affineBlowupAlgebra pB (algebraMap S.R B π) (Localization.Away (algebraMap S.R B π))
  let A' := affineBlowupAlgebra S.maximalIdealPreimage (algebraMap S.R S.A π)
    (Localization.Away (algebraMap S.R S.A π))
  have hmap' : Ideal.map (algebraMap B S.A) pB = S.maximalIdealPreimage := by
    show Ideal.map f.toRingHom pB = S.maximalIdealPreimage
    exact Ideal.map_comap_of_surjective f.toRingHom hf _
  have hπmap : algebraMap B S.A (algebraMap S.R B π) = algebraMap S.R S.A π :=
    (IsScalarTower.algebraMap_apply S.R B S.A π).symm
  have haA : algebraMap S.R S.A π ∈ S.maximalIdealPreimage := by
    rw [← hmap', ← f.commutes π]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨e⟩ := affineBlowup_baseChange_iso (R := B) (I := pB)
    (a := algebraMap S.R B π) ha (S := S.A)
  refine ⟨?_⟩
  have hB : B' = affineBlowup0BIP pB (algebraMap S.R B π) ha :=
    affineBlowupAlgebra_eq_affineBlowup0BIP pB _ ha
  have hA : A' = affineBlowup0BIP S.maximalIdealPreimage (algebraMap S.R S.A π) haA :=
    affineBlowupAlgebra_eq_affineBlowup0BIP _ _ haA
  show (TensorProduct B S.A B' ⧸ torsionIdeal (TensorProduct B S.A B') (algebraMap S.R _ π))
    ≃ₐ[S.A] A'
  rw [hB, hA]
  have hmapmem : (algebraMap B S.A) ((algebraMap S.R B) π) ∈
      Ideal.map (algebraMap B S.A) pB := Ideal.mem_map_of_mem _ ha
  have hsub : affineBlowup0BIP (Ideal.map (algebraMap B S.A) pB)
      ((algebraMap B S.A) ((algebraMap S.R B) π)) hmapmem =
    affineBlowup0BIP S.maximalIdealPreimage
        ((algebraMap B S.A) ((algebraMap S.R B) π)) (by simpa [hπmap] using haA) := by
    generalize hj : S.maximalIdealPreimage = J at hmap' haA ⊢
    cases hmap'
    rfl
  have hscalar : algebraMap S.R
      (TensorProduct B S.A (affineBlowup0BIP pB (algebraMap S.R B π) ha)) π =
      algebraMap S.A (TensorProduct B S.A (affineBlowup0BIP pB (algebraMap S.R B π) ha))
        (algebraMap B S.A (algebraMap S.R B π)) := by
    rw [hπmap]
    exact IsScalarTower.algebraMap_apply S.R S.A _ π
  rw [hscalar]
  simpa [hmap', ← IsScalarTower.algebraMap_apply S.R S.A] using
    (e.trans (Subalgebra.equivOfEq _ _ hsub)).trans
      (affineBlowup0BIP_algEquiv_of_denominator_eq S.maximalIdealPreimage _ _
        (by simpa [hπmap] using haA) haA hπmap)

/-- **Stacks 0BJ3.** A surjection `B → A` of flat finite-type `R`-algebras presents the blowup
of `A` at `𝔭`: it is the blowup of `B` at the preimage of `𝔭`, modulo the extended kernel and
then modulo the `π`-power torsion. -/
@[stacks 0BJ3 "neron_surjection"]
lemma blowup_quotient_by_surjection (S : NeronSituation) (π : S.R)
    (hπ : Ideal.span ({π} : Set S.R) = IsLocalRing.maximalIdeal S.R)
    (B : Type*) [CommRing B] [Algebra S.R B] [Module.Flat S.R B]
    [Algebra.FiniteType S.R B]
    (f : B →ₐ[S.R] S.A) (hf : Function.Surjective f) :
    Nonempty <|
      let pB : Ideal B := Ideal.comap f.toRingHom S.maximalIdealPreimage
      let B' := affineBlowupAlgebra pB (algebraMap S.R B π)
        (Localization.Away (algebraMap S.R B π))
      let I : Ideal B := RingHom.ker f.toRingHom
      let IB' : Ideal B' := Ideal.map (algebraMap B B') I
      let T := B' ⧸ IB'
      let A' := affineBlowupAlgebra S.maximalIdealPreimage
        (algebraMap S.R S.A π) (Localization.Away (algebraMap S.R S.A π))
      (T ⧸ torsionIdeal T (algebraMap S.R T π)) ≃ₐ[S.R] A' := by
  let pB : Ideal B := Ideal.comap f.toRingHom S.maximalIdealPreimage
  let B' := affineBlowupAlgebra pB (algebraMap S.R B π) (Localization.Away (algebraMap S.R B π))
  let I : Ideal B := RingHom.ker f.toRingHom
  let A' := affineBlowupAlgebra S.maximalIdealPreimage
    (algebraMap S.R S.A π) (Localization.Away (algebraMap S.R S.A π))
  let _ : Algebra B S.A := f.toRingHom.toAlgebra
  have ha : algebraMap S.R B π ∈ pB := by
    show f (algebraMap S.R B π) ∈ S.maximalIdealPreimage
    rw [f.commutes]
    apply Ideal.mem_comap.mpr
    rw [← IsScalarTower.algebraMap_apply S.R S.A S.Λ, IsLocalRing.mem_maximalIdeal]
    exact fun hu => (IsLocalRing.mem_maximalIdeal π).mp (hπ ▸ Ideal.mem_span_singleton_self π)
      (S.extension.2.map_nonunit π hu)
  obtain ⟨e'⟩ :
      Nonempty ((TensorProduct B S.A B' ⧸
        torsionIdeal (TensorProduct B S.A B') (algebraMap S.R _ π)) ≃ₐ[S.A] A') :=
    nonempty_blowupBaseChangeAlgEquiv S π B f hf ha
  refine ⟨?_⟩
  let q : (B' ⧸ Ideal.map (algebraMap B B') I) ≃ₐ[B'] TensorProduct B B' (B ⧸ I) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot B' I
  let k : (B ⧸ I) ≃ₐ[B] S.A :=
    Ideal.quotientKerAlgEquivOfSurjective (R₁ := B) (f := (Algebra.ofId B S.A)) hf
  let t : TensorProduct B B' (B ⧸ I) ≃ₐ[B'] TensorProduct B B' S.A :=
    tensorProductMapAlgEquiv AlgEquiv.refl k
  let c : TensorProduct B B' S.A ≃ₐ[B] TensorProduct B S.A B' :=
    Algebra.TensorProduct.comm B B' S.A
  let g : (B' ⧸ Ideal.map (algebraMap B B') I) ≃ₐ[S.R] TensorProduct B S.A B' :=
    (q.trans t).restrictScalars S.R |>.trans (c.restrictScalars S.R)
  exact (Ideal.quotientEquivAlg
    (torsionIdeal (B' ⧸ Ideal.map (algebraMap B B') I) (algebraMap S.R _ π))
    (torsionIdeal (TensorProduct B S.A B') (algebraMap S.R _ π)) g
    (map_torsionIdeal_algEquiv g π).symm).trans (e'.restrictScalars S.R)

end Stacks.Smoothing

end
