module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Cech.Substrate
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.TorsionCohomologyBaseChange

/-!
# The glueing complex of a module

Given a ring map `R → S`, a finite family `f = (f₁, …, f_t)` in `R`, and an `R`-module `M`, this
file constructs the complex

`M → (M ⊗[R] S) × ∏ i, M_{f i} →
  (∏ i, (M ⊗[R] S)_{f i}) × (∏ i < j, M_{f i * f j})`,

and shows that its two maps compose to zero. Its exactness — including at its initial term — as
soon as `R → S` is flat and induces an isomorphism `R / I ≅ S / IS` for `I = (f₁, …, f_t)` is
proved in `FormalGlueingComplex.Exact`.

## Main definitions

* `FormalGlueing.GlueingTerm`: the product of localizations indexed by subsets of a fixed size.
* `FormalGlueing.glueingAlpha`: the first map of the glueing complex.
* `FormalGlueing.glueingBeta`: the second map of the glueing complex.

## Main results

* `FormalGlueing.glueingBeta_comp_glueingAlpha`: the two maps compose to zero.

## Implementation notes

Products over indices and pairs of indices are represented uniformly by products over one- and
two-element finite subsets. The second component of `glueingBeta` is the negative of the
alternating Čech differential, so its component at `{i, j}` for `i < j` is `m_i - m_j`. The ideal
`I = (f₁, …, f_t)` is represented directly by `Ideal.span (Set.range f)`, and an isomorphism of
the quotient rings is expressed as bijectivity of their canonical ring homomorphism.

## References

* [Stacks Project, Tag 05EJ](https://stacks.math.columbia.edu/tag/05EJ)
-/

/-! ### The glueing complex for a module -/

section


@[expose] public section

namespace FormalGlueing

universe u v w

open Cech

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R) (M : Type w) [AddCommGroup M] [Module R M]

/-- The product of the localizations of `N` at products of `p` distinct members of `f`.
In degrees one and two these are respectively `∏ i, N_{f i}` and
`∏ i < j, N_{f i f j}`. -/
public abbrev GlueingTerm (N : Type*) [AddCommGroup N] [Module R N] (p : ℕ) :=
  (s : {s : Finset (Fin r) // s.card = p}) → cechMod f N s.1

/-- Removing a member from a `(p + 1)`-element indexing set gives a `p`-element indexing set. -/
public def eraseIndex (p : ℕ) (T : {s : Finset (Fin r) // s.card = p + 1}) (k : T.1) :
    {s : Finset (Fin r) // s.card = p} :=
  ⟨T.1.erase k, by rw [Finset.card_erase_of_mem k.2, T.2]; omega⟩

/-- The diagonal map `N → ∏ i, N_{f i}`, sending `n` to the family of fractions `n / 1`. -/
public noncomputable def localizationDiagonal
    (N : Type*) [AddCommGroup N] [Module R N] : N →ₗ[R] GlueingTerm f N 1 :=
  LinearMap.pi fun s ↦ LocalizedModule.mkLinearMap (cechSub f s.1) N

/-- Localize the canonical map `M → M ⊗[R] S`, `m ↦ m ⊗ₜ 1`, at every product of
members of `f`. -/
public noncomputable def localizationTensorMap (p : ℕ) :
    GlueingTerm f M p →ₗ[R] GlueingTerm f (TensorProduct R M S) p :=
  LinearMap.pi fun s ↦
    ((LocalizedModule.map (cechSub f s.1) ((TensorProduct.mk R M S).flip 1)).restrictScalars R).comp
      (LinearMap.proj s : GlueingTerm f M p →ₗ[R] cechMod f M s.1)

/-- The alternating Čech differential on products of localizations. -/
public noncomputable def glueingDifferential
    (N : Type*) [AddCommGroup N] [Module R N] (p : ℕ) :
    GlueingTerm f N p →ₗ[R] GlueingTerm f N (p + 1) :=
  LinearMap.pi fun T ↦
    ∑ k ∈ T.1.attach, cechSign T.1 k •
      (cechι f N (Finset.erase_subset _ _)).comp (LinearMap.proj (eraseIndex p T k))

/-- The first map of the glueing complex. It sends `m` to `m ⊗ₜ 1` together with the
family `(m / 1)_i`. -/
public noncomputable def glueingAlpha :
    M →ₗ[R] TensorProduct R M S × GlueingTerm f M 1 :=
  LinearMap.prod ((TensorProduct.mk R M S).flip 1) (localizationDiagonal f M)

/-- The second map of the glueing complex. Its first component is
`(m' / 1 - m_i ⊗ₜ 1)_i`, and its second component is `(m_i - m_j)_{i < j}`. -/
public noncomputable def glueingBeta :
    TensorProduct R M S × GlueingTerm f M 1 →ₗ[R]
      GlueingTerm f (TensorProduct R M S) 1 × GlueingTerm f M 2 :=
  LinearMap.prod
    ((localizationDiagonal f (TensorProduct R M S)).comp
        (LinearMap.fst R (TensorProduct R M S) (GlueingTerm f M 1)) -
      (localizationTensorMap S f M 1).comp
        (LinearMap.snd R (TensorProduct R M S) (GlueingTerm f M 1)))
    (-(glueingDifferential f M 1).comp
      (LinearMap.snd R (TensorProduct R M S) (GlueingTerm f M 1)))

end FormalGlueing
end

end

section

namespace FormalGlueing

universe u v w

open Cech

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R) (M : Type w) [AddCommGroup M] [Module R M]

private lemma sum_cechSign_eq_zero_of_card_eq_two (T : Finset (Fin r)) (hT : T.card = 2) :
    ∑ k ∈ T.attach, cechSign T k.1 = 0 := by
  rw [Finset.sum_attach]
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT
  rcases lt_or_gt_of_ne hab with hab' | hab'
  · have ha : {x ∈ ({a, b} : Finset (Fin r)) | x < a} = ∅ := by
      ext x
      simp
      omega
    have hb : {x ∈ ({a, b} : Finset (Fin r)) | x < b} = {a} := by
      ext x
      simp
      omega
    rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]
    simp [cechSign, ha, hb]
  · have ha : {x ∈ ({a, b} : Finset (Fin r)) | x < a} = {b} := by
      ext x
      simp
      omega
    have hb : {x ∈ ({a, b} : Finset (Fin r)) | x < b} = ∅ := by
      ext x
      simp
      omega
    rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]
    simp [cechSign, ha, hb]

/-- The maps `glueingAlpha` and `glueingBeta` form the glueing complex of Stacks Project,
Tag 05EJ. -/
@[stacks 05EJ]
public theorem glueingBeta_comp_glueingAlpha :
    (glueingBeta S f M).comp (glueingAlpha S f M) = 0 := by
  apply LinearMap.ext
  intro m
  apply Prod.ext
  · funext T
    simp [glueingBeta, glueingAlpha, localizationDiagonal, localizationTensorMap]
  · funext T
    simp only [glueingBeta, localizationDiagonal, Nat.reduceAdd, glueingDifferential, eraseIndex,
      glueingAlpha, LinearMap.coe_comp, Function.comp_apply, LinearMap.prod_apply,
      Function.prod_apply, LinearMap.flip_apply, TensorProduct.mk_apply, LinearMap.coe_neg,
      LinearMap.coe_snd, LinearMap.sub_apply, LinearMap.coe_fst, Pi.neg_apply, LinearMap.pi_apply,
      LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply, Prod.snd_zero, Pi.zero_apply,
      neg_eq_zero]
    have hterm (k : T.1) :
        cechι f M (Finset.erase_subset k.1 T.1)
            (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
      change cechι f M (Finset.erase_subset k.1 T.1)
          (LocalizedModule.mkLinearMap (cechSub f (T.1.erase k.1)) M m) =
        LocalizedModule.mkLinearMap (cechSub f T.1) M m
      exact cechι_mk f M (Finset.erase_subset k.1 T.1) m
    change (∑ k ∈ T.1.attach, cechSign T.1 k.1 •
      cechι f M (Finset.erase_subset k.1 T.1) (LocalizedModule.mk m 1)) = 0
    rw [Finset.sum_congr rfl (fun k _ => congrArg (cechSign T.1 k.1 • ·) (hterm k))]
    rw [← Finset.sum_smul]
    simp [sum_cechSign_eq_zero_of_card_eq_two T.1 T.2]

end FormalGlueing


end
