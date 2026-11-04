module

public import StacksFrontier.RingTheory.Koszul.FlatQuotient

/-!
# Regularity of a quasi-regular sequence in a flat local algebra with flat quotient

Let `R → T` be a local homomorphism of local rings with `T` flat over `R` and essentially of
finite presentation, and let `f = f₁, …, f_r` be a sequence in the maximal ideal of `T` which is
quasi-regular and whose quotient `T/(f)` is again flat over `R`. Then `f` is a *regular* sequence
in `T`, and every partial quotient `T/(f₁, …, f_i)` is flat over `R`.

This is the local step of the proof of Stacks tag 063U. It is assembled from three results:

* Stacks tag 0CEP, `Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat`, carries
  quasi-regularity of `f` to the closed fibre `T/𝔪_R T`, using exactly the flatness of `T/(f)`;
* Stacks tag 061S, `RingTheory.Sequence.IsRegular.of_isQuasiRegular_of_mem_maximalIdeal`,
  upgrades quasi-regularity to regularity on that fibre, which is Noetherian because `T` is
  essentially of finite type over `R`;
* Stacks tag 0470,
  `Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal`, carries
  fibre regularity back up to `T` — with *no Noetherian hypothesis*, which is what makes the
  step available at a stalk of a scheme.

Nothing here is about schemes. Regularity of an immersion, tag 063J part (1), asks for a
generating sequence that is regular at *every* point of an open neighbourhood, whereas the
hypotheses used here — quasi-regularity of the germs, and flatness of the quotient — are
available only at the points of the immersed subscheme itself.

## Main results

* `isQuasiRegular_closedFibre`: the image of `f` in `T/𝔪_R T` is quasi-regular.
* `isRegular_closedFibre`: that image is a regular sequence.
* `isRegular_and_flat_quotient_of_isQuasiRegular`: `f` is a regular sequence in `T`, and each
  partial quotient is flat over `R`.

## Implementation notes

The closed fibre is spelled `T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)`. Tag 0470
states its hypothesis with the submodule `𝔪_R T • (⊤ : Submodule T T)` instead, and with the
sequence acting through `T` rather than through the fibre; the two translations are
`Ideal.smul_top_eq_map` and `AddEquiv.isRegular_congr`.

`isQuasiRegular_map_of_flat` moves quasi-regularity across the ring isomorphism
`T ⊗[R] R/𝔪_R ≅ T/𝔪_R T`.

## References

* [Stacks Project, Lemma 10.69.6 (Tag 061S)](https://stacks.math.columbia.edu/tag/061S)
* [Stacks Project, Lemma 10.99.3 (Tag 0470)](https://stacks.math.columbia.edu/tag/0470)
* [Stacks Project, Lemma 15.32.4 (Tag 0CEP)](https://stacks.math.columbia.edu/tag/0CEP)
* [Stacks Project, Lemma 31.23.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public section

open RingTheory.Sequence
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.RelativeQuasiRegularFibre

/-- Quasi-regularity of a sequence travels along a flat ring map. -/
theorem isQuasiRegular_map_of_flat {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Flat) {l : List A} (hl : IsQuasiRegular A l) : IsQuasiRegular B (l.map φ) := by
  let := φ.toAlgebra
  have : Module.Flat A B := hφ
  exact hl.of_flat_of_isBaseChange (IsBaseChange.linearMap A B)

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] [IsLocalRing R]

/-- **The closed fibre is quasi-regular.** Stacks tag 0CEP applied to the base change
`R → R/𝔪_R`: if the quotient of `T` by a quasi-regular sequence is flat over `R`, the image of
that sequence in the closed fibre `T/𝔪_R T` is quasi-regular. -/
theorem isQuasiRegular_closedFibre {r : ℕ} (f : Fin r → T)
    (hqr : IsQuasiRegular T (List.ofFn f))
    (hflat : Module.Flat R (T ⧸ Ideal.span (Set.range f))) :
    IsQuasiRegular (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T))
      (List.ofFn fun i =>
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R T)) (f i)) := by
  have h := (Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat
    (A' := R ⧸ IsLocalRing.maximalIdeal R) f hflat).1 hqr
  let e : (T ⊗[R] (R ⧸ IsLocalRing.maximalIdeal R)) ≃+*
      (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)) :=
    (Algebra.TensorProduct.comm R T (R ⧸ IsLocalRing.maximalIdeal R)).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T
        (IsLocalRing.maximalIdeal R)).symm.toRingEquiv
  have h' := isQuasiRegular_map_of_flat e.toRingHom
    (RingHom.Flat.of_bijective (f := e.toRingHom) e.bijective) h
  have hfun : (⇑e.toRingHom ∘ KoszulH1.fp (A := R) (A' := R ⧸ IsLocalRing.maximalIdeal R) f) =
      fun i => Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R T)) (f i) := by
    funext i
    change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T
        (IsLocalRing.maximalIdeal R)).symm
        (Algebra.TensorProduct.comm R T (R ⧸ IsLocalRing.maximalIdeal R) (f i ⊗ₜ[R] 1)) = _
    rw [Algebra.TensorProduct.comm_tmul,
      ← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk T
        (IsLocalRing.maximalIdeal R) (f i)]
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T
      (IsLocalRing.maximalIdeal R)).symm_apply_apply _
  rwa [List.map_ofFn, hfun] at h'

variable [IsLocalRing T] [IsLocalHom (algebraMap R T)] [Algebra.EssFiniteType R T]

/-- **The closed fibre is regular.** Stacks tag 061S applied to the closed fibre `T/𝔪_R T`, which
is Noetherian because `T` is essentially of finite type over `R`. -/
theorem isRegular_closedFibre {r : ℕ} (f : Fin r → T)
    (hmem : ∀ i, f i ∈ IsLocalRing.maximalIdeal T)
    (hqr : IsQuasiRegular T (List.ofFn f))
    (hflat : Module.Flat R (T ⧸ Ideal.span (Set.range f))) :
    IsRegular (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T))
      (List.ofFn fun i =>
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R T)) (f i)) := by
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  have : Nontrivial (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R T)).ne
  have : IsLocalRing (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)) :=
    Algebra.EssFiniteType.isNoetherianRing (R ⧸ IsLocalRing.maximalIdeal R) _
  have : IsLocalHom
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R T))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine IsRegular.of_isQuasiRegular_of_mem_maximalIdeal (fun x hx => ?_)
    (isQuasiRegular_closedFibre f hqr hflat)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact IsLocalRing.map_maximalIdeal_le
    (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R T)))
    (Ideal.mem_map_of_mem _ (hmem i))

/-- **The local step of Stacks tag 063U.** Let `R → T` be a local homomorphism of local rings,
essentially of finite presentation, with `T` flat over `R` and essentially of finite type over
`R`. A quasi-regular sequence `f` in the maximal ideal of `T` whose quotient `T/(f)` is flat over
`R` is a *regular* sequence in `T`, and each of its partial quotients is flat over `R`.

No Noetherian hypothesis appears: the Noetherian ring in the proof is the closed fibre, which is
Noetherian for free. -/
theorem isRegular_and_flat_quotient_of_isQuasiRegular [Module.Flat R T]
    (hefp : (algebraMap R T).EssentiallyOfFinitePresentation) {r : ℕ} (f : Fin r → T)
    (hmem : ∀ i, f i ∈ IsLocalRing.maximalIdeal T)
    (hqr : IsQuasiRegular T (List.ofFn f))
    (hflat : Module.Flat R (T ⧸ Ideal.span (Set.range f))) :
    IsRegular T (List.ofFn f) ∧
      ∀ i, Module.Flat R
        (T ⧸ (Ideal.ofList ((List.ofFn f).take i) • (⊤ : Submodule T T))) := by
  refine Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
    (R := R) (S := T) (M := T) hefp (List.ofFn f) ?_
  -- The submodule `𝔪_R T • ⊤` of `T` is the ideal `𝔪_R T`.
  have heq : ((IsLocalRing.maximalIdeal R).map (algebraMap R T)) • (⊤ : Submodule T T) =
      (((IsLocalRing.maximalIdeal R).map (algebraMap R T) : Ideal T) : Submodule T T) := by
    simp
  rw [(Submodule.quotEquivOfEq _ _ heq).isRegular_congr (List.ofFn f)]
  -- Pass from the action of `T` to the action of the fibre.
  refine ((AddEquiv.refl (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T))).isRegular_congr
    (R := T) (S := T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T))
    (as := List.ofFn f)
    (bs := (List.ofFn f).map (Ideal.Quotient.mk _))
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun t _ x => by
      change t • x = Ideal.Quotient.mk _ t • x
      rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul])))).mpr ?_
  rw [List.map_ofFn]
  exact isRegular_closedFibre f hmem hqr hflat

end Stacks.AlgebraicGeometry.RelativeQuasiRegularFibre

end
