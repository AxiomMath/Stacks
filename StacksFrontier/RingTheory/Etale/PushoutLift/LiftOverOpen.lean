module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.Algebra.Ring.Fin

/-!
# Lifting maps out of an algebra which is étale away from `V(I)`

Let `A` be a ring, `I ⊆ A` an ideal and `G` an `A`-algebra such that `G_x` is formally étale over
`A` for every `x ∈ I` ("`Spec G → Spec A` is étale over `Spec A \ V(I)`"). Let `T` be an
`A`-algebra lying over `Spec A \ V(I)`, i.e. with `I T = T`. Then `T ⊗[A] G` is formally étale over
`T` (`formallyEtale_tensorProduct_of_map_eq_top`), which is checked on the cover of
`Spec (T ⊗[A] G)` by the basic opens of the elements of `I`. Consequently `A`-algebra maps
`G → T` lift uniquely along nilpotent thickenings of `T`: this is `exists_lift_of_map_eq_top` and
`ext_of_map_eq_top`, stated under the hypothesis that `T ⊗[A] G` is formally étale over `T`.

These are used in the proof of Stacks 0ALT, where the maps to be lifted live over the complement
of the closed set along which the source glues.

## References

* [Stacks Project, Tag 0ALT](https://stacks.math.columbia.edu/tag/0ALT)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Etale.PushoutLift

/-- An ideal which together with a nilpotent ideal generates the unit ideal is the unit ideal. -/
theorem eq_top_of_sup_eq_top_of_isNilpotent {R : Type*} [CommRing R] {𝔞 𝔫 : Ideal R}
    (h𝔫 : IsNilpotent 𝔫) (h : 𝔞 ⊔ 𝔫 = ⊤) : 𝔞 = ⊤ := by
  obtain ⟨n, hn⟩ := h𝔫
  obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.mp (h.ge (Submodule.mem_top : (1 : R) ∈ ⊤))
  have hknil : IsNilpotent k := ⟨n, by
    have hmem : k ^ n ∈ 𝔫 ^ n := Ideal.pow_mem_pow hk n
    rw [hn] at hmem
    simpa using hmem⟩
  exact Ideal.eq_top_of_isUnit_mem _ ha (eq_sub_of_add_eq hak ▸ hknil.isUnit_one_sub)

variable {A G T : Type*} [CommRing A] [CommRing G] [CommRing T] [Algebra A G] [Algebra A T]

/-- **Base change to an algebra over `Spec A \ V(I)` of an algebra étale over it is formally
étale.** If `G_x` is formally étale over `A` for all `x ∈ I` and `I T = T`, then `T ⊗[A] G` is
formally étale over `T`. -/
theorem formallyEtale_tensorProduct_of_map_eq_top (I : Ideal A)
    (hG : ∀ x ∈ I, Algebra.FormallyEtale A (Localization.Away (algebraMap A G x)))
    (hT : I.map (algebraMap A T) = ⊤) : Algebra.FormallyEtale T (T ⊗[A] G) := by
  rw [← Algebra.etaleLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun Q => ?_
  have hP : I.map (algebraMap A (T ⊗[A] G)) = ⊤ := by
    rw [IsScalarTower.algebraMap_eq A T (T ⊗[A] G), ← Ideal.map_map, hT, Ideal.map_top]
  obtain ⟨x, hxI, hxQ⟩ : ∃ x ∈ I, algebraMap A (T ⊗[A] G) x ∉ Q.asIdeal := by
    by_contra! hcon
    have : I.map (algebraMap A (T ⊗[A] G)) ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.mpr hcon
    rw [hP, top_le_iff] at this
    exact Q.isPrime.ne_top this
  set h := algebraMap A G x with hh
  let Gh := Localization.Away h
  have : Algebra.FormallyEtale A Gh := hG x hxI
  let φ : (T ⊗[A] G) →ₐ[T] (T ⊗[A] Gh) :=
    Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom A G Gh)
  let : Algebra (T ⊗[A] G) (T ⊗[A] Gh) := φ.toRingHom.toAlgebra
  have : IsScalarTower T (T ⊗[A] G) (T ⊗[A] Gh) :=
    IsScalarTower.of_algebraMap_eq fun t => (φ.commutes t).symm
  have hloc := IsLocalization.tensorProduct_tensorProduct_right A T (Submonoid.powers h) Gh
    (by ext g; simp [RingHom.algebraMap_toAlgebra, φ])
  rw [Submonoid.map_powers] at hloc
  have hy : (Algebra.TensorProduct.includeRight (R := A) (A := T) h) =
      algebraMap A (T ⊗[A] G) x := by
    rw [hh, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  rw [hy] at hloc
  have hTGh : Algebra.FormallyEtale T (T ⊗[A] Gh) := inferInstance
  have hfe : Algebra.FormallyEtale T (Localization.Away (algebraMap A (T ⊗[A] G) x)) :=
    Algebra.FormallyEtale.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A (T ⊗[A] G) x))
        (T ⊗[A] Gh) _).restrictScalars T)
  exact (Algebra.basicOpen_subset_etaleLocus_iff.mpr hfe) hxQ

variable (hTG : Algebra.FormallyEtale T (T ⊗[A] G))

include hTG

/-- **Existence of lifts over `Spec A \ V(I)`.** If `T ⊗[A] G` is formally étale over `T` (for
example when `G` is étale over `Spec A \ V(I)` and `I T = T`,
`formallyEtale_tensorProduct_of_map_eq_top`), every `A`-algebra map `G → T ⧸ N` with `N`
nilpotent lifts to `G → T`. -/
theorem exists_lift_of_map_eq_top (N : Ideal T) (hN : IsNilpotent N) (g : G →ₐ[A] T ⧸ N) :
    ∃ g' : G →ₐ[A] T, (Ideal.Quotient.mkₐ A N).comp g' = g := by
  have := hTG
  let ĝ : T ⊗[A] G →ₐ[T] T ⧸ N :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ T N) g fun _ _ => Commute.all _ _
  let ℓ := Algebra.FormallySmooth.lift N hN ĝ
  refine ⟨(ℓ.restrictScalars A).comp Algebra.TensorProduct.includeRight, ?_⟩
  ext y
  have := Algebra.FormallySmooth.mk_lift N hN ĝ ((1 : T) ⊗ₜ y)
  simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply]
  rw [this]
  simp [ĝ]

/-- **Uniqueness of lifts over `Spec A \ V(I)`.** If `T ⊗[A] G` is formally étale over `T`, two
`A`-algebra maps `G → T` which agree modulo a nilpotent ideal agree. -/
theorem ext_of_map_eq_top (N : Ideal T) (hN : IsNilpotent N) {g₁ g₂ : G →ₐ[A] T}
    (h : ∀ x, Ideal.Quotient.mk N (g₁ x) = Ideal.Quotient.mk N (g₂ x)) : g₁ = g₂ := by
  have := hTG
  let ĝ (g : G →ₐ[A] T) : T ⊗[A] G →ₐ[T] T :=
    Algebra.TensorProduct.lift (Algebra.ofId T T) g fun _ _ => Commute.all _ _
  have hĝ : ĝ g₁ = ĝ g₂ := by
    refine Algebra.FormallyUnramified.ext (R := T) N hN fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul t y =>
      simp only [ĝ, Algebra.TensorProduct.lift_tmul, map_mul]
      rw [h y]
    | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  ext y
  have := congrArg (fun φ : T ⊗[A] G →ₐ[T] T => φ ((1 : T) ⊗ₜ y)) hĝ
  simpa [ĝ] using this

end Stacks.Etale.PushoutLift

end
