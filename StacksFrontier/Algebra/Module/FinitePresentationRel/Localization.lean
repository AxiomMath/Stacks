module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksFrontier.Algebra.Module.FinitePresentationRel.BaseChange
public import StacksFrontier.Algebra.Module.FinitePresentationRel.Basic

@[expose] public section

/-!
# Relative finite presentation and localization

Let `R → A` be a ring map and let `M` be an `A`-module. This file records how the predicate
`Module.FinitePresentationRel R A M` interacts with localization at one element, and shows that
the predicate is Zariski-local on `Spec A`.

## Main results

* `Module.finitePresentationRel_localizedAway`: relative finite presentation is stable under
  localizing both the algebra and the module at an element `g : A`.
* `Module.finitePresentationRel_away_of_away` (Stacks 065A): if the base is itself a
  localization `R_f` and `M` is finitely presented relative to `R_f`, then `M_g` over `A_g` is
  finitely presented relative to the *original* base `R`.
* `Module.finitePresentationRel_iff_of_span_eq_top` (Stacks 065D): for a finite type algebra
  `R → A`, relative finite presentation may be checked on any finite family of principal opens
  covering `Spec A`.

## Implementation notes

Localizations are `Localization.Away` and `LocalizedModule.Away`. In Stacks 065A the base ring
of the conclusion is `R` rather than `R_f`, so the `R`-algebra structure on `A_g` is not
available from the ambient instances; it comes from an `Algebra R A` instance together with the
scalar tower `R → R_f → A`.

The finite list of Stacks 065D is represented by a family indexed by an arbitrary finite type,
and "generate the unit ideal" by the span of the range being `⊤`.

## References

* [The Stacks Project, Lemma 15.82.8 (065A)](https://stacks.math.columbia.edu/tag/065A)
* [The Stacks Project, Lemma 15.82.9 (065D)](https://stacks.math.columbia.edu/tag/065D)
-/

universe u v w x

namespace Module

/-- Relative finite presentation is stable under localizing at an element of the algebra: if the
`A`-module `M` is finitely presented relative to `R`, then `M_g` is finitely presented relative
to `R` as a module over `A_g`. -/
theorem finitePresentationRel_localizedAway {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    [Algebra R A] (g : A) {M : Type w} [AddCommGroup M] [Module A M]
    (hM : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R (Localization.Away g) (LocalizedModule.Away g M) := by
  obtain ⟨n, α, hα, hfp⟩ := finitelyPresentedRelative_baseChange R A (Localization.Away g) M hM
  refine ⟨n, α, hα, ?_⟩
  let _ : Module (MvPolynomial (Fin n) R) (TensorProduct A (Localization.Away g) M) :=
    Module.compHom _ α.toRingHom
  let _ : Module (MvPolynomial (Fin n) R) (LocalizedModule.Away g M) :=
    Module.compHom _ α.toRingHom
  let eL := (LocalizedModule.equivTensorProduct (.powers g) M).symm
  let e : TensorProduct A (Localization.Away g) M ≃ₗ[MvPolynomial (Fin n) R]
      LocalizedModule.Away g M :=
    { eL with map_smul' := fun p z => eL.map_smul (α p) z }
  exact (LinearEquiv.finitePresentation_iff e).mp hfp

/-- Let `A` be a finite type algebra over a localization `R_f`, and let `M` be an `A`-module
finitely presented relative to `R_f`. For `g : A` the localized module `M_g` over `A_g` is
finitely presented relative to `R`. The composite `R → R_f → A` is given by an `Algebra R A`
instance together with the scalar tower `R → R_f → A`. -/
@[stacks 065A]
theorem finitePresentationRel_away_of_away {R : Type u} [CommRing R] (f : R) {A : Type v}
    [CommRing A] [Algebra (Localization.Away f) A] [Algebra R A]
    [IsScalarTower R (Localization.Away f) A]
    [Algebra.FiniteType (Localization.Away f) A] (g : A) {M : Type w} [AddCommGroup M]
    [Module A M] (hM : Module.FinitePresentationRel (Localization.Away f) A M) :
    Module.FinitePresentationRel R (Localization.Away g) (LocalizedModule.Away g M) := by
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  exact finitePresentationRel_localizedAway g
    (Module.finitePresentationRel_comp (R := R) (A := Localization.Away f) (B := A) hM)

end Module

namespace Module.FinitePresentationRel

variable {P : Type u} [CommRing P] {A : Type v} [CommRing A] {M : Type w} [AddCommGroup M]
  [Module A M]

/-- Descent of finite presentation along a surjection `π : P → A` from localizations: if a finite
family `s : ι → P` generates the unit ideal and each localization of `M` at `π (s i)` is finitely
presented over `P_{s i}`, then `M` is finitely presented over `P`.

All the module structures are the `Module.compHom` ones transported along `π` and the induced
maps on localizations, so this is a statement about `P`-modules throughout. -/
theorem finitePresentation_compHom_of_localizationSpan (π : P →+* A) {ι : Type x} [Finite ι]
    (s : ι → P) (hs : Ideal.span (Set.range s) = ⊤)
    (h : ∀ i, @Module.FinitePresentation (Localization.Away (s i))
      (LocalizedModule.Away (π (s i)) M) _ _
      (Module.compHom _ (IsLocalization.Away.map (Localization.Away (s i))
        (Localization.Away (π (s i))) π (s i)))) :
    @Module.FinitePresentation P M _ _ (Module.compHom M π) := by
  classical
  let _ : Algebra P A := π.toAlgebra
  let _ : Module P M := Module.compHom M π
  apply Module.FinitePresentation.of_localizationSpan (Set.range s) hs
  rintro ⟨_, i, rfl⟩
  let β : Localization.Away (s i) →+* Localization.Away (π (s i)) :=
    IsLocalization.Away.map _ _ π (s i)
  let _ : Algebra (Localization.Away (s i)) (Localization.Away (π (s i))) := β.toAlgebra
  let _ : Module (Localization.Away (s i)) (LocalizedModule.Away (π (s i)) M) :=
    Module.compHom _ β
  let _ : Module P (LocalizedModule.Away (π (s i)) M) :=
    Module.compHom _ (β.comp (algebraMap P (Localization.Away (s i))))
  have hβ (p : P) :
      β (algebraMap P (Localization.Away (s i)) p) =
        algebraMap A (Localization.Away (π (s i))) (π p) := by
    change IsLocalization.map _ π _ (algebraMap P _ p) = _
    exact IsLocalization.map_eq _ p
  have hsmul (p : P) (z : LocalizedModule.Away (π (s i)) M) :
      β (algebraMap P _ p) • z = π p • z := by
    rw [hβ]
    exact IsScalarTower.algebraMap_smul (Localization.Away (π (s i))) (π p) z
  let locA := LocalizedModule.mkLinearMap (Submonoid.powers (π (s i))) M
  let locP : M →ₗ[P] LocalizedModule.Away (π (s i)) M :=
    { locA with
      map_smul' := fun p m => by
        change locA (π p • m) = β (algebraMap P _ p) • locA m
        rw [locA.map_smul, hsmul] }
  have hloc : IsLocalizedModule (Submonoid.powers (s i)) locP := by
    apply IsLocalizedModule.Away.mk_of_addCommGroup
    · rw [Module.End.isUnit_iff]
      have hz := (Module.End.isUnit_iff _).mp
        (IsLocalizedModule.Away.isUnit_algebraMap locA (π (s i)))
      convert hz using 1
      funext z
      exact hsmul (s i) z
    · intro z
      obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj locA (π (s i)) z
      exact ⟨n, m, by
        change β (algebraMap P _ ((s i) ^ n)) • z = locA m
        rw [hsmul, map_pow]
        exact hm⟩
    · intro m hm
      have hm' : locA m = locA 0 := by simpa [locP] using hm
      obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := locA) (π (s i)) hm'
      exact ⟨n, by
        change π ((s i) ^ n) • m = 0
        rw [map_pow]
        simpa using hn⟩
  let _ : IsScalarTower P (Localization.Away (s i)) (LocalizedModule.Away (π (s i)) M) :=
    ⟨fun p a m => by
      change β (p • a) • m = β (algebraMap P _ p) • (β a • m)
      rw [Algebra.smul_def, map_mul, mul_smul]⟩
  let eP : LocalizedModule.Away (s i) M ≃ₗ[P] LocalizedModule.Away (π (s i)) M :=
    IsLocalizedModule.linearEquiv (Submonoid.powers (s i))
      (LocalizedModule.mkLinearMap _ M) locP
  let e := LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers (s i))
    (Localization.Away (s i)) eP
  exact (LinearEquiv.finitePresentation_iff e).mpr (h i)

end Module.FinitePresentationRel

namespace Module

open MvPolynomial

/-- Relative finite presentation of a module over a finite type algebra can be checked on a
finite family of principal opens covering the spectrum: if `f : ι → A` generates the unit ideal,
then `M` is finitely presented relative to `R` exactly when each `M_{f i}` is finitely presented
relative to `R` over `A_{f i}`. -/
@[stacks 065D]
theorem finitePresentationRel_iff_of_span_eq_top {R : Type u} [CommRing R] {A : Type v}
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {M : Type w} [AddCommGroup M]
    [Module A M] {ι : Type x} [Finite ι] (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤) :
    (∀ i, Module.FinitePresentationRel R (Localization.Away (f i))
      (LocalizedModule.Away (f i) M)) ↔ Module.FinitePresentationRel R A M := by
  refine ⟨fun h => ?_, fun h i => finitePresentationRel_localizedAway (f i) h⟩
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hone : (1 : A) ∈ Ideal.span (Set.range f) := by rw [hf]; simp
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  obtain ⟨n, α₀, hα₀⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  set σ := Fin n ⊕ ι ⊕ ι with hσ
  set Q := MvPolynomial σ R with hQ
  set α : Q →ₐ[R] A := MvPolynomial.aeval (Sum.elim (fun j => α₀ (MvPolynomial.X j))
    (Sum.elim f g)) with hαdef
  have hαX (j : σ) : α (MvPolynomial.X j) =
      Sum.elim (fun j => α₀ (MvPolynomial.X j)) (Sum.elim f g) j := MvPolynomial.aeval_X _ _
  have hα : Function.Surjective α := by
    intro a
    obtain ⟨p, rfl⟩ := hα₀ a
    refine ⟨MvPolynomial.rename Sum.inl p, ?_⟩
    rw [← AlgHom.comp_apply]
    have : α.comp (MvPolynomial.rename Sum.inl) = α₀ :=
      MvPolynomial.algHom_ext fun j => by rw [AlgHom.comp_apply, MvPolynomial.rename_X, hαX]; rfl
    rw [this]
  have hαf (i : ι) : α (MvPolynomial.X (Sum.inr (Sum.inl i))) = f i := hαX _
  have hαg (i : ι) : α (MvPolynomial.X (Sum.inr (Sum.inr i))) = g i := hαX _
  set q : Q := ∑ i, MvPolynomial.X (Sum.inr (Sum.inl i)) *
    MvPolynomial.X (Sum.inr (Sum.inr i)) - 1 with hqdef
  have hq : α q = 0 := by
    simp only [hqdef, map_sub, map_sum, map_mul, map_one, hαf, hαg]
    rw [show ∑ i, f i * g i = 1 by simpa only [mul_comm] using hg]
    exact sub_self 1
  set J : Ideal Q := Ideal.span {q} with hJdef
  set P := Q ⧸ J with hPdef
  have hJ : ∀ a ∈ J, (α : Q →+* A) a = 0 := by
    intro a ha
    refine (show J ≤ RingHom.ker α.toRingHom from ?_) ha
    rw [hJdef, Ideal.span_le, Set.singleton_subset_iff]
    exact hq
  set π : P →ₐ[R] A := Ideal.Quotient.liftₐ J α hJ with hπdef
  have hπmk (p : Q) : π ((Ideal.Quotient.mk J) p) = α p :=
    calc π ((Ideal.Quotient.mk J) p) = (π.comp (Ideal.Quotient.mkₐ R J)) p := rfl
      _ = α p := congrArg (fun φ : Q →ₐ[R] A => φ p) (Ideal.Quotient.liftₐ_comp J α hJ)
  have hπ : Function.Surjective π := by
    intro a
    obtain ⟨p, rfl⟩ := hα a
    exact ⟨Ideal.Quotient.mk J p, hπmk p⟩
  set y : ι → P := fun i => Ideal.Quotient.mk J (MvPolynomial.X (Sum.inr (Sum.inl i))) with hydef
  have hy : Ideal.span (Set.range y) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun i => Ideal.Quotient.mk J (MvPolynomial.X (Sum.inr (Sum.inr i))), ?_⟩
    have hzero : Ideal.Quotient.mk J q = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (show q ∈ ({q} : Set Q) by simp))
    simpa only [hqdef, hydef, map_sub, map_sum, map_mul, map_one, zero_add, sub_add_cancel,
      mul_comm] using congrArg (fun z : P => z + 1) hzero
  have hπy (i : ι) : π (y i) = f i := (hπmk _).trans (hαf i)
  have hPfp : Algebra.FinitePresentation R P :=
    (inferInstance : Algebra.FinitePresentation R Q).quotient
      (Submodule.fg_span (Set.finite_singleton q))
  have hlocal (i : ι) :
      @Module.FinitePresentation (Localization.Away (y i))
        (LocalizedModule.Away (π (y i)) M) _ _
        (Module.compHom _ (IsLocalization.Away.map (Localization.Away (y i))
          (Localization.Away (π (y i))) π.toRingHom (y i))) := by
    let β : Localization.Away (y i) →ₐ[R] Localization.Away (π (y i)) :=
      IsLocalization.Away.mapₐ (Localization.Away (y i)) (Localization.Away (π (y i))) π (y i)
    have hβ : Function.Surjective β :=
      IsLocalization.Away.mapₐ_surjective_of_surjective (y i) hπ
    have hi : Module.FinitePresentationRel R (Localization.Away (π (y i)))
        (LocalizedModule.Away (π (y i)) M) := by
      rw [hπy i]
      exact h i
    exact Module.FinitePresentationRel.allFPCovers_of_finitePresentationRel hi
      (Localization.Away (y i)) inferInstance β hβ
  have hPM : @Module.FinitePresentation P M _ _ (Module.compHom M π.toRingHom) :=
    Module.FinitePresentationRel.finitePresentation_compHom_of_localizationSpan π.toRingHom y hy
      hlocal
  obtain ⟨m, δ, hδ, hker⟩ := hPfp.out
  exact ⟨m, π.comp δ, hπ.comp hδ,
    Module.finitePresentation_compHom_comp π.toRingHom δ.toRingHom hδ hker hPM⟩

end Module
