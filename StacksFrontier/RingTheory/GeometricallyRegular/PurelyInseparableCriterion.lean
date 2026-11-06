module

import StacksFrontier.RingTheory.Etale.Basic
public import Mathlib
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.FieldTheory.KaehlerDifferential.CartierEquality
public import StacksFrontier.RingTheory.Flat.RegularSequence
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.NaiveCotangent.H1
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.RingTheory.Cotangent.H1BaseChange

@[expose] public section

/-!
# Geometric regularity over an imperfect base field

Let `A` be a Noetherian local algebra over a field `k` of positive characteristic `p`, with residue
field `K`. This file characterizes geometric regularity of `A` over `k` by regularity after the
finite base changes inside `k^{1/p}`, and by injectivity of the canonical maps
`H₁(L_{K/k}) → 𝔪/𝔪²` and `Ω_{k/𝔽_p} ⊗_k K → Ω_{A/𝔽_p} ⊗_A K`. It also shows that lifts to `A` of
elements of the residue field whose differentials form a basis define a flat map from the
corresponding localized polynomial ring, with regular closed fibre.

## Main results

* `geometricallyRegular_tfae`: the four characterizations of geometric regularity.
* `flat_localization_and_regular_quotient_of_basis_kaehlerDifferential`: `A` is flat over the
  localized polynomial algebra determined by a basis of differentials, and the quotient by the
  extended prime is regular.
* `isLocalRing_tensorProduct_of_isPurelyInseparable`: the base change of a local ring along a
  purely inseparable field extension is local.

## References

* [Stacks Project, Tag 07E5](https://stacks.math.columbia.edu/tag/07E5)
* [Stacks Project, Tag 07E6](https://stacks.math.columbia.edu/tag/07E6)
* [G. Faltings, *Ein einfacher Beweis, dass geometrische Regularität formale Glattheit
  impliziert*][Faltings-einfacher]
-/

/-! ### Characterizations of geometric regularity -/

section

set_option maxRecDepth 4096

open scoped TensorProduct
open Algebra KaehlerDifferential TensorProduct

universe u v w

private lemma isRegularLocalRing_of_first_root_baseChange
    (p : ℕ) [Fact p.Prime] (k : Type u) (A : Type v)
    [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
    [Algebra k (PerfectClosure k p)]
    (h : ∀ (L : IntermediateField k (PerfectClosure k p)),
      FiniteDimensional k L →
      (∀ x : L, (x : PerfectClosure k p) ^ p ∈
        Set.range (algebraMap k (PerfectClosure k p))) →
      IsRegularRing (A ⊗[k] L)) : IsRegularLocalRing A := by
  have : IsRegularRing (A ⊗[k] (⊥ : IntermediateField k (PerfectClosure k p))) :=
    h ⊥ inferInstance fun x ↦ by
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp x.2
      exact ⟨a ^ p, by rw [map_pow, ha]⟩
  have : IsRegularRing A := IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := A))
      (IntermediateField.botEquiv k (PerfectClosure k p))).trans
      (Algebra.TensorProduct.rid k k A)).toRingEquiv
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing A

private lemma injective_iff_of_exact_commutative_square
    {R U V U' V' W : Type*} [Ring R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup U'] [Module R U'] [AddCommGroup V'] [Module R V']
    [AddCommMonoid W] [Module R W]
    (i : U →ₗ[R] V) (j : U' →ₗ[R] V') (q : V →ₗ[R] W)
    (q' : V' →ₗ[R] W) (f : U →ₗ[R] U') (g : V →ₗ[R] V')
    (hi : Function.Injective i) (hj : Function.Injective j)
    (he : Function.Exact i q)
    (hs : g.comp i = j.comp f) (ht : q'.comp g = q) :
    Function.Injective f ↔ Function.Injective g := by
  constructor
  · intro hf
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx ↦ ?_)
    have hqx : q x = 0 := by
      rw [← ht, LinearMap.comp_apply, hx, map_zero]
    obtain ⟨u, rfl⟩ := (he x).mp hqx
    have hfu : f u = 0 := hj (by
      rw [← LinearMap.comp_apply, ← hs, LinearMap.comp_apply, hx, map_zero])
    rw [(map_eq_zero_iff f hf).mp hfu, map_zero]
  · exact fun hg x y hxy ↦ hi (hg ((DFunLike.congr_fun hs x).trans
      ((congrArg j hxy).trans (DFunLike.congr_fun hs y).symm)))

section Naturality
variable (R S A T : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing T]
  [Algebra R S] [Algebra R A] [Algebra R T] [Algebra S A] [Algebra S T] [Algebra A T]
  [IsScalarTower R S A] [IsScalarTower R S T] [IsScalarTower R A T]
  [IsScalarTower S A T]

set_option backward.isDefEq.respectTransparency false in
private lemma h1Cotangent_delta_naturality (x : H1Cotangent S T) :
    H1Cotangent.δ R A T (H1Cotangent.map S A T T x) =
      ((mapBaseChange R S A).baseChange T)
        ((AlgebraTensorModule.cancelBaseChange S A T T Ω[S⁄R]).symm
          (H1Cotangent.δ R S T x)) := by
  let P := Generators.self S T
  let Q := Generators.self A T
  let f : Generators.Hom P Q := Generators.defaultHom P Q
  have hf : ∀ z : MvPolynomial T S,
      f.toAlgHom z = MvPolynomial.map (algebraMap S A) z := by
    intro z
    have he : f.toAlgHom.toRingHom = MvPolynomial.map (algebraMap S A) := by
      ext i <;> simp [f, P, Q, Generators.defaultHom, Generators.self,
        Generators.σ]
    exact DFunLike.congr_fun he z
  let g := ((mapBaseChange R S A).baseChange T).comp
    (AlgebraTensorModule.cancelBaseChange S A T T Ω[S⁄R]).symm.toLinearMap
  have haux : ∀ z : MvPolynomial T S,
      Generators.H1Cotangent.δAux R Q (f.toAlgHom z) =
        g (Generators.H1Cotangent.δAux R P z) := by
    intro z
    rw [hf]
    induction z using MvPolynomial.induction_on' with
    | monomial n s =>
      simp [MvPolynomial.map_monomial, Generators.H1Cotangent.δAux_monomial,
        g, P, Q]
    | add z w hz hw => simp only [RingHom.map_add, LinearMap.map_add, hz, hw]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Extension.Cotangent.mk_surjective x
  show Generators.H1Cotangent.δ Q (Generators.self R A)
    (Extension.H1Cotangent.map f.toExtensionHom ⟨Extension.Cotangent.mk y, hx⟩) =
      g (Generators.H1Cotangent.δ P (Generators.self R S) ⟨Extension.Cotangent.mk y, hx⟩)
  show Generators.H1Cotangent.δ Q (Generators.self R A) ⟨_, _⟩ = _
  simp only [LinearMap.domRestrict_apply, Extension.Cotangent.map_mk,
    Generators.H1Cotangent.δ_eq_δAux]
  exact haux y.val

private lemma h1Cotangent_delta_injective [Subsingleton (H1Cotangent R T)] :
    Function.Injective (H1Cotangent.δ R S T) := by
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx ↦ ?_)
  obtain ⟨z, rfl⟩ := (H1Cotangent.exact_map_δ R S T x).mp hx
  rw [Subsingleton.elim z 0, map_zero]

private lemma h1Cotangent_map_injective_iff_baseChange_mapBaseChange
    [Subsingleton (H1Cotangent R T)] :
    Function.Injective (H1Cotangent.map S A T T) ↔
      Function.Injective ((mapBaseChange R S A).baseChange T) := by
  let e := AlgebraTensorModule.cancelBaseChange S A T T Ω[S⁄R]
  let g := ((mapBaseChange R S A).baseChange T).comp e.symm.toLinearMap
  have h := injective_iff_of_exact_commutative_square
    (H1Cotangent.δ R S T) (H1Cotangent.δ R A T)
    (mapBaseChange R S T) (mapBaseChange R A T)
    (H1Cotangent.map S A T T) g
    (h1Cotangent_delta_injective R S T) (h1Cotangent_delta_injective R A T)
    (H1Cotangent.exact_δ_mapBaseChange R S T)
    (by ext x; exact (h1Cotangent_delta_naturality R S A T x).symm)
    (by
      ext x
      simp [g, e, ← IsScalarTower.algebraMap_apply S A T])
  refine h.trans ⟨?_, fun hf ↦ hf.comp e.symm.injective⟩
  intro hg x y hxy
  obtain ⟨x, rfl⟩ := e.symm.surjective x
  obtain ⟨y, rfl⟩ := e.symm.surjective y
  exact congrArg e.symm (hg hxy)

end Naturality

private lemma subsingleton_h1Cotangent_of_perfectField
    (R T : Type*) [Field R] [PerfectField R] [Field T] [Algebra R T] :
    Subsingleton (H1Cotangent R T) := by
  have hsep : Algebra.IsSeparableExtension R T :=
    ⟨fun L _ ↦ by
      obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField R L
      exact ⟨⟨s, hs, hsep⟩⟩⟩
  exact
    ((Algebra.isSeparableExtension_of_charZero_and_tfae R T).2.out 1 5).mp hsep

private lemma h1Cotangent_map_injective_iff_of_perfectField
    (R S A T : Type*) [Field R] [PerfectField R] [CommRing S] [CommRing A] [Field T]
    [Algebra R S] [Algebra R A] [Algebra R T] [Algebra S A] [Algebra S T] [Algebra A T]
    [IsScalarTower R S A] [IsScalarTower R S T] [IsScalarTower R A T]
    [IsScalarTower S A T] :
    Function.Injective (H1Cotangent.map S A T T) ↔
      Function.Injective ((mapBaseChange R S A).baseChange T) := by
  have := subsingleton_h1Cotangent_of_perfectField R T
  exact h1Cotangent_map_injective_iff_baseChange_mapBaseChange R S A T

/-- An integral extension of a local ring whose induced map on spectra is injective is local. -/
lemma isLocalRing_of_isIntegral_of_injective_comap
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [Nontrivial S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (PrimeSpectrum.comap (algebraMap R S))) : IsLocalRing S := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := S)
  have : m.IsMaximal := hm
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m, hm, fun q hq ↦ ?_⟩
  have : q.IsMaximal := hq
  refine congrArg PrimeSpectrum.asIdeal
    (hinj (a₁ := ⟨q, inferInstance⟩) (a₂ := ⟨m, inferInstance⟩) (PrimeSpectrum.ext ?_))
  exact (IsLocalRing.isMaximal_iff R).mp
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) q) |>.trans
    ((IsLocalRing.isMaximal_iff R).mp
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m)).symm

/-- The base change `A ⊗[k] L` of a local ring `A` along a purely inseparable field extension
`L / k` is local. -/
lemma isLocalRing_tensorProduct_of_isPurelyInseparable
    (k A L : Type*) [Field k] [CommRing A] [IsLocalRing A] [Field L]
    [Algebra k A] [Algebra k L] [IsPurelyInseparable k L] :
    IsLocalRing (A ⊗[k] L) :=
  isLocalRing_of_isIntegral_of_injective_comap A _
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k L A).injective

private lemma ringKrullDim_tensorProduct_of_isPurelyInseparable
    (k A L : Type*) [Field k] [CommRing A] [Field L]
    [Algebra k A] [Algebra k L] [IsPurelyInseparable k L] :
    ringKrullDim (A ⊗[k] L) = ringKrullDim A := by
  simpa only [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] using
    IsHomeomorph.topologicalKrullDim_eq _
      (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k L A)

private lemma finrank_comap_le
    {F V W : Type*} [DivisionRing F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) (p : Submodule F W)
    [FiniteDimensional F p] [FiniteDimensional F f.ker] :
    Module.finrank F (p.comap f) ≤ Module.finrank F p + Module.finrank F f.ker := by
  have h := f.lift_rank_comap_le p
  simpa only [← Module.finrank_eq_rank, Cardinal.lift_natCast, ← Nat.cast_add,
    Nat.cast_le] using h

private lemma finrank_le_of_exact_of_injective
    {F C V C' V' W X X' : Type*} [DivisionRing F]
    [AddCommGroup C] [Module F C] [AddCommGroup V] [Module F V]
    [AddCommGroup C'] [Module F C'] [AddCommGroup V'] [Module F V']
    [AddCommGroup W] [Module F W] [AddCommGroup X] [Module F X]
    [AddCommGroup X'] [Module F X']
    [FiniteDimensional F C']
    [FiniteDimensional F V] [FiniteDimensional F V']
    (i : C →ₗ[F] V) (d : V →ₗ[F] W) (q : W →ₗ[F] X)
    (i' : C' →ₗ[F] V') (d' : V' →ₗ[F] W) (q' : W →ₗ[F] X')
    (α : X →ₗ[F] X') [FiniteDimensional F α.ker]
    (hi : Function.Injective i) (hid : Function.Exact i d) (hdq : Function.Exact d q)
    (hid' : Function.Exact i' d') (hdq' : Function.Exact d' q')
    (hs : q' = α.comp q)
    (hnum : Module.finrank F C' + Module.finrank F α.ker ≤ Module.finrank F C) :
    Module.finrank F V' ≤ Module.finrank F V := by
  have : FiniteDimensional F C := FiniteDimensional.of_injective i hi
  have : FiniteDimensional F q.ker := by
    rw [hdq.linearMap_ker_eq]
    infer_instance
  have hq : Module.finrank F q'.ker ≤ Module.finrank F α.ker + Module.finrank F q.ker := by
    rw [hs, LinearMap.ker_comp]
    exact finrank_comap_le q α.ker
  have hd := d.finrank_range_add_finrank_ker
  have hd' := d'.finrank_range_add_finrank_ker
  rw [← hdq.linearMap_ker_eq, hid.linearMap_ker_eq] at hd
  rw [← hdq'.linearMap_ker_eq, hid'.linearMap_ker_eq] at hd'
  have hi' := LinearMap.finrank_range_le i'
  have hiRank := LinearMap.finrank_range_of_inj hi
  omega

private lemma finrank_add_finrank_ker_le_of_index
    {F C C' X X' : Type*} [DivisionRing F]
    [AddCommGroup C] [Module F C] [AddCommGroup C'] [Module F C']
    [AddCommGroup X] [Module F X] [AddCommGroup X'] [Module F X']
    [FiniteDimensional F C] (β : C →ₗ[F] C') (α : X →ₗ[F] X')
    [FiniteDimensional F (C' ⧸ β.range)]
    (h : (Module.finrank F α.ker : ℤ) - Module.finrank F β.ker +
      Module.finrank F (C' ⧸ β.range) ≤ 0) :
    Module.finrank F C' + Module.finrank F α.ker ≤ Module.finrank F C := by
  have : FiniteDimensional F C' := Module.Finite.of_submodule_quotient β.range
  have hβ := β.finrank_range_add_finrank_ker
  have hquot := Submodule.finrank_quotient_add_finrank β.range
  omega

private lemma geometricallyRegular_of_spanFinrank_tensorProduct_le
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsRegularLocalRing A]
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [Module.Finite k L]
      [IsPurelyInseparable k L],
      letI := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
      (IsLocalRing.maximalIdeal (A ⊗[k] L)).spanFinrank ≤
        (IsLocalRing.maximalIdeal A).spanFinrank) : Algebra.IsGeometricallyRegular k A := by
  constructor
  apply (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k A).mpr
  intro L _ _ _ _
  have : IsLocalRing (A ⊗[k] L) := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
  have : IsNoetherianRing (A ⊗[k] L) :=
    isNoetherian_of_tower A (S := A ⊗[k] L) (M := A ⊗[k] L) inferInstance
  have : IsRegularLocalRing (A ⊗[k] L) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [ringKrullDim_tensorProduct_of_isPurelyInseparable k A L,
      ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)]
    exact_mod_cast h L
  have hiff : IsRegularLocalRing (A ⊗[k] L) ↔ IsRegularRing (A ⊗[k] L) :=
    (IsLocalRing.isRegularRing_tfae (R := A ⊗[k] L)).out 1 3
  have : IsRegularRing (A ⊗[k] L) := hiff.mp inferInstance
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k A L).toRingEquiv

private noncomputable def h1CotangentResidueFieldEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Algebra.H1Cotangent A (IsLocalRing.ResidueField A) ≃ₗ[IsLocalRing.ResidueField A]
      IsLocalRing.CotangentSpace A :=
  ((h1Cotangent_equiv_cotangent_of_surjective A (IsLocalRing.ResidueField A)
    IsLocalRing.residue_surjective).trans
    (Ideal.Cotangent.equivOfEq _ _ (IsLocalRing.ker_residue (R := A)))).extendScalarsOfSurjective
      IsLocalRing.residue_surjective

open IsLocalRing in
/-- The first cotangent homology `H₁(L_{κ/A})` of the residue field `κ` of a Noetherian local
ring `A` is finite-dimensional over `κ`. -/
lemma finite_h1Cotangent_residueField
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Module.Finite (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)) :=
  Module.Finite.equiv (h1CotangentResidueFieldEquiv A).symm

open IsLocalRing in
private lemma finrank_h1Cotangent_residueField
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Module.finrank (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)) =
      (maximalIdeal A).spanFinrank :=
  (h1CotangentResidueFieldEquiv A).finrank_eq.trans
    (spanFinrank_maximalIdeal_eq_finrank_cotangentSpace A).symm

set_option backward.isDefEq.respectTransparency false in
private lemma h1Cotangent_delta_naturality_base
    (R R' S T : Type*) [CommRing R] [CommRing R'] [CommRing S] [CommRing T]
    [Algebra R R'] [Algebra R S] [Algebra R T] [Algebra R' S] [Algebra R' T]
    [Algebra S T] [IsScalarTower R R' S] [IsScalarTower R R' T]
    [IsScalarTower R S T] [IsScalarTower R' S T]
    (x : H1Cotangent S T) :
    H1Cotangent.δ R' S T x =
      ((KaehlerDifferential.map R R' S S).baseChange T) (H1Cotangent.δ R S T x) := by
  let Q := Generators.self S T
  have haux : ∀ z : Q.Ring,
      Generators.H1Cotangent.δAux R' Q z =
        ((KaehlerDifferential.map R R' S S).baseChange T)
          (Generators.H1Cotangent.δAux R Q z) := by
    intro z
    induction z using MvPolynomial.induction_on' with
    | monomial n s => simp [Generators.H1Cotangent.δAux_monomial]
    | add z w hz hw => simp only [map_add, hz, hw]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Extension.Cotangent.mk_surjective x
  show Generators.H1Cotangent.δ Q (Generators.self R' S) ⟨_, _⟩ = _
  simp only [H1Cotangent.δ, Q, Generators.H1Cotangent.δ_eq_δAux]
  exact haux y.val

open IsLocalRing in
private lemma spanFinrank_tensorProduct_le_of_injective_h1Cotangent_map
    (k A L : Type*) [Field k] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [IsLocalRing A] [Field L] [Algebra k L]
    [Module.Finite k L] [IsPurelyInseparable k L]
    (hinj : Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A))) :
    letI := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
    (maximalIdeal (A ⊗[k] L)).spanFinrank ≤ (maximalIdeal A).spanFinrank := by
  let B := A ⊗[k] L
  have : IsLocalRing B := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
  have : IsNoetherianRing B := isNoetherian_of_tower A (S := B) (M := B) inferInstance
  have : IsLocalHom (algebraMap A B) := Stacks.LocalHom.isLocalHom_of_isIntegral A B
  let K := ResidueField A
  let T := ResidueField B
  let : Algebra L B := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k L B := inferInstance
  have : Algebra.IsPushout k L A B := Algebra.IsPushout.symm inferInstance
  let i := (H1Cotangent.map k A K K).baseChange T
  let d := (H1Cotangent.δ k A K).baseChange T
  let q := (mapBaseChange k A K).baseChange T
  let i' := H1Cotangent.map L B T T
  let d' := H1Cotangent.δ L B T
  let q' := mapBaseChange L B T
  let e : (T ⊗[K] (K ⊗[A] Ω[A⁄k])) ≃ₗ[T] (T ⊗[B] Ω[B⁄L]) :=
    (AlgebraTensorModule.cancelBaseChange A K T T Ω[A⁄k]).trans
      ((AlgebraTensorModule.cancelBaseChange A B T T Ω[A⁄k]).symm.trans
        ((tensorKaehlerEquiv k L A B).baseChange B T _ _))
  let α := (KaehlerDifferential.map k L K T).liftBaseChange T
  let β := (H1Cotangent.map k L K T).liftBaseChange T
  have hi : Function.Injective i :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := T) _ hinj
  have hid : Function.Exact i d := Module.Flat.lTensor_exact T
    (H1Cotangent.exact_map_δ k A K)
  have hdq : Function.Exact d q := Module.Flat.lTensor_exact T
    (H1Cotangent.exact_δ_mapBaseChange k A K)
  have hid' : Function.Exact i' (e.symm.toLinearMap.comp d') :=
    (H1Cotangent.exact_map_δ L B T).comp_injective e.symm e.symm.injective (map_zero _)
  have hdq' : Function.Exact (e.symm.toLinearMap.comp d') (q'.comp e.toLinearMap) :=
    (e.symm.conj_exact_iff_exact d' q').mpr (H1Cotangent.exact_δ_mapBaseChange L B T)
  have hs : q'.comp e.toLinearMap = α.comp q := by
    ext a
    simp [q', q, e, α, ← IsScalarTower.algebraMap_apply A K T,
      ← IsScalarTower.algebraMap_apply A B T]
  have hsurj : Function.Surjective α := by
    have h := (mapBaseChange_surjective L B T residue_surjective).comp e.surjective
    change Function.Surjective (q'.comp e.toLinearMap) at h
    rw [hs] at h
    exact Function.Surjective.of_comp h
  obtain ⟨hα, _, _, hβ, hnum⟩ :=
    finrank_ker_sub_finrank_coker_kaehlerDifferential_map_sub_h1Cotangent_map k K L T
  have : FiniteDimensional T α.ker := hα
  have : FiniteDimensional T (H1Cotangent L T ⧸ β.range) := hβ
  have : FiniteDimensional K (H1Cotangent A K) := finite_h1Cotangent_residueField A
  have : FiniteDimensional K (H1Cotangent k K) := FiniteDimensional.of_injective _ hinj
  have : FiniteDimensional T (H1Cotangent B T) := finite_h1Cotangent_residueField B
  have : FiniteDimensional T (H1Cotangent L T) := Module.Finite.of_submodule_quotient β.range
  have hn : Module.finrank T (H1Cotangent L T) + Module.finrank T α.ker ≤
      Module.finrank T (T ⊗[K] H1Cotangent k K) := by
    apply finrank_add_finrank_ker_le_of_index β α
    have hr : α.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
    change (Module.finrank T α.ker : ℤ) - Module.finrank T (Ω[T⁄L] ⧸ α.range) -
      Module.finrank T β.ker + Module.finrank T (H1Cotangent L T ⧸ β.range) = _ at hnum
    rw [hr] at hnum
    simpa only [Module.finrank_eq_zero_of_subsingleton, sub_zero,
      trdeg_eq_zero, map_zero, Nat.cast_zero] using hnum.le
  have h := finrank_le_of_exact_of_injective i d q i' (e.symm.toLinearMap.comp d')
    (q'.comp e.toLinearMap) α hi hid hdq hid' hdq' hs hn
  rw [Module.finrank_baseChange] at h
  change Module.finrank (ResidueField B) (H1Cotangent B (ResidueField B)) ≤
    Module.finrank (ResidueField A) (H1Cotangent A (ResidueField A)) at h
  simpa only [finrank_h1Cotangent_residueField] using h

private lemma index_eq_of_surjective_square
    {F V V' W W' : Type*} [DivisionRing F]
    [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
    [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W']
    (q : V →ₗ[F] W) (q' : V' →ₗ[F] W') (β : V →ₗ[F] V') (γ : W →ₗ[F] W')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hcomm : q'.comp β = γ.comp q)
    [FiniteDimensional F q.ker] [FiniteDimensional F q'.ker]
    [FiniteDimensional F β.ker] [FiniteDimensional F (V' ⧸ β.range)]
    [FiniteDimensional F γ.ker] [FiniteDimensional F (W' ⧸ γ.range)] :
    β.index = γ.index + Module.finrank F q.ker - Module.finrank F q'.ker := by
  have : FiniteDimensional F (W ⧸ q.range) := by
    rw [LinearMap.range_eq_top.mpr hq]; infer_instance
  have : FiniteDimensional F (W' ⧸ q'.range) := by
    rw [LinearMap.range_eq_top.mpr hq']; infer_instance
  have h := congrArg LinearMap.index hcomm
  rw [LinearMap.index_comp, LinearMap.index_comp,
    LinearMap.index_of_surjective hq, LinearMap.index_of_surjective hq'] at h
  omega

private lemma finiteDimensional_ker_of_surjective_square
    {F V V' W W' : Type*} [DivisionRing F]
    [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
    [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W']
    (q : V →ₗ[F] W) (q' : V' →ₗ[F] W') (β : V →ₗ[F] V') (γ : W →ₗ[F] W')
    (hcomm : q'.comp β = γ.comp q)
    [FiniteDimensional F q.ker] [FiniteDimensional F γ.ker] :
    FiniteDimensional F β.ker := by
  have : FiniteDimensional F (γ.comp q).ker := by
    rw [LinearMap.ker_comp]; infer_instance
  exact Submodule.finiteDimensional_of_le (show β.ker ≤ (γ.comp q).ker by
    rw [← hcomm]; exact LinearMap.ker_le_ker_comp β q')

private lemma lTensor_exact_of_flat_cokernel
    {R M N P Q : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Flat R Q]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] Q)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h)
    (hh : Function.Surjective h) (T : Type*) [AddCommGroup T] [Module R T] :
    Function.Exact (f.lTensor T) (g.lTensor T) := by
  have hsub : Function.Exact g.range.subtype h := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact hgh.linearMap_ker_eq
  have hj : Function.Injective (g.range.subtype.lTensor T) :=
    LinearMap.lTensor_injective_of_exact_of_flat h hh g.range.subtype
      g.range.injective_subtype hsub T
  have hfg' : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact hfg x
  have hg : g = g.range.subtype.comp g.rangeRestrict := rfl
  rw [hg, LinearMap.lTensor_comp]
  exact (lTensor_exact T hfg' g.surjective_rangeRestrict).comp_injective _ hj (map_zero _)

set_option backward.isDefEq.respectTransparency false in
private lemma h1Cotangent_delta_naturality_square
    (R S A T B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing T] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R T] [Algebra R B]
    [Algebra S A] [Algebra S T] [Algebra S B] [Algebra A B] [Algebra T B]
    [IsScalarTower R S A] [IsScalarTower R S T] [IsScalarTower R S B]
    [IsScalarTower R A B] [IsScalarTower R T B] [IsScalarTower S A B] [IsScalarTower S T B]
    (x : H1Cotangent S T) :
    H1Cotangent.δ R A B (H1Cotangent.map S A T B x) =
      ((mapBaseChange R S A).baseChange B)
        ((AlgebraTensorModule.cancelBaseChange S A B B Ω[S⁄R]).symm
          (TensorProduct.map (IsScalarTower.toAlgHom S T B).toLinearMap LinearMap.id
            (H1Cotangent.δ R S T x))) := by
  let P := Generators.self S T
  let Q := Generators.self A B
  let f : Generators.Hom P Q := Generators.defaultHom P Q
  have hf : ∀ z : MvPolynomial T S,
      f.toAlgHom z = MvPolynomial.map (algebraMap S A)
        (MvPolynomial.rename (algebraMap T B) z) := by
    intro z
    have he : f.toAlgHom.toRingHom = (MvPolynomial.map (algebraMap S A)).comp
        (MvPolynomial.rename (algebraMap T B)).toRingHom := by
      ext i <;> simp [f, P, Q, Generators.defaultHom, Generators.self, Generators.σ]
    exact DFunLike.congr_fun he z
  let g := (((mapBaseChange R S A).baseChange B).comp
    (AlgebraTensorModule.cancelBaseChange S A B B Ω[S⁄R]).symm.toLinearMap).restrictScalars S
  let t := TensorProduct.map (IsScalarTower.toAlgHom S T B).toLinearMap
    (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R])
  have haux : ∀ z : MvPolynomial T S,
      Generators.H1Cotangent.δAux R Q (f.toAlgHom z) =
        g (t (Generators.H1Cotangent.δAux R P z)) := by
    intro z
    rw [hf]
    induction z using MvPolynomial.induction_on' with
    | monomial n s =>
      simp only [MvPolynomial.rename_monomial, MvPolynomial.map_monomial,
        Generators.H1Cotangent.δAux_monomial, Generators.self_val, id_eq,
        LinearMap.restrictScalars_comp, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        IsScalarTower.coe_toAlgHom', LinearMap.id_coe, LinearMap.coe_comp,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Function.comp_apply,
        AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
        mapBaseChange_tmul, map_D, one_smul, Q, g, t, P]
      congr 1
      rw [Finsupp.prod_mapDomain_index (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)]
      simp [Finsupp.prod, map_prod, map_pow]
    | add z w hz hw => rw [map_add (MvPolynomial.rename (R := S) ⇑(algebraMap T B)) z w]; simp only [RingHom.map_add, LinearMap.map_add, hz, hw]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Extension.Cotangent.mk_surjective x
  show Generators.H1Cotangent.δ Q (Generators.self R A)
    (Extension.H1Cotangent.map f.toExtensionHom ⟨Extension.Cotangent.mk y, hx⟩) =
      g (t (Generators.H1Cotangent.δ P (Generators.self R S) ⟨Extension.Cotangent.mk y, hx⟩))
  show Generators.H1Cotangent.δ Q (Generators.self R A) ⟨_, _⟩ = _
  simp only [LinearMap.domRestrict_apply, Extension.Cotangent.map_mk,
    Generators.H1Cotangent.δ_eq_δAux]
  exact haux y.val

private lemma isBaseChange_h1Cotangent_tensorProduct
    (k L A : Type*) [CommRing k] [CommRing L] [CommRing A] [Algebra k L] [Algebra k A]
    [Module.Flat k A] :
    letI : Algebra L (A ⊗[k] L) := Algebra.TensorProduct.rightAlgebra
    IsBaseChange (A ⊗[k] L) (H1Cotangent.map k A L (A ⊗[k] L)) := by
  let : Algebra L (A ⊗[k] L) := Algebra.TensorProduct.rightAlgebra
  apply Stacks.Cotangent.H1BaseChange.isBaseChange_of_isBaseChange_of_isPushout
    (R := k) (R' := A)
  exact IsBaseChange.of_equiv (Algebra.tensorH1CotangentOfFlat k L A)
    (by intro x; simp [Algebra.tensorH1CotangentOfFlat_tmul])

private lemma finiteDimensional_coker_of_exact
    {F M N P : Type*} [DivisionRing F]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [AddCommGroup P] [Module F P] [FiniteDimensional F P]
    (f : M →ₗ[F] N) (g : N →ₗ[F] P) (he : Function.Exact f g) :
    FiniteDimensional F (N ⧸ f.range) := by
  rw [← he.linearMap_ker_eq]
  exact FiniteDimensional.of_injective g.quotKerEquivRange.toLinearMap
    g.quotKerEquivRange.injective

private lemma finrank_coker_of_exact_of_surjective
    {F M N P : Type*} [DivisionRing F]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [AddCommGroup P] [Module F P]
    (f : M →ₗ[F] N) (g : N →ₗ[F] P) (he : Function.Exact f g)
    (hg : Function.Surjective g) :
    Module.finrank F (N ⧸ f.range) = Module.finrank F P := by
  rw [← he.linearMap_ker_eq]
  exact (g.quotKerEquivOfSurjective hg).finrank_eq

private lemma injective_of_exact_of_finrank_eq
    {F M N P : Type*} [DivisionRing F]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [AddCommGroup P] [Module F P] [FiniteDimensional F M]
    (f : M →ₗ[F] N) (g : N →ₗ[F] P) (he : Function.Exact f g)
    (hd : Module.finrank F g.ker = Module.finrank F M) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have h := f.finrank_range_add_finrank_ker
  rw [he.linearMap_ker_eq] at hd
  omega

open IsLocalRing in
private lemma injective_delta_baseChange_of_regular_tensorProduct
    (R k A L : Type*) [Field R] [PerfectField R] [Field k] [CommRing A] [Field L]
    [Algebra R k] [Algebra R A] [Algebra k A] [IsScalarTower R k A]
    [Algebra k L] [Module.Finite k L] [IsPurelyInseparable k L]
    [IsRegularLocalRing A] [IsRegularRing (A ⊗[k] L)] :
    letI := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
    Function.Injective ((H1Cotangent.δ R A (A ⊗[k] L)).baseChange (ResidueField (A ⊗[k] L))) := by
  let B := A ⊗[k] L
  have : IsLocalRing B := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
  have : IsRegularLocalRing B := IsRegularLocalRing.of_isRegularRing_of_isLocalRing B
  have : IsLocalHom (algebraMap A B) := Stacks.LocalHom.isLocalHom_of_isIntegral A B
  let K := ResidueField A
  let T := ResidueField B
  let : Algebra L B := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k L B := inferInstance
  have : Subsingleton (H1Cotangent R K) := subsingleton_h1Cotangent_of_perfectField R K
  have : Subsingleton (H1Cotangent R T) := subsingleton_h1Cotangent_of_perfectField R T
  have : FiniteDimensional K (H1Cotangent A K) := finite_h1Cotangent_residueField A
  have : FiniteDimensional T (H1Cotangent B T) := finite_h1Cotangent_residueField B
  obtain ⟨hΩ, hH, hdim⟩ := trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k L
  have : FiniteDimensional L Ω[L⁄k] := hΩ
  have : FiniteDimensional L (H1Cotangent k L) := hH
  let eΩ := tensorKaehlerEquiv k A L B
  have : Module.Finite B Ω[B⁄A] := Module.Finite.equiv eΩ
  have : Module.Flat B Ω[B⁄A] := Module.Flat.of_linearEquiv eΩ.symm
  let eH := (isBaseChange_h1Cotangent_tensorProduct k L A).equiv
  have : Module.Finite B (H1Cotangent A B) := Module.Finite.equiv eH
  let d := (H1Cotangent.δ R A B).baseChange T
  let β := (mapBaseChange R A B).baseChange T
  let r := (KaehlerDifferential.map R A B B).baseChange T
  have hdr : Function.Exact d β := lTensor_exact_of_flat_cokernel
    (H1Cotangent.δ R A B) (mapBaseChange R A B) (KaehlerDifferential.map R A B B)
    (H1Cotangent.exact_δ_mapBaseChange R A B) (exact_mapBaseChange_map R A B)
    (KaehlerDifferential.map_surjective R A B) T
  have hβr : Function.Exact β r := lTensor_exact T (exact_mapBaseChange_map R A B)
    (KaehlerDifferential.map_surjective R A B)
  have hr : Function.Surjective r :=
    LinearMap.lTensor_surjective T (KaehlerDifferential.map_surjective R A B)
  have : FiniteDimensional T (T ⊗[B] Ω[B⁄R] ⧸ β.range) :=
    finiteDimensional_coker_of_exact β r hβr
  let e : (T ⊗[K] (K ⊗[A] Ω[A⁄R])) ≃ₗ[T] (T ⊗[B] (B ⊗[A] Ω[A⁄R])) :=
    (AlgebraTensorModule.cancelBaseChange A K T T Ω[A⁄R]).trans
      (AlgebraTensorModule.cancelBaseChange A B T T Ω[A⁄R]).symm
  let q := ((mapBaseChange R A K).baseChange T).comp e.symm.toLinearMap
  let q' := mapBaseChange R B T
  let i := e.toLinearMap.comp ((H1Cotangent.δ R A K).baseChange T)
  let i' := H1Cotangent.δ R B T
  let γ := (KaehlerDifferential.map R R K T).liftBaseChange T
  have hi : Function.Injective i := e.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := T) _
      (h1Cotangent_delta_injective R A K))
  have hi' : Function.Injective i' := h1Cotangent_delta_injective R B T
  have hiq : Function.Exact i q :=
    (e.conj_exact_iff_exact _ _).mpr
      (Module.Flat.lTensor_exact T (H1Cotangent.exact_δ_mapBaseChange R A K))
  have hiq' : Function.Exact i' q' := H1Cotangent.exact_δ_mapBaseChange R B T
  have hq : Function.Surjective q :=
    (LinearMap.lTensor_surjective T
      (mapBaseChange_surjective R A K residue_surjective)).comp e.symm.surjective
  have hq' : Function.Surjective q' := mapBaseChange_surjective R B T residue_surjective
  have hcomm : q'.comp β = γ.comp q := by
    ext a
    simp [q', β, γ, q, e, ← IsScalarTower.algebraMap_apply A B T,
      ← IsScalarTower.algebraMap_apply A K T]
  have : FiniteDimensional T q.ker := by rw [hiq.linearMap_ker_eq]; infer_instance
  have : FiniteDimensional T q'.ker := by rw [hiq'.linearMap_ker_eq]; infer_instance
  obtain ⟨hγ, hcγ, _, _, hindexγ⟩ :=
    finrank_ker_sub_finrank_coker_kaehlerDifferential_map_sub_h1Cotangent_map R K R T
  have : FiniteDimensional T γ.ker := hγ
  have : FiniteDimensional T (Ω[T⁄R] ⧸ γ.range) := hcγ
  have : FiniteDimensional T β.ker := finiteDimensional_ker_of_surjective_square q q' β γ hcomm
  have hγzero : γ.index = 0 := by
    simpa only [LinearMap.index_eq_finrank_sub, Module.finrank_eq_zero_of_subsingleton,
      trdeg_eq_zero, map_zero, Nat.cast_zero, sub_zero, add_zero] using hindexγ
  have hqrank : Module.finrank T q.ker = (maximalIdeal A).spanFinrank := by
    rw [hiq.linearMap_ker_eq, LinearMap.finrank_range_of_inj hi, Module.finrank_baseChange]
    exact finrank_h1Cotangent_residueField A
  have hqrank' : Module.finrank T q'.ker = (maximalIdeal B).spanFinrank := by
    rw [hiq'.linearMap_ker_eq, LinearMap.finrank_range_of_inj hi']
    exact finrank_h1Cotangent_residueField B
  have hsame : (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank := by
    have h := ringKrullDim_tensorProduct_of_isPurelyInseparable k A L
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A),
      ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)] at h
    exact_mod_cast h.symm
  have hβzero : β.index = 0 := by
    rw [index_eq_of_surjective_square q q' β γ hq hq' hcomm, hγzero, hqrank, hqrank', hsame]
    omega
  apply injective_of_exact_of_finrank_eq d β hdr
  have hΩrank := (eΩ.baseChange B T _ _).finrank_eq
  have hHrank := (eH.baseChange B T _ _).finrank_eq
  rw [(AlgebraTensorModule.cancelBaseChange L B T T Ω[L⁄k]).finrank_eq,
    Module.finrank_baseChange] at hΩrank
  rw [(AlgebraTensorModule.cancelBaseChange L B T T (H1Cotangent k L)).finrank_eq,
    Module.finrank_baseChange] at hHrank
  rw [LinearMap.index_eq_finrank_sub, finrank_coker_of_exact_of_surjective β r hβr hr] at hβzero
  simp only [trdeg_eq_zero, map_zero, Nat.cast_zero] at hdim
  change Module.finrank L (H1Cotangent k L) = Module.finrank T (T ⊗[B] H1Cotangent A B) at hHrank
  omega

set_option maxHeartbeats 1000000 in
-- The `hcomm` square below elaborates a four-fold base-change composite, which exceeds the
-- default heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
private lemma eq_zero_of_mapBaseChange_eq_zero_of_regular_tensorProduct
    (R k A L : Type*) [Field R] [PerfectField R] [Field k] [CommRing A] [Field L]
    [Algebra R k] [Algebra R A] [Algebra k A] [IsScalarTower R k A]
    [Algebra k L] [Algebra R L] [IsScalarTower R k L]
    [Module.Finite k L] [IsPurelyInseparable k L]
    [IsRegularLocalRing A] [IsRegularRing (A ⊗[k] L)] :
    letI := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
    letI : Algebra L (A ⊗[k] L) := Algebra.TensorProduct.rightAlgebra
    let T := ResidueField (A ⊗[k] L)
    ∀ v : T ⊗[k] Ω[k⁄R],
      (mapBaseChange R k A).baseChange T
        ((AlgebraTensorModule.cancelBaseChange k A T T Ω[k⁄R]).symm v) = 0 →
      (mapBaseChange R k L).baseChange T
        ((AlgebraTensorModule.cancelBaseChange k L T T Ω[k⁄R]).symm v) = 0 → v = 0 := by
  have : IsLocalRing (A ⊗[k] L) := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
  let B := A ⊗[k] L
  let : Algebra L B := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k L B := inferInstance
  have : IsScalarTower R k B := IsScalarTower.to₁₂₄ R k A B
  have : IsScalarTower R L B := IsScalarTower.to₁₃₄ R k L B
  let T := ResidueField B
  let c := AlgebraTensorModule.cancelBaseChange k L T T Ω[k⁄R]
  let f := ((mapBaseChange R k A).baseChange T).comp
    (AlgebraTensorModule.cancelBaseChange k A T T Ω[k⁄R]).symm.toLinearMap
  let h := c.toLinearMap.comp ((H1Cotangent.δ R k L).baseChange T)
  let eH : B ⊗[L] H1Cotangent k L ≃ₗ[B] H1Cotangent A B :=
    (isBaseChange_h1Cotangent_tensorProduct k L A).equiv
  let e := (AlgebraTensorModule.cancelBaseChange L B T T (H1Cotangent k L)).symm.trans
    (eH.baseChange B T _ _)
  let d := (AlgebraTensorModule.cancelBaseChange A B T T Ω[A⁄R]).toLinearMap.comp
    ((H1Cotangent.δ R A B).baseChange T)
  have hd : Function.Injective d :=
    (AlgebraTensorModule.cancelBaseChange A B T T Ω[A⁄R]).injective.comp
      (injective_delta_baseChange_of_regular_tensorProduct R k A L)
  have heH (x : H1Cotangent k L) : eH (1 ⊗ₜ[L] x) = H1Cotangent.map k A L B x :=
    (isBaseChange_h1Cotangent_tensorProduct k L A).equiv_tmul 1 x |>.trans (one_smul _ _)
  have hcomm : d.comp e.toLinearMap = f.comp h := by
    ext x
    show d (e (1 ⊗ₜ[L] x)) = f (h (1 ⊗ₜ[L] x))
    simp only [d, e, f, h, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
      LinearMap.baseChange_tmul]
    rw [heH, h1Cotangent_delta_naturality_square R k A L B]
    generalize H1Cotangent.δ R k L x = y
    induction y with
    | tmul a z => simp [c]
    | add x y hx hy => simpa [f, h, c, tmul_add] using congrArg₂ (· + ·) hx hy
  dsimp only
  intro v hv hw
  have hex : Function.Exact ((H1Cotangent.δ R k L).baseChange T)
      ((mapBaseChange R k L).baseChange T) :=
    Module.Flat.lTensor_exact T (H1Cotangent.exact_δ_mapBaseChange R k L)
  obtain ⟨x, hx⟩ := (hex (c.symm v)).mp hw
  have hh : h x = v := by dsimp [h]; rw [hx, c.apply_symm_apply]
  have he : e x = 0 := hd (by
    show d (e x) = d 0
    rw [map_zero]
    calc
      d (e x) = f (h x) := DFunLike.congr_fun hcomm x
      _ = 0 := by rw [hh]; exact hv)
  have hx0 : x = 0 := e.injective (he.trans (map_zero e).symm)
  rw [← hh, hx0, map_zero]

private lemma exists_finite_first_root_extension
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    [Algebra k (PerfectClosure k p)] (s : Finset k) :
    ∃ L : IntermediateField k (PerfectClosure k p), FiniteDimensional k L ∧
      (∀ x : L, (x : PerfectClosure k p) ^ p ∈ Set.range (algebraMap k (PerfectClosure k p))) ∧
      (∀ a ∈ s, ∃ b : L, b ^ p = algebraMap k L a) := by
  classical
  let E := PerfectClosure k p
  let b : k → E := fun a ↦ (frobeniusEquiv E p).symm (algebraMap k E a)
  have hb (a : k) : b a ^ p = algebraMap k E a :=
    (frobeniusEquiv E p).apply_symm_apply (algebraMap k E a)
  let U : IntermediateField k E :=
    { (algebraMap k E).fieldRange.comap (frobenius E p) with
      algebraMap_mem' := fun a ↦ ⟨a ^ p, by simp [frobenius_def]⟩ }
  let L := IntermediateField.adjoin k (b '' (s : Set k))
  have hle : L ≤ U := IntermediateField.adjoin_le_iff.mpr (by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, (hb a).symm⟩)
  have hfin : FiniteDimensional k L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨a, ha, rfl⟩
    exact IsIntegral.of_pow (Fact.out : p.Prime).pos (hb a ▸ isIntegral_algebraMap))
  refine ⟨L, hfin, fun x ↦ hle x.2, fun a ha ↦ ?_⟩
  exact ⟨⟨b a, IntermediateField.subset_adjoin k _ ⟨a, ha, rfl⟩⟩, Subtype.val_injective (hb a)⟩

private lemma isPurelyInseparable_of_first_root_extension
    (p : ℕ) [Fact p.Prime] (k E : Type*) [Field k] [CharP k p] [Field E] [Algebra k E]
    (L : IntermediateField k E)
    (h : ∀ x : L, (x : E) ^ p ∈ Set.range (algebraMap k E)) :
    IsPurelyInseparable k L := by
  apply (isPurelyInseparable_iff_pow_mem k p).mpr
  intro x
  obtain ⟨a, ha⟩ := h x
  refine ⟨1, a, ?_⟩
  apply Subtype.val_injective
  show algebraMap k E a = (x : E) ^ (p ^ 1)
  simpa only [pow_one] using ha

set_option maxHeartbeats 1500000 in
-- The proof builds a tower of tensor-product base changes over the residue field of `A ⊗[k] L`,
-- whose elaboration exceeds the default heartbeat budget.
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
private lemma injective_mapBaseChange_of_first_root_baseChange
    (p : ℕ) [Fact p.Prime] (k : Type u) (A : Type v)
    [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
    [Algebra (ZMod p) k] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) k A]
    [Algebra k (PerfectClosure k p)]
    (hreg : ∀ (L : IntermediateField k (PerfectClosure k p)),
      FiniteDimensional k L →
      (∀ x : L, (x : PerfectClosure k p) ^ p ∈ Set.range (algebraMap k (PerfectClosure k p))) →
      IsRegularRing (A ⊗[k] L)) :
    Function.Injective ((mapBaseChange (ZMod p) k A).baseChange (ResidueField A)) := by
  classical
  have : IsRegularLocalRing A := isRegularLocalRing_of_first_root_baseChange p k A hreg
  let R := ZMod p
  let K := ResidueField A
  let cA := AlgebraTensorModule.cancelBaseChange k A K K Ω[k⁄R]
  let f := ((mapBaseChange R k A).baseChange K).comp cA.symm.toLinearMap
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    have hspan : Submodule.span K (Set.range fun a : k ↦ (1 : K) ⊗ₜ[k] D R k a) = ⊤ := by
      simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
        Function.comp_def, TensorProduct.mk_apply] using
        congrArg (Submodule.baseChange K) (span_range_derivation R k)
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
      (show u ∈ Submodule.span K (Set.range fun a : k ↦ (1 : K) ⊗ₜ[k] D R k a) by
        rw [hspan]; trivial)
    obtain ⟨L, hLfin, hLroot, hroots⟩ := exists_finite_first_root_extension p k c.support
    have : FiniteDimensional k L := hLfin
    have : IsPurelyInseparable k L := isPurelyInseparable_of_first_root_extension p k _ L hLroot
    have : IsRegularRing (A ⊗[k] L) := hreg L hLfin hLroot
    let B := A ⊗[k] L
    have : IsLocalRing B := isLocalRing_tensorProduct_of_isPurelyInseparable k A L
    have : IsLocalHom (algebraMap A B) := Stacks.LocalHom.isLocalHom_of_isIntegral A B
    let : Algebra L B := Algebra.TensorProduct.rightAlgebra
    let : Algebra R L := ((algebraMap k L).comp (algebraMap R k)).toAlgebra
    have : IsScalarTower R k L := IsScalarTower.of_algebraMap_eq' rfl
    have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
    let T := ResidueField B
    have : FaithfulSMul K T :=
      (faithfulSMul_iff_algebraMap_injective K T).mpr (algebraMap K T).injective
    let t : (K ⊗[k] Ω[k⁄R]) →ₗ[K] T ⊗[k] Ω[k⁄R] :=
      (AlgebraTensorModule.cancelBaseChange k K T T Ω[k⁄R]).toLinearMap.restrictScalars K ∘ₗ
        TensorProduct.mk K T (K ⊗[k] Ω[k⁄R]) 1
    have ht : Function.Injective t :=
      (AlgebraTensorModule.cancelBaseChange k K T T Ω[k⁄R]).injective.comp
        (Module.Flat.tensorProduct_mk_injective K (K ⊗[k] Ω[k⁄R]) T)
    let fT := ((mapBaseChange R k A).baseChange T).comp
      (AlgebraTensorModule.cancelBaseChange k A T T Ω[k⁄R]).symm.toLinearMap
    let gT := ((mapBaseChange R k L).baseChange T).comp
      (AlgebraTensorModule.cancelBaseChange k L T T Ω[k⁄R]).symm.toLinearMap
    have hv : fT (t u) = 0 := by
      have hcomm : ∀ x, fT (t x) =
          (AlgebraTensorModule.cancelBaseChange A K T T Ω[A⁄R]) (1 ⊗ₜ[K] f x) := by
        intro x
        induction x with
        | tmul a z => simp [t, fT, f, cA]
        | add x y hx hy => simpa [tmul_add] using congrArg₂ (· + ·) hx hy
      rw [hcomm, hu, tmul_zero, map_zero]
    have hw : gT (t u) = 0 := by
      rw [← hc]
      simp only [Finsupp.sum, smul_tmul', smul_eq_mul, mul_one, map_sum]
      apply Finset.sum_eq_zero
      intro a ha
      obtain ⟨b, hb⟩ := hroots a ha
      have hD : D R L (algebraMap k L a) = 0 := by
        rw [← hb, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul L, CharP.cast_eq_zero,
          zero_smul]
      simp [t, gT, hD]
    have hz : t u = 0 :=
      eq_zero_of_mapBaseChange_eq_zero_of_regular_tensorProduct R k A L (t u) hv hw
    exact ht (hz.trans (map_zero t).symm)
  intro x y hxy
  apply cA.injective
  apply hf
  simpa [f] using hxy

/-- Let `A` be a Noetherian local algebra over a field `k` of positive characteristic `p`.
The following are equivalent:

1. `A` is geometrically regular over `k`;
2. `A ⊗[k] k'` is regular for every finite intermediate field `k'` of `k¹ᵖ`;
3. `A` is regular and the canonical map from `H¹(L_(K/k))` to `𝔪/𝔪²` is injective;
4. `A` is regular and the canonical map from `Ω[k/ZMod p] ⊗[k] K` to
   `Ω[A/ZMod p] ⊗[A] K` is injective,

where `K` is the residue field of `A`. -/
@[stacks 07E5, ega "0 22.5.8" "b) ⇔ b'), char p"]
public theorem geometricallyRegular_tfae
    (p : ℕ) [Fact p.Prime] (k : Type u) (A : Type v)
    [Field k] [CharP k p] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [IsLocalRing A] :
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : Algebra (ZMod p) A :=
      ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
    letI : IsScalarTower (ZMod p) k A := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra k (PerfectClosure k p) := (PerfectClosure.of k p).toAlgebra
    List.TFAE [
      Algebra.IsGeometricallyRegular k A,
      (∀ (k' : IntermediateField k (PerfectClosure k p)),
        FiniteDimensional k k' →
        (∀ x : k', (x : PerfectClosure k p) ^ p ∈
          Set.range (algebraMap k (PerfectClosure k p))) →
        IsRegularRing (A ⊗[k] k')),
      IsRegularLocalRing A ∧
        Function.Injective
          (Algebra.H1Cotangent.map k A (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField A)),
      IsRegularLocalRing A ∧
        Function.Injective
          ((KaehlerDifferential.mapBaseChange (ZMod p) k A).baseChange
            (IsLocalRing.ResidueField A))] := by
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra (ZMod p) A :=
    ((algebraMap k A).comp (algebraMap (ZMod p) k)).toAlgebra
  let : IsScalarTower (ZMod p) k A := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra k (PerfectClosure k p) := (PerfectClosure.of k p).toAlgebra
  tfae_have 1 → 2 := by
    intro h L hfin _
    have : Algebra.IsGeometricallyRegular k A := h
    have : FiniteDimensional k L := hfin
    have : IsRegularRing (L ⊗[k] A) :=
      Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular k A L
    exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k L A).toRingEquiv
  tfae_have 2 → 4 := by
    intro h
    exact ⟨isRegularLocalRing_of_first_root_baseChange p k A h,
      injective_mapBaseChange_of_first_root_baseChange p k A h⟩
  tfae_have 3 → 1 := by
    rintro ⟨_, hinj⟩
    exact geometricallyRegular_of_spanFinrank_tensorProduct_le k A fun L _ _ _ _ ↦
      spanFinrank_tensorProduct_le_of_injective_h1Cotangent_map k A L hinj
  tfae_have 3 ↔ 4 := and_congr_right fun _ ↦
    h1Cotangent_map_injective_iff_of_perfectField (ZMod p) k A (IsLocalRing.ResidueField A)
  tfae_finish

end

/-! ### Flat local coordinates from a differential basis -/

section

open IsLocalRing Module Submodule
open scoped TensorProduct

universe u v w

/-- A list whose entries are the images of a set spanning the maximal ideal generates it. -/
private lemma ofList_eq_maximalIdeal_of_span_eq_top
    {R : Type*} [CommRing R] [IsLocalRing R] (l : List R) (S : Set (maximalIdeal R))
    (hl : {r : R | r ∈ l} = (↑) '' S) (h : span R S = ⊤) :
    Ideal.ofList l = maximalIdeal R := by
  have h' := congrArg (Submodule.map (maximalIdeal R).subtype) h
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    Ideal.submodule_span_eq] at h'
  exact (congrArg Ideal.span hl).trans h'

private lemma ofList_eq_maximalIdeal_of_span_cotangent
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (x : Fin n → maximalIdeal R)
    (hx : span (ResidueField R) (Set.range fun i => (maximalIdeal R).toCotangent (x i)) = ⊤) :
    Ideal.ofList (List.ofFn fun i => (x i : R)) = maximalIdeal R :=
  ofList_eq_maximalIdeal_of_span_eq_top _ (Set.range x) (by ext r; simp)
    (CotangentSpace.span_image_eq_top_iff.mp
      (by simpa only [← Set.range_comp, Function.comp_def] using hx))

private lemma exists_minimal_generators_append_of_linearIndependent
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (x : Fin n → maximalIdeal R)
    (hx : LinearIndependent (ResidueField R) fun i => (maximalIdeal R).toCotangent (x i)) :
    ∃ ys : List R,
      Ideal.ofList ((List.ofFn fun i => (x i : R)) ++ ys) = maximalIdeal R ∧
      ((List.ofFn fun i => (x i : R)) ++ ys).length = (maximalIdeal R).spanFinrank := by
  classical
  obtain ⟨b, hb⟩ :=
    Stacks.RegularLocalRing.RegularQuotient.exists_span_range_union_range_eq_top hx
  choose y hy using fun j ↦ (maximalIdeal R).toCotangent_surjective (b j)
  refine ⟨List.ofFn fun j ↦ (y j : R), ?_, ?_⟩
  · refine ofList_eq_maximalIdeal_of_span_eq_top _ (Set.range x ∪ Set.range y)
      (by ext r; simp [or_and_right, exists_or]) ?_
    apply CotangentSpace.span_image_eq_top_iff.mp
    simpa only [Set.image_union, ← Set.range_comp, Function.comp_def, hy] using hb
  · have hn := hx.fintype_card_le_finrank
    rw [List.length_append, List.length_ofFn, List.length_ofFn,
      spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    simpa using Nat.add_sub_of_le hn

/-- A local map between regular local rings with injective cotangent map is flat with
regular closed fibre. -/
private lemma flat_and_regular_quotient_of_cotangent_injective
    {R S : Type*} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsRegularLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (f : ResidueField S ⊗[ResidueField R] CotangentSpace R →ₗ[ResidueField S] CotangentSpace S)
    (hf : ∀ x : maximalIdeal R, f (1 ⊗ₜ (maximalIdeal R).toCotangent x) =
      (maximalIdeal S).toCotangent
        ⟨algebraMap R S x, map_nonunit (algebraMap R S) x x.property⟩)
    (hinj : Function.Injective f) :
    Module.Flat R S ∧ IsRegularLocalRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) := by
  classical
  let b := finBasis (ResidueField R) (CotangentSpace R)
  choose x hx using fun i ↦ (maximalIdeal R).toCotangent_surjective (b i)
  let z : Fin (finrank (ResidueField R) (CotangentSpace R)) → maximalIdeal S :=
    fun i ↦ ⟨algebraMap R S (x i), map_nonunit (algebraMap R S) _ (x i).property⟩
  have hz : LinearIndependent (ResidueField S) fun i ↦ (maximalIdeal S).toCotangent (z i) := by
    have h := (b.baseChange (ResidueField S)).linearIndependent.map'
      f (LinearMap.ker_eq_bot.mpr hinj)
    change LinearIndependent (ResidueField S) (fun i ↦ f (b.baseChange (ResidueField S) i)) at h
    simpa only [Basis.baseChange_apply, ← hx, hf] using h
  obtain ⟨ys, hys, hlen⟩ := exists_minimal_generators_append_of_linearIndependent z hz
  let xs := List.ofFn fun i ↦ (x i : R)
  have hxs : Ideal.ofList xs = maximalIdeal R := by
    apply ofList_eq_maximalIdeal_of_span_cotangent
    simpa only [hx] using b.span_eq
  have hmin : xs.length = (maximalIdeal R).spanFinrank := by
    simp only [xs, List.length_ofFn, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  have hmap : xs.map (algebraMap R S) = List.ofFn fun i ↦ (z i : S) := by
    simp [xs, z, Function.comp_def]
  have hreg :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay S).1
      _ hys hlen
  constructor
  · apply Module.Flat.of_ofList_eq_maximalIdeal_of_isWeaklyRegular_map S S xs hxs hmin
    rw [hmap]
    exact (RingTheory.Sequence.isWeaklyRegular_append_iff S _ _).mp hreg.1.toIsWeaklyRegular |>.1
  · have hq := (hreg.2 (List.ofFn fun i ↦ (z i : S)).length (by simp)).1
    rw [List.take_left] at hq
    have hi : Ideal.map (algebraMap R S) (maximalIdeal R) =
        Ideal.ofList (List.ofFn fun i ↦ (z i : S)) := by
      calc
        _ = Ideal.map (algebraMap R S) (Ideal.ofList xs) := congrArg _ hxs.symm
        _ = _ := by rw [Ideal.map_ofList, hmap]
    exact hi ▸ hq

private lemma h1Cotangent_map_surjective_of_mapBaseChange_injective
    (k R K : Type*) [CommRing k] [CommRing R] [CommRing K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    (h : Function.Injective (KaehlerDifferential.mapBaseChange k R K)) :
    Function.Surjective (Algebra.H1Cotangent.map k R K K) := by
  intro x
  exact (Algebra.H1Cotangent.exact_map_δ k R K x).mp (h
    (((Algebra.H1Cotangent.exact_δ_mapBaseChange k R K).apply_apply_eq_zero x).trans
      (map_zero _).symm))

/-- For a local homomorphism `R → S` of local `k`-algebras, if
`κ(R) ⊗[R] Ω[R⁄k] → Ω[κ(R)⁄k]` and `H₁(L_{κ(S)/k}) → H₁(L_{κ(S)/S})` are injective, then the
`κ(S)`-linear extension of `H₁(L_{κ(R)/R}) → H₁(L_{κ(S)/S})` is injective. -/
private lemma h1Cotangent_map_liftBaseChange_injective
    (k R S : Type*) [Field k] [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra k R] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] [IsLocalHom (algebraMap R S)]
    (hR : Function.Injective (KaehlerDifferential.mapBaseChange k R (ResidueField R)))
    (hS : Function.Injective (Algebra.H1Cotangent.map k S (ResidueField S) (ResidueField S))) :
    Function.Injective
      ((Algebra.H1Cotangent.map R S (ResidueField R) (ResidueField S)).liftBaseChange
        (ResidueField S)) := by
  let a := Algebra.H1Cotangent.map k R (ResidueField R) (ResidueField R)
  let i := (Algebra.H1Cotangent.map k k (ResidueField R) (ResidueField S)).liftBaseChange
    (ResidueField S)
  let d := (Algebra.H1Cotangent.map R S (ResidueField R) (ResidueField S)).liftBaseChange
    (ResidueField S)
  have ha : Function.Surjective (a.baseChange (ResidueField S)) :=
    LinearMap.baseChange_surjective _ (h1Cotangent_map_surjective_of_mapBaseChange_injective
      k R (ResidueField R) hR)
  have hi : Function.Injective i :=
    (jacobiZariski_exact_of_fieldExtensions k (ResidueField R) (ResidueField S)).1
  have hsquare : d ∘ₗ a.baseChange (ResidueField S) =
      (Algebra.H1Cotangent.map k S (ResidueField S) (ResidueField S)) ∘ₗ i := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c x
    show d (a.baseChange (ResidueField S) (c ⊗ₜ x)) =
      Algebra.H1Cotangent.map k S (ResidueField S) (ResidueField S) (i (c ⊗ₜ x))
    simp only [a, i, d, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
    congr 1
    simp only [Algebra.H1Cotangent.map,
      ← Algebra.Extension.H1Cotangent.map_comp_apply]
    rw [Algebra.Extension.H1Cotangent.map_eq]
  apply Function.Injective.of_comp_right (g := a.baseChange (ResidueField S)) _ ha
  show Function.Injective (d ∘ₗ a.baseChange (ResidueField S))
  rw [hsquare]
  exact hS.comp hi

private noncomputable abbrev residueExtension (R : Type*) [CommRing R] [IsLocalRing R] :
    Algebra.Extension R (ResidueField R) where
  Ring := R
  σ := Function.surjInv residue_surjective
  algebraMap_σ := Function.surjInv_eq residue_surjective

private noncomputable def residueCotangentEquiv (R : Type*) [CommRing R] [IsLocalRing R] :
    (residueExtension R).Cotangent ≃ₗ[ResidueField R] CotangentSpace R :=
  ((residueExtension R).cotangentEquivCotangentKer.trans
    (Ideal.Cotangent.equivOfEq _ _ (ker_residue (R := R)))).extendScalarsOfSurjective
      residue_surjective

private lemma residueCotangentEquiv_mk (R : Type*) [CommRing R] [IsLocalRing R]
    (x : (residueExtension R).ker) :
    residueCotangentEquiv R (Algebra.Extension.Cotangent.mk x) =
      (maximalIdeal R).toCotangent ⟨x, by
        have hx : x.val ∈ RingHom.ker (residue R) := x.property
        rwa [ker_residue] at hx⟩ := by
  rfl

/-- If the `κ(S)`-linear extension of `H₁(L_{κ(R)/R}) → H₁(L_{κ(S)/S})` is injective, then there
is an injective map `κ(S) ⊗ 𝔪_R/𝔪_R² → 𝔪_S/𝔪_S²` sending `1 ⊗ x̄` to the class of the image of
`x`. -/
private lemma cotangent_map_injective_of_h1Cotangent_map_injective
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hinj : Function.Injective
      ((Algebra.H1Cotangent.map R S (ResidueField R) (ResidueField S)).liftBaseChange
        (ResidueField S))) :
    ∃ f : ResidueField S ⊗[ResidueField R] CotangentSpace R →ₗ[ResidueField S] CotangentSpace S,
      Function.Injective f ∧ ∀ x : maximalIdeal R,
        f (1 ⊗ₜ (maximalIdeal R).toCotangent x) = (maximalIdeal S).toCotangent
          ⟨algebraMap R S x, map_nonunit (algebraMap R S) x x.property⟩ := by
  let P := residueExtension R
  let Q := residueExtension S
  let g : P.Hom Q :=
    { toRingHom := algebraMap R S
      toRingHom_algebraMap := fun _ ↦ rfl
      algebraMap_toRingHom := fun _ ↦ rfl }
  let g' : P.extendScalars.Hom Q.extendScalars :=
    { toRingHom := algebraMap R S
      toRingHom_algebraMap := fun _ ↦ rfl
      algebraMap_toRingHom := fun _ ↦ rfl }
  let eR := P.h1CotangentEquivCotangent
  let eS := Q.h1CotangentEquivCotangent
  have hsquare (x : Algebra.H1Cotangent R (ResidueField R)) :
      Algebra.Extension.Cotangent.map g (eR x) =
        eS (Algebra.H1Cotangent.map R S (ResidueField R) (ResidueField S) x) := by
    show (Algebra.Extension.Cotangent.map g)
      (Algebra.Extension.H1Cotangent.map P.extendScalars.defaultHom x).val =
        (Algebra.Extension.H1Cotangent.map Q.extendScalars.defaultHom
          (Algebra.H1Cotangent.map R S (ResidueField R) (ResidueField S) x)).val
    show (Algebra.Extension.H1Cotangent.map g'
      (Algebra.Extension.H1Cotangent.map P.extendScalars.defaultHom x)).val = _
    simp only [Algebra.H1Cotangent.map, ← Algebra.Extension.H1Cotangent.map_comp_apply]
    rw [Algebra.Extension.H1Cotangent.map_eq]
  let d := (Algebra.Extension.Cotangent.map g).liftBaseChange (ResidueField S)
  have hd : Function.Injective d := by
    have heq : d ∘ₗ eR.toLinearMap.baseChange (ResidueField S) =
        eS.toLinearMap ∘ₗ
          (Algebra.H1Cotangent.map R S (ResidueField R) (ResidueField S)).liftBaseChange
            (ResidueField S) := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c x
      show d (eR.toLinearMap.baseChange (ResidueField S) (c ⊗ₜ x)) = _
      simpa only [d, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul,
        LinearMap.comp_apply, LinearEquiv.coe_coe] using congrArg (c • ·) (hsquare x)
    apply Function.Injective.of_comp_right (g := eR.toLinearMap.baseChange (ResidueField S))
      _ (LinearMap.baseChange_surjective _ eR.surjective)
    show Function.Injective (d ∘ₗ eR.toLinearMap.baseChange (ResidueField S))
    rw [heq]
    exact eS.injective.comp hinj
  let f := (residueCotangentEquiv S).toLinearMap ∘ₗ d ∘ₗ
    (residueCotangentEquiv R).symm.toLinearMap.baseChange (ResidueField S)
  refine ⟨f, (residueCotangentEquiv S).injective.comp
    (hd.comp (LinearEquiv.baseChange (ResidueField R) (ResidueField S) _ _
      (residueCotangentEquiv R).symm).injective), ?_⟩
  intro x
  let x' : P.ker := ⟨x, by
    show residue R x = 0
    exact (residue_eq_zero_iff (R := R) x).mpr x.property⟩
  have hx : (residueCotangentEquiv R).symm ((maximalIdeal R).toCotangent x) =
      Algebra.Extension.Cotangent.mk x' := by
    apply (residueCotangentEquiv R).injective
    simpa only [LinearEquiv.apply_symm_apply] using (residueCotangentEquiv_mk R x').symm
  show residueCotangentEquiv S
    (d (((residueCotangentEquiv R).symm.toLinearMap.baseChange (ResidueField S))
      (1 ⊗ₜ (maximalIdeal R).toCotangent x))) = _
  simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hx, d,
    LinearMap.liftBaseChange_tmul, one_smul, Algebra.Extension.Cotangent.map_mk]
  rfl

/-- Independent differentials in a field extending the residue field make the residue
map on differentials injective for a formally étale polynomial algebra. -/
private lemma mapBaseChange_residueField_injective_of_linearIndependent
    (k : Type*) [CommRing k] (ι : Type*) (R F : Type*) [CommRing R] [IsLocalRing R]
    [Field F] [Algebra k R] [Algebra (MvPolynomial ι k) R]
    [IsScalarTower k (MvPolynomial ι k) R] [Algebra.FormallyEtale (MvPolynomial ι k) R]
    [Algebra k F] [Algebra R F] [IsScalarTower k R F]
    [Algebra (ResidueField R) F] [IsScalarTower R (ResidueField R) F]
    [IsScalarTower k (ResidueField R) F]
    (hF : LinearIndependent F fun i => KaehlerDifferential.D k F
      (algebraMap R F (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)))) :
    Function.Injective (KaehlerDifferential.mapBaseChange k R (ResidueField R)) := by
  let bR := ((KaehlerDifferential.mvPolynomialBasis k ι).baseChange R).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) R)
  let bK := bR.baseChange (ResidueField R)
  have hK : LinearIndependent (ResidueField R) fun i ↦
      KaehlerDifferential.D k (ResidueField R)
        (algebraMap R (ResidueField R) (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i))) := by
    apply LinearIndependent.of_comp (KaehlerDifferential.map k k (ResidueField R) F)
    simpa only [Function.comp_def, KaehlerDifferential.map_D,
      ← IsScalarTower.algebraMap_apply R (ResidueField R) F] using
        hF.restrict_scalars' (ResidueField R)
  apply LinearMap.injective_of_linearIndependent bK.span_eq
  simpa only [bK, bR, Function.comp_def, Basis.baseChange_apply, Basis.map_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D] using hK

/-- Let `A` be a Noetherian local algebra over a field `k` of positive characteristic, and assume
that `A` is geometrically regular over `k`. Let `F` be a finitely generated intermediate field of
the residue field of `A`. If `yᵢ ∈ F` have differentials forming a basis of `Ω[F⁄k]`, and a
map `k[X₁, …, Xₘ] → A` lifts the `yᵢ`, then `A` is flat over its localization at the inverse
image of the maximal ideal, and the quotient of `A` by the extended prime is regular local. -/
@[stacks 07E6]
public theorem flat_localization_and_regular_quotient_of_basis_kaehlerDifferential
    (p : ℕ) [Fact p.Prime] (k : Type u) (A : Type v)
    [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsNoetherianRing A] [IsLocalRing A]
    [Algebra.IsGeometricallyRegular k A] (m : ℕ)
    (F : IntermediateField k (ResidueField A)) [Algebra.EssFiniteType k F]
    (y : Fin m → F) (b : Module.Basis (Fin m) F Ω[F⁄k])
    (hb : ∀ i, b i = KaehlerDifferential.D k F (y i))
    (φ : MvPolynomial (Fin m) k →ₐ[k] A)
    (hφ : ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i)) :
    letI : Algebra (MvPolynomial (Fin m) k) A := φ.toRingHom.toAlgebra
    ∀ (A₀ : Type w) [CommRing A₀] [Algebra (MvPolynomial (Fin m) k) A₀]
      [IsLocalization.AtPrime A₀ ((maximalIdeal A).comap φ)] [Algebra A₀ A]
      [IsScalarTower (MvPolynomial (Fin m) k) A₀ A],
      Module.Flat A₀ A ∧
        IsRegularLocalRing (A ⧸ Ideal.map φ ((maximalIdeal A).comap φ)) := by
  classical
  let : Algebra (MvPolynomial (Fin m) k) A := φ.toRingHom.toAlgebra
  intro A₀ _ _ _ _ _
  let P := MvPolynomial (Fin m) k
  let q : Ideal P := (maximalIdeal A).comap φ
  have : q.IsPrime := Ideal.IsPrime.comap φ
  have : IsLocalRing A₀ := IsLocalization.AtPrime.isLocalRing A₀ q
  have : IsRegularLocalRing A₀ := IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) A₀).toRingEquiv
  let : Algebra k A₀ := ((algebraMap P A₀).comp (algebraMap k P)).toAlgebra
  have : IsScalarTower k P A₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower k A₀ A := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq P A₀ A]
    exact φ.comp_algebraMap.symm)
  have hmapideal : Ideal.map (algebraMap A₀ A) (maximalIdeal A₀) = Ideal.map φ q := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q A₀, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq P A₀ A]
    rfl
  have : IsLocalHom (algebraMap A₀ A) := by
    have hle : Ideal.map (algebraMap A₀ A) (maximalIdeal A₀) ≤ maximalIdeal A := by
      rw [hmapideal]
      exact Ideal.map_comap_le
    constructor
    intro a ha
    by_contra hn
    exact (hle (Ideal.mem_map_of_mem _ hn)) ha
  let ψ : P →ₐ[k] F := MvPolynomial.aeval y
  have hψ : F.val.comp ψ = (IsScalarTower.toAlgHom k A (ResidueField A)).comp φ := by
    ext i
    show algebraMap F (ResidueField A) (MvPolynomial.aeval y (MvPolynomial.X i)) =
      residue A (φ (MvPolynomial.X i))
    simpa only [MvPolynomial.aeval_X] using (hφ i).symm
  have hker : RingHom.ker ψ.toRingHom = q := by
    ext a
    show ψ a = 0 ↔ φ a ∈ maximalIdeal A
    rw [← residue_eq_zero_iff]
    have h := DFunLike.congr_fun hψ a
    change algebraMap F (ResidueField A) (ψ a) = residue A (φ a) at h
    rw [← h, map_eq_zero_iff _ (algebraMap F (ResidueField A)).injective]
  let g : A₀ →ₐ[k] F := IsLocalization.liftAlgHom (M := q.primeCompl) (f := ψ) fun t ↦
    isUnit_iff_ne_zero.mpr fun ht ↦ t.property (hker.le ht)
  let : Algebra A₀ F := g.toRingHom.toAlgebra
  have : IsScalarTower k A₀ F := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have hg (a : P) : g (algebraMap P A₀ a) = ψ a :=
    IsLocalization.lift_eq (g := ψ.toRingHom) _ a
  have : IsLocalHom (algebraMap A₀ F) := by
    constructor
    intro a ha
    obtain ⟨x, t, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl a
    apply (IsLocalization.AtPrime.isUnit_mk'_iff A₀ q x t).mpr
    intro hx
    have hz : g (IsLocalization.mk' A₀ x t) = 0 := by
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk']
      have : ψ x = 0 := by change x ∈ RingHom.ker ψ.toRingHom; rwa [hker]
      simp [this]
    exact (isUnit_iff_ne_zero.mp ha) hz
  let : Algebra (ResidueField A₀) F := (ResidueField.lift (algebraMap A₀ F)).toAlgebra
  have : IsScalarTower A₀ (ResidueField A₀) F := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k (ResidueField A₀) F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq k A₀ (ResidueField A₀), ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq A₀ (ResidueField A₀) F]
    exact IsScalarTower.algebraMap_eq k A₀ F)
  have : Algebra.FormallyEtale P A₀ := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have hd : Function.Injective (KaehlerDifferential.mapBaseChange k A₀ (ResidueField A₀)) := by
    apply mapBaseChange_residueField_injective_of_linearIndependent k (Fin m) A₀ F
    have hy : ∀ i, algebraMap A₀ F (algebraMap P A₀ (MvPolynomial.X i)) = y i := by
      intro i
      show g (algebraMap P A₀ (MvPolynomial.X i)) = y i
      rw [hg, MvPolynomial.aeval_X]
    convert b.linearIndependent using 1
    funext i
    exact (congrArg (KaehlerDifferential.D k F) (hy i)).trans (hb i).symm
  have hreg := ((geometricallyRegular_tfae p k A).out 1 3).mp
    (inferInstance : Algebra.IsGeometricallyRegular k A)
  have : IsRegularLocalRing A := hreg.1
  obtain ⟨f, hf, hfx⟩ := cotangent_map_injective_of_h1Cotangent_map_injective
    (h1Cotangent_map_liftBaseChange_injective k A₀ A hd hreg.2)
  have h := flat_and_regular_quotient_of_cotangent_injective f hfx hf
  exact ⟨h.1, hmapideal ▸ h.2⟩

end

end
