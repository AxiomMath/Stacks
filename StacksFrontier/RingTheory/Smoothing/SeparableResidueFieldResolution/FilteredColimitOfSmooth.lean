module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.Smooth.FieldExtensionCompleteIntersectionColimit
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.CompleteIntersection.Smooth
public import StacksFrontier.RingTheory.Flat.RegularSequence
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smoothing.DesingularizationLifting
public import StacksFrontier.RingTheory.Smoothing.ImprovingPresentations
public import StacksFrontier.RingTheory.Smoothing.IndSmooth
public import StacksFrontier.RingTheory.Smoothing.LiftingProblem
public import StacksFrontier.RingTheory.Smoothing.LiftingResolutionsFromEighthPowers
public import StacksFrontier.RingTheory.Smoothing.LocalSmoothingSituation
public import StacksFrontier.RingTheory.Smoothing.ParametersWithPowersInIdeal
public import StacksFrontier.RingTheory.Smoothing.SingularIdealFactorization
public import StacksFrontier.RingTheory.Smoothing.SingularIdeals
public import StacksFrontier.RingTheory.Smoothing.SpreadingOutResolutions
public import StacksFrontier.RingTheory.Smoothing.StablyFreeStrictlyStandardPowers
public import StacksFrontier.RingTheory.Smoothing.StandardnessConditions
public import StacksFrontier.RingTheory.Smoothing.ZeroDimensionalResolution
public import StacksFrontier.RingTheory.Smoothing.SeparableResidueFieldResolution.ParameterPresentation
import all StacksFrontier.RingTheory.Smoothing.SeparableResidueFieldResolution.ParameterPresentation

/-!
# Filtered colimits of smooth algebras

Auxiliary results for the resolution of a local smoothing situation with separable residue
field: flatness of a localization over a polynomial ring in parameters, uniform strictly standard
powers, the ideals of eighth powers of parameters, and filtered colimits of smooth algebras.

## Main definitions

* `Stacks.Smoothing.IsFilteredColimitOfSmooth`: `Λ` is a filtered colimit of smooth
  `R`-algebras, in a form that allows `R` and `Λ` to live in different universes.

## Implementation notes

`IsFilteredColimitOfSmooth` is the universe-polymorphic form of the property `PT` of Tag 07F1:
`PT` is stated for a base and a target in `Type`, and the reduction step here compares a base in
one universe with a target in another.

Proposition 07CM is used in the spelling it is stated in,
`Stacks.Smoothing.ind_smooth_of_isNilpotent`, through two translation lemmas between
`IsFilteredColimitOfSmooth` and `CategoryTheory.ObjectProperty.ind` of `RingHom.Smooth` on
`Under (CommRingCat.of R)`: one direction is the factorization criterion of Tag 07C3, the other
carries a colimit presentation along `commAlgCatEquivUnder`.

## References

* [Stacks Project, Tag 07F1](https://stacks.math.columbia.edu/tag/07F1)
* [Stacks Project, Tag 07FE](https://stacks.math.columbia.edu/tag/07FE)
-/

@[expose] public section

namespace Stacks.Smoothing

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w u' v' t

private lemma flat_polynomial_localization_of_parameters
    {k Λ : Type*} [Field k] [CommRing Λ] {d : ℕ}
    [Algebra (MvPolynomial (Fin d) k) Λ]
    (q : Ideal Λ) [q.IsPrime] [IsRegularLocalRing (Localization.AtPrime q)]
    (hXq : ∀ i : Fin d, algebraMap (MvPolynomial (Fin d) k) Λ (MvPolynomial.X i) ∈ q)
    (hspan : Ideal.map (algebraMap Λ (Localization.AtPrime q))
      (Ideal.span (Set.range fun i : Fin d =>
        algebraMap (MvPolynomial (Fin d) k) Λ (MvPolynomial.X i))) =
      Ideal.map (algebraMap Λ (Localization.AtPrime q)) q)
    (hd : ringKrullDim (Localization.AtPrime q) = d) :
    Module.Flat (MvPolynomial (Fin d) k) (Localization.AtPrime q) := by
  let R := MvPolynomial (Fin d) k
  let m : Ideal R := MvPolynomial.idealOfVars (Fin d) k
  have : m.IsMaximal := polynomial_idealOfVars_isMaximal
  have hm : m = q.comap (algebraMap R Λ) := by
    apply Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance)
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hXq i
  let Rp := Localization.AtPrime m
  let L := Localization.AtPrime q
  let f : Rp →+* L := Localization.localRingHom m q (algebraMap R Λ) hm
  let : Algebra Rp L := f.toAlgebra
  have : IsScalarTower R Rp L := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap R L x = f (algebraMap R Rp x)
    exact (Localization.localRingHom_to_map m q (algebraMap R Λ) hm x).symm
  have : IsLocalHom (algebraMap Rp L) :=
    Localization.isLocalHom_localRingHom m q (algebraMap R Λ) hm
  obtain ⟨hregRp, hdimRp⟩ :=
    (MvPolynomial.isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization
      k (Fin d)).2.2 m Rp
  let := hregRp
  let xs : List Rp := List.ofFn fun i : Fin d => algebraMap R Rp (MvPolynomial.X i)
  have hxs : Ideal.ofList xs = IsLocalRing.maximalIdeal Rp := by
    have hmmap := IsLocalization.AtPrime.map_eq_maximalIdeal m Rp
    change Ideal.map (algebraMap R Rp) (Ideal.span (Set.range MvPolynomial.X)) = _ at hmmap
    rw [Ideal.map_span, ← Set.range_comp] at hmmap
    rw [← hmmap]
    unfold Ideal.ofList
    congr 1
    ext x
    simp [xs]
  have hlen : xs.length = (IsLocalRing.maximalIdeal Rp).spanFinrank := by
    have h := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := Rp)).trans hdimRp
    have : d = (IsLocalRing.maximalIdeal Rp).spanFinrank := by
      simp only [Nat.card_fin] at h
      exact_mod_cast h.symm
    simpa [xs] using this
  have hreg := isRegular_localized_parameters q
    (fun i : Fin d => algebraMap R Λ (MvPolynomial.X i)) hspan hd
  have hreg' : RingTheory.Sequence.IsWeaklyRegular L (xs.map (algebraMap Rp L)) := by
    convert hreg.toIsWeaklyRegular using 1
    simp only [xs, List.map_ofFn, Function.comp_def]
    congr 1
    funext i
    exact Localization.localRingHom_to_map m q (algebraMap R Λ) hm _
  have : Module.Flat Rp L :=
    Module.Flat.of_ofList_eq_maximalIdeal_of_isWeaklyRegular_map L L xs hxs hlen hreg'
  exact Module.Flat.trans R Rp L

private lemma exists_uniform_strictStandard_power
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.FinitePresentation R C] {d : ℕ} (x : Fin d → R)
    (hsmooth : ∀ i, Algebra.Smooth R
      (Localization.Away (algebraMap R C (x i))))
    (hfree : ∀ i, Module.Free (Localization.Away (algebraMap R C (x i)))
      (KaehlerDifferential R (Localization.Away (algebraMap R C (x i))))) :
    ∃ c : ℕ, 0 < c ∧ ∀ i,
      IsStrictlyStandard (R := R) (A := C)
        (algebraMap R C (x i) ^ c) := by
  classical
  let S (i : Fin d) : SixStandardnessConditions.{u, v} :=
    { R := R, A := C, a := algebraMap R C (x i) }
  have hstable (i : Fin d) :
      Module.IsStablyFree (Localization.Away (algebraMap R C (x i)))
        (KaehlerDifferential R (Localization.Away (algebraMap R C (x i)))) :=
    (Stacks.Smoothing.free_of_differentials_implies_stably_free (S i) ⟨hsmooth i, hfree i⟩).2
  have H (i : Fin d) : ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandard (R := R) ((algebraMap R C (x i)) ^ e) :=
    Stacks.Smoothing.exists_eventually_isStrictlyStandard_pow (S i) ⟨hsmooth i, hstable i⟩
  choose e₀ he₀ using H
  let c := 1 + ∑ i : Fin d, e₀ i
  refine ⟨c, by dsimp [c]; omega, ?_⟩
  intro i
  apply he₀ i c
  dsimp [c]
  have hle := Finset.single_le_sum (s := Finset.univ) (f := e₀) (by intro j hj; omega)
    (Finset.mem_univ i)
  omega

private lemma mem_parameter_prefix_iff_support
    {k : Type u} [Field k] {d c : ℕ} (i : Fin d) (p : MvPolynomial (Fin d) k) :
    p ∈ eighthPowerPrefixIdeal (fun j : Fin d => MvPolynomial.X j ^ c) i ↔
      ∀ m ∈ p.support, ∃ j : Fin i.val,
        c * 8 ≤ m (j.castLE (Nat.le_of_lt i.isLt)) := by
  classical
  let G : Set (Fin d →₀ ℕ) := Set.range fun j : Fin i.val =>
    Finsupp.single (j.castLE (Nat.le_of_lt i.isLt)) (c * 8)
  have hgens :
      {z : MvPolynomial (Fin d) k |
        ∃ j : Fin d, j < i ∧ z = (MvPolynomial.X j ^ c) ^ 8} =
      (fun m : Fin d →₀ ℕ => MvPolynomial.monomial m (1 : k)) '' G := by
    ext z
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨Finsupp.single j (c * 8), ?_, ?_⟩
      · exact ⟨⟨j.val, hj⟩, rfl⟩
      · calc
          MvPolynomial.monomial (Finsupp.single j (c * 8)) (1 : k) =
              MvPolynomial.X j ^ (c * 8) := by rw [MvPolynomial.X_pow_eq_monomial]
          _ = (MvPolynomial.X j ^ c) ^ 8 := by rw [pow_mul]
    · rintro ⟨m, ⟨j, rfl⟩, rfl⟩
      refine ⟨j.castLE (Nat.le_of_lt i.isLt), j.isLt, ?_⟩
      calc
        MvPolynomial.monomial
            (Finsupp.single (j.castLE (Nat.le_of_lt i.isLt)) (c * 8)) (1 : k) =
            MvPolynomial.X (j.castLE (Nat.le_of_lt i.isLt)) ^ (c * 8) := by
          rw [MvPolynomial.X_pow_eq_monomial]
        _ = (MvPolynomial.X (j.castLE (Nat.le_of_lt i.isLt)) ^ c) ^ 8 := by
          rw [pow_mul]
  rw [eighthPowerPrefixIdeal, hgens,
    MvPolynomial.mem_ideal_span_monomial_image]
  simp only [G, Set.mem_range]
  constructor
  · intro h m hm
    obtain ⟨e, he, hem⟩ := h m hm
    obtain ⟨j, rfl⟩ := he
    refine ⟨j, ?_⟩
    exact (Finsupp.single_le_iff).mp hem
  · intro h m hm
    obtain ⟨j, hj⟩ := h m hm
    refine ⟨Finsupp.single (j.castLE (Nat.le_of_lt i.isLt)) (c * 8), ?_, ?_⟩
    · exact ⟨j, rfl⟩
    · exact (Finsupp.single_le_iff).mpr hj

private lemma mul_X_pow_mem_parameter_prefix_cancel
    {k : Type u} [Field k] {d c : ℕ} (i : Fin d) (p : MvPolynomial (Fin d) k)
    (hp : p * MvPolynomial.X i ^ c ∈
      eighthPowerPrefixIdeal (fun j : Fin d => MvPolynomial.X j ^ c) i) :
    p ∈ eighthPowerPrefixIdeal (fun j : Fin d => MvPolynomial.X j ^ c) i := by
  classical
  rw [mem_parameter_prefix_iff_support] at hp ⊢
  have hsupp : (p * MvPolynomial.X i ^ c).support =
      p.support.map (addRightEmbedding (Finsupp.single i c)) := by
    rw [MvPolynomial.X_pow_eq_monomial]
    exact AddMonoidAlgebra.support_coeff_mul_single p 1 (by simp)
      (Finsupp.single i c)
  intro m hm
  have hm' : m + Finsupp.single i c ∈ (p * MvPolynomial.X i ^ c).support := by
    rw [hsupp]
    exact Finset.mem_map.mpr ⟨m, hm, rfl⟩
  obtain ⟨j, hj⟩ := hp (m + Finsupp.single i c) hm'
  refine ⟨j, ?_⟩
  have hji : (j.castLE (Nat.le_of_lt i.isLt)) ≠ i := by
    intro h
    exact (Nat.ne_of_lt j.isLt) (congrArg Fin.val h)
  simpa [Finsupp.add_apply, Finsupp.single_apply, hji] using hj

private lemma parameter_prefix_ann_stable
    {k : Type u} [Field k] {d c : ℕ} (i : Fin d)
    (x : MvPolynomial (Fin d) k ⧸
      eighthPowerPrefixIdeal (fun j : Fin d => MvPolynomial.X j ^ c) i) :
    x * Ideal.Quotient.mk _ (MvPolynomial.X i ^ c) = 0 ↔
      x * (Ideal.Quotient.mk _ (MvPolynomial.X i ^ c)) ^ 2 = 0 := by
  classical
  let I : Ideal (MvPolynomial (Fin d) k) :=
    eighthPowerPrefixIdeal (fun j : Fin d => MvPolynomial.X j ^ c) i
  have hregular (y : MvPolynomial (Fin d) k ⧸ I) :
      y * Ideal.Quotient.mk I (MvPolynomial.X i ^ c) = 0 → y = 0 := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    intro hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (mul_X_pow_mem_parameter_prefix_cancel i p
      (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_mul] using hy)))
  constructor
  · intro h
    simp [hregular x h]
  · intro h
    have hxy : (x * Ideal.Quotient.mk I (MvPolynomial.X i ^ c)) *
        Ideal.Quotient.mk I (MvPolynomial.X i ^ c) = 0 := by
      simpa [pow_two, mul_assoc] using h
    exact hregular (x * Ideal.Quotient.mk I (MvPolynomial.X i ^ c)) hxy

private lemma map_eighthPowerPrefixIdeal_eq_span
    {R Λ : Type*} [CommRing R] [CommRing Λ] [Algebra R Λ]
    {d : ℕ} (x : Fin d → R) (π : Fin d → Λ) (i : Fin d)
    (hx : ∀ j, algebraMap R Λ (x j) = π j) :
    Ideal.map (algebraMap R Λ) (eighthPowerPrefixIdeal x i) =
      Ideal.span (Set.range fun j : Fin i.val =>
        π (j.castLE (Nat.le_of_lt i.isLt)) ^ 8) := by
  classical
  rw [eighthPowerPrefixIdeal, Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨⟨j, hj⟩, ?_⟩
    simpa using (show algebraMap R Λ (x j ^ 8) = π j ^ 8 by rw [map_pow, hx]).symm
  · rintro ⟨j, rfl⟩
    refine ⟨x (j.castLE (Nat.le_of_lt i.isLt)) ^ 8,
      ⟨j.castLE (Nat.le_of_lt i.isLt), j.isLt, rfl⟩, ?_⟩
    rw [map_pow, hx]

private lemma map_eighthPowerIdeal_eq_span
    {R Λ : Type*} [CommRing R] [CommRing Λ] [Algebra R Λ]
    {d : ℕ} (x : Fin d → R) (π : Fin d → Λ)
    (hx : ∀ i, algebraMap R Λ (x i) = π i) :
    Ideal.map (algebraMap R Λ) (eighthPowerIdeal x) =
      Ideal.span (Set.range fun i => π i ^ 8) := by
  rw [eighthPowerIdeal, Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [map_pow, hx]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨x i ^ 8, ⟨i, rfl⟩, by rw [map_pow, hx]⟩

private lemma radical_span_range_pow
    {R ι : Type*} [CommSemiring R] (a : ι → R) {n : ℕ} (hn : 0 < n) :
    (Ideal.span (Set.range fun i => a i ^ n)).radical =
      (Ideal.span (Set.range a)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_of_mem (Ideal.span (Set.range a))
      (Ideal.subset_span ⟨i, rfl⟩) n hn
  · apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨n, Ideal.subset_span ⟨i, rfl⟩⟩

private lemma isNilpotent_map_span_range_of_pow_mem
    {R ι : Type*} [CommRing R] [Finite ι] (a : ι → R) (I : Ideal R)
    (n : ℕ) (ha : ∀ i, a i ^ n ∈ I) :
    IsNilpotent (Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range a))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply (Ideal.FG.isNilpotent_iff_le_nilradical
    (Submodule.fg_span (Set.finite_range _))).mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  show Ideal.Quotient.mk I (a i) ∈ nilradical (R ⧸ I)
  apply mem_nilradical.mpr
  refine ⟨n, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (ha i)

/-- `Λ` is a filtered colimit of smooth `R`-algebras: there is a filtered index category, a
diagram of smooth `R`-algebras over it, and a colimit of that diagram isomorphic to `Λ` as an
`R`-algebra. This is the property `PT` of Tag 07F1, with the base, the target and the index
allowed to live in three different universes. -/
def IsFilteredColimitOfSmooth (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] : Prop :=
  ∃ (I : Type t) (_ : SmallCategory I) (_ : IsFiltered I)
    (F : I ⥤ CommAlgCat.{t} R) (c : Cocone F),
      (∀ i, Algebra.Smooth R (F.obj i)) ∧
      Nonempty (IsColimit ((forget (CommAlgCat R)).mapCocone c)) ∧
      Nonempty (c.pt ≃ₐ[R] A)

private lemma isFilteredColimitOfSmooth_transport
    {R : Type u} {S : Type u'} {A : Type v} {B : Type v'}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (eR : R ≃+* S) (eA : A ≃+* B)
    (he : ∀ r, eA (algebraMap R A r) = algebraMap S B (eR r))
    (h : IsFilteredColimitOfSmooth.{u, v, t} R A) : IsFilteredColimitOfSmooth.{u', v', t} S B := by
  obtain ⟨I, hI, hfilt, F, c, hsmooth, ⟨hc⟩, ⟨e⟩⟩ := h
  let E : CommAlgCat.{t} R ⥤ CommAlgCat.{t} S :=
    { obj := fun X =>
        let : Algebra S X := ((algebraMap R X).comp eR.symm.toRingHom).toAlgebra
        CommAlgCat.of S X
      map := fun {X Y} f =>
        let : Algebra S X := ((algebraMap R X).comp eR.symm.toRingHom).toAlgebra
        let : Algebra S Y := ((algebraMap R Y).comp eR.symm.toRingHom).toAlgebra
        CommAlgCat.ofHom
        { toRingHom := f.hom.toRingHom
          commutes' := fun s => by
            show f.hom (algebraMap R X (eR.symm s)) =
              algebraMap R Y (eR.symm s)
            exact f.hom.commutes (eR.symm s) }
      map_id := by intro X; ext x; rfl
      map_comp := by intro X Y Z f g; ext x; rfl }
  refine ⟨I, hI, hfilt, F ⋙ E, E.mapCocone c, ?_, ?_, ?_⟩
  · intro i
    have hE : RingHom.Smooth eR.symm.toRingHom :=
      RingHom.Smooth.of_bijective eR.symm.bijective
    have hF : RingHom.Smooth (algebraMap R (F.obj i)) :=
      RingHom.smooth_algebraMap.mpr (hsmooth i)
    exact RingHom.smooth_algebraMap.mp (RingHom.Smooth.comp hE hF)
  · refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
    · intro x
      obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hc x
      refine ⟨i, a, ?_⟩
      show x = (c.ι.app i).hom a
      exact ha.symm
    · intro i j a b hab
      have hh : (c.ι.app i).hom a = (c.ι.app j).hom b := by
        change (c.ι.app i).hom a = (c.ι.app j).hom b at hab
        exact hab
      obtain ⟨k, f, g, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).mp hh
      refine ⟨k, f, g, ?_⟩
      show (F.map f).hom a = (F.map g).hom b
      exact hk
  · let e' : (E.mapCocone c).pt ≃ₐ[S] B :=
      { toRingEquiv := e.toRingEquiv.trans eA
        commutes' := fun s => by
          show eA (e (algebraMap R c.pt (eR.symm s))) = algebraMap S B s
          rw [e.commutes, he, eR.apply_symm_apply] }
    exact ⟨e'⟩

private lemma isFilteredColimitOfSmooth_of_algEquiv
    {R : Type u} {Λ Γ : Type v} [CommRing R] [CommRing Λ] [CommRing Γ]
    [Algebra R Λ] [Algebra R Γ] (e : Λ ≃ₐ[R] Γ)
    (h : IsFilteredColimitOfSmooth.{u, v, t} R Λ) :
    IsFilteredColimitOfSmooth.{u, v, t} R Γ := by
  obtain ⟨I, hI, hfilt, F, c, hsmooth, hc, ⟨e'⟩⟩ := h
  exact ⟨I, hI, hfilt, F, c, hsmooth, hc, ⟨e'.trans e⟩⟩

private theorem isSeparableExtension_of_ringEquiv_square
    {k k' : Type u} {K K' : Type v}
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k K] [Algebra k' K'] (e : k ≃+* k') (E : K ≃+* K')
    (he : ∀ a, E (algebraMap k K a) = algebraMap k' K' (e a))
    (hsep : Algebra.IsSeparableExtension k K) :
    Algebra.IsSeparableExtension k' K' := by
  let p := ringExpChar k
  have : ExpChar k' p := expChar_of_injective_ringHom
    (f := e.toRingHom) e.injective p
  have hpow := ((Algebra.isSeparableExtension_tfae k K p).out 1 2).mp hsep
  apply ((Algebra.isSeparableExtension_tfae k' K' p).out 2 1).mp
  intro s hs
  have hsmul (a : k) (x : K) : E (a • x) = e a • E x := by
    simp only [Algebra.smul_def, map_mul, he]
  have hsmul' (a : k') (x : K') : E.symm (a • x) = e.symm a • E.symm x := by
    apply E.injective
    rw [E.apply_symm_apply, hsmul, e.apply_symm_apply, E.apply_symm_apply]
  have hs' : LinearIndependent k (fun x : s => E.symm x.1) :=
    hs.map_of_surjective_injectiveₛ e.symm E.symm.toAddMonoidHom
      e.symm.surjective E.symm.injective hsmul'
  have hp' : LinearIndependent k (fun x : s => (E.symm x.1) ^ p) :=
    (linearIndepOn_range_iff hs'.injective (· ^ p)).mp
      (hpow _ hs'.linearIndepOn_id)
  have hh := hp'.map_of_surjective_injectiveₛ e E.toAddMonoidHom
    e.surjective E.injective hsmul
  change LinearIndependent k' (fun x : s => E (E.symm x.1 ^ p)) at hh
  show LinearIndependent k' (fun x : s => x.1 ^ p)
  simpa only [map_pow, E.apply_symm_apply] using hh

private lemma isFilteredColimitOfSmooth_of_isSeparableExtension
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparableExtension k K] :
    IsFilteredColimitOfSmooth.{u, v, max u v} k K := by
  classical
  obtain ⟨hdir, hcover⟩ := Subalgebra.directedOn_smooth_and_exists_mem k K
  let I := ULift.{u} {A : Subalgebra k K // Algebra.Smooth k A}
  have : Nonempty I := by
    obtain ⟨A, hA, _⟩ := hcover 0
    exact ⟨⟨⟨A, hA⟩⟩⟩
  have : IsDirectedOrder I := ⟨fun A B => by
    obtain ⟨C, hC, hAC, hBC⟩ := hdir A.down.1 A.down.2 B.down.1 B.down.2
    exact ⟨⟨⟨C, hC⟩⟩, hAC, hBC⟩⟩
  let F : I ⥤ CommAlgCat.{max u v} k :=
    { obj := fun A => CommAlgCat.of k (ULift.{u} A.down.1)
      map := fun {A B} f => CommAlgCat.ofHom
        (ULift.algEquiv.symm.toAlgHom.comp
          ((Subalgebra.inclusion (show A.down.1 ≤ B.down.1 from
            (leOfHom f : A ≤ B))).comp ULift.algEquiv.toAlgHom)) }
  let c : Cocone F :=
    { pt := CommAlgCat.of k (ULift.{u} K)
      ι :=
        { app := fun A => CommAlgCat.ofHom
            (ULift.algEquiv.symm.toAlgHom.comp
              (A.down.1.val.comp ULift.algEquiv.toAlgHom))
          naturality := fun _ _ _ => by ext; rfl } }
  refine ⟨I, inferInstance, inferInstance, F, c, ?_, ?_, ⟨ULift.algEquiv⟩⟩
  · intro A
    let := A.down.2
    exact Algebra.Smooth.of_equiv (ULift.algEquiv.symm : A.down.1 ≃ₐ[k] ULift.{u} A.down.1)
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro x
    obtain ⟨A, hA, hx⟩ := hcover x.down
    exact ⟨⟨⟨A, hA⟩⟩, ⟨⟨x.down, hx⟩⟩, rfl⟩
  · intro A B a b hab
    obtain ⟨C, hC, hAC, hBC⟩ := hdir A.down.1 A.down.2 B.down.1 B.down.2
    refine ⟨⟨⟨C, hC⟩⟩, homOfLE (show A ≤ (⟨⟨C, hC⟩⟩ : I) from hAC),
      homOfLE (show B ≤ (⟨⟨C, hC⟩⟩ : I) from hBC), ?_⟩
    exact ULift.ext _ _ (Subtype.ext (congrArg ULift.down hab))

private lemma isFilteredColimitOfSmooth_localization_of_dim_zero
    {k : Type u} {Λ : Type v} [Field k] [CommRing Λ] [Algebra k Λ]
    (q : Ideal Λ) [q.IsPrime] [IsRegularLocalRing (Localization.AtPrime q)]
    [Algebra.IsSeparableExtension k q.ResidueField]
    (hd : ringKrullDim (Localization.AtPrime q) = 0) :
    IsFilteredColimitOfSmooth.{u, v, max u v} k (Localization.AtPrime q) := by
  let L := Localization.AtPrime q
  have : Ring.KrullDimLE 0 L := Ring.krullDimLE_iff.mpr hd.le
  have : IsDomain L := IsRegularLocalRing.isDomain L
  let : Field L := (Ring.KrullDimLE.isField_of_isDomain (R := L)).toField
  let f : L →ₐ[k] q.ResidueField := IsScalarTower.toAlgHom k L q.ResidueField
  let e : L ≃ₐ[k] q.ResidueField := AlgEquiv.ofBijective f
    ⟨f.injective, fun x => Ideal.Quotient.mk_surjective x⟩
  exact isFilteredColimitOfSmooth_of_algEquiv e.symm
    (isFilteredColimitOfSmooth_of_isSeparableExtension k q.ResidueField)

private lemma exists_smooth_factorization_of_isFilteredColimitOfSmooth
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]
    (f : A →ₐ[R] Λ) (hPT : IsFilteredColimitOfSmooth.{u, w, max u w} R Λ) :
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : Algebra R D),
      Algebra.Smooth R D ∧ ∃ (g : A →ₐ[R] D) (h : D →ₐ[R] Λ), h.comp g = f := by
  classical
  obtain ⟨I, _, _, F, c, hsmooth, ⟨hc⟩, ⟨e⟩⟩ := hPT
  let R' := ULift.{max v w} R
  let A' := ULift.{max u w} A
  let F' : I ⥤ CommRingCat.{max u v w} :=
    { obj := fun i => CommRingCat.of (ULift.{max v w} (F.obj i))
      map := fun h => CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((F.map h).hom.toRingHom.comp ULift.ringEquiv.toRingHom)) }
  let c' : Cocone F' :=
    { pt := CommRingCat.of (ULift.{max v w} c.pt)
      ι :=
        { app := fun i => CommRingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp
              ((c.ι.app i).hom.toRingHom.comp ULift.ringEquiv.toRingHom))
          naturality := fun i j h => by
            ext x
            exact congrArg ULift.up (congrArg (fun f => f.hom x.down) (c.w h)) } }
  have hc' : IsColimit ((forget CommRingCat).mapCocone c') := by
    apply Types.FilteredColimit.isColimitOf _ _
    · intro x
      obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hc x.down
      exact ⟨i, ULift.up a, congrArg ULift.up ha.symm⟩
    · intro i j a b hab
      obtain ⟨l, hil, hjl, h⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hc).mp (congrArg ULift.down hab)
      exact ⟨l, hil, hjl, congrArg ULift.up h⟩
  have : PreservesFilteredColimitsOfSize.{max u w, max u w}
      (forget CommRingCat.{max u v w}) :=
    preservesFilteredColimitsOfSize_shrink.{max u w, max v w, max u w, max v w} _
  let : HasColimitsOfSize.{max u w, max u w} CommRingCat.{max u v w} :=
    hasColimitsOfSizeShrink.{max u w, max u w, max v w, max v w} _
  let : ReflectsColimit F' (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms F' (forget CommRingCat)
  have hcRing : IsColimit c' := isColimitOfReflects (forget CommRingCat) hc'
  let p : CommRingCat.of R' ⟶ CommRingCat.of A' := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((algebraMap R A).comp ULift.ringEquiv.toRingHom))
  let α : (Functor.const I).obj (CommRingCat.of R') ⟶ F' :=
    { app := fun i => CommRingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((algebraMap R (F.obj i)).comp ULift.ringEquiv.toRingHom))
      naturality := fun i j h => by
        ext x
        exact ((F.map h).hom.commutes x.down).symm }
  let f' : CommRingCat.of A' ⟶ c'.pt := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.comp f.toRingHom).comp ULift.ringEquiv.toRingHom))
  have hp : p.hom.FinitePresentation :=
    (RingHom.FinitePresentation.of_bijective ULift.ringEquiv.symm.bijective).comp
      ((RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
        (RingHom.FinitePresentation.of_bijective ULift.ringEquiv.bijective))
  have hbase (i : I) : p ≫ f' = α.app i ≫ c'.ι.app i := by
    ext x
    show e.symm (f (algebraMap R A x.down)) =
      (c.ι.app i).hom (algebraMap R (F.obj i) x.down)
    rw [f.commutes, e.symm.commutes, (c.ι.app i).hom.commutes]
    rfl
  obtain ⟨i, g', hgBase, hgFact⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (CommRingCat.of R') F' α p c' hcRing hp f' hbase
  let D := ULift.{max v w} (F.obj i)
  let g : A →ₐ[R] D :=
    { g'.hom.comp ULift.ringEquiv.symm.toRingHom with
      commutes' := fun r => congrArg (fun h => h (ULift.up r)) hgBase }
  let h : D →ₐ[R] Λ :=
    e.toAlgHom.comp ((c.ι.app i).hom.comp ULift.algEquiv.toAlgHom)
  have := hsmooth i
  refine ⟨D, inferInstance, inferInstance,
    Algebra.Smooth.of_equiv (ULift.algEquiv.symm : (F.obj i) ≃ₐ[R] D), g, h, ?_⟩
  ext a
  have hf := congrArg (fun h => (h (ULift.up a)).down) hgFact
  show e ((c.ι.app i).hom (g' (ULift.up a)).down) = f a
  exact (congrArg e hf).symm.trans (e.apply_symm_apply (f a))

/-- A filtered colimit of smooth algebras in the `CommAlgCat` spelling is one in the
`Under (CommRingCat.of R)` spelling: by Tag 07C3 the latter is the property that every map from
an algebra of finite presentation factors through a smooth algebra. -/
private lemma indSmoothUnder_of_isFilteredColimitOfSmooth {R Λ : Type u} [CommRing R]
    [CommRing Λ] [Algebra R Λ] (h : IsFilteredColimitOfSmooth.{u, u, u} R Λ) :
    IndSmooth R Λ := by
  refine (CommRingCat.ind_under_iff_exists_factorization _
    (fun _ hB ↦ RingHom.Smooth.finitePresentation hB)).2 ?_
  intro A hA f
  let : Algebra R A.right := A.hom.hom.toAlgebra
  have : Algebra.FinitePresentation R A.right :=
    RingHom.finitePresentation_algebraMap.mp hA
  let f' : A.right →ₐ[R] Λ :=
    { f.right.hom with
      commutes' := fun r =>
        congrArg (fun z : CommRingCat.of R ⟶ CommRingCat.of Λ ↦ z.hom r) f.w }
  obtain ⟨D, hD, hRD, hsm, g, k, hcomp⟩ :=
    exists_smooth_factorization_of_isFilteredColimitOfSmooth f' h
  let := hD
  let := hRD
  refine ⟨Under.mk (CommRingCat.ofHom (algebraMap R D)),
    Under.homMk (CommRingCat.ofHom g.toRingHom) ?_,
    Under.homMk (CommRingCat.ofHom k.toRingHom) ?_, ?_, ?_⟩
  · exact CommRingCat.hom_ext (RingHom.ext fun r => g.commutes r)
  · exact CommRingCat.hom_ext (RingHom.ext fun r => k.commutes r)
  · exact Under.UnderMorphism.ext
      (CommRingCat.hom_ext (RingHom.ext fun a => AlgHom.congr_fun hcomp a))
  · show (algebraMap R D).Smooth
    exact RingHom.smooth_algebraMap.mpr hsm

/-- Conversely, the `Under (CommRingCat.of R)` spelling gives the `CommAlgCat` one: the
equivalence `CommAlgCat R ≌ Under (CommRingCat.of R)` carries a colimit presentation, and the
colimit remains one of underlying types because both forgetful functors preserve filtered
colimits. -/
private lemma isFilteredColimitOfSmooth_of_indSmoothUnder {R Λ : Type u} [CommRing R]
    [CommRing Λ] [Algebra R Λ] (h : IndSmooth R Λ) :
    IsFilteredColimitOfSmooth.{u, u, u} R Λ := by
  obtain ⟨J, _, _, pres, hp⟩ := h
  let E := commAlgCatEquivUnder (CommRingCat.of R)
  refine ⟨J, inferInstance, inferInstance, pres.diag ⋙ E.inverse,
    E.inverse.mapCocone pres.cocone, fun j => RingHom.smooth_algebraMap.mp (hp j), ?_, ?_⟩
  · exact ⟨isColimitOfPreserves
      (Under.forget (CommRingCat.of R) ⋙ forget CommRingCat) pres.isColimit⟩
  · exact ⟨CommAlgCat.algEquivOfIso (E.unitIso.app (CommAlgCat.of R Λ)).symm⟩

/-- **Stacks 07CM across universes.** If `I ⊂ R` is nilpotent, `S` is flat over `R` and `S/IS`
is a filtered colimit of smooth `R/I`-algebras, then `S` is a filtered colimit of smooth
`R`-algebras, with the base and the target in different universes. -/
private theorem isFilteredColimitOfSmooth_of_isNilpotent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : IsNilpotent I)
    (hres : IsFilteredColimitOfSmooth.{u, v, max u v} (R ⧸ I)
      (S ⧸ I.map (algebraMap R S)))
    (hflat : Module.Flat R S) :
    IsFilteredColimitOfSmooth.{u, v, max u v} R S := by
  let R' := ULift.{v} R
  let S' := ULift.{u} S
  let eR : R ≃+* R' := ULift.ringEquiv.symm
  let eS : S ≃+* S' := ULift.ringEquiv.symm
  let : Algebra R' S' :=
    ((eS.toRingHom.comp (algebraMap R S)).comp eR.symm.toRingHom).toAlgebra
  let I' : Ideal R' := I.map (eR : R →+* R')
  let J : Ideal S := I.map (algebraMap R S)
  let J' : Ideal S' := I'.map (algebraMap R' S')
  have hI' : IsNilpotent I' := by
    obtain ⟨n, hn⟩ := hI
    exact ⟨n, by rw [← Ideal.map_pow, hn]; simp⟩
  have hJ' : J' = J.map (eS : S →+* S') := by
    dsimp [J', J, I']
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  let eRq : (R ⧸ I) ≃+* (R' ⧸ I') :=
    Ideal.quotientEquiv I I' eR rfl
  let eSq : (S ⧸ J) ≃+* (S' ⧸ J') :=
    Ideal.quotientEquiv J J' eS hJ'
  let : Algebra (R' ⧸ I') (S' ⧸ J') :=
    Ideal.Quotient.algebraQuotientMapQuotient
  have hcompat (x : R ⧸ I) :
      eSq (algebraMap (R ⧸ I) (S ⧸ J) x) =
        algebraMap (R' ⧸ I') (S' ⧸ J') (eRq x) := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    show (Ideal.quotientEquiv J J' eS hJ')
      (Ideal.Quotient.mk J (algebraMap R S r)) =
      algebraMap (R' ⧸ I') (S' ⧸ J')
        ((Ideal.quotientEquiv I I' eR rfl) (Ideal.Quotient.mk I r))
    rw [Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk,
      Ideal.Quotient.algebraMap_quotient_map_quotient]
    rfl
  have hres' : IsFilteredColimitOfSmooth.{max u v, max u v, max u v} (R' ⧸ I') (S' ⧸ J') :=
    isFilteredColimitOfSmooth_transport eRq eSq hcompat hres
  let : Module R' S' := Algebra.toModule
  have hflat' : Module.Flat R' S' := by
    have h₁ : eR.symm.toRingHom.Flat := RingHom.Flat.of_bijective eR.symm.bijective
    have h₂ : (algebraMap R S).Flat := RingHom.flat_algebraMap_iff.mpr hflat
    have h₃ : eS.toRingHom.Flat := RingHom.Flat.of_bijective eS.bijective
    exact RingHom.flat_algebraMap_iff.mp ((h₁.comp h₂).comp h₃)
  have : Module.Flat R' S' := hflat'
  have hpt' : IsFilteredColimitOfSmooth.{max u v, max u v, max u v} R' S' :=
    isFilteredColimitOfSmooth_of_indSmoothUnder
      (ind_smooth_of_isNilpotent I' hI'
        (indSmoothUnder_of_isFilteredColimitOfSmooth hres'))
  have hcompat' (x : R') :
      eS.symm (algebraMap R' S' x) =
        algebraMap R S (eR.symm x) := by
    rfl
  exact isFilteredColimitOfSmooth_transport eR.symm eS.symm hcompat' hpt'

private lemma canBeResolved_of_isFilteredColimitOfSmooth
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]
    [Algebra.FinitePresentation R A] (q : Ideal Λ) [q.IsPrime]
    (hPT : IsFilteredColimitOfSmooth.{u, w, max u w} R Λ) :
    CanBeResolved R A Λ q := by
  let f := IsScalarTower.toAlgHom R A Λ
  obtain ⟨D, hD, hRD, hsmooth, g, h, hcomp⟩ :=
    exists_smooth_factorization_of_isFilteredColimitOfSmooth.{u, v, w} f hPT
  let := hD
  let := hRD
  let := hsmooth
  let : Algebra A D := g.toRingHom.toAlgebra
  let : Algebra D Λ := h.toRingHom.toAlgebra
  have : IsScalarTower R A D :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := A) (A := D)
      (fun x => (g.commutes x).symm)
  have : IsScalarTower R D Λ :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := D) (A := Λ)
      (fun x => (h.commutes x).symm)
  have : IsScalarTower A D Λ :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := D) (A := Λ)
      (fun x => (AlgHom.congr_fun hcomp x).symm)
  have htop : Stacks.Smoothing.singularIdeal R D = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
    exact mem_singularIdeal_of_smooth_away
      (Algebra.Smooth.localization_away (R := R) (S := D) 1)
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [htop, Ideal.map_top, Ideal.radical_top]
    exact le_top
  · rw [htop, Ideal.map_top, Ideal.radical_top]
    exact fun hle => Ideal.IsPrime.ne_top (inferInstance : q.IsPrime) (top_unique hle)

private lemma canBeResolved_of_isFilteredColimitOfSmooth_localization
    (R : Type u) (A : Type v) (Λ : Type w)
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [Algebra A Λ]
    [IsScalarTower R A Λ] [IsNoetherianRing R]
    [Algebra.FinitePresentation R A] (q : Ideal Λ) [q.IsPrime]
    (hq : q ∈ (Ideal.map (algebraMap A Λ)
      (Stacks.Smoothing.singularIdeal R A)).radical.minimalPrimes)
    (hd : ringKrullDim (Localization.AtPrime q) = 0)
    (hunit : ∀ x : R, x ∉ q.comap (algebraMap R Λ) → IsUnit x)
    (hPT : IsFilteredColimitOfSmooth.{u, w, max u w} R (Localization.AtPrime q)) :
    CanBeResolved R A Λ q := by
  let S : LocalSmoothingSituation.{u, v, w} :=
    { R := R, A := A, Λ := Λ, q := q }
  refine Stacks.Smoothing.canBeResolved_of_localization_dim_zero S hq
    (show S.IsResolvableAfterLocalizing from ?_) hd
  let p : Ideal R := q.comap (algebraMap R Λ)
  have hp : p.primeCompl ≤ IsUnit.submonoid R := by
    intro x hx
    exact hunit x hx
  have hloc : IsLocalization p.primeCompl R := IsLocalization.of_le_isUnit hp
  have hlocA : IsLocalization (p.primeCompl.map (algebraMap R A)) A := by
    apply IsLocalization.of_le_isUnit
    rintro _ ⟨x, hx, rfl⟩
    exact (hp hx).map (algebraMap R A)
  refine ⟨R, inferInstance, inferInstance, hloc,
    A, inferInstance, inferInstance, inferInstance, inferInstance,
    hlocA, inferInstance, inferInstance,
    Localization.AtPrime q, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact canBeResolved_of_isFilteredColimitOfSmooth _ hPT

private lemma canBeResolved_of_isRegularLocalRing_dim_zero
    (k : Type u) (A : Type v) (Λ : Type w)
    [Field k] [CommRing A] [CommRing Λ]
    [Algebra k A] [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ]
    [Algebra.FinitePresentation k A] (q : Ideal Λ) [q.IsPrime]
    (hq : (Ideal.map (algebraMap A Λ)
      (Stacks.Smoothing.singularIdeal k A)).radical.IsMinimalPrime q)
    [IsRegularLocalRing (Localization.AtPrime q)]
    [Algebra.IsSeparableExtension k q.ResidueField]
    (hd : ringKrullDim (Localization.AtPrime q) = 0) :
    CanBeResolved k A Λ q :=
  canBeResolved_of_isFilteredColimitOfSmooth_localization k A Λ q hq hd
    (fun _ hx => isUnit_iff_ne_zero.mpr fun h0 => hx (h0 ▸ Ideal.zero_mem _))
    (isFilteredColimitOfSmooth_localization_of_dim_zero q hd)

end Stacks.Smoothing

end
