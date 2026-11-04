module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.HartshorneLichtenbaumVanishing.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.UniverseChange
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.Ideal.SymbolicPower
public import
  StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.DualizingComplexVanishing
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.Jacobson
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.RestrictScalars
public import StacksFrontier.RingTheory.LocalCohomology.TopLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.TorsionColimit

/-!
# Hartshorne–Lichtenbaum vanishing from a condition on the completion

Let `A` be a Noetherian local ring with completion `A^∧` and let `I ⊆ A` be an ideal such that
`dim V(I A^∧ + 𝔭) ≥ 1` for every minimal prime `𝔭 ⊆ A^∧` of dimension `dim(A)`. Then the
cohomological dimension of `I` in `A` is strictly less than `dim(A)`.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_lt_of_minimalPrimes_adicCompletion` —
  Hartshorne–Lichtenbaum vanishing: the condition on the completion bounds the cohomological
  dimension of `I` strictly by `dim(A)`.
* `Stacks.LocalCohomology.cohomologicalDimension_lt_of_minimalPrimes_of_isAdicComplete` — the
  same statement for a ring that is already complete, where the condition is read on `A` itself.

## References

* [Stacks Project, Tag 0EB6](https://stacks.math.columbia.edu/tag/0EB6)
* [Stacks Project, Tag 0EB1](https://stacks.math.columbia.edu/tag/0EB1)
* [Stacks Project, Tag 0EB2](https://stacks.math.columbia.edu/tag/0EB2)
* [Stacks Project, Tag 0EB4](https://stacks.math.columbia.edu/tag/0EB4)
* [Stacks Project, Tag 0EB5](https://stacks.math.columbia.edu/tag/0EB5)
* [Stacks Project, Tag 0BJB](https://stacks.math.columbia.edu/tag/0BJB)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
* [Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Dualizing (localCohomology quotientPowerSucc extPowers)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-! ### The Ext description of local cohomology in the coreflection model -/

/-- Over a Noetherian ring the coreflection model of local cohomology agrees in every degree
with the termwise-torsion model, by the comparison of Stacks 0955. -/
private def localCohomologyDerivedHomologyIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (K : DerivedCategory (ModuleCat.{u} A)) (q : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((localCohomologyDerived A I hI).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (localCohomology A I K) := by
  have := isIso_compareSectionsWithSupportLocalCohomology_app.{u, 0} A I hI K
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).mapIso
      (asIso ((compareSectionsWithSupportLocalCohomology.{u, 0} A I hI).app K))).symm ≪≫
    localCohomologyWithSupportInHomologyIso A I K q

/-- Vanishing of the colimit of the Ext system of Stacks 0954 gives vanishing of local cohomology
in the coreflection model. -/
private theorem isZero_homology_localCohomologyDerived_of_isZero_colimit
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{u} A)) (q : ℤ)
    (h : IsZero (colimit (extPowers A I K q))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
      ((localCohomologyDerived A I hI).obj K)) := by
  have hlift : IsZero ((ModuleCat.uliftFunctor.{u + 1} A).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (localCohomology A I K))) :=
    IsZero.of_iso h (localCohomologyHomologyIsoColimitExt A I K q)
  rw [ModuleCat.isZero_iff_subsingleton] at hlift
  refine IsZero.of_iso ?_ (localCohomologyDerivedHomologyIso A I hI K q)
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => ?_⟩
  exact congrArg ULift.down (hlift.allEq ⟨x⟩ ⟨y⟩)

/-! ### A colimit over `ℕ` with vanishing transition maps -/

/-- A sequential colimit vanishes as soon as every object admits a later one to which it maps by
the zero map. -/
private theorem isZero_colimit_of_forall_exists_map_eq_zero
    {A : Type u} [CommRing A] (F : ℕ ⥤ ModuleCat.{u + 1} A) [HasColimit F]
    (h : ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m, F.map (homOfLE hnm) = 0) :
    IsZero (colimit F) := by
  rw [IsZero.iff_id_eq_zero]
  refine colimit.hom_ext fun n ↦ ?_
  obtain ⟨m, hnm, hmap⟩ := h n
  rw [← colimit.w F (homOfLE hnm), hmap]
  simp

/-- The transition map of the Ext system of Stacks 0954 from `n` to `j` is precomposition with
the quotient map `A/Iʲ → A/Iⁿ`. -/
private lemma extPowers_map_apply
    {A : Type u} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A)) (q : ℤ)
    {n j : ℕ} (h : n ≤ j)
    (x : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ I ^ n))) K q) :
    (extPowers A I K q).map (homOfLE h) x =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom
          (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (I := I) h)).toLinearMap) ≫ x := by
  induction j, h using Nat.le_induction with
  | base =>
      have hid : ModuleCat.ofHom
          (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (I := I) (le_refl n))).toLinearMap =
          𝟙 (ModuleCat.of A (A ⧸ I ^ n)) := by
        refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        rfl
      rw [show homOfLE (le_refl n) = 𝟙 n from Subsingleton.elim _ _, hid,
        CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
  | succ j hnj ih =>
      have hstep : quotientPowerSucc A I j ≫
            ModuleCat.ofHom
              (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (I := I) hnj)).toLinearMap =
          ModuleCat.ofHom (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (I := I) (hnj.trans (Nat.le_succ j)))).toLinearMap := by
        refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        rfl
      have hcomp : homOfLE (show n ≤ j + 1 from hnj.trans (Nat.le_succ j)) =
          homOfLE hnj ≫ homOfLE (Nat.le_succ j) := Subsingleton.elim _ _
      have hmapeq : (extPowers A I K q).map (homOfLE (Nat.le_succ j)) =
          ModuleCat.ofHom
            { toFun := fun z : DerivedCategory.Ext
                  ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                    (ModuleCat.of A (A ⧸ I ^ j))) K q =>
                (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
                  (quotientPowerSucc A I j) ≫ z
              map_add' := fun z w => by simp
              map_smul' := fun r z => by simp } :=
        Functor.ofSequence_map_homOfLE_succ _ j
      have hsucc : ∀ y : DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A (A ⧸ I ^ j))) K q,
          (extPowers A I K q).map (homOfLE (Nat.le_succ j)) y =
            (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
              (quotientPowerSucc A I j) ≫ y := by
        intro y
        rw [hmapeq]
        rfl
      rw [hcomp, CategoryTheory.Functor.map_comp]
      have hone : ((extPowers A I K q).map (homOfLE hnj) ≫
            (extPowers A I K q).map (homOfLE (Nat.le_succ j))) x =
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (quotientPowerSucc A I j) ≫
            ((extPowers A I K q).map (homOfLE hnj) x) :=
        (ModuleCat.comp_apply _ _ _).trans (hsucc _)
      rw [hone, ih, ← Category.assoc, ← CategoryTheory.Functor.map_comp, hstep]

/-! ### Positive depth of the quotients by the symbolic powers -/

/-- In a Noetherian local ring the associated primes of the quotient by a positive symbolic power
of a prime `p` are exactly `{p}`. -/
private theorem associatedPrimes_quotient_symbolicPower
    (A : Type u) [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (n : ℕ) (hn : n ≠ 0) :
    associatedPrimes A (A ⧸ Ideal.symbolicPower p n) = {p} := by
  rw [Ideal.symbolicPower_eq_symbolicPower',
    associatedPrimes.eq_singleton_of_isPrimary (symbolicPower_isPrimary p n hn),
    symbolicPower_radical p n hn]

/-- The quotient by a positive symbolic power of a prime of dimension one has positive depth. -/
private theorem depth_quotient_symbolicPower_pos
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (hp : ringKrullDim (A ⧸ p) = 1) :
    0 < Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.symbolicPower p n) := by
  classical
  set M := A ⧸ Ideal.symbolicPower p n with hM
  set m := IsLocalRing.maximalIdeal A with hm
  have hass : associatedPrimes A M = {p} := associatedPrimes_quotient_symbolicPower A p n hn
  have hpm : p ≠ m := by
    intro h
    let : Field (A ⧸ m) := Ideal.Quotient.field m
    have hzero : ringKrullDim (A ⧸ p) = 0 := h ▸ ringKrullDim_eq_zero_of_field (A ⧸ m)
    norm_num [hzero] at hp
  have hnot : ∀ q ∈ associatedPrimes A M, ¬ m ≤ q := by
    intro q hq hmq
    rw [hass, Set.mem_singleton_iff] at hq
    subst hq
    exact hpm (le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime q) hmq)
  obtain ⟨x, hxm, hxreg⟩ :=
    (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le m M
      (associatedPrimes.finite A M)).2 hnot
  have hweak : RingTheory.Sequence.IsWeaklyRegular M [x] := by
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
    exact ⟨hxreg, RingTheory.Sequence.IsWeaklyRegular.nil A (QuotSMulTop x M)⟩
  have hdep : (1 : ℕ∞) ≤ Module.depth A m M := by
    rw [Module.depth_eq_iSup_isWeaklyRegular_length]
    exact le_iSup_of_le [x] (le_iSup_of_le ⟨by simp [hxm], hweak⟩ (by simp))
  exact zero_lt_one.trans_le hdep

/-- The degree-zero Ext group into a normalized dualizing complex vanishes on the quotient by a
positive symbolic power of a prime of dimension one. -/
private theorem subsingleton_ext_quotient_symbolicPower
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (hp : ringKrullDim (A ⧸ p) = 1)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.symbolicPower p n))) K 0) := by
  set M := A ⧸ Ideal.symbolicPower p n with hM
  rw [← not_nontrivial_iff_subsingleton]
  intro hE
  have hle : (⨅ (i : ℕ) (_ : Nontrivial (Dualizing.moduleExtInto M K (-(i : ℤ)))),
      (i : ℕ∞)) ≤ 0 :=
    iInf_le_of_le 0 (iInf_le_of_le (by simpa [Dualizing.moduleExtInto] using hE) (by simp))
  rw [← Dualizing.depth_eq_iInf_nontrivial_moduleExtInto (A := A) (M := M) K hK] at hle
  exact absurd (depth_quotient_symbolicPower_pos A p n hn hp) (not_lt_of_ge hle)

/-! ### Degree-zero local cohomology at a prime of dimension one -/

/-- In a complete Noetherian local domain the Ext system of Stacks 0954 at a prime of dimension
one has vanishing colimit. -/
private theorem isZero_colimit_extPowers_of_dim_one_prime
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : Ideal A) [p.IsPrime] (hp : ringKrullDim (A ⧸ p) = 1)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) :
    IsZero (colimit (extPowers A p K 0)) := by
  classical
  refine isZero_colimit_of_forall_exists_map_eq_zero _ fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · refine ⟨0, le_refl 0, ?_⟩
    have hsingle : IsZero ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ p ^ (0 : ℕ)))) :=
      Functor.map_isZero _ (ModuleCat.isZero_iff_subsingleton.mpr (by simp [pow_zero]))
    exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ hsingle.eq_of_src _ _)
  · obtain ⟨m, hnm, hsym⟩ := Ideal.exists_symbolicPower_le_pow (A := A) p hp n hnpos
    have hmpos : m ≠ 0 := by omega
    have hsub := subsingleton_ext_quotient_symbolicPower A p m hmpos hp K hK
    have hpowsym : p ^ m ≤ Ideal.symbolicPower p m := by
      rw [Ideal.symbolicPower_eq_symbolicPower']
      exact pow_le_symbolicPower p m
    refine ⟨m, hnm, ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
    set S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
    set beta : ModuleCat.of A (A ⧸ p ^ m) ⟶ ModuleCat.of A (A ⧸ Ideal.symbolicPower p m) :=
      ModuleCat.ofHom (Ideal.Quotient.factorₐ A hpowsym).toLinearMap
    set alpha : ModuleCat.of A (A ⧸ Ideal.symbolicPower p m) ⟶ ModuleCat.of A (A ⧸ p ^ n) :=
      ModuleCat.ofHom (Ideal.Quotient.factorₐ A hsym).toLinearMap
    have hcomp : beta ≫ alpha =
        ModuleCat.ofHom (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (I := p) hnm)).toLinearMap := by
      refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      rfl
    rw [extPowers_map_apply p K 0 hnm x, ← hcomp, Functor.map_comp]
    calc (S.map beta ≫ S.map alpha) ≫ x
        = S.map beta ≫ (S.map alpha ≫ x) := Category.assoc _ _ _
      _ = S.map beta ≫ 0 := by rw [hsub.allEq (S.map alpha ≫ x) 0]
      _ = 0 := by simp

/-- In a complete Noetherian local domain the degree-zero local cohomology of a normalized
dualizing complex with support in a prime of dimension one vanishes. -/
private theorem isZero_homology_localCohomologyDerived_of_dim_one_prime
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : Ideal A) [p.IsPrime] (hp : ringKrullDim (A ⧸ p) = 1)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((localCohomologyDerived A p (Ideal.fg_of_isNoetherianRing p)).obj K)) :=
  isZero_homology_localCohomologyDerived_of_isZero_colimit A p
    (Ideal.fg_of_isNoetherianRing p) K 0
    (isZero_colimit_extPowers_of_dim_one_prime A p hp K hK)

/-! ### Finding a prime of dimension one over the ideal -/

/-- In a Noetherian local ring, an ideal whose quotient has dimension at least one is contained in
a prime whose quotient has dimension exactly one. -/
private theorem exists_isPrime_ringKrullDim_quotient_eq_one
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (I : Ideal A) (hI : (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ I)) :
    ∃ p : Ideal A, p.IsPrime ∧ I ≤ p ∧ ringKrullDim (A ⧸ p) = 1 := by
  classical
  have hItop : I ≠ ⊤ := by
    intro h
    have hsub : Subsingleton (A ⧸ I) := by rw [h]; infer_instance
    have hempty : IsEmpty (PrimeSpectrum (A ⧸ I)) :=
      PrimeSpectrum.isEmpty_iff_subsingleton.2 hsub
    have hdim : ringKrullDim (A ⧸ I) = ⊥ := by
      rw [ringKrullDim, Order.krullDim_eq_bot_iff]
      exact hempty
    rw [hdim] at hI
    norm_num at hI
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  let : IsLocalRing (A ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  set mQ := IsLocalRing.maximalIdeal (A ⧸ I) with hmQ
  let : mQ.IsPrime := (IsLocalRing.maximalIdeal.isMaximal (A ⧸ I)).isPrime
  have hheight : (1 : ℕ∞) ≤ mQ.height := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hI
    exact_mod_cast hI
  have hnotmin : ¬ Minimal Ideal.IsPrime mQ := by
    intro hmin
    have hz : mQ.height = 0 :=
      (Ideal.height_eq_zero_iff (I := mQ)).2 (by rwa [minimalPrimes_eq_minimals])
    norm_num [hz] at hheight
  obtain ⟨qQ, hqQlt, hqQprime⟩ :=
    exists_lt_of_not_minimal (show Ideal.IsPrime mQ from inferInstance) hnotmin
  set f : A →+* A ⧸ I := Ideal.Quotient.mk I with hf
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hmQmap : mQ = (IsLocalRing.maximalIdeal A).map f :=
    (IsLocalRing.map_maximalIdeal_of_surjective f hsurj).symm
  set p₀ : Ideal A := Ideal.comap f qQ with hp₀def
  have hp₀ : p₀.IsPrime := hqQprime.comap f
  have hIp₀ : I ≤ p₀ := fun x hx => by
    show f x ∈ qQ
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem qQ
  have hp₀lt : p₀ < IsLocalRing.maximalIdeal A := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p₀) fun heq => ?_
    refine hqQlt.ne ?_
    rw [← Ideal.map_comap_of_surjective f hsurj qQ, ← hp₀def, heq, ← hmQmap]
  set S : Set (Ideal A) := {r | r.IsPrime ∧ I ≤ r ∧ r < IsLocalRing.maximalIdeal A} with hSdef
  obtain ⟨p, hpS, hpmax⟩ := (wellFounded_gt (α := Ideal A)).has_min S ⟨p₀, hp₀, hIp₀, hp₀lt⟩
  obtain ⟨hp, hIp, hpm⟩ := hpS
  refine ⟨p, hp, hIp, ?_⟩
  let : Nontrivial (A ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  let : IsLocalRing (A ⧸ p) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  set g : A →+* A ⧸ p := Ideal.Quotient.mk p with hg
  have hgsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hmRmap : IsLocalRing.maximalIdeal (A ⧸ p) = (IsLocalRing.maximalIdeal A).map g :=
    (IsLocalRing.map_maximalIdeal_of_surjective g hgsurj).symm
  have hsimple : IsSimpleOrder (PrimeSpectrum (A ⧸ p)) := by
    have hbotne : (⊥ : PrimeSpectrum (A ⧸ p)) ≠ (⊤ : PrimeSpectrum (A ⧸ p)) := by
      intro heq
      have htop := congrArg PrimeSpectrum.asIdeal heq
      rw [PrimeSpectrum.asIdeal_bot, IsLocalRing.PrimeSpectrum.asIdeal_top] at htop
      obtain ⟨a, haM, hap⟩ := Set.not_subset.mp (not_le_of_gt hpm)
      have hga : g a ∈ (IsLocalRing.maximalIdeal A).map g := Ideal.mem_map_of_mem g haM
      rw [← hmRmap, ← htop] at hga
      exact hap (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hga))
    let : Nontrivial (PrimeSpectrum (A ⧸ p)) := ⟨⟨⊥, ⊤, hbotne⟩⟩
    refine IsSimpleOrder.of_forall_eq_top fun x hxb => ?_
    set r : Ideal A := Ideal.comap g x.asIdeal with hr
    have : x.asIdeal.IsPrime := x.isPrime
    have hrprime : r.IsPrime := x.isPrime.comap g
    have hpr : p ≤ r := fun a ha => by
      show g a ∈ x.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact Ideal.zero_mem x.asIdeal
    have hmap : r.map g = x.asIdeal := Ideal.map_comap_of_surjective g hgsurj x.asIdeal
    by_cases hrp : r = p
    · refine absurd (PrimeSpectrum.ext ?_) hxb
      rw [PrimeSpectrum.asIdeal_bot, ← hmap, hrp]
      exact Ideal.map_mk_eq_bot_of_le (le_rfl : p ≤ p)
    · have hplt : p < r := lt_of_le_of_ne hpr (fun heq => hrp heq.symm)
      have hrmax : r = IsLocalRing.maximalIdeal A := by
        by_contra hne
        exact hpmax r ⟨hrprime, hIp.trans hpr,
          lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime r) hne⟩ hplt
      refine PrimeSpectrum.ext ?_
      rw [← hmap, hrmax, IsLocalRing.PrimeSpectrum.asIdeal_top, ← hmRmap]
  rwa [ringKrullDim, Order.krullDim_eq_one_iff_of_boundedOrder]

/-! ### The complete local domain case -/

/-- **Hartshorne–Lichtenbaum vanishing over a complete local domain.** For a complete Noetherian
local domain `A` of dimension `d` and an ideal `I` with `dim(A/I) ≥ 1`, the cohomological
dimension of `I` is strictly less than `d`. -/
private theorem cohomologicalDimension_lt_of_isDomain
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) (I : Ideal A)
    (hI : (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ I)) :
    cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) < (d : ℤ) := by
  obtain ⟨p, hp, hIp, hpd⟩ := exists_isPrime_ringKrullDim_quotient_eq_one A I hI
  have : p.IsPrime := hp
  obtain ⟨ω, hω⟩ :=
    Dualizing.exists_isNormalizedDualizingComplex_of_isPrecomplete_maximalIdeal A
  have hωu : Dualizing.IsNormalizedDualizingComplex.{u, u} ω :=
    isNormalizedDualizingComplex_of_ulift_zero hω
  exact cohomologicalDimension_lt_of_le_of_le_jacobson A d hd I p hIp
    ((IsLocalRing.le_maximalIdeal_of_isPrime p).trans
      (IsLocalRing.ringJacobson_eq_maximalIdeal A).ge)
    (cohomologicalDimension_lt_of_isZero_homology_localCohomologyDerived A d hd ω hωu p
      (isZero_homology_localCohomologyDerived_of_dim_one_prime A p hpd ω hωu))

/-! ### The complete case -/

/-- The quotient of a complete Noetherian local ring by an ideal is complete for its own maximal
ideal. -/
private theorem isAdicComplete_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : Ideal A) [IsLocalRing (A ⧸ p)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (A ⧸ p)) (A ⧸ p) := by
  have hcomp : IsAdicComplete (IsLocalRing.maximalIdeal A) (A ⧸ p) :=
    isAdicComplete_of_iInf_smul_eq_bot _
      (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _
        (IsAdicComplete.le_jacobson_bot (IsLocalRing.maximalIdeal A)))
  have hmap : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p) =
      IsLocalRing.maximalIdeal (A ⧸ p) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← hmap, ← Ideal.Quotient.algebraMap_eq]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr hcomp

/-- **Hartshorne–Lichtenbaum vanishing over a complete local ring.** Let `A` be a complete
Noetherian local ring of dimension `d` and `I ⊆ A` an ideal with `dim V(I + 𝔭) ≥ 1` for every
minimal prime `𝔭` of dimension `d`. Then the cohomological dimension of `I` is less than `d`. -/
theorem cohomologicalDimension_lt_of_minimalPrimes_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) (I : Ideal A)
    (h : ∀ q : PrimeSpectrum A, IsMinimalPrime q.asIdeal →
      ringKrullDim (A ⧸ q.asIdeal) = (d : WithBot ℕ∞) →
      (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ (I + q.asIdeal))) :
    cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) < (d : ℤ) := by
  classical
  set hI := Ideal.fg_of_isNoetherianRing I with hIdef
  have hquot : ∀ q : PrimeSpectrum A,
      IsZero (localCohomologyModule A I hI (ModuleCat.of A (A ⧸ q.asIdeal)) (d : ℤ)) := by
    intro q
    have hqp : q.asIdeal.IsPrime := q.isPrime
    let : IsLocalRing (A ⧸ q.asIdeal) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    let : IsDomain (A ⧸ q.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).mpr q.isPrime
    by_cases htop : IsMinimalPrime q.asIdeal ∧
        ringKrullDim (A ⧸ q.asIdeal) = (d : WithBot ℕ∞)
    · have : IsAdicComplete (IsLocalRing.maximalIdeal (A ⧸ q.asIdeal)) (A ⧸ q.asIdeal) :=
        isAdicComplete_quotient A q.asIdeal
      have hpos : (1 : WithBot ℕ∞) ≤
          ringKrullDim ((A ⧸ q.asIdeal) ⧸ I.map (Ideal.Quotient.mk q.asIdeal)) := by
        refine le_trans (h q htop.1 htop.2) (le_of_eq ?_)
        rw [Ideal.add_eq_sup, sup_comm]
        exact (ringKrullDim_eq_of_ringEquiv
          (DoubleQuot.quotQuotEquivQuotSup q.asIdeal I)).symm
      have hcd := cohomologicalDimension_lt_of_isDomain (A ⧸ q.asIdeal) d htop.2
        (I.map (Ideal.Quotient.mk q.asIdeal)) hpos
      have hzero : IsZero (localCohomologyModule (A ⧸ q.asIdeal)
          (I.map (Ideal.Quotient.mk q.asIdeal)) (hI.map (Ideal.Quotient.mk q.asIdeal))
          (ModuleCat.of (A ⧸ q.asIdeal) (A ⧸ q.asIdeal)) (d : ℤ)) :=
        (isLocalCohomologyBound_cohomologicalDimension (A ⧸ q.asIdeal)
          (I.map (Ideal.Quotient.mk q.asIdeal))
          (hI.map (Ideal.Quotient.mk q.asIdeal))).2 (d : ℤ) (by simpa using hcd)
      have hrestr : IsZero ((ModuleCat.restrictScalars (Ideal.Quotient.mk q.asIdeal)).obj
          (localCohomologyModule (A ⧸ q.asIdeal) (I.map (Ideal.Quotient.mk q.asIdeal))
            (hI.map (Ideal.Quotient.mk q.asIdeal))
            (ModuleCat.of (A ⧸ q.asIdeal) (A ⧸ q.asIdeal)) (d : ℤ))) := by
        rwa [ModuleCat.isZero_iff_subsingleton] at hzero ⊢
      have hres := hrestr.of_iso (localCohomologyModuleRestrictScalarsIso
        (Ideal.Quotient.mk q.asIdeal) I hI
        (ModuleCat.of (A ⧸ q.asIdeal) (A ⧸ q.asIdeal)) (d : ℤ))
      rwa [ModuleCat.isZero_iff_subsingleton] at hres ⊢
    · have hav : ∀ r : PrimeSpectrum A, IsMinimalPrime r.asIdeal →
          ringKrullDim (A ⧸ r.asIdeal) = (d : WithBot ℕ∞) →
            r ∉ Module.support A (A ⧸ q.asIdeal) := by
        intro r hr hrd hrsupp
        have hpr : q.asIdeal ≤ r.asIdeal :=
          (PrimeSpectrum.mem_zeroLocus r (q.asIdeal : Set A)).mp
            (by simpa [Module.support_eq_zeroLocus, Ideal.annihilator_quotient] using hrsupp)
        have heq : q = r := PrimeSpectrum.ext (le_antisymm hpr (hr.2 ⟨q.isPrime, bot_le⟩ hpr))
        subst heq
        exact htop ⟨hr, hrd⟩
      refine localCohomologyModule_isZero_of_supportDim_lt.{u, u} A I hI _ (d : ℤ) ?_
      rw [Int.toNat_natCast]
      exact supportDim_lt_of_notMem_support_of_top_minimalPrimes A (A ⧸ q.asIdeal) d hd.le hav
  have hA : IsZero (localCohomologyModule A I hI (ModuleCat.of A A) (d : ℤ)) := by
    refine isZero_localCohomologyModule_of_isQuotientPrime A I hI d (ModuleCat.of A A)
      fun N _ r e ↦ ?_
    exact IsZero.of_iso (hquot r) <|
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (d : ℤ)).mapIso
        ((Dualizing.derivedPowerTorsionProperty A I hI).ι.mapIso
          ((Dualizing.localCohomologyFunctor A I hI).mapIso
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso e.toModuleIso)))
  refine cohomologicalDimension_lt_of_isZero_localCohomologyModule A d hd I
    (ModuleCat.of A A) ?_ hA
  intro r _ _
  rw [Module.support_eq_zeroLocus,
    Module.annihilator_eq_bot.2 (inferInstance : FaithfulSMul A A), PrimeSpectrum.zeroLocus_bot]
  trivial

/-! ### Hartshorne–Lichtenbaum vanishing -/

/-- **Hartshorne–Lichtenbaum vanishing.** Let `A` be a Noetherian
local ring with completion `A^∧` and let `I ⊆ A` be an ideal such that
`dim V(I A^∧ + 𝔭) ≥ 1` for every minimal prime `𝔭 ⊆ A^∧` of dimension `dim(A)`. Then the
cohomological dimension of `I` in `A` is strictly less than `dim(A)`. -/
@[stacks 0EB6]
theorem cohomologicalDimension_lt_of_minimalPrimes_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) (I : Ideal A)
    (h : ∀ q : PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A),
      IsMinimalPrime q.asIdeal →
      ringKrullDim ((AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ q.asIdeal) =
        (d : WithBot ℕ∞) →
      (1 : WithBot ℕ∞) ≤
        ringKrullDim ((AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸
          (I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) +
            q.asIdeal))) :
    cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) < (d : ℤ) := by
  set B := AdicCompletion (IsLocalRing.maximalIdeal A) A with hB
  set f : A →+* B := algebraMap A B with hf
  have hff : f.FaithfullyFlat := by
    show Module.FaithfullyFlat A B
    exact AdicCompletion.faithfullyFlat_of_le_ringJacobson (IsLocalRing.maximalIdeal A)
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have hdB : ringKrullDim B = (d : WithBot ℕ∞) :=
    (ringKrullDim_adicCompletion_maximalIdeal (A := A)).symm.trans hd
  have : IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact AdicCompletion.isAdicComplete_self (IsLocalRing.maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing _)
  rw [← cohomologicalDimension_map_eq_of_faithfullyFlat f hff I
    (Ideal.fg_of_isNoetherianRing I)]
  exact cohomologicalDimension_lt_of_minimalPrimes_of_isAdicComplete B d hdB (I.map f) h

end Stacks.LocalCohomology

end
