module

public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Dualizing.LocalizedExt
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernel
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FiniteTypeCriterion
import all StacksFrontier.RingTheory.Dualizing.LocalizedExt
import all StacksFrontier.RingTheory.LocalCompleteIntersection.FiniteTypeCriterion
import all StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernel

/-!
# Localizing the relative dualizing complex of a surjection

Let `R → A` be a surjective homomorphism of commutative rings with `R` Noetherian, and let
`g : R`.  Write `S = R_g` and `B = A_{f g}` for the localizations away from `g` and from its
image, so that `S → B` is again a surjection.  This file compares the derived localization of
`RHom_R(A, R)` along `A → B` with `RHom_S(B, S)`, and deduces that the first is the free module
of rank one in degree `c` as soon as the second is.

This is the statement that, in the local complete intersection case of [Stacks, Tag 0E4B],
replaces the compatibility of upper shriek with localization on the polynomial algebra, i.e. the
isomorphism assertion of [Stacks, Tag 0BZN]: that assertion is not available unconditionally,
whereas the comparison proved here is.  It is weaker — only the value at the unit is compared,
and no naturality is claimed — but it is all the invertibility statement needs.

Also proved here is the ring-theoretic input: a Koszul-regular ideal of a Noetherian ring is
generated, after one principal localization away from any prime containing it, by an honest
regular sequence.

## Main results

* `Dualizing.LocalCompleteIntersection.exists_away_regular_generators_of_isKoszulRegular` — a
  Koszul-regular ideal of a Noetherian ring is regular.
* `Dualizing.LocalCompleteIntersection.nonempty_homologyIso_away` — the derived localization of
  `RHom_R(A, R)` and `RHom_{R_g}(A_g, R_g)` have the same cohomology in every degree.
* `Dualizing.LocalCompleteIntersection.nonempty_iso_single_away` — hence the first is the free
  module of rank one in degree `c` whenever the second is.

## Implementation notes

The comparison is made degree by degree, through `Ext` over the base ring.  Three identifications
are composed: the cohomology of a derived localization is the localization of the cohomology; the
cohomology of `RHom_R(A, R)` is `Ext^q_R(A, R)` ([Stacks, Tag 0A71]); and localization of such an
`Ext` module out of a finite module is the `Ext` module of the localizations ([Stacks, Tag 0A6A],
the base-change isomorphism for derived Hom along the flat map `R → R_g`).  The last of these is
`Dualizing.localized_ext_nontrivial_iff` with its proof read as an isomorphism rather than as an
equivalence of nonvanishing statements.

The composite is only `R_g`-linear to begin with.  It is `A_g`-linear because `R_g → A_g` is
surjective, an `R_g`-linear map of `A_g`-modules being `A_g`-linear in that case; this is
`Dualizing.InvertibleKernel.linearEquivOfSurjectiveRestriction`.  Nothing in the chain uses the
open keystone `Dualizing.ProjectionCompatibility` or any other unproved hypothesis.

Passing from the degreewise comparison to an isomorphism of objects is possible because the
right-hand side is concentrated in one degree: the left-hand side then is too, and an object of
the derived category concentrated in a single degree is the single complex on its cohomology
there.

## References

* [Stacks Project, Tag 0E4B](https://stacks.math.columbia.edu/tag/0E4B)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* [Stacks Project, Tag 09CC](https://stacks.math.columbia.edu/tag/09CC)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing.LocalCompleteIntersection

/-- Localizing an `A`-module at the powers of `f g` localizes its underlying `R`-module at the
powers of `g`, for any ring homomorphism `f : R → A` and any `g : R`. -/
private theorem isLocalizedModule_powers_of_restrictScalars
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) (g : R)
    {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    [IsLocalizedModule (Submonoid.powers (f g)) φ.hom] :
    IsLocalizedModule (Submonoid.powers g) ((ModuleCat.restrictScalars f).map φ).hom where
  map_units x := by
    obtain ⟨n, hn⟩ := x.2
    have hx : f (x : R) = f g ^ n := by rw [← show g ^ n = (x : R) from hn, map_pow]
    have h := IsLocalizedModule.map_units (S := Submonoid.powers (f g)) φ.hom
      ⟨f g ^ n, n, rfl⟩
    rw [Module.End.isUnit_iff] at h ⊢
    have heq : ∀ y : (N : Type u),
        (algebraMap R (Module.End R ((ModuleCat.restrictScalars f).obj N))) (x : R) y =
          (algebraMap A (Module.End A N)) (f g ^ n) y := by
      intro y
      simp only [Module.algebraMap_end_apply]
      show f (x : R) • y = f g ^ n • y
      rw [hx]
    refine ⟨fun y z hyz => h.1 ?_, fun y => ?_⟩
    · rw [← heq y, ← heq z]
      exact hyz
    · obtain ⟨z, hz⟩ := h.2 y
      exact ⟨z, by rw [heq z]; exact hz⟩
  surj y := by
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers (f g)) φ.hom y
    obtain ⟨n, hn⟩ := s.2
    refine ⟨⟨m, ⟨g ^ n, n, rfl⟩⟩, ?_⟩
    have hfn : f (g ^ n) = (s : A) := by rw [map_pow]; exact hn
    show f (g ^ n) • y = φ.hom m
    rw [hfn]
    exact hs
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f g)) (f := φ.hom) h
    obtain ⟨n, hn⟩ := c.2
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    have hfn : f (g ^ n) = (c : A) := by rw [map_pow]; exact hn
    show f (g ^ n) • x₁ = f (g ^ n) • x₂
    rw [hfn]
    exact hc

/-- A `B`-module read as an `R`-module through `R → A → B` is the same as read through
`R → S → B`, the two composites being equal. -/
private def restrictScalarsSquareIso
    {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    (f : R →+* A) (a : A →+* B) (s : R →+* S) (b : S →+* B)
    (h : a.comp f = b.comp s) (N : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars f).obj ((ModuleCat.restrictScalars a).obj N) ≅
      (ModuleCat.restrictScalars s).obj ((ModuleCat.restrictScalars b).obj N) :=
  (ModuleCat.restrictScalarsComp'App f a (a.comp f) rfl N).symm ≪≫
    (ModuleCat.restrictScalarsCongr h).app N ≪≫
    ModuleCat.restrictScalarsComp'App s b (b.comp s) rfl N

/-- **Localization of an `Ext` module out of a finite module**, as a linear equivalence.  The
localization at `T` of `Ext^i_A(M, K)` is the `Ext` module over `T⁻¹A` formed from the
localizations of `M` and of `K`; this is `Dualizing.localizedExtLinearEquivOfDerivedHom`. -/
private def localizedExtLinearEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] {T : Submonoid A}
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ) :
    LocalizedModule T (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) K i)
      ≃ₗ[Localization T]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
          ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M)))
        ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i :=
  Dualizing.localizedExtLinearEquivOfDerivedHom.{u} T M K hKge i

/-- **The cohomology of `RHom_R(A, R)` in a non-negative degree**, read as an `Ext` module in
the derived category of `R`-modules. -/
private def derivedHomHomologyEquivExt
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (q : ℕ) :
    (((ModuleCat.restrictScalars (algebraMap R A)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (q : ℤ)).obj
          ((Dualizing.derivedHom.{u, u} (algebraMap R A)).obj
            (Stacks0BZE.unitObject.{u, u} R)))) : Type u) ≃ₗ[R]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (ULift.{u} A)))
        (Stacks0BZE.unitObject.{u, u} R) (q : ℤ) :=
  (Dualizing.InvertibleKernel.derivedHomHomologyEquivExt.{u, u} q).trans
    (Abelian.Ext.homLinearEquiv (R := R))

/-- **`RHom_R(A, R)` has no cohomology in negative degrees**, the derived argument being a
single complex in degree zero. -/
private theorem derivedHomHomology_isZero_of_neg
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (q : ℤ) (hq : q < 0) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
      ((Dualizing.derivedHom.{u, u} (algebraMap R A)).obj
        (Stacks0BZE.unitObject.{u, u} R))) := by
  let e := (Dualizing.derivedCoextendScalarsHomologyLinearEquivExt (algebraMap R A)
    (Dualizing.derivedHom.{u, u} (algebraMap R A))
    (Dualizing.InvertibleKernel.derivedHomUnit.{u, u} (algebraMap R A))).linearEquiv
      (Stacks0BZE.unitObject.{u, u} R) q
  let : DerivedCategory.TStructure.t.IsGE (Stacks0BZE.unitObject.{u, u} R) 0 :=
    inferInstanceAs (DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ULift.{u} R))) 0)
  have := DerivedCategory.TStructure.t.isGE_shift
    (Stacks0BZE.unitObject.{u, u} R) 0 q (-q) (by omega)
  have h (x) : e x = 0 := DerivedCategory.TStructure.t.zero (e x) 0 (-q) (by omega)
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => e.injective (by rw [h x, h y])⟩

/-- The localization of `R` as a module at `S` is the localization ring, linearly. -/
private def localizedModuleSelfLinearEquiv {R : Type u} [CommRing R] (S : Submonoid R) :
    LocalizedModule S R ≃ₗ[Localization S] Localization S :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S R)
      (Algebra.linearMap R (Localization S)))

/-- Localizing an `R`-module `M` at `S` gives any module `N` over the localization of `R` at `S`
receiving a localization map from `M`. -/
private def localizedModuleFunctorObjIso {R : Type u} [CommRing R] (S : Submonoid R) {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module (Localization S) N]
    [IsScalarTower R (Localization S) N] (φ : M →ₗ[R] N) [IsLocalizedModule S φ] :
    (ModuleCat.localizedModuleFunctor.{u} S).obj (ModuleCat.of R M) ≅
      ModuleCat.of (Localization S) N :=
  have : IsLocalizedModule S ((ModuleCat.of R M).localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule _ _
  (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S ((ModuleCat.of R M).localizedModuleMkLinearMap S)
      φ)).toModuleIso

/-- **A Koszul-regular ideal of a Noetherian ring is regular.**  At every prime containing a
Koszul-regular ideal, some principal localization away from the prime is generated by a regular
sequence.

Localizing at the prime turns the local Koszul-regular generators into a regular sequence, by
Stacks 09CC, and the denominators of such a sequence are cleared by one further principal
localization. -/
theorem exists_away_regular_generators_of_isKoszulRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : Ideal.IsKoszulRegular I) (p : Ideal R) [p.IsPrime] (hp : I ≤ p) :
    ∃ g : R, g ∉ p ∧ ∃ n : ℕ, ∃ xs : Fin n → Localization.Away g,
      RingTheory.Sequence.IsRegular (Localization.Away g) (List.ofFn xs) ∧
        I.map (algebraMap R (Localization.Away g)) = Ideal.span (Set.range xs) := by
  classical
  obtain ⟨rs, hrs, hspan⟩ :=
    LocalCompleteIntersection.exists_regular_generators_of_koszulRegularIdeal I hI p hp
  let n := rs.length
  let x : Fin n → Localization.AtPrime p := fun i => rs.get i
  have hxlist : List.ofFn x = rs := List.ofFn_get rs
  let rep : Fin n → R × p.primeCompl := fun i =>
    Classical.choose (IsLocalization.surj p.primeCompl (x i))
  let num : Fin n → R := fun i => (rep i).1
  let den : Fin n → R := fun i => (rep i).2
  let F : Fin n → R := fun i => num i *
    ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, den j
  let dprod : p.primeCompl := ∏ i, (rep i).2
  let D : Localization.AtPrime p := algebraMap R (Localization.AtPrime p) dprod
  have hD : IsUnit D := IsLocalization.map_units (Localization.AtPrime p) dprod
  have hnum (i : Fin n) : algebraMap R (Localization.AtPrime p) (num i) =
      algebraMap R (Localization.AtPrime p) (den i) * x i := by
    simpa [num, den, mul_comm] using
      (Classical.choose_spec (IsLocalization.surj p.primeCompl (x i))).symm
  have hF (i : Fin n) : algebraMap R (Localization.AtPrime p) (F i) = D * x i := by
    dsimp only [F, D, num, den]
    have hpSubtype : (rep i).2 *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (rep j).2 = dprod := by
      dsimp [dprod]
      exact Finset.mul_prod_erase Finset.univ (fun j : Fin n => (rep j).2)
        (Finset.mem_univ i)
    have hp : (rep i).2 *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ((rep j).2 : R) =
          (dprod : R) := by
      simpa using congrArg (fun s : p.primeCompl => (s : R)) hpSubtype
    rw [← hp, map_mul, map_mul, hnum]
    ring
  have hscaled : RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (List.ofFn (fun i : Fin n => D * x i)) := by
    have hl : rs.map (D * ·) = List.ofFn (fun i : Fin n => D * x i) := by
      rw [← hxlist]
      simp [Function.comp_def]
    exact hl ▸ hrs.map_mul_unit hD
  let xs : List R := List.ofFn F
  have hregAt : RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (xs.map (algebraMap R (Localization.AtPrime p))) := by
    have heq : xs.map (algebraMap R (Localization.AtPrime p)) =
        List.ofFn (fun i : Fin n => D * x i) := by
      simp only [xs, List.map_ofFn]
      exact congrArg List.ofFn (funext hF)
    rwa [heq]
  have hspanAt : I.map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span (Set.range (fun i : Fin n => algebraMap R (Localization.AtPrime p) (F i))) := by
    calc
      I.map (algebraMap R (Localization.AtPrime p)) = Ideal.ofList rs := hspan.symm
      _ = Ideal.ofList (rs.map (D * ·)) :=
        (Ideal.ofList_map_mul_unit hD rs).symm
      _ = Ideal.ofList (List.ofFn (fun i : Fin n => D * x i)) := by
        rw [← hxlist]
        simp [Function.comp_def]
      _ = Ideal.span (Set.range (fun i : Fin n =>
          algebraMap R (Localization.AtPrime p) (F i))) := by
        rw [← congrArg List.ofFn (funext hF), Ideal.ofList]
        congr 1
        ext z
        simp [List.mem_ofFn]
  have hregM : RingTheory.Sequence.IsRegular (LocalizedModule p.primeCompl R)
      (xs.map (algebraMap R (Localization.AtPrime p))) :=
    ((localizedModuleSelfLinearEquiv p.primeCompl).isRegular_congr _).2
      hregAt
  let K : Ideal R := Ideal.span (Set.range F)
  have hspanAt' : I.map (algebraMap R (Localization.AtPrime p)) =
      K.map (algebraMap R (Localization.AtPrime p)) := by
    simpa only [K, Ideal.map_span, ← Set.range_comp, Function.comp_def] using hspanAt
  obtain ⟨d, hd, hdI, hdK⟩ := LocalCompleteIntersection.exists_away_eq_of_atPrime_eq I K
    (IsNoetherian.noetherian I) (IsNoetherian.noetherian K) p hspanAt'
  obtain ⟨c, hc, hcd, hregMc⟩ :=
    LocalCompleteIntersection.regular_sequence_localize_away_of_atPrime_mul p xs hregM d hd
  have hregAway : RingTheory.Sequence.IsRegular (Localization.Away c)
      (xs.map (algebraMap R (Localization.Away c))) :=
    ((localizedModuleSelfLinearEquiv (Submonoid.powers c)).isRegular_congr
      _).1 hregMc
  let xsAway : Fin n → Localization.Away c := fun i => algebraMap R _ (F i)
  have hregAway' : RingTheory.Sequence.IsRegular (Localization.Away c) (List.ofFn xsAway) := by
    convert hregAway using 1
    simp [xs, xsAway, List.map_ofFn, Function.comp_def]
  have hKmap : K.map (algebraMap R (Localization.Away c)) =
      Ideal.span (Set.range xsAway) := by
    simp [K, xsAway, Ideal.map_span, ← Set.range_comp, Function.comp_def]
  have hmapMem (J : Ideal R) (y : R) (hy : c * y ∈ J) :
      algebraMap R (Localization.Away c) y ∈ J.map (algebraMap R (Localization.Away c)) := by
    have hmap := Ideal.mem_map_of_mem (algebraMap R (Localization.Away c)) hy
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away c) c
    simpa [← hu, ← mul_assoc] using
      (J.map (algebraMap R (Localization.Away c))).mul_mem_left (↑u⁻¹ : Localization.Away c) hmap
  have hspanAway : I.map (algebraMap R (Localization.Away c)) =
      Ideal.span (Set.range xsAway) := by
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro y hy
      have hmem : c * y ∈ K := by
        obtain ⟨k, rfl⟩ := hcd
        convert K.mul_mem_left k (hdI y hy) using 1
        ring
      exact hKmap ▸ hmapMem K y hmem
    · rw [Ideal.span_le]
      rintro y ⟨i, rfl⟩
      have hmem : c * F i ∈ I := by
        obtain ⟨k, rfl⟩ := hcd
        convert I.mul_mem_left k (hdK (F i) (Ideal.subset_span ⟨i, rfl⟩)) using 1
        ring
      exact hmapMem I _ hmem
  exact ⟨c, hc, n, xsAway, hregAway', hspanAway⟩

/-! ### Localizing a surjection away from an element -/

section Away

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (g : R)

/-- The localization of `A` away from the image of `g`, as an algebra over the localization of
`R` away from `g`: the structure map is the localized homomorphism. -/
private noncomputable instance awayAlgebra :
    Algebra (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
  (IsLocalization.Away.map (Localization.Away g) (Localization.Away (algebraMap R A g))
    (algebraMap R A) g).toAlgebra

/-- The two ways of mapping `R` into the localization of `A` away from the image of `g`, through
`A` and through the localization of `R` away from `g`, agree. -/
private instance awayTower :
    IsScalarTower R (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away (algebraMap R A g)) r]
    exact (IsLocalization.map_eq (S := Localization.Away g)
      (Q := Localization.Away (algebraMap R A g)) (g := algebraMap R A)
      (M := Submonoid.powers g) (T := Submonoid.powers (algebraMap R A g))
      (fun y hy => by obtain ⟨n, rfl⟩ := hy; exact ⟨n, (map_pow _ g n).symm⟩) r).symm

/-- The localization away from `g` of the lifted copy of `R` is the lifted copy of the
localization of `R` away from `g`. -/
private def awayLocalizedULiftBaseIso :
    (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers g)).obj
        (ModuleCat.of R (ULift.{u} R)) ≅
      ModuleCat.of (Localization.Away g) (ULift.{u} (Localization.Away g)) := by
  letI φ : ULift.{u} R →ₗ[R] ULift.{u} (Localization.Away g) :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ (Algebra.linearMap R (Localization.Away g)) ∘ₗ
      ULift.moduleEquiv.toLinearMap
  exact localizedModuleFunctorObjIso (Submonoid.powers g) φ

/-- The localization away from `g` of the lifted copy of `A` is the lifted copy of the
localization of `A` away from the image of `g`. -/
private def awayLocalizedULiftIso :
    (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers g)).obj
        (ModuleCat.of R (ULift.{u} A)) ≅
      ModuleCat.of (Localization.Away g)
        (ULift.{u} (Localization.Away (algebraMap R A g))) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers g))
      (Localization.Away (algebraMap R A g)) := by
    rw [show Algebra.algebraMapSubmonoid A (Submonoid.powers g)
        = Submonoid.powers (algebraMap R A g) from Submonoid.map_powers _ _]
    infer_instance
  letI φ : ULift.{u} A →ₗ[R] ULift.{u} (Localization.Away (algebraMap R A g)) :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ
      (IsScalarTower.toAlgHom R A (Localization.Away (algebraMap R A g))).toLinearMap ∘ₗ
      ULift.moduleEquiv.toLinearMap
  exact localizedModuleFunctorObjIso (Submonoid.powers g) φ

/-- Localizing away from `g` takes the unit of `D(R)` to the unit of `D(R_g)`. -/
private def awayLocalizedUnitIso :
    (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers g)).mapDerivedCategory.obj
        (Stacks0BZE.unitObject.{u, u} R) ≅
      Stacks0BZE.unitObject.{u, u} (Localization.Away g) :=
  ((ModuleCat.localizedModuleFunctor.{u}
      (Submonoid.powers g)).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of R (ULift.{u} R)) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away g)) 0).mapIso
      (awayLocalizedULiftBaseIso g)

/-- **The cohomology of the localized relative dualizing complex of a surjection.**  Let
`R → A` be a surjection of rings with `R` Noetherian and let `g : R`.  Then the derived
localization of `RHom_R(A, R)` away from the image of `g` has the same cohomology, degree by
degree, as `RHom_{R_g}(A_g, R_g)`.

Both sides are computed through `Ext` over the base: the cohomology of `RHom_R(A, R)` is
`Ext^q_R(A, R)` by Stacks 0A71, localization of such an `Ext` module is the `Ext` module of the
localizations, and the cohomology of a derived localization is the localization of the
cohomology.  The resulting comparison is a priori only `R_g`-linear, and it is `A_g`-linear
because `R_g → A_g` is surjective. -/
theorem nonempty_homologyIso_away [IsNoetherianRing R]
    (hf : Function.Surjective (algebraMap R A)) (q : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (Localization.Away (algebraMap R A g))) q).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A (Localization.Away (algebraMap R A g)))).functor.obj
          ((Dualizing.derivedHom.{u, u} (algebraMap R A)).obj
            (Stacks0BZE.unitObject.{u, u} R))) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (Localization.Away (algebraMap R A g))) q).obj
        ((Dualizing.derivedHom.{u, u} (IsLocalization.Away.map (Localization.Away g)
            (Localization.Away (algebraMap R A g)) (algebraMap R A) g)).obj
          (Stacks0BZE.unitObject.{u, u} (Localization.Away g)))) := by
  have : Module.Finite R A := Module.Finite.of_surjective (Algebra.linearMap R A) hf
  set X := (Dualizing.derivedHom.{u, u} (algebraMap R A)).obj (Stacks0BZE.unitObject.{u, u} R)
    with hXdef
  set XB := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (Localization.Away (algebraMap R A g)))).functor.obj X with hXBdef
  set Y := (Dualizing.derivedHom.{u, u} (algebraMap (Localization.Away g)
    (Localization.Away (algebraMap R A g)))).obj
      (Stacks0BZE.unitObject.{u, u} (Localization.Away g)) with hYdef
  -- the comparison of step one: the cohomology of `XB` localizes the cohomology of `X`
  have α : (ModuleCat.restrictScalars
        (algebraMap A (Localization.Away (algebraMap R A g)))).obj
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Localization.Away (algebraMap R A g))) q).obj XB) ≅
      ModuleCat.of A (LocalizedModule (Submonoid.powers (algebraMap R A g))
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj X)) := by
    simpa only [hXBdef, Functor.comp_obj,
      CochainComplex.DerivedTensor.localizedModuleFunctor] using
      (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, u}
        (R := A) (A := Localization.Away (algebraMap R A g))
        (S := Submonoid.powers (algebraMap R A g)) q).app X
  by_cases hneg : q < 0
  · -- both sides vanish
    have hX0 : Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj X) :=
      derivedHomHomology_isZero_of_neg q hneg
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj X : Type u) :=
      ModuleCat.isZero_iff_subsingleton.mp hX0
    have hXB0 : Limits.IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Localization.Away (algebraMap R A g))) q).obj XB) := by
      refine ModuleCat.isZero_iff_subsingleton.mpr ?_
      exact (α.toLinearEquiv.toEquiv.subsingleton_congr).mpr inferInstance
    exact ⟨hXB0.iso (derivedHomHomology_isZero_of_neg q hneg)⟩
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = (n : ℤ) := ⟨q.toNat, by omega⟩
    -- step two: the `A`-localization of the cohomology is its `R`-localization
    have : IsLocalizedModule (Submonoid.powers (algebraMap R A g))
        (ModuleCat.ofHom (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R A g))
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj X))).hom :=
      inferInstanceAs (IsLocalizedModule _ (LocalizedModule.mkLinearMap _ _))
    have := isLocalizedModule_powers_of_restrictScalars (algebraMap R A) g
      (ModuleCat.ofHom (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R A g))
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj X)))
    have v : (((ModuleCat.restrictScalars (algebraMap R A)).obj
          ((ModuleCat.restrictScalars (algebraMap A (Localization.Away (algebraMap R A g)))).obj
            ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} (Localization.Away (algebraMap R A g))) (n : ℤ)).obj XB))) :
            Type u) ≃ₗ[R]
        LocalizedModule (Submonoid.powers g)
          (((ModuleCat.restrictScalars (algebraMap R A)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj X)) : Type u) :=
      ((ModuleCat.restrictScalars (algebraMap R A)).mapIso α).toLinearEquiv.trans
        (IsLocalizedModule.iso (Submonoid.powers g)
          (((ModuleCat.restrictScalars (algebraMap R A)).map
            (ModuleCat.ofHom (LocalizedModule.mkLinearMap
              (Submonoid.powers (algebraMap R A g))
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj X)))).hom)).symm
    -- steps three to six: the localized cohomology, read through `Ext`
    have w : LocalizedModule (Submonoid.powers g)
          (((ModuleCat.restrictScalars (algebraMap R A)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj X)) : Type u)
        ≃ₗ[Localization.Away g]
        (((ModuleCat.restrictScalars (algebraMap (Localization.Away g)
            (Localization.Away (algebraMap R A g)))).obj
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (Localization.Away (algebraMap R A g))) (n : ℤ)).obj Y)) : Type u) :=
      (IsLocalizedModule.mapEquiv (Submonoid.powers g)
          (LocalizedModule.mkLinearMap (Submonoid.powers g) _)
          (LocalizedModule.mkLinearMap (Submonoid.powers g) _) (Localization.Away g)
          (derivedHomHomologyEquivExt n)).trans
        ((localizedExtLinearEquiv (A := R) (T := Submonoid.powers g) (M := ULift.{u} A)
            (Stacks0BZE.unitObject.{u, u} R)
            ⟨0, inferInstanceAs (DerivedCategory.IsGE
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                (ModuleCat.of R (ULift.{u} R))) 0)⟩ (n : ℤ)).trans
          ((Linear.homCongr (Localization.Away g)
              ((DerivedCategory.singleFunctor
                (ModuleCat.{u} (Localization.Away g)) 0).mapIso (awayLocalizedULiftIso g))
              ((shiftFunctor (DerivedCategory (ModuleCat.{u} (Localization.Away g))) (n : ℤ)).mapIso
                (awayLocalizedUnitIso g))).trans
            (derivedHomHomologyEquivExt (R := Localization.Away g)
              (A := Localization.Away (algebraMap R A g)) n).symm))
    -- the two readings of `R` acting on the cohomology of `XB`
    have hcomp : (algebraMap A (Localization.Away (algebraMap R A g))).comp (algebraMap R A) =
        (algebraMap (Localization.Away g) (Localization.Away (algebraMap R A g))).comp
          (algebraMap R (Localization.Away g)) :=
      (IsScalarTower.algebraMap_eq R A (Localization.Away (algebraMap R A g))).symm.trans
        (IsScalarTower.algebraMap_eq R (Localization.Away g)
          (Localization.Away (algebraMap R A g)))
    have v' : (((ModuleCat.restrictScalars (algebraMap R (Localization.Away g))).obj
          ((ModuleCat.restrictScalars (algebraMap (Localization.Away g)
            (Localization.Away (algebraMap R A g)))).obj
            ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} (Localization.Away (algebraMap R A g))) (n : ℤ)).obj XB))) :
            Type u) ≃ₗ[R]
        LocalizedModule (Submonoid.powers g)
          (((ModuleCat.restrictScalars (algebraMap R A)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj X)) : Type u) :=
      (restrictScalarsSquareIso (algebraMap R A)
        (algebraMap A (Localization.Away (algebraMap R A g)))
        (algebraMap R (Localization.Away g))
        (algebraMap (Localization.Away g) (Localization.Away (algebraMap R A g))) hcomp
        _).symm.toLinearEquiv.trans v
    have : IsScalarTower R (Localization.Away g)
        (((ModuleCat.restrictScalars (algebraMap R (Localization.Away g))).obj
          ((ModuleCat.restrictScalars (algebraMap (Localization.Away g)
            (Localization.Away (algebraMap R A g)))).obj
            ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} (Localization.Away (algebraMap R A g))) (n : ℤ)).obj XB))) :
            Type u) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hb : Function.Surjective
        (algebraMap (Localization.Away g) (Localization.Away (algebraMap R A g))) := by
      refine (IsLocalization.Away.map_surjective_iff (Localization.Away g)
        (Localization.Away (algebraMap R A g)) (algebraMap R A) g).mpr ?_
      intro y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨x, 0, by simp⟩
    exact ⟨(Dualizing.InvertibleKernel.linearEquivOfSurjectiveRestriction.{u, u}
      (algebraMap (Localization.Away g) (Localization.Away (algebraMap R A g))) hb _ _
      ((LinearEquiv.extendScalarsOfIsLocalization (Submonoid.powers g)
        (Localization.Away g) v').trans w)).toModuleIso⟩

/-- **The localized relative dualizing complex of a surjection is a shifted unit as soon as the
localized surjection says so.**  Let `R → A` be a surjection of rings with `R` Noetherian and let
`g : R`.  If `RHom_{R_g}(A_g, R_g)` is the free module of rank one in degree `c`, then so is the
derived localization of `RHom_R(A, R)` away from the image of `g`.

The two objects have the same cohomology by `nonempty_homologyIso_away`, so the second is
concentrated in degree `c` with value `A_g` there, and an object of the derived category
concentrated in a single degree is the single complex on its cohomology there. -/
theorem nonempty_iso_single_away [IsNoetherianRing R]
    (hf : Function.Surjective (algebraMap R A)) (c : ℤ)
    (hY : Nonempty ((Dualizing.derivedHom.{u, u} (IsLocalization.Away.map (Localization.Away g)
            (Localization.Away (algebraMap R A g)) (algebraMap R A) g)).obj
          (Stacks0BZE.unitObject.{u, u} (Localization.Away g)) ≅
        (DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization.Away (algebraMap R A g))) c).obj
          (ModuleCat.of (Localization.Away (algebraMap R A g))
            (Localization.Away (algebraMap R A g))))) :
    Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A (Localization.Away (algebraMap R A g)))).functor.obj
        ((Dualizing.derivedHom.{u, u} (algebraMap R A)).obj
          (Stacks0BZE.unitObject.{u, u} R)) ≅
      (DerivedCategory.singleFunctor
          (ModuleCat.{u} (Localization.Away (algebraMap R A g))) c).obj
        (ModuleCat.of (Localization.Away (algebraMap R A g))
          (Localization.Away (algebraMap R A g)))) := by
  obtain ⟨eY⟩ := hY
  set XB := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (Localization.Away (algebraMap R A g)))).functor.obj
      ((Dualizing.derivedHom.{u, u} (algebraMap R A)).obj (Stacks0BZE.unitObject.{u, u} R))
    with hXBdef
  have hzero : ∀ q : ℤ, q ≠ c → Limits.IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away (algebraMap R A g))) q).obj XB) := by
    intro q hq
    obtain ⟨κ⟩ := nonempty_homologyIso_away g hf q
    refine Limits.IsZero.of_iso ?_ (hXBdef ▸ κ)
    refine Limits.IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away (algebraMap R A g))) q).mapIso eY)
    rcases lt_or_gt_of_ne hq with h | h
    · exact DerivedCategory.isZero_of_isGE _ c q h
    · exact DerivedCategory.isZero_of_isLE _ c q h
  have hLE : XB.IsLE c := (DerivedCategory.isLE_iff XB c).2 fun q hq => hzero q (by omega)
  have hGE : XB.IsGE c := (DerivedCategory.isGE_iff XB c).2 fun q hq => hzero q (by omega)
  obtain ⟨W, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE XB c
  obtain ⟨κc⟩ := nonempty_homologyIso_away g hf c
  refine ⟨e ≪≫ (DerivedCategory.singleFunctor
    (ModuleCat.{u} (Localization.Away (algebraMap R A g))) c).mapIso ?_⟩
  exact ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} (Localization.Away (algebraMap R A g))) c).app W).symm ≪≫
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away (algebraMap R A g))) c).mapIso e.symm ≪≫
    (hXBdef ▸ κc) ≪≫
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away (algebraMap R A g))) c).mapIso eY ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (Localization.Away (algebraMap R A g))) c).app
        (ModuleCat.of (Localization.Away (algebraMap R A g))
          (Localization.Away (algebraMap R A g)))

end Away

end Dualizing.LocalCompleteIntersection

end
