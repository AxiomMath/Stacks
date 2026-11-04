module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.DerivedHomHomologyDual
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayCriterion
public import StacksFrontier.RingTheory.Dualizing.ConcentratedDualizingModule
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayFromModule
public import StacksFrontier.RingTheory.Dualizing.LocalizedExt
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.Serre.Surjection
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# `Ext` out of a Cohen--Macaulay quotient into a dualizing module

Let `S` be a Noetherian ring with a dualizing module `ω`, and let `I ⊂ S` be an ideal such that
`C = S ⧸ I` is Cohen--Macaulay of constant codimension `c`: `dim S_P = dim C_P + c` at every prime
`P ⊇ I`. Then `Ext^j_S(C, ω) = 0` for `j ≠ c`, and `Ext^c_S(C, ω)` is a dualizing module over `C`.
This is the computation used for the charts of a blowup embedded in a polynomial ring, where
`S = A[x_1, …, x_N]`, `ω = ω_A ⊗_A S` and `c = N`.

## Main results

* `Dualizing.eq_of_nontrivial_ext_of_isCohenMacaulayAtMaximalIdeal` — local duality for a
  Cohen--Macaulay module: over a Noetherian local ring `R` with a dualizing complex concentrated in
  degree `n`, `Ext^j_R(M, K) ≠ 0` forces `j = n + dim R - dim Supp M`.
* `Dualizing.subsingleton_ext_quotient_of_ne` — `Ext^j_S(S ⧸ I, ω) = 0` for `j ≠ c`.
* `Dualizing.extQuotient_concentration_derivedHom` — the dualizing complex `RHom_S(S ⧸ I, ω)` of
  [Stacks, Tag 0AX0] has its cohomology in degree `c` only, and `H^c` is a dualizing module over
  `S ⧸ I` which, read over `S`, is `Ext^c_S(S ⧸ I, ω)`.
* `Dualizing.extQuotient_concentration` — the same, phrased with Mathlib's `Abelian.Ext`.

## Implementation notes

The vanishing is checked after localizing at the primes of `S`. Localization commutes with `Ext`
out of a finite module (`Dualizing.localized_ext_nontrivial_iff`), a dualizing module localizes
to a dualizing module [Stacks, Tag 0A7G], and at a prime `P ⊇ I` the localization `(S ⧸ I)_P` is a
Cohen--Macaulay `S_P`-module whose support has dimension `dim (S ⧸ I)_P`; the Cohen--Macaulay
criterion of [Stacks, Tag 0B5A], read against the normalized shift of `ω_P`, locates the only
nonzero `Ext` in degree `dim S_P - dim (S ⧸ I)_P = c`. The `S ⧸ I`-module structure of the
conclusion is that of the cohomology of `RHom_S(S ⧸ I, ω)`, which is identified with
`Ext^c_S(S ⧸ I, ω)` by [Stacks, Tag 0A71]; once its cohomology is concentrated in degree `c`, that
dualizing complex is `H^c` placed in degree `c`.

The Cohen--Macaulay and dimension hypotheses are indexed by the primes `Q` of `S ⧸ I`, the
corresponding prime of `S` being `Q.comap (Ideal.Quotient.mk I)`; this is the same data as the
primes of `S` containing `I`.

## References

* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
* [Stacks Project, Tag 0B5A](https://stacks.math.columbia.edu/tag/0B5A)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- Being a dualizing complex depends on the object only through its isomorphism class. -/
theorem isDualizingComplex_iff_of_iso {B : Type u} [CommRing B] [IsNoetherianRing B]
    {K L : DerivedCategory (ModuleCat.{u} B)} (e : K ≅ L) :
    IsDualizingComplex K ↔ IsDualizingComplex L := by
  suffices h : ∀ {K L : DerivedCategory (ModuleCat.{u} B)}, (K ≅ L) →
      IsDualizingComplex K → IsDualizingComplex L from ⟨h e, h e.symm⟩
  intro K L e hK
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
    exact ⟨a, b, I, hge, hle, hinj, ⟨e.symm ≪≫ eI⟩⟩
  · intro i
    have : Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj K) :=
      hK.finiteCohomology i
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso e).toLinearEquiv
  · rintro I ⟨eI⟩ hinj hbound
    exact hK.homothetyQuasiIso I ⟨eI ≪≫ e.symm⟩ hinj hbound

/-- The cohomology of an object that is both `≥ n` and `≤ n` vanishes away from degree `n`. -/
private theorem isZero_homologyFunctor_obj_of_ne {B : Type u} [CommRing B]
    (K : DerivedCategory (ModuleCat.{u} B)) (n : ℤ) {i : ℤ} (hi : i ≠ n) [K.IsGE n] [K.IsLE n] :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj K) := by
  rcases lt_or_gt_of_ne hi with h | h
  · exact DerivedCategory.isZero_of_isGE K n i h
  · exact DerivedCategory.isZero_of_isLE K n i h

/-- **Local duality for a Cohen--Macaulay module.** Let `R` be a Noetherian local ring of
dimension `d_R` and `K` a dualizing complex over `R` with cohomology concentrated in degree `n`.
For a nonzero finite Cohen--Macaulay `R`-module `M` with support of dimension `d_M`, the module
`Ext^j_R(M, K)` vanishes unless `j = n + d_R - d_M`. -/
theorem eq_of_nontrivial_ext_of_isCohenMacaulayAtMaximalIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsDualizingComplex K) (n : ℤ)
    (hn : ∀ i : ℤ, i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K))
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : Module.IsCohenMacaulayAtMaximalIdeal R M) (dR dM : ℕ)
    (hdR : ringKrullDim R = dR) (hdM : Module.supportDim R M = dM) (j : ℤ)
    (hj : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R M)) K j)) :
    j = n + dR - dM := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0} K hK
  have hshift : ∀ i : ℤ, i ≠ n + m →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (K⟦-m⟧)) := by
    intro i hi
    exact (hn (-m + i) (by omega)).of_iso (homologyShiftObjIsoOfEq K (-m) i (-m + i) rfl)
  have hconc : IsCohomologicallyConcentratedInOneDegree (K⟦-m⟧) := ⟨n + m, hshift⟩
  have hA : IsCohenMacaulayLocalRing R :=
    ((isCohenMacaulay_tfae_dualizingComplex (K⟦-m⟧) hm).out 2 1).mp hconc
  obtain ⟨e⟩ := ((isCohenMacaulay_tfae_dualizingComplex (K⟦-m⟧) hm).out 1 3).mp hA
  have hdim : ∀ i : ℤ, i ≠ -(localRingDimension R : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (K⟦-m⟧)) := by
    intro i hi
    exact IsZero.of_iso (isZero_homologyFunctor_obj_of_ne _ _ hi)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e)
  obtain ⟨j₀, hj₀⟩ := exists_not_isZero_homology (K⟦-m⟧) hm.1
  have hj₁ : j₀ = n + m := Classical.byContradiction fun hc => hj₀ (hshift j₀ hc)
  have hj₂ : j₀ = -(localRingDimension R : ℤ) :=
    Classical.byContradiction fun hc => hj₀ (hdim j₀ hc)
  have hloc : localRingDimension R = dR := by
    have hh : (IsLocalRing.maximalIdeal R).height = (dR : ℕ∞) := by
      have h1 : (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) =
          ((dR : ℕ∞) : WithBot ℕ∞) := by
        rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdR]
        rfl
      exact_mod_cast h1
    simp [localRingDimension, hh]
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R M)
  have hj' : Nontrivial (DerivedCategory.Ext X (K⟦-m⟧) (j + m)) := by
    let s := (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} R)) (-m) (j + m) j
      (by omega)).app K
    show Nontrivial (X ⟶ (K⟦-m⟧)⟦j + m⟧)
    exact (Iso.homCongr (Iso.refl X) s).nontrivial_congr.mp hj
  have h3 := ((isCohenMacaulay_iff_ext_concentrated.{u, 0} (M := M) (K⟦-m⟧) hm).out 1 3).mp hM
  have hcond : 0 ≤ -(j + m) ∧
      Module.supportDim R M = (((-(j + m)).toNat : ℕ∞) : WithBot ℕ∞) := by
    by_contra hc
    have hsub := h3 (-(j + m)) hc
    rw [neg_neg] at hsub
    exact (not_subsingleton_iff_nontrivial.mpr hj') hsub
  obtain ⟨hnonneg, hsd⟩ := hcond
  rw [hdM] at hsd
  have hdM' : dM = (-(j + m)).toNat := by exact_mod_cast hsd
  omega

/-- **The localization of `S ⧸ I` at a prime, read over the ambient ring.** For a prime `Q` of
`S ⧸ I` with preimage `P ⊂ S`, the localization `(S ⧸ I)_P` is a nonzero `S_P`-module whose depth
along the maximal ideal of `S_P` is the depth of the local ring `(S ⧸ I)_Q` and whose support has
the dimension of `(S ⧸ I)_Q`. -/
theorem localizedModule_quotient_depth_supportDim (S : Type u) [CommRing S] (I : Ideal S)
    (Q : Ideal (S ⧸ I)) [Q.IsPrime] :
    Nontrivial (LocalizedModule (Q.comap (Ideal.Quotient.mk I)).primeCompl (S ⧸ I)) ∧
      Module.depth (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))
          (IsLocalRing.maximalIdeal (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))
          (LocalizedModule (Q.comap (Ideal.Quotient.mk I)).primeCompl (S ⧸ I)) =
        localRingDepth (Localization.AtPrime Q) ∧
      Module.supportDim (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))
          (LocalizedModule (Q.comap (Ideal.Quotient.mk I)).primeCompl (S ⧸ I)) =
        ringKrullDim (Localization.AtPrime Q) := by
  classical
  set P := Q.comap (Ideal.Quotient.mk I) with hPdef
  let C := S ⧸ I
  let SP := Localization.AtPrime P
  let CQ := Localization.AtPrime Q
  let N := LocalizedModule P.primeCompl C
  have : Q.LiesOver P := ⟨rfl⟩
  have hsub : Algebra.algebraMapSubmonoid C P.primeCompl = Q.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective Q P Ideal.Quotient.mk_surjective
  have : IsLocalization (Algebra.algebraMapSubmonoid C P.primeCompl) CQ := by
    rw [hsub]
    infer_instance
  have : IsLocalizedModule P.primeCompl (IsScalarTower.toAlgHom S C CQ).toLinearMap :=
    (isLocalizedModule_iff_isLocalization (S := P.primeCompl) (A := C) (Aₛ := CQ)).mpr
      inferInstance
  let e₀ : N ≃ₗ[S] CQ := IsLocalizedModule.linearEquiv P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl C) (IsScalarTower.toAlgHom S C CQ).toLinearMap
  let : Algebra SP CQ :=
    (Localization.localRingHom P Q (Ideal.Quotient.mk I) hPdef).toAlgebra
  have hsurj : Function.Surjective (algebraMap SP CQ) :=
    Localization.surjective_localRingHom (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective P Q
      hPdef
  have : IsScalarTower S SP CQ := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    show algebraMap S CQ x = Localization.localRingHom P Q (Ideal.Quotient.mk I) hPdef
      (algebraMap S SP x)
    rw [Localization.localRingHom_to_map]
    rfl
  let e : N ≃ₗ[SP] CQ := e₀.extendScalarsOfIsLocalization P.primeCompl SP
  refine ⟨e.toEquiv.nontrivial, ?_, ?_⟩
  · rw [Module.depth_eq_depth_of_linearEquiv _ e,
      Module.depth_eq_depth_map_algebraMap hsurj (IsLocalRing.maximalIdeal SP) CQ,
      IsLocalRing.map_maximalIdeal_of_surjective (algebraMap SP CQ) hsurj,
      localRingDepth_eq_depth_self]
  · let f : SP →ₐ[SP] CQ := Algebra.ofId SP CQ
    let e₂ : (SP ⧸ RingHom.ker f) ≃ₐ[SP] CQ := Ideal.quotientKerAlgEquivOfSurjective hsurj
    rw [Module.supportDim_eq_of_equiv e, ← Module.supportDim_eq_of_equiv e₂.toLinearEquiv,
      Module.supportDim_quotient_eq_ringKrullDim]
    exact ringKrullDim_eq_of_ringEquiv e₂.toRingEquiv

/-- **Localizing a dualizing module at a prime.** If `ω` placed in degree zero is a dualizing
complex over a Noetherian ring `S`, then for every prime `P` its localization `ω_P`, placed in
degree zero, is a dualizing complex over `S_P` with cohomology concentrated in degree zero. -/
theorem isDualizingComplex_localizedModuleFunctor_single (S : Type u) [CommRing S]
    [IsNoetherianRing S] (ω : ModuleCat.{u} S)
    (hω : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω))
    (P : Ideal S) [P.IsPrime] :
    IsDualizingComplex ((ModuleCat.localizedModuleFunctor.{u} P.primeCompl).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω)) ∧
      ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Localization.AtPrime P)) i).obj
          ((ModuleCat.localizedModuleFunctor.{u} P.primeCompl).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω))) := by
  let K0 := (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω
  let R := Localization.AtPrime P
  let f := algebraMap S R
  let F := ModuleCat.extendScalars.{u, u, u} f
  let G := ModuleCat.localizedModuleFunctor.{u} P.primeCompl
  have : F.Additive := (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive
  have : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' f
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat R P.primeCompl))
  have : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  refine ⟨?_, fun i hi => ?_⟩
  · exact (isDualizingComplex_iff_of_iso
      (mapDerivedCategoryIsoFromNatIso F G
        (extendScalarsIsoLocalizedModuleFunctor.{u, u} P.primeCompl) K0)).mp
      (isDualizingComplex_extendScalars_of_isLocalization (B := R) P.primeCompl K0 hω)
  · exact Functor.isZero_homologyFunctor_mapDerivedCategory_obj (F := G) K0 i
      (isZero_homologyFunctor_obj_of_ne _ _ hi)

/-- The Krull dimension of a Noetherian local ring is a natural number. -/
theorem exists_ringKrullDim_eq_natCast_of_isLocalRing (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] : ∃ d : ℕ, (d : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1
    (Ideal.height_ne_top_of_isPrime (I := IsLocalRing.maximalIdeal A))
  refine ⟨d, ?_⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hd]
  rfl

/-- **Vanishing of `Ext^j_S(S ⧸ I, ω)` off the codimension.** Let `S` be a Noetherian ring, `ω`
an `S`-module which placed in degree zero is a dualizing complex, and `I ⊂ S` an ideal such that
`S ⧸ I` is Cohen--Macaulay and `dim S_P = dim (S ⧸ I)_P + c` at every prime `P ⊇ I`. Then
`Ext^j_S(S ⧸ I, ω) = 0` for every `j ≠ c`.

The module is zero as soon as all its localizations at primes are. Localizing at `P` turns it
into `Ext^j_{S_P}((S ⧸ I)_P, ω_P)` (`Dualizing.localized_ext_nontrivial_iff`), which vanishes if
`P ⊉ I`, since then `(S ⧸ I)_P = 0`; and if `P ⊇ I` the module `(S ⧸ I)_P` is Cohen--Macaulay over
`S_P` with support of dimension `dim (S ⧸ I)_P`, so local duality
(`Dualizing.eq_of_nontrivial_ext_of_isCohenMacaulayAtMaximalIdeal`) locates the only nonzero
`Ext` in degree `dim S_P - dim (S ⧸ I)_P = c`. -/
theorem subsingleton_ext_quotient_of_ne (S : Type u) [CommRing S] [IsNoetherianRing S]
    (ω : ModuleCat.{u} S)
    (hω : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω))
    (I : Ideal S) (c : ℕ) (hCM : IsCohenMacaulayRing (S ⧸ I))
    (hdim : ∀ (Q : Ideal (S ⧸ I)) [Q.IsPrime],
      ringKrullDim (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))) =
        ringKrullDim (Localization.AtPrime Q) + c)
    (j : ℤ) (hj : j ≠ c) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S (S ⧸ I)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω) j) := by
  classical
  let K0 := (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω
  rw [← Module.support_eq_empty_iff (R := S)]
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  rw [Module.mem_support_iff] at hp
  obtain ⟨P, hP⟩ := p
  dsimp only at hp
  have hnt : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime P)) 0).obj
        ((ModuleCat.localizedModuleFunctor.{u} P.primeCompl).obj (ModuleCat.of S (S ⧸ I))))
      ((ModuleCat.localizedModuleFunctor.{u} P.primeCompl).mapDerivedCategory.obj K0) j) :=
    (localized_ext_nontrivial_iff.{u, 0} (T := P.primeCompl) (M := S ⧸ I) K0
      ⟨0, inferInstance⟩ j).mp hp
  let eM : ((ModuleCat.localizedModuleFunctor.{u} P.primeCompl).obj (ModuleCat.of S (S ⧸ I)) :
      Type u) ≃ₗ[Localization.AtPrime P] LocalizedModule P.primeCompl (S ⧸ I) :=
    Shrink.linearEquiv.{u} (Localization.AtPrime P) _
  by_cases hIP : I ≤ P
  swap
  · obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
    have hsub : Subsingleton (LocalizedModule P.primeCompl (S ⧸ I)) := by
      rw [LocalizedModule.subsingleton_iff]
      intro m
      refine ⟨s, hsP, ?_⟩
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.mpr hsI, zero_mul]
    have hX : IsZero ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime P))
        0).obj ((ModuleCat.localizedModuleFunctor.{u} P.primeCompl).obj
          (ModuleCat.of S (S ⧸ I)))) :=
      Functor.map_isZero _ (ModuleCat.isZero_iff_subsingleton.mpr eM.toEquiv.subsingleton)
    obtain ⟨x, y, hxy⟩ := hnt
    exact hxy (hX.eq_of_src x y)
  obtain ⟨Q, hQ, rfl⟩ : ∃ Q : Ideal (S ⧸ I), Q.IsPrime ∧ Q.comap (Ideal.Quotient.mk I) = P :=
    ⟨P.map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
      Ideal.comap_map_mk hIP⟩
  obtain ⟨hdualP, hconcP⟩ := isDualizingComplex_localizedModuleFunctor_single S ω hω
    (Q.comap (Ideal.Quotient.mk I))
  obtain ⟨hNnt, hdepth, hsupp⟩ := localizedModule_quotient_depth_supportDim S I Q
  have : Nontrivial ((ModuleCat.localizedModuleFunctor.{u}
      (Q.comap (Ideal.Quotient.mk I)).primeCompl).obj (ModuleCat.of S (S ⧸ I))) :=
    eM.toEquiv.nontrivial
  have : Module.Finite (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))
      ((ModuleCat.localizedModuleFunctor.{u}
        (Q.comap (Ideal.Quotient.mk I)).primeCompl).obj (ModuleCat.of S (S ⧸ I))) :=
    Module.Finite.equiv eM.symm
  obtain ⟨dQ, hdQ⟩ := exists_ringKrullDim_eq_natCast_of_isLocalRing (Localization.AtPrime Q)
  have hsupp' : Module.supportDim (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))
      ((ModuleCat.localizedModuleFunctor.{u}
        (Q.comap (Ideal.Quotient.mk I)).primeCompl).obj (ModuleCat.of S (S ⧸ I))) = dQ := by
    exact (Module.supportDim_eq_of_equiv eM).trans (hsupp.trans hdQ.symm)
  have hCMM : Module.IsCohenMacaulayAtMaximalIdeal
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))
      ((ModuleCat.localizedModuleFunctor.{u}
        (Q.comap (Ideal.Quotient.mk I)).primeCompl).obj (ModuleCat.of S (S ⧸ I))) := by
    show (Module.depth _ _ _ : WithBot ℕ∞) = _
    rw [hsupp', Module.depth_eq_depth_of_linearEquiv _ eM, hdepth, hdQ]
    exact hCM Q
  have hdR : ringKrullDim (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))) =
      ((dQ + c : ℕ) : WithBot ℕ∞) := by
    rw [hdim Q, ← hdQ]
    push_cast
    rfl
  have := eq_of_nontrivial_ext_of_isCohenMacaulayAtMaximalIdeal _ hdualP 0 hconcP
    ((ModuleCat.localizedModuleFunctor.{u}
        (Q.comap (Ideal.Quotient.mk I)).primeCompl).obj (ModuleCat.of S (S ⧸ I)))
    hCMM (dQ + c) dQ hdR hsupp' j hnt
  push_cast at this
  omega

/-- A dualizing module may be placed in degree zero: if `ω` placed in some degree is a dualizing
complex, so is `ω` placed in degree zero. -/
theorem isDualizingComplex_singleFunctor_zero_of_isDualizingRingModule (S : Type u) [CommRing S]
    [IsNoetherianRing S] (ω : ModuleCat.{u} S) (hω : Stacks.Duality.IsDualizingRingModule S ω) :
    IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω) := by
  obtain ⟨-, n, hn⟩ := hω
  exact (isDualizingComplex_iff_of_iso
    (((DerivedCategory.singleFunctors (ModuleCat.{u} S)).shiftIso n 0 n (by omega)).app ω)).mp
      (isDualizingComplex_shift _ hn n)

/-- **The dualizing complex `RHom_S(S ⧸ I, ω)` is a dualizing module in degree `c`, explicitly.**
In the situation of `Dualizing.extQuotient_concentration`, write
`L = RHom_S(S ⧸ I, ω) = (Dualizing.derivedHom (Ideal.Quotient.mk I)).obj ω[0]`, the dualizing
complex over `S ⧸ I` of [Stacks, Tag 0AX0]. Then `H^i(L) = 0` for `i ≠ c`, the module `H^c(L)` is a
dualizing module over `S ⧸ I`, and read over `S` it is `Ext^c_S(S ⧸ I, ω)`. -/
theorem extQuotient_concentration_derivedHom (S : Type u) [CommRing S] [IsNoetherianRing S]
    (ω : ModuleCat.{u} S) (hω : Stacks.Duality.IsDualizingRingModule S ω) (I : Ideal S) (c : ℕ)
    (hCM : IsCohenMacaulayRing (S ⧸ I))
    (hdim : ∀ (Q : Ideal (S ⧸ I)) [Q.IsPrime],
      ringKrullDim (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))) =
        ringKrullDim (Localization.AtPrime Q) + c) :
    (∀ i : ℤ, i ≠ c → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (S ⧸ I)) i).obj
        ((derivedHom.{u, u, u} (Ideal.Quotient.mk I)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω)))) ∧
      Stacks.Duality.IsDualizingRingModule (S ⧸ I)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (S ⧸ I)) c).obj
          ((derivedHom.{u, u, u} (Ideal.Quotient.mk I)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω))) ∧
      Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (S ⧸ I)) c).obj
            ((derivedHom.{u, u, u} (Ideal.Quotient.mk I)).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω))) ≃ₗ[S]
        Abelian.Ext (ModuleCat.of S (S ⧸ I)) ω c) := by
  let f := Ideal.Quotient.mk I
  let K0 := (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj ω
  have hK0 : IsDualizingComplex K0 :=
    isDualizingComplex_singleFunctor_zero_of_isDualizingRingModule S ω hω
  let L := (derivedHom.{u, u, u} f).obj K0
  have hL : IsDualizingComplex L :=
    isDualizingComplex_derivedHom_of_finite.{u, u} f
      (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) K0 hK0
  let eSource : (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj
        ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of (S ⧸ I) (ULift.{u} (S ⧸ I)))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S (S ⧸ I)) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).mapIso
      (uliftRestrictLinearEquiv (R := S) (A := S ⧸ I)).toModuleIso
  let E : ∀ i : ℤ, ((ModuleCat.restrictScalars.{u} f).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (S ⧸ I)) i).obj L)) ≃ₗ[S]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S (S ⧸ I))) K0 i :=
    fun i => (derivedHomHomologyLinearEquivExtStandard f K0 i).trans
      (Linear.homCongr S eSource (Iso.refl _))
  have hzero : ∀ i : ℤ, i ≠ c →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (S ⧸ I)) i).obj L) := by
    intro i hi
    refine ModuleCat.isZero_iff_subsingleton.mpr ?_
    have := subsingleton_ext_quotient_of_ne S ω hK0 I c hCM hdim i hi
    exact (E i).toEquiv.subsingleton
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero L c hzero
  refine ⟨hzero, ⟨hL.finiteCohomology c, c, (isDualizingComplex_iff_of_iso e).mp hL⟩,
    ⟨(E c).trans (Abelian.Ext.homLinearEquiv (R := S)).symm⟩⟩

/-- **`Ext` out of a Cohen--Macaulay quotient into a dualizing module is concentrated in the
codimension, and there it is a dualizing module of the quotient.** Let `S` be a Noetherian ring
with a dualizing module `ω`, and `I ⊂ S` an ideal such that `S ⧸ I` is Cohen--Macaulay and
`dim S_P = dim (S ⧸ I)_P + c` at every prime `P ⊇ I` (the hypothesis is indexed by the primes `Q`
of `S ⧸ I`, with `P = Q.comap (Ideal.Quotient.mk I)`). Then `Ext^j_S(S ⧸ I, ω) = 0` for `j ≠ c`,
and `Ext^c_S(S ⧸ I, ω)` carries a structure of `S ⧸ I`-module which is a dualizing module over
`S ⧸ I`.

The `S ⧸ I`-module is `H^c(RHom_S(S ⧸ I, ω))`, the only nonzero cohomology module of the
dualizing complex of [Stacks, Tag 0AX0]; see `Dualizing.extQuotient_concentration_derivedHom`. -/
theorem extQuotient_concentration (S : Type u) [CommRing S] [IsNoetherianRing S]
    (ω : ModuleCat.{u} S) (hω : Stacks.Duality.IsDualizingRingModule S ω) (I : Ideal S) (c : ℕ)
    (hCM : IsCohenMacaulayRing (S ⧸ I))
    (hdim : ∀ (Q : Ideal (S ⧸ I)) [Q.IsPrime],
      ringKrullDim (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))) =
        ringKrullDim (Localization.AtPrime Q) + c) :
    (∀ j : ℕ, j ≠ c → Subsingleton (Abelian.Ext (ModuleCat.of S (S ⧸ I)) ω j)) ∧
    ∃ ωC : ModuleCat.{u} (S ⧸ I), Stacks.Duality.IsDualizingRingModule (S ⧸ I) ωC ∧
      Nonempty ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj ωC ≃ₗ[S]
        Abelian.Ext (ModuleCat.of S (S ⧸ I)) ω c) := by
  obtain ⟨-, hdual, hext⟩ := extQuotient_concentration_derivedHom S ω hω I c hCM hdim
  refine ⟨fun j hj => ?_, _, hdual, hext⟩
  have := subsingleton_ext_quotient_of_ne S ω
    (isDualizingComplex_singleFunctor_zero_of_isDualizingRingModule S ω hω) I c hCM hdim j
    (by exact_mod_cast hj)
  exact (Abelian.Ext.homLinearEquiv (R := S)).toEquiv.subsingleton

end Dualizing

end
