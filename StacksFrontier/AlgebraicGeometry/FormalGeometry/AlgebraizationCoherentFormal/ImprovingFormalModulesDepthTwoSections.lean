module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoSystem
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Support
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.CokernelDepthTwo
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AnnihilatorSheaf
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormulaGeneral
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
import all StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic

/-!
# Sections of a depth-two extension over an affine open

Let `X` be a Noetherian scheme, `T' ⊆ X` a subset and `φ : 𝒢' ⟶ 𝒢` a map of quasi-coherent
modules which is injective, an isomorphism on the stalks away from `T'`, and whose target has
depth at least two at the points of `T'`. Over an affine open `U` with ring `A₀ = Γ(X, U)` this
file reads these properties off the sections: `Γ(U, 𝒢') → Γ(U, 𝒢)` is injective, its cokernel
vanishes at the primes of `A₀` outside `T'`, and `Γ(U, 𝒢)` has depth at least two at the primes
in `T'`. So the short exact sequence of sections is a depth-two embedding in the sense of
`Stacks.LocalCohomology.IsDepthTwoEmbedding`, whose cokernel is `H¹_{T'}(Γ(U, 𝒢'))` by
`Stacks.LocalCohomology.cokernelNatIsoLocalCohomologyOne`. When `𝒢'` is annihilated by an ideal
power, so is `𝒢`.

These are the inputs, at the level of an affine open, of the identification
`ℳ''ₙ / ℳ'ₙ = H¹_{T'}(ℳ'ₙ)` in the proof of [Stacks, Tag 0EJF].

## Main results

* `Stacks.Algebraization.smul_top_eq_bot_of_localized_quotient_of_depth`: a finite module over a
  Noetherian ring which agrees with a submodule annihilated by `J` away from `T`, and has positive
  depth along `T`, is annihilated by `J`.
* `Stacks.Algebraization.subsingleton_localizedModule_quotient_range`: where a map of
  quasi-coherent modules is surjective on stalks, the cokernel of the map on sections over an
  affine open vanishes after localizing at the corresponding prime.
* `Stacks.Algebraization.isDepthTwoEmbedding_sections`: the sections over an affine open of a
  depth-two extension form a depth-two embedding.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

/-! ### A module-level annihilation criterion -/

/-- **Annihilation away from `T` plus positive depth along `T`.** Let `N` be a finite module over
a Noetherian ring with a submodule `N'` annihilated by `J`, such that `N/N'` vanishes at every
prime outside `T` and `N` has depth at least one at every prime of `T`. Then `N` is annihilated by
`J`: the submodule `J N` vanishes outside `T`, so all of its associated primes lie in `T`, where
`N` has none. -/
public theorem smul_top_eq_bot_of_localized_quotient_of_depth {R : Type u} [CommRing R]
    [IsNoetherianRing R] {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (T : Set (PrimeSpectrum R)) (J : Ideal R) (N' : Submodule R N) (hN' : J • N' = ⊥)
    (hsupp : ∀ p : PrimeSpectrum R, p ∉ T →
      Subsingleton (LocalizedModule p.asIdeal.primeCompl (N ⧸ N')))
    (hdepth : ∀ p : PrimeSpectrum R, p ∈ T →
      1 ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl N)) :
    J • (⊤ : Submodule R N) = ⊥ := by
  set K := J • (⊤ : Submodule R N)
  have hkill : ∀ p : PrimeSpectrum R, p ∉ T → ∀ k ∈ K, ∃ s ∉ p.asIdeal, s • k = 0 := by
    intro p hp k hk
    have hsub := hsupp p hp
    refine Submodule.smul_induction_on (p := fun k => ∃ s ∉ p.asIdeal, s • k = 0) hk ?_ ?_
    · intro a ha y _
      have h0 : LocalizedModule.mkLinearMap p.asIdeal.primeCompl (N ⧸ N')
          (Submodule.Quotient.mk y) = 0 := Subsingleton.elim _ _
      obtain ⟨⟨s, hs⟩, hsy⟩ := (IsLocalizedModule.eq_zero_iff (S := p.asIdeal.primeCompl)
        (f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl (N ⧸ N'))).1 h0
      refine ⟨s, hs, ?_⟩
      have hsy' : s • y ∈ N' := by
        have h1 : s • (Submodule.Quotient.mk y : N ⧸ N') = 0 := hsy
        rw [← Submodule.Quotient.mk_smul] at h1
        exact (Submodule.Quotient.mk_eq_zero _).1 h1
      have : a • (s • y) ∈ J • N' := Submodule.smul_mem_smul ha hsy'
      rw [hN'] at this
      rw [smul_comm]
      exact (Submodule.mem_bot R).1 this
    · rintro x y ⟨s, hs, hsx⟩ ⟨t, ht, hty⟩
      refine ⟨s * t, fun h => (p.isPrime.mem_or_mem h).elim hs ht, ?_⟩
      simp only [smul_add, mul_smul, smul_comm s t x, hsx, hty, smul_zero, add_zero]
  have hass : associatedPrimes R K = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun q hq => ?_
    have hqN : q ∈ associatedPrimes R N :=
      associatedPrimes.subset_of_injective (f := K.subtype) Subtype.val_injective hq
    by_cases hqT : (⟨q, hq.toIsPrime⟩ : PrimeSpectrum R) ∈ T
    · exact Stacks.LocalCohomology.notMem_associatedPrimes_of_one_le_depth ⟨q, hq.toIsPrime⟩
        (hdepth _ hqT) hqN
    · obtain ⟨k, hk⟩ := hq.eq_radical_colon
      obtain ⟨s, hs, hsk⟩ := hkill ⟨q, hq.toIsPrime⟩ hqT k.1 k.2
      have hsq : s ∈ q := by
        rw [hk]
        refine Ideal.le_radical (Submodule.mem_colon_singleton.2 ?_)
        rw [Submodule.mem_bot]
        exact Subtype.ext hsk
      exact hs hsq
  have : Subsingleton K := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact (associatedPrimes.nonempty R K).ne_empty hass
  exact (Submodule.eq_bot_iff _).2 fun k hk => congrArg Subtype.val
    (Subsingleton.elim (⟨k, hk⟩ : K) 0)

/-! ### From stalks to sections over an affine open -/

section Sections

variable {X : Scheme.{u}}

/-- The stalk map of a morphism of modules sends the germ of a section to the germ of its image. -/
private theorem stalkMapLinear_germ {F G : X.Modules} (f : F ⟶ G) {U : X.Opens} {x : X} (hx : x ∈ U)
    (z : Γ(F, U)) :
    AlgebraicGeometry.stalkMapLinear (R := X.presheaf) F.val G.val f.val x
        (F.presheaf.germ U x hx z) = G.presheaf.germ U x hx (f.app U z) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hx
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val) z

/-- **Surjectivity on a stalk kills the localized cokernel on sections.** For a map
`f : 𝒢' ⟶ 𝒢` of quasi-coherent modules, a point `x` of an affine open `U` at which `f` is
surjective on stalks, and `𝔭` the prime of `Γ(X, U)` corresponding to `x`, the localization at
`𝔭` of the cokernel of `Γ(U, 𝒢') → Γ(U, 𝒢)` vanishes. -/
public theorem subsingleton_localizedModule_quotient_range {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U)
    (hsurj : Function.Surjective
      (AlgebraicGeometry.stalkMapLinear (R := X.presheaf) F.val G.val f.val x)) :
    Subsingleton (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Γ(G, U) ⧸ LinearMap.range (Stacks.AlgebraicGeometry.QcohLimits.appₗ f U))) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let := Stacks.ModuleStalkSpecialization.stalkModule G x
  let : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    Stacks.ModuleStalkSpecialization.stalkModule F x
  let : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
    Stacks.ModuleStalkSpecialization.stalkModule G x
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule F hx
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule G hx
  have hF := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ F hU hx
  set p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  refine subsingleton_of_forall_eq 0 fun c => ?_
  induction c using LocalizedModule.induction_on with
  | h y s =>
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨w, hw⟩ := hsurj (G.presheaf.germ U x hx y)
    obtain ⟨⟨z, t⟩, hzt⟩ := IsLocalizedModule.surj p
      (Stacks.ModuleStalkSpecialization.germₗ F hx) w
    have hG := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ G hU hx
    have hgerm : Stacks.ModuleStalkSpecialization.germₗ G hx ((t : Γ(X, U)) • y) =
        Stacks.ModuleStalkSpecialization.germₗ G hx (f.app U z) := by
      rw [map_smul]
      show (X.presheaf.germ U x hx (t : Γ(X, U))) • G.presheaf.germ U x hx y = _
      rw [← hw]
      refine (@LinearMap.map_smul _ _ _ _ _ _
        (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x)
        (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x)
        (AlgebraicGeometry.stalkMapLinear (R := X.presheaf) F.val G.val f.val x)
        (X.presheaf.germ U x hx (t : Γ(X, U))) w).symm.trans ?_
      exact (congrArg (fun v => AlgebraicGeometry.stalkMapLinear (R := X.presheaf) F.val G.val
        f.val x v) hzt).trans (stalkMapLinear_germ f hx z)
    obtain ⟨⟨r, hr⟩, hrt⟩ := IsLocalizedModule.exists_of_eq (S := p) hgerm
    have hzero : (r * t : Γ(X, U)) • (Submodule.Quotient.mk y :
        Γ(G, U) ⧸ LinearMap.range (Stacks.AlgebraicGeometry.QcohLimits.appₗ f U)) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul]
      show r • ((t : Γ(X, U)) • y) ∈ _
      have hrt' : r • ((t : Γ(X, U)) • y) = r • f.app U z := hrt
      rw [hrt']
      exact ⟨r • z, by rw [map_smul]; rfl⟩
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨r * t, p.mul_mem hr t.2⟩, ?_⟩
    rw [smul_zero, smul_zero, smul_comm]
    exact (congrArg (s • ·) hzero).trans (smul_zero s)

/-- The set of primes of `Γ(X, U)` whose points lie in a given subset of `X`. -/
public def primesIn {U : X.Opens} (hU : IsAffineOpen U) (T : Set X) :
    Set (PrimeSpectrum Γ(X, U)) :=
  {p | hU.fromSpec p ∈ T}

/-- The image of a prime of `Γ(X, U)` under `hU.fromSpec` lies in `U`. -/
theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec p ∈ U :=
  AlgebraicGeometry.mem_of_fromSpec hU p

/-- The prime of `Γ(X, U)` attached to the point `hU.fromSpec p` of `U` is `p`. -/
theorem primeIdealOf_fromSpec_eq {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    hU.primeIdealOf ⟨hU.fromSpec p, fromSpec_mem hU p⟩ = p :=
  AlgebraicGeometry.primeIdealOf_fromSpec hU p

/-- `Stacks.Algebraization.subsingleton_localizedModule_quotient_range` at the point
`hU.fromSpec p`, localizing at the prime `p` itself. -/
private theorem subsingleton_localizedModule_quotient_range_fromSpec {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U))
    (hsurj : Function.Surjective
      (AlgebraicGeometry.stalkMapLinear (R := X.presheaf) F.val G.val f.val (hU.fromSpec p))) :
    Subsingleton (LocalizedModule p.asIdeal.primeCompl
      (Γ(G, U) ⧸ LinearMap.range (Stacks.AlgebraicGeometry.QcohLimits.appₗ f U))) := by
  have h := subsingleton_localizedModule_quotient_range f hU (fromSpec_mem hU p) hsurj
  rwa [primeIdealOf_fromSpec_eq hU p] at h

/-- The localization at a prime of the sections over an affine open has the depth of the stalk at
the corresponding point. -/
theorem depth_localizedModule_sections_eq {U : X.Opens} (hU : IsAffineOpen U) (G : X.Modules)
    [G.IsQuasicoherent] (p : PrimeSpectrum Γ(X, U)) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule G (hU.fromSpec p)
    Module.depth (Localization.AtPrime p.asIdeal) (IsLocalRing.maximalIdeal _)
        (LocalizedModule p.asIdeal.primeCompl Γ(G, U)) =
      Module.depth (X.presheaf.stalk (hU.fromSpec p))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (hU.fromSpec p)))
        (G.presheaf.stalk (hU.fromSpec p)) := by
  have h := Stacks.ModuleStalkSpecialization.depth_stalk_eq_depth_localizedModule G hU
    ⟨hU.fromSpec p, fromSpec_mem hU p⟩
  rw [primeIdealOf_fromSpec_eq hU p] at h
  exact h.symm

/-- The short complex of sections over an affine open of a map `φ : 𝒢' ⟶ 𝒢`, with the cokernel
on sections as third term. -/
public def sectionsShortComplex {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) :
    ShortComplex (ModuleCat.{u} Γ(X, U)) :=
  ShortComplex.mk (ModuleCat.ofHom (Stacks.AlgebraicGeometry.QcohLimits.appₗ φ U))
    (ModuleCat.ofHom (LinearMap.range (Stacks.AlgebraicGeometry.QcohLimits.appₗ φ U)).mkQ)
    (by
      ext s
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨s, rfl⟩)

/-- The sections of a monomorphism form a short exact sequence with the cokernel on sections. -/
theorem sectionsShortComplex_shortExact {F G : X.Modules} (φ : F ⟶ G) [Mono φ] (U : X.Opens) :
    (sectionsShortComplex φ U).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (Submodule.ker_mkQ _).symm
  mono_f := (ModuleCat.mono_iff_injective _).2 (injective_app_of_mono φ U)
  epi_g := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

/-- **The sections over an affine open of a depth-two extension form a depth-two embedding.**
Let `φ : 𝒢' ⟶ 𝒢` be a monomorphism of quasi-coherent modules which is an isomorphism on the stalks
away from `T'`, with `𝒢` of finite type and of depth at least two at the points of `T'`. Over an
affine open `U` the sequence `0 → Γ(U, 𝒢') → Γ(U, 𝒢) → Γ(U, 𝒢)/Γ(U, 𝒢') → 0` satisfies the
hypotheses of `Stacks.LocalCohomology.IsDepthTwoEmbedding` for the primes of `Γ(X, U)` lying in
`T'`. -/
public theorem isDepthTwoEmbedding_sections [IsLocallyNoetherian X] {T' : Set X}
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] [G.IsFiniteType] (φ : F ⟶ G)
    (hiso : ∀ x : X, x ∉ T' → Function.Bijective
      (AlgebraicGeometry.stalkMapLinear (R := X.presheaf) F.val G.val φ.val x))
    (hdepth : ∀ x : X, x ∈ T' →
      letI := Stacks.ModuleStalkSpecialization.stalkModule G x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (G.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Stacks.LocalCohomology.IsDepthTwoEmbedding.{u, u} (primesIn hU T')
      (sectionsShortComplex φ U) where
  finite := Stacks.AlgebraicGeometry.CoherentFinite.finite_sections G hU
  supp p hp := subsingleton_localizedModule_quotient_range_fromSpec φ hU p (hiso _ hp).2
  depth p hp := by
    show 2 ≤ Module.depth (Localization.AtPrime p.asIdeal) (IsLocalRing.maximalIdeal _)
      (LocalizedModule p.asIdeal.primeCompl Γ(G, U))
    exact (hdepth _ hp).trans_eq (depth_localizedModule_sections_eq hU G p).symm

/-- **A depth-two extension of a module annihilated by an ideal power is annihilated by it.** -/
public theorem idealPowerMultiple_eq_bot_of_depth_extension [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (k : ℕ) {T' : Set X}
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] [G.IsFiniteType] (φ : F ⟶ G)
    (hiso : ∀ x : X, x ∉ T' → Function.Bijective
      (AlgebraicGeometry.stalkMapLinear (R := X.presheaf) F.val G.val φ.val x))
    (hdepth : ∀ x : X, x ∈ T' →
      letI := Stacks.ModuleStalkSpecialization.stalkModule G x
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (G.presheaf.stalk x))
    (hF : idealPowerMultiple I k F = ⊥) : idealPowerMultiple I k G = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U a ha x => ?_
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := Stacks.AlgebraicGeometry.CoherentFinite.finite_sections G U.2
  have hann := smul_top_eq_bot_of_localized_quotient_of_depth (primesIn U.2 T') (I.ideal U ^ k)
    (LinearMap.range (Stacks.AlgebraicGeometry.QcohLimits.appₗ φ U.1)) ?_ ?_ ?_
  · have := Submodule.smul_mem_smul ha (Submodule.mem_top (x := x))
    rw [hann] at this
    exact (Submodule.mem_bot _).1 this
  · rw [LinearMap.range_eq_map, ← Submodule.map_smul'',
      affine_smul_top_eq_bot_of_idealPowerMultiple_eq_bot hF U, Submodule.map_bot]
  · exact fun p hp => subsingleton_localizedModule_quotient_range_fromSpec φ U.2 p (hiso _ hp).2
  · exact fun p hp => (hdepth _ hp).trans_eq (depth_localizedModule_sections_eq U.2 G p).symm

end Sections

/-! ### The canonical depth-two improvement -/

section Canonical

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
  (hdual : HasDualizingComplexOnAffineCover X) (F : Stacks.Coherent.CoherentAdicSystems I)
  {T T' : Set X} (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
  (hTY : T ⊆ I.support) (hTT' : T' ⊆ T)
  (himm : ∀ x x' : X, x ∈ I.support → IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)

/-- The terms of the depth-one quotient system are annihilated by the same powers of `ℐ` as those
of the coherent adic system. -/
theorem idealPowerMultiple_improvedSystem_eq_bot (n : ℕ) :
    idealPowerMultiple I (n + 1) ((improvedSystem T hT F.obj).obj (op n)) = ⊥ := by
  have hq := isDepthOneQuotient_toImprovedSystem_app T hT F.obj (op n)
  have : ((improvedSystem T hT F.obj).obj (op n)).IsCoherent := hq.1
  have : (F.obj.obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : ((improvedSystem T hT F.obj).obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : Epi ((toImprovedSystem T hT F.obj).app (op n)) := hq.2.1
  exact idealPowerMultiple_eq_bot_of_epi I (n + 1) ((toImprovedSystem T hT F.obj).app (op n))
    (F.property.2.1 n)

/-- The canonical depth-two extensions are isomorphisms on stalks away from `T'`, as linear maps
of stalks. -/
theorem bijective_stalkMapLinear_canonicalExtend (n : ℕᵒᵖ) (x : X) (hx : x ∉ T') :
    Function.Bijective (AlgebraicGeometry.stalkMapLinear (R := X.presheaf) _ _
      ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend n).val x) :=
  (ConcreteCategory.isIso_iff_bijective _).1
    (((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend_isDepthTwoExtension n).2.1
      x hx)

/-- **The terms of the improved system are annihilated by `ℐ^{n+1}`.** -/
public theorem idealPowerMultiple_canonicalImprovedSystem_eq_bot (n : ℕ) :
    idealPowerMultiple I (n + 1) ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj (op n)) =
      ⊥ := by
  set S := canonicalDepthTwoImprovement hdual F hT hT' hTY himm
  have hq := isDepthOneQuotient_toImprovedSystem_app T hT F.obj (op n)
  have : ((improvedSystem T hT F.obj).obj (op n)).IsCoherent := hq.1
  have : ((improvedSystem T hT F.obj).obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hc : _root_.SheafOfModules.IsCoherent.{u}
      ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj (op n)) :=
    (S.extend_isDepthTwoExtension (op n)).1
  have : ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj (op n)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : ((canonicalImprovedSystem hdual F hT hT' hTY himm).obj (op n)).IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).2
  exact idealPowerMultiple_eq_bot_of_depth_extension I (n + 1) (S.extend (op n))
    (bijective_stalkMapLinear_canonicalExtend hdual F hT hT' hTY himm (op n))
    (fun x hx => le_trans (by norm_num) ((S.extend_isDepthTwoExtension (op n)).2.2 x hx))
    (idealPowerMultiple_improvedSystem_eq_bot F hT n)

include hTT' in
/-- **The canonical depth-two extensions are monomorphisms**: a map out of a depth-one quotient
along `T` which is an isomorphism on the stalks away from `T` is a monomorphism. -/
public theorem mono_canonicalExtend (n : ℕᵒᵖ) :
    Mono ((canonicalDepthTwoImprovement hdual F hT hT' hTY himm).extend n) := by
  set S := canonicalDepthTwoImprovement hdual F hT hT' hTY himm
  have : (S.term n).IsCoherent := (S.extend_isDepthTwoExtension n).1
  exact mono_of_depthOneQuotient_source _ (isDepthOneQuotient_toImprovedSystem_app T hT F.obj n)
    (S.extend n) fun x hx => (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_stalkMapLinear_canonicalExtend hdual F hT hT' hTY himm n x fun h => hx (hTT' h))

include hTT' in
/-- **The terms of the improved system vanish off the support of `ℐ`.** -/
public theorem subsingleton_stalk_canonicalImprovedSystem_of_notMem_support (n : ℕᵒᵖ) (x : X)
    (hx : x ∉ I.support) :
    Subsingleton (((canonicalImprovedSystem hdual F hT hT' hTY himm).obj n).presheaf.stalk x) := by
  set S := canonicalDepthTwoImprovement hdual F hT hT' hTY himm
  have hbij := bijective_stalkMapLinear_canonicalExtend hdual F hT hT' hTY himm n x
    fun h => hx (hTY (hTT' h))
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((toImprovedSystem T hT F.obj).app n).mapPresheaf) :=
    (isDepthOneQuotient_toImprovedSystem_app T hT F.obj n).2.2.1 x fun h => hx (hTY h)
  have hsurj := ((ConcreteCategory.isIso_iff_bijective _).1 hiso).2
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hbij.2 a
  obtain ⟨b', rfl⟩ := hbij.2 b
  obtain ⟨a'', rfl⟩ := hsurj a'
  obtain ⟨b'', rfl⟩ := hsurj b'
  rw [eq_zero_stalk_of_notMem_support F hx n.unop a'',
    eq_zero_stalk_of_notMem_support F hx n.unop b'']

end Canonical

end Stacks.Algebraization

end
