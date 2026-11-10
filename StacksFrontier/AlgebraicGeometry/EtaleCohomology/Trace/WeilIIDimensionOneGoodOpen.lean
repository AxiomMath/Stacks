module

public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.Curves.AffineLineBasicOpenCurve
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleOpenAffineLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveCompactSupportFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionOne
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.NoetherianCase

/-!
# Weil II in dimension at most one

Every nonempty scheme `Z` of dimension at most one, separated of finite type over a finite field
`k`, has a nonempty open subscheme satisfying the weight bound of Weil II; this is
`Stacks.EtaleCohomology.LAdicSheaf.exists_open_satisfiesWeightBound_of_topologicalKrullDim_le_one`.
An affine open `Spec R` inside one irreducible component has `A = R_red` a domain of finite type
over `k`. If `dim A = 0`, `Spec A ⟶ Spec R` is a surjective closed immersion from a scheme of
dimension zero. If `dim A = 1`, there are `a ∈ A` and a finite étale `Spec A_a ⟶ D(g) ⊆ 𝔸¹_k`
(`Stacks.GenericFiniteEtale.exists_finite_etale_specAway`); the weight bound on `D(g)` (the curve
case on opens of the affine line) passes to `Spec A_a` along the finite étale map and then to the
open `Spec R_ã ⊆ Z` for a lift `ã` of `a`, of which `Spec A_a` is a surjective closed subscheme.
Noetherian induction
(`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_forall_exists_open`) then gives the
weight bound on every scheme of dimension at most one
(`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_topologicalKrullDim_le_one`).

The curve case on opens of the affine line,
`Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine`, is carried as a hypothesis; the
finiteness of the cohomology in dimension at most one is
`Stacks.EtaleCohomology.LAdicSheaf.hasFiniteCompactSupportCohomology_of_topologicalKrullDim_le_one`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  (k : Type u) [Field k] [Fintype k]

variable {B ℓ k} {kbar : Type u} [Field kbar] [Algebra k kbar]
  {p q : ℕ} [Fact p.Prime] [CharP k p] {hcard : Fintype.card k = p ^ q} {ι : ℚ_[ℓ] →+* ℂ}

/-- A surjective ring map with nil kernel induces a surjection on spectra. -/
theorem surjective_specMap_base_of_ker_le_nilradical {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hs : Function.Surjective φ) (hk : RingHom.ker φ.hom ≤ nilradical R) :
    Function.Surjective (Spec.map φ).base := by
  intro x
  have h : x ∈ Set.range (PrimeSpectrum.comap φ.hom) := by
    rw [range_comap_of_surjective _ φ.hom hs]
    exact hk.trans (nilradical_le_prime x.asIdeal)
  exact h

/-- **A nonempty open of `Z` with the weight bound, from a surjective closed subscheme of an
affine open.**  If `o : Spec R ⟶ Z` is an open immersion with `R ≠ 0` and `φ : R ⟶ A` is
surjective with nil kernel, the weight bound on `Spec A` gives the weight bound on the open
`Spec R` of `Z`. -/
theorem LAdicSheaf.exists_open_satisfiesWeightBound_of_specMap {Z : B.Scheme}
    [IsNoetherian Z.1] (fZ : Z.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fZ] [QuasiCompact fZ]
    [IsSeparated fZ] {R A : CommRingCat.{u}} [Nontrivial R] (o : Spec R ⟶ Z.1)
    [IsOpenImmersion o] (φ : R ⟶ A) (hs : Function.Surjective φ)
    (hk : RingHom.ker φ.hom ≤ nilradical R)
    (hfin : ∀ (Y : B.Scheme) [IsNoetherian Y.1] (g : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType g]
      [QuasiCompact g] [IsSeparated g], topologicalKrullDim Y.1 ≤ topologicalKrullDim Z.1 →
        LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Y g)
    (hA : ∀ (hB : B.Contains (Spec A)) [IsNoetherian (Spec A)]
      [LocallyOfFiniteType (Spec.map φ ≫ o ≫ fZ)] [QuasiCompact (Spec.map φ ≫ o ≫ fZ)]
      [IsSeparated (Spec.map φ ≫ o ≫ fZ)],
      LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι (B.obj (Spec A) hB)
        (Spec.map φ ≫ o ≫ fZ)) :
    ∃ (U : B.Scheme) (_ : IsNoetherian U.1) (jU : U ⟶ Z)
      (_ : IsOpenImmersion (B.inclusion.map jU)) (_ : QuasiCompact (B.inclusion.map jU ≫ fZ)),
      Nonempty U.1 ∧ LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U
        (B.inclusion.map jU ≫ fZ) := by
  have hU : B.Contains (Spec R) :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit o Z.property
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hs
  have hA' : B.Contains (Spec A) :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit (Spec.map φ) hU
  have : IsLocallyNoetherian Z.1 := ‹AlgebraicGeometry.IsNoetherian Z.1›.toIsLocallyNoetherian
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion o
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.1 inferInstance
  have : IsNoetherianRing A := isNoetherianRing_of_surjective R A φ.hom hs
  let U : B.Scheme := B.obj (Spec R) hU
  let jU : U ⟶ Z := ObjectProperty.homMk o
  let U' : B.Scheme := B.obj (Spec A) hA'
  let iU : U' ⟶ U := ObjectProperty.homMk (Spec.map φ)
  have : IsNoetherian U.1 := inferInstanceAs (IsNoetherian (Spec R))
  have : IsNoetherian U'.1 := inferInstanceAs (IsNoetherian (Spec A))
  have : IsOpenImmersion (B.inclusion.map jU) := ‹IsOpenImmersion o›
  have : IsClosedImmersion (B.inclusion.map iU) := ‹IsClosedImmersion (Spec.map φ)›
  have hqc : QuasiCompact (o ≫ fZ) :=
    (quasiCompact_iff_compactSpace (o ≫ fZ)).2 (inferInstance : CompactSpace (Spec R))
  have : QuasiCompact (B.inclusion.map jU ≫ fZ) := hqc
  have : LocallyOfFiniteType (B.inclusion.map jU ≫ fZ) :=
    inferInstanceAs (LocallyOfFiniteType (o ≫ fZ))
  have : IsSeparated (B.inclusion.map jU ≫ fZ) := inferInstanceAs (IsSeparated (o ≫ fZ))
  have : LocallyOfFiniteType (Spec.map φ ≫ o ≫ fZ) := inferInstance
  have : QuasiCompact (Spec.map φ ≫ o ≫ fZ) := inferInstance
  have : IsSeparated (Spec.map φ ≫ o ≫ fZ) := inferInstance
  have : LocallyOfFiniteType (B.inclusion.map iU ≫ B.inclusion.map jU ≫ fZ) :=
    inferInstanceAs (LocallyOfFiniteType (Spec.map φ ≫ o ≫ fZ))
  have : QuasiCompact (B.inclusion.map iU ≫ B.inclusion.map jU ≫ fZ) :=
    inferInstanceAs (QuasiCompact (Spec.map φ ≫ o ≫ fZ))
  have : IsSeparated (B.inclusion.map iU ≫ B.inclusion.map jU ≫ fZ) :=
    inferInstanceAs (IsSeparated (Spec.map φ ≫ o ≫ fZ))
  refine ⟨U, inferInstance, jU, inferInstance, inferInstance,
    inferInstanceAs (Nonempty (Spec R)), ?_⟩
  exact LAdicSheaf.satisfiesWeightBound_of_surjective (B.inclusion.map jU ≫ fZ) iU
    (surjective_specMap_base_of_ker_le_nilradical φ hs hk)
    (hfin _ _ (o.isOpenEmbedding.isInducing.comp
      (Spec.map φ).isClosedEmbedding.isInducing).topologicalKrullDim_le) ((hA hA').congr rfl)

/-- An element of `WithBot ℕ∞` which is at most one is at most zero or equal to one. -/
theorem le_zero_or_eq_one_of_le_one {d : WithBot ℕ∞} (hd : d ≤ 1) : d ≤ 0 ∨ d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact Or.inl bot_le
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd hd (by decide)
    | coe m =>
      have hm : m ≤ 1 := by exact_mod_cast hd
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)

/-- **The kernel of `R_b ⟶ (R_red)_b̄` is nil** when `R_red` is a domain and `b̄ ≠ 0`. -/
theorem ker_le_nilradical_localizationAway_map {R : Type u} [CommRing R]
    [(nilradical R).IsPrime] (b : R) (hb : Ideal.Quotient.mk (nilradical R) b ≠ 0) :
    RingHom.ker (IsLocalization.map (M := Submonoid.powers b)
      (Localization.Away (Ideal.Quotient.mk (nilradical R) b))
      (Ideal.Quotient.mk (nilradical R)) (Submonoid.powers b).le_comap_map :
        Localization.Away b →+* Localization.Away (Ideal.Quotient.mk (nilradical R) b)) ≤
      nilradical (Localization.Away b) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers b) x
  rw [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨m, hm⟩, hmr⟩ := hx
  obtain ⟨j, ⟨i, rfl⟩, rfl⟩ := hm
  have hr : Ideal.Quotient.mk (nilradical R) r = 0 := by
    simpa [map_pow, pow_ne_zero i hb] using hmr
  rw [Ideal.Quotient.eq_zero_iff_mem] at hr
  obtain ⟨N, hN⟩ := hr
  refine ⟨N, Ideal.mem_bot.2 ?_⟩
  rw [← IsLocalization.mk'_pow, Ideal.mem_bot.1 hN, IsLocalization.mk'_zero]

/-- **A good open in dimension at most one.**  Every nonempty scheme `Z` of dimension at most one,
separated of finite type over `k`, has a nonempty open subscheme satisfying the weight bound:
take an affine open `Spec R` inside one irreducible component, so that `A = R_red` is a domain of
finite type over `k` of dimension `≤ 1`. In dimension zero `Spec A ⟶ Spec R` is a surjective
closed immersion from a scheme of dimension zero. In dimension one there is a finite étale
`Spec A_a ⟶ D(g) ⊆ 𝔸¹_k`; the weight bound on `D(g)` is the curve case on opens of the affine
line, it passes to `Spec A_a` along the finite étale map, and from `Spec A_a` to the open
`Spec R_b` of `Z`, for a lift `b` of `a`, along the surjective closed immersion
`Spec A_a ⟶ Spec R_b`. -/
theorem LAdicSheaf.exists_open_satisfiesWeightBound_of_topologicalKrullDim_le_one
    [IsAlgClosure k kbar] (hcurve : WeilIICurveBoundOpenAffineLine.{u}) (hℓ : ℓ ≠ p)
    (hfin : ∀ (Y : B.Scheme) [IsNoetherian Y.1] (g : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType g]
      [QuasiCompact g] [IsSeparated g], topologicalKrullDim Y.1 ≤ 1 →
        LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Y g)
    {Z : B.Scheme} [IsNoetherian Z.1] (fZ : Z.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fZ]
    [QuasiCompact fZ] [IsSeparated fZ] (hdim : topologicalKrullDim Z.1 ≤ 1) (hne : Nonempty Z.1) :
    ∃ (U : B.Scheme) (_ : IsNoetherian U.1) (jU : U ⟶ Z)
      (_ : IsOpenImmersion (B.inclusion.map jU)) (_ : QuasiCompact (B.inclusion.map jU ≫ fZ)),
      Nonempty U.1 ∧ LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι U
        (B.inclusion.map jU ≫ fZ) := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  -- an affine open `Spec R` inside one irreducible component
  obtain ⟨z⟩ := hne
  obtain ⟨o, ho, ⟨x, hx⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent z) (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨R, e, he, ⟨y, -⟩, hes⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨o, ho⟩) hx
  have := he
  have hirr : IrreducibleSpace (PrimeSpectrum R) := by
    have hpre : IsPreirreducible (e.base ⁻¹' irreducibleComponent z) :=
      isIrreducible_irreducibleComponent.isPreirreducible.preimage e.isOpenEmbedding
    have huniv : e.base ⁻¹' irreducibleComponent z = Set.univ :=
      Set.eq_univ_of_forall fun t => hoC (hes ⟨t, rfl⟩)
    rw [huniv] at hpre
    exact { isPreirreducible_univ := hpre, toNonempty := ⟨y⟩ }
  have hprime : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 hirr
  have : Nontrivial R := ⟨⟨0, 1, fun h => hprime.ne_top
    ((Ideal.eq_top_iff_one _).2 (h ▸ (nilradical R).zero_mem))⟩⟩
  -- the `k`-algebra `R` and its reduction `A`
  let φ0 : CommRingCat.of k ⟶ R := Spec.preimage (e ≫ fZ)
  have hφ0 : Spec.map φ0 = e ≫ fZ := Spec.map_preimage _
  let : Algebra k R := φ0.hom.toAlgebra
  have : Algebra.FiniteType k R := by
    have h : LocallyOfFiniteType (Spec.map φ0) := by rw [hφ0]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  have : IsDomain (R ⧸ nilradical R) := Ideal.Quotient.isDomain _
  have : Algebra.FiniteType k (R ⧸ nilradical R) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (nilradical R))
      (Ideal.Quotient.mkₐ_surjective k _)
  have hdimA : ringKrullDim (R ⧸ nilradical R) ≤ 1 := by
    refine (ringKrullDim_quotient_le _).trans ?_
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact e.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  rcases le_zero_or_eq_one_of_le_one hdimA with h0 | h1
  · -- dimension zero: `Spec A ⟶ Spec R` is a surjective closed immersion
    refine LAdicSheaf.exists_open_satisfiesWeightBound_of_specMap fZ e
      (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R))) Ideal.Quotient.mk_surjective
      (by rw [CommRingCat.hom_ofHom, Ideal.mk_ker]) (fun Y _ g _ _ _ hY => hfin Y g (hY.trans hdim))
      fun hB _ _ _ _ => ?_
    have h0' : topologicalKrullDim (Spec (.of (R ⧸ nilradical R))) ≤ 0 :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R ⧸ nilradical R)).le.trans h0
    exact LAdicSheaf.satisfiesWeightBound_of_topologicalKrullDim_le_zero _ _ h0'
      fun Y _ g _ _ _ hY => hfin Y g (hY.trans (h0'.trans zero_le_one))
  · -- dimension one: `Spec A_a` is finite étale over `D(g) ⊆ 𝔸¹_k`
    obtain ⟨a, ha, g, hg, π, hπf, hπe, hπk, -⟩ :=
      Stacks.GenericFiniteEtale.exists_finite_etale_specAway k (R ⧸ nilradical R) h1
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : IsLocalization ((Submonoid.powers b).map (Ideal.Quotient.mk (nilradical R)))
        (Localization.Away (Ideal.Quotient.mk (nilradical R) b)) := by
      rw [Submonoid.map_powers]; infer_instance
    let φ : Localization.Away b →+* Localization.Away (Ideal.Quotient.mk (nilradical R) b) :=
      IsLocalization.map (M := Submonoid.powers b)
        (Localization.Away (Ideal.Quotient.mk (nilradical R) b))
        (Ideal.Quotient.mk (nilradical R)) (Submonoid.powers b).le_comap_map
    have hφs : Function.Surjective φ :=
      IsLocalization.map_surjective_of_surjective (Submonoid.powers b) _ _
        Ideal.Quotient.mk_surjective
    have : IsDomain (Localization.Away (Ideal.Quotient.mk (nilradical R) b)) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
    have : Nontrivial (Localization.Away b) := hφs.nontrivial
    refine LAdicSheaf.exists_open_satisfiesWeightBound_of_specMap fZ
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b))) ≫ e)
      (CommRingCat.ofHom φ) hφs (ker_le_nilradical_localizationAway_map b ha)
      (fun Y _ g _ _ _ hY => hfin Y g (hY.trans hdim)) fun hB _ _ _ _ => ?_
    -- the open `D(g)` of the affine line
    have hVB : B.Contains (Spec (.of (Localization.Away g))) := by
      have hk : (Spec (.of k)).size < B.cutoff := by
        rw [Scheme.size_Spec]
        exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)
      exact Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
        (Submonoid.powers g) _ (Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
          B.cutoff_isStrongPrelimit k k[X] hk)
    let V : B.Scheme := B.obj (Spec (.of (Localization.Away g))) hVB
    let fV : V.1 ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g)))
    have := Stacks.GenericFiniteEtale.isDomain_away k hg
    have : IsNoetherianRing (Localization.Away g) :=
      IsLocalization.isNoetherianRing (Submonoid.powers g) _ inferInstance
    have : IsNoetherian V.1 := inferInstanceAs (IsNoetherian (Spec (.of (Localization.Away g))))
    have : ConnectedSpace V.1 := inferInstanceAs (ConnectedSpace (PrimeSpectrum _))
    have : SmoothOfRelativeDimension 1 fV :=
      Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_away k g
    have : Smooth fV := SmoothOfRelativeDimension.smooth 1 fV
    have : IsCurve k fV := Stacks.GenericFiniteEtale.isCurve_specMap_away k hg
    have : ConnectedSpace ↥(pullback fV (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) :=
      Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_away k hg kbar
    have heV : Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away g))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k[X])) = fV := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    obtain ⟨v⟩ : Nonempty V.1 := inferInstanceAs (Nonempty (PrimeSpectrum _))
    have hV := LAdicSheaf.satisfiesWeightBound_of_weilIICurveBoundOpenAffineLine (B := B)
      (ℓ := ℓ) (kbar := kbar) (hcard := hcard) (ι := ι) hcurve V fV _ heV hℓ
      (Stacks.Etale.ofPoint v)
    -- the finite étale cover `Spec A_a ⟶ D(g)`
    let U' : B.Scheme :=
      B.obj (Spec (.of (Localization.Away (Ideal.Quotient.mk (nilradical R) b)))) hB
    let πB : U' ⟶ V := ObjectProperty.homMk π
    have : IsFinite (B.inclusion.map πB) := hπf
    have : Etale (B.inclusion.map πB) := hπe
    have hirr' : IrreducibleSpace
        (PrimeSpectrum (Localization.Away (Ideal.Quotient.mk (nilradical R) b))) :=
      PrimeSpectrum.irreducibleSpace
    have : ConnectedSpace U'.1 := IrreducibleSpace.connectedSpace
      (PrimeSpectrum (Localization.Away (Ideal.Quotient.mk (nilradical R) b)))
    have : LocallyOfFiniteType (B.inclusion.map πB ≫ fV) :=
      inferInstanceAs (LocallyOfFiniteType (π ≫ fV))
    have : QuasiCompact (B.inclusion.map πB ≫ fV) := inferInstanceAs (QuasiCompact (π ≫ fV))
    have : IsSeparated (B.inclusion.map πB ≫ fV) := inferInstanceAs (IsSeparated (π ≫ fV))
    obtain ⟨jV, -⟩ := hasCompactification_of_isNoetherian fV
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
      IsClosedImmersion.spec_of_surjective _ hφs
    have hdU' : topologicalKrullDim U'.1 ≤ 1 :=
      (((e.isOpenEmbedding.isInducing.comp (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away b)))).isOpenEmbedding.isInducing).comp
          (Spec.map
            (CommRingCat.ofHom φ)).isClosedEmbedding.isInducing).topologicalKrullDim_le).trans
        hdim
    have hU' := LAdicSheaf.satisfiesWeightBound_of_finite_etale fV πB jV (hfin _ _ hdU') hV
    refine hU'.congr ?_
    change π ≫ fV = _
    rw [hπk]
    simp only [Category.assoc]
    rw [← hφ0, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext c
    change algebraMap k _ c = φ (algebraMap R (Localization.Away b) (φ0.hom c))
    rw [IsLocalization.map_eq, IsScalarTower.algebraMap_apply k (R ⧸ nilradical R)
      (Localization.Away (Ideal.Quotient.mk (nilradical R) b))]
    rfl

/-- **The weight bound of Weil II in dimension at most one**: noetherian induction on the closed
subschemes, each of which has a nonempty open with the weight bound; the cohomology groups are
finite in dimension at most one. -/
theorem LAdicSheaf.satisfiesWeightBound_of_topologicalKrullDim_le_one [IsAlgClosure k kbar]
    (hcurve : WeilIICurveBoundOpenAffineLine.{u}) (hℓ : ℓ ≠ p)
    (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] (hdim : topologicalKrullDim X.1 ≤ 1) :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have hfin : ∀ (Y : B.Scheme) [IsNoetherian Y.1] (g : Y.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g], topologicalKrullDim Y.1 ≤ 1 →
      LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Y g := fun Y _ g _ _ _ hY =>
    LAdicSheaf.hasFiniteCompactSupportCohomology_of_topologicalKrullDim_le_one B ℓ kbar p q hcard Y
      g hY
  exact LAdicSheaf.satisfiesWeightBound_of_forall_exists_open X f
    (fun Y _ g _ _ _ hY => hfin Y g (hY.trans hdim)) fun _ _ iZ _ hZ => by
    have hfinZ : IsFinite (B.inclusion.map iZ) := inferInstance
    have : LocallyOfFiniteType (B.inclusion.map iZ) :=
      ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp hfinZ).2
    have : LocallyOfFiniteType (B.inclusion.map iZ ≫ f) := inferInstance
    exact LAdicSheaf.exists_open_satisfiesWeightBound_of_topologicalKrullDim_le_one hcurve hℓ hfin
      (B.inclusion.map iZ ≫ f)
      ((B.inclusion.map iZ).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim) hZ

end Stacks.EtaleCohomology
