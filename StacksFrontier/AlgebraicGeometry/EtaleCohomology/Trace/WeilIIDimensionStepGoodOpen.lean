module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionOneGoodOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStep
public import StacksFrontier.AlgebraicGeometry.F6Rank89.RegularSurfaceWitness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteEtaleOpenAffineSpace
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# The good open of the induction step of Weil II

In the step `S(n) → S(n + 1)` (`n ≥ 1`) of the induction on the dimension in the weight bound of
Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3), every
nonempty scheme `Z` of dimension `≤ n + 1` separated of finite type over `k`, and every lisse,
pointwise mixed, realizable sheaf `G` on `Z`, have a nonempty open `U ⊆ Z` on which `G` satisfies
the weight bound: take an affine open `Spec R` inside one irreducible component and `A = R_red`.
If `dim A ≤ n`, the weight bound in dimension `n` holds on `Spec A`, a surjective closed subscheme
of `Spec R`. If `dim A = n + 1`, an open `Spec A_a` is finite étale over an open `D(f)` of
`𝔸ⁿ⁺¹_k = 𝔸¹_{𝔸ⁿ}`, so that the projection `g : Spec A_a ⟶ 𝔸ⁿ` is affine and smooth of relative
dimension one; over a basic open `D(h)` of `𝔸ⁿ` on which all `Rʳ g_! G` are lisse and realizable
the Leray step (`Stacks.EtaleCohomology.LAdicSheaf.compactSupportWeightLE_of_higherDirectImage`)
gives the weight bound on `g⁻¹ D(h)`, a surjective closed subscheme of an open of `Z`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- **The kernel of a localization of a ring map with nil kernel is nil.** -/
theorem ker_le_nilradical_localization_map {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T)
    (hk : RingHom.ker φ ≤ nilradical S) (M : Submonoid S) (Q : Type u) [CommRing Q] [Algebra T Q]
    [IsLocalization (M.map φ) Q] :
    RingHom.ker (IsLocalization.map Q φ M.le_comap_map : Localization M →+* Q) ≤
      nilradical (Localization M) := by
  intro y hy
  rw [RingHom.mem_ker] at hy
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  rw [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hy
  obtain ⟨⟨_, m, hm, rfl⟩, hmr⟩ := hy
  have hr : m * r ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_mul]
    exact hmr
  obtain ⟨N, hN⟩ := hk hr
  replace hN : (m * r) ^ N = 0 := hN
  refine ⟨N, Ideal.mem_bot.2 ?_⟩
  show (IsLocalization.mk' (Localization M) r s) ^ N = 0
  have h1 : (algebraMap S (Localization M) (m * r)) ^ N = 0 := by
    rw [← map_pow, hN, map_zero]
  have hu : IsUnit (algebraMap S (Localization M) m) := IsLocalization.map_units _ ⟨m, hm⟩
  rw [map_mul, mul_pow] at h1
  have h2 : (algebraMap S (Localization M) r) ^ N = 0 := (hu.pow N).mul_right_eq_zero.1 h1
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_pow, h2, zero_mul]

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
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

/-- A morphism locally of finite type to a scheme of finite type over a field maps closed points
to closed points. -/
theorem mem_closedPoints_of_locallyOfFiniteType {k : Type u} [Field k] {Y X : Scheme.{u}}
    (c : Y ⟶ X) [LocallyOfFiniteType c] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (y : closedPoints Y) : c.base y.1 ∈ closedPoints X := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  exact c.closePoints_subset_preimage_closedPoints y.2

/-- **The good open over a smooth affine family of curves.**  Let `Spec S` be a surjective closed
subscheme of an open `Spec T₀` of `Z`, and `g : Spec S ⟶ W = 𝔸ⁿ_k` affine and smooth of relative
dimension one over `k`. For a lisse, pointwise mixed, realizable sheaf `G` on `Z`, there is a
nonempty open of `Z` on which `G` satisfies the weight bound: over a basic open `D(h)` of `𝔸ⁿ`
on which all `Rʳ g_! (G|_{Spec S})` are lisse and realizable, the Leray step gives the weight
bound on `g⁻¹ D(h) = Spec S_{g^♯ h}`, a surjective closed subscheme of the open `Spec T_{x}` of
`Z` for a lift `x` of `g^♯ h`. -/
theorem LAdicSheaf.exists_open_compactSupportWeightLE_of_smoothAffineFamily
    {R : LAdicSheaf.HigherDirectImageFamily B ℓ} (hleray : LAdicSheaf.LerayWeightInput R)
    (hstalk : LAdicSheaf.HigherDirectImageStalkInput R)
    (hlisse : LAdicSheaf.HigherDirectImageLisseLocusInput R)
    (hreal : LAdicSheaf.HigherDirectImageRealizableInput R)
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ)
    (hind : LAdicSheaf.CompactSupportCompactificationIndependenceInput B ℓ) {n : ℕ}
    (hS : LAdicSheaf.WeightBoundInDimension B ℓ n) (hS1 : LAdicSheaf.WeightBoundInDimension B ℓ 1)
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] {p q : ℕ} [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ)
    {Z : B.Scheme} [IsNoetherian Z.1] (fZ : Z.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fZ]
    [QuasiCompact fZ] [IsSeparated fZ]
    (T₀ : Type u) [CommRing T₀] (o : Spec (.of T₀) ⟶ Z.1) [IsOpenImmersion o]
    (S : Type u) [CommRing S] [IsDomain S] (φ : T₀ →+* S) (hφs : Function.Surjective φ)
    (hφk : RingHom.ker φ ≤ nilradical T₀)
    (ψ : MvPolynomial (Fin n) k →+* S)
    [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom ψ))]
    [IsAffineHom (Spec.map (CommRingCat.ofHom ψ))]
    (hψk : Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) =
      Spec.map (CommRingCat.ofHom φ) ≫ o ≫ fZ)
    {G : LAdicSheaf.{u, u + 1} B Z ℓ} {w : ℤ} (hl : G.IsLisse)
    (hm : LAdicSheaf.IsPointwiseMixedOfWeightLE B Z ℓ fZ G (p ^ q) ι w)
    (hr : LAdicSheaf.IsIotaRealizable B Z ℓ fZ G ι) :
    ∃ (U : B.Scheme) (_ : IsNoetherian U.1) (jU : U ⟶ Z)
      (_ : IsOpenImmersion (B.inclusion.map jU)) (_ : QuasiCompact (B.inclusion.map jU ≫ fZ)),
      Nonempty U.1 ∧ LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι U
        (B.inclusion.map jU ≫ fZ) (LAdicSheaf.inverseImage jU G) w := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  -- the open `Spec T₀` of `Z` and its surjective closed subscheme `Spec S`, in `B`
  have hT₀ : B.Contains (Spec (.of T₀)) :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit o Z.property
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφs
  have hS₀ : B.Contains (Spec (.of S)) :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      (Spec.map (CommRingCat.ofHom φ)) hT₀
  have : IsLocallyNoetherian Z.1 := ‹AlgebraicGeometry.IsNoetherian Z.1›.toIsLocallyNoetherian
  have : IsLocallyNoetherian (Spec (.of T₀)) := isLocallyNoetherian_of_isOpenImmersion o
  have : IsNoetherianRing T₀ :=
    isLocallyNoetherian_Spec (R := CommRingCat.of T₀) |>.1 inferInstance
  have : IsNoetherianRing S := isNoetherianRing_of_surjective T₀ S φ hφs
  let U₀ : B.Scheme := B.obj (Spec (.of S)) hS₀
  have : IsNoetherian U₀.1 := inferInstanceAs (IsNoetherian (Spec (.of S)))
  -- the base `W = 𝔸ⁿ_k`
  have hW : B.Contains (Spec (.of (MvPolynomial (Fin n) k))) := by
    have hk : (Spec (.of k)).size < B.cutoff := by
      rw [Scheme.size_Spec]
      exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)
    exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k _ hk
  let W : B.Scheme := B.obj (Spec (.of (MvPolynomial (Fin n) k))) hW
  have : IsNoetherian W.1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (MvPolynomial (Fin n) k))))
  have : IsReduced W.1 := inferInstanceAs (IsReduced (Spec (.of (MvPolynomial (Fin n) k))))
  have : IrreducibleSpace W.1 :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (MvPolynomial (Fin n) k)))
  let fW : W.1 ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k)))
  have : LocallyOfFiniteType fW := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
    (RingHom.finiteType_algebraMap.2 inferInstance)
  have : QuasiCompact fW := inferInstanceAs (QuasiCompact (Spec.map _))
  have : IsSeparated fW := inferInstanceAs (IsSeparated (Spec.map _))
  -- the family `g : Spec S ⟶ W` and the restriction `G₀` of `G` to `Spec S`
  let g₀ : U₀ ⟶ W := ObjectProperty.homMk (Spec.map (CommRingCat.ofHom ψ))
  have : SmoothOfRelativeDimension 1 (B.inclusion.map g₀) :=
    ‹SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom ψ))›
  have : IsAffineHom (B.inclusion.map g₀) := ‹IsAffineHom (Spec.map (CommRingCat.ofHom ψ))›
  have : Smooth (Spec.map (CommRingCat.ofHom ψ)) := SmoothOfRelativeDimension.smooth 1 _
  have : LocallyOfFiniteType (B.inclusion.map g₀) :=
    inferInstanceAs (LocallyOfFiniteType (Spec.map (CommRingCat.ofHom ψ)))
  have : QuasiCompact (B.inclusion.map g₀) := inferInstanceAs (QuasiCompact (Spec.map _))
  have : IsSeparated (B.inclusion.map g₀) := inferInstanceAs (IsSeparated (Spec.map _))
  let c₀ : U₀ ⟶ Z := ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ) ≫ o)
  have : LocallyOfFiniteType (B.inclusion.map c₀) :=
    inferInstanceAs (LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ) ≫ o))
  have hgc : B.inclusion.map g₀ ≫ fW = B.inclusion.map c₀ ≫ fZ := by
    show Spec.map _ ≫ Spec.map _ = (Spec.map _ ≫ o) ≫ fZ
    rw [hψk, Category.assoc]
  have hc₀ : ∀ y : closedPoints U₀.1, (B.inclusion.map c₀).base y.1 ∈ closedPoints Z.1 :=
    mem_closedPoints_of_locallyOfFiniteType (B.inclusion.map c₀) fZ
  have : LocallyOfFiniteType (B.inclusion.map g₀ ≫ fW) := inferInstance
  have : LocallyOfFiniteType (B.inclusion.map c₀ ≫ fZ) := inferInstance
  let G₀ := LAdicSheaf.inverseImage c₀ G
  have hl₀ : G₀.IsLisse := hl.inverseImage c₀
  have hm₀ : LAdicSheaf.IsPointwiseMixedOfWeightLE B U₀ ℓ (B.inclusion.map g₀ ≫ fW) G₀ (p ^ q)
      ι w := (LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage Z ℓ c₀ fZ hm hc₀).congr hgc.symm
  have hr₀ : LAdicSheaf.IsIotaRealizable B U₀ ℓ (B.inclusion.map g₀ ≫ fW) G₀ ι :=
    LAdicSheaf.IsIotaRealizable.inverseImage ℓ fZ c₀ hr hc₀
  -- the lisse and the realizable loci of the `Rʳ g_! G₀`, and a basic open `D(h)` inside both
  have u₀ : PrimeSpectrum S := Classical.arbitrary _
  have : Nonempty U₀.1 := ⟨u₀⟩
  obtain ⟨V₁, jV₁, hV₁o, hV₁ne, H₁⟩ := hlisse U₀ W g₀ G₀ hl₀
    ⟨(Spec.map (CommRingCat.ofHom ψ)).base u₀⟩
  obtain ⟨V₂, jV₂, hV₂o, hV₂ne, H₂⟩ := hreal k p q hcard hℓ (p ^ q) ι U₀ W g₀ fW G₀ w hl₀ hm₀ hr₀
    inferInstance inferInstance
  have := hV₁o
  have := hV₂o
  have : Flat (B.inclusion.map g₀) := inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom ψ)))
  have : LocallyOfFinitePresentation (B.inclusion.map g₀) :=
    inferInstanceAs (LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom ψ)))
  have : UniversallyOpen (B.inclusion.map g₀) := UniversallyOpen.of_flat _
  have hO₁ := (B.inclusion.map jV₁).isOpenEmbedding.isOpen_range
  have hO₂ := (B.inclusion.map jV₂).isOpenEmbedding.isOpen_range
  have hO₃ := (B.inclusion.map g₀).isOpenMap.isOpen_range
  have : PreirreducibleSpace ↥(B.inclusion.obj W) :=
    inferInstanceAs (PreirreducibleSpace (PrimeSpectrum (MvPolynomial (Fin n) k)))
  obtain ⟨v₁⟩ := hV₁ne
  obtain ⟨v₂⟩ := hV₂ne
  obtain ⟨x, ⟨hx₁, hx₂⟩, hx₃⟩ := nonempty_preirreducible_inter (hO₁.inter hO₂) hO₃
    (nonempty_preirreducible_inter hO₁ hO₂ ⟨_, Set.mem_range_self v₁⟩ ⟨_, Set.mem_range_self v₂⟩)
    ⟨_, Set.mem_range_self (f := (B.inclusion.map g₀).base) u₀⟩
  have hx : (x : PrimeSpectrum (MvPolynomial (Fin n) k)) ∈
      (Set.range (B.inclusion.map jV₁).base ∩ Set.range (B.inclusion.map jV₂).base :
        Set (PrimeSpectrum (MvPolynomial (Fin n) k))) := ⟨hx₁, hx₂⟩
  obtain ⟨_, ⟨h, rfl⟩, hxh, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens
      (R := MvPolynomial (Fin n) k)).exists_subset_of_mem_open hx (hO₁.inter hO₂)
  -- the open `V' = D(h)` of `W`
  have hV' : B.Contains (Spec (.of (Localization.Away h))) :=
    Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (Submonoid.powers h) _ hW
  let V' : B.Scheme := B.obj (Spec (.of (Localization.Away h))) hV'
  have : IsNoetherianRing (Localization.Away h) :=
    IsLocalization.isNoetherianRing (Submonoid.powers h) _ inferInstance
  have : IsNoetherian V'.1 := inferInstanceAs (IsNoetherian (Spec (.of (Localization.Away h))))
  let jW : Spec (.of (Localization.Away h)) ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) k) (Localization.Away h)))
  have hjW : Set.range jW.base =
      (PrimeSpectrum.basicOpen h : Set (PrimeSpectrum (MvPolynomial (Fin n) k))) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away h) h
  let jV₁' : V' ⟶ V₁ := ObjectProperty.homMk (IsOpenImmersion.lift (B.inclusion.map jV₁) jW
    (hjW ▸ hsub.trans Set.inter_subset_left))
  let jV₂' : V' ⟶ V₂ := ObjectProperty.homMk (IsOpenImmersion.lift (B.inclusion.map jV₂) jW
    (hjW ▸ hsub.trans Set.inter_subset_right))
  have hjV₁ : B.inclusion.map (jV₁' ≫ jV₁) = jW := by
    rw [Functor.map_comp]
    exact IsOpenImmersion.lift_fac _ _ _
  have hjV₂ : B.inclusion.map (jV₂' ≫ jV₂) = jW := by
    rw [Functor.map_comp]
    exact IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (B.inclusion.map jV₁' ≫ B.inclusion.map jV₁) := by
    rw [← Functor.map_comp, hjV₁]
    infer_instance
  have : IsOpenImmersion (B.inclusion.map jV₂' ≫ B.inclusion.map jV₂) := by
    rw [← Functor.map_comp, hjV₂]
    infer_instance
  have hV₁' : IsOpenImmersion (B.inclusion.map jV₁') :=
    IsOpenImmersion.of_comp _ (B.inclusion.map jV₁)
  have hV₂' : IsOpenImmersion (B.inclusion.map jV₂') :=
    IsOpenImmersion.of_comp _ (B.inclusion.map jV₂)
  let fV' : V'.1 ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))
  have hfV' : jW ≫ fW = fV' := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have : LocallyOfFiniteType fV' := by rw [← hfV']; infer_instance
  have : QuasiCompact fV' := inferInstanceAs (QuasiCompact (Spec.map _))
  have : IsSeparated fV' := inferInstanceAs (IsSeparated (Spec.map _))
  -- the open `U' = g⁻¹ D(h) = Spec S_{ψ h}` of `Spec S`, and the base change `g' : U' ⟶ V'`
  have hU' : B.Contains (Spec (.of (Localization.Away (ψ h)))) :=
    Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (Submonoid.powers (ψ h)) _ hS₀
  let U' : B.Scheme := B.obj (Spec (.of (Localization.Away (ψ h)))) hU'
  have : IsNoetherianRing (Localization.Away (ψ h)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (ψ h)) _ inferInstance
  have : IsNoetherian U'.1 := inferInstanceAs (IsNoetherian (Spec (.of (Localization.Away (ψ h)))))
  let jU : U' ⟶ U₀ :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ψ h)))))
  have : IsOpenImmersion (B.inclusion.map jU) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap S (Localization.Away (ψ h))))))
  let g' : U' ⟶ V' := ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Localization.awayMap ψ h)))
  have : IsLocalization ((Submonoid.powers h).map ψ) (Localization.Away (ψ h)) := by
    rw [Submonoid.map_powers]
    infer_instance
  have hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g₀) jW :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isLocalization ψ
      (Localization.awayMap ψ h) (IsLocalization.map_comp _) (Submonoid.powers h))
  have : LocallyOfFiniteType (B.inclusion.map g' ≫ jW) := by
    rw [← hpb.w]
    infer_instance
  have : LocallyOfFiniteType (B.inclusion.map g') :=
    LocallyOfFiniteType.of_comp (f := B.inclusion.map g') (g := jW) inferInstance
  have : QuasiCompact (B.inclusion.map g') := inferInstanceAs (QuasiCompact (Spec.map _))
  have : IsSeparated (B.inclusion.map g') := inferInstanceAs (IsSeparated (Spec.map _))
  have : IsNoetherian (B.inclusion.obj V') := ‹IsNoetherian V'.1›
  obtain ⟨jg', -⟩ := hasCompactification_of_isNoetherian (B.inclusion.map g')
  have hRl : ∀ r : ℕ, (R g' jg' (LAdicSheaf.inverseImage jU G₀) r).IsLisse :=
    H₁ V' U' jV₁' jU g' jg' hV₁' (hjV₁ ▸ hpb)
  have hRr : ∀ r : ℕ, LAdicSheaf.IsIotaRealizable B V' ℓ fV'
      (R g' jg' (LAdicSheaf.inverseImage jU G₀) r) ι := fun r =>
    H₂ V' U' jV₂' jU g' jg' hV₂' (hjV₂ ▸ hpb) fV' r
  -- the Leray step on `g' : U' ⟶ V'`
  have hdimV' : topologicalKrullDim V'.1 ≤ n :=
    jW.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
      (topologicalKrullDim_Spec_mvPolynomial k n).le
  have hsm' : SmoothOfRelativeDimension 1 (B.inclusion.map g') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hpb
      ‹SmoothOfRelativeDimension 1 (B.inclusion.map g₀)›
  have hdim' : ∀ y : V'.1, topologicalKrullDim ↥((B.inclusion.map g').base ⁻¹' ({y} : Set V'.1)) ≤
      (1 : WithBot ℕ∞) := by
    intro y
    refine ((B.inclusion.map g').fiberHomeo y).symm.isInducing.topologicalKrullDim_le.trans ?_
    have hsy : SmoothOfRelativeDimension 1 ((B.inclusion.map g').fiberToSpecResidueField y) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback (B.inclusion.map g') (V'.1.fromSpecResidueField y)) hsm'
    rcases isEmpty_or_nonempty ((B.inclusion.map g').fiber y) with hE | hE
    · have : IsEmpty (TopologicalSpace.IrreducibleCloseds ((B.inclusion.map g').fiber y)) :=
        ⟨fun s => hE.elim s.isIrreducible.nonempty.some⟩
      rw [topologicalKrullDim, Order.krullDim_eq_bot]
      exact bot_le
    · rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field
        (k := V'.1.residueField y) 1 ((B.inclusion.map g').fiberToSpecResidueField y)]
      simp
  have hjUcl : ∀ y : closedPoints U'.1, (B.inclusion.map jU).base y.1 ∈ closedPoints U₀.1 :=
    mem_closedPoints_of_isOpenImmersion (B.inclusion.map jU) (B.inclusion.map g₀ ≫ fW)
  have heqU' : B.inclusion.map jU ≫ B.inclusion.map g₀ ≫ fW = B.inclusion.map g' ≫ fV' := by
    rw [← Category.assoc, hpb.w, Category.assoc, hfV']
  have hU' := LAdicSheaf.compactSupportWeightLE_of_higherDirectImage hleray hstalk hfin hind hS hS1
    kbar hcard hℓ ι g' jg' fV' hdimV' hdim' (hl₀.inverseImage jU)
    ((LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage U₀ ℓ jU (B.inclusion.map g₀ ≫ fW) hm₀
      hjUcl).congr heqU')
    (LAdicSheaf.IsIotaRealizable.inverseImage ℓ (B.inclusion.map g₀ ≫ fW) jU hr₀ hjUcl) hRl hRr
  -- back to `Z`: `U'` is a surjective closed subscheme of the open `Spec T₀_{xt}` of `Z`
  obtain ⟨xt, hxt⟩ := hφs (ψ h)
  have : IsLocalization ((Submonoid.powers xt).map φ) (Localization.Away (ψ h)) := by
    rw [Submonoid.map_powers, hxt]
    infer_instance
  let φ' : Localization.Away xt →+* Localization.Away (ψ h) :=
    IsLocalization.map (M := Submonoid.powers xt) (Localization.Away (ψ h)) φ
      (Submonoid.powers xt).le_comap_map
  have hφ's : Function.Surjective φ' :=
    IsLocalization.map_surjective_of_surjective (Submonoid.powers xt) _ _ hφs
  have hφ'k : RingHom.ker φ' ≤ nilradical (Localization.Away xt) :=
    ker_le_nilradical_localization_map φ hφk (Submonoid.powers xt) (Localization.Away (ψ h))
  let oT : Spec (.of (Localization.Away xt)) ⟶ Z.1 :=
    Spec.map (CommRingCat.ofHom (algebraMap T₀ (Localization.Away xt))) ≫ o
  have hUT : B.Contains (Spec (.of (Localization.Away xt))) :=
    Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit oT Z.property
  let UT : B.Scheme := B.obj (Spec (.of (Localization.Away xt))) hUT
  have : IsNoetherianRing (Localization.Away xt) :=
    IsLocalization.isNoetherianRing (Submonoid.powers xt) _ inferInstance
  have : IsNoetherian UT.1 := inferInstanceAs (IsNoetherian (Spec (.of (Localization.Away xt))))
  let jT : UT ⟶ Z := ObjectProperty.homMk oT
  have : IsOpenImmersion (B.inclusion.map jT) := inferInstanceAs (IsOpenImmersion oT)
  have hqcT : QuasiCompact (oT ≫ fZ) :=
    (quasiCompact_iff_compactSpace (oT ≫ fZ)).2
      (inferInstance : CompactSpace (Spec (.of (Localization.Away xt))))
  have : QuasiCompact (B.inclusion.map jT ≫ fZ) := hqcT
  have : LocallyOfFiniteType (B.inclusion.map jT ≫ fZ) :=
    inferInstanceAs (LocallyOfFiniteType (oT ≫ fZ))
  have : IsSeparated (B.inclusion.map jT ≫ fZ) := inferInstanceAs (IsSeparated (oT ≫ fZ))
  let iT : U' ⟶ UT := ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ'))
  have : IsClosedImmersion (B.inclusion.map iT) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ') hφ's
  have hsurj : Function.Surjective (B.inclusion.map iT).base :=
    surjective_specMap_base_of_ker_le_nilradical (CommRingCat.ofHom φ') hφ's hφ'k
  have hcomp : jU ≫ c₀ = iT ≫ jT := by
    apply B.inclusion.map_injective
    show Spec.map _ ≫ Spec.map _ ≫ o = Spec.map _ ≫ Spec.map _ ≫ o
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, IsLocalization.map_comp]
  have heq₂ : B.inclusion.map g' ≫ fV' = B.inclusion.map iT ≫ B.inclusion.map jT ≫ fZ := by
    rw [← heqU', hgc, ← Category.assoc, ← Functor.map_comp, hcomp, Functor.map_comp,
      Category.assoc]
  -- a point of `U'`
  obtain ⟨u, hu⟩ := hx₃
  have hu' : u ∈ (PrimeSpectrum.basicOpen (ψ h) : Set (PrimeSpectrum S)) := by
    show ψ h ∉ u.asIdeal
    intro hmem
    apply (show h ∉ (x : PrimeSpectrum (MvPolynomial (Fin n) k)).asIdeal from hxh)
    rw [← hu]
    exact hmem
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (ψ h)) (ψ h)] at hu'
  obtain ⟨u', -⟩ := hu'
  refine ⟨UT, inferInstance, jT, inferInstance, inferInstance,
    ⟨(Spec.map (CommRingCat.ofHom φ')).base u'⟩, ?_⟩
  refine LAdicSheaf.compactSupportWeightLE_of_surjective (B.inclusion.map jT ≫ fZ) iT hsurj
    (hfin k kbar p q hcard hℓ U' _) ?_
  exact (LAdicSheaf.compactSupportWeightLE_iff_of_padicTowerIso _
    (LAdicSheaf.padicTowerInverseImageCompIso jU c₀ (iT ≫ jT) hcomp G ≪≫
      (LAdicSheaf.padicTowerInverseImageCompIso iT jT (iT ≫ jT) rfl G).symm)
    (hfin k kbar p q hcard hℓ U' _) w).1 (hU'.congr heq₂)

/-- **A good open in dimension at most `n + 1`** (the induction step of Weil II).  Every nonempty
scheme `Z` of dimension at most `n + 1`, separated of finite type over `k`, and every lisse,
pointwise `ι`-mixed, `ι`-realizable sheaf `G` on `Z` have a nonempty open subscheme of `Z` on
which `G` satisfies the weight bound: take an affine open `Spec R` inside one irreducible
component, so that `A = R_red` is a domain of finite type over `k` of dimension `≤ n + 1`. In
dimension `≤ n` the weight bound in dimension `n` holds on `Spec A`, a surjective closed
subscheme of `Spec R`. In dimension `n + 1` an open `Spec A_a` is finite étale over an open
`D(f)` of `𝔸ⁿ⁺¹_k = 𝔸¹_{𝔸ⁿ}` (`GenericFiniteEtale.exists_finite_etale_specAway_mvPolynomial`),
and its projection to `𝔸ⁿ` is affine and smooth of relative dimension one
(`LAdicSheaf.exists_open_compactSupportWeightLE_of_smoothAffineFamily`). -/
theorem LAdicSheaf.exists_open_compactSupportWeightLE_of_weightBoundInDimension
    {R : LAdicSheaf.HigherDirectImageFamily B ℓ} (hleray : LAdicSheaf.LerayWeightInput R)
    (hstalk : LAdicSheaf.HigherDirectImageStalkInput R)
    (hlisse : LAdicSheaf.HigherDirectImageLisseLocusInput R)
    (hreal : LAdicSheaf.HigherDirectImageRealizableInput R)
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ)
    (hind : LAdicSheaf.CompactSupportCompactificationIndependenceInput B ℓ) {n : ℕ}
    (hS : LAdicSheaf.WeightBoundInDimension B ℓ n) (hS1 : LAdicSheaf.WeightBoundInDimension B ℓ 1)
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] {p q : ℕ} [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ)
    {Z : B.Scheme} [IsNoetherian Z.1] (fZ : Z.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fZ]
    [QuasiCompact fZ] [IsSeparated fZ] (hdim : topologicalKrullDim Z.1 ≤ n + 1)
    (hne : Nonempty Z.1) {G : LAdicSheaf.{u, u + 1} B Z ℓ} {w : ℤ} (hl : G.IsLisse)
    (hm : LAdicSheaf.IsPointwiseMixedOfWeightLE B Z ℓ fZ G (p ^ q) ι w)
    (hr : LAdicSheaf.IsIotaRealizable B Z ℓ fZ G ι) :
    ∃ (U : B.Scheme) (_ : IsNoetherian U.1) (jU : U ⟶ Z)
      (_ : IsOpenImmersion (B.inclusion.map jU)) (_ : QuasiCompact (B.inclusion.map jU ≫ fZ)),
      Nonempty U.1 ∧ LAdicSheaf.CompactSupportWeightLE B ℓ kbar p q hcard ι U
        (B.inclusion.map jU ≫ fZ) (LAdicSheaf.inverseImage jU G) w := by
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
  have hdimA : ringKrullDim (R ⧸ nilradical R) ≤ n + 1 := by
    refine (ringKrullDim_quotient_le _).trans ?_
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact e.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hfinZ : ∀ (Y : B.Scheme) [IsNoetherian Y.1] (g : Y.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g],
      topologicalKrullDim Y.1 ≤ topologicalKrullDim Z.1 →
        LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar Y g :=
    fun Y _ g _ _ _ _ => hfin k kbar p q hcard hℓ Y g
  rcases le_or_eq_add_one_of_le_add_one hdimA with h0 | h1
  · -- dimension `≤ n`: the weight bound in dimension `n` on `Spec A`
    obtain ⟨U, hU, jU, hjU, hqc, hUne, hUw⟩ :=
      LAdicSheaf.exists_open_satisfiesWeightBound_of_specMap
      (ι := ι) (hcard := hcard) fZ e
      (CommRingCat.ofHom (Ideal.Quotient.mk (nilradical R))) Ideal.Quotient.mk_surjective
      (by rw [CommRingCat.hom_ofHom, Ideal.mk_ker]) hfinZ fun hB _ _ _ _ => by
        have h0' : topologicalKrullDim (Spec (.of (R ⧸ nilradical R))) ≤ n :=
          (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R ⧸ nilradical R)).le.trans h0
        exact hS k kbar p q hcard hℓ ι _ _ h0'
    have := hjU
    have hcl : ∀ y : closedPoints U.1, (B.inclusion.map jU).base y.1 ∈ closedPoints Z.1 :=
      mem_closedPoints_of_isOpenImmersion (B.inclusion.map jU) fZ
    exact ⟨U, hU, jU, hjU, hqc, hUne,
      (LAdicSheaf.satisfiesWeightBound_iff_forall_compactSupportWeightLE U _).1 hUw _ w
        (hl.inverseImage jU) (LAdicSheaf.IsPointwiseMixedOfWeightLE.inverseImage Z ℓ jU fZ hm hcl)
        (LAdicSheaf.IsIotaRealizable.inverseImage ℓ fZ jU hr hcl)⟩
  · -- dimension `n + 1`: `Spec A_a` is finite étale over an open `D(f)` of `𝔸¹_{𝔸ⁿ}`
    obtain ⟨a, ha, f, hf, π, hπf, hπe, hπk⟩ :=
      Stacks.GenericFiniteEtale.exists_finite_etale_specAway_mvPolynomial k (R ⧸ nilradical R)
        (n + 1) (by rw [h1]; push_cast; rfl)
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
    -- the projection `D(f) ⊆ 𝔸ⁿ⁺¹ = 𝔸¹_{𝔸ⁿ} ⟶ 𝔸ⁿ`
    let : Algebra (MvPolynomial (Fin n) k) (MvPolynomial (Fin (n + 1)) k) :=
      ((MvPolynomial.finSuccEquiv k n).symm.toRingHom.comp Polynomial.C).toAlgebra
    let eP : Polynomial (MvPolynomial (Fin n) k) ≃ₐ[MvPolynomial (Fin n) k]
        MvPolynomial (Fin (n + 1)) k :=
      AlgEquiv.ofRingEquiv (f := (MvPolynomial.finSuccEquiv k n).symm.toRingEquiv)
        (fun _ => rfl)
    have : Algebra.IsStandardSmoothOfRelativeDimension 1 (MvPolynomial (Fin n) k)
        (MvPolynomial (Fin (n + 1)) k) := by
      have : Algebra.IsStandardSmoothOfRelativeDimension 1 (MvPolynomial (Fin n) k)
          (Polynomial (MvPolynomial (Fin n) k)) :=
        .of_algEquiv 1 (MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin n) k) (Fin 1))
      exact .of_algEquiv 1 eP
    have : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin (n + 1)) k)
        (Localization.Away f) := Algebra.IsStandardSmoothOfRelativeDimension.localization_away f
    have hsm : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial (Fin n) k) (Localization.Away f)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
      refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
      show RingHom.IsStandardSmoothOfRelativeDimension 1
        (algebraMap (MvPolynomial (Fin n) k) (Localization.Away f))
      rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
      simpa using Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 (MvPolynomial (Fin n) k)
        (MvPolynomial (Fin (n + 1)) k) (Localization.Away f)
    have hkQ : (algebraMap (MvPolynomial (Fin n) k) (Localization.Away f)).comp
        (algebraMap k (MvPolynomial (Fin n) k)) = algebraMap k (Localization.Away f) := by
      ext c
      show algebraMap (MvPolynomial (Fin (n + 1)) k) (Localization.Away f)
          ((MvPolynomial.finSuccEquiv k n).symm (Polynomial.C (algebraMap k _ c))) = _
      rw [← Polynomial.algebraMap_apply, AlgEquiv.commutes,
        ← IsScalarTower.algebraMap_apply]
    -- the family `ψ : k[x₁, …, xₙ] → A_a`
    let ψ : MvPolynomial (Fin n) k →+* Localization.Away (Ideal.Quotient.mk (nilradical R) b) :=
      (Spec.preimage π).hom.comp (algebraMap (MvPolynomial (Fin n) k) (Localization.Away f))
    have hψ : Spec.map (CommRingCat.ofHom ψ) = π ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial (Fin n) k) (Localization.Away f))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
    have : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom ψ)) := by
      rw [hψ]
      have := hsm
      have h01 : SmoothOfRelativeDimension (0 + 1) (π ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial (Fin n) k) (Localization.Away f)))) := inferInstance
      rwa [zero_add] at h01
    have : IsAffineHom (Spec.map (CommRingCat.ofHom ψ)) := by
      rw [hψ]
      infer_instance
    have hψk : Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) =
        Spec.map (CommRingCat.ofHom φ) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b))) ≫ e) ≫ fZ := by
      rw [hψ, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hkQ, hπk,
        Category.assoc, ← hφ0, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext c
      show algebraMap k _ c = φ (algebraMap R (Localization.Away b) (φ0.hom c))
      rw [IsLocalization.map_eq, IsScalarTower.algebraMap_apply k (R ⧸ nilradical R)
        (Localization.Away (Ideal.Quotient.mk (nilradical R) b))]
      rfl
    exact LAdicSheaf.exists_open_compactSupportWeightLE_of_smoothAffineFamily hleray hstalk hlisse
      hreal hfin hind hS hS1 kbar hcard hℓ ι fZ (Localization.Away b)
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b))) ≫ e)
      (Localization.Away (Ideal.Quotient.mk (nilradical R) b)) φ hφs
      (ker_le_nilradical_localizationAway_map b ha) ψ hψk hl hm hr

/-- **The induction step of Weil II**, `S(n) → S(n + 1)` for `n ≥ 1`, from the results named in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepInputs`: by noetherian
induction (`LAdicSheaf.satisfiesWeightBound_of_forall_exists_open_compactSupportWeightLE`) it
suffices that every lisse, pointwise mixed, realizable sheaf on every nonempty closed subscheme of
a scheme of dimension `≤ n + 1` satisfies the weight bound on a nonempty open
(`LAdicSheaf.exists_open_compactSupportWeightLE_of_weightBoundInDimension`). -/
theorem LAdicSheaf.weightBoundInDimension_succ_of_inputs
    {R : LAdicSheaf.HigherDirectImageFamily B ℓ} (hleray : LAdicSheaf.LerayWeightInput R)
    (hstalk : LAdicSheaf.HigherDirectImageStalkInput R)
    (hlisse : LAdicSheaf.HigherDirectImageLisseLocusInput R)
    (hreal : LAdicSheaf.HigherDirectImageRealizableInput R)
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ)
    (hind : LAdicSheaf.CompactSupportCompactificationIndependenceInput B ℓ) (n : ℕ) (hn : 1 ≤ n)
    (hS : LAdicSheaf.WeightBoundInDimension B ℓ n) :
    LAdicSheaf.WeightBoundInDimension B ℓ (n + 1) := by
  intro k _ _ kbar _ _ _ p q _ _ hcard hℓ ι X _ f _ _ _ hdim
  have hS1 : LAdicSheaf.WeightBoundInDimension B ℓ 1 :=
    fun k _ _ kbar _ _ _ p q _ _ hcard hℓ ι Y _ g _ _ _ hY =>
      hS k kbar p q hcard hℓ ι Y g (hY.trans (by exact_mod_cast hn))
  exact LAdicSheaf.satisfiesWeightBound_of_forall_exists_open_compactSupportWeightLE X f
    (fun Y _ g _ _ _ _ => hfin k kbar p q hcard hℓ Y g)
    fun Z _ iZ _ hZ G w hl hm hr =>
      LAdicSheaf.exists_open_compactSupportWeightLE_of_weightBoundInDimension hleray hstalk hlisse
        hreal hfin hind hS hS1 kbar hcard hℓ ι (B.inclusion.map iZ ≫ f)
        ((B.inclusion.map iZ).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
          (by exact_mod_cast hdim)) hZ hl hm hr

/-- **Tag 03VH from the curve case on opens of the affine line and the inputs of the induction
step.**  For `X` connected, separated of finite type over `k` with `q = p ^ m` elements,
`ℓ ≠ p`, and `ρ` a continuous representation of `π₁(X, x̄)` satisfying the conclusions of
Deligne's conjecture, the eigenvalues of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` are algebraic numbers
of absolute value `q ^ (w / 2)` with `w ≤ i` along every `ι`. -/
theorem LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_inputs
    (hcurve : WeilIICurveBoundOpenAffineLine.{u})
    {R : LAdicSheaf.HigherDirectImageFamily B ℓ} (hleray : LAdicSheaf.LerayWeightInput R)
    (hstalk : LAdicSheaf.HigherDirectImageStalkInput R)
    (hlisse : LAdicSheaf.HigherDirectImageLisseLocusInput R)
    (hreal : LAdicSheaf.HigherDirectImageRealizableInput R)
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ)
    (hind : LAdicSheaf.CompactSupportCompactificationIndependenceInput B ℓ)
    {k : Type u} [Field k] [Fintype k] {kbar : Type u} [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] {p q : ℕ} [Fact p.Prime] [CharP k p] {hcard : Fintype.card k = p ^ q}
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ)
    (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i)] (ι : ℚ_[ℓ] →+* ℂ) :
    IsCharpolyMixedOfWeightLE (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom :=
  LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_weightBoundInDimension_succ hcurve
    (fun n hn hS => LAdicSheaf.weightBoundInDimension_succ_of_inputs hleray hstalk hlisse hreal
      hfin hind n hn hS) hℓ X f j x ρ hρ hD i ι

end Stacks.EtaleCohomology
