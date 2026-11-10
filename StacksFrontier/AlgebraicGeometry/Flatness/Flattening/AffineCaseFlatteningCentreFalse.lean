module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.MvPolynomial.Variables
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescentFiniteType
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescentTop

/-!
# The affine case of [Stacks, Tag 0815] needs its open to be quasi-compact

[Stacks, Tag 0815] assumes throughout that `U ⊆ S` is a quasi-compact open. This file shows that
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses`, which records hypotheses
(2)-(5) of the source, fails without that assumption: the statement
`AlgebraicGeometry.AffineCaseFlatteningCentreNoCompact`, asking it of every open, is false. The
open seen on an affine chart is `V ∩ A` for an affine open `V`, and an open of an affine scheme
need not be quasi-compact. In the witness `T = Y = Spec P` is affine and `p = 𝟙` is locally of
finite presentation, so the only hypothesis of
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace` that fails
is the quasi-compactness of `A`.

## The witness

Take `P = k[x₀, x₁, x₂, …]` with countably many variables, `m = (x₀, x₁, …)` its augmentation
ideal, `T = Y = Spec P`, `p = 𝟙`, `A = Spec P \ {m}` and `G` the structure sheaf of the closed
point `m` pushed forward along the closed immersion. Then

* `p` is locally of finite presentation — hypothesis (2);
* `G` is quasi-coherent and of finite type — hypothesis (3), because `P/m` is a finite
  `P`-module;
* `G` restricted to `A` is the zero module, hence of finite presentation and flat over `A` —
  hypotheses (4) and (5).

On the chart `V = W = ⊤` the predicate therefore produces a centre `I` of finite presentation
with `Disjoint A I.support`. Since `I` is of finite type the complement of its support is a
quasi-compact open of `Spec P` containing `A`; but `m` is not the radical of any finitely
generated ideal, so the only quasi-compact open containing `A` is the whole of `Spec P`. Hence
`I.support = ∅`, hence `I = ⊤`, hence the blowup is an isomorphism and the strict transform is
`G` itself — and the predicate asserts that `G` is flat over `Spec P`. It is not: `x₀` is a
nonzerodivisor of `P` which kills the class of `1` in `P/m`.

`m` is not the radical of a finitely generated ideal because a finite set of generators involves
only finitely many variables: if `x_N` occurs in none of them, substituting `0` for every
variable but `x_N` kills the generators and not `x_N`, so the kernel of that substitution is a
prime in the zero locus other than `m`.

## Main definitions

* `AlgebraicGeometry.AffineCaseFlatteningCentreNoCompact`: the affine case asked of every datum
  and every open, with the quasi-compactness of `A` deleted.

## Main results

* `AlgebraicGeometry.not_affineCaseFlatteningCentreNoCompact`:
  `¬ AffineCaseFlatteningCentreNoCompact.{u}`.
* `AlgebraicGeometry.AffineCase0815.not_isCompact_punctured`: the witness open is not
  quasi-compact.
* `AlgebraicGeometry.isCompact_compl_support_of_isFiniteType`: the complement of the support of
  a finite-type ideal sheaf on an affine scheme is quasi-compact.
* `AlgebraicGeometry.eq_top_of_disjoint_support_of_isFiniteType`: a finite-type centre supported
  away from an open which no proper quasi-compact open contains is the unit centre.
* `AlgebraicGeometry.isFlatOver_of_affineChartFlatteningCentre_of_isAffine`: over such an
  open, `AlgebraicGeometry.AffineChartFlatteningCentre` implies flatness over the base.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Finite-type centres have quasi-compact complements -/

/-- **The complement of the support of a finite-type ideal sheaf on an affine scheme is
quasi-compact.** -/
theorem isCompact_compl_support_of_isFiniteType {Z : Scheme.{u}} [IsAffine Z]
    {I : Z.IdealSheafData} (hI : Scheme.IdealSheafData.IsFiniteType I) :
    IsCompact ((I.support : Set Z)ᶜ) := by
  set J : Ideal Γ(Z, ⊤) := I.ideal ⟨⊤, isAffineOpen_top Z⟩ with hJdef
  have hsupp : (I.support : Set Z) = Z.zeroLocus (U := ⊤) (J : Set Γ(Z, ⊤)) := by
    ext x
    exact I.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top Z⟩) trivial
  have hcpt : IsCompact ((PrimeSpectrum.zeroLocus (J : Set Γ(Z, ⊤)))ᶜ) :=
    (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨J, hI _, rfl⟩).1
  have hpre : (Scheme.homeoOfIso Z.isoSpec) ⁻¹' (PrimeSpectrum.zeroLocus (J : Set Γ(Z, ⊤))) =
      Z.zeroLocus (U := ⊤) (J : Set Γ(Z, ⊤)) := by
    rw [Scheme.coe_homeoOfIso, Scheme.isoSpec_hom]
    exact Z.toSpecΓ_preimage_zeroLocus _
  rw [hsupp, ← hpre]
  exact (Homeomorph.isCompact_preimage (h := Scheme.homeoOfIso Z.isoSpec)
    (s := (PrimeSpectrum.zeroLocus (J : Set Γ(Z, ⊤)))ᶜ)).mpr hcpt

/-- **A finite-type centre supported away from an open that no proper quasi-compact open
contains is the unit centre.** -/
theorem eq_top_of_disjoint_support_of_isFiniteType {Z : Scheme.{u}} [IsAffine Z]
    {I : Z.IdealSheafData} (hI : Scheme.IdealSheafData.IsFiniteType I) {U : Z.Opens}
    (hdisj : Disjoint (U : Set Z) (I.support : Set Z))
    (hU : ∀ W : Z.Opens, IsCompact (W : Set Z) → U ≤ W → W = ⊤) :
    I = ⊤ := by
  have hopen : IsOpen ((I.support : Set Z)ᶜ) := I.support.2.isOpen_compl
  have hW := hU ⟨(I.support : Set Z)ᶜ, hopen⟩ (isCompact_compl_support_of_isFiniteType hI)
    fun x hx ↦ Set.disjoint_left.mp hdisj hx
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine SetLike.coe_injective ?_
  rw [TopologicalSpace.Closeds.coe_bot, ← Set.compl_univ_iff]
  exact Opens.coe_eq_univ.mpr hW

/-! ### What the chart predicate asks of an open with no proper quasi-compact neighbourhood -/

/-- **The chart predicate forces flatness over the base when no proper quasi-compact open of
the base contains `U`.** -/
theorem isFlatOver_of_affineChartFlatteningCentre_of_isAffine
    {S X : Scheme.{u}} [IsAffine S] [IsAffine X] (f : X ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] (U : S.Opens)
    (hU : ∀ W : S.Opens, IsCompact (W : Set S) → U ≤ W → W = ⊤)
    (H : AffineChartFlatteningCentre f F U) :
    IsFlatOver f.toLRSHom.toShHom F := by
  have : IsAffine (⊤ : S.Opens).toScheme := isAffineOpen_top S
  have hVW : ((⊤ : X.Opens) : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens) := le_top
  obtain ⟨I, hIfp, hdisj, hflat⟩ := H ⟨⊤, isAffineOpen_top S⟩ ⟨⊤, isAffineOpen_top X⟩ hVW
  set h := Scheme.homeoOfIso S.topIso with hh
  have hcoe : ⇑h = ⇑(⊤ : S.Opens).ι := by rw [hh, Scheme.coe_homeoOfIso, Scheme.topIso_hom]
  have hU' : ∀ W : (⊤ : S.Opens).toScheme.Opens, IsCompact (W : Set (⊤ : S.Opens).toScheme) →
      ((⊤ : S.Opens).ι ⁻¹ᵁ U) ≤ W → W = ⊤ := by
    intro W hWc hUW
    have himg : IsOpen (h '' (W : Set (⊤ : S.Opens).toScheme)) := h.isOpenMap _ W.2
    have hcpt : IsCompact (h '' (W : Set (⊤ : S.Opens).toScheme)) := hWc.image h.continuous
    have hle : U ≤ (⟨_, himg⟩ : S.Opens) := by
      intro s hs
      obtain ⟨z, rfl⟩ := h.surjective s
      refine ⟨z, hUW (show z ∈ (⊤ : S.Opens).ι ⁻¹ᵁ U from ?_), rfl⟩
      simpa [← hcoe] using hs
    have htop := hU ⟨_, himg⟩ hcpt hle
    have huniv : h '' (W : Set (⊤ : S.Opens).toScheme) = Set.univ :=
      Opens.coe_eq_univ.mpr htop
    refine TopologicalSpace.Opens.ext (Set.eq_univ_iff_forall.mpr fun z ↦ ?_)
    obtain ⟨z', hz', hzz⟩ := Set.eq_univ_iff_forall.mp huniv (h z)
    exact h.injective hzz ▸ hz'
  have hItop : I = ⊤ :=
    eq_top_of_disjoint_support_of_isFiniteType
      ((finitePresentation_subschemeι_iff_isFiniteType I).mp hIfp) hdisj hU'
  subst hItop
  have : ((Scheme.Modules.pullback (⊤ : X.Opens).ι).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (⊤ : X.Opens).ι F ‹_›
  have hres : IsFlatOver (f.resLE ⊤ ⊤ hVW).toLRSHom.toShHom
      ((Scheme.Modules.pullback (⊤ : X.Opens).ι).obj F) :=
    isFlatOver_of_isFlatOver_strictTransformSheaf_top _ _ hflat
  intro x
  have hflatι : IsFlatAt (⊤ : X.Opens).ι.toLRSHom.toShHom (⟨x, trivial⟩ : (⊤ : X.Opens).toScheme) :=
    Flat.stalkMap (⊤ : X.Opens).ι ⟨x, trivial⟩
  refine (isFlatOverAt_iff_modulePullback_isFlatOverAt (⊤ : X.Opens).ι f F ⟨x, trivial⟩
    hflatι).mpr ?_
  rw [show ((⊤ : X.Opens).ι ≫ f) = f.resLE ⊤ ⊤ hVW ≫ (⊤ : S.Opens).ι from
    (Scheme.Hom.resLE_comp_ι f hVW).symm]
  exact (isFlatOverAt_comp_iff_of_etale (f.resLE ⊤ ⊤ hVW) (⊤ : S.Opens).ι
    ((Scheme.Modules.pullback (⊤ : X.Opens).ι).obj F) ⟨x, trivial⟩).mpr (hres ⟨x, trivial⟩)

/-! ### Spectra in which a point is not cut out by a finitely generated ideal -/

/-- **If no finitely generated ideal cuts out the closed point `z`, no proper quasi-compact open
of `Spec A` contains the complement of `z`.** -/
theorem eq_top_of_isCompact_of_compl_singleton_le {A : CommRingCat.{u}}
    (z : PrimeSpectrum A)
    (hz : ∀ J : Ideal A, J.FG → PrimeSpectrum.zeroLocus (J : Set A) ⊆ {z} → J = ⊤)
    (W : (Spec A).Opens) (hWc : IsCompact (W : Set (Spec A)))
    (hW : ∀ p : PrimeSpectrum A, p ≠ z → p ∈ (W : Set (Spec A))) :
    W = ⊤ := by
  obtain ⟨J, hJfg, hJW⟩ :=
    PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hWc, W.2⟩
  have hsub : PrimeSpectrum.zeroLocus (J : Set A) ⊆ {z} := by
    intro p hp
    by_contra hne
    have hmem : p ∈ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ := by
      rw [hJW]; exact hW p hne
    exact hmem hp
  have hz0 : PrimeSpectrum.zeroLocus (J : Set A) = ∅ :=
    PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr (hz J hJfg hsub)
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_top, ← hJW, hz0, Set.compl_empty]
  exact rfl

/-! ### A spectrum with a point not cut out by any finitely generated ideal -/

namespace AffineCase0815

open MvPolynomial

/-- The coefficient field. -/
abbrev K : Type u := ULift.{u} ℚ

/-- The polynomial ring in countably many variables. -/
abbrev P : Type u := MvPolynomial ℕ K.{u}

/-- The augmentation ideal of `P`: the polynomials with zero constant term. -/
def augIdeal : Ideal P.{u} := RingHom.ker (constantCoeff : P.{u} →+* K.{u})

/-- The constant coefficient map `P → K` is surjective. -/
theorem constantCoeff_surjective : Function.Surjective (constantCoeff : P.{u} →+* K.{u}) :=
  fun a ↦ ⟨C a, by simp⟩

/-- The augmentation ideal is maximal. -/
instance augIdeal_isMaximal : (augIdeal.{u}).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ constantCoeff_surjective

/-- The point of `Spec P` cut out by the augmentation ideal. -/
def augPt : PrimeSpectrum P.{u} := ⟨augIdeal, (augIdeal_isMaximal).isPrime⟩

/-- **The augmentation ideal is not the radical of a finitely generated ideal.** A finitely
generated ideal whose zero locus is contained in the augmentation point is the unit ideal. -/
theorem eq_top_of_fg_of_zeroLocus_subset (J : Ideal P.{u}) (hJ : J.FG)
    (h : PrimeSpectrum.zeroLocus (J : Set P.{u}) ⊆ {augPt}) : J = ⊤ := by
  classical
  by_contra hne
  obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal J hne
  have hnmem : (⟨n, hn.isPrime⟩ : PrimeSpectrum P.{u}) ∈
      PrimeSpectrum.zeroLocus (J : Set P.{u}) := hJn
  have hnaug : n = augIdeal.{u} := congrArg PrimeSpectrum.asIdeal (h hnmem)
  have hJaug : J ≤ augIdeal.{u} := hnaug ▸ hJn
  obtain ⟨G, hG⟩ := hJ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ g ∈ G, N ∉ (g : P.{u}).vars := by
    obtain ⟨N, hN⟩ := (G.biUnion fun g ↦ g.vars).exists_notMem
    exact ⟨N, fun g hg hmem ↦ hN (Finset.mem_biUnion.mpr ⟨g, hg, hmem⟩)⟩
  set φ : P.{u} →+* Polynomial K.{u} :=
    eval₂Hom (Polynomial.C : K.{u} →+* Polynomial K.{u})
      (fun i ↦ if i = N then Polynomial.X else 0) with hφ
  have hker : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hJker : J ≤ RingHom.ker φ := by
    rw [← hG, Ideal.span_le]
    intro g hg
    have hvars : ∀ i ∈ (g : P.{u}).vars,
        (fun i ↦ if i = N then Polynomial.X else (0 : Polynomial K.{u})) i = 0 := by
      intro i hi
      have hiN : i ≠ N := fun hh ↦ hN g hg (hh ▸ hi)
      simp [hiN]
    have hc : constantCoeff g = 0 := by
      have hmem : g ∈ augIdeal.{u} := hJaug (by rw [← hG]; exact Ideal.subset_span hg)
      simpa [augIdeal, RingHom.mem_ker] using hmem
    simp only [SetLike.mem_coe, RingHom.mem_ker, hφ]
    rw [eval₂Hom_eq_constantCoeff_of_vars _ hvars, hc, map_zero]
  have hmem : (⟨RingHom.ker φ, hker⟩ : PrimeSpectrum P.{u}) ∈
      PrimeSpectrum.zeroLocus (J : Set P.{u}) := hJker
  have hkeraug : RingHom.ker φ = augIdeal.{u} := congrArg PrimeSpectrum.asIdeal (h hmem)
  have h1 : (X N : P.{u}) ∈ augIdeal.{u} := by simp [augIdeal, RingHom.mem_ker]
  have hXN : φ (X N) = Polynomial.X := by simp [hφ]
  have h2 : (X N : P.{u}) ∉ RingHom.ker φ := by
    rw [RingHom.mem_ker, hXN]
    exact Polynomial.X_ne_zero
  exact h2 (hkeraug ▸ h1)

/-- **The residue field of the augmentation ideal is not a flat module.** The variable `X 0` is a
nonzerodivisor of `P` which kills the nonzero class of `1`, so `P ⧸ m` has torsion. -/
theorem not_flat_quotient : ¬ Module.Flat P.{u} (P.{u} ⧸ augIdeal.{u}) := by
  intro hflat
  have : Nontrivial (P.{u} ⧸ augIdeal.{u}) :=
    Ideal.Quotient.nontrivial_iff.mpr (augIdeal_isMaximal.{u}).ne_top
  have hmem : (X 0 : P.{u}) ∈ augIdeal.{u} := by simp [augIdeal, RingHom.mem_ker]
  have hX0 : (X 0 : P.{u}) ∈ nonZeroDivisors P.{u} :=
    mem_nonZeroDivisors_of_ne_zero (X_ne_zero 0)
  have hreg : IsSMulRegular (P.{u} ⧸ augIdeal.{u}) (X 0 : P.{u}) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hX0
  have hsmul : ∀ r y : P.{u}, r • (Ideal.Quotient.mk augIdeal.{u} y) =
      Ideal.Quotient.mk augIdeal.{u} (r * y) := fun _ _ ↦ rfl
  have hone : (1 : P.{u} ⧸ augIdeal.{u}) = Ideal.Quotient.mk augIdeal.{u} 1 := rfl
  have h1 : (X 0 : P.{u}) • (1 : P.{u} ⧸ augIdeal.{u}) = 0 := by
    rw [hone, hsmul, mul_one, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  exact one_ne_zero (hreg (h1.trans (smul_zero _).symm))

/-! ### The counterexample -/

/-- The affine base `Spec P`. -/
abbrev baseRing : CommRingCat.{u} := CommRingCat.of P.{u}

/-- The residue ring of the augmentation ideal. -/
abbrev quotRing : CommRingCat.{u} := CommRingCat.of (P.{u} ⧸ augIdeal.{u})

/-- The quotient map. -/
def quotHom : baseRing.{u} ⟶ quotRing.{u} := CommRingCat.ofHom (Ideal.Quotient.mk augIdeal.{u})

/-- The closed immersion of the augmentation point. -/
def clo : Spec quotRing.{u} ⟶ Spec baseRing.{u} := Spec.map quotHom.{u}

/-- `clo` is a closed immersion. -/
instance : IsClosedImmersion clo.{u} :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The complement of the augmentation point, an open which is not quasi-compact and which no
proper quasi-compact open contains. -/
def punctured : (Spec baseRing.{u}).Opens :=
  ⟨({augPt.{u}}ᶜ : Set (PrimeSpectrum P.{u})),
    (((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      augIdeal_isMaximal).isOpen_compl)⟩

/-- The structure sheaf of the augmentation point, pushed forward to `Spec P`. -/
def modu : (Spec baseRing.{u}).Modules :=
  (Scheme.Modules.pushforward clo.{u}).obj (Spec quotRing.{u}).unitModule

/-- `modu` is quasi-coherent. -/
instance modu_isQuasicoherent : modu.{u}.IsQuasicoherent :=
  inferInstanceAs
    (((Scheme.Modules.pushforward clo.{u}).obj (Spec quotRing.{u}).unitModule)).IsQuasicoherent

/-- `modu` is of finite type. -/
instance modu_isFiniteType : modu.{u}.IsFiniteType :=
  have : (Spec quotRing.{u}).unitModule.IsFiniteType :=
    inferInstanceAs (SheafOfModules.unit (Spec quotRing.{u}).ringCatSheaf).IsFiniteType
  isFiniteType_pushforward_of_isFinite' clo.{u} (Spec quotRing.{u}).unitModule

/-- The closed immersion hits only the augmentation point. -/
theorem clo_base_eq (z : Spec quotRing.{u}) : clo.{u}.base z = augPt.{u} := by
  refine PrimeSpectrum.ext ?_
  refine ((augIdeal_isMaximal.{u}).eq_of_le ?_ ?_).symm
  · exact (clo.{u}.base z).2.ne_top
  · intro x hx
    change (Ideal.Quotient.mk augIdeal.{u}) x ∈ z.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Submodule.zero_mem _

/-- The preimage under `clo` of an open contained in `punctured` is empty. -/
theorem isEmpty_clo_preimage (V : (Spec baseRing.{u}).Opens) (hV : V ≤ punctured.{u}) :
    IsEmpty ↥(clo.{u} ⁻¹ᵁ V) := by
  refine ⟨fun y ↦ ?_⟩
  have h2 : clo.{u}.base y.1 ∈ punctured.{u} := hV y.2
  rw [clo_base_eq] at h2
  exact h2 rfl

/-- **The module vanishes on every open avoiding the augmentation point.** -/
theorem isZero_modu_restrict (V : (Spec baseRing.{u}).Opens) (hV : V ≤ punctured.{u}) :
    IsZero (modu.{u}.restrict V.ι) := by
  have := isEmpty_clo_preimage V hV
  have hz : IsZero ((Spec quotRing.{u}).unitModule.restrict (clo.{u} ⁻¹ᵁ V).ι) :=
    isZero_of_forall_isZero_stalk _ fun x ↦
      ((isEmpty_clo_preimage V hV).false x).elim
  have : (Scheme.Modules.pushforward (clo.{u} ∣_ V)).Additive := ⟨rfl⟩
  refine IsZero.of_iso (Functor.map_isZero (Scheme.Modules.pushforward (clo.{u} ∣_ V)) hz) ?_
  exact (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso clo.{u} V).app _

/-- **No proper quasi-compact open contains `punctured`.** -/
theorem punctured_eq_top_of_isCompact (W : (Spec baseRing.{u}).Opens)
    (hWc : IsCompact (W : Set (Spec baseRing.{u}))) (hW : punctured.{u} ≤ W) : W = ⊤ := by
  refine eq_top_of_isCompact_of_compl_singleton_le augPt.{u} eq_top_of_fg_of_zeroLocus_subset
    W hWc fun p hp ↦ ?_
  have hmem : p ∈ punctured.{u} := by
    change p ∈ ({augPt.{u}}ᶜ : Set (PrimeSpectrum P.{u}))
    exact hp
  exact hW hmem

/-- **The module is not flat over the base.** -/
theorem not_isFlatOver_modu :
    ¬ IsFlatOver
      (𝟙 (Spec baseRing.{u}) : Scheme.Hom (Spec baseRing.{u})
        (Spec baseRing.{u})).toLRSHom.toShHom modu.{u} := by
  intro hflat
  have h1 : IsFlatOver (clo.{u} ≫ (𝟙 (Spec baseRing.{u}) : Scheme.Hom (Spec baseRing.{u})
      (Spec baseRing.{u}))).toLRSHom.toShHom (Spec quotRing.{u}).unitModule :=
    (isFlatOver_pushforward_iff clo.{u} (𝟙 _) (Spec quotRing.{u}).unitModule).mpr hflat
  rw [Category.comp_id] at h1
  have h2 : Flat clo.{u} :=
    Flat.of_stalkMap clo.{u} fun z ↦ (isFlatOverAt_unit_iff_isFlatAt clo.{u} z).mp (h1 z)
  have h3 : RingHom.Flat quotHom.{u}.hom := HasRingHomProperty.Spec_iff.mp h2
  refine not_flat_quotient (RingHom.flat_algebraMap_iff.mp ?_)
  rw [show (algebraMap P.{u} (P.{u} ⧸ augIdeal.{u})) = Ideal.Quotient.mk augIdeal.{u} from
    Ideal.Quotient.algebraMap_eq _]
  exact h3

/-- The identity of the base, as a scheme morphism. -/
abbrev baseId : Spec baseRing.{u} ⟶ Spec baseRing.{u} := 𝟙 _

/-- The preimage of `punctured` under `baseId` is contained in `punctured`. -/
theorem baseId_preimage_punctured_le : baseId.{u} ⁻¹ᵁ punctured.{u} ≤ punctured.{u} :=
  fun _ hx ↦ hx

end AffineCase0815

/-- **The quasi-compactness-free form of the affine case of [Stacks, Tag 0815].**
This is `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses` asked of every
datum and every open of the base, rather than only of the quasi-compact ones. It is false, by
`AlgebraicGeometry.not_affineCaseFlatteningCentreNoCompact`. -/
def AffineCaseFlatteningCentreNoCompact : Prop :=
  ∀ {T Y : Scheme.{u}} (p : Y ⟶ T) (G : Y.Modules), G.IsQuasicoherent →
    ∀ A : T.Opens, AffineChartFlatteningCentreUnderSourceHypotheses p G A

open AffineCase0815 in
/-- **`AlgebraicGeometry.AffineCaseFlatteningCentreNoCompact` is false**: the
quasi-compactness of `A` in
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace` cannot be
dropped.

The witness is `P = k[x₀, x₁, x₂, …]`, `T = Y = Spec P`, `p = 𝟙`, `A` the complement of the
closed point `m = (x₀, x₁, …)`, and `G` the structure sheaf of that closed point pushed
forward. Then `p` is locally of finite presentation, `G` is quasi-coherent of finite type, and
`G` restricted to `A` is the zero module, hence of finite presentation and flat over `A` — all
four hypotheses (2)-(5) of the source hold, and `A` is the only thing that is not quasi-compact.
But `m` is not the radical of a finitely generated ideal, so the only finitely presented centre
on the chart `V = ⊤` supported away from `A` is the unit centre, whose blowup is an
isomorphism; the predicate therefore demands that `G` be flat over `Spec P`, and it is not:
`x₀` is a nonzerodivisor of `P` killing the class of `1`. -/
theorem not_affineCaseFlatteningCentreNoCompact :
    ¬ AffineCaseFlatteningCentreNoCompact.{u} := by
  intro H
  have hzero : IsZero (modu.{u}.restrict (baseId.{u} ⁻¹ᵁ punctured.{u}).ι) :=
    isZero_modu_restrict _ baseId_preimage_punctured_le
  have hraw : AffineChartFlatteningCentre baseId.{u} modu.{u} punctured.{u} :=
    H baseId.{u} modu.{u} inferInstance punctured.{u} inferInstance inferInstance
      (isFinitePresentation_of_isZero _ hzero)
      (isFlatOver_of_isZero _ _ hzero)
  exact not_isFlatOver_modu
    (isFlatOver_of_affineChartFlatteningCentre_of_isAffine baseId.{u} modu.{u}
      punctured.{u} punctured_eq_top_of_isCompact hraw)

/-- **The witness open `punctured` is not quasi-compact.** -/
theorem AffineCase0815.not_isCompact_punctured :
    ¬ IsCompact (punctured.{u} : Set (Spec baseRing.{u})) := by
  intro hc
  have htop : punctured.{u} = ⊤ := punctured_eq_top_of_isCompact _ hc le_rfl
  have hmem : augPt.{u} ∈ punctured.{u} := htop ▸ trivial
  exact hmem rfl

end AlgebraicGeometry

end
