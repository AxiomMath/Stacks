module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartDescentSurjectiveSquare
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorChartBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductRepresentableEtaleConsequences
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EssentiallySurjectiveSpf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumSigma
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.UniqueLiftingAlongUniversalHomeomorphism

/-!
# Condition (3) implies condition (1) of Stacks 0ANG, from the axioms of a local property

Let `S` be a scheme contained in a big fppf site `B`, let `C` be a class of linearly topologized
rings and let `P` be a local property of morphisms of rings of the class, that is
`TopologicalRing.PropertyIsLocal P C`. This file proves the implication (3) ⟹ (1) of
**Stacks 0ANG** from the three axioms of Situation 0CBA themselves, following the source's
proof: axiom (1) carries `P` from the members of the covering of condition (3) to the charts of
a refinement, axiom (2) moves the target of each refined chart to the target of the given
diagram, axiom (3) assembles the finitely many refined charts into one map out of their
disjoint union, and axiom (2) descends `P` along the surjection of that disjoint union onto the
source of the given diagram.

## Main results

* `hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal`: condition (3) of
  Stacks 0ANG implies condition (1) for a local property `P`.

## References

* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Topology

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The size of a presenting ring -/

/-- **A weakly admissible topological ring with a countable fundamental system of neighbourhoods
of zero which carries a quotient system over `S` is smaller than the cutoff of the site.** Its
quotients by weak ideals of definition are the rings of affine schemes of the site, so are
smaller than the cutoff; a countable fundamental system of such ideals with zero intersection
embeds the ring into a countable product of them; and the cutoff, a strong limit cardinal of
uncountable cofinality, is closed under countable products. -/
theorem mk_lt_cutoff_of_isWeaklyAdmissible {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hc : (𝓝 (0 : A)).IsCountablyGenerated) (D : QuotientSystem B S hS A) :
    Cardinal.mk A < B.cutoff := by
  have := hA.2.2
  obtain ⟨I, hI⟩ := hA.1
  obtain ⟨x, hxopen, hx⟩ :=
    (IsLinearTopology.hasBasis_open_submodule A (M := A)).exists_antitone_subbasis
  let J : ℕ → TopologicalRing.WeakIdealOfDefinitionIndex A := fun n ↦
    ⟨I ⊓ x n, hI.1.inter (hxopen n), fun a ha ↦ hI.2 a (Ideal.mem_inf.mp ha).1⟩
  let Q : ℕ → Type u := fun n ↦ A ⧸ (J n).1
  have hQ (n : ℕ) : Cardinal.mk (Q n) < B.cutoff :=
    (le_max_right _ _).trans_lt ((Scheme.size_Spec (.of (A ⧸ (J n).1))).symm.trans_lt
      (D.inSite (J n)))
  have hsup : (⨆ n, Cardinal.mk (Q n)) < B.cutoff :=
    Cardinal.lift_iSup_lt_of_lt_cof_ord (by simpa using B.aleph0_lt_cutoff_cof) hQ
  have hinj :
      Function.Injective (Pi.ringHom fun n ↦ Ideal.Quotient.mk (J n).1 : A →+* ∀ n, Q n) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨n, -, hn⟩ := hx.toHasBasis.mem_iff.mp (compl_singleton_mem_nhds (Ne.symm hne))
    exact hn (Ideal.mem_inf.mp (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun ha n))).2 rfl
  calc Cardinal.mk A ≤ Cardinal.mk (∀ n, Q n) := Cardinal.mk_le_of_injective hinj
    _ = Cardinal.prod fun n ↦ Cardinal.mk (Q n) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod fun _ : ℕ ↦ ⨆ n, Cardinal.mk (Q n) :=
        Cardinal.prod_le_prod _ _ fun n ↦ le_ciSup Cardinal.bddAbove_of_small n
    _ = (⨆ n, Cardinal.mk (Q n)) ^ Cardinal.aleph0 := by simp [Cardinal.prod_const]
    _ < B.cutoff :=
        Cardinal.power_aleph0_lt_of_isStrongPrelimit B.aleph0_lt_cutoff
          B.cutoff_isStrongPrelimit hsup

/-! ### The class of rings -/

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- Every ring of the class `C` has a countable fundamental system of neighbourhoods of zero.
This holds for each of the classes `WAdm^count`, `WAdm^{adic*}` and `WAdm^{Noeth}` of
Stacks 0ANA, but `C` itself is an arbitrary predicate. -/
abbrev ClassHasCountableNhdsZero : Prop :=
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], C R → (𝓝 (0 : R)).IsCountablyGenerated

/-- The class `C` is stable under finite products, for the product topology. This is what makes
the target of the map assembled by axiom (3) of Situation 0CBA a ring of the class, as the
source's remark that the categories of Stacks 0ANA have finite products presupposes. -/
abbrev ClassIsStableUnderFinitePi : Prop :=
  ∀ {K : Type u} [Finite K] (A : K → Type u) [∀ k, CommRing (A k)] [∀ k, TopologicalSpace (A k)]
    [∀ k, IsTopologicalRing (A k)] [∀ k, IsLinearTopology (A k) (A k)],
    letI : IsLinearTopology (∀ k, A k) (∀ k, A k) := TopologicalRing.pi_isLinearTopology
    (∀ k, C (A k)) → C (∀ k, A k)

/-! ### Transporting the property between presentations -/

/-- A map of affine formal algebraic spaces presented, for *one* pair of presentations by rings
of the class `C`, by a continuous homomorphism with the property `P`, has `P` on every
presentation, provided `P` is invariant under isomorphism of sources and of targets: two
presentations of the same map differ by continuous ring isomorphisms of the presenting rings,
by Stacks 0AN0. -/
theorem hasPropertyOnAffineChartMap_of_presentation
    (hCw : ClassIsWeaklyAdmissible C)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} C P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    {U V : FppfSheaf B S hS} (t : U ⟶ V) {A R : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hCA : C A) (hCR : C R)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS R)
    (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E)
    (hgt : t = eU.hom ≫ formalSpectrumMap (hCw A hCA) g ≫ eV.inv) (hPg : P g.toRingHom) :
    HasPropertyOnAffineChartMap B S hS C P t := by
  have hAw := hCw A hCA
  have hRw := hCw R hCR
  intro A₁ R₁ _ _ _ _ _ _ _ _ hCA₁ hCR₁ hA₁ D₁ E₁ eU₁ eV₁ g₁ hg₁
  have hR₁ : TopologicalRing.IsWeaklyAdmissible R₁ := hCw R₁ hCR₁
  obtain ⟨gv, -, φ, hgv, -, hφ, -, hφc, hφc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hA₁ hAw (eV.symm ≪≫ eV₁)
  obtain ⟨gu, -, χ, hgu, -, hχ, -, hχc, hχc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hRw hR₁ (eU₁.symm ≪≫ eU)
  have hφr : φ.toRingHom = gv.toRingHom := RingHom.ext fun x ↦ congrFun hφ x
  have hχr : χ.toRingHom = gu.toRingHom := RingHom.ext fun x ↦ congrFun hχ x
  have hg₁eq : g₁ = ContinuousHom.comp hRw hA₁ gu (ContinuousHom.comp hAw hA₁ g gv) := by
    refine (existsUnique_continuousHom_formalSpectrumMap_eq hA₁ hR₁
      (eU₁.inv ≫ t ≫ eV₁.hom)).unique (by rw [hg₁]; simp) ?_
    rw [← formalSpectrumMap_comp_eq hRw hA₁ gu (ContinuousHom.comp hAw hA₁ g gv),
      ← formalSpectrumMap_comp_eq hAw hA₁ g gv, hgu, hgv, hgt]
    simp
  rw [hg₁eq, ContinuousHom.comp_toRingHom, ContinuousHom.comp_toRingHom, ← hφr, ← hχr]
  exact htgt hCA₁ hCR hCR₁ _ χ (g.continuous.comp hφc) hχc hχc'
    (hsrc hCA hCA₁ hCR g.toRingHom φ g.continuous hφc hφc' hPg)

/-! ### Axiom (3) of Situation 0CBA, read on charts -/

attribute [local instance] sheaf_hasColimits TopologicalRing.pi_isLinearTopology

/-- **Axiom (3) of Situation 0CBA, read on affine formal algebraic charts.** If `P` holds on
each member of a finite family of maps `Wₛ ⟶ V` of charts of the class `C`, then it holds on the
map `∐ₛ Wₛ ⟶ V` they induce. The disjoint union is the formal spectrum of the product of the
rings presenting its summands, with the inclusions the formal spectra of the projections
(`AlgebraicGeometry.FormalSpace.ι_sigmaFormalSpectrumIso_hom`), so the map out of it is
presented by the homomorphism into the product assembled from the homomorphisms presenting
the members, to which axiom (3) applies. -/
theorem hasPropertyOnAffineChartMap_sigmaDesc
    (hCw : ClassIsWeaklyAdmissible C) (hCc : ClassHasCountableNhdsZero C)
    (hCpi : ClassIsStableUnderFinitePi C)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} C P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    (hP : TopologicalRing.PropertyIsLocal P C)
    {σ : Type (u + 1)} [Finite σ] (W : σ → FppfSheaf B S hS) {V : FppfSheaf B S hS}
    (h : ∀ s, W s ⟶ V) (hW : ∀ s, IsChartOfClass B S hS C (W s))
    (hV : IsChartOfClass B S hS C V) (hh : ∀ s, HasPropertyOnAffineChartMap B S hS C P (h s)) :
    HasPropertyOnAffineChartMap B S hS C P (Sigma.desc h) := by
  classical
  obtain ⟨A, _, _, _, _, hCA, D, ⟨eV⟩⟩ := hV
  have hAw := hCw A hCA
  choose R iCR iTS iTR iLT hCR E hE using hW
  let := iCR
  let := iTS
  let := iTR
  let := iLT
  have eW : ∀ s, W s ≅ formalSpectrum (E s) := fun s ↦ (hE s).some
  let : Small.{u} σ := Countable.toSmall.{u} σ
  let e : Shrink.{u} σ ≃ σ := (equivShrink.{u} σ).symm
  have : Finite (Shrink.{u} σ) := Finite.of_equiv _ e.symm
  let : Fintype (Shrink.{u} σ) := Fintype.ofFinite _
  let R' : Shrink.{u} σ → Type u := fun k ↦ R (e k)
  have hR'w : ∀ k, TopologicalRing.IsWeaklyAdmissible (R' k) := fun k ↦ hCw _ (hCR (e k))
  let E' : ∀ k, QuotientSystem B S hS (R' k) := fun k ↦ E (e k)
  let Θ := sigmaFormalSpectrumIso B S hS R' hR'w E'
  let Ψ : (∐ W) ≅
      formalSpectrum (sigmaFormalSpectrumPresentation B S hS R' hR'w E').quotientSystem :=
    (Sigma.whiskerEquiv e fun k ↦ eW (e k)).symm ≪≫ Θ
  have hpiw := TopologicalRing.isWeaklyAdmissible_pi R' hR'w
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAw hpiw
    (Ψ.inv ≫ Sigma.desc h ≫ eV.hom)
  have hgt : Sigma.desc h = Ψ.hom ≫ formalSpectrumMap hAw g ≫ eV.inv := by
    rw [hg]
    simp
  refine hasPropertyOnAffineChartMap_of_presentation B S hS C P hCw hsrc htgt _ hCA
    (hCpi R' fun k ↦ hCR (e k)) D _ Ψ eV g hgt ?_
  rw [show g.toRingHom = RingHom.pi fun k ↦ (Pi.evalRingHom R' k).comp g.toRingHom from
    RingHom.ext fun _ ↦ funext fun _ ↦ rfl]
  refine hP.finiteProduct hAw (hCc A hCA) R' hR'w (fun k ↦ hCc _ (hCR (e k))) _
    (fun k ↦ (continuous_apply k).comp g.continuous) hCA (fun k ↦ hCR (e k)) fun k ↦ ?_
  let gk := ContinuousHom.comp hpiw hAw (piProjContinuousHom B S hS R' hR'w E' k) g
  -- the `k`-th inclusion of the disjoint union, read through `Ψ`
  have hι : Sigma.ι W (e k) ≫ (Sigma.whiskerEquiv e fun k ↦ eW (e k)).inv =
      (eW (e k)).hom ≫ Sigma.ι (fun k ↦ formalSpectrum (E' k)) k := by
    have h1 : Sigma.ι (fun k ↦ formalSpectrum (E' k)) k ≫
        (Sigma.whiskerEquiv e fun k ↦ eW (e k)).hom = (eW (e k)).inv ≫ Sigma.ι W (e k) :=
      Sigma.ι_comp_map' _ _ k
    rw [← cancel_epi (eW (e k)).inv, ← reassoc_of% h1, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  have hk : h (e k) = (eW (e k)).hom ≫ formalSpectrumMap hAw gk ≫ eV.inv := by
    rw [← formalSpectrumMap_comp_eq hpiw hAw (piProjContinuousHom B S hS R' hR'w E' k) g,
      ← ι_sigmaFormalSpectrumIso_hom B S hS R' hR'w E' k, ← Sigma.ι_desc h (e k), hgt]
    simp only [Ψ, Iso.trans_hom, Iso.symm_hom, Category.assoc, reassoc_of% hι, Θ]
  exact hh (e k) A (R' k) hCA (hCR (e k)) hAw D (E' k) (eW (e k)) eV gk hk

/-! ### Charts of the class -/

/-- A chart of a class of weakly admissible rings with countable fundamental systems of
neighbourhoods of zero is presented by a ring of the class below the cutoff of the site, by
`AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_isWeaklyAdmissible`. -/
theorem hasPresentationOfClass_of_isChartOfClass (hCw : ClassIsWeaklyAdmissible C)
    (hCc : ClassHasCountableNhdsZero C) {U : FppfSheaf B S hS}
    (hU : IsChartOfClass B S hS C U) : HasPresentationOfClass B S hS C U := by
  obtain ⟨A, _, _, _, _, hCA, D, ⟨eU⟩⟩ := hU
  exact ⟨A, _, _, _, _, D, hCA, hCw A hCA, hCc A hCA,
    mk_lt_cutoff_of_isWeaklyAdmissible B S hS (hCw A hCA) (hCc A hCA) D, ⟨eU⟩⟩

/-- **An affine formal algebraic space representable étale over a chart of the class is a chart
of the class**, provided the class is stable under completion along étale maps. By the
essential-surjectivity clause of **Stacks 0AN8**,
`AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf`, it is the formal spectrum of the
completion of an étale algebra over the ring presenting the chart. -/
theorem isChartOfClass_of_isRepresentableEtale (hCw : ClassIsWeaklyAdmissible C)
    (hCc : ClassHasCountableNhdsZero C) (hCcompl : ClassIsStableUnderEtaleCompletion C)
    {W U : FppfSheaf B S hS} (w : W ⟶ U) (hU : IsChartOfClass B S hS C U)
    (hW : IsAffineFormalAlgebraicSpace B S hS W) (hw : IsRepresentableEtale B S hS w) :
    IsChartOfClass B S hS C W := by
  obtain ⟨A, _, _, _, _, hCA, D, ⟨eU⟩⟩ := hU
  have hAw := hCw A hCA
  obtain ⟨A', _, _, _, E, -, ε, -, -⟩ := isEssentiallySurjectiveSpf B S hS A hAw D
    (hasLargeSite_of_mk_lt_cutoff D (mk_lt_cutoff_of_isWeaklyAdmissible B S hS hAw (hCc A hCA) D))
    W (w ≫ eU.hom) hW
    (IsRepresentableEtale.comp B S hS hw (isRepresentableEtale_iso_hom B S hS eU))
  exact ⟨_, _, _, _, _, hCcompl (algebraMap A A') hCA hAw
    (RingHom.etale_algebraMap.2 inferInstance), E, ⟨ε⟩⟩

/-! ### Axiom (2) of Situation 0CBA on charts, at every presentation -/

/-- Condition `IsEssentiallySurjectiveSpf` of Stacks 0AN8 holds on the site. -/
private theorem isEssentiallySurjectiveSpf_of_mk_lt_cutoff : IsEssentiallySurjectiveSpf B S hS :=
  fun R _ _ _ _ hR hRcard D V v hV hv ↦
    isEssentiallySurjectiveSpf B S hS R hR D (hasLargeSite_of_mk_lt_cutoff D hRcard) V v hV hv

/-- **Axiom (2) of Situation 0CBA, read on affine formal algebraic charts for a single
surjective chart change, with no invariance of `P` under isomorphism.** Let `P` be a local
property of morphisms of rings of the class `C`, and let

    W ⟶ Z
    │     │
    U ⟶ V

be a commuting square of affine formal algebraic spaces whose vertical maps are representable
étale and whose left vertical map `W ⟶ U` is surjective. If `P` holds on the upper map `W ⟶ Z`
for every presentation by rings of the class, then it holds on the lower map `t : U ⟶ V` for
every presentation by rings of the class.

This is `hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_presentation` without its
hypotheses `hsrc` and `htgt`. There the localization diagram is built on one chosen presentation
of `t` and `P` is then transported to the others along isomorphisms of presenting rings; here it
is built on the presentation of `t` at hand, which needs no transport. The presenting rings are
below the cutoff of the site by `AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_isWeaklyAdmissible`,
which is what the localization diagram of `exists_localizationDiagram_of_chartSquare` asks; its
upper map presents `W ⟶ Z`, so has `P` by hypothesis; its source edge is faithfully flat by
**Stacks 0AN9**; and axiom (2) carries `P` to its lower map, the given presentation of `t`. -/
theorem hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_isLocal
    (hCw : ClassIsWeaklyAdmissible C) (hCc : ClassHasCountableNhdsZero C)
    (hCcompl : ClassIsStableUnderEtaleCompletion C)
    (hP : TopologicalRing.PropertyIsLocal P C)
    {U V W Z : FppfSheaf B S hS} (t : U ⟶ V) (p : W ⟶ U) (m : W ⟶ Z) (r : Z ⟶ V)
    (hW : IsAffineFormalAlgebraicSpace B S hS W)
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z)
    (hp : IsRepresentableEtale B S hS p) (hr : IsRepresentableEtale B S hS r)
    (hpsurj : Sheaf.IsLocallySurjective p) (hsq : p ≫ t = m ≫ r)
    (hm : HasPropertyOnAffineChartMap B S hS C P m) :
    HasPropertyOnAffineChartMap B S hS C P t := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hAw D E eU eV g hgt
  have hRw : TopologicalRing.IsWeaklyAdmissible R := hCw R hCR
  have hAc := hCc A hCA
  have hRc := hCc R hCR
  have hg : formalSpectrumMap hAw g = eU.inv ≫ t ≫ eV.hom := by
    rw [hgt]
    simp
  have hpe : IsRepresentableEtale B S hS (p ≫ eU.hom) :=
    IsRepresentableEtale.comp B S hS hp (isRepresentableEtale_iso_hom B S hS eU)
  have hre : IsRepresentableEtale B S hS (r ≫ eV.hom) :=
    IsRepresentableEtale.comp B S hS hr (isRepresentableEtale_iso_hom B S hS eV)
  have hsq' : (p ≫ eU.hom) ≫ formalSpectrumMap hAw g = m ≫ r ≫ eV.hom := by
    rw [hg, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hsq, Category.assoc]
  obtain ⟨R', A', _, _, Dg, E', D', g', cq, eU', eV', hmap, hcm, hcq, hεq, hpres'⟩ :=
    exists_localizationDiagram_of_chartSquare B S hS
      (isEssentiallySurjectiveSpf_of_mk_lt_cutoff B S hS) hAw hRw hAc hRc
      (mk_lt_cutoff_of_isWeaklyAdmissible B S hS hAw hAc D)
      (mk_lt_cutoff_of_isWeaklyAdmissible B S hS hRw hRc E) g
      m (p ≫ eU.hom) (r ≫ eV.hom) hW hZ hpe hre hsq'
  have hCAc : C (TopologicalRing.CompletionOver Dg.toB') :=
    hCcompl Dg.toB' hCA hAw Dg.etaleB
  have hCRc : C (TopologicalRing.CompletionOver Dg.toA') :=
    hCcompl Dg.toA' hCR hRw Dg.etaleA
  -- `P` on the upper map of the diagram, which presents the given map of charts
  have hPcm : P Dg.completedMap := by
    rw [hcm]
    exact hm (TopologicalRing.CompletionOver Dg.toB')
      (TopologicalRing.CompletionOver Dg.toA') hCAc hCRc
      (TopologicalRing.completionOver_isWeaklyAdmissible Dg.toB' hAw) D' E' eU' eV' g' hpres'
  -- the source edge of the diagram is faithfully flat, by Stacks 0AN9
  have hff : Dg.toA'.FaithfullyFlat := by
    have hfac : eU'.inv ≫ p ≫ eU.hom = formalSpectrumMap hRw cq := by
      rw [← hεq, Iso.inv_hom_id_assoc]
    have hep : Epi p := (Sheaf.isLocallySurjective_iff_epi p).mp hpsurj
    have hls : Sheaf.IsLocallySurjective (formalSpectrumMap hRw cq) := by
      rw [Sheaf.isLocallySurjective_iff_epi, ← hfac]
      infer_instance
    exact ((etaleFormalSpectrumMap_surjective_tfae B S hS Dg.toA' Dg.etaleA hRw E E' cq
      hcq).out 1 2).mp (isSurjective_of_isLocallySurjective B S hS hls)
  rw [← hmap]
  exact hP.faithfullyFlatDescent Dg hCR hCA hCRc hCAc hff hPcm

/-! ### Stacks 0ANG, condition (3) implies condition (1) -/

/-- **Stacks 0ANG, condition (3), with the charts of the covering of the class.** There is an
affine étale covering of the source, each member of which is a chart of the class `C` and
factors through a chart of the class `C` representable étale over the target by a map with
`P`. This is `AlgebraicGeometry.FormalSpace.HasPropertyAfterSourceCover` together with the
membership of the charts of the covering in the class, which condition (3) of the source
presupposes when it speaks of a morphism of `WAdm^count` (resp. of `WAdm^{adic*}`). -/
abbrev HasPropertyAfterSourceCoverOfClass {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U u ∧
      ∀ i, ∃ (V : FppfSheaf B S hS) (v : V ⟶ Y) (t : U i ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS V ∧ IsRepresentableEtale B S hS v ∧
          u i ≫ f = t ≫ v ∧ IsChartOfClass B S hS C (U i) ∧ IsChartOfClass B S hS C V ∧
            HasPropertyOnAffineChartMap B S hS C P t

/-- Condition (3) of Stacks 0ANG gives its form with charts of the class when every affine
formal algebraic space representable étale over the source, and every one representable étale
over the target, is a chart of the class — which is the implication (2) ⟹ (1) of
**Stacks 0AKX** for a locally countably indexed, resp. locally adic\*, formal algebraic space. -/
theorem hasPropertyAfterSourceCoverOfClass_of_afterSourceCover {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (hX : ∀ (U : FppfSheaf B S hS) (a : U ⟶ X), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → IsChartOfClass B S hS C U)
    (hY : ∀ (V : FppfSheaf B S hS) (b : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS b → IsChartOfClass B S hS C V)
    (hf : HasPropertyAfterSourceCover B S hS C P f) :
    HasPropertyAfterSourceCoverOfClass B S hS C P f := by
  obtain ⟨I, U, u, hcover, hfac⟩ := hf
  refine ⟨I, U, u, hcover, fun i ↦ ?_⟩
  obtain ⟨V, v, t, hV, hv, hsq, hP⟩ := hfac i
  exact ⟨V, v, t, hV, hv, hsq, hX (U i) (u i) (hcover.1 i) (hcover.2.1 i), hY V v hV hv, hP⟩

/-- **Stacks 0ANG, condition (3) implies condition (1), from the axioms of a local property.**
Let `P` be a local property of morphisms of rings of a class `C`, invariant under isomorphism
of sources and of targets as Situation 0CBA requires, the class consisting of weakly
admissible rings with countable fundamental systems of neighbourhoods of zero and being stable
under completion along étale maps and under finite products. If `f : X ⟶ Y` has an affine étale
covering of its source by charts of the class, each factoring through a chart of the class
representable étale over the target by a map with `P`, then `P` holds on every affine étale
diagram over `f`.

The proof is the source's. A diagram `U₀ ⟶ V₀` over `f` is given, and `P` is to be shown on any
presentation of it by rings of the class, so `U₀` and `V₀` are charts of the class. The covering
is refined against the diagram by `href` into a finite affine étale covering `{Wₛ ⟶ U₀}` with
maps `Wₛ ⟶ Zₛ` to charts `Zₛ` representable étale over `V₀` and over a target chart `Vᵢ` of the
covering; every `Wₛ` and `Zₛ` is a chart of the class by
`AlgebraicGeometry.FormalSpace.isChartOfClass_of_isRepresentableEtale`. Axiom (1) carries `P`
to `Wₛ ⟶ Zₛ`; axiom (2), applied to a square whose source edge is an identity, carries it to
`Wₛ ⟶ V₀`; axiom (3) carries it to `∐ₛ Wₛ ⟶ V₀`; and axiom (2) descends it along the
surjective representable étale map `∐ₛ Wₛ ⟶ U₀`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover_of_isLocal
    (hCw : ClassIsWeaklyAdmissible C) (hCc : ClassHasCountableNhdsZero C)
    (hCcompl : ClassIsStableUnderEtaleCompletion C) (hCpi : ClassIsStableUnderFinitePi C)
    (hsrc : PropertyIsInvariantUnderSourceIso.{u} C P)
    (htgt : PropertyIsInvariantUnderTargetIsoOn.{u} C P)
    (hP : TopologicalRing.PropertyIsLocal P C) {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (href : HasEtaleRefinementOfSourceCover B S hS f)
    (hf : HasPropertyAfterSourceCoverOfClass B S hS C P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS C P f := by
  have hES := isEssentiallySurjectiveSpf_of_mk_lt_cutoff B S hS
  obtain ⟨I, U, u, hUcover, hfac⟩ := hf
  choose V v t hVaff hVet hVsq hUc hVc hVP using hfac
  intro U₀ V₀ a b τ hU₀ hV₀ ha hb hsq
  suffices hτ : IsChartOfClass B S hS C U₀ → IsChartOfClass B S hS C V₀ →
      HasPropertyOnAffineChartMap B S hS C P τ by
    intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
    exact hτ ⟨R, _, _, _, _, hCR, E, ⟨eU⟩⟩ ⟨A, _, _, _, _, hCA, D, ⟨eV⟩⟩
      A R hCA hCR hA D E eU eV g hg
  intro hU₀c hV₀c
  obtain ⟨σ, hσ, k, W, Z, p, q, m, r, c, hWcover, hZaff, hq, hr, hc, hsq₁, hsq₂⟩ :=
    href U V u v t hUcover hVaff hVet hVsq U₀ V₀ a b τ hU₀ hV₀ ha hb hsq
  have := hσ
  have pres := fun {T : FppfSheaf B S hS} (hT : IsChartOfClass B S hS C T) ↦
    hasPresentationOfClass_of_isChartOfClass B S hS C hCw hCc hT
  have hWc : ∀ s, IsChartOfClass B S hS C (W s) := fun s ↦
    isChartOfClass_of_isRepresentableEtale B S hS C hCw hCc hCcompl (p s) hU₀c (hWcover.1 s)
      (hWcover.2.1 s)
  have hZc : ∀ s, IsChartOfClass B S hS C (Z s) := fun s ↦
    isChartOfClass_of_isRepresentableEtale B S hS C hCw hCc hCcompl (c s) hV₀c (hZaff s) (hc s)
  -- axiom (1): from the members of the covering to the refined charts
  have hm : ∀ s, HasPropertyOnAffineChartMap B S hS C P (m s) := fun s ↦
    hasPropertyOnAffineChartMap_of_etaleSquare_of_propertyIsLocal B S hS C P
      hES hCw hCcompl hsrc htgt hP (t (k s)) (m s) (q s) (r s)
      (pres (hUc (k s))) (pres (hVc (k s))) (hWcover.1 s) (hZaff s) (hq s) (hr s) (hsq₁ s)
      (hVP (k s))
  -- axiom (2) along an identity: to the target of the given diagram
  have hmc : ∀ s, HasPropertyOnAffineChartMap B S hS C P (m s ≫ c s) := fun s ↦
    hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_presentation B S hS C P
      hES hCw hCcompl hsrc htgt hP (m s ≫ c s) (𝟙 _) (m s) (c s)
      (pres (hWc s)) (pres hV₀c) (hWcover.1 s) (hZaff s)
      (isRepresentableEtale_iso_hom B S hS (Iso.refl _)) (hc s)
      ((Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance) (Category.id_comp _) (hm s)
  -- axiom (3): to the disjoint union
  have hσP := hasPropertyOnAffineChartMap_sigmaDesc B S hS C P hCw hCc hCpi hsrc htgt hP W
    (fun s ↦ m s ≫ c s) hWc hV₀c hmc
  -- axiom (2) along the disjoint union
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hpd, hpd'⟩ := coproductsRepresentableEtale B S hS σ W U₀ p hσ hWcover.2.1
  exact hasPropertyOnAffineChartMap_of_surjectiveChartSquare_of_presentation B S hS C P
    hES hCw hCcompl hsrc htgt hP τ (Sigma.desc p)
    (Sigma.desc fun s ↦ m s ≫ c s) (𝟙 _) (pres hU₀c) (pres hV₀c)
    (isAffineFormalAlgebraicSpace_sigma B S hS W hWcover.1) hV₀
    ⟨hpd, hpd'⟩ (isRepresentableEtale_iso_hom B S hS (Iso.refl _)) hWcover.2.2
    (Sigma.hom_ext _ _ fun s ↦ by simp [hsq₂]) hσP

end AlgebraicGeometry.FormalSpace

end
