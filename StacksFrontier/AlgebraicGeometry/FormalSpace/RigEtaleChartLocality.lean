module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EssentiallySurjectiveSpf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.RingTheory.Rig.RigEtaleIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverNoetherian

/-!
# Rig-étaleness on affine charts along representable étale maps

Let `S` be a scheme contained in a big fppf site `B`. This file reads the locality of
rig-étaleness (Stacks 0AQL) on morphisms of affine formal algebraic spaces, through the
equivalence of Stacks 0AN8 between representable étale morphisms into `Spf R` and completions
of étale `R`-algebras, and the full faithfulness of `Spf` (Stacks 0AN0).

## Main results

* `AlgebraicGeometry.FormalSpace.exists_etale_completion_of_isRepresentableEtale`: an affine
  formal algebraic space representable étale over `Spf R`, for `R` Noetherian adic, is the
  formal spectrum of the completion of an étale `R`-algebra.
* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_isRepresentableEtale`:
  rig-étaleness of a chart map `U ⟶ V` presented by Noetherian adic rings ascends to every
  square `U' ⟶ V'` over it whose vertical maps are representable étale.

## Implementation notes

The ascent is axiom (1) of Situation 0CBA, `Rig.rigEtale_localizationPreserves`, applied to the
localization diagram that Stacks 0AN8 attaches to the square, followed by the transport of
rig-étaleness along the isomorphisms of topological rings relating that diagram to the given
presentation of `U' ⟶ V'` (`Rig.isRigEtale_ringEquiv_comp_comp`).

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AQL](https://stacks.math.columbia.edu/tag/0AQL)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AN8 for a Noetherian adic ring.** An affine formal algebraic space `U'` with a
representable étale morphism to an affine formal algebraic space presented by a Noetherian adic
ring `R` is the formal spectrum of the completion of an étale `R`-algebra, compatibly with the
morphisms to `Spf R`. The site condition of Stacks 0AIF holds for `R`, its cardinality being
bounded by the cutoff of the site. -/
theorem exists_etale_completion_of_isRepresentableEtale {U U' : FppfSheaf B S hS}
    (q : U' ⟶ U) (hU' : IsAffineFormalAlgebraicSpace B S hS U')
    (hq : IsRepresentableEtale B S hS q) (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hR : TopologicalRing.IsAdic R)
    (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Algebra.Etale R R₁)
      (E₁ : QuotientSystem B S hS (CompletionOver (algebraMap R R₁)))
      (c : ContinuousHom E E₁) (ε : U' ≅ formalSpectrum E₁),
      c.toRingHom = CompletionOver.canonicalMap (algebraMap R R₁) ∧
        ε.hom ≫ formalSpectrumMap hR.isWeaklyAdmissible c = q ≫ eU.hom := by
  have hRw := hR.isWeaklyAdmissible
  exact exists_etale_completion_iso_of_isRepresentableEtale B S hS R hRw E
    (hasLargeSite_of_mk_lt_cutoff E (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hR E)) U'
    (q ≫ eU.hom) hU' (hq.comp B S hS (isRepresentableEtale_of_isIso B S hS eU.hom))
    ⟨hRw.1.choose, hRw.1.choose_spec⟩

/-- Two continuous homomorphisms over `S` with the same formal spectrum have the same
underlying ring map: this is the uniqueness clause of Stacks 0AN0. -/
theorem toRingHom_eq_of_formalSpectrumMap_eq {A C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} {g g' : ContinuousHom D E}
    (h : formalSpectrumMap hA g = formalSpectrumMap hA g') : g.toRingHom = g'.toRingHom := by
  obtain ⟨g₀, -, hu⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hC
    (formalSpectrumMap hA g)
  rw [hu g rfl, hu g' h.symm]

/-- The completion of a finite type algebra over a Noetherian adic ring is Noetherian adic. -/
private theorem isNoetherianAdic_completionOver_algebraMap {R R₁ : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] [CommRing R₁]
    [Algebra R R₁] [Algebra.FiniteType R R₁] (hR : TopologicalRing.IsNoetherianAdic R) :
    TopologicalRing.IsNoetherianAdic (CompletionOver (algebraMap R R₁)) :=
  have : IsNoetherianRing R := hR.2
  completionOver_isNoetherianAdic _ hR (Algebra.FiniteType.isNoetherianRing R R₁)

/-- **Rig-étaleness ascends along representable étale squares of affine charts.** Let
`t : U ⟶ V` be a morphism of affine formal algebraic spaces presented, by Noetherian adic rings,
by a rig-étale continuous homomorphism `g`. Then every morphism `t' : U' ⟶ V'` of affine formal
algebraic spaces fitting in a commutative square `q ≫ t = t' ≫ r` with `q`, `r` representable
étale corresponds to a rig-étale arrow of `WAdm^{Noeth}`, for every presentation of it.

By Stacks 0AN8, `q` and `r` are the formal spectra of the completions `R → R₁^` and `A → A₁^` of
étale algebras, and by Stacks 0AN0 the square is the formal spectrum of a localization diagram,
so axiom (1) of Situation 0CBA makes the induced map `A₁^ → R₁^` rig-étale; a second
presentation of `t'` differs from that one by isomorphisms of topological rings. -/
theorem hasPropertyOnAffineChartMap_of_isRepresentableEtale
    {U V U' V' : FppfSheaf B S hS} (t : U ⟶ V) (t' : U' ⟶ V') (q : U' ⟶ U) (r : V' ⟶ V)
    (hU' : IsAffineFormalAlgebraicSpace B S hS U') (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (hq : IsRepresentableEtale B S hS q) (hr : IsRepresentableEtale B S hS r)
    (hcomm : q ≫ t = t' ≫ r)
    (A R : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hCA : TopologicalRing.IsNoetherianAdic A) (hCR : TopologicalRing.IsNoetherianAdic R)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
    (g : ContinuousHom D E) (hg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv)
    (hP : TopologicalRing.IsRigEtaleHom g.toRingHom) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic
      TopologicalRing.IsRigEtaleHom t' := by
  intro A' R' _ _ _ _ _ _ _ _ hCA' hCR' hA'w D' E' eU' eV' g' hg'
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing R := hCR.2
  have hRw := hCR.1.isWeaklyAdmissible
  have hR'w := hCR'.1.isWeaklyAdmissible
  obtain ⟨R₁, _, _, _, E₁, cU, εU, hcU, hεU⟩ :=
    exists_etale_completion_of_isRepresentableEtale B S hS q hU' hq R hCR.1 E eU
  obtain ⟨A₁, _, _, _, D₁, cV, εV, hcV, hεV⟩ :=
    exists_etale_completion_of_isRepresentableEtale B S hS r hV' hr A hCA.1 D eV
  have hR₁ := isNoetherianAdic_completionOver_algebraMap (R₁ := R₁) hCR
  have hA₁ := isNoetherianAdic_completionOver_algebraMap (R₁ := A₁) hCA
  have hR₁w := hR₁.1.isWeaklyAdmissible
  have hA₁w := hA₁.1.isWeaklyAdmissible
  obtain ⟨h, hh, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA₁w hR₁w
    (εU.inv ≫ t' ≫ εV.hom)
  -- the square is the formal spectrum of a localization diagram
  have hspf : formalSpectrumMap hRw cU ≫ formalSpectrumMap hA g =
      formalSpectrumMap hA₁w h ≫ formalSpectrumMap hA cV := by
    rw [hh, Category.assoc, Category.assoc, hεV, ← reassoc_of% hcomm,
      show t ≫ eV.hom = eU.hom ≫ formalSpectrumMap hA g by simp [hg], ← reassoc_of% hεU,
      Iso.inv_hom_id_assoc]
  have hring : cU.toRingHom.comp g.toRingHom = h.toRingHom.comp cV.toRingHom := by
    rw [formalSpectrumMap_comp_eq hRw hA, formalSpectrumMap_comp_eq hA₁w hA] at hspf
    exact toRingHom_eq_of_formalSpectrumMap_eq B S hS hA hR₁w hspf
  let LD : LocalizationDiagram R A R₁ A₁ :=
    { toA' := algebraMap R R₁
      toB' := algebraMap A A₁
      map := g.toRingHom
      completedMap := h.toRingHom
      weaklyAdmissibleA := hRw
      weaklyAdmissibleB := hA
      countableA := Rig.countablyGenerated_nhds_of_isAdicRing hCR.1
      countableB := Rig.countablyGenerated_nhds_of_isAdicRing hCA.1
      etaleA := RingHom.etale_algebraMap.mpr inferInstance
      etaleB := RingHom.etale_algebraMap.mpr inferInstance
      continuousMap := g.continuous
      continuousCompletedMap := h.continuous
      commutes := by rwa [← hcU, ← hcV] }
  have hrig : RingHom.IsRigEtaleArrow h.toRingHom :=
    Rig.rigEtale_localizationPreserves LD hCR hCA hR₁ hA₁ hP
  -- a second presentation of `t'` differs from this one by isomorphisms of topological rings
  obtain ⟨gU, -, φU, hgU, -, hφU, -, hφUc, hφUc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hR₁w hR'w (eU'.symm ≪≫ εU)
  obtain ⟨-, gV', φV, -, hgV', -, hφV', hφVc, hφVc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hA₁w hA'w (eV'.symm ≪≫ εV)
  have hspf' : formalSpectrumMap hA'w g' = formalSpectrumMap hA'w
      (ContinuousHom.comp hA₁w hA'w (ContinuousHom.comp hR₁w hA₁w gU h) gV') := by
    rw [← formalSpectrumMap_comp_eq hA₁w hA'w, ← formalSpectrumMap_comp_eq hR₁w hA₁w, hgU, hh,
      hgV', hg']
    simp
  have hring' : g'.toRingHom =
      (φU : CompletionOver (algebraMap R R₁) →+* R').comp
        (h.toRingHom.comp (φV.symm : A' →+* CompletionOver (algebraMap A A₁))) := by
    rw [toRingHom_eq_of_formalSpectrumMap_eq B S hS hA'w hR'w hspf']
    ext x
    simp [hφU, hφV']
  intro _ _ _ _
  have : IsNoetherianRing (CompletionOver (algebraMap R R₁)) := hR₁.2
  have : IsNoetherianRing (CompletionOver (algebraMap A A₁)) := hA₁.2
  refine ⟨g'.continuous, ?_⟩
  rw [hring']
  exact Rig.isRigEtale_ringEquiv_comp_comp hA₁.1 hCA'.1 hR₁.1 hCR'.1 φV.symm hφVc' hφVc φU hφUc
    hφUc' h.toRingHom hrig.1 hrig.2

/-- A continuous ring map `π : C' → C` under two continuous homomorphisms `c : A → C'` and
`d : A → C` over `S`, with `π ∘ c = d`, is a continuous homomorphism over `S` for the quotient
systems of `C'` and `C`: both structure maps to `S` are read off from that of `A`. -/
def ContinuousHom.ofComp {A C' C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C'] [TopologicalSpace C']
    [CommRing C] [TopologicalSpace C] (hA : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} {E' : QuotientSystem B S hS C'} {E : QuotientSystem B S hS C}
    (c : ContinuousHom D E') (d : ContinuousHom D E) (π : C' →+* C) (hπ : Continuous π)
    (hcomp : π.comp c.toRingHom = d.toRingHom) : ContinuousHom E' E where
  toRingHom := π
  continuous := hπ
  overS J' K h := by
    obtain ⟨J, hJ⟩ := exists_isWeakIdealOfDefinition_le_comap hA.1 c.toRingHom c.continuous J'
    have hJK : J.1 ≤ Ideal.comap d.toRingHom K.1 := by
      rw [← hcomp, ← Ideal.comap_comap]
      exact hJ.trans (Ideal.comap_mono h)
    rw [← c.overS J J' hJ, ← d.overS J K hJK, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
    simp [← hcomp]

/-- **A finite affine étale covering of `Spf R` by completed étale charts is faithfully flat.**
If `Spf (Rₛ)^ ⟶ Spf R` are the formal spectra of the completions of finitely many étale
`R`-algebras and they jointly cover `Spf R` as in Definition 0AIM, then `R → ∏ₛ Rₛ` is
faithfully flat.

The family factors through `Spf (∏ₛ Rₛ)^ ⟶ Spf R`, which is therefore a surjection of sheaves,
hence surjective on points, so `R → ∏ₛ Rₛ` is faithfully flat by Stacks 0AN9. -/
theorem faithfullyFlat_pi_of_isLocallySurjective {σ : Type u} [Fintype σ]
    (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsAdic R) (E : QuotientSystem B S hS R) {U : FppfSheaf B S hS}
    (eU : U ≅ formalSpectrum E) (R' : σ → Type u) [∀ s, CommRing (R' s)]
    [∀ s, Algebra R (R' s)] [∀ s, Algebra.Etale R (R' s)]
    (E' : ∀ s, QuotientSystem B S hS (CompletionOver (algebraMap R (R' s))))
    (c : ∀ s, ContinuousHom E (E' s))
    (hc : ∀ s, (c s).toRingHom = CompletionOver.canonicalMap (algebraMap R (R' s)))
    (W : σ → FppfSheaf B S hS) (ε : ∀ s, W s ≅ formalSpectrum (E' s)) (p : ∀ s, W s ⟶ U)
    (hp : ∀ s, (ε s).hom ≫ formalSpectrumMap hR.isWeaklyAdmissible (c s) = p s ≫ eU.hom)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc p)) :
    Module.FaithfullyFlat R (∀ s, R' s) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hRw := hR.isWeaklyAdmissible
  let f : R →+* ∀ s, R' s := Pi.ringHom fun s ↦ algebraMap R (R' s)
  have hEl : E.HasLargeSite :=
    hasLargeSite_of_mk_lt_cutoff E (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hR E)
  have hfa : f.toAlgebra = (inferInstance : Algebra R (∀ s, R' s)) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  have hft : let : Algebra R (∀ s, R' s) := f.toAlgebra; Algebra.FiniteType R (∀ s, R' s) := by
    rw [hfa]
    infer_instance
  obtain ⟨Q, cQ, hcQ⟩ := exists_completionOver_quotientSystem B S hS f hft hRw E hEl
  let Φ := CompletionOver.piRingEquiv fun s ↦ algebraMap R (R' s)
  have hπ : ∀ s, ((Pi.evalRingHom (fun s ↦ CompletionOver (algebraMap R (R' s))) s).comp
      (Φ : CompletionOver f →+* _)).comp cQ.toRingHom = (c s).toRingHom := by
    intro s
    refine RingHom.ext fun a ↦ ?_
    rw [hc, hcQ]
    exact congrFun (CompletionOver.piRingEquiv_canonicalMap _ a) s
  let π : ∀ s, ContinuousHom Q (E' s) := fun s ↦ ContinuousHom.ofComp B S hS hRw cQ (c s)
    ((Pi.evalRingHom (fun s ↦ CompletionOver (algebraMap R (R' s))) s).comp
      (Φ : CompletionOver f →+* _))
    ((continuous_apply s).comp (CompletionOver.continuous_piRingEquiv _)) (hπ s)
  have hQw := TopologicalRing.completionOver_isWeaklyAdmissible f hRw
  have hfac : Sigma.desc (fun s ↦ (ε s).hom ≫ formalSpectrumMap hQw (π s)) ≫
      formalSpectrumMap hRw cQ = Sigma.desc p ≫ eU.hom := by
    refine Sigma.hom_ext _ _ fun s ↦ ?_
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, Category.assoc, ← hp s,
      formalSpectrumMap_comp hRw hQw cQ (π s) (c s) (hπ s).symm]
  have hsurj : Sheaf.IsLocallySurjective (formalSpectrumMap hRw cQ) := by
    have : Sheaf.IsLocallySurjective (Sigma.desc p ≫ eU.hom) := inferInstance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ (congrArg (fun k ↦ k.hom) hfac)
  have hff := ((etaleFormalSpectrumMap_surjective_tfae B S hS f (by rw [hfa]; infer_instance)
    hRw E Q cQ hcQ).out 1 2).mp (isSurjective_of_isLocallySurjective B S hS hsurj)
  exact RingHom.faithfullyFlat_algebraMap_iff.mp hff

/-- **Rig-étaleness descends along a finite affine étale covering of the source chart.** Let
`τ : U ⟶ V` be a morphism of affine formal algebraic spaces and `{Wₛ ⟶ U}` a finite family of
affine formal algebraic spaces, representable étale over `U` and covering it as in Definition
0AIM. If every composite `Wₛ ⟶ U ⟶ V` corresponds to a rig-étale arrow of `WAdm^{Noeth}`, so
does `τ`.

For a presentation `g : A → R` of `τ`, Stacks 0AN8 presents `Wₛ ⟶ U` as `Spf (Rₛ)^ ⟶ Spf R` for
étale `R`-algebras `Rₛ`, the covering makes `R → ∏ₛ Rₛ` faithfully flat by Stacks 0AN9, and
`Rig.isRigEtaleArrow_of_finite_etale_family` (axioms (2) and (3) of Situation 0CBA) descends
rig-étaleness from the composites `A → R → (Rₛ)^` to `g`. -/
theorem hasPropertyOnAffineChartMap_of_finite_cover {U V : FppfSheaf B S hS} (τ : U ⟶ V)
    {σ : Type u} [Fintype σ] (W : σ → FppfSheaf B S hS) (p : ∀ s, W s ⟶ U)
    (hW : ∀ s, IsAffineFormalAlgebraicSpace B S hS (W s))
    (hp : ∀ s, IsRepresentableEtale B S hS (p s))
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc p))
    (hP : ∀ s, HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic
      TopologicalRing.IsRigEtaleHom (p s ≫ τ)) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic
      TopologicalRing.IsRigEtaleHom τ := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  have hRw := hCR.1.isWeaklyAdmissible
  choose R' i₁ i₂ i₃ E' c ε hc hε using fun s ↦
    exists_etale_completion_of_isRepresentableEtale B S hS (p s) (hW s) (hp s) R hCR.1 E eU
  let := i₁
  let := i₂
  let := i₃
  have hff := faithfullyFlat_pi_of_isLocallySurjective B S hS R hCR.1 E eU R' E' c hc W ε p hε
    hcov
  have : IsNoetherianRing R := hCR.2
  have : IsNoetherianRing A := hCA.2
  have hT := fun s ↦ isNoetherianAdic_completionOver_algebraMap (R₁ := R' s) hCR
  have hs : ∀ s, RingHom.IsRigEtaleArrow
      ((CompletionOver.canonicalMap (algebraMap R (R' s))).comp g.toRingHom) := by
    intro s
    have hTw := (hT s).1.isWeaklyAdmissible
    have : IsNoetherianRing (CompletionOver (algebraMap R (R' s))) := (hT s).2
    have hsq : p s ≫ τ = (ε s).hom ≫
        formalSpectrumMap hA (ContinuousHom.comp hRw hA (c s) g) ≫ eV.inv := by
      rw [← formalSpectrumMap_comp_eq hRw hA]
      simp only [Category.assoc]
      rw [reassoc_of% (hε s), hg]
    have h := hP s A (CompletionOver (algebraMap R (R' s))) hCA (hT s) hA D (E' s) (ε s) eV
      (ContinuousHom.comp hRw hA (c s) g) hsq
    rw [ContinuousHom.comp_toRingHom, hc] at h
    exact fun _ _ _ _ ↦ h
  show RingHom.IsRigEtaleArrow g.toRingHom
  exact Rig.isRigEtaleArrow_of_finite_etale_family hCA hCR g.toRingHom g.continuous R' hff hs

end AlgebraicGeometry.FormalSpace

end
