module

public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpenClosedComplement
public import
StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumExactSequence
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0BSA for weakly étale morphisms over a strictly henselian local ring

The local input is a statement about an arbitrary weakly étale morphism `g : T ⟶ Spec R` with `R`
strictly henselian local: the local ring of `T` at a point over the closed point of `Spec R` is `R`
(Olivier's theorem), that point is closed in `T`, and so Stacks 0BSA applies to the open immersion
`g ⁻¹ᵁ (Spec R ∖ {𝔪}) ⊆ T`. Every projection of an `n`-fold fibre product of `Xˢʰ` over `X` is
weakly étale, so this applies to `Xˢʰ ×_X Xˢʰ` and `Xˢʰ ×_X Xˢʰ ×_X Xˢʰ`.

## Main results

* `AlgebraicGeometry.bijective_algebraMap_of_isStrictHenselization_of_strictlyHenselian`: a
  strictly henselian local ring is its own strict henselization.
* `AlgebraicGeometry.isIso_stalkMap_of_weaklyEtale_of_strictlyHenselian`: a weakly étale morphism
  to the spectrum of a strictly henselian local ring induces an isomorphism of local rings at every
  point over the closed point.
* `AlgebraicGeometry.isClosed_singleton_of_weaklyEtale_of_strictlyHenselian`: such a point is
  closed.
* `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_preimage_puncturedSpectrum_of_weaklyEtale`
  — Stacks 0BSA for the preimage of the punctured spectrum under a weakly étale morphism.

## References

* [Stacks Project, Tag 0BSA](https://stacks.math.columbia.edu/tag/0BSA)
* [Stacks Project, Tag 092B](https://stacks.math.columbia.edu/tag/092B)
* [Stacks Project, Tag 092N](https://stacks.math.columbia.edu/tag/092N)
* [Stacks Project, Tag 092Z](https://stacks.math.columbia.edu/tag/092Z)
* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.Divisors
open Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-! ### A strict henselization is weakly étale -/

/-- A strict henselization `Sˢʰ` of a local ring `S` is weakly étale over `S`. -/
theorem weaklyEtale_of_isStrictHenselization (S : Type u) [CommRing S] [IsLocalRing S]
    (κsep : Type u) [Field κsep] [Algebra (maximalIdeal S).ResidueField κsep]
    [IsSepClosure (maximalIdeal S).ResidueField κsep]
    (Ssh : Type u) [CommRing Ssh] [IsLocalRing Ssh] [Algebra S Ssh]
    (h : Stacks.StrictHenselization.IsStrictHenselization S κsep Ssh) :
    Algebra.WeaklyEtale S Ssh :=
  Algebra.weaklyEtale_of_ind_etale h.isFilteredColimitEtale

/-- A strictly henselian local ring is its own strict henselization: the structure map of a strict
henselization of it is bijective. -/
@[ega "IV 18.8.8"]
theorem bijective_algebraMap_of_isStrictHenselization_of_strictlyHenselian
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    (κsep : Type u) [Field κsep] [Algebra (maximalIdeal R).ResidueField κsep]
    [IsSepClosure (maximalIdeal R).ResidueField κsep]
    (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (h : Stacks.StrictHenselization.IsStrictHenselization R κsep Rsh) :
    Function.Bijective (algebraMap R Rsh) :=
  have := h.isLocalHom
  bijective_algebraMap_of_weaklyEtale_of_isLocalHom R Rsh
    (weaklyEtale_of_isStrictHenselization R κsep Rsh h)

/-! ### Connectedness of punctured spectra of strictly henselian local rings -/

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]

/-- If `R ≃+* S` are local rings and the punctured spectrum of `R` is connected, then so is that of
`S`. -/
theorem isConnected_compl_closedPoint_of_ringEquiv
    {S : Type u} [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    (hconn : _root_.IsConnected ({closedPoint R}ᶜ : Set (PrimeSpectrum R))) :
    _root_.IsConnected ({closedPoint S}ᶜ : Set (PrimeSpectrum S)) := by
  let φ : PrimeSpectrum R ≃ₜ PrimeSpectrum S := PrimeSpectrum.homeomorphOfRingEquiv e
  have hclosed : φ (closedPoint R) = closedPoint S := comap_closedPoint (e.symm : S →+* R)
  have himg : φ '' ({closedPoint R}ᶜ) = ({closedPoint S}ᶜ : Set (PrimeSpectrum S)) := by
    rw [Set.image_compl_eq φ.bijective, Set.image_singleton, hclosed]
  exact himg ▸ hconn.image _ φ.continuous.continuousOn

/-- A strictly henselian local ring whose punctured spectrum is connected satisfies
`AlgebraicGeometry.IsConnectedPuncturedStrictHenselization`. -/
theorem isConnectedPuncturedStrictHenselization_of_isConnected
    (hconn : _root_.IsConnected ({closedPoint R}ᶜ : Set (PrimeSpectrum R))) :
    IsConnectedPuncturedStrictHenselization R := by
  intro κsep _ _ _ Rsh _ _ _ h
  exact isConnected_compl_closedPoint_of_ringEquiv R
    (RingEquiv.ofBijective _
      (bijective_algebraMap_of_isStrictHenselization_of_strictlyHenselian R κsep Rsh h)) hconn

/-! ### Weakly étale morphisms over a strictly henselian local scheme -/

/-- The local ring of `Spec R` at a point over the closed point is isomorphic to `R`. -/
private def ringEquivStalkOfEqClosedPoint
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of R)) (t : T)
    (ht : g.base t = closedPoint (CommRingCat.of R)) :
    R ≃+* (Spec (CommRingCat.of R)).presheaf.stalk (g.base t) :=
  ((stalkClosedPointIso (CommRingCat.of R)).symm ≪≫
    eqToIso (congrArg (Spec (CommRingCat.of R)).presheaf.stalk ht.symm)).commRingCatIsoToRingEquiv

/-- The local ring of `Spec R` at the image of a point mapping to the closed point is strictly
henselian. -/
theorem strictlyHenselianLocalRing_stalk_of_eq_closedPoint
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of R)) (t : T)
    (ht : g.base t = closedPoint (CommRingCat.of R)) :
    StrictlyHenselianLocalRing ((Spec (CommRingCat.of R)).presheaf.stalk (g.base t)) :=
  StrictlyHenselianLocalRing.of_ringEquiv (R := R) (ringEquivStalkOfEqClosedPoint R g t ht)

/-- **Olivier's theorem on schemes.** Let `R` be a strictly henselian local ring and let
`g : T ⟶ Spec R` be weakly étale. At a point of `T` lying over the closed point of `Spec R` the map
of local rings induced by `g` is an isomorphism. -/
theorem isIso_stalkMap_of_weaklyEtale_of_strictlyHenselian
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of R)) [WeaklyEtale g] (t : T)
    (ht : g.base t = closedPoint (CommRingCat.of R)) :
    IsIso (g.stalkMap t) := by
  have hsh := strictlyHenselianLocalRing_stalk_of_eq_closedPoint R g t ht
  let : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk (g.base t)) (T.presheaf.stalk t) :=
    (g.stalkMap t).hom.toAlgebra
  have hwe : Algebra.WeaklyEtale ((Spec (CommRingCat.of R)).presheaf.stalk (g.base t))
      (T.presheaf.stalk t) := (weaklyEtale_iff_stalkMap_weaklyEtale g).mp inferInstance t
  have hloc : IsLocalHom (algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk (g.base t))
      (T.presheaf.stalk t)) := inferInstanceAs (IsLocalHom (g.stalkMap t).hom)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_algebraMap_of_weaklyEtale_of_isLocalHom _ _ hwe)

/-- For `R` strictly henselian local and `g : T ⟶ Spec R` weakly étale, a point of `T` lying over
the closed point of `Spec R` is a closed point of `T`. -/
theorem isClosed_singleton_of_weaklyEtale_of_strictlyHenselian
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of R)) [WeaklyEtale g] (t : T)
    (ht : g.base t = closedPoint (CommRingCat.of R)) :
    IsClosed ({t} : Set T) := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun s hs => ?_) subset_closure
  have hts : t ⤳ s := specializes_iff_mem_closure.mpr hs
  have hgs : g.base s = closedPoint (CommRingCat.of R) :=
    (IsLocalRing.specializes_closedPoint (g.base s)).antisymm
      (ht ▸ hts.map g.base.hom.continuous) |>.eq
  have : IsIso (g.stalkMap s) := isIso_stalkMap_of_weaklyEtale_of_strictlyHenselian R g s hgs
  have hiso : IsIso ((Spec (CommRingCat.of R)).fromSpecStalk (g.base s)) := by
    rw [hgs, ← Spec_stalkClosedPointIso]; infer_instance
  have hcomp : IsIso (T.fromSpecStalk s ≫ g) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]; infer_instance
  have hinj : Function.Injective (fun x => g.base ((T.fromSpecStalk s).base x)) :=
    fun _ _ hxy => (Scheme.homeoOfIso (asIso (T.fromSpecStalk s ≫ g))).injective hxy
  obtain ⟨a, ha⟩ : t ∈ Set.range (T.fromSpecStalk s).base := by
    rw [Scheme.range_fromSpecStalk]; exact hts
  have hb : (T.fromSpecStalk s).base (closedPoint (T.presheaf.stalk s)) = s :=
    Scheme.fromSpecStalk_closedPoint
  have heq : g.base ((T.fromSpecStalk s).base a)
      = g.base ((T.fromSpecStalk s).base (closedPoint (T.presheaf.stalk s))) := by
    rw [ha, hb, ht, hgs]
  exact (show t = s by rw [← ha, hinj heq, hb]).symm

/-- For `R` strictly henselian local with connected punctured spectrum and `g : T ⟶ Spec R` weakly
étale, the local ring of `T` at a point over the closed point of `Spec R` satisfies
`AlgebraicGeometry.IsConnectedPuncturedStrictHenselization`. -/
theorem isConnectedPuncturedStrictHenselization_stalk_of_weaklyEtale
    (hconn : _root_.IsConnected ({closedPoint R}ᶜ : Set (PrimeSpectrum R)))
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of R)) [WeaklyEtale g] (t : T)
    (ht : g.base t = closedPoint (CommRingCat.of R)) :
    IsConnectedPuncturedStrictHenselization (T.presheaf.stalk t) := by
  have := isIso_stalkMap_of_weaklyEtale_of_strictlyHenselian R g t ht
  let e : R ≃+* (T.presheaf.stalk t) :=
    (ringEquivStalkOfEqClosedPoint R g t ht).trans (asIso (g.stalkMap t)).commRingCatIsoToRingEquiv
  have : StrictlyHenselianLocalRing (T.presheaf.stalk t) :=
    StrictlyHenselianLocalRing.of_ringEquiv (R := R) e
  exact isConnectedPuncturedStrictHenselization_of_isConnected _
    (isConnected_compl_closedPoint_of_ringEquiv R e hconn)

/-! ### The open immersion to which Stacks 0BSA is applied -/

/-- If every point of `X` is a specialization of a point of the open `U` and `g : T ⟶ X` lifts
generalizations, then the inclusion of `g ⁻¹ᵁ U` in `T` is dominant. -/
theorem isDominant_preimage_ι_of_generalizingMap {T X : Scheme.{u}} (g : T ⟶ X)
    (hgen : GeneralizingMap g.base) (U : X.Opens)
    (hU : ∀ x : X, ∃ u, u ∈ U ∧ u ⤳ x) : IsDominant (g ⁻¹ᵁ U).ι := by
  refine ⟨?_⟩
  change Dense (Set.range (g ⁻¹ᵁ U).ι.base)
  rw [Scheme.Opens.range_ι, dense_iff_closure_eq, ← Set.univ_subset_iff]
  intro ξ _
  obtain ⟨u, huU, hu⟩ := hU (g.base ξ)
  obtain ⟨ξ', hξ', hgξ'⟩ := hgen hu
  have hmem : ξ' ∈ (g ⁻¹ᵁ U : Set T) := show g.base ξ' ∈ U from hgξ' ▸ huU
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) (specializes_iff_mem_closure.mp hξ')

/-- If the punctured spectrum of a local ring is nonempty, every point of the spectrum is a
specialization of a point of the punctured spectrum. -/
theorem exists_mem_puncturedSpectrum_specializes (R₀ : Type u) [CommRing R₀] [IsLocalRing R₀]
    (hne : ({closedPoint R₀}ᶜ : Set (PrimeSpectrum R₀)).Nonempty)
    (x : Spec (CommRingCat.of R₀)) :
    ∃ u, u ∈ puncturedSpectrum R₀ ∧ u ⤳ x := by
  by_cases hx : x = closedPoint (CommRingCat.of R₀)
  · obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu, hx ▸ IsLocalRing.specializes_closedPoint u⟩
  · exact ⟨x, hx, specializes_rfl⟩

/-- If the punctured spectrum of a local ring `R₀` is nonempty, its preimage under a flat morphism
`g : T ⟶ Spec R₀` is dense in `T`. -/
theorem isDominant_preimage_puncturedSpectrum_ι_of_flat (R₀ : Type u) [CommRing R₀]
    [IsLocalRing R₀] (hne : ({closedPoint R₀}ᶜ : Set (PrimeSpectrum R₀)).Nonempty)
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of R₀)) [Flat g] :
    IsDominant (g ⁻¹ᵁ puncturedSpectrum R₀).ι :=
  isDominant_preimage_ι_of_generalizingMap g (Flat.generalizingMap g) _
    (exists_mem_puncturedSpectrum_specializes R₀ hne)

/-- If the inclusion of an open `U` is quasi-compact, so is that of its preimage under `g`. -/
private theorem quasiCompact_ι_preimage {T X : Scheme.{u}} (g : T ⟶ X) (U : X.Opens)
    [QuasiCompact U.ι] : QuasiCompact (g ⁻¹ᵁ U).ι :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict g U) inferInstance

/-- **Stacks Project, Tag 0BSA for the preimage of a punctured spectrum under a weakly étale
morphism.** Let `R` be a strictly henselian local ring whose punctured spectrum is connected and
retrocompact, and let `g : T ⟶ Spec R` be weakly étale. Then base change of finite étale covers
along the open immersion `g ⁻¹ᵁ (Spec R ∖ {𝔪}) ⟶ T` is fully faithful. -/
theorem fullyFaithful_finiteEtaleBaseChange_preimage_puncturedSpectrum_of_weaklyEtale
    (hconn : _root_.IsConnected ({closedPoint R}ᶜ : Set (PrimeSpectrum R)))
    [QuasiCompact (puncturedSpectrum R).ι]
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of R)) [WeaklyEtale g] :
    Nonempty (finiteEtaleBaseChange (g ⁻¹ᵁ puncturedSpectrum R).ι).FullyFaithful := by
  have : QuasiCompact (g ⁻¹ᵁ puncturedSpectrum R).ι := quasiCompact_ι_preimage g _
  have : IsDominant (g ⁻¹ᵁ puncturedSpectrum R).ι :=
    isDominant_preimage_puncturedSpectrum_ι_of_flat R hconn.nonempty g
  have hcp : ∀ t : T, t ∉ Set.range (g ⁻¹ᵁ puncturedSpectrum R).ι.base →
      g.base t = closedPoint (CommRingCat.of R) := by
    intro t htt
    rw [Scheme.Opens.range_ι] at htt
    by_contra hne
    exact htt (show g.base t ∈ puncturedSpectrum R from hne)
  exact fullyFaithful_finiteEtaleBaseChange_of_quasiCompact_of_isClosed_compl _
    (fun t htt => isClosed_singleton_of_weaklyEtale_of_strictlyHenselian R g t (hcp t htt))
    (fun t htt => isConnectedPuncturedStrictHenselization_stalk_of_weaklyEtale R hconn g t
      (hcp t htt))

/-! ### Stacks 0BSA over the spectrum of a strict henselization -/

variable (A : Type u) [CommRing A] [IsLocalRing A]
  (κsep : Type u) [Field κsep] [Algebra (maximalIdeal A).ResidueField κsep]
  [IsSepClosure (maximalIdeal A).ResidueField κsep]
  (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]

/-- A strict henselization is a strictly henselian local ring. -/
theorem strictlyHenselianLocalRing_of_isStrictHenselization
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash) :
    StrictlyHenselianLocalRing Ash :=
  have := hAsh.henselian
  have := hAsh.sepClosed
  have : IsSepClosed (ResidueField Ash) := isSepClosed_residueField_of_maximalIdeal Ash
  ⟨⟩

/-- For a strict henselization `Aˢʰ` of `A`, the morphism `Spec Aˢʰ ⟶ Spec A` is weakly étale. -/
theorem weaklyEtale_specMap_algebraMap_of_isStrictHenselization
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) := by
  have hwe : Algebra.WeaklyEtale A Ash := weaklyEtale_of_isStrictHenselization A κsep Ash hAsh
  have heq : (CommRingCat.ofHom (algebraMap A Ash)).hom.toAlgebra =
      (inferInstance : Algebra A Ash) := Algebra.algebra_ext _ _ fun _ => rfl
  rw [weaklyEtale_specMap_iff]
  exact heq ▸ hwe

/-- The punctured spectrum of a strict henselization of `A` is retrocompact when that of `A` is. -/
theorem quasiCompact_ι_puncturedSpectrum_of_isStrictHenselization
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    [QuasiCompact (puncturedSpectrum A).ι] :
    QuasiCompact (puncturedSpectrum Ash).ι := by
  rw [← preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh]
  exact quasiCompact_ι_preimage _ _

/-- **Stacks Project, Tag 0BSA for every stage of the cover `Xˢʰ ⟶ X`.** Let `(A, 𝔪)` be a local
ring with retrocompact punctured spectrum `U`, let `Aˢʰ` be a strict henselization of `A` with
connected punctured spectrum, and write `f : Xˢʰ = Spec Aˢʰ ⟶ X = Spec A`. For every weakly étale
`g : T ⟶ Xˢʰ`, base change of finite étale covers along the inclusion of the preimage of `U` in `T`
is fully faithful. -/
theorem fullyFaithful_finiteEtaleBaseChange_preimage_puncturedSpectrum_comp
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    [QuasiCompact (puncturedSpectrum A).ι]
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of Ash)) (hg : WeaklyEtale g) :
    Nonempty (finiteEtaleBaseChange ((g ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ash)))
      ⁻¹ᵁ puncturedSpectrum A).ι).FullyFaithful := by
  have := strictlyHenselianLocalRing_of_isStrictHenselization A κsep Ash hAsh
  have := quasiCompact_ι_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh
  have := hg
  have hpre : (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A Ash))) ⁻¹ᵁ puncturedSpectrum A
      = g ⁻¹ᵁ puncturedSpectrum Ash := by
    rw [← preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh]
    rfl
  rw [hpre]
  exact fullyFaithful_finiteEtaleBaseChange_preimage_puncturedSpectrum_of_weaklyEtale Ash
    hconnected g

/-- With the notation of
`AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_preimage_puncturedSpectrum_comp`, base
change of finite étale covers along the open immersion

```
(pr₁ ≫ f) ⁻¹ᵁ U  ⟶  Xˢʰ ×_X Xˢʰ
```

is fully faithful. -/
theorem fullyFaithful_finiteEtaleBaseChange_pullback_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    [QuasiCompact (puncturedSpectrum A).ι] :
    Nonempty (finiteEtaleBaseChange
      ((pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A Ash)))
            (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A Ash))) ⁻¹ᵁ
        puncturedSpectrum A).ι).FullyFaithful :=
  have := weaklyEtale_specMap_algebraMap_of_isStrictHenselization A κsep Ash hAsh
  fullyFaithful_finiteEtaleBaseChange_preimage_puncturedSpectrum_comp A κsep Ash hAsh
    hconnected _ inferInstance

/-! ### Split covers extend along morphisms of connected schemes -/

/-- A finite coproduct of terminal objects is in the essential image of any functor preserving
finite limits and finite colimits whose source has finite coproducts and a terminal object. -/
theorem essImage_of_isFiniteCoproductOfTerminal {C : Type*} {D : Type*}
    [Category C] [Category D] [HasFiniteCoproducts C] [HasTerminal C]
    (H : C ⥤ D) [PreservesFiniteColimits H] [PreservesFiniteLimits H]
    {Y : D} (hY : IsFiniteCoproductOfTerminal Y) : H.essImage Y := by
  obtain ⟨n, A, g, hA, ⟨hcolim⟩⟩ := hY
  have hT : IsTerminal (H.obj (⊤_ C)) := (terminalIsTerminal (C := C)).isTerminalObj H _
  let K : Discrete (Fin n) ⥤ C := Discrete.functor fun _ => (⊤_ C)
  have hc : IsColimit (H.mapCocone (colimit.cocone K)) :=
    isColimitOfPreserves H (colimit.isColimit K)
  let α : Discrete.functor A ≅ K ⋙ H :=
    Discrete.natIso fun i => (hA i.as).some.uniqueUpToIso hT
  exact ⟨colimit K, ⟨(IsColimit.coconePointsIsoOfNatIso hcolim hc α).symm⟩⟩

/-- A finite étale cover of a connected scheme `T` which is a finite coproduct of copies of `T` is
the base change of a finite étale cover of any connected scheme `T'` under `T`. -/
theorem essImage_finiteEtaleBaseChange_of_isFiniteCoproductOfTerminal
    {T T' : Scheme.{u}} (h : T ⟶ T') [ConnectedSpace T] [ConnectedSpace T']
    (w : GeometricPoint T) {Y : FiniteEtaleOver T}
    (hY : IsFiniteCoproductOfTerminal Y) : (finiteEtaleBaseChange h).essImage Y := by
  have hex := exactFunctor_finiteEtaleBaseChange h w
  have : PreservesFiniteLimits (finiteEtaleBaseChange h) := hex.1
  have : PreservesFiniteColimits (finiteEtaleBaseChange h) := hex.2
  exact essImage_of_isFiniteCoproductOfTerminal _ hY

end AlgebraicGeometry

end
