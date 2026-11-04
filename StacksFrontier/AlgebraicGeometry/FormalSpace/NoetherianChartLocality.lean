module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartPresentationTransport
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterizationCharts

/-!
# Local properties of arrows of `WAdm^{Noeth}` are étale local on formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a property of arrows of
`WAdm^{Noeth}` and let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S`. This file
proves, for every `P` satisfying the hypotheses below, the equivalence of the four conditions
that Stacks 0GCZ states for rig-étaleness and Stacks 0GCQ for rig-smoothness:

1. for every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y`, every presentation of `U ⟶ V` by Noetherian adic rings has `P`;
2. for every such square the map `U ⟶ V` *corresponds to a `P`-map in `WAdm^{Noeth}`*: `U` and
   `V` are formal spectra of Noetherian adic rings and `U ⟶ V` is the formal spectrum of a
   homomorphism with `P`;
3. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a `P`-map;
4. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space, `Yᵢ ⟶ Y` representable étale and
   `Xᵢ ⟶ Yᵢ` corresponding to a `P`-map.

The implication (4) ⟹ (1) needs no hypothesis on `X` and `Y`; the implication (1) ⟹ (3), and
the equivalence of (1) and (2), use that `X` and `Y` are locally Noetherian.

The hypotheses on `P` are the ones the source's proofs use: `P` is a local property of arrows of
`WAdm^{Noeth}` (Situation 0CBA, in the Noetherian form of Remark 0ANI) stable under composition
(Remark 0GBK), it is invariant under isomorphisms of topological rings on source and target, and
it holds for the canonical map from a Noetherian adic ring to the completion of an étale algebra
over it. Rig-étaleness and rig-smoothness both have them; for rig-étaleness the four conditions
are those of `AlgebraicGeometry.FormalSpace.isRigEtale_tfae_of_isLocallyNoetherian'`, and for
rig-smoothness this file's results give Stacks 0GCQ
(`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothLocalCharacterization`).

## Main definitions

* `AlgebraicGeometry.FormalSpace.CorrespondsToNoetherianMap`: a morphism of fppf sheaves is the
  formal spectrum of a homomorphism of Noetherian adic rings with `P`.
* `AlgebraicGeometry.FormalSpace.CorrespondsToNoetherianMapOnEveryAffineEtaleDiagram`,
  `AlgebraicGeometry.FormalSpace.CorrespondsToNoetherianMapAfterTargetCover`,
  `AlgebraicGeometry.FormalSpace.CorrespondsToNoetherianMapAfterSourceCover`: conditions (2), (3)
  and (4).
* `AlgebraicGeometry.FormalSpace.PropertyHoldsOnEtaleCompletion`: `P` holds for the canonical
  map to the completion of an étale algebra.

## Main results

* `AlgebraicGeometry.FormalSpace.property_of_finite_etale_family`: `P` descends along a finite
  jointly faithfully flat family of completed étale maps (axioms (2) and (3) of Situation 0CBA).
* `hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToNoetherianMapAfterSourceCover`:
  (4) ⟹ (1).
* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_tfae_of_isLocallyNoetherian`:
  the equivalence of the four conditions for locally Noetherian `X` and `Y`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GBK](https://stacks.math.columbia.edu/tag/0GBK)
* [Stacks Project, Tag 0GCQ](https://stacks.math.columbia.edu/tag/0GCQ)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- A morphism `t : U ⟶ V` of fppf sheaves *corresponds to a `P`-map in `WAdm^{Noeth}`*: `V`
and `U` are formal spectra of Noetherian adic rings `A` and `R`, and `t` is the formal spectrum
of a continuous homomorphism `A → R` with `P`. For `P` rig-étaleness this is
`AlgebraicGeometry.FormalSpace.CorrespondsToRigEtaleMap`. -/
abbrev CorrespondsToNoetherianMap {U V : FppfSheaf B S hS} (t : U ⟶ V) : Prop :=
  ∃ (A R : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsLinearTopology A A) (_ : CommRing R) (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
    (_ : IsLinearTopology R R), IsNoetherianAdic A ∧ IsNoetherianAdic R ∧
    ∃ (hA : IsWeaklyAdmissible A) (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS R)
      (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
      t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv ∧ P g.toRingHom

/-- **Condition (2)** of Stacks 0GCZ and Stacks 0GCQ for the property `P`: for every
commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y`
representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a `P`-map in
`WAdm^{Noeth}`. -/
abbrev CorrespondsToNoetherianMapOnEveryAffineEtaleDiagram {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) : Prop :=
  ∀ (U V : FppfSheaf B S hS) (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V),
    IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
    IsRepresentableEtale B S hS a → IsRepresentableEtale B S hS b →
    a ≫ f = t ≫ b → CorrespondsToNoetherianMap B S hS P t

/-- **Condition (3)** of Stacks 0GCZ and Stacks 0GCQ for the property `P`: there is a covering
`{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in
Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a `P`-map in `WAdm^{Noeth}`. -/
abbrev CorrespondsToNoetherianMapAfterTargetCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    Prop :=
  ∃ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
    IsAffineEtaleCover B S hS V v ∧
      ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS)
        (w : ∀ i, U i ⟶ pullback (v j) f),
        IsAffineEtaleCover B S hS U w ∧
          ∀ i, CorrespondsToNoetherianMap B S hS P (w i ≫ pullback.fst (v j) f)

/-- **Condition (4)** of Stacks 0GCZ and Stacks 0GCQ for the property `P`: there is a covering
`{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an
affine formal algebraic space, `Yᵢ ⟶ Y` representable étale and `Xᵢ ⟶ Yᵢ` corresponding to a
`P`-map in `WAdm^{Noeth}`. -/
abbrev CorrespondsToNoetherianMapAfterSourceCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U u ∧
      ∀ i, ∃ (V : FppfSheaf B S hS) (v : V ⟶ Y) (t : U i ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS V ∧ IsRepresentableEtale B S hS v ∧
          u i ≫ f = t ≫ v ∧ CorrespondsToNoetherianMap B S hS P t

/-- The property `P` holds for the canonical map `A → (A₁)^` from a Noetherian adic ring `A` to
the completion over `A` of an étale `A`-algebra `A₁`, whenever that completion is a Noetherian
adic ring. -/
abbrev PropertyHoldsOnEtaleCompletion : Prop :=
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    {A₁ : Type u} [CommRing A₁] (c : A →+* A₁), c.Etale → IsNoetherianAdic A →
      IsNoetherianAdic (CompletionOver c) → P (CompletionOver.canonicalMap c)

variable {B S hS P}

/-! ### Presentations -/

/-- The completion of a finite type algebra over a Noetherian adic ring is Noetherian adic. -/
private theorem isNoetherianAdic_completionOver_algebraMap {A A₁ : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [CommRing A₁] [Algebra A A₁]
    [Algebra.FiniteType A A₁] (hA : IsNoetherianAdic A) :
    IsNoetherianAdic (CompletionOver (algebraMap A A₁)) :=
  have := hA.2
  completionOver_isNoetherianAdic _ hA (Algebra.FiniteType.isNoetherianRing A A₁)

/-- A representable étale map followed by the forward map of an isomorphism is representable
étale. -/
private theorem isRepresentableEtale_comp_hom {X Y Z : FppfSheaf B S hS} {g : X ⟶ Y}
    (hg : IsRepresentableEtale B S hS g) (e : Y ≅ Z) : IsRepresentableEtale B S hS (g ≫ e.hom) :=
  hg.comp B S hS (isRepresentableEtale_of_isIso B S hS _)

/-- Local surjectivity of the composite of a family of covers pulled back along `f` with covers of
the pullbacks. -/
private theorem isLocallySurjective_sigmaDesc_comp_pullback_snd {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) {J : Type (u + 1)} {V : J → FppfSheaf B S hS} (v : ∀ j, V j ⟶ Y)
    (hv : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc v))
    {K : J → Type (u + 1)} {W : ∀ j, K j → FppfSheaf B S hS} (w : ∀ j k, W j k ⟶ pullback (v j) f)
    (hw : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
      ∀ j, Sheaf.IsLocallySurjective (Sigma.desc (w j))) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective
      (Sigma.desc fun x : Σ j, K j ↦ w x.1 x.2 ≫ pullback.snd (v x.1) f) :=
  isLocallySurjective_sigmaDesc_comp_sigma B S hS (fun j ↦ pullback.snd (v j) f)
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hv) (fun x ↦ w x.1 x.2) hw

/-- **Presentation independence.** If `P` is invariant under isomorphisms of topological rings,
a morphism corresponding to a `P`-map in `WAdm^{Noeth}` has every presentation by Noetherian adic
rings with `P`: two presentations differ by such isomorphisms (Stacks 0AN0). -/
theorem hasPropertyOnAffineChartMap_of_correspondsToNoetherianMap
    (hiso : PropertyInvariantUnderRingEquiv IsNoetherianAdic P) {U V : FppfSheaf B S hS}
    {t : U ⟶ V} (ht : CorrespondsToNoetherianMap B S hS P t) :
    HasPropertyOnAffineChartMap B S hS IsNoetherianAdic P t := by
  obtain ⟨A, R, _, _, _, _, _, _, _, _, hCA, hCR, hA, D, E, eU, eV, g, hg, hP⟩ := ht
  exact hasPropertyOnAffineChartMap_of_presentation_of_propertyInvariantUnderRingEquiv
    (fun _ _ _ _ _ hR ↦ hR.1.isWeaklyAdmissible) hiso t hCA hCR D E eU eV g hg hP

/-- A morphism between formal spectra of Noetherian adic rings all of whose Noetherian
presentations have `P` corresponds to a `P`-map in `WAdm^{Noeth}`: the presenting homomorphism
exists by Stacks 0AN0. -/
theorem correspondsToNoetherianMap_of_hasPropertyOnAffineChartMap {U V : FppfSheaf B S hS}
    {t : U ⟶ V} (ht : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic P t)
    {A R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hCA : IsNoetherianAdic A) (hCR : IsNoetherianAdic R) (D : QuotientSystem B S hS A)
    (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D) :
    CorrespondsToNoetherianMap B S hS P t := by
  have hA := hCA.1.isWeaklyAdmissible
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA
    hCR.1.isWeaklyAdmissible (eU.inv ≫ t ≫ eV.hom)
  have htg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv := by simp [hg]
  exact ⟨A, R, _, _, _, _, _, _, _, _, hCA, hCR, hA, D, E, eU, eV, g, htg,
    ht A R hCA hCR hA D E eU eV g htg⟩

/-- A morphism between Noetherian affine formal algebraic spaces all of whose Noetherian
presentations have `P` corresponds to a `P`-map in `WAdm^{Noeth}`: both are formal spectra of
Noetherian adic rings. -/
theorem correspondsToNoetherianMap_of_hasPropertyOnAffineChartMap_of_isNoetherian
    {U V : FppfSheaf B S hS} {t : U ⟶ V}
    (ht : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic P t)
    (hU : IsNoetherian B S hS U) (hV : IsNoetherian B S hS V) :
    CorrespondsToNoetherianMap B S hS P t := by
  obtain ⟨R, _, _, _, _, E, hCR, ⟨eU⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hU
  obtain ⟨A, _, _, _, _, D, hCA, ⟨eV⟩⟩ := exists_iso_formalSpectrum_of_isNoetherian B S hS hV
  exact correspondsToNoetherianMap_of_hasPropertyOnAffineChartMap ht hCA hCR D E eU eV

/-! ### The ring-theoretic inputs -/

/-- **A local property descends along a finite jointly faithfully flat family of completed
étale maps.** Let `P` be a local property of arrows of `WAdm^{Noeth}` invariant under
isomorphisms of topological rings, let `g : R₀ → A` be a continuous homomorphism of Noetherian
adic rings and let `A → A'ₛ` be finitely many étale ring maps with `A → ∏ₛ A'ₛ` faithfully flat.
If each composite `R₀ → A → (A'ₛ)^` has `P`, then so does `g`.

This is axioms (2) and (3) of Situation 0CBA together: by finite products `R₀ → ∏ₛ (A'ₛ)^` has
`P`, `∏ₛ (A'ₛ)^` is the completion of `∏ₛ A'ₛ` (`TopologicalRing.CompletionOver.piRingEquiv`) and
`R₀` its own completion, and faithfully flat descent along `A → ∏ₛ A'ₛ` with the identity on
`R₀` applies. For rig-étaleness this is `Rig.isRigEtaleArrow_of_finite_etale_family`. -/
theorem property_of_finite_etale_family (hloc : PropertyIsLocalNoetherian.{u} P)
    (hiso : PropertyInvariantUnderRingEquiv IsNoetherianAdic P) {R₀ A : Type u} [CommRing R₀]
    [TopologicalSpace R₀] [IsTopologicalRing R₀] [IsLinearTopology R₀ R₀] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hR₀ : IsNoetherianAdic R₀) (hA : IsNoetherianAdic A)
    (g : R₀ →+* A) (hg : Continuous g) {σ : Type u} [Fintype σ] (A' : σ → Type u)
    [∀ s, CommRing (A' s)] [∀ s, Algebra A (A' s)] [∀ s, Algebra.Etale A (A' s)]
    (hff : Module.FaithfullyFlat A (∀ s, A' s))
    (hP : ∀ s, P ((CompletionOver.canonicalMap (algebraMap A (A' s))).comp g)) :
    P g := by
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing R₀ := hR₀.2
  have : ∀ s, IsNoetherianRing (A' s) := fun s ↦ Algebra.FiniteType.isNoetherianRing A (A' s)
  let f : A →+* ∀ s, A' s := Pi.ringHom fun s ↦ algebraMap A (A' s)
  have hT : ∀ s, IsNoetherianAdic (CompletionOver (algebraMap A (A' s))) :=
    fun s ↦ isNoetherianAdic_completionOver_algebraMap hA
  have hTf : IsNoetherianAdic (CompletionOver f) :=
    completionOver_isNoetherianAdic _ hA inferInstance
  have hTR : IsNoetherianAdic (CompletionOver (RingHom.id R₀)) :=
    completionOver_isNoetherianAdic _ hR₀ inferInstance
  have : ∀ s, IsNoetherianRing (CompletionOver (algebraMap A (A' s))) := fun s ↦ (hT s).2
  have hcont : ∀ s, Continuous ((CompletionOver.canonicalMap (algebraMap A (A' s))).comp g) :=
    fun s ↦ (continuous_canonicalMap _).comp hg
  have hTpi : TopologicalRing.IsAdic (∀ s, CompletionOver (algebraMap A (A' s))) :=
    Rig.isAdic_pi _ fun s ↦ (hT s).1
  -- an adic ring is linearly topologized, by the powers of an ideal defining its topology
  have : IsLinearTopology (∀ s, CompletionOver (algebraMap A (A' s)))
      (∀ s, CompletionOver (algebraMap A (A' s))) := by
    obtain ⟨⟨J, -, hJ⟩, -, -⟩ := hTpi
    exact IsLinearTopology.mk_of_hasBasis _ (S := Ideal _) (s := fun n ↦ J ^ n)
      hJ.hasBasis_nhds_zero
  -- finite products
  let ψ : R₀ →+* ∀ s, CompletionOver (algebraMap A (A' s)) :=
    RingHom.pi fun s ↦ (CompletionOver.canonicalMap (algebraMap A (A' s))).comp g
  have hprod : P ψ := hloc.finiteProduct hR₀.1.isWeaklyAdmissible
    (Rig.countablyGenerated_nhds_of_isAdicRing hR₀.1)
    (fun s ↦ CompletionOver (algebraMap A (A' s))) (fun s ↦ (hT s).1.isWeaklyAdmissible)
    (fun s ↦ Rig.countablyGenerated_nhds_of_isAdicRing (hT s).1) _ hcont hR₀ hT hP
  have hψc : Continuous ψ := continuous_pi hcont
  -- the identifications
  obtain ⟨eR, heR, heRc, heRc'⟩ := Rig.exists_ringEquiv_completionOver_id hR₀.1
  let Φ := CompletionOver.piRingEquiv fun s ↦ algebraMap A (A' s)
  have hΦc := CompletionOver.continuous_piRingEquiv fun s ↦ algebraMap A (A' s)
  have hΦc' := CompletionOver.continuous_piRingEquiv_symm fun s ↦ algebraMap A (A' s)
  let φ : CompletionOver (RingHom.id R₀) →+* CompletionOver f :=
    (Φ.symm : (∀ s, CompletionOver (algebraMap A (A' s))) →+* CompletionOver f).comp
      (ψ.comp (eR.symm : CompletionOver (RingHom.id R₀) →+* R₀))
  have hφ : P φ := by
    refine hiso hR₀ ⟨hTpi, inferInstance⟩ hTR hTf ψ φ hψc eR heRc heRc' Φ.symm hΦc' hΦc ?_
      hprod
    ext x
    simp [φ]
  have hφc : Continuous φ := hΦc'.comp (hψc.comp heRc')
  let LD : LocalizationDiagram A R₀ (∀ s, A' s) R₀ :=
    { toA' := f
      toB' := RingHom.id R₀
      map := g
      completedMap := φ
      weaklyAdmissibleA := hA.1.isWeaklyAdmissible
      weaklyAdmissibleB := hR₀.1.isWeaklyAdmissible
      countableA := Rig.countablyGenerated_nhds_of_isAdicRing hA.1
      countableB := Rig.countablyGenerated_nhds_of_isAdicRing hR₀.1
      etaleA := (RingHom.etale_algebraMap.mpr inferInstance : (algebraMap A (∀ s, A' s)).Etale)
      etaleB := (RingHom.etale_algebraMap.mpr inferInstance : (algebraMap R₀ R₀).Etale)
      continuousMap := hg
      continuousCompletedMap := hφc
      commutes := by
        refine RingHom.ext fun b ↦ Φ.injective ?_
        have h1 : eR.symm (CompletionOver.canonicalMap (RingHom.id R₀) b) = b := by
          rw [← heR]; exact eR.symm_apply_apply b
        simp only [RingHom.comp_apply, φ, ψ, RingEquiv.coe_toRingHom, h1,
          RingEquiv.apply_symm_apply]
        rw [CompletionOver.piRingEquiv_canonicalMap]
        rfl }
  exact hloc.faithfullyFlatDescent LD hA hR₀ hTf hTR
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff : f.FaithfullyFlat) hφ

/-! ### Charts -/

/-- **A local property ascends along representable étale squares of affine charts.** Let
`t : U ⟶ V` be a morphism of affine formal algebraic spaces presented, by Noetherian adic rings,
by a continuous homomorphism `g` with `P`. Then every morphism `t' : U' ⟶ V'` of affine formal
algebraic spaces fitting in a commutative square `q ≫ t = t' ≫ r` with `q`, `r` representable
étale has every Noetherian presentation with `P`.

By Stacks 0AN8, `q` and `r` are the formal spectra of the completions `R → R₁^` and `A → A₁^` of
étale algebras, and by Stacks 0AN0 the square is the formal spectrum of a localization diagram,
so axiom (1) of Situation 0CBA gives `P` for the induced map `A₁^ → R₁^`; a second presentation
of `t'` differs from that one by isomorphisms of topological rings. For rig-étaleness this is
`AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_isRepresentableEtale`. -/
theorem hasPropertyOnAffineChartMap_of_isRepresentableEtale_of_propertyIsLocalNoetherian
    (hloc : PropertyIsLocalNoetherian.{u} P)
    (hiso : PropertyInvariantUnderRingEquiv IsNoetherianAdic P)
    {U V U' V' : FppfSheaf B S hS} (t : U ⟶ V) (t' : U' ⟶ V') (q : U' ⟶ U) (r : V' ⟶ V)
    (hU' : IsAffineFormalAlgebraicSpace B S hS U') (hV' : IsAffineFormalAlgebraicSpace B S hS V')
    (hq : IsRepresentableEtale B S hS q) (hr : IsRepresentableEtale B S hS r)
    (hcomm : q ≫ t = t' ≫ r)
    (A R : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hCA : IsNoetherianAdic A) (hCR : IsNoetherianAdic R)
    (hA : IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
    (g : ContinuousHom D E) (hg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv)
    (hP : P g.toRingHom) :
    HasPropertyOnAffineChartMap B S hS IsNoetherianAdic P t' := by
  intro A' R' _ _ _ _ _ _ _ _ hCA' hCR' hA'w D' E' eU' eV' g' hg'
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing R := hCR.2
  have hRw := hCR.1.isWeaklyAdmissible
  have hR'w := hCR'.1.isWeaklyAdmissible
  obtain ⟨R₁, _, _, _, E₁, cU, εU, hcU, hεU⟩ :=
    exists_etale_completion_of_isRepresentableEtale B S hS q hU' hq R hCR.1 E eU
  obtain ⟨A₁, _, _, _, D₁, cV, εV, hcV, hεV⟩ :=
    exists_etale_completion_of_isRepresentableEtale B S hS r hV' hr A hCA.1 D eV
  have hR₁ := isNoetherianAdic_completionOver_algebraMap (A₁ := R₁) hCR
  have hA₁ := isNoetherianAdic_completionOver_algebraMap (A₁ := A₁) hCA
  have hR₁w := hR₁.1.isWeaklyAdmissible
  have hA₁w := hA₁.1.isWeaklyAdmissible
  obtain ⟨h, hh, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA₁w hR₁w
    (εU.inv ≫ t' ≫ εV.hom)
  -- the square is the formal spectrum of a localization diagram
  have hspf : formalSpectrumMap hRw cU ≫ formalSpectrumMap hA g =
      formalSpectrumMap hA₁w h ≫ formalSpectrumMap hA cV := by
    have h1 : t ≫ eV.hom = eU.hom ≫ formalSpectrumMap hA g := by
      rw [hg]; simp
    rw [hh, Category.assoc, Category.assoc, hεV, ← reassoc_of% hcomm, h1, ← reassoc_of% hεU,
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
      commutes := by rw [← hcU, ← hcV]; exact hring }
  have hPh : P h.toRingHom := hloc.localizationPreserves LD hCR hCA hR₁ hA₁ hP
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
  refine hiso hA₁ hR₁ hCA' hCR' h.toRingHom g'.toRingHom h.continuous φV hφVc hφVc' φU hφUc
    hφUc' ?_ hPh
  rw [hring']
  ext x
  simp

/-- **A chart map with `P` followed by a representable étale map.** Let `m : W ⟶ Z` be a
morphism of affine formal algebraic spaces all of whose Noetherian presentations have `P` and
let `c : Z ⟶ V` be representable étale. Then every Noetherian presentation of `m ≫ c` has `P`.

For a presentation `A → R` of `m ≫ c`, Stacks 0AN8 presents `c` by the canonical map
`A → A₁^` to the completion of an étale `A`-algebra, which has `P`; by Stacks 0AN0 the
presentation of `m ≫ c` factors as `A → A₁^ → R` with `A₁^ → R` a presentation of `m`, and `P`
is stable under composition. For rig-étaleness this is
`AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_comp_of_isRepresentableEtale`. -/
theorem hasPropertyOnAffineChartMap_comp_of_isRepresentableEtale_of_stableUnderComposition
    (hcomp : PropertyIsStableUnderCompositionNoetherian.{u} P)
    (hcan : PropertyHoldsOnEtaleCompletion P) {W Z V : FppfSheaf B S hS}
    (m : W ⟶ Z) (c : Z ⟶ V) (hZ : IsAffineFormalAlgebraicSpace B S hS Z)
    (hc : IsRepresentableEtale B S hS c)
    (hm : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic P m) :
    HasPropertyOnAffineChartMap B S hS IsNoetherianAdic P (m ≫ c) := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eW eV g hg
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing R := hCR.2
  have hRw := hCR.1.isWeaklyAdmissible
  obtain ⟨A₁, _, _, _, D₁, cV, εZ, hcV, hεZ⟩ :=
    exists_etale_completion_of_isRepresentableEtale B S hS c hZ hc A hCA.1 D eV
  have hA₁ := isNoetherianAdic_completionOver_algebraMap (A₁ := A₁) hCA
  have hA₁w := hA₁.1.isWeaklyAdmissible
  obtain ⟨h, hh, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA₁w hRw
    (eW.inv ≫ m ≫ εZ.hom)
  have hmh : m = eW.hom ≫ formalSpectrumMap hA₁w h ≫ εZ.inv := by simp [hh]
  have hPh : P h.toRingHom := hm _ _ hA₁ hCR hA₁w D₁ E eW εZ h hmh
  have hspf : formalSpectrumMap hA g = formalSpectrumMap hA (ContinuousHom.comp hA₁w hA h cV) := by
    rw [← formalSpectrumMap_comp_eq hA₁w hA, hh]
    have h1 : formalSpectrumMap hA g = eW.inv ≫ (m ≫ c) ≫ eV.hom := by simp [hg]
    rw [h1, Category.assoc, Category.assoc, Category.assoc, hεZ]
  have hring : g.toRingHom = h.toRingHom.comp cV.toRingHom := by
    rw [toRingHom_eq_of_formalSpectrumMap_eq B S hS hA hRw hspf]
    rfl
  rw [hring, hcV]
  exact hcomp.comp hCR hA₁ hCA h.toRingHom _ h.continuous (continuous_canonicalMap _) hPh
    (hcan _ (RingHom.etale_algebraMap.mpr inferInstance) hCA hA₁)

/-! ### The four conditions -/

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **(4) ⟹ (1).** If the members of an affine étale covering of `X` factor through affine
representable étale charts of `Y` by maps corresponding to `P`-maps in `WAdm^{Noeth}`, then every
affine étale square over `f` has every Noetherian presentation of its upper map with `P`.

Given a square `U₀ ⟶ V₀` over `f` and a presentation `g : A → R` of it, the fibre products
`Qᵢ = Vᵢ ×_Y V₀` are covered by formal spectra `Z` of completed étale `A`-algebras, and the
fibre products `Zᵢ ×_{Qᵢ} (Uᵢ ×_X U₀)` by formal spectra `W` of completed étale `R`-algebras;
the `W` cover `U₀` and finitely many of them make `R` faithfully flat over their product
(`exists_finite_faithfullyFlat_of_isLocallySurjective`). Each `W ⟶ Z` has `P` by the ascent
from `Uᵢ ⟶ Vᵢ`, hence so has `W ⟶ Z ⟶ V₀`, which is `W ⟶ U₀ ⟶ V₀`, and `P` descends to `g`
(`property_of_finite_etale_family`). For rig-étaleness this is
`hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToNoetherianMapAfterSourceCover
    (hcomp : PropertyIsStableUnderCompositionNoetherian.{u} P)
    (hiso : PropertyInvariantUnderRingEquiv IsNoetherianAdic P)
    (hcan : PropertyHoldsOnEtaleCompletion P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : CorrespondsToNoetherianMapAfterSourceCover B S hS P f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic P f := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, U, u, hUcover, hfac⟩ := hf
  choose V v t hVaff hVet hsq hcorr using hfac
  intro U₀ V₀ a b τ hU₀ hV₀ ha hb hτ A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing R := hCR.2
  have hRw := hCR.1.isWeaklyAdmissible
  -- the charts `Z` of `Vᵢ ×_Y V₀`
  have hφ : ∀ i, IsRepresentableEtale B S hS (pullback.snd (v i) b ≫ eV.hom) := fun i ↦
    isRepresentableEtale_comp_hom (isRepresentableEtale_pullback_snd B S hS (v i) b (hVet i)) eV
  choose Kz Cz instCz fz hfz Qz gz hgz wz hwz hwzet hZaff hZnoeth hZsurj using fun i ↦
    exists_noetherian_completion_cover_of_isRepresentableEtale B S hS hCA D _ (hφ i)
  -- the map `Uᵢ ×_X U₀ ⟶ Vᵢ ×_Y V₀`
  let π : ∀ i, pullback (u i) a ⟶ pullback (v i) b := fun i ↦
    pullback.lift (pullback.fst (u i) a ≫ t i) (pullback.snd (u i) a ≫ τ) (by
      rw [Category.assoc, Category.assoc, ← hsq i, ← hτ, ← Category.assoc, ← Category.assoc,
        pullback.condition])
  have hπfst : ∀ i, π i ≫ pullback.fst (v i) b = pullback.fst (u i) a ≫ t i := fun i ↦
    pullback.lift_fst _ _ _
  have hπsnd : ∀ i, π i ≫ pullback.snd (v i) b = pullback.snd (u i) a ≫ τ := fun i ↦
    pullback.lift_snd _ _ _
  -- the charts `W` of `Z ×_{Qᵢ} (Uᵢ ×_X U₀)`
  have hψ : ∀ i (k : Kz i), IsRepresentableEtale B S hS
      (pullback.snd (wz i k) (π i) ≫ pullback.snd (u i) a ≫ eU.hom) := fun i k ↦
    (isRepresentableEtale_pullback_snd B S hS (wz i k) (π i) (hwzet i k)).comp B S hS
      (isRepresentableEtale_comp_hom
        (isRepresentableEtale_pullback_snd B S hS (u i) a (hUcover.2.1 i)) eU)
  choose Kw Cw instCw fw hfw Qw gw hgw ww hww hwwet hWaff hWnoeth hWsurj using fun i k ↦
    exists_noetherian_completion_cover_of_isRepresentableEtale B S hS hCR E _ (hψ i k)
  -- the refined family, indexed by `x = ⟨i, k, l⟩`
  let Ix := Σ i, Σ k : Kz i, Kw i k
  let p : ∀ x : Ix, formalSpectrum (Qw x.1 x.2.1 x.2.2) ⟶ U₀ := fun x ↦
    ww x.1 x.2.1 x.2.2 ≫ pullback.snd (wz x.1 x.2.1) (π x.1) ≫ pullback.snd (u x.1) a
  have hpE : ∀ x : Ix, p x ≫ eU.hom = formalSpectrumMap hRw (gw x.1 x.2.1 x.2.2) := fun x ↦ by
    simpa only [p, Category.assoc] using hww x.1 x.2.1 x.2.2
  -- joint surjectivity
  have hsurjP : Sheaf.IsLocallySurjective (Sigma.desc p) := by
    have hstage : ∀ i, Sheaf.IsLocallySurjective (Sigma.desc fun y : Σ k : Kz i, Kw i k ↦
        ww i y.1 y.2 ≫ pullback.snd (wz i y.1) (π i)) := fun i ↦
      isLocallySurjective_sigmaDesc_comp_pullback_snd (π i) (wz i) (hZsurj i) (ww i) (hWsurj i)
    have h := isLocallySurjective_sigmaDesc_comp_pullback_snd a u hUcover.2.2
      (K := fun i ↦ Σ k : Kz i, Kw i k) (W := fun i y ↦ formalSpectrum (Qw i y.1 y.2))
      (fun i y ↦ ww i y.1 y.2 ≫ pullback.snd (wz i y.1) (π i)) hstage
    simpa only [p, Category.assoc] using h
  have hsurjE : Sheaf.IsLocallySurjective
      (Sigma.desc fun x : Ix ↦ formalSpectrumMap hRw (gw x.1 x.2.1 x.2.2)) := by
    have hfac : Sigma.desc p ≫ eU.hom =
        Sigma.desc fun x : Ix ↦ formalSpectrumMap hRw (gw x.1 x.2.1 x.2.2) :=
      Sigma.hom_ext _ _ fun x ↦ by rw [Sigma.ι_desc_assoc, Sigma.ι_desc, hpE]
    rw [← hfac]
    have := (Sheaf.isLocallySurjective_iff_epi _).1 hsurjP
    exact (Sheaf.isLocallySurjective_iff_epi _).2 (epi_comp _ _)
  obtain ⟨σ, _, kx, hff⟩ := exists_finite_faithfullyFlat_of_isLocallySurjective hRw E
    (fun x : Ix ↦ fw x.1 x.2.1 x.2.2) (fun x ↦ hfw x.1 x.2.1 x.2.2)
    (fun x ↦ Qw x.1 x.2.1 x.2.2) (fun x ↦ gw x.1 x.2.1 x.2.2) (fun x ↦ hgw x.1 x.2.1 x.2.2)
    hsurjE
  -- the property for each composite `W ⟶ U₀ ⟶ V₀`
  have hcompW : ∀ x : Ix, HasPropertyOnAffineChartMap B S hS IsNoetherianAdic P (p x ≫ τ) := by
    rintro ⟨i, k, l⟩
    let m : formalSpectrum (Qw i k l) ⟶ formalSpectrum (Qz i k) :=
      ww i k l ≫ pullback.fst (wz i k) (π i)
    let r : formalSpectrum (Qz i k) ⟶ V i := wz i k ≫ pullback.fst (v i) b
    let c : formalSpectrum (Qz i k) ⟶ V₀ := wz i k ≫ pullback.snd (v i) b
    let q : formalSpectrum (Qw i k l) ⟶ U i :=
      ww i k l ≫ pullback.snd (wz i k) (π i) ≫ pullback.fst (u i) a
    have hq : IsRepresentableEtale B S hS q :=
      (hwwet i k l).comp B S hS ((isRepresentableEtale_pullback_snd B S hS (wz i k) (π i)
        (hwzet i k)).comp B S hS (isRepresentableEtale_pullback_fst B S hS (u i) a ha))
    have hr : IsRepresentableEtale B S hS r :=
      (hwzet i k).comp B S hS (isRepresentableEtale_pullback_fst B S hS (v i) b hb)
    have hc : IsRepresentableEtale B S hS c :=
      (hwzet i k).comp B S hS (isRepresentableEtale_pullback_snd B S hS (v i) b (hVet i))
    have hqr : q ≫ t i = m ≫ r := by
      simp only [q, m, r, Category.assoc]
      rw [← hπfst, ← reassoc_of% (pullback.condition (f := wz i k) (g := π i))]
    have hpc : p ⟨i, k, l⟩ ≫ τ = m ≫ c := by
      simp only [p, m, c, Category.assoc]
      rw [← hπsnd, ← reassoc_of% (pullback.condition (f := wz i k) (g := π i))]
    obtain ⟨Ai, Ri, _, _, _, _, _, _, _, _, hCAi, hCRi, hAi, Di, Ei, eUi, eVi, gi, hgi, hPi⟩ :=
      hcorr i
    have hm : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic P m :=
      hasPropertyOnAffineChartMap_of_isRepresentableEtale_of_propertyIsLocalNoetherian
        hcomp.isLocal hiso (t i) m q r (hWaff i k l) (hZaff i k) hq hr hqr Ai Ri hCAi hCRi hAi
        Di Ei eUi eVi gi hgi hPi
    rw [hpc]
    exact hasPropertyOnAffineChartMap_comp_of_isRepresentableEtale_of_stableUnderComposition
      hcomp hcan m c (hZaff i k) hc hm
  -- descent along the finite faithfully flat family
  let : ∀ j, Algebra R (Cw (kx j).1 (kx j).2.1 (kx j).2.2) := fun j ↦
    (fw (kx j).1 (kx j).2.1 (kx j).2.2).toAlgebra
  have : ∀ j, Algebra.Etale R (Cw (kx j).1 (kx j).2.1 (kx j).2.2) := fun j ↦
    hfw (kx j).1 (kx j).2.1 (kx j).2.2
  refine property_of_finite_etale_family hcomp.isLocal hiso (σ := σ) hCA hCR g.toRingHom
    g.continuous (fun j : σ ↦ Cw (kx j).1 (kx j).2.1 (kx j).2.2) hff fun j ↦ ?_
  have hsqW : p (kx j) ≫ τ = (Iso.refl _).hom ≫ formalSpectrumMap hA
      (ContinuousHom.comp hRw hA (gw (kx j).1 (kx j).2.1 (kx j).2.2) g) ≫ eV.inv := by
    rw [← formalSpectrumMap_comp_eq hRw hA, Iso.refl_hom, Category.id_comp, ← hpE (kx j), hg]
    simp
  have h := hcompW (kx j) A _ hCA (hWnoeth (kx j).1 (kx j).2.1 (kx j).2.2) hA D
    (Qw (kx j).1 (kx j).2.1 (kx j).2.2) (Iso.refl _) eV
    (ContinuousHom.comp hRw hA (gw (kx j).1 (kx j).2.1 (kx j).2.2) g) hsqW
  rwa [ContinuousHom.comp_toRingHom, hgw] at h

/-- **(3) ⟹ (4).** Composing the coverings of the fibre products `Yⱼ ×_Y X` with their
projections to `X` gives a covering of `X` whose members factor through the charts `Yⱼ` by the
same maps. -/
theorem correspondsToNoetherianMapAfterSourceCover_of_afterTargetCover
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : CorrespondsToNoetherianMapAfterTargetCover B S hS P f) :
    CorrespondsToNoetherianMapAfterSourceCover B S hS P f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, ⟨hVaffine, hVetale, hVsurj⟩, hcharts⟩ := hf
  choose I U w hUcover hUproperty using hcharts
  refine ⟨(j : J) × I j, fun p ↦ U p.1 p.2, fun p ↦ w p.1 p.2 ≫ pullback.snd (v p.1) f,
    ⟨fun p ↦ (hUcover p.1).1 p.2, fun p ↦ IsRepresentableEtale.comp B S hS
      ((hUcover p.1).2.1 p.2)
      (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVetale p.1)), ?_⟩,
    fun p ↦ ⟨V p.1, v p.1, w p.1 p.2 ≫ pullback.fst (v p.1) f, hVaffine p.1, hVetale p.1,
      by rw [Category.assoc, Category.assoc, ← pullback.condition], hUproperty p.1 p.2⟩⟩
  exact isLocallySurjective_sigmaDesc_comp_pullback_snd f v hVsurj
    w fun j ↦ (hUcover j).2.2

/-- **(1) ⟹ (3).** For a morphism of locally Noetherian formal algebraic spaces with `P` on
every affine étale diagram, the Noetherian atlas of `Y`, together with, for each of its members
`Yⱼ`, the covering of `Yⱼ ×_Y X` by formal spectra of completed étale algebras over the members
`Xᵢ` of the Noetherian atlas of `X` (charts of `Xᵢ ×_X (Yⱼ ×_Y X)`, Stacks 0AN8), is as in
condition (3): each chart map is a map of formal spectra of Noetherian adic rings, which the
chart condition gives `P`. -/
theorem correspondsToNoetherianMapAfterTargetCover_of_hasPropertyOnEveryAffineEtaleDiagram
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic P f) :
    CorrespondsToNoetherianMapAfterTargetCover B S hS P f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, IX, Xi, ui, -, hXet, hXsurj, hXnoeth⟩ := hX
  obtain ⟨-, JY, Yj, vj, hYaff, hYet, hYsurj, hYnoeth⟩ := hY
  refine ⟨JY, Yj, vj, ⟨hYaff, hYet, hYsurj⟩, fun j ↦ ?_⟩
  obtain ⟨-, Aj, _, _, _, _, hApres, hAnoeth, hAadic⟩ := hYnoeth j
  have hCA : IsNoetherianAdic Aj := ⟨hAadic, hAnoeth⟩
  let Dj := hApres.2.some.quotientSystem
  let eYj : Yj j ≅ formalSpectrum Dj := hApres.2.some.formalSpectrumIso
  have hPsnd : IsRepresentableEtale B S hS (pullback.snd (vj j) f) :=
    isRepresentableEtale_pullback_snd B S hS (vj j) f (hYet j)
  have hcharts : ∀ i : IX, ∃ (K : Type (u + 1)) (W : K → FppfSheaf B S hS)
      (w : ∀ k, W k ⟶ pullback (ui i) (pullback.snd (vj j) f)),
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (W k)) ∧
      (∀ k, IsRepresentableEtale B S hS (w k)) ∧
      Sheaf.IsLocallySurjective (Sigma.desc w) ∧
      ∀ k, CorrespondsToNoetherianMap B S hS P
        (w k ≫ pullback.snd (ui i) (pullback.snd (vj j) f) ≫ pullback.fst (vj j) f) := by
    intro i
    obtain ⟨-, Ri, _, _, _, _, hRpres, hRnoeth, hRadic⟩ := hXnoeth i
    have hCR : IsNoetherianAdic Ri := ⟨hRadic, hRnoeth⟩
    let Ei := hRpres.2.some.quotientSystem
    let eXi : Xi i ≅ formalSpectrum Ei := hRpres.2.some.formalSpectrumIso
    have hφ : IsRepresentableEtale B S hS
        (pullback.fst (ui i) (pullback.snd (vj j) f) ≫ eXi.hom) :=
      isRepresentableEtale_comp_hom (isRepresentableEtale_pullback_fst B S hS (ui i) _ hPsnd) eXi
    obtain ⟨K, C, _, fk, -, Q, g, -, w, -, hwet, hWaff, hWnoeth, hsurj⟩ :=
      exists_noetherian_completion_cover_of_isRepresentableEtale B S hS hCR Ei _ hφ
    refine ⟨K, fun k ↦ formalSpectrum (Q k), w, hWaff, hwet, hsurj, fun k ↦ ?_⟩
    have hsq : (w k ≫ pullback.snd (ui i) (pullback.snd (vj j) f) ≫ pullback.snd (vj j) f) ≫ f =
        (w k ≫ pullback.snd (ui i) (pullback.snd (vj j) f) ≫ pullback.fst (vj j) f) ≫ vj j := by
      simp only [Category.assoc, pullback.condition]
    exact correspondsToNoetherianMap_of_hasPropertyOnAffineChartMap
      (hf _ _ _ (vj j) _ (hWaff k) (hYaff j) ((hwet k).comp B S hS
        ((isRepresentableEtale_pullback_snd B S hS (ui i) _ (hXet i)).comp B S hS hPsnd))
        (hYet j) hsq) hCA (hWnoeth k) Dj (Q k) (Iso.refl _) eYj
  choose K W w hWaff hWet hWsurj hWcorr using hcharts
  refine ⟨(i : IX) × K i, fun x ↦ W x.1 x.2,
    fun x ↦ w x.1 x.2 ≫ pullback.snd (ui x.1) (pullback.snd (vj j) f),
    ⟨fun x ↦ hWaff x.1 x.2, fun x ↦ (hWet x.1 x.2).comp B S hS
      (isRepresentableEtale_pullback_snd B S hS (ui x.1) _ (hXet x.1)), ?_⟩,
    fun x ↦ by simpa only [Category.assoc] using hWcorr x.1 x.2⟩
  exact isLocallySurjective_sigmaDesc_comp_pullback_snd _ ui hXsurj
    w hWsurj

/-- **The two readings of condition (1) agree.** For a morphism `f : X ⟶ Y` of locally
Noetherian formal algebraic spaces and a property `P` invariant under isomorphisms of
topological rings, every affine étale square over `f` has its upper map corresponding to a
`P`-map in `WAdm^{Noeth}` if and only if every Noetherian presentation of that upper map has
`P`.

A map corresponding to a `P`-map has every Noetherian presentation with `P` (Stacks 0AN0).
Conversely the two charts of a square are Noetherian by Stacks 0AKX, hence formal spectra of
Noetherian adic rings, and a presentation of the upper map between them exists by Stacks
0AN0. -/
theorem correspondsToNoetherianMapOnEveryAffineEtaleDiagram_iff
    (hiso : PropertyInvariantUnderRingEquiv IsNoetherianAdic P) {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    CorrespondsToNoetherianMapOnEveryAffineEtaleDiagram B S hS P f ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic P f :=
  ⟨fun h U V a b t hU hV ha hb hsq ↦ hasPropertyOnAffineChartMap_of_correspondsToNoetherianMap
    hiso (h U V a b t hU hV ha hb hsq), fun h U V a b t hU hV ha hb hsq ↦
    correspondsToNoetherianMap_of_hasPropertyOnAffineChartMap_of_isNoetherian
      (h U V a b t hU hV ha hb hsq)
      (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX a hU ha)
      (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hY b hV hb)⟩

/-- **The four conditions agree** (Stacks 0GCZ and Stacks 0GCQ for the property `P`). Let `P` be
a local property of arrows of `WAdm^{Noeth}` stable under composition, invariant under
isomorphisms of topological rings and holding for the canonical maps to completions of étale
algebras, and let `f : X ⟶ Y` be a morphism of locally Noetherian formal algebraic spaces over
`S`. The following are equivalent:

1. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, every presentation of `U ⟶ V` by
   Noetherian adic rings has `P`;
2. for every such square the morphism `U ⟶ V` corresponds to a `P`-map in `WAdm^{Noeth}`;
3. condition (3) of Stacks 0GCZ for `P` (`CorrespondsToNoetherianMapAfterTargetCover`);
4. condition (4) of Stacks 0GCZ for `P` (`CorrespondsToNoetherianMapAfterSourceCover`). -/
theorem hasPropertyOnEveryAffineEtaleDiagram_tfae_of_isLocallyNoetherian
    (hcomp : PropertyIsStableUnderCompositionNoetherian.{u} P)
    (hiso : PropertyInvariantUnderRingEquiv IsNoetherianAdic P)
    (hcan : PropertyHoldsOnEtaleCompletion P)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic P f,
        CorrespondsToNoetherianMapOnEveryAffineEtaleDiagram B S hS P f,
        CorrespondsToNoetherianMapAfterTargetCover B S hS P f,
        CorrespondsToNoetherianMapAfterSourceCover B S hS P f] := by
  tfae_have 1 ↔ 2 := (correspondsToNoetherianMapOnEveryAffineEtaleDiagram_iff hiso f hX hY).symm
  tfae_have 1 → 3 :=
    correspondsToNoetherianMapAfterTargetCover_of_hasPropertyOnEveryAffineEtaleDiagram f hX hY
  tfae_have 3 → 4 := correspondsToNoetherianMapAfterSourceCover_of_afterTargetCover f
  tfae_have 4 → 1 :=
    hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToNoetherianMapAfterSourceCover hcomp
      hiso hcan f
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
