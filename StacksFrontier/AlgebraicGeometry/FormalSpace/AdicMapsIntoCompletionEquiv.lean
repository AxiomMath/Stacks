module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMapsIntoCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseSubspaces

/-!
# Adic maps out of a formal spectrum into a completion, as a bijection

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `T ⊆ |X|` be a closed
subset whose complementary open subspace has quasi-compact inclusion `X \ T ⟶ X`. Let `R` be
a Noetherian complete local `S`-algebra with maximal ideal `𝔪`. **Stacks 0GBU** says that the
adic morphisms `p : Spf R ⟶ X_{/T}` correspond to the morphisms `g : Spec R ⟶ X` with
`g⁻¹(T) = {𝔪}`, the correspondence sending `p` to the unique `g` restricting on `Spf R` to the
composite `Spf R ⟶ X_{/T} ⟶ X`.

The direction from `p` to `g` is
`AlgebraicGeometry.FormalSpace.existsUnique_algebraization_of_adic_into_completion`. This file
proves the converse direction and assembles the two into one bijection.

## Main definitions

* `AlgebraicGeometry.FormalSpace.formalSpectrumIsoCompletion`: for `R` a Noetherian local ring
  whose weak ideals of definition are cofinal among the powers of `𝔪`, the formal spectrum
  `Spf R` is the completion of `Spec R` along its closed point.
* `AlgebraicGeometry.FormalSpace.adicOfAlgebraization`: the morphism `Spf R ⟶ X_{/T}` through
  which the restriction of a `g : Spec R ⟶ X` with `g⁻¹(T) = {𝔪}` to `Spf R` factors.
* `AlgebraicGeometry.FormalSpace.algebraizationOfAdic`: the morphism `g : Spec R ⟶ X` attached
  to an adic `p : Spf R ⟶ X_{/T}`.
* `AlgebraicGeometry.FormalSpace.adicCompletionHomEquiv`: **Stacks 0GBU**, the bijection between
  the adic morphisms `Spf R ⟶ X_{/T}` and the morphisms `g : Spec R ⟶ X` with `g⁻¹(T) = {𝔪}`.

## Main results

* `AlgebraicGeometry.FormalSpace.formalSpectrumToSpec_comp_eq_adicOfAlgebraization_comp`: the
  restriction of `g` to `Spf R` is `adicOfAlgebraization` followed by `X_{/T} ⟶ X`.
* `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_adicOfAlgebraization`:
  `adicOfAlgebraization` is adic, i.e. representable by algebraic spaces.
* `AlgebraicGeometry.FormalSpace.existsUnique_adic_of_preimageEqClosedPoint`: the converse half
  of **Stacks 0GBU**, every `g` with `g⁻¹(T) = {𝔪}` restricts on `Spf R` to a unique morphism
  into `X_{/T}`, and that morphism is adic.
* `AlgebraicGeometry.FormalSpace.formalSpectrumToSpec_comp_adicCompletionHomEquiv` and
  `AlgebraicGeometry.FormalSpace.adicCompletionHomEquiv_apply_eq_iff`: the bijection sends `p`
  to the morphism `g` whose restriction to `Spf R` is `p` followed by `X_{/T} ⟶ X`.

## Implementation notes

*The converse direction.* Given `g` with `g⁻¹(T) = {𝔪}`, the morphism `Spf R ⟶ X_{/T}` is the
composite

`Spf R ≅ (Spec R)_{/{𝔪}} = (Spec R)_{/g⁻¹(T)} ⟶ X_{/T}`.

The first arrow identifies the formal spectrum with the completion of `Spec R` along its closed
point. That completion is the colimit of the spectra `Spec (R ⧸ J)` over the ideals `J` with
`√J = 𝔪`, by `AlgebraicGeometry.FormalSpace.isIso_supportComparison` (the presentation of
Stacks 0AIY); the weak ideals of definition of `R` are among those ideals and are cofinal in
them, because they contain and are cofinal with the powers of `𝔪` and `𝔪` is finitely
generated, so the two colimits agree. The last arrow is the morphism of completions induced by
`g`, which is representable by algebraic spaces by **Stacks 0APV**
(`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionMap`); this is where
adicness of the converse comes from. Its compatibility with `g` is checked on each quotient
stage `Spec (R ⧸ J)`, where both sides are the restriction of `g` along `Spec (R ⧸ J) ⟶ Spec R`.

*The bijection.* The two composites are identities by the two uniqueness statements available:
`X_{/T} ⟶ X` is a monomorphism, and a morphism `Spec R ⟶ X` is determined by its restriction
to `Spf R` (**Stacks 0AQH**).

*The hypotheses.* Closedness of `T` and quasi-compactness of `X \ T ⟶ X` are hypotheses of the
source, which uses them to see that `X_{/T}` is adic*, so that adicness of a morphism into it is
meaningful; they are carried by the bijection, whose forward direction is stated under them, but
the converse direction does not use them.

## References

* [Stacks Project, Tag 0GBU](https://stacks.math.columbia.edu/tag/0GBU)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

/-! ### The weak ideals of definition of a Noetherian local ring -/

section WeakIdeals

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsLocalRing R]

/-- A weak ideal of definition of a local ring lies in the maximal ideal, as soon as some weak
ideal of definition does: otherwise it is the unit ideal, so `1` is topologically nilpotent and
lies in every open ideal. -/
theorem weakIdeal_le_maximalIdeal_of_exists_weakIdeal_le
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ IsLocalRing.maximalIdeal R ^ n)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    J.1 ≤ IsLocalRing.maximalIdeal R := by
  refine IsLocalRing.le_maximalIdeal fun hJ => ?_
  obtain ⟨J₀, hJ₀⟩ := hD 1
  rw [pow_one] at hJ₀
  have h1 : (1 : R) ∈ J.1 := hJ ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (J.2.2 1 h1).exists_pow_mem_of_mem_nhds (J₀.2.1.mem_nhds J₀.1.zero_mem)
  rw [one_pow] at hn
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top (hJ₀ hn)

/-- A weak ideal of definition of a local ring whose weak ideals of definition are cofinal with
the powers of the maximal ideal has radical the maximal ideal: it contains a power of `𝔪` and
lies in `𝔪`. -/
theorem radical_weakIdeal_eq
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ IsLocalRing.maximalIdeal R ^ n)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    J.1.radical = (IsLocalRing.maximalIdeal R).radical := by
  refine le_antisymm (Ideal.radical_mono (weakIdeal_le_maximalIdeal_of_exists_weakIdeal_le hD J)) ?_
  rw [(IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical]
  obtain ⟨n, hn⟩ := hD₁ J
  exact fun x hx => ⟨n, hn (Ideal.pow_mem_pow hx n)⟩

/-- In a Noetherian local ring every ideal with radical the maximal ideal contains a weak ideal
of definition, when these are cofinal among the powers of `𝔪`: such an ideal contains a power
of the finitely generated ideal `𝔪`. -/
theorem exists_weakIdeal_le_of_radical_eq [IsNoetherianRing R]
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ IsLocalRing.maximalIdeal R ^ n)
    (K : Ideal R) (hK : K.radical = (IsLocalRing.maximalIdeal R).radical) :
    ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }, J.1 ≤ K := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (Ideal.le_radical.trans hK.symm.le) ((IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing)
  obtain ⟨J, hJ⟩ := hD n
  exact ⟨J, hJ.trans hn⟩

/-- The weak ideals of definition of `R`, ordered by reverse inclusion, as indices of the
presentation of the completion of `Spec R` along its closed point by the quotients of `R` by
the ideals with radical `𝔪`. -/
def weakIdealSupportIndex
    (hrad : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1.radical = (IsLocalRing.maximalIdeal R).radical) :
    OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } ⥤
      SupportIndex (IsLocalRing.maximalIdeal R) :=
  Monotone.functor
    (f := fun J => ULift.up (OrderDual.toDual ⟨(OrderDual.ofDual J).1, hrad _⟩))
    (fun _ _ h => h)

/-- The weak ideals of definition are cofinal among the ideals with radical `𝔪`. -/
theorem final_weakIdealSupportIndex [IsNoetherianRing R]
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ IsLocalRing.maximalIdeal R ^ n)
    (hrad : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1.radical = (IsLocalRing.maximalIdeal R).radical) :
    (weakIdealSupportIndex hrad).Final := by
  have := weakIdeals_isDirected (R := R)
  refine Functor.final_of_exists_of_isFiltered _ (fun K => ?_)
    (fun {_ c} _ _ => ⟨c, 𝟙 c, Subsingleton.elim _ _⟩)
  obtain ⟨J, hJ⟩ := exists_weakIdeal_le_of_radical_eq hD (OrderDual.ofDual K.down).1
    (OrderDual.ofDual K.down).2
  exact ⟨OrderDual.toDual J, ⟨homOfLE hJ⟩⟩

end WeakIdeals

/-! ### The formal spectrum is the completion along the closed point -/

section Comparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] [IsLocalRing R]

/-- The quotient stage `Spec (R ⧸ J)` of the quotient system is the stage `Spec (R ⧸ J)` of the
presentation of the completion along the closed point: the two carry the same structure
morphism to `S`. -/
def stageIsoSupportStage
    (D : QuotientSystem B S hS R)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (hrad : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1.radical = (IsLocalRing.maximalIdeal R).radical)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    D.stage J ≅ supportStage B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨J.1, hrad J⟩ :=
  ObjectProperty.isoMk _ (Over.isoMk (Iso.refl _) (by
    apply ObjectProperty.hom_ext
    exact (Category.id_comp _).trans (hq J)))

/-- The diagram of quotient stages of `R` is the restriction of the presentation of the
completion along the closed point to the weak ideals of definition. -/
def weakIdealDiagramIso
    (D : QuotientSystem B S hS R)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (hrad : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1.radical = (IsLocalRing.maximalIdeal R).radical) :
    weakIdealSupportIndex hrad ⋙ supportDiagram B S hS hRS q (IsLocalRing.maximalIdeal R) ≅
      D.diagram :=
  NatIso.ofComponents (fun J => (stageIsoSupportStage D hRS q hq hrad (OrderDual.ofDual J)).symm)
    (by
      intro J K f
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The formal spectrum of a Noetherian complete local ring is the completion of its spectrum
along the closed point**: `Spf R ≅ (Spec R)_{/V(𝔪)}`, for a quotient system on `R` whose weak
ideals of definition are cofinal among the powers of `𝔪`. -/
def formalSpectrumIsoCompletion [IsNoetherianRing R]
    (D : QuotientSystem B S hS R)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (hrad : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1.radical = (IsLocalRing.maximalIdeal R).radical)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ IsLocalRing.maximalIdeal R ^ n) :
    formalSpectrum D ≅ zeroLocusCompletion B S hS hRS q (IsLocalRing.maximalIdeal R) :=
  have := final_weakIdealSupportIndex hD hrad
  have := isIso_supportComparison B S hS hRS q (IsLocalRing.maximalIdeal R)
  (HasColimit.isoOfNatIso (Functor.isoWhiskerRight (weakIdealDiagramIso D hRS q hq hrad)
      (BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))).symm ≪≫
    Functor.Final.colimitIso (weakIdealSupportIndex hrad)
      (supportSheafDiagram B S hS hRS q (IsLocalRing.maximalIdeal R)) ≪≫
    asIso (supportComparison B S hS hRS q (IsLocalRing.maximalIdeal R))

/-- On a quotient stage the identification `Spf R ≅ (Spec R)_{/V(𝔪)}` is the canonical
morphism of that stage into the completion. -/
theorem formalSpectrumInclusion_comp_formalSpectrumIsoCompletion_hom [IsNoetherianRing R]
    (D : QuotientSystem B S hS R)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (hrad : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1.radical = (IsLocalRing.maximalIdeal R).radical)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ IsLocalRing.maximalIdeal R ^ n)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    formalSpectrumInclusion D (OrderDual.toDual J) ≫
        (formalSpectrumIsoCompletion D hRS q hq hrad hD).hom =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (stageIsoSupportStage D hRS q hq hrad J).hom) ≫
        supportStageToCompletion B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨J.1, hrad J⟩ := by
  have := final_weakIdealSupportIndex hD hrad
  have := isIso_supportComparison B S hS hRS q (IsLocalRing.maximalIdeal R)
  let w := Functor.isoWhiskerRight (weakIdealDiagramIso D hRS q hq hrad)
    (BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
  have h1 := HasColimit.isoOfNatIso_ι_inv w (OrderDual.toDual J)
  have h2 := Functor.Final.ι_colimitIso_hom (weakIdealSupportIndex hrad)
    (supportSheafDiagram B S hS hRS q (IsLocalRing.maximalIdeal R)) (OrderDual.toDual J)
  have h3 := supportComparison_stage B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨J.1, hrad J⟩
  calc _ = (colimit.ι (formalSpectrumDiagram D) (OrderDual.toDual J) ≫
          (HasColimit.isoOfNatIso w).inv) ≫
        (Functor.Final.colimitIso (weakIdealSupportIndex hrad)
          (supportSheafDiagram B S hS hRS q (IsLocalRing.maximalIdeal R))).hom ≫
          supportComparison B S hS hRS q (IsLocalRing.maximalIdeal R) :=
        (Category.assoc _ _ _).symm
    _ = w.inv.app (OrderDual.toDual J) ≫ (colimit.ι
          (weakIdealSupportIndex hrad ⋙
            supportSheafDiagram B S hS hRS q (IsLocalRing.maximalIdeal R))
            (OrderDual.toDual J) ≫
          (Functor.Final.colimitIso (weakIdealSupportIndex hrad)
          (supportSheafDiagram B S hS hRS q (IsLocalRing.maximalIdeal R))).hom) ≫
          supportComparison B S hS hRS q (IsLocalRing.maximalIdeal R) := by
        rw [h1, Category.assoc, Category.assoc]
        rfl
    _ = _ := by
        rw [h2]
        exact congrArg (_ ≫ ·) h3

end Comparison

/-! ### The converse: from `g` with `g⁻¹(T) = {𝔪}` to an adic morphism into `X_{/T}` -/

section Converse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For an `R`-point `g` of `X` with `g⁻¹(T) = {𝔪}`, the inverse image of `T` under `g` is the
zero locus of `𝔪`, read as a set of points of the presheaf represented by `Spec R`. -/
theorem zeroLocusPoints_maximalIdeal_eq {R : Type u} [CommRing R]
    (hR : IsNoetherianCompleteLocalRing R)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X))
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (s : X.obj (op ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q))))
    (hs : PreimageEqClosedPoint hR T hRS q s) :
    zeroLocusPoints B S hS hRS q (@IsLocalRing.maximalIdeal R _ hR.isLocal) =
      Space.pointsMap B S hS
        (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)))
        (yonedaEquiv.symm s) ⁻¹' T := by
  let := hR.isLocal
  have key : ∀ y : PrimeSpectrum R,
      y ∈ PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R) ↔
        y = IsLocalRing.closedPoint R := by
    intro y
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    refine ⟨fun h => PrimeSpectrum.ext
      (le_antisymm (IsLocalRing.le_maximalIdeal y.isPrime.ne_top) h), ?_⟩
    rintro rfl
    exact le_rfl
  rw [hs, ← supportedPoints_zeroLocus]
  ext x
  exact key (Space.pointsToScheme B S hS _ x)

/-- **The adic morphism attached to an algebraization.** For a morphism `g : Spec R ⟶ X` with
`g⁻¹(T) = {𝔪}`, the morphism `Spf R ⟶ X_{/T}`: the identification of `Spf R` with the completion
of `Spec R` along its closed point, followed by the morphism of completions
`(Spec R)_{/g⁻¹(T)} ⟶ X_{/T}` induced by `g`. -/
def adicOfAlgebraization {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX)
    (hg : PreimageEqClosedPoint hR T hRS q
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) :
    formalSpectrum D ⟶ Space.completionSheaf B S hS X T :=
  let := hR.isLocal
  let := hR.isNoetherian
  (formalSpectrumIsoCompletion D hRS q hq (radical_weakIdeal_eq hD₁ hD) hD).hom ≫
    Space.completionSheafRestrict B S hS
      (yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down)
      (zeroLocusPoints B S hS hRS q (IsLocalRing.maximalIdeal R)) T
      (zeroLocusPoints_maximalIdeal_eq hR T hRS q _ hg).le

/-- The stage morphism `Spec (R ⧸ J) ⟶ Spec R` of the quotient system, read through the
identification of the stage with the stage of the presentation of the completion, is the
morphism of that presentation. -/
private theorem stageIsoSupportStage_hom_comp_supportStageToAffine
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsLocalRing R]
    (D : QuotientSystem B S hS R)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (hrad : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1.radical = (IsLocalRing.maximalIdeal R).radical)
    (J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (BigAffineFppf.inclusion B S hS).map (stageIsoSupportStage D hRS q hq hrad J).hom ≫
        supportStageToAffine B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨J.1, hrad J⟩ =
      (BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS q J (hq J)) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact Category.id_comp _

/-- **The restriction of `g` to `Spf R` factors through `X_{/T}`.** For `g : Spec R ⟶ X` with
`g⁻¹(T) = {𝔪}`, the restriction of `g` along `Spf R ⟶ Spec R` is
`AlgebraicGeometry.FormalSpace.adicOfAlgebraization` followed by `X_{/T} ⟶ X`. Both sides are
checked on each quotient stage `Spec (R ⧸ J)`, where they are the restriction of `g` along
`Spec (R ⧸ J) ⟶ Spec R`. -/
theorem formalSpectrumToSpec_comp_eq_adicOfAlgebraization_comp
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX)
    (hg : PreimageEqClosedPoint hR T hRS q
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) :
    formalSpectrumToSpec D hRS q hq ≫ g =
      adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g hg ≫ completionToUpliftedSheaf X hX T := by
  let := hR.isLocal
  let := hR.isNoetherian
  let J := BigFppfOver.topology B S hS
  let U := (BigAffineFppf.inclusion B S hS).obj (specOver hRS q)
  let s := (Sheaf.sectionEquiv J g).down
  let g₀ : yoneda.obj U ⟶ X := yonedaEquiv.symm s
  let hrad := radical_weakIdeal_eq hD₁ hD
  let Z : Set (Space.points B S hS (yoneda.obj U)) :=
    zeroLocusPoints B S hS hRS q (IsLocalRing.maximalIdeal R)
  have hZ : Z ⊆ Space.pointsMap B S hS (yoneda.obj U) g₀ ⁻¹' T :=
    (zeroLocusPoints_maximalIdeal_eq hR T hRS q _ hg).le
  let ρ := Space.completionSheafRestrict B S hS g₀ Z T hZ
  apply colimit.hom_ext
  intro K
  let K' := OrderDual.ofDual K
  have hL : formalSpectrumInclusion D (OrderDual.toDual K') ≫ formalSpectrumToSpec D hRS q hq ≫ g =
      (Sheaf.sheafifiedYoneda J).map
        ((BigAffineFppf.inclusion B S hS).map (stageToSpec D hRS q K' (hq K'))) ≫ g :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ g) (formalSpectrumToSpec_spec D hRS q hq K'))
  have hst := formalSpectrumInclusion_comp_formalSpectrumIsoCompletion_hom D hRS q hq hrad hD K'
  have hR' : formalSpectrumInclusion D (OrderDual.toDual K') ≫
        adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g hg ≫ completionToUpliftedSheaf X hX T =
      (Sheaf.sheafifiedYoneda J).map
          ((BigAffineFppf.inclusion B S hS).map (stageIsoSupportStage D hRS q hq hrad K').hom) ≫
        supportStageToCompletion B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨K'.1, hrad K'⟩ ≫
          ρ ≫ completionToUpliftedSheaf X hX T :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ completionToUpliftedSheaf X hX T)
        ((Category.assoc (formalSpectrumInclusion D (OrderDual.toDual K'))
          (formalSpectrumIsoCompletion D hRS q hq hrad hD).hom ρ).symm.trans
          (congrArg (· ≫ ρ) hst))).trans ((Category.assoc _ _ _).trans (Category.assoc _ _ _))
  refine hL.trans (Eq.trans ?_ hR'.symm)
  apply (Sheaf.sectionEquiv J).injective
  rw [Sheaf.sectionEquiv_map_comp, Sheaf.sectionEquiv_map_comp]
  have hnat := Space.completionSheafRestrict_comp_completionSheafToAmbient B S hS g₀ Z T hZ
    (upliftedSheaf (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).property
    (upliftedSheaf X hX).property
  have hamb := Space.toSheafify_comp_completionSheafToAmbient B S hS (yoneda.obj U)
    (upliftedSheaf (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).property Z
  have hsec : Sheaf.sectionEquiv J
        (supportStageToCompletion B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨K'.1, hrad K'⟩ ≫
          ρ ≫ completionToUpliftedSheaf X hX T) =
      ULift.up (X.map (supportStageToAffine B S hS hRS q (IsLocalRing.maximalIdeal R)
        ⟨K'.1, hrad K'⟩).op s) := by
    let V := (BigAffineFppf.inclusion B S hS).obj
      (supportStage B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨K'.1, hrad K'⟩)
    let C := Space.completionSubfunctor B S hS (yoneda.obj U) Z
    let x : C.toFunctor.obj (op V) :=
      ⟨⟨supportStageToAffine B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨K'.1, hrad K'⟩⟩,
        supportStage_hasImageIn B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨K'.1, hrad K'⟩⟩
    refine (Sheaf.sectionEquiv_comp J _ _).trans ?_
    refine (congrArg ((ρ ≫ completionToUpliftedSheaf X hX T).hom.app (op V))
      ((Sheaf.sectionEquiv J).apply_symm_apply _)).trans ?_
    exact (congrArg (fun φ => φ.app (op V) ((J.toSheafify C.toFunctor).app (op V) x)) hnat).trans
      (congrArg (fun φ => (Functor.whiskerRight g₀ uliftFunctor.{u + 1}).app (op V)
        (φ.app (op V) x)) hamb)
  refine Eq.trans ?_ (congrArg _ hsec.symm)
  refine congrArg ULift.up ?_
  refine (congrArg (fun f => X.map f.op s)
    (stageIsoSupportStage_hom_comp_supportStageToAffine D hRS q hq hrad K').symm).trans ?_
  exact X.map_comp_apply
    (supportStageToAffine B S hS hRS q (IsLocalRing.maximalIdeal R) ⟨K'.1, hrad K'⟩).op
    ((BigAffineFppf.inclusion B S hS).map (stageIsoSupportStage D hRS q hq hrad K').hom).op s

/-- **The converse of Stacks 0GBU is adic.** For `g : Spec R ⟶ X` with `g⁻¹(T) = {𝔪}`, the
morphism `AlgebraicGeometry.FormalSpace.adicOfAlgebraization` is representable by algebraic
spaces: up to the identification `Spf R ≅ (Spec R)_{/g⁻¹(T)}` it is the morphism of completions
induced by `g`, which is representable by algebraic spaces by **Stacks 0APV**. -/
theorem isRepresentableByAlgebraicSpacesULift_adicOfAlgebraization
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX)
    (hg : PreimageEqClosedPoint hR T hRS q
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g hg).hom := by
  let := hR.isLocal
  let := hR.isNoetherian
  let U := (BigAffineFppf.inclusion B S hS).obj (specOver hRS q)
  let g₀ : yoneda.obj U ⟶ X :=
    yonedaEquiv.symm (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down
  have hZ := zeroLocusPoints_maximalIdeal_eq hR T hRS q _ hg
  let e := formalSpectrumIsoCompletion D hRS q hq (radical_weakIdeal_eq hD₁ hD) hD ≪≫
    eqToIso (congrArg (Space.completionSheaf B S hS (yoneda.obj U)) hZ)
  have hP : adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g hg =
      e.hom ≫ Space.completionSheafMap B S hS g₀ T :=
    (congrArg (fun k => (formalSpectrumIsoCompletion D hRS q hq (radical_weakIdeal_eq hD₁ hD)
        hD).hom ≫ k)
      (Space.completionSheafRestrict_eq_eqToHom_comp B S hS g₀ _ T hZ.le hZ)).trans
      (Category.assoc _ _ _).symm
  rw [hP]
  refine Space.isRepresentableByAlgebraicSpacesULift_of_iso B S hS
    ((sheafToPresheaf _ _).mapIso e.symm) (Iso.refl _) ?_
    (Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
      (isAlgebraicSpace_yoneda B S hS U) hX g₀ T)
  show _ ≫ 𝟙 _ = e.inv.hom ≫ (e.hom ≫ Space.completionSheafMap B S hS g₀ T).hom
  rw [Category.comp_id]
  exact (congrArg (fun k => k.hom) (e.inv_hom_id_assoc (Space.completionSheafMap B S hS g₀ T))).symm

/-- Two morphisms into the completion `X_{/T}` agreeing after `X_{/T} ⟶ X` agree, because
`X_{/T} ⟶ X` is a monomorphism. -/
private theorem hom_ext_completionToUpliftedSheaf
    {F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) {P P' : F ⟶ Space.completionSheaf B S hS X T}
    (h : P ≫ completionToUpliftedSheaf X hX T = P' ≫ completionToUpliftedSheaf X hX T) :
    P = P' := by
  have := Space.mono_completionSheafToAmbient B S hS X (upliftedSheaf X hX).property T
  exact Sheaf.hom_ext ((cancel_mono
    (Space.completionSheafToAmbient B S hS X (upliftedSheaf X hX).property T)).1
      (congrArg (fun k => k.hom) h))

/-- **The converse half of Stacks 0GBU.** Let `g : Spec R ⟶ X` satisfy `g⁻¹(T) = {𝔪}`. Then the
restriction of `g` to `Spf R` factors through `X_{/T}` by a unique morphism
`p : Spf R ⟶ X_{/T}`, and `p` is adic, i.e. representable by algebraic spaces. -/
theorem existsUnique_adic_of_preimageEqClosedPoint
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX)
    (hg : PreimageEqClosedPoint hR T hRS q
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down) :
    ∃! P : formalSpectrum D ⟶ Space.completionSheaf B S hS X T,
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS P.hom ∧
        formalSpectrumToSpec D hRS q hq ≫ g = P ≫ completionToUpliftedSheaf X hX T := by
  refine ⟨adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g hg,
    ⟨isRepresentableByAlgebraicSpacesULift_adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g hg,
      formalSpectrumToSpec_comp_eq_adicOfAlgebraization_comp hR D hD₁ hD hRS q hq hX T g hg⟩,
    fun P hP => ?_⟩
  exact hom_ext_completionToUpliftedSheaf hX T (hP.2.symm.trans
    (formalSpectrumToSpec_comp_eq_adicOfAlgebraization_comp hR D hD₁ hD hRS q hq hX T g hg))

end Converse

/-! ### The bijection -/

section Bijection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two morphisms into the completion `X_{/T}` agreeing after `X_{/T} ⟶ X` agree, because
`X_{/T} ⟶ X` is a monomorphism. -/
theorem eq_of_comp_completionToUpliftedSheaf_eq
    {F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) {P P' : F ⟶ Space.completionSheaf B S hS X T}
    (h : P ≫ completionToUpliftedSheaf X hX T = P' ≫ completionToUpliftedSheaf X hX T) :
    P = P' := by
  exact hom_ext_completionToUpliftedSheaf hX T h

/-- The algebraization of an adic morphism `p : Spf R ⟶ X_{/T}`: the unique `g : Spec R ⟶ X`
with `g⁻¹(T) = {𝔪}` restricting on `Spf R` to `p` followed by `X_{/T} ⟶ X`, given by
`AlgebraicGeometry.FormalSpace.existsUnique_algebraization_of_adic_into_completion`. -/
def algebraizationOfAdic
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (hTqc : letI : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
      Space.IsQuasiCompact B S hS
        ((Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (P : formalSpectrum D ⟶ Space.completionSheaf B S hS X T)
    (hP : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS P.hom) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX :=
  (existsUnique_algebraization_of_adic_into_completion hR D hD₁ hD hRS q hq X hX T hT hTqc P
    hP).exists.choose

/-- The algebraization of an adic morphism restricts to it on `Spf R` and has fibre over `T`
the closed point. -/
theorem algebraizationOfAdic_spec
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (hTqc : letI : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
      Space.IsQuasiCompact B S hS
        ((Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (P : formalSpectrum D ⟶ Space.completionSheaf B S hS X T)
    (hP : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS P.hom) :
    formalSpectrumToSpec D hRS q hq ≫
        algebraizationOfAdic hR D hD₁ hD hRS q hq X hX T hT hTqc P hP =
      P ≫ completionToUpliftedSheaf X hX T ∧
    PreimageEqClosedPoint hR T hRS q (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (algebraizationOfAdic hR D hD₁ hD hRS q hq X hX T hT hTqc P hP)).down :=
  (existsUnique_algebraization_of_adic_into_completion hR D hD₁ hD hRS q hq X hX T hT hTqc P
    hP).exists.choose_spec

/-- **Stacks 0GBU.** Let `S` be a scheme, `X` an algebraic space over `S` and `T` a closed set of
points of `X` whose complementary open subspace has quasi-compact inclusion into `X`. Let `R` be
a Noetherian complete local `S`-algebra whose spectrum lies in the site, equipped with a
quotient system whose weak ideals of definition are cofinal among the powers of the maximal
ideal `𝔪`. Then the adic morphisms `p : Spf R ⟶ X_{/T}` correspond bijectively to the morphisms
`g : Spec R ⟶ X` with `g⁻¹(T) = {𝔪}`.

The bijection sends `p` to the unique `g` restricting on `Spf R` to `p` followed by
`X_{/T} ⟶ X` (`AlgebraicGeometry.FormalSpace.existsUnique_algebraization_of_adic_into_completion`),
and its inverse sends `g` to `AlgebraicGeometry.FormalSpace.adicOfAlgebraization`; the
correspondence is characterised by
`AlgebraicGeometry.FormalSpace.adicCompletionHomEquiv_apply_eq_iff`. -/
@[stacks 0GBU "The bijection between adic morphisms Spf R ⟶ X_{/T} and morphisms \
g : Spec R ⟶ X with g⁻¹(T) = {𝔪}."]
def adicCompletionHomEquiv
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (hTqc : letI : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
      Space.IsQuasiCompact B S hS
        ((Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) :
    { p : formalSpectrum D ⟶ Space.completionSheaf B S hS X T //
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom } ≃
      { g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX //
        PreimageEqClosedPoint hR T hRS q
          (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down } where
  toFun p := ⟨algebraizationOfAdic hR D hD₁ hD hRS q hq X hX T hT hTqc p.1 p.2,
    (algebraizationOfAdic_spec hR D hD₁ hD hRS q hq X hX T hT hTqc p.1 p.2).2⟩
  invFun g := ⟨adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g.1 g.2,
    isRepresentableByAlgebraicSpacesULift_adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g.1 g.2⟩
  left_inv p := Subtype.ext (eq_of_comp_completionToUpliftedSheaf_eq hX T
    ((formalSpectrumToSpec_comp_eq_adicOfAlgebraization_comp hR D hD₁ hD hRS q hq hX T
      (algebraizationOfAdic hR D hD₁ hD hRS q hq X hX T hT hTqc p.1 p.2)
      (algebraizationOfAdic_spec hR D hD₁ hD hRS q hq X hX T hT hTqc p.1 p.2).2).symm.trans
      (algebraizationOfAdic_spec hR D hD₁ hD hRS q hq X hX T hT hTqc p.1 p.2).1))
  right_inv g := Subtype.ext ((existsUnique_algebraization_of_adic_into_completion hR D hD₁ hD
      hRS q hq X hX T hT hTqc (adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g.1 g.2)
      (isRepresentableByAlgebraicSpacesULift_adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g.1
        g.2)).unique
    (algebraizationOfAdic_spec hR D hD₁ hD hRS q hq X hX T hT hTqc
      (adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g.1 g.2)
      (isRepresentableByAlgebraicSpacesULift_adicOfAlgebraization hR D hD₁ hD hRS q hq hX T g.1
        g.2))
    ⟨formalSpectrumToSpec_comp_eq_adicOfAlgebraization_comp hR D hD₁ hD hRS q hq hX T g.1 g.2,
      g.2⟩)

/-- The bijection of **Stacks 0GBU** sends an adic `p : Spf R ⟶ X_{/T}` to a morphism
`g : Spec R ⟶ X` restricting on `Spf R` to `p` followed by `X_{/T} ⟶ X`. -/
theorem formalSpectrumToSpec_comp_adicCompletionHomEquiv
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (hTqc : letI : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
      Space.IsQuasiCompact B S hS
        ((Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (p : { p : formalSpectrum D ⟶ Space.completionSheaf B S hS X T //
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom }) :
    formalSpectrumToSpec D hRS q hq ≫
        (adicCompletionHomEquiv hR D hD₁ hD hRS q hq X hX T hT hTqc p).1 =
      p.1 ≫ completionToUpliftedSheaf X hX T := by
  unfold adicCompletionHomEquiv
  exact (algebraizationOfAdic_spec hR D hD₁ hD hRS q hq X hX T hT hTqc p.1 p.2).1

/-- **Stacks 0GBU, the correspondence.** The bijection `adicCompletionHomEquiv` sends an adic
`p : Spf R ⟶ X_{/T}` to `g : Spec R ⟶ X` with `g⁻¹(T) = {𝔪}` exactly when `g` restricts on
`Spf R` to `p` followed by `X_{/T} ⟶ X`. -/
@[stacks 0GBU "The bijection is the correspondence: p ↦ g exactly when g restricts on Spf R \
to p followed by X_{/T} ⟶ X."]
theorem adicCompletionHomEquiv_apply_eq_iff
    {R : Type u} [CommRing R] [TopologicalSpace R]
    (hR : IsNoetherianCompleteLocalRing R)
    (D : QuotientSystem B S hS R)
    (hD₁ : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ n : ℕ, (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n ≤ J.1)
    (hD : ∀ n : ℕ, ∃ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      J.1 ≤ (@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)
    (hRS : B.Contains (Spec (.of R))) (q : Spec (.of R) ⟶ S)
    (hq : ∀ J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q = D.overS J)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (hTqc : letI : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
      Space.IsQuasiCompact B S hS
        ((Space.openSubspacesOrderIso B S hS X hX).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι)
    (p : { p : formalSpectrum D ⟶ Space.completionSheaf B S hS X T //
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom })
    (g : { g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (specOver hRS q)) ⟶ upliftedSheaf X hX //
        PreimageEqClosedPoint hR T hRS q
          (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g).down }) :
    adicCompletionHomEquiv hR D hD₁ hD hRS q hq X hX T hT hTqc p = g ↔
      formalSpectrumToSpec D hRS q hq ≫ g.1 = p.1 ≫ completionToUpliftedSheaf X hX T := by
  refine ⟨fun h => h ▸ formalSpectrumToSpec_comp_adicCompletionHomEquiv hR D hD₁ hD hRS q hq X
    hX T hT hTqc p, fun h => Subtype.ext ?_⟩
  exact (existsUnique_algebraization_of_adic_into_completion hR D hD₁ hD hRS q hq X hX T hT
    hTqc p.1 p.2).unique
    ⟨formalSpectrumToSpec_comp_adicCompletionHomEquiv hR D hD₁ hD hRS q hq X hX T hT hTqc p,
      (adicCompletionHomEquiv hR D hD₁ hD hRS q hq X hX T hT hTqc p).2⟩ ⟨h, g.2⟩

end Bijection

end AlgebraicGeometry.FormalSpace

end
