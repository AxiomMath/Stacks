module

public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.ManyVariableAlgebra
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SharpnessOfRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.RingTheory.Rig.RigSmooth
import all StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealOfDefinitionExample

/-!
# The chart-locality hypotheses of Stacks 0ANG are not satisfiable for rig-étaleness

The implication (3) ⟹ (1) of Stacks 0ANG is proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty` from the locality axiom
`AlgebraicGeometry.FormalSpace.ChartPropertyAscendsAlongAffineEtale`, and it is carried as the
hypothesis `AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryAffineEtaleDiagram` by the
base change results built on Stacks 0GBG. Both quantify over *all* affine formal algebraic
spaces, while the chart condition `AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap`
only constrains the presentations by rings of the class `C`; for a chart with no such
presentation it holds vacuously. This file shows that, for the class of Noetherian adic rings
and for rig-étaleness (`RingHom.IsRigEtaleArrow`), both hypotheses are **false**, over every
base over which the ring `k[x] × (k ⊕ k^(ℤ))` below is a scheme of the site.

## The counterexample

Let `k` be a field, `P = k[x]`, `M = k ⊕ k^(ℤ)` the trivial square-zero extension of `k` by an
infinite dimensional vector space (`ManyVariable.sqz`), which is not Noetherian, `R = P × M`,
and `K = k(x)` the fraction field of `P`; all four rings carry the discrete topology. Put
`V = Spf R`, `V' = Spf P`, `U = Spf K`, let `r : V' ⟶ V` be the formal spectrum of the
projection `R → P` and `t' : U ⟶ V'` that of `P → K`.

* `r` is representable étale: the projection is the localization of `R` at the idempotent
  `(1, 0)`, and for discrete rings the formal spectrum is the represented affine scheme.
* Every ring presenting `V` is isomorphic to `R` (Stacks 0AN0, in the form
  `AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_formalSpectrum_iso`), and `R`
  is not Noetherian; so the chart condition holds for `t = t' ≫ r` vacuously.
* `t'` is presented by `P → K`, which is not of finite type (Zariski's lemma: `k(x)` is not
  finite over `k`), hence not rig-étale.

So the square `𝟙 ≫ t = t' ≫ r` refutes the ascent axiom, and the morphism `t : U ⟶ V`, covered
by `{𝟙 : U ⟶ U}` with the factorization `U ⟶ V ⟶ V` through `t`, refutes the implication
(3) ⟹ (1): the diagram `U ⟶ U`, `V' ⟶ V` over `t` has the chart map `t'`.

The defect is in the hypotheses, not in Definition 0AQM: `AlgebraicGeometry.FormalSpace.IsRigEtale`
asks for rig-étaleness of every presentation by Noetherian adic rings, and for locally
Noetherian formal algebraic spaces every chart has one (Stacks 0AKY). The corrected locality
statements restrict the charts to those presented by Noetherian adic rings.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_sheafifiedYoneda_map`: the sheaf
  represented by an étale morphism of the site is representable étale.
* `AlgebraicGeometry.FormalSpace.continuousHomOfSpec`: a continuous ring map as a morphism of
  the quotient systems `AlgebraicGeometry.FormalSpace.quotientSystemOfSpec`.
* `AlgebraicGeometry.FormalSpace.isIso_formalSpectrumInclusion_bot` and
  `AlgebraicGeometry.FormalSpace.isRepresentableEtale_formalSpectrumMap_of_bot`: the formal
  spectrum of a ring in which `0` is a weak ideal of definition is the represented spectrum,
  and an étale map of such rings has a representable étale formal spectrum.
* `AlgebraicGeometry.FormalSpace.not_chartPropertyAscendsAlongAffineEtale_isRigEtaleArrow`:
  the ascent hypothesis `hasc` is false for rig-étaleness.
* `AlgebraicGeometry.FormalSpace.not_sourceCoverImpliesEveryAffineEtaleDiagram_isRigEtaleArrow`:
  the hypothesis `h31` is false for rig-étaleness.

## References

* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Represented étale morphisms -/

/-- The morphism of fppf sheaves represented by a morphism of the big fppf site whose underlying
morphism of schemes is étale is representable étale: its base change along a scheme-valued
point is represented by the base change of the morphism of the site. -/
theorem isRepresentableEtale_sheafifiedYoneda_map {W V : BigFppfOver B S hS} (φ : W ⟶ V)
    (hφ : Etale ((BigFppfOver.toScheme B S hS).map φ)) :
    IsRepresentableEtale B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map φ) := by
  let G := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let Y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have hrel := Space.relative_uliftYoneda_map.{u + 1} B S hS (@Etale.{u}) φ hφ
  have hiso : IsPullback (sheafifiedYonedaObjIso B S hS W).hom ((uliftYoneda.{u + 1}).map φ)
      (G.map (Y.map φ)) (sheafifiedYonedaObjIso B S hS V).hom :=
    IsPullback.of_horiz_isIso ⟨(sheafifiedYonedaObjIso_naturality B S hS φ).symm⟩
  have key : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ G.obj (Y.obj V)),
      ∃ (b : BigFppfOver B S hS) (snd : b ⟶ U)
        (fst : (uliftYoneda.{u + 1}).obj b ⟶ G.obj (Y.obj W)),
        IsPullback fst ((uliftYoneda.{u + 1}).map snd) (G.map (Y.map φ)) ξ ∧
          Etale ((BigFppfOver.toScheme B S hS).map snd) := by
    intro U ξ
    obtain ⟨b, snd, fst, hpb⟩ := hrel.1 (ξ ≫ (sheafifiedYonedaObjIso B S hS V).inv)
    refine ⟨b, snd, fst ≫ (sheafifiedYonedaObjIso B S hS W).hom, ?_, hrel.2 _ _ _ hpb⟩
    have h := hpb.paste_horiz hiso
    rwa [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  refine ⟨fun U ξ ↦ ?_, fun U ξ ↦ ?_⟩
  · obtain ⟨b, snd, fst, hpb, -⟩ := key U ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS hpb.flip.isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS b)
  · obtain ⟨b, snd, fst, hpb, hsnd⟩ := key U ξ
    have h := isEtaleULift_precomp_iso B S hS hpb.flip.isoPullback.symm _
      ((Space.isEtaleULift_uliftYoneda_map_iff B S hS snd).mpr hsnd)
    have heq : hpb.flip.isoPullback.symm.hom ≫ (uliftYoneda.{u + 1}).map snd =
        pullback.fst ξ (G.map (Y.map φ)) := by
      rw [Iso.symm_hom, Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst]
    rwa [heq] at h

/-! ### Formal spectra of discrete rings -/

section Discrete

variable {B S hS}

/-- A continuous ring map `A → C` is a continuous homomorphism over `S` between the quotient
systems of `A` and of `C`, the structure morphism of `Spec C` being the composite through
`Spec A`. -/
def continuousHomOfSpec {A C : Type u} [CommRing A] [TopologicalSpace A] [CommRing C]
    [TopologicalSpace C] (φ : A →+* C) (hφ : Continuous φ) (f : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C))) :
    ContinuousHom (quotientSystemOfSpec (hS := hS) hA f)
      (quotientSystemOfSpec (hS := hS) hC (Spec.map (CommRingCat.ofHom φ) ≫ f)) where
  toRingHom := φ
  continuous := hφ
  overS J K h := by
    change Spec.map _ ≫ Spec.map _ ≫ f = Spec.map _ ≫ Spec.map _ ≫ f
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The zero ideal of a discrete ring is a weak ideal of definition. -/
theorem isWeakIdealOfDefinition_bot_of_discreteTopology [DiscreteTopology A] :
    TopologicalRing.IsWeakIdealOfDefinition (⊥ : Ideal A) :=
  ⟨isOpen_discrete _, fun x hx ↦ by
    obtain rfl := Ideal.mem_bot.mp hx
    exact IsTopologicallyNilpotent.zero⟩

/-- The zero ideal of a discrete ring is an ideal of definition. -/
theorem isIdealOfDefinition_bot_of_discreteTopology [DiscreteTopology A] :
    TopologicalRing.IsIdealOfDefinition (⊥ : Ideal A) :=
  ⟨isOpen_discrete _, fun U hU ↦ ⟨1, by
    rw [pow_one]
    intro x hx
    obtain rfl := Ideal.mem_bot.mp hx
    exact mem_of_mem_nhds hU⟩⟩

/-- A discrete ring is adic in the sense of Stacks 07E8 (8). -/
theorem isAdic_of_discreteTopology [DiscreteTopology A] : TopologicalRing.IsAdic A :=
  ⟨⟨⊥, isIdealOfDefinition_bot_of_discreteTopology,
      TopologicalRing.isAdic_bot_of_discreteTopology A⟩,
    (TopologicalRing.isWeaklyAdmissible_discreteTopology A).2.2,
    (TopologicalRing.isWeaklyAdmissible_discreteTopology A).2.1⟩

/-- The zero ideal, as an index of the diagram of quotient stages, when it is a weak ideal of
definition. -/
abbrev botIndex (hbot : TopologicalRing.IsWeakIdealOfDefinition (⊥ : Ideal A)) :
    { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
  ⟨⊥, hbot⟩

/-- When the zero ideal is a weak ideal of definition, the formal spectrum is the spectrum: the
inclusion of the stage of the zero ideal is an isomorphism, that stage being terminal among
the stages. -/
theorem isIso_formalSpectrumInclusion_bot (D : QuotientSystem B S hS A)
    (hbot : TopologicalRing.IsWeakIdealOfDefinition (⊥ : Ideal A)) :
    IsIso (formalSpectrumInclusion D (OrderDual.toDual (botIndex hbot))) := by
  have ht : IsTerminal (OrderDual.toDual (botIndex hbot)) :=
    IsTerminal.ofUniqueHom
      (fun J ↦ homOfLE (show (⊥ : Ideal A) ≤ (OrderDual.ofDual J).1 from bot_le))
      (fun _ _ ↦ Subsingleton.elim _ _)
  exact isIso_ι_of_isTerminal ht _

/-- When the zero ideal is a weak ideal of definition, the inclusion of the stage of the zero
ideal into the formal spectrum, as an isomorphism. -/
def formalSpectrumIsoOfBot (D : QuotientSystem B S hS A)
    (hbot : TopologicalRing.IsWeakIdealOfDefinition (⊥ : Ideal A)) :
    (formalSpectrumDiagram D).obj (OrderDual.toDual (botIndex hbot)) ≅ formalSpectrum D :=
  @asIso _ _ _ _ (formalSpectrumInclusion D (OrderDual.toDual (botIndex hbot)))
    (isIso_formalSpectrumInclusion_bot D hbot)

/-- The forward morphism of `formalSpectrumIsoOfBot` is the inclusion of the stage of the zero
ideal into the formal spectrum. -/
theorem formalSpectrumIsoOfBot_hom (D : QuotientSystem B S hS A)
    (hbot : TopologicalRing.IsWeakIdealOfDefinition (⊥ : Ideal A)) :
    (formalSpectrumIsoOfBot D hbot).hom =
      formalSpectrumInclusion D (OrderDual.toDual (botIndex hbot)) :=
  rfl

/-- The formal spectrum of a discrete ring is an affine formal algebraic space, the topology
being the `0`-adic one. -/
theorem isAffineFormalAlgebraicSpace_formalSpectrum_of_discreteTopology [DiscreteTopology A]
    (D : QuotientSystem B S hS A) :
    IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
  WeakIdealOfDefinitionExample.isAffineFormalAlgebraicSpace_of_isAdic ⊥
    (TopologicalRing.isAdic_bot_of_discreteTopology A) D

omit [TopologicalSpace A] in
/-- An étale ring map is étale modulo the zero ideals. -/
theorem etale_quotientMap_bot {C : Type u} [CommRing C] (φ : A →+* C) (hφ : φ.Etale)
    (h : (⊥ : Ideal A) ≤ Ideal.comap φ ⊥) :
    (Ideal.quotientMap (⊥ : Ideal C) φ h).Etale := by
  let eA : A ≃+* A ⧸ (⊥ : Ideal A) := RingEquiv.ofBijective (Ideal.Quotient.mk ⊥)
    ⟨(RingHom.injective_iff_ker_eq_bot _).mpr Ideal.mk_ker, Ideal.Quotient.mk_surjective⟩
  have hmkC : Function.Bijective (Ideal.Quotient.mk (⊥ : Ideal C)) :=
    ⟨(RingHom.injective_iff_ker_eq_bot _).mpr Ideal.mk_ker, Ideal.Quotient.mk_surjective⟩
  have heq : Ideal.quotientMap (⊥ : Ideal C) φ h =
      ((Ideal.Quotient.mk (⊥ : Ideal C)).comp φ).comp eA.symm.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    change Ideal.quotientMap ⊥ φ h (Ideal.Quotient.mk ⊥ a) =
      Ideal.Quotient.mk ⊥ (φ (eA.symm (eA a)))
    rw [RingEquiv.symm_apply_apply, Ideal.quotientMap_mk]
  rw [heq]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective eA.symm.bijective)
    (RingHom.Etale.stableUnderComposition _ _ hφ (RingHom.Etale.of_bijective hmkC))

/-- An étale continuous homomorphism of topological rings in which the zero ideals are weak
ideals of definition has a representable étale formal spectrum: it is, up to the isomorphisms
of `AlgebraicGeometry.FormalSpace.isIso_formalSpectrumInclusion_bot`, the morphism represented
by the spectrum of the ring map. -/
theorem isRepresentableEtale_formalSpectrumMap_of_bot [IsTopologicalRing A]
    [IsLinearTopology A A] {C : Type u} [CommRing C] [TopologicalSpace C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} (g : ContinuousHom D E)
    (hbotA : TopologicalRing.IsWeakIdealOfDefinition (⊥ : Ideal A))
    (hbotC : TopologicalRing.IsWeakIdealOfDefinition (⊥ : Ideal C))
    (het : g.toRingHom.Etale) :
    IsRepresentableEtale B S hS (formalSpectrumMap hA g) := by
  have hle : (botIndex hbotA).1 ≤ Ideal.comap g.toRingHom (botIndex hbotC).1 := bot_le
  have heq : formalSpectrumMap hA g =
      (formalSpectrumIsoOfBot E hbotC).inv ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (g.stageMap (botIndex hbotA) (botIndex hbotC) hle)) ≫
        (formalSpectrumIsoOfBot D hbotA).hom := by
    rw [Iso.eq_inv_comp, formalSpectrumIsoOfBot_hom, formalSpectrumIsoOfBot_hom]
    exact formalSpectrumMap_spec hA g (botIndex hbotA) (botIndex hbotC) hle
  rw [heq]
  refine IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isIso B S hS _)
    (IsRepresentableEtale.comp B S hS (isRepresentableEtale_sheafifiedYoneda_map B S hS _ ?_)
      (@isRepresentableEtale_of_isIso B S hS _ _ _ (Iso.isIso_hom _)))
  change Etale (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ⊥ g.toRingHom hle)))
  exact HasRingHomProperty.Spec_iff.mpr (etale_quotientMap_bot g.toRingHom het hle)

end Discrete

/-! ### The example -/

namespace ChartLocalityCounterexample

variable (k : Type u) [Field k]

/-- The discrete topology on `k[x]`. -/
@[instance_reducible] def polyTop : TopologicalSpace (Polynomial k) := ⊥

/-- The discrete topology on `k(x)`. -/
@[instance_reducible] def fracTop : TopologicalSpace (FractionRing (Polynomial k)) := ⊥

/-- The discrete topology on `k[x] × (k ⊕ k^(ℤ))`. -/
@[instance_reducible] def prodTop :
    TopologicalSpace (Polynomial k × ManyVariable.sqz k) := ⊥

attribute [local instance] polyTop fracTop prodTop

/-- The topology `polyTop` on `k[x]` is the discrete topology. -/
theorem discreteTopology_poly : DiscreteTopology (Polynomial k) := ⟨rfl⟩

/-- The topology `fracTop` on `k(x)` is the discrete topology. -/
theorem discreteTopology_frac : DiscreteTopology (FractionRing (Polynomial k)) := ⟨rfl⟩

/-- The topology `prodTop` on `k[x] × (k ⊕ k^(ℤ))` is the discrete topology. -/
theorem discreteTopology_prod : DiscreteTopology (Polynomial k × ManyVariable.sqz k) := ⟨rfl⟩

attribute [local instance] discreteTopology_poly discreteTopology_frac discreteTopology_prod

/-- **`k[x] → k(x)` is not rig-étale** for the discrete topologies: modulo the ideal of
definition `0` it would be of finite type, and `k(x)` is not of finite type over `k[x]`, since
by Zariski's lemma it would then be finite over `k`, making `x` algebraic. -/
theorem not_isRigEtaleArrow_algebraMap :
    ¬ RingHom.IsRigEtaleArrow (algebraMap (Polynomial k) (FractionRing (Polynomial k))) := by
  intro h
  obtain ⟨-, hft, -⟩ := h
  let φ := algebraMap (Polynomial k) (FractionRing (Polynomial k))
  have hq : (Ideal.quotientMap ((⊥ : Ideal (Polynomial k)).map φ) φ
      (Ideal.map_le_iff_le_comap.mp le_rfl)).FiniteType :=
    (hft ⊥ isIdealOfDefinition_bot_of_discreteTopology).2.2
  let e : FractionRing (Polynomial k) ⧸ (⊥ : Ideal (Polynomial k)).map φ ≃+*
      FractionRing (Polynomial k) :=
    (Ideal.quotEquivOfEq Ideal.map_bot).trans (RingEquiv.quotientBot _)
  have hφ : φ = e.toRingHom.comp ((Ideal.quotientMap ((⊥ : Ideal (Polynomial k)).map φ) φ
      (Ideal.map_le_iff_le_comap.mp le_rfl)).comp (Ideal.Quotient.mk ⊥)) := by
    refine RingHom.ext fun x ↦ ?_
    simp [e, Ideal.quotientMap_mk, Ideal.quotEquivOfEq_mk, RingEquiv.quotientBot_mk]
  have hφft : φ.FiniteType := by
    rw [hφ]
    exact (RingHom.FiniteType.of_surjective _ e.surjective).comp
      (hq.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective))
  have : Algebra.FiniteType (Polynomial k) (FractionRing (Polynomial k)) :=
    RingHom.finiteType_algebraMap.mp hφft
  have : Algebra.FiniteType k (FractionRing (Polynomial k)) :=
    Algebra.FiniteType.trans (S := Polynomial k) inferInstance this
  have : Module.Finite k (FractionRing (Polynomial k)) :=
    finite_of_finite_type_of_isJacobsonRing k (FractionRing (Polynomial k))
  have hint : _root_.IsIntegral k (algebraMap (Polynomial k) (FractionRing (Polynomial k))
      Polynomial.X) := Algebra.IsIntegral.isIntegral _
  exact ((transcendental_algebraMap_iff (IsFractionRing.injective (Polynomial k)
    (FractionRing (Polynomial k)))).mpr (Polynomial.transcendental_X k)) hint.isAlgebraic

variable {k}

/-- The counterexample data: affine formal algebraic spaces `U`, `V`, `V'`, a representable
étale `r : V' ⟶ V` and `t' : U ⟶ V'`, such that the chart condition for Noetherian adic rings
and rig-étaleness holds for `t' ≫ r` (vacuously, `V` having no Noetherian adic presentation)
and fails for `t'`. -/
theorem exists_vacuous_rigEtaleArrow_chart (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (f : Spec (.of (Polynomial k × ManyVariable.sqz k)) ⟶ S)
    (hR : B.Contains (Spec (.of (Polynomial k × ManyVariable.sqz k)))) :
    ∃ (U V V' : FppfSheaf B S hS) (t' : U ⟶ V') (r : V' ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U ∧ IsAffineFormalAlgebraicSpace B S hS V ∧
        IsAffineFormalAlgebraicSpace B S hS V' ∧ IsRepresentableEtale B S hS r ∧
        HasPropertyOnAffineChartMap B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
          (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
            [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
            RingHom.IsRigEtaleArrow φ) (t' ≫ r) ∧
        ¬ HasPropertyOnAffineChartMap B S hS
          (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
          (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
            [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
            RingHom.IsRigEtaleArrow φ) t' := by
  classical
  let fst := RingHom.fst (Polynomial k) (ManyVariable.sqz k)
  let ι := algebraMap (Polynomial k) (FractionRing (Polynomial k))
  have hP : B.Contains (Spec (.of (Polynomial k))) := by
    have : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom fst)) :=
      AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Prod.fst_surjective
    exact Scheme.size_lt_of_isClosedImmersion (Spec.map (CommRingCat.ofHom fst)) hR
  have hK : B.Contains (Spec (.of (FractionRing (Polynomial k)))) := by
    have : Epi (CommRingCat.ofHom ι) := IsLocalization.epi (nonZeroDivisors _) _
    have : Mono (Spec.map (CommRingCat.ofHom ι)) := by
      change Mono (Scheme.Spec.map (CommRingCat.ofHom ι).op)
      exact Functor.map_mono Scheme.Spec _
    exact Scheme.size_lt_of_mono_quasiCompact (Spec.map (CommRingCat.ofHom ι)) hP
  let fP := Spec.map (CommRingCat.ofHom fst) ≫ f
  let DR := quotientSystemOfSpec (hS := hS) hR f
  let DP := quotientSystemOfSpec (hS := hS) hP fP
  let DK := quotientSystemOfSpec (hS := hS) hK (Spec.map (CommRingCat.ofHom ι) ≫ fP)
  let gr : ContinuousHom DR DP :=
    continuousHomOfSpec fst continuous_of_discreteTopology f hR hP
  let gK : ContinuousHom DP DK :=
    continuousHomOfSpec ι continuous_of_discreteTopology fP hP hK
  have hRw := TopologicalRing.isWeaklyAdmissible_discreteTopology
    (Polynomial k × ManyVariable.sqz k)
  have hPw := TopologicalRing.isWeaklyAdmissible_discreteTopology (Polynomial k)
  have hfst : fst.Etale := by
    let : Algebra (Polynomial k × ManyVariable.sqz k) (Polynomial k) := fst.toAlgebra
    exact (inferInstance : Algebra.Etale (Polynomial k × ManyVariable.sqz k) (Polynomial k))
  refine ⟨formalSpectrum DK, formalSpectrum DR, formalSpectrum DP, formalSpectrumMap hPw gK,
    formalSpectrumMap hRw gr,
    isAffineFormalAlgebraicSpace_formalSpectrum_of_discreteTopology DK,
    isAffineFormalAlgebraicSpace_formalSpectrum_of_discreteTopology DR,
    isAffineFormalAlgebraicSpace_formalSpectrum_of_discreteTopology DP,
    isRepresentableEtale_formalSpectrumMap_of_bot hRw gr
      isWeakIdealOfDefinition_bot_of_discreteTopology
      isWeakIdealOfDefinition_bot_of_discreteTopology hfst, ?_, ?_⟩
  · -- every presentation of `V = Spf R` is by a ring isomorphic to `R`, which is not Noetherian
    intro A C _ _ _ _ _ _ _ _ hCA _ hA D E eU eV g hg
    exfalso
    obtain ⟨-, -, φ, -⟩ := exists_continuous_ringEquiv_of_formalSpectrum_iso hA hRw eV
    have := hCA.2
    have : IsNoetherianRing (Polynomial k × ManyVariable.sqz k) :=
      isNoetherianRing_of_ringEquiv A φ
    exact ManyVariable.not_isNoetherianRing_sqz k
      (isNoetherianRing_of_surjective (Polynomial k × ManyVariable.sqz k) (ManyVariable.sqz k)
        (RingHom.snd (Polynomial k) (ManyVariable.sqz k)) fun m ↦ ⟨(0, m), rfl⟩)
  · exact fun h ↦ not_isRigEtaleArrow_algebraMap k
      (h (Polynomial k) (FractionRing (Polynomial k))
        ⟨isAdic_of_discreteTopology, inferInstance⟩ ⟨isAdic_of_discreteTopology, inferInstance⟩
        hPw DP DK (Iso.refl _) (Iso.refl _) gK (by simp))

end ChartLocalityCounterexample

open ChartLocalityCounterexample in
/-- **The ascent hypothesis of Stacks 0ANG is false for rig-étaleness.** For the class of
Noetherian adic rings and the property `RingHom.IsRigEtaleArrow`,
`AlgebraicGeometry.FormalSpace.ChartPropertyAscendsAlongAffineEtale` fails over every base `S`
over which `Spec (k[x] × (k ⊕ k^(ℤ)))` is a scheme of the site, `k` a field: the chart
condition holds vacuously on a chart without Noetherian adic presentation, and does not ascend
to a representable étale chart which has one. -/
theorem not_chartPropertyAscendsAlongAffineEtale_isRigEtaleArrow (k : Type u) [Field k]
    (f : Spec (.of (Polynomial k × ManyVariable.sqz k)) ⟶ S)
    (hR : B.Contains (Spec (.of (Polynomial k × ManyVariable.sqz k)))) :
    ¬ ChartPropertyAscendsAlongAffineEtale B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ) := by
  intro h
  obtain ⟨U, V, V', t', r, hU, hV, hV', hr, hvac, hfail⟩ :=
    exists_vacuous_rigEtaleArrow_chart B S hS f hR
  exact hfail (h (t' ≫ r) t' (𝟙 U) r hU hV hU hV' (isRepresentableEtale_of_isIso B S hS _) hr
    (Category.id_comp _) hvac)

open ChartLocalityCounterexample in
/-- **The implication (3) ⟹ (1) of Stacks 0ANG, as quantified by
`AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryAffineEtaleDiagram`, is false for
rig-étaleness.** Over every base `S` over which `Spec (k[x] × (k ⊕ k^(ℤ)))` is a scheme of the
site, `k` a field, there is a morphism of affine formal algebraic spaces with the chart
condition on an affine étale covering of its source (vacuously, through a target without
Noetherian adic presentation) but not on every affine étale diagram. So the hypothesis `h31`
of the base change results for rig-étaleness can never be supplied. -/
theorem not_sourceCoverImpliesEveryAffineEtaleDiagram_isRigEtaleArrow (k : Type u) [Field k]
    (f : Spec (.of (Polynomial k × ManyVariable.sqz k)) ⟶ S)
    (hR : B.Contains (Spec (.of (Polynomial k × ManyVariable.sqz k)))) :
    ¬ SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ) := by
  intro h
  obtain ⟨U, V, V', t', r, hU, hV, hV', hr, hvac, hfail⟩ :=
    exists_vacuous_rigEtaleArrow_chart B S hS f hR
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hsurj : Sheaf.IsLocallySurjective (Sigma.desc (fun _ : PUnit.{u + 2} ↦ 𝟙 U)) :=
    (Sheaf.isLocallySurjective_iff_epi _).mpr
      (epi_of_epi_fac (Sigma.ι_comp_desc (fun _ : PUnit.{u + 2} ↦ 𝟙 U) PUnit.unit))
  have hcov : HasPropertyAfterSourceCover B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ) (t' ≫ r) :=
    ⟨PUnit.{u + 2}, fun _ ↦ U, fun _ ↦ 𝟙 U,
      ⟨fun _ ↦ hU, fun _ ↦ isRepresentableEtale_of_isIso B S hS _, hsurj⟩,
      fun _ ↦ ⟨V, 𝟙 V, t' ≫ r, hV, isRepresentableEtale_of_isIso B S hS _, by simp, hvac⟩⟩
  exact hfail (h (t' ≫ r) hcov U V' (𝟙 U) r t' hU hV'
    (isRepresentableEtale_of_isIso B S hS _) hr (Category.id_comp _))

end AlgebraicGeometry.FormalSpace

end
