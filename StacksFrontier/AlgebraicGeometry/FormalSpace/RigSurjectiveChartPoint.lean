module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCompletionCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCompletionRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointlyRigSurjectiveComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.JointlyRigSurjectiveEtalePoint
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellationGeneral
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveClosedImmersionCharts
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverNoetherian
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition

/-!
# Lifting a discrete valuation point to an affine étale chart over a rig-surjection

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a rig-surjective
morphism from a locally Noetherian formal algebraic space `X`, and let `a : V ⟶ Y` be
representable by algebraic spaces and étale. Every adic morphism `y : Spf R ⟶ V` out of the
formal spectrum of a complete discrete valuation ring lifts, after an extension `R ⊂ R'` of
complete discrete valuation rings, to an affine formal algebraic space `Spf A` with `A`
Noetherian and adic, which comes with a representable étale chart `c : Spf A ⟶ X` and a map
`s : Spf A ⟶ V` forming a commutative square over `f` and `a`.

This is the step of the proof of Stacks 0GH6 which lifts `Spf R ⟶ V` to `X ×_Y V` and then, by
Stacks 0AQU, to a member `Spf A` of an affine étale covering of `X ×_Y V`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_chart_lift_of_isRigSurjective`: the statement
  above.

## Implementation notes

The source passes through `X ×_Y V`, whose being a formal algebraic space is Stacks 0AJ3. Here
the lift through `f` is followed instead by a lift through a member `Uᵢ` of the Noetherian atlas
of `X` (the composite family `{Uᵢ ⟶ X ⟶ Y}` is jointly rig-surjective, by Stacks 0AQU for the
atlas and `IsJointlyRigSurjective.comp_of_isRigSurjective`), and the affine étale covering is
taken of `V ×_Y Uᵢ`, which is representable étale over the affine `Uᵢ`, so that Stacks 0AN8 and
Stacks 04D1 cover it by formal spectra of completions of étale algebras
(`exists_completion_cover_of_isRepresentableEtale`). The members of that covering are
representable étale over `V ×_Y Uᵢ` by the cancellation lemma
`isRepresentableEtale_of_comp'`, which needs no knowledge of `V ×_Y Uᵢ` beyond the fact that it
is representable over `Uᵢ`, through the universe-lifted Stacks 05LA.

## References

* [Stacks Project, Tag 05LA](https://stacks.math.columbia.edu/tag/05LA)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0AQU](https://stacks.math.columbia.edu/tag/0AQU)
* [Stacks Project, Tag 0GH6](https://stacks.math.columbia.edu/tag/0GH6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A discrete valuation point of an étale sheaf over a Noetherian formal spectrum lifts to an
affine étale chart.** Let `A₀` be a Noetherian adic ring, let `φ : P ⟶ Spf A₀` be representable
by algebraic spaces and étale, and let `z : Spf R ⟶ P` be an adic morphism out of the formal
spectrum of a complete discrete valuation ring. Then there are a Noetherian adic ring `A` with
`Spf A` affine, a representable étale morphism `c : Spf A ⟶ P`, an extension `R ⊂ R'` of complete
discrete valuation rings and a morphism `ζ : Spf R' ⟶ Spf A` with `ζ ≫ c` the restriction of `z`
to `Spf R'`. -/
theorem exists_affine_chart_lift_of_isRepresentableEtale {A₀ : Type u} [CommRing A₀]
    [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] [IsNoetherianRing A₀]
    (hA₀ : TopologicalRing.IsAdic A₀) (D₀ : QuotientSystem B S hS A₀) {P : FppfSheaf B S hS}
    (φ : P ⟶ formalSpectrum D₀) (hφ : IsRepresentableEtale B S hS φ)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hRadic : _root_.IsAdic (IsLocalRing.maximalIdeal R))
    (hRcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (hR : TopologicalRing.IsWeaklyAdmissible R) (D : QuotientSystem B S hS R)
    (z : formalSpectrum D ⟶ P)
    (hz : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS z.hom) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (_ : IsNoetherianRing A), TopologicalRing.IsAdic A ∧
      ∃ (DA : QuotientSystem B S hS A) (c : formalSpectrum DA ⟶ P),
        IsAffineFormalAlgebraicSpace B S hS (formalSpectrum DA) ∧
        IsRepresentableEtale B S hS c ∧
        ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
          (_ : Algebra R R') (_ : IsDiscreteValuationRing.IsExtension R R')
          (_ : TopologicalSpace R') (_ : IsTopologicalRing R') (_ : IsLinearTopology R' R'),
          _root_.IsAdic (IsLocalRing.maximalIdeal R') ∧
            IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧
            ∃ (D' : QuotientSystem B S hS R') (e : ContinuousHom D D')
              (ζ : formalSpectrum D' ⟶ formalSpectrum DA),
              e.toRingHom = algebraMap R R' ∧ ζ ≫ c = formalSpectrumMap hR e ≫ z := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hA₀w : TopologicalRing.IsWeaklyAdmissible A₀ := Rig.weaklyAdmissible_of_isAdicRing hA₀
  obtain ⟨I₀, -, hI₀adic⟩ := hA₀.1
  have hD₀ : D₀.HasLargeSite := hasLargeSite_of_mk_lt_cutoff D₀
    (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hA₀ D₀)
  obtain ⟨K, C, _, fk, hfk, Q, g, hg, w, hw, hwsurj⟩ :=
    exists_completion_cover_of_isRepresentableEtale B S hS hA₀w
      (Ideal.fg_of_isNoetherianRing I₀) hI₀adic D₀ hD₀ φ hφ
  have hft : ∀ k, let : Algebra A₀ (C k) := (fk k).toAlgebra; Algebra.FiniteType A₀ (C k) :=
    fun k ↦ by
      let : Algebra A₀ (C k) := (fk k).toAlgebra
      have : Algebra.Etale A₀ (C k) := hfk k
      infer_instance
  have hQaff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (formalSpectrum (Q k)) := fun k ↦
    isAffineFormalAlgebraicSpace_formalSpectrum
      (TopologicalRing.completionOver_isWeaklyAdmissible (fk k) hA₀w) (Q k)
      (hasLargeSite_completionOver_of_finiteType B S hS (fk k) (hft k) hD₀ (Q k))
  have hwet : ∀ k, IsRepresentableEtale B S hS (w k) := fun k ↦
    isRepresentableEtale_of_comp' B S hS (w k) φ hφ (by
      rw [hw k]
      exact isRepresentableEtale_formalSpectrumMap_of_etale B S hS hA₀w D₀ hD₀ (fk k) (hfk k)
        (Q k) (g k) (hg k))
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, k, ζ, he, -, hζ⟩ :=
    isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective B S hS _ w
      (fun k ↦ isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hQaff k)) hwet
      (exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS w hwsurj)
      R hRadic hRcomplete hR D z hz
  have hCnoeth : IsNoetherianRing (C k) :=
    letI := (fk k).toAlgebra
    haveI := hft k
    Algebra.FiniteType.isNoetherianRing A₀ (C k)
  obtain ⟨hAadic, hAnoeth⟩ :=
    TopologicalRing.completionOver_isNoetherianAdic (fk k) ⟨hA₀, inferInstance⟩ hCnoeth
  exact ⟨TopologicalRing.CompletionOver (fk k), inferInstance, inferInstance, inferInstance,
    inferInstance, hAnoeth, hAadic, Q k, w k, hQaff k, hwet k, R', hR'ring, hR'dom, hR'dvr,
    hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic, hR'complete, D', e, ζ, he, hζ⟩

/-- **A discrete valuation point lifts to an affine étale chart over a rig-surjection.** Let
`f : X ⟶ Y` be rig-surjective with `X` a locally Noetherian formal algebraic space, let
`a : V ⟶ Y` be representable by algebraic spaces and étale, and let `y : Spf R ⟶ V` be an adic
morphism out of the formal spectrum of a complete discrete valuation ring. Then there are a
Noetherian adic topological ring `A` presented over `S`, a representable étale morphism
`c : Spf A ⟶ X` and a morphism `s : Spf A ⟶ V` with `c ≫ f = s ≫ a`, an extension `R ⊂ R'` of
complete discrete valuation rings and a morphism `ζ : Spf R' ⟶ Spf A` with `ζ ≫ s` the
restriction of `y` to `Spf R'`.

The point `y ≫ a` of `Y` lifts through `f` and then through a member `uᵢ : Uᵢ ⟶ X` of the
Noetherian atlas (the composite family being jointly rig-surjective), producing a point of
`V ×_Y Uᵢ`; the latter is covered by formal spectra of completions of étale algebras over the
presenting ring of `Uᵢ`, jointly rig-surjectively since each member is representable étale over
it, and the point lifts to one of them. -/
theorem exists_affine_chart_lift_of_isRigSurjective {X Y V : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hf : IsRigSurjective B S hS f)
    (a : V ⟶ Y) (ha : IsRepresentableEtale B S hS a)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hRadic : _root_.IsAdic (IsLocalRing.maximalIdeal R))
    (hRcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (hR : TopologicalRing.IsWeaklyAdmissible R) (D : QuotientSystem B S hS R)
    (y : formalSpectrum D ⟶ V)
    (hy : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS y.hom) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (_ : IsNoetherianRing A), TopologicalRing.IsAdic A ∧
      ∃ (DA : QuotientSystem B S hS A) (c : formalSpectrum DA ⟶ X) (s : formalSpectrum DA ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS (formalSpectrum DA) ∧
        IsRepresentableEtale B S hS c ∧ c ≫ f = s ≫ a ∧
        ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
          (_ : Algebra R R') (_ : IsDiscreteValuationRing.IsExtension R R')
          (_ : TopologicalSpace R') (_ : IsTopologicalRing R') (_ : IsLinearTopology R' R'),
          _root_.IsAdic (IsLocalRing.maximalIdeal R') ∧
            IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧
            ∃ (D' : QuotientSystem B S hS R') (e : ContinuousHom D D')
              (ζ : formalSpectrum D' ⟶ formalSpectrum DA),
              e.toRingHom = algebraMap R R' ∧ ζ ≫ s = formalSpectrumMap hR e ≫ y := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hXf, I, U, u, hUaff, hUet, hUsurj, hUnoeth⟩ := hX
  have hUrig : IsJointlyRigSurjective B S hS U (fun i ↦ u i ≫ f) :=
    IsJointlyRigSurjective.comp_of_isRigSurjective B S hS u f hXf
      (isJointlyRigSurjective_of_isRepresentableEtale_of_isJointlySurjective B S hS U u
        (fun i => isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hUaff i))
        hUet (exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS u hUsurj)) hf
  obtain ⟨R₂, _, _, _, _, _, _, _, _, hR₂adic, hR₂complete, D₂, e₂, i, x₂, he₂, hx₂rep, hx₂⟩ :=
    hUrig R hRadic hRcomplete hR D (y ≫ a)
      (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ hy ha.1)
  have hR₂w : TopologicalRing.IsWeaklyAdmissible R₂ :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hR₂adic hR₂complete
  obtain ⟨-, A₀, _, _, _, _, hA₀pres, _, hA₀adic⟩ := hUnoeth i
  let D₀ := hA₀pres.2.some.quotientSystem
  let eU : U i ≅ formalSpectrum D₀ := hA₀pres.2.some.formalSpectrumIso
  have hsnd := isRepresentableEtale_pullback_snd B S hS a (u i ≫ f) ha
  let z : formalSpectrum D₂ ⟶ pullback a (u i ≫ f) :=
    pullback.lift (formalSpectrumMap hR e₂ ≫ y) x₂ (by rw [hx₂, Category.assoc])
  have hzfst : z ≫ pullback.fst a (u i ≫ f) = formalSpectrumMap hR e₂ ≫ y :=
    pullback.lift_fst _ _ _
  have hzrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS z.hom := by
    have hzsnd : z ≫ pullback.snd a (u i ≫ f) = x₂ := pullback.lift_snd _ _ _
    refine Space.isRepresentableByAlgebraicSpacesULift_of_comp B S hS z.hom _
      (Space.isRepresentableByAlgebraicSpacesULift_pullback_diagonal _ hsnd.1) ?_
    change Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (z ≫ pullback.snd a (u i ≫ f)).hom
    rwa [hzsnd]
  obtain ⟨A, _, _, _, _, hAnoeth, hAadic, DA, c, hDA, hc, R₃, _, _, _, _,
    _, _, _, _, hR₃adic, hR₃complete, D₃, e₃, ζ, he₃, hζ⟩ :=
    exists_affine_chart_lift_of_isRepresentableEtale B S hS hA₀adic D₀
      (pullback.snd a (u i ≫ f) ≫ eU.hom)
      (IsRepresentableEtale.comp B S hS hsnd (isRepresentableEtale_of_isIso B S hS eU.hom))
      hR₂adic hR₂complete hR₂w D₂ z hzrep
  let : Algebra R R₃ := ((algebraMap R₂ R₃).comp (algebraMap R R₂)).toAlgebra
  have halg : (algebraMap R R₃ : R →+* R₃) = (algebraMap R₂ R₃).comp (algebraMap R R₂) :=
    RingHom.algebraMap_toAlgebra _
  let : IsScalarTower R R₂ R₃ := IsScalarTower.of_algebraMap_eq' halg
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, hAnoeth, hAadic, DA,
    c ≫ pullback.snd a (u i ≫ f) ≫ u i, c ≫ pullback.fst a (u i ≫ f), hDA,
    IsRepresentableEtale.comp B S hS hc (IsRepresentableEtale.comp B S hS hsnd (hUet i)), ?_,
    R₃, inferInstance, inferInstance, inferInstance, inferInstance,
    IsDiscreteValuationRing.IsExtension.trans R R₂ R₃, inferInstance, inferInstance,
    inferInstance, hR₃adic, hR₃complete, D₃, ContinuousHom.comp hR₂w hR e₃ e₂, ζ, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [pullback.condition]
  · rw [ContinuousHom.comp_toRingHom, he₃, he₂, halg]
  · rw [← Category.assoc, hζ, Category.assoc, hzfst, ← Category.assoc,
      formalSpectrumMap_comp_eq hR₂w hR e₃ e₂]

end AlgebraicGeometry.FormalSpace

end
