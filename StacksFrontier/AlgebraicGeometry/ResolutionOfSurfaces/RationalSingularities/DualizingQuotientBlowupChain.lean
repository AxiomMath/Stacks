module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.GorensteinOfDualizingQuotient
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.RationalStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageBlowUp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.RingTheory.Dualizing.DualizingRingModuleQuotient

/-!
# Dualizing quotients along a sequence of blowups in singular points

Let `A` be a local normal Nagata domain of dimension two defining a rational singularity, with a
dualizing module `ω_A`, and let `X_n ⟶ … ⟶ X_0 = Spec(A)` be a sequence of blowups in singular
closed points with normal stages. The proof of [Stacks, Tag 0BBV] shows by induction along the
sequence that the canonical maps `f_i^*ω_A ⟶ ω_{X_i}` are surjective on stalks, using
[Stacks, Tag 0B64] at each blowup. Read on local rings
(`AlgebraicGeometry.DualizingQuotientAt`): some dualizing module of `𝒪_{X_i, x}` is a quotient of
`𝒪_{X_i, x} ⊗_A ω_A`.

The induction runs pointwise. At the points of `Spec(A)` the module `A_𝔭 ⊗_A ω_A` is dualizing
([Stacks, Tag 0A7G]). Blowing up a closed point `w` of a stage `W` does not change the local
rings off `w`. A point `q` over `w` has the local ring of a point of the blowup of
`Spec 𝒪_{W, w}` in its maximal ideal ([Stacks, Tag 0805]); `𝒪_{W, w}` is again a local normal
Nagata domain of dimension two defining a rational singularity ([Stacks, Tag 0BG0]) which is not
regular, so the local step (the stalks of [Stacks, Tag 0B64] (3)) gives a dualizing quotient of
`𝒪_{X, q} ⊗_{𝒪_{W, w}} ω_w` for the dualizing module `ω_w` of `𝒪_{W, w}`, and quotients of base
changes compose.

## Main results

* `AlgebraicGeometry.dualizingQuotientAt_id`: the points of `Spec(A)`.
* `AlgebraicGeometry.dualizingQuotientAt_comp_of_isIso_stalkMap`: the points off the centre.
* `AlgebraicGeometry.dualizingQuotientAt_blowUpToBase_of_eq`: the points over the centre.
* `AlgebraicGeometry.SingularPointBlowupChain.stalk_situation`: the local ring at a singular
  point of a stage.
* `AlgebraicGeometry.dualizingQuotientAt_of_singularPointBlowupChain_of_local`: the induction,
  over the local step.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- `AlgebraicGeometry.stalkAlgebraOfSpec` of a composite is the stalk map composed with the
map to the stalk at the image point. -/
theorem stalkAlgebraOfSpec_comp (A : Type u) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ Spec (.of A)) (x : X) :
    stalkAlgebraOfSpec A (g ≫ h) x = (g.stalkMap x).hom.comp (stalkAlgebraOfSpec A h (g x)) := by
  rw [stalkAlgebraOfSpec, stalkAlgebraOfSpec, ← CommRingCat.hom_comp]
  congr 1
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  exact congrArg (fun k => (Scheme.ΓSpecIso (.of A)).inv ≫ h.appTop ≫ k)
    (Scheme.Hom.germ_stalkMap g ⊤ x trivial).symm

/-- `AlgebraicGeometry.stalkAlgebraOfSpec` at equal points. -/
theorem stalkCongr_comp_stalkAlgebraOfSpec (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) {x x' : X} (hx : x = x') :
    (X.presheaf.stalkCongr (.of_eq hx)).hom.hom.comp (stalkAlgebraOfSpec A f x) =
      stalkAlgebraOfSpec A f x' := by
  subst hx
  ext a
  simp

/-- At the points of `Spec(A)` itself, `AlgebraicGeometry.stalkAlgebraOfSpec` is the
localization map `A ⟶ A_𝔭`. -/
theorem stalkAlgebraOfSpec_id (A : Type u) [CommRing A] (x : Spec (.of A)) :
    stalkAlgebraOfSpec A (𝟙 _) x = (StructureSheaf.toStalk A x).hom :=
  rfl

/-- **Every point of `Spec(A)` carries a dualizing quotient**: `A_𝔭 ⊗_A ω_A` is a dualizing
module of `A_𝔭` ([Stacks, Tag 0A7G]). -/
theorem dualizingQuotientAt_id (A : Type u) [CommRing A] [IsNoetherianRing A] (ωA : Type u)
    [AddCommGroup ωA] [Module A ωA] (hωA : Stacks.Duality.IsDualizingRingModule A ωA)
    (x : Spec (.of A)) : DualizingQuotientAt A ωA (𝟙 _) x :=
  have := x.isPrime
  Dualizing.exists_isDualizingRingModule_quotient_of_isLocalization
    (stalkAlgebraOfSpec A (𝟙 _) x) x.asIdeal.primeCompl
    (StructureSheaf.IsLocalization.to_stalk A x) ωA hωA

/-- **The local ring at the centre of a stage.** Let `g : W ⟶ Spec(A)` be the composite of a
chain of blowups in singular closed points with normal stages, over a local normal Nagata domain
`A` of dimension two defining a rational singularity. Then the local ring of `W` at a singular
point is a local normal Nagata domain of dimension two defining a rational singularity
([Stacks, Tag 0BG0]), and that point is closed. -/
theorem SingularPointBlowupChain.stalk_situation (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsNormalDomain A] (hN : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hA : DefinesRationalSingularity A) {W : Scheme.{u}} {g : W ⟶ Spec (.of A)}
    (h : SingularPointBlowupChain IsNormal (Spec (.of A)) W g) (w : W)
    (hw : w ∈ singularLocus W) :
    ∃ (_ : IsLocallyNoetherian W) (_ : IsNormalDomain (W.presheaf.stalk w)),
      IsClosed ({w} : Set W) ∧ IsNagataRing (W.presheaf.stalk w) ∧
        ringKrullDim (W.presheaf.stalk w) = 2 ∧
        DefinesRationalSingularity (W.presheaf.stalk w) := by
  have : IsNormal (Spec (.of A)) := h.base
  have hNs : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A hN
  have hdimS : topologicalKrullDim (Spec (.of A)) = 2 := by
    change topologicalKrullDim (PrimeSpectrum A) = 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
  have hg : IsModification g :=
    isModification_of_singularPointBlowupChain (fun _ hW => hW) hNs hdimS h
  have : IsNormal W := h.last
  have : IsIntegral W := hg.source_isIntegral
  have : IsProper g := hg.isProper
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  have hdimW : topologicalKrullDim W = 2 := by
    rw [← hdimS]
    exact hg.isBirational.topologicalKrullDim_eq_of_isClosedMap g.isClosedMap
  have hw2 : ringKrullDim (W.presheaf.stalk w) = 2 :=
    ringKrullDim_stalk_eq_two_of_mem_singularLocus W hdimW.le w hw
  have hwc : IsClosed ({w} : Set W) := isClosed_singleton_of_mem_singularLocus W hdimW.le w hw
  have hwη : w ≠ genericPoint W := by
    rintro rfl
    exact absurd (hw2.symm.trans (ringKrullDim_eq_zero_of_field W.functionField)) (by decide)
  exact ⟨inferInstance, ⟨inferInstance, IsNormal.stalk_normal w⟩, hwc,
    isNagataRing_stalk_of_isNagataScheme (isNagataScheme_of_locallyOfFiniteType g hNs) w, hw2,
    definesRationalSingularity_stalk_of_isModification A hdim hA g hg w hwc hwη⟩

/-- **Dualizing quotients pass along isomorphisms of local rings.** If `g : X ⟶ Y` induces an
isomorphism `𝒪_{Y, g(x)} ≅ 𝒪_{X, x}` and some dualizing module of `𝒪_{Y, g(x)}` is a quotient of
`𝒪_{Y, g(x)} ⊗_A ω_A`, then some dualizing module of `𝒪_{X, x}` is a quotient of
`𝒪_{X, x} ⊗_A ω_A`. -/
theorem dualizingQuotientAt_comp_of_isIso_stalkMap (A : Type u) [CommRing A] (ωA : Type u)
    [AddCommGroup ωA] [Module A ωA] {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (g : X ⟶ Y) (f : Y ⟶ Spec (.of A)) (x : X)
    (hg : IsIso (g.stalkMap x)) (hQ : DualizingQuotientAt A ωA f (g x)) :
    DualizingQuotientAt A ωA (g ≫ f) x :=
  Dualizing.exists_isDualizingRingModule_quotient_trans _ (g.stalkMap x).hom _
    (stalkAlgebraOfSpec_comp A g f x).symm ωA hQ fun N _ _ hN =>
      Dualizing.exists_isDualizingRingModule_quotient_of_bijective _
        (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv.bijective N hN

/-- **Dualizing quotients over the centre of a blowup.** Let `w` be a closed point of a locally
Noetherian scheme `W ⟶ Spec(A)` at which some dualizing module of `𝒪_{W, w}` is a quotient of
`𝒪_{W, w} ⊗_A ω_A`. Suppose that for every dualizing module `ω` of `𝒪_{W, w}` every local ring of
the blowup of `Spec 𝒪_{W, w}` in its maximal ideal carries a dualizing quotient of its base change
of `ω`. Then so does the local ring of the blowup of `W` in `w` at every point `q` over `w`,
with respect to `ω_A`. -/
theorem dualizingQuotientAt_blowUpToBase_of_eq (A : Type u) [CommRing A] (ωA : Type u)
    [AddCommGroup ωA] [Module A ωA] {W : Scheme.{u}} [IsLocallyNoetherian W]
    (h : W ⟶ Spec (.of A)) (w : W) (hw : IsClosed ({w} : Set W))
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))]
    (hQ : DualizingQuotientAt A ωA h w)
    (hloc : ∀ (N : Type u) [AddCommGroup N] [Module (W.presheaf.stalk w) N],
      Stacks.Duality.IsDualizingRingModule (W.presheaf.stalk w) N →
        ∀ (_ : IsLocallyNoetherian (blowUp (maximalIdealSheaf (W.presheaf.stalk w))))
          (z : blowUp (maximalIdealSheaf (W.presheaf.stalk w))),
          DualizingQuotientAt (W.presheaf.stalk w) N
            (blowUpToBase (maximalIdealSheaf (W.presheaf.stalk w))) z)
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))
    (hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q = w) :
    DualizingQuotientAt A ωA
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ≫ h) q := by
  have hlnB : IsLocallyNoetherian (blowUp (maximalIdealSheaf (W.presheaf.stalk w))) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf _))
  obtain ⟨z, -, ε, hε⟩ :=
    exists_maximalIdealSheaf_point_of_blowUp _ w hw (RingEquiv.refl (W.presheaf.stalk w)) q hq
  let ψ : W.presheaf.stalk w →+* _ :=
    ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).stalkMap
      q).hom.comp (W.presheaf.stalkCongr (.of_eq hq.symm)).hom.hom
  have hψ : ψ.comp (stalkAlgebraOfSpec A h w) = stalkAlgebraOfSpec A
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ≫ h) q := by
    rw [stalkAlgebraOfSpec_comp, ← stalkCongr_comp_stalkAlgebraOfSpec A h hq.symm]
    rfl
  have hεψ : (ε.symm : _ →+* _).comp
      (stalkAlgebraOfSpec _ (blowUpToBase (maximalIdealSheaf (W.presheaf.stalk w))) z) = ψ := by
    ext a
    apply ε.injective
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    rw [show stalkAlgebraOfSpec _ (blowUpToBase (maximalIdealSheaf (W.presheaf.stalk w))) z =
      maximalIdealBlowUpStalkHom _ z from (maximalIdealBlowUpStalkHom_eq _ z).symm,
      ← hε a, eqRec_stalk_eq_stalkCongr]
    rfl
  refine Dualizing.exists_isDualizingRingModule_quotient_trans _ ψ _ hψ ωA hQ fun N _ _ hN => ?_
  exact Dualizing.exists_isDualizingRingModule_quotient_trans _ (ε.symm : _ →+* _) ψ hεψ N
    (hloc N hN hlnB z) fun P _ _ hP =>
      Dualizing.exists_isDualizingRingModule_quotient_of_bijective _ ε.symm.bijective P hP

/-- **Step (C2) of the proof of [Stacks, Tag 0BBV], over the local step.** Let `A` be a local
normal Nagata domain of dimension two defining a rational singularity, with a dualizing module
`ω_A`, and let `Y ⟶ Spec(A)` be a chain of blowups in singular closed points with normal stages.
Suppose that, for every local normal Nagata domain `R` of dimension two defining a rational
singularity which is not regular, and every dualizing module `ω` of `R`, every local ring of the
blowup of `Spec(R)` in its maximal ideal carries a dualizing quotient of its base change of `ω`
(the local step, [Stacks, Tag 0B64] (3) on stalks). Then every local ring `𝒪_{Y, y}` carries a
dualizing quotient of `𝒪_{Y, y} ⊗_A ω_A`. -/
theorem dualizingQuotientAt_of_singularPointBlowupChain_of_local (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A] (hN : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hA : DefinesRationalSingularity A) (ωA : Type u)
    [AddCommGroup ωA] [Module A ωA] (hωA : Stacks.Duality.IsDualizingRingModule A ωA)
    (hlocal : ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [IsNormalDomain R], IsNagataRing R → ringKrullDim R = 2 → DefinesRationalSingularity R →
        ¬ IsRegularLocalRing R → ∀ (N : Type u) [AddCommGroup N] [Module R N],
          Stacks.Duality.IsDualizingRingModule R N →
            ∀ (_ : IsLocallyNoetherian (blowUp (maximalIdealSheaf R)))
              (z : blowUp (maximalIdealSheaf R)),
              DualizingQuotientAt R N (blowUpToBase (maximalIdealSheaf R)) z)
    {Y : Scheme.{u}} {f : Y ⟶ Spec (.of A)}
    (h : SingularPointBlowupChain IsNormal (Spec (.of A)) Y f) [IsLocallyNoetherian Y] (y : Y) :
    DualizingQuotientAt A ωA f y := by
  revert y
  revert ‹IsLocallyNoetherian Y›
  induction h with
  | refl _ =>
    intro _ y
    exact dualizingQuotientAt_id A ωA hωA y
  | @step W g hh w hw hsing hP ih =>
    intro _ q
    obtain ⟨hlnW, hnorm, -, hNw, hdimw, hratw⟩ :=
      SingularPointBlowupChain.stalk_situation A hN hdim hA hh w hsing
    by_cases hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) q = w
    · exact dualizingQuotientAt_blowUpToBase_of_eq A ωA g w hw (ih w)
        (fun N _ _ hN' => hlocal _ hNw hdimw hratw hsing N hN') q hq
    · exact dualizingQuotientAt_comp_of_isIso_stalkMap A ωA _ g q
        (isIso_stalkMap_blowUpToBase_of_ne w hw q hq) (ih _)

end AlgebraicGeometry

end
