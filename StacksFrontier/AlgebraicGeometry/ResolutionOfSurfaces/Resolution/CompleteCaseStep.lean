module

public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.RegularLocus
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStepAlgebra
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStepCompletedStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStepDegree
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUpsAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularLocusFinite
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# The geometric step of the induction proving Tag 0BGN

The proof of [Stacks, Tag 0BGN] inducts on the degree of a complete local normal domain `A` of
dimension two over a regular complete local subring. In the inductive step one has a finite
injective map `B → A` of Noetherian complete local normal domains and a resolution of
singularities `Y ⟶ Spec B`, and one lets `X` be the normalization of `Y ×_{Spec B} Spec A` (in the
function field of `A`). Then `X ⟶ Spec A` is a normal modification with finitely many singular
points, each closed, and at each of them, with `y` the image in `Y`, the completed local ring
`𝒪_{X,x}^` is a normal domain of dimension two which is finite over the complete regular local
ring `𝒪_{Y,y}^` of dimension two, of degree at most `[A : B]`. This file proves exactly that.

## Main results

* `AlgebraicGeometry.exists_normal_modification_completedStalk_finite_of_isResolution`: the
  statement above.

## Implementation notes

`X` is `AlgebraicGeometry.CompleteCaseStep.liftToFibreProduct`'s normalization; its global
properties are in `CompleteCaseStepNormalization` and its degree over `Y` in
`CompleteCaseStepDegree`. At a point `x` of `X` over `y ∈ Y` choose an affine open `U ∋ y`; its
preimage `V` in `X` is affine and `Γ(X, V)` is a finite `Γ(Y, U)`-algebra of rank `[A : B]`. The
local rings `𝒪_{Y,y}` and `𝒪_{X,x}` are localizations of `Γ(Y, U)` and `Γ(X, V)`, so
`CompleteCaseStepAlgebra` applies, through [Stacks, Tag 07N9]. The `𝒪_{Y,y}^`-algebra structure on
`𝒪_{X,x}^` produced there is the one induced by the factor of [Stacks, Tag 07N9].

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
* [Stacks Project, Tag 07N9](https://stacks.math.columbia.edu/tag/07N9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

namespace CompleteCaseStep

variable {B A : Type u} [CommRing B] [CommRing A] [IsNoetherianRing B] [IsLocalRing B]
  [IsDomain B] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  [IsAdicComplete (maximalIdeal A) A] [Algebra B A] [Module.Finite B A] [FaithfulSMul B A]
  {Y : Scheme.{u}} [IsIntegral Y] {g : Y ⟶ Spec (.of B)}

/-- The point of the spectrum of the sections over an affine open corresponding to a point of
the open is the given prime, when the point is the image of that prime. -/
private theorem primeIdealOf_fromSpec {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V)
    (q : PrimeSpectrum Γ(Z, V)) (hq : hV.fromSpec q ∈ V) :
    hV.primeIdealOf ⟨hV.fromSpec q, hq⟩ = q :=
  hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec q, hq⟩)

/-- **The completed local ring of a finite morphism over the completed local ring below.** Let
`π : Z ⟶ W` be a finite morphism, `U` an affine open of `W` whose ring of sections is a
Noetherian domain, and `z` a point of `Z` over `U`, with image `w`. Suppose the completion of
`𝒪_{W,w}` is a domain, `𝒪_{W,w}` has dimension at most two, and the completion of `𝒪_{Z,z}` is a
domain of dimension two. Then `𝒪_{W,w}^` has dimension two and `𝒪_{Z,z}^` is a finite
`𝒪_{W,w}^`-algebra with injective structure map, of rank at most that of `Γ(Z, π⁻¹U)` over
`Γ(W, U)`. -/
theorem exists_algebra_adicCompletion_stalk_of_isFinite {Z W : Scheme.{u}} (π : Z ⟶ W)
    [IsFinite π] {U : W.Opens} (hU : IsAffineOpen U) [IsDomain Γ(W, U)]
    [IsNoetherianRing Γ(W, U)] (z : Z) (hz : π z ∈ U)
    [IsDomain (AdicCompletion (maximalIdeal (W.presheaf.stalk (π z))) (W.presheaf.stalk (π z)))]
    [IsDomain (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))]
    (hdimW : ringKrullDim (W.presheaf.stalk (π z)) ≤ 2)
    (hdimZ : ringKrullDim (AdicCompletion (maximalIdeal (Z.presheaf.stalk z))
      (Z.presheaf.stalk z)) = 2) :
    letI := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    ∃ _ : Algebra (AdicCompletion (maximalIdeal (W.presheaf.stalk (π z))) (W.presheaf.stalk (π z)))
        (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)),
      Module.Finite
          (AdicCompletion (maximalIdeal (W.presheaf.stalk (π z))) (W.presheaf.stalk (π z)))
          (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) ∧
        FaithfulSMul
          (AdicCompletion (maximalIdeal (W.presheaf.stalk (π z))) (W.presheaf.stalk (π z)))
          (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) ∧
        ringKrullDim
          (AdicCompletion (maximalIdeal (W.presheaf.stalk (π z))) (W.presheaf.stalk (π z))) = 2 ∧
        Module.finrank
            (AdicCompletion (maximalIdeal (W.presheaf.stalk (π z))) (W.presheaf.stalk (π z)))
            (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) ≤
          Module.finrank Γ(W, U) Γ(Z, π ⁻¹ᵁ U) := by
  let := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  have hzV : z ∈ π ⁻¹ᵁ U := hz
  have : Module.Finite Γ(W, U) Γ(Z, π ⁻¹ᵁ U) := by
    have h : (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.Finite := by
      rw [Scheme.Hom.appLE_eq_app]
      exact π.finite_app U hU
    exact h
  -- `z` is the image of a prime of `Γ(Z, π⁻¹U)`
  obtain ⟨q', hq'⟩ : ∃ q', hV.fromSpec q' = z := ⟨_, hV.fromSpec_primeIdealOf ⟨z, hzV⟩⟩
  subst hq'
  -- the local ring of `W` as a localization
  obtain ⟨p, hp⟩ : ∃ p, (hU.primeIdealOf ⟨π (hV.fromSpec q'), hz⟩).asIdeal = p := ⟨_, rfl⟩
  have : p.IsPrime := hp ▸ inferInstance
  let : Algebra Γ(W, U) (W.presheaf.stalk (π (hV.fromSpec q'))) :=
    W.presheaf.algebra_section_stalk ⟨_, hz⟩
  have : IsLocalization.AtPrime (W.presheaf.stalk (π (hV.fromSpec q'))) p := by
    subst hp
    exact hU.isLocalization_stalk ⟨_, hz⟩
  -- the point lies over its image
  have hlies : q'.asIdeal.LiesOver p := by
    refine ⟨?_⟩
    have h := congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE
      (f := π) (x := hV.fromSpec q') U hU (π ⁻¹ᵁ U) hV le_rfl hzV)
    rw [primeIdealOf_fromSpec hV q' hzV] at h
    rw [← hp, ← h]
    rfl
  -- the local rings of `Z` over the image as localizations
  have hmem (q : p.primesOver Γ(Z, π ⁻¹ᵁ U)) :
      hV.fromSpec ⟨q.1, Ideal.primesOver.isPrime p q⟩ ∈ π ⁻¹ᵁ U :=
    hV.range_fromSpec.subset ⟨_, rfl⟩
  let Sq : p.primesOver Γ(Z, π ⁻¹ᵁ U) → Type u := fun q =>
    Z.presheaf.stalk (hV.fromSpec ⟨q.1, Ideal.primesOver.isPrime p q⟩)
  let : ∀ q, Algebra Γ(Z, π ⁻¹ᵁ U) (Sq q) := fun q => Z.presheaf.algebra_section_stalk ⟨_, hmem q⟩
  have : ∀ q, IsLocalization.AtPrime (Sq q) q.1 := fun q =>
    hV.isLocalization_stalk' ⟨q.1, Ideal.primesOver.isPrime p q⟩ (hmem q)
  have : ∀ q, IsLocalRing (Sq q) := fun q => inferInstanceAs (IsLocalRing (Z.presheaf.stalk _))
  let q₀ : p.primesOver Γ(Z, π ⁻¹ᵁ U) := ⟨q'.asIdeal, q'.isPrime, hlies⟩
  have : IsDomain (AdicCompletion (maximalIdeal (Sq q₀)) (Sq q₀)) :=
    inferInstanceAs (IsDomain (AdicCompletion (maximalIdeal (Z.presheaf.stalk (hV.fromSpec q')))
      (Z.presheaf.stalk (hV.fromSpec q'))))
  exact exists_algebra_adicCompletion_finite_faithfulSMul_finrank_le p
    (W.presheaf.stalk (π (hV.fromSpec q'))) Sq q₀ hdimW hdimZ

omit [IsLocalRing B] in
/-- **The completed local rings of `X` over those of `Y`.** Let `x` be a point of `X` whose
completed local ring `𝒪_{X,x}^` is a domain of dimension two, and `y` its image in `Y`. Then
`𝒪_{Y,y}^` is a complete regular local ring of dimension two over which `𝒪_{X,x}^` is a finite
algebra with injective structure map, of rank at most `[A : B]`. -/
theorem exists_finite_adicCompletion_stalk (hg : IsResolution g) (x : _)
    (hdom : IsDomain (AdicCompletion (maximalIdeal
      ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x))
      ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x)))
    (hdim : ringKrullDim (AdicCompletion (maximalIdeal
      ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x))
      ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x)) = 2)
    (hdimA : ringKrullDim A = 2) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsRegularLocalRing R)
      (_ : IsAdicComplete (maximalIdeal R) R)
      (_ : Algebra R (AdicCompletion (maximalIdeal
        ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x))
        ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x))),
      Module.Finite R (AdicCompletion (maximalIdeal
        ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x))
        ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x)) ∧
      FaithfulSMul R (AdicCompletion (maximalIdeal
        ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x))
        ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x)) ∧
      ringKrullDim R = 2 ∧
      Module.finrank R (AdicCompletion (maximalIdeal
        ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x))
        ((liftToFibreProduct B A hg.1.1).normalization.presheaf.stalk x)) ≤
        Module.finrank B A := by
  have : IsProper g := hg.1.2.1
  have : IsFinite (toResolution B A hg.1.1) := isFinite_toResolution hg.1.1
  have : IsLocallyNoetherian (Spec (.of B)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  -- an affine open around the image of `x`
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (toResolution B A hg.1.1 x)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hyU⟩⟩
  have : Nonempty (toResolution B A hg.1.1 ⁻¹ᵁ U) := ⟨⟨x, hyU⟩⟩
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  -- the local ring of `Y` and its completion
  have : IsRegularLocalRing (Y.presheaf.stalk (toResolution B A hg.1.1 x)) :=
    IsRegular.isRegularLocalRing_stalk hg.2 _
  have hregR : IsRegularLocalRing (AdicCompletion (maximalIdeal
      (Y.presheaf.stalk (toResolution B A hg.1.1 x)))
      (Y.presheaf.stalk (toResolution B A hg.1.1 x))) :=
    isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp inferInstance
  have : IsDomain (AdicCompletion (maximalIdeal (Y.presheaf.stalk (toResolution B A hg.1.1 x)))
      (Y.presheaf.stalk (toResolution B A hg.1.1 x))) := IsRegularLocalRing.isDomain _
  -- the dimension of `𝒪_{Y,y}` is at most that of `Y`, which is two
  have hdimB : ringKrullDim B = 2 := by
    rw [← hdimA]
    exact Algebra.IsIntegral.ringKrullDim_eq B A
  have hdimY : ringKrullDim (Y.presheaf.stalk (toResolution B A hg.1.1 x)) ≤ 2 := by
    have h := topologicalKrullDim_eq_of_isModification_spec B g hg.1
    rw [hdimB, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk] at h
    exact h ▸ le_iSup (fun z : Y => ringKrullDim (Y.presheaf.stalk z)) _
  obtain ⟨alg, hfin, hfaith, hdimR, hrank⟩ :=
    exists_algebra_adicCompletion_stalk_of_isFinite (toResolution B A hg.1.1) hU x hyU hdimY hdim
  refine ⟨_, inferInstance, hregR, inferInstance, alg, hfin, hfaith, hdimR, hrank.trans ?_⟩
  exact (finrank_appLE_toResolution hg.1.1 hU (hU.preimage _)).le

end CompleteCaseStep

open CompleteCaseStep in
/-- **The geometric step of the induction of [Stacks, Tag 0BGN].** Let `B → A` be a finite
injective map of Noetherian complete local normal domains with `A` of dimension two, and let
`Y ⟶ Spec B` be a resolution of singularities. Then there is a normal modification
`X ⟶ Spec A` — the normalization of `Y ×_{Spec B} Spec A` — with finitely many singular points,
and at each singular point `x` the completion `𝒪_{X,x}^` of the local
ring is a normal domain of dimension two which is a finite algebra, with injective structure
map, over a complete regular local ring `R` of dimension two, of rank at most `[A : B]`. (The
ring `R` is the completion of the local ring of `Y` at the image of `x`; that the singular points
are closed is `AlgebraicGeometry.isClosed_singleton_of_mem_singularLocus`.) -/
theorem exists_normal_modification_completedStalk_finite_of_isResolution
    (B A : Type u) [CommRing B] [CommRing A] [IsNoetherianRing B] [IsLocalRing B]
    [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B] [IsNoetherianRing A] [IsLocalRing A]
    [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] (hdimA : ringKrullDim A = 2)
    [Algebra B A] [Module.Finite B A] [FaithfulSMul B A] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of B)) (hg : IsResolution g) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsNormal X ∧ IsModification f ∧
      (singularLocus X).Finite ∧
      ∀ x ∈ singularLocus X,
        IsNormalDomain (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)) ∧
        ringKrullDim (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)) = 2 ∧
        ∃ (R : Type u) (_ : CommRing R) (_ : IsRegularLocalRing R)
          (_ : IsAdicComplete (maximalIdeal R) R)
          (_ : Algebra R (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x))),
          Module.Finite R (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)) ∧
          FaithfulSMul R (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)) ∧
          ringKrullDim R = 2 ∧
          Module.finrank R (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)) ≤ Module.finrank B A := by
  have : IsIntegral Y := hg.1.2.2
  have : IsProper g := hg.1.2.1
  set X := (liftToFibreProduct B A hg.1.1).normalization
  set f := toBase B A hg.1.1
  have hnormal : IsNormal X := isNormal_normalization hg.1.1
  have hmod : IsModification f := isModification_toBase hg.1.1
  have : IsProper f := hmod.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have hdimX : topologicalKrullDim X = 2 := by
    rw [topologicalKrullDim_eq_of_isModification_spec A f hmod, hdimA]
  refine ⟨X, f, hnormal, hmod,
    finite_singularLocus_of_locallyOfFiniteType_over_completeLocalRing A f hdimX.le,
    fun x hx => ?_⟩
  have : IsDomain (X.presheaf.stalk x) := hnormal.stalk_isDomain x
  have : IsIntegrallyClosed (X.presheaf.stalk x) := hnormal.stalk_normal x
  have hnd : IsNormalDomain
      (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :=
    isNormalDomain_adicCompletion_stalk_of_locallyOfFiniteType A f x
      (IsNormalRing.of_isIntegrallyClosed _)
  have hdim : ringKrullDim
      (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) = 2 :=
    (_root_.ringKrullDim_adicCompletion_maximalIdeal (A := X.presheaf.stalk x)).symm.trans
      (ringKrullDim_stalk_eq_two_of_mem_singularLocus X hdimX.le x hx)
  obtain ⟨R, _, hR, hc, alg, hfin, hfaith, hdimR, hrank⟩ :=
    exists_finite_adicCompletion_stalk hg x hnd.isDomain hdim hdimA
  exact ⟨hnd, hdim, R, inferInstance, hR, hc, alg, hfin, hfaith, hdimR, hrank⟩

end AlgebraicGeometry

end
