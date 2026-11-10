module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherenceAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace

/-!
# Coherence of the higher direct images along a proper morphism of algebraic spaces

This file proves **Stacks 08AR**: for a proper morphism `f : X ⟶ Y` of algebraic spaces over `S`
with `Y` locally Noetherian and a coherent `𝒪_X`-module `𝓕`, every `R^i f_* 𝓕` is coherent.

The source's proof reduces to a Noetherian affine base and applies the dévissage of Stacks 08AN
on the source to the property that all higher direct images are coherent; that reduction and
the first two conditions of the dévissage are
`AlgebraicGeometry.Space.isCoherent_rightDerived_of_isProper_of_witness`.  This file supplies the
third condition: for `f' : X' ⟶ T` proper over a Noetherian affine scheme `T` and a reduced
closed subspace `Z ⊆ X'` with `|Z|` irreducible, a coherent module with scheme-theoretic support
`Z` and coherent higher direct images along `f'`.

## Main results

* `AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_of_isProper_of_isAffine`: the
  third condition of Stacks 08AN for that property.  The module is the Chow twist
  `𝒢 = q_* ((𝒪_{Z'} ⊗ ℒ^{⊗ d})^a)` of
  `AlgebraicGeometry.Space.exists_chowTwist_hasCoherentHigherDirectImages`, for a proper
  surjection `p : h_{Z'} ⟶ Z` from Chow's lemma and `q = p ≫ (Z ⟶ X')`.  Its scheme-theoretic
  support lies in `Z` because `𝒢` is a direct image from `Z` (Stacks 07U0, minimality), and
  contains `Z` because `Z` is reduced and its points lie in the support of `𝒢`
  (Stacks 07U0 part (4) and the reduced lifting criterion).
* `AlgebraicGeometry.Space.isCoherent_rightDerived_of_isProper`: Stacks 08AR.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The third condition of Stacks 08AN for coherence of the higher direct images.**  Let `T` be
a Noetherian affine scheme of the site and `f' : X' ⟶ h_T` a proper morphism.  For every reduced
closed subspace `Z ⊆ X'` with `|Z|` irreducible there is a coherent `𝒪_{X'}`-module with
scheme-theoretic support `Z` all of whose higher direct images along `f'` are coherent.

The module is the Chow twist `𝒢 = q_* 𝓜^a` of
`AlgebraicGeometry.Space.exists_chowTwist_hasCoherentHigherDirectImages`, where
`q = p ≫ (Z ⟶ X')` for a proper surjection `p : h_{Z'} ⟶ Z`.  As `𝒢` is the direct image of
`p_* 𝓜^a` along `Z ⟶ X'`, its scheme-theoretic support lies in `Z` (Stacks 07U0, minimality).
Conversely, the points of `Z` are the images of the points of `h_{Z'}`, which lie in the support
of `𝒢`; that support is the set of points of the scheme-theoretic support (Stacks 07U0
part (4)), so the inclusion of the reduced `Z` factors through the scheme-theoretic support. -/
theorem hasCoherentWitnessOnIntegralSubspaces_of_isProper_of_isAffine (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hTN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))
    (X' : AlgebraicSpaces B S hS)
    (f' : X' ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (hf' : IsProper B S hS f'.hom) :
    HasCoherentWitnessOnIntegralSubspaces B S hS X' (HasCoherentHigherDirectImages B S hS f') := by
  intro Z hZ hZri
  obtain ⟨Z', p, M, -, hps, -, -, -, hcoh, hdi, hsupp⟩ :=
    exists_chowTwist_hasCoherentHigherDirectImages B S hS T hT hTN X' f' hf' hZ
  let pZ : (⟨yoneda.obj Z', isAlgebraicSpace_yoneda B S hS Z'⟩ : AlgebraicSpaces B S hS) ⟶
      closedSubfunctorSpace B S hS hZ := ObjectProperty.homMk p
  let G := (modulePushforward B S hS (pZ ≫ closedSubfunctorι B S hS hZ)).obj
    ((representedAssociatedModule B S hS Z' (isAlgebraicSpace_yoneda B S hS Z')).obj M)
  have hcoh' : IsCoherent B S hS X'.1 X'.2 G := hcoh
  refine ⟨G, hcoh', le_antisymm ?_ ?_, hdi⟩
  · exact schemeTheoreticSupport_le B S hS X' G ⟨Z, hZ⟩
      ((modulePushforward B S hS pZ).obj
        ((representedAssociatedModule B S hS Z' (isAlgebraicSpace_yoneda B S hS Z')).obj M))
      ((modulePushforwardCompIso B S hS pZ (closedSubfunctorι B S hS hZ)).app _)
  · let := hcoh'
    obtain ⟨hZs, -⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X' G
      hcoh'.toIsQuasicoherentOnSite hcoh'.toIsCoherentOnSite.isFiniteType
    have hpts := supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X' G
      hcoh'.toIsQuasicoherentOnSite (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X' G)
    obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS X'.2 hZ.1
      _ hZs hZri.1 Z.ι).2 (by
        rw [← hpts]
        rintro _ ⟨z, rfl⟩
        obtain ⟨z', rfl⟩ := hps z
        refine hsupp ⟨z', ?_⟩
        change pointsMap B S hS _ (p ≫ Z.ι) z' = _
        rw [pointsMap_comp]
        rfl)
    exact Subfunctor.le_of_comp_eq_ι g hg

/-- **Stacks 08AR.**  Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y`
locally Noetherian, and let `𝓕` be a coherent `𝒪_X`-module.  Then `R^i f_* 𝓕` is a coherent
`𝒪_Y`-module for every `i ≥ 0`.

This is `AlgebraicGeometry.Space.isCoherent_rightDerived_of_isProper_of_witness` (the reduction to
a Noetherian affine base and the dévissage of Stacks 08AN on the source), with the integral
witness supplied by
`AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_of_isProper_of_isAffine`. -/
@[stacks 08AR]
theorem isCoherent_rightDerived_of_isProper {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived n).obj F) :=
  isCoherent_rightDerived_of_isProper_of_witness B S hS
    (hasCoherentWitnessOnIntegralSubspaces_of_isProper_of_isAffine B S hS) f hf hY F hF n

end AlgebraicGeometry.Space

end
