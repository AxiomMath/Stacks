module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward

/-!
# Part (3) of Stacks 04CJ: direct image as a functor on quasi-coherent modules

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝓘 = ker(i♯) ⊆ 𝒪_X` be the quasi-coherent ideal cutting out `Z`.
[Stacks, Tag 04CJ], part (3) says that the direct image

`i_* : QCoh(𝒪_Z) ⟶ QCoh(𝒪_X)`

is exact, is fully faithful, and has for essential image the quasi-coherent `𝒪_X`-modules
annihilated by `𝓘`.  This file proves all three, unconditionally, and packages the two inputs
that [Stacks, Tag 04CL] consumes.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDirectImageEquivalence`: **part (3) of Stacks 04CJ in the
  form Stacks 04CL consumes** — the direct image of a quasi-coherent module is quasi-coherent,
  and every quasi-coherent module annihilated by `𝓘` is the direct image of a quasi-coherent
  module.
* `AlgebraicGeometry.Space.quasicoherentDirectImageOfClosedImmersion`: the functor
  `i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` of part (3).
* `AlgebraicGeometry.Space.fullyFaithfulQuasicoherentDirectImage`: **part (3)**, the
  full-faithfulness clause.

## Main results

* `AlgebraicGeometry.Space.exactFunctor_quasicoherentDirectImage`: **part (3)**, the exactness
  clause.
* `AlgebraicGeometry.Space.essImage_quasicoherentDirectImage_iff`: **part (3)**, the
  essential-image clause.

## The proofs

The functor exists by the two preservation statements of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQuasicoherentPushforward.lean`, which are
the closed-immersion cases of Stacks 03M9 and Stacks 03GA.

*Exactness.*  The inclusion of the quasi-coherent modules into all modules is exact and reflects
isomorphisms (`AlgebraicGeometry.Space.preservesFiniteLimits_quasicoherentSheavesι` and its
colimit companion), so exactness is inherited from the direct image of all modules, which is
exact by `Space.exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity`.

*Full faithfulness.*  A lift along a full subcategory inclusion is fully faithful as soon as the
functor it lifts is, and that is
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward` (part (2)).

*Essential image.*  One inclusion is
`AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward`.  For the other, an
annihilated module `𝓕` has invertible unit by
`AlgebraicGeometry.Space.essImage_modulePushforward_iff`, so `𝓕 ≅ i_*i^*𝓕`, and `i^*𝓕` is
quasi-coherent by the closed-immersion case of Stacks 03GA.

## References

* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04CL](https://stacks.math.columbia.edu/tag/04CL)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **Part (3) of Stacks 04CJ in the form Stacks 04CL consumes.**  For a closed immersion
`i : Z ⟶ X` of algebraic spaces the direct image carries quasi-coherent `𝒪_Z`-modules to
quasi-coherent `𝒪_X`-modules, and every quasi-coherent `𝒪_X`-module annihilated by `𝓘 = ker(i♯)`
is the direct image of a quasi-coherent `𝒪_Z`-module.

The first clause is the closed-immersion case of Stacks 03M9,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion`.  For the
second, an annihilated `𝒪_X`-module is a direct image by the unconditional essential-image clause
`AlgebraicGeometry.Space.essImage_modulePushforward_iff`, so the unit `𝓕 ⟶ i_*i^*𝓕` is an
isomorphism, and the witness `i^*𝓕` is quasi-coherent by the closed-immersion case of
Stacks 03GA. -/
@[stacks 04CJ "part (3): quasi-coherence of the direct image, and quasi-coherence of the \
module whose direct image an annihilated quasi-coherent module is"]
theorem quasicoherentDirectImageEquivalence (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    QuasicoherentDirectImageEquivalence B S hS i where
  pushforward_isQuasicoherentOnSite F hF :=
    isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B S hS i hi F hF
  exists_pushforward_iso G hG hann := by
    have hiso : IsIso ((modulePullbackAdjunction B S hS i).unit.app G) :=
      (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi G).1
        ((essImage_modulePushforward_iff B S hS i hi G).2 hann)
    exact ⟨(modulePullback B S hS i).obj G,
      isQuasicoherentOnSite_modulePullback_of_isClosedImmersion B S hS i hi G hG,
      ⟨(asIso ((modulePullbackAdjunction B S hS i).unit.app G)).symm⟩⟩

/-- **The functor `i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` of Stacks 04CJ, part (3)**, for a closed
immersion `i : Z ⟶ X` of algebraic spaces.

This is `AlgebraicGeometry.Space.quasicoherentPushforwardOfEquivalence` with its hypothesis
discharged by `AlgebraicGeometry.Space.quasicoherentDirectImageEquivalence`; composing it with
the inclusion of the quasi-coherent modules gives back the direct image of all modules, so it is
the functor the source names and not another one of the same type. -/
@[stacks 04CJ "part (3): the induced functor on quasi-coherent modules"]
def quasicoherentDirectImageOfClosedImmersion (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2 ⥤ QuasicoherentSheaves.{u, u} B S hS X.1 X.2 :=
  quasicoherentPushforwardOfEquivalence B S hS i (quasicoherentDirectImageEquivalence B S hS i hi)

/-- Composing `AlgebraicGeometry.Space.quasicoherentDirectImageOfClosedImmersion` with the
inclusion of the
quasi-coherent modules is the direct image of all modules restricted to them.  This holds by
definition: the functor *is* that lift. -/
def quasicoherentDirectImageCompIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    quasicoherentDirectImageOfClosedImmersion B S hS i hi ⋙ quasicoherentSheavesι B S hS X ≅
      quasicoherentSheavesι B S hS Z ⋙ modulePushforward B S hS i :=
  Iso.refl _

/-- **Stacks 04CJ, part (3), the full-faithfulness clause.**  The direct image
`i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` along a closed immersion of algebraic spaces is fully faithful.

The direct image is fully faithful on all modules by
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward` (part (2)), and a lift along a full
subcategory inclusion inherits that. -/
@[stacks 04CJ "part (3): the direct image on quasi-coherent modules is fully faithful"]
def fullyFaithfulQuasicoherentDirectImage (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    (quasicoherentDirectImageOfClosedImmersion B S hS i hi).FullyFaithful :=
  fullyFaithfulQuasicoherentPushforward B S hS i hi
    (quasicoherentDirectImageEquivalence B S hS i hi)

/-- The direct image on quasi-coherent modules along a closed immersion is left exact: the
inclusion of the quasi-coherent modules preserves and reflects finite limits, and the direct
image of all modules is left exact with no hypothesis on `i`. -/
theorem preservesFiniteLimits_quasicoherentDirectImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    PreservesFiniteLimits (quasicoherentDirectImageOfClosedImmersion B S hS i hi) := by
  have : PreservesFiniteLimits
      (quasicoherentDirectImageOfClosedImmersion B S hS i hi ⋙ quasicoherentSheavesι B S hS X) :=
    preservesFiniteLimits_of_natIso (quasicoherentDirectImageCompIso B S hS i hi).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS X)

/-- The direct image on quasi-coherent modules along a closed immersion is right exact: the
inclusion of the quasi-coherent modules preserves and reflects finite colimits, and the direct
image of all modules is right exact by
`AlgebraicGeometry.Space.preservesFiniteColimits_modulePushforward_of_isClosedImmersion`. -/
theorem preservesFiniteColimits_quasicoherentDirectImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    PreservesFiniteColimits (quasicoherentDirectImageOfClosedImmersion B S hS i hi) := by
  have := preservesFiniteColimits_modulePushforward_of_isClosedImmersion B S hS i hi
  have : PreservesFiniteColimits
      (quasicoherentDirectImageOfClosedImmersion B S hS i hi ⋙ quasicoherentSheavesι B S hS X) :=
    preservesFiniteColimits_of_natIso (quasicoherentDirectImageCompIso B S hS i hi).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (quasicoherentSheavesι B S hS X)

/-- **Stacks 04CJ, part (3), the exactness clause.**  The direct image
`i_* : QCoh(𝒪_Z) ⥤ QCoh(𝒪_X)` along a closed immersion of algebraic spaces is an exact
functor. -/
@[stacks 04CJ "part (3): the direct image on quasi-coherent modules is exact"]
theorem exactFunctor_quasicoherentDirectImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    exactFunctor (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2)
      (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
      (quasicoherentDirectImageOfClosedImmersion B S hS i hi) :=
  ⟨preservesFiniteLimits_quasicoherentDirectImage B S hS i hi,
    preservesFiniteColimits_quasicoherentDirectImage B S hS i hi⟩

/-- **Stacks 04CJ, part (3), the essential-image clause.**  A quasi-coherent `𝒪_X`-module is the
direct image of a quasi-coherent `𝒪_Z`-module along the closed immersion `i` exactly when the
ideal `𝓘 = ker(i♯)` cutting out `Z` annihilates it.

The forward implication is
`AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward`, applied to the
underlying `𝒪_X`-module.  The converse is the second clause of
`AlgebraicGeometry.Space.quasicoherentDirectImageEquivalence`. -/
@[stacks 04CJ "part (3): the essential image is the quasi-coherent modules annihilated by the \
defining ideal"]
theorem essImage_quasicoherentDirectImage_iff (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (F : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) :
    (quasicoherentDirectImageOfClosedImmersion B S hS i hi).essImage F ↔
      AnnihilatedByKerIdeal B S hS i F.obj := by
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    exact annihilatedByKerIdeal_of_essImage_modulePushforward B S hS i
      ⟨G.obj, ⟨(quasicoherentSheavesι B S hS X).mapIso e⟩⟩
  · intro hann
    obtain ⟨M, hM, ⟨e⟩⟩ :=
      (quasicoherentDirectImageEquivalence B S hS i hi).exists_pushforward_iso F.obj
        F.property hann
    exact ⟨⟨M, hM⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

end AlgebraicGeometry.Space

end
