module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareMap
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of two immersions

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be immersions of schemes fitting into a commutative triangle
`i ≫ p = j` over a morphism `p : X ⟶ Y`. [Stacks, Tag 067L] asserts that there is a canonical
exact sequence of `𝒪_Z`-modules

`𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0`,

whose first arrow is the canonical map of [Stacks, Tag 01R4] and whose second arrow is the
conormal differential of [Stacks, Tag 01UZ].

This file constructs the first arrow and characterizes it.

## Main definitions

* `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap`: the canonical map
  `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` attached to the triangle.

## Main results

* `Stacks.ConormalSequenceTwoImmersions.isInducedConormalSheafMap_conormalTransitivityMap`:
  over a compatible pair of affine opens the map carries the class of a section `a` of the
  ideal cutting out `Z` in `Y` to the class of its image `p^♯ a` in the ideal cutting out `Z`
  in `X`.
* `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap_unique`: that affine formula
  determines the map, so it is canonical.

## Construction

A triangle `i ≫ p = j` is the commutative square whose vertical morphisms are `i` and `j`,
whose top morphism is the identity of `Z` and whose bottom morphism is `p`. The canonical map
of [Stacks, Tag 01R4] for that square is a morphism `(𝟙 Z)^* 𝒞_{Z/Y} ⟶ 𝒞_{Z/X}`, and pullback
along an identity is the identity functor, so transporting along that isomorphism gives a
morphism `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` with no further choices. The transport is performed once, by
`Stacks.ConormalSequenceTwoImmersions.pullbackIdIso`, so that the two arrows of the composite
agree on the spelling of their common object.

## The rest of the tag

[Stacks, Tag 067L] makes three further assertions, all of which refer to the second arrow of
the sequence. None of them is proved in this file; all three are proved elsewhere in this
repository, in modules that import this one.

* **The second arrow.** The conormal differential `𝒞_{Z/X} ⟶ i^*Ω_{X/Y}`, which is also the
  first arrow of the conormal sequence of the single immersion `i` and the assertion of
  [Stacks, Tag 01UZ], is `Stacks.ConormalSequenceRight.conormalDifferential` of
  `StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic`. It is built on the pullback of a
  *sectionwise* kernel, where the first arrow above is built on the pullback of the
  *categorical* kernel; `Stacks.ConormalSequenceTwoImmersions.conormalDifferentialModules` is
  that differential read through the identification of the two presentations, which is the
  spelling in which the two arrows compose.
* **The vanishing of the composite and exactness at `𝒞_{Z/X}`** are
  `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMapModules_comp_eq_zero`
  and `Stacks.ConormalSequenceTwoImmersions.conormalShortComplexModules_exact` of
  `StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence`, where they
  are also the engine of the clauses of [Stacks, Tag 067V]. Neither assumes anything of `p`.
* **Surjectivity of the second arrow** is
  `Stacks.ConormalSequenceTwoImmersions.epi_conormalDifferential` of
  `StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalExact`. The
  right-hand end of the sequence of a single immersion is a different assertion, and is
  `Stacks.ConormalSequenceRight.differentialsMapOver_epi`.

The commutative-algebra counterpart of the full statement — exactness of
`I/I² ⟶ J/J² ⟶ Ω_{B/A} ⊗_B B/J ⟶ 0` for ring maps `A → B → C` with `A → C` surjective — is
`NaiveCotangent.Conormal.exact_mapCotangent_kerCotangentToTensor_and_surjective`, and it is what
the stalkwise proof of exactness at `𝒞_{Z/X}` is an instance of.

## References

* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 065V](https://stacks.math.columbia.edu/tag/065V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.ConormalSequenceTwoImmersions

/-- Pullback of sheaves of modules along the identity of a scheme is the identity functor.

This is `RingedSpaceModuleAdjunction.modulePullbackId`, stated at the morphism of
ringed spaces underlying `𝟙 W`, which is the form in which the conormal sheaf of an immersion
presents its pullbacks. -/
def pullbackIdIso (W : Scheme.{u}) :
    modulePullback (Scheme.Hom.toLRSHom (𝟙 W)).toShHom ≅
      𝟭 (SheafOfModules.{u} (structureSheafRing W.toLocallyRingedSpace.toRingedSpace)) :=
  RingedSpaceModuleAdjunction.modulePullbackId W.toLocallyRingedSpace.toRingedSpace

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [IsImmersion i] [IsImmersion j]

/-- **[Stacks, Tag 067L], the first arrow.** For immersions `i : Z ⟶ X` and `j : Z ⟶ Y` in a
commutative triangle `i ≫ p = j`, the canonical map `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of conormal sheaves.

It is the canonical map of [Stacks, Tag 01R4] for the square whose top morphism is `𝟙 Z`,
transported along the identification of pullback along an identity with the identity
functor. -/
@[stacks 067L "the first arrow"]
def conormalTransitivityMap (h : i ≫ p = j) :
    Stacks.Conormal.conormalSheaf j ⟶ Stacks.Conormal.conormalSheaf i :=
  (pullbackIdIso Z).inv.app (Stacks.Conormal.conormalSheaf j) ≫
    Stacks.Immersion.immersionConormalSheafMap i j (𝟙 Z) p
      (Stacks.Immersion.toShHom_square (h.trans (Category.id_comp j).symm))

/-- Composing the first arrow with the identification of `𝒞_{Z/Y}` with its pullback along
`𝟙 Z` recovers the canonical map of [Stacks, Tag 01R4] for the square. -/
theorem pullbackIdIso_hom_comp_conormalTransitivityMap (h : i ≫ p = j) :
    (pullbackIdIso Z).hom.app (Stacks.Conormal.conormalSheaf j) ≫
        conormalTransitivityMap i j p h =
      Stacks.Immersion.immersionConormalSheafMap i j (𝟙 Z) p
        (Stacks.Immersion.toShHom_square (h.trans (Category.id_comp j).symm)) := by
  rw [conormalTransitivityMap, Iso.hom_inv_id_app_assoc]

/-- **The first arrow is the induced map on conormal sheaves.** Over a pair of affine opens
`V ⊆ Y` and `U ⊆ X` with `U ⊆ p⁻¹ V`, on which `Z` is cut out by ideals `J ⊆ Γ(Y, V)` and
`I ⊆ Γ(X, U)`, the first arrow sends the class in `J/J²` of a section `a` to the class in
`I/I²` of any `b` with `b = p^♯ a`.

This is the affine formula of [Stacks, Tag 01R4] for the square whose top morphism
is `𝟙 Z`. -/
theorem isInducedConormalSheafMap_conormalTransitivityMap (h : i ≫ p = j) :
    Stacks.Immersion.IsInducedConormalSheafMap i j (𝟙 Z) p
      (h.trans (Category.id_comp j).symm)
      ((pullbackIdIso Z).hom.app (Stacks.Conormal.conormalSheaf j) ≫
        conormalTransitivityMap i j p h) := by
  rw [pullbackIdIso_hom_comp_conormalTransitivityMap]
  exact Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap i j (𝟙 Z) p _

/-- **The affine formula determines the first arrow.** A morphism `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` whose
transport to a morphism out of the pullback along `𝟙 Z` satisfies the affine formula of
[Stacks, Tag 01R4] is `conormalTransitivityMap`. -/
theorem conormalTransitivityMap_unique (h : i ≫ p = j)
    (φ : Stacks.Conormal.conormalSheaf j ⟶ Stacks.Conormal.conormalSheaf i)
    (hφ : Stacks.Immersion.IsInducedConormalSheafMap i j (𝟙 Z) p
      (h.trans (Category.id_comp j).symm)
      ((pullbackIdIso Z).hom.app (Stacks.Conormal.conormalSheaf j) ≫ φ)) :
    φ = conormalTransitivityMap i j p h :=
  (cancel_epi ((pullbackIdIso Z).hom.app (Stacks.Conormal.conormalSheaf j))).mp
    ((Stacks.Immersion.immersionConormalSheafMap_unique i j (𝟙 Z) p
        (h.trans (Category.id_comp j).symm) _ hφ).trans
      (pullbackIdIso_hom_comp_conormalTransitivityMap i j p h).symm)

end Stacks.ConormalSequenceTwoImmersions

end
