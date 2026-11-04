module

public import StacksFrontier.AlgebraicGeometry.Simplicial.PhHypercoveringSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismPropertyAbsoluteCoskeleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective

/-!
# Proper hypercoverings of algebraic spaces

Let `S` be a scheme, `X` an algebraic space over `S` and `a : U → X` an augmented simplicial
algebraic space over `S`. Following Section 0DHI of the Stacks project, `U` is a *proper
hypercovering* of `X` when

1. `U₀ → X` is proper and surjective,
2. `U₁ → U₀ ×_X U₀` is proper and surjective,
3. `U_{n+1} → (cosk_n sk_n U)_{n+1}` is proper and surjective for `n ≥ 1`.

The category of algebraic spaces over `S` has all finite limits, hence the coskeleta used in this
formulation exist. Since a proper surjective morphism is a ph covering (Stacks 0DFI), a proper
hypercovering is a hypercovering of `X` in the big ph site in the sense of Section 09X8, which is
the first step of every comparison of a proper hypercovering with the ph topology.

## Main definitions

* `AlgebraicGeometry.Space.properSurjective`: the proper surjective morphisms of algebraic spaces
  over `S`.
* `AlgebraicGeometry.Space.IsProperHypercovering`: proper hypercoverings, the hypercoverings for
  the class of proper surjective morphisms.

## Main results

* `AlgebraicGeometry.Space.hasFiniteLimits_algebraicSpaces`: the category of algebraic spaces
  over `S` has all finite limits.
* `AlgebraicGeometry.Space.hasPointwiseRightKanExtension_truncatedInclusion`: the coskeleta of
  truncated simplicial algebraic spaces over `S` exist.
* `AlgebraicGeometry.Space.isProperHypercovering_iff`: the three conditions of the definition,
  with the coskeleta formed in the category of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.IsProperHypercovering.isProper_zero`,
  `AlgebraicGeometry.Space.IsProperHypercovering.isProper_one`: the augmentations `U₀ → X` and
  `U₁ → X` are proper.
* `AlgebraicGeometry.BigPHSpaceSite.isPHCoveringMorphism_of_properSurjective`: a proper
  surjective morphism defines a ph covering.
* `AlgebraicGeometry.BigPHSpaceSite.IsProperHypercovering.isPHHypercovering`: a proper
  hypercovering is a ph hypercovering.
* `AlgebraicGeometry.BigPHSpaceSite.IsProperHypercovering.isHypercoveringAugmentation`: a proper
  hypercovering is a hypercovering of `X` in `(Spaces/S)_ph` in the sense of Section 09X8.

## Implementation notes

`IsProperHypercovering` is the `P`-hypercovering of Stacks 0DER for `P` the proper surjective
morphisms, whose coskeleta are formed in the category of algebraic spaces over `X`. For `n ≥ 1`
the limit defining `(cosk_n sk_n U)_{n+1}` is indexed by a connected category, and the forgetful
functor from algebraic spaces over `X` to algebraic spaces over `S` preserves connected limits,
so the matching morphism does not depend on the choice; `isProperHypercovering_iff` records the
definition with the coskeleta of `U` formed over `S`, as in the source. For `n = 0` the two
coskeleta differ (`U₀ × U₀` against `U₀ ×_X U₀`), which is why condition 2 is stated separately.

## References

* [Stacks Project, Section 0DHI](https://stacks.math.columbia.edu/tag/0DHI)
* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
* [Stacks Project, Tag 0DFI](https://stacks.math.columbia.edu/tag/0DFI)
* [Stacks Project, Section 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Section 0DHI.** The category of algebraic spaces over `S` has all finite limits: it has a
final object, the base `S` itself, and fibre products. -/
theorem hasFiniteLimits_algebraicSpaces : HasFiniteLimits (AlgebraicSpaces B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- **Section 0DHI.** The coskeleta of simplicial algebraic spaces over `S` exist: every
`n`-truncated simplicial algebraic space over `S` has a pointwise right Kan extension along
`(Δ_{≤n} ⊆ Δ)ᵒᵖ`, its `n`-coskeleton, because the category of algebraic spaces over `S` has
all finite limits. -/
instance hasPointwiseRightKanExtension_truncatedInclusion (n : ℕ)
    (F : SimplicialObject.Truncated (AlgebraicSpaces B S hS) n) :
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F :=
  haveI := hasFiniteLimits_algebraicSpaces B S hS
  SimplicialObject.Truncated.hasPointwiseRightKanExtension_of_hasFiniteLimits n F

/-- The proper surjective morphisms of algebraic spaces over `S`. -/
def properSurjective : MorphismProperty (AlgebraicSpaces B S hS) := fun _ _ f ↦
  IsProper B S hS f.hom ∧ IsSurjective B S hS f.hom

/-- Proper surjective morphisms of algebraic spaces over `S` are stable under base change,
properness by Stacks 04WP and surjectivity by Stacks 03MH. -/
instance properSurjective_isStableUnderBaseChange :
    (properSurjective B S hS).IsStableUnderBaseChange :=
  ⟨fun sq hg ↦ ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback sq hg.1,
    isSurjective_of_isPullback B S hS sq hg.2⟩⟩

/-- **Section 0DHI.** An augmented simplicial algebraic space `a : U → X` over `S` is a *proper
hypercovering* of `X` when `U₀ → X`, `U₁ → U₀ ×_X U₀` and the matching morphisms
`U_{n+1} → (cosk_n sk_n U)_{n+1}` for `n ≥ 1` are proper and surjective.

The coskeleta are formed here in the category of algebraic spaces over `X`, as for the
`P`-hypercoverings of Stacks 0DER; `isProperHypercovering_iff` states the equivalent definition
with the coskeleta of `U` formed in the category of algebraic spaces over `S`. -/
abbrev IsProperHypercovering (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) : Prop :=
  MorphismProperty.IsHypercovering (properSurjective B S hS) A

/-- **Section 0DHI, the definition as stated.** Let `a : U → X` be an augmentation of a
simplicial algebraic space `U` over `S` towards an algebraic space `X` over `S`. Then `U` is a
proper hypercovering of `X` if and only if

1. `U₀ → X` is proper and surjective,
2. `U₁ → U₀ ×_X U₀` is proper and surjective,
3. `U_{n+1} → (cosk_n sk_n U)_{n+1}` is proper and surjective for `n ≥ 1`,

the coskeleta being formed in the category of algebraic spaces over `S`, which has all finite
limits. For `n ≥ 1` the limits defining `(cosk_n sk_n U)_{n+1}` are connected, so they do not
change when formed over `X` instead. -/
theorem isProperHypercovering_iff (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)) :
    IsProperHypercovering B S hS A ↔
      (IsProper B S hS (A.hom.app (op ⦋0⦌)).hom ∧
          IsSurjective B S hS (A.hom.app (op ⦋0⦌)).hom) ∧
        (IsProper B S hS (SimplicialObject.Augmented.firstMatchingArrow A).hom.hom ∧
          IsSurjective B S hS (SimplicialObject.Augmented.firstMatchingArrow A).hom.hom) ∧
        ∀ n : ℕ, 1 ≤ n →
          IsProper B S hS (((SimplicialObject.coskAdj n).unit.app A.left).app (op ⦋n + 1⦌)).hom ∧
            IsSurjective B S hS
              (((SimplicialObject.coskAdj n).unit.app A.left).app (op ⦋n + 1⦌)).hom :=
  MorphismProperty.isHypercovering_iff_coskAdj_unit (properSurjective B S hS) A

variable {B S hS} {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

/-- The augmentation `U₀ → X` of a proper hypercovering is proper. -/
theorem IsProperHypercovering.isProper_zero (h : IsProperHypercovering B S hS A) :
    IsProper B S hS (A.hom.app (op ⦋0⦌)).hom :=
  h.map_zero.1

/-- The augmentation `U₁ → X` of a proper hypercovering is proper: it is the composite of
`U₁ → U₀ ×_X U₀`, of the first projection, which is a base change of `U₀ → X`, and of
`U₀ → X`. -/
theorem IsProperHypercovering.isProper_one (h : IsProperHypercovering B S hS A) :
    IsProper B S hS (A.hom.app (op ⦋1⦌)).hom := by
  let a₀ := A.hom.app (op ⦋0⦌)
  have e : A.hom.app (op ⦋1⦌) = (SimplicialObject.Augmented.firstMatchingArrow A).hom ≫
      pullback.fst a₀ a₀ ≫ a₀ := by
    rw [SimplicialObject.Augmented.firstMatchingArrow_hom_fst_assoc]
    have := A.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op
    exact (Category.comp_id _).symm.trans this.symm
  have hfst : IsProper B S hS (pullback.fst a₀ a₀).hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (IsPullback.of_hasPullback a₀ a₀).flip h.map_zero.1
  rw [e]
  exact isProper_comp' B S hS _ _ (pullback a₀ a₀).property A.right.property h.map_one.1
    (isProper_comp' B S hS _ _ (A.left.obj (op ⦋0⦌)).property A.right.property hfst
      h.map_zero.1)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigPHSpaceSite

open Space Stacks.CategoryTheory.Hypercovering

variable {S : Scheme.{u}} {T : BigPHSpaceSite S} {A : SimplicialObject.Augmented T.Spaces}

/-- **Section 0DHI, (a).** A proper surjective morphism of algebraic spaces defines a ph covering
(Stacks 0DFI). -/
theorem isPHCoveringMorphism_of_properSurjective {X Y : T.Spaces} {f : X ⟶ Y}
    (hf : properSurjective T.fppfSite S T.fppf_mem f) : T.IsPHCoveringMorphism f :=
  IsPHCovering.punit _ _ _
    (isPHCovering_of_isProper_isSurjective T.fppfSite S T.fppf_mem f.hom Y.property X.property
      hf.1 hf.2)

/-- **A proper hypercovering is a ph hypercovering**: proper surjective morphisms are ph
coverings (Stacks 0DFI). -/
theorem IsProperHypercovering.isPHHypercovering
    (h : IsProperHypercovering T.fppfSite S T.fppf_mem A) :
    MorphismProperty.IsHypercovering T.IsPHCoveringMorphism A :=
  ⟨isPHCoveringMorphism_of_properSurjective h.map_zero,
    isPHCoveringMorphism_of_properSurjective h.map_one,
    fun n hn ↦ isPHCoveringMorphism_of_properSurjective (h.matching n hn)⟩

/-- **Section 0DHI. A proper hypercovering is a ph hypercovering**: a proper hypercovering
`U → X` is a hypercovering of `X` in the site `(Spaces/S)_ph` in the sense of Section 09X8, by
Stacks 0DFI. -/
theorem IsProperHypercovering.isHypercoveringAugmentation
    (h : IsProperHypercovering T.fppfSite S T.fppf_mem A) :
    IsHypercoveringAugmentation T.topology.toPretopology A.left A.hom :=
  isHypercoveringAugmentation_of_isHypercovering (IsProperHypercovering.isPHHypercovering h)

end AlgebraicGeometry.BigPHSpaceSite

end
