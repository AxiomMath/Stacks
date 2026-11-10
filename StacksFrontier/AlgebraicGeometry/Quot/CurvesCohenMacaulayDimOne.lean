module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackOfAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmooth
import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.RelativeDimensionLocus

/-!
# The locus of Cohen–Macaulay curves of relative dimension one

For a family of curves `f : X → S` the set `S'` of points of `S` over which `f` is
Cohen–Macaulay and has relative dimension one is open, for an arbitrary family: this is the
input (o) of Stacks 0E0E for the open substack `Curves^{CM,1}` of Stacks 0E1F. Together with
the base-change compatibility of `S'` it says that `S'` is the largest open subscheme of `S`
over which `f` is Cohen–Macaulay of relative dimension one, and that its formation commutes with
arbitrary base change.

Over the spectrum of a field the condition is read off the proper scheme itself: a proper
scheme `X` of dimension at most one over a field `k` is a family of curves over `Spec k`, and
that family is Cohen–Macaulay of relative dimension one exactly when `X` is Cohen–Macaulay and
equidimensional of dimension one.

## Main results

* `AlgebraicGeometry.CurveFamily.compl_cohenMacaulayDimOneBaseLocus`: the complement of the
  locus is the image of the set of points of the total space at which the family is not
  Cohen–Macaulay of relative dimension one.
* `AlgebraicGeometry.CurveFamily.cohenMacaulayDimOneBaseLocus_isOpen`: **Stacks 0E1F**, the
  locus is open, for every family of curves.
* `AlgebraicGeometry.isOpenCurvesLocus_isCohenMacaulayDimOneFamily`: **Stacks 0E1F**, condition
  (o) of Section 0E0E for `Curves^{CM,1}`, the step of the proof from which the method of that
  section makes the open substack.
* `AlgebraicGeometry.isCohenMacaulayDimOneFamily_curveFamilyOfSchemeMorphism_iff`:
  **Stacks 0E1F**, part (2) on the family: over the spectrum of a field, the family of curves of
  a proper scheme of dimension at most one is Cohen–Macaulay of relative dimension one exactly
  when the scheme is Cohen–Macaulay and every irreducible component of it has dimension one.

## Implementation notes

The source proves openness of the locus through the Cohen–Macaulay locus: once the family is
Cohen–Macaulay, Tag 0E11 splits the total space by relative dimension. For an arbitrary family
the same argument is run on the open subspace of the total space where the family is
Cohen–Macaulay (Tag 0E10), which is
`AlgebraicGeometry.Space.isOpen_setOf_isCohenMacaulayAt_and_hasRelativeDimensionAt`: the set of
points of the total space at which the family is Cohen–Macaulay of relative dimension one is
open, so its complement is closed, and properness carries that complement to a closed subset of
the base, the complement of the locus.

"Equidimensional of dimension one" is read as in Tag 0058: all irreducible components have the
same dimension, and that dimension is one. Read componentwise the equivalence over a field needs
no non-emptiness hypothesis, the empty scheme being Cohen–Macaulay of relative dimension one
with no irreducible component.

The open substack itself, and the two characterizations of it, are in
`StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulayDimOneSubstack`.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E10](https://stacks.math.columbia.edu/tag/0E10)
* [Stacks Project, Tag 0E11](https://stacks.math.columbia.edu/tag/0E11)
* [Stacks Project, Tag 0E1F](https://stacks.math.columbia.edu/tag/0E1F)
* [Stacks Project, Tag 0058](https://stacks.math.columbia.edu/tag/0058)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The complement of the locus in the base of a family of curves over which it is
Cohen–Macaulay of relative dimension one is the image of the set of points of the total space
at which it is not Cohen–Macaulay of relative dimension one. -/
theorem CurveFamily.compl_cohenMacaulayDimOneBaseLocus (X : CurveFamily B hZ) :
    (CurveFamily.cohenMacaulayDimOneBaseLocus B hZ X)ᶜ =
      Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom ''
        {x : Space.points B integerBase hZ X.total.obj |
          Space.IsCohenMacaulayAt B integerBase hZ X.toBase.hom x ∧
            Space.HasRelativeDimensionAt ((1 : ℕ) : ℕ∞) B integerBase hZ X.toBase.hom x}ᶜ := by
  ext y
  simp only [CurveFamily.cohenMacaulayDimOneBaseLocus, CurveFamily.relativeDimensionOneBaseLocus,
    Space.cohenMacaulayBaseLocus, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_image]
  refine ⟨fun hy => ?_, fun ⟨x, hx, hxy⟩ ⟨hCM, hdim⟩ => hx ⟨hCM x hxy, hdim x hxy⟩⟩
  by_contra hne
  have hall : ∀ x, Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x = y →
      Space.IsCohenMacaulayAt B integerBase hZ X.toBase.hom x ∧
        Space.HasRelativeDimensionAt ((1 : ℕ) : ℕ∞) B integerBase hZ X.toBase.hom x :=
    fun x hx => not_not.mp fun h => hne ⟨x, h, hx⟩
  exact hy ⟨fun x hx => (hall x hx).1, fun x hx => (hall x hx).2⟩

/-- **The locus of Cohen–Macaulay relative dimension one is open.** For every family of curves
`f : X → S`, the set of points of `S` over which `f` is Cohen–Macaulay and has relative
dimension one is open.

The set of points of the total space at which `f` is Cohen–Macaulay of relative dimension one is
open (Tags 0E10 and 0E11), and `f` is proper, so the image of its complement — the complement
of the locus — is closed. -/
@[stacks 0E1F "the open locus in the base of Cohen–Macaulay relative dimension one, for an \
arbitrary family"]
theorem CurveFamily.cohenMacaulayDimOneBaseLocus_isOpen (X : CurveFamily B hZ) :
    IsOpen (CurveFamily.cohenMacaulayDimOneBaseLocus B hZ X) := by
  rw [← isClosed_compl_iff, CurveFamily.compl_cohenMacaulayDimOneBaseLocus]
  exact Space.isClosed_of_universallyClosed B integerBase hZ (schemeSpace X.base).property
    X.toBase.hom X.proper.universallyClosed _
    (Space.isOpen_setOf_isCohenMacaulayAt_and_hasRelativeDimensionAt B integerBase hZ
      X.total.property (schemeSpace X.base).property X.toBase.hom X.flat
      X.finitePresentation.1 1).isClosed_compl

/-- **Condition (o) of Section 0E0E for `Curves^{CM,1}`.** For every family of curves `X → S`
there is an open subset `S'` of the base such that a family of curves mapping to `X → S` is
Cohen–Macaulay of relative dimension one exactly when its base maps into `S'`: the locus of
Cohen–Macaulay relative dimension one, which is open for every family and commutes with base
change. -/
@[stacks 0E1F "condition (o) of 0E0E: the open locus in the base, for an arbitrary family"]
theorem isOpenCurvesLocus_isCohenMacaulayDimOneFamily :
    IsOpenCurvesLocus B hZ (IsCohenMacaulayDimOneFamily B hZ) :=
  IsOpenCurvesLocus.of_baseLocus (CurveFamily.cohenMacaulayDimOneBaseLocus B hZ)
    (CurveFamily.cohenMacaulayDimOneBaseLocus_isOpen B hZ)
    (CurveFamily.preimage_cohenMacaulayDimOneBaseLocus B hZ)
    (isCohenMacaulayDimOneFamily_iff_cohenMacaulayDimOneBaseLocus_eq_univ B hZ)

/-- A morphism of schemes into the spectrum of a field is flat. -/
@[ega "IV 11.9.9" "Parenthetical clause"]
theorem flat_of_eq_spec_field {X Y : Scheme.{u}} (f : X ⟶ Y) (k : Type u) [Field k]
    (hY : Y = Spec (.of k)) : Flat f := by
  subst hY
  infer_instance

/-- A proper morphism of schemes into the spectrum of a field is locally of finite
presentation, the spectrum of a field being Noetherian. -/
theorem locallyOfFinitePresentation_of_eq_spec_field {X Y : Scheme.{u}} (f : X ⟶ Y)
    (k : Type u) [Field k] (hY : Y = Spec (.of k)) [IsProper f] :
    LocallyOfFinitePresentation f := by
  subst hY
  infer_instance

/-- **Part (2) of Stacks 0E1F, on the family.** Let `g : T ⟶ U` be a morphism of the big fppf
site of the integers whose target scheme is the spectrum of a field `k`, whose underlying
morphism of schemes is proper, and whose source scheme has dimension at most one. Then the
family of curves of `g` is Cohen–Macaulay of relative dimension one exactly when the source
scheme is Cohen–Macaulay and equidimensional of dimension one, every irreducible component of it
having dimension one. -/
@[stacks 0E1F "part (2), on the family of curves of the proper scheme: Cohen–Macaulay and \
equidimensional of dimension one"]
theorem isCohenMacaulayDimOneFamily_curveFamilyOfSchemeMorphism_iff
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsCohenMacaulayDimOneFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g
          (flat_of_eq_spec_field _ k hU) hproper
          (locallyOfFinitePresentation_of_eq_spec_field _ k hU)
          (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
          ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
          ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
          hdim) ↔
      (IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        TopologicalSpace.Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        ∀ W ∈ irreducibleComponents ((BigFppfOver.toScheme B integerBase hZ).obj T),
          topologicalKrullDim W = (1 : WithBot ℕ∞)) := by
  set F := BigFppfOver.toScheme B integerBase hZ
  have := flat_of_eq_spec_field (F.map g) k hU
  have := locallyOfFinitePresentation_of_eq_spec_field (F.map g) k hU
  have hfib : ∀ v : F.obj U, IsLocallyNoetherian ((F.map g).fiber v) := fun v => by
    have : LocallyOfFiniteType ((F.map g).fiberToSpecResidueField v) := by
      change LocallyOfFiniteType (pullback.snd (F.map g) ((F.obj U).fromSpecResidueField v))
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian ((F.map g).fiberToSpecResidueField v)
  have hCM := isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec B hZ g k hU hfib
  have hdimOne :=
    hasRelativeDimension_schemeSpaceMap_iff_forall_irreducibleComponents B hZ 1 g k hU
      inferInstance
  rw [show ((1 : ℕ) : WithBot ℕ∞) = 1 by norm_num] at hdimOne
  refine ⟨fun hX => ?_, fun hX => ⟨hCM.mpr hX.1, hdimOne.mpr hX.2.2⟩⟩
  have hcomp := hdimOne.mp hX.2
  exact ⟨hCM.mp hX.1, fun C hC D hD => (hcomp C hC).trans (hcomp D hD).symm, hcomp⟩

end AlgebraicGeometry

end
