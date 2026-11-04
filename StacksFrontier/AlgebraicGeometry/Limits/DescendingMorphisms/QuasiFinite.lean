module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiberSequence

/-!
# Quasi-finite morphisms descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms,
and let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact and quasi-separated schemes over one
stage of the diagram. If `f₀` is locally of finite type and its base change to the limit is
quasi-finite, then its base change to some later stage is already quasi-finite.

## Main results

* `AlgebraicGeometry.exists_quasiFinite_baseChange_of_quasiFinite_limitBaseChange` descends
  quasi-finiteness from the limit to a finite stage.

## Implementation notes

Schemes over a fixed base and their base changes are represented by `CategoryTheory.Over` and
`CategoryTheory.Over.pullback`. A morphism `g : i ⟶ i₀` expresses that `i` is a stage later than
`i₀` in the cofiltered indexing category, and the cone leg at `i₀` gives the base change to the
limit. Quasi-finiteness is the unbundled conjunction of local finite type, quasi-compactness and
local quasi-finiteness (Tag 01TD part (3), and
`AlgebraicGeometry.quasiFinite_conditions_iff_isDiscrete_fibers`).

Quasi-compactness of `f₀` is not assumed: it follows from `X₀` being quasi-compact and `Y₀`
quasi-separated. The theorem also assumes that the stage `D.obj i₀` is quasi-compact and
quasi-separated and that `X₀` is quasi-separated.

## References

* [Stacks Project, Tag 094M](https://stacks.math.columbia.edu/tag/094M)
* [Stacks Project, Tag 081D](https://stacks.math.columbia.edu/tag/081D)
* [Stacks Project, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A fibre of a morphism locally of finite type is a locally Noetherian scheme. -/
private alias fiber_isLocallyNoetherian' := Stacks.AlgebraicGeometry.isLocallyNoetherian_fiber

/-- A locally quasi-finite morphism locally of finite type has fibres of dimension at
most zero. -/
private lemma topologicalKrullDim_fiber_le_zero_of_locallyQuasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [LocallyQuasiFinite f] (s : S) :
    topologicalKrullDim (f.fiber s) ≤ (0 : WithBot ℕ∞) := by
  have hrel : RelativeDimension f 0 :=
    (locallyQuasiFinite_iff_relativeDimension_zero f).mp inferInstance
  by_cases hs : Nonempty (f.fiber s)
  · exact le_of_eq (by simpa using (hrel s hs).2)
  · exact ((topologicalKrullDim_eq_bot_iff_isEmpty _).mpr (not_nonempty_iff.mp hs)).trans_le bot_le

/-- A morphism locally of finite type all of whose fibres have dimension at most zero is
locally quasi-finite. -/
private lemma locallyQuasiFinite_of_forall_topologicalKrullDim_fiber_le_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ (0 : WithBot ℕ∞)) :
    LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  intro s
  have : DiscreteTopology (f.fiber s) := by
    by_cases hs : Nonempty (f.fiber s)
    · have := fiber_isLocallyNoetherian' f s
      have := IsLocallyArtinian.of_topologicalKrullDim_le_zero (h s)
      infer_instance
    · have := not_nonempty_iff.mp hs
      infer_instance
  exact _root_.isDiscrete_iff_discreteTopology.mpr <| (f.fiberHomeo s).discreteTopology_iff.mp this

/-- Let `c` be a limit cone of a cofiltered diagram `D` of schemes with affine transition
morphisms, and let `f₀ : X₀ ⟶ Y₀` be a morphism locally of finite type of quasi-compact and
quasi-separated schemes over the quasi-compact and quasi-separated stage `D.obj i₀`. If the base
change of `f₀` to the limit is quasi-finite, then the base change of `f₀` to some later stage is
quasi-finite. -/
@[stacks 094M]
theorem exists_quasiFinite_baseChange_of_quasiFinite_limitBaseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [LocallyOfFiniteType ((Over.pullback (c.π.app i₀)).map f₀).left]
    [QuasiCompact ((Over.pullback (c.π.app i₀)).map f₀).left]
    [LocallyQuasiFinite ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀),
      (LocallyOfFiniteType ((Over.pullback (D.map g)).map f₀).left ∧
          QuasiCompact ((Over.pullback (D.map g)).map f₀).left) ∧
        LocallyQuasiFinite ((Over.pullback (D.map g)).map f₀).left := by
  have hfqc : QuasiCompact f₀.left := inferInstance
  let : ∀ {a b : Over i₀} (g : a ⟶ b),
      IsAffineHom ((baseChangeDiagram D i₀ Y₀).map g) := fun g =>
    isAffineHom_baseChangeDiagram_map D i₀ Y₀ g
  let : ∀ a : Over i₀, CompactSpace ((baseChangeDiagram D i₀ Y₀).obj a) := fun a =>
    compactSpace_baseChangeDiagram_obj D i₀ Y₀ a
  let : ∀ a : Over i₀,
      LocallyOfFiniteType ((baseChangeDiagramMap D i₀ f₀).app a) := fun a =>
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (baseChangeMap_isPullback (D.map a.hom) X₀ Y₀ f₀).flip inferInstance
  let : ∀ a : Over i₀, QuasiCompact ((baseChangeDiagramMap D i₀ f₀).app a) := fun a =>
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (baseChangeMap_isPullback (D.map a.hom) X₀ Y₀ f₀).flip hfqc
  let : ∀ {a b : Over i₀} (g : a ⟶ b),
      IsClosedImmersion (pullback.lift ((baseChangeDiagram D i₀ X₀).map g)
        ((baseChangeDiagramMap D i₀ f₀).app a)
        ((baseChangeDiagramMap D i₀ f₀).naturality g)) := by
    intro a b g
    have := isIso_pullback_lift_of_isPullback (baseChangeDiagramMap_isPullback D i₀ f₀ g)
    infer_instance
  have hf : ∀ a : Over i₀, (baseChangeCone D c i₀ X₀).π.app a ≫
      (baseChangeDiagramMap D i₀ f₀).app a =
      baseChangeMap (c.π.app i₀) X₀ Y₀ f₀ ≫ (baseChangeCone D c i₀ Y₀).π.app a := fun a =>
    (baseChangeCone_π_isPullback D i₀ f₀ c a).w
  have hlim : ∀ a : Over i₀, IsClosedImmersion
      (pullback.lift ((baseChangeCone D c i₀ X₀).π.app a)
        (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) (hf a)) := by
    intro a
    have := isIso_pullback_lift_of_isPullback (baseChangeCone_π_isPullback D i₀ f₀ c a)
    infer_instance
  let : LocallyOfFiniteType (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (baseChangeMap_isPullback (c.π.app i₀) X₀ Y₀ f₀).flip inferInstance
  have hr : MorphismProperty.RespectsIso (@LocallyQuasiFinite) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : LocallyQuasiFinite (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) :=
    (baseChangeMap_prop_iff (@LocallyQuasiFinite) (c.π.app i₀) X₀ Y₀ f₀).mpr inferInstance
  obtain ⟨j, hj⟩ := exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_cofiltered
    (I := Over i₀) (baseChangeDiagramMap D i₀ f₀)
    (baseChangeConeIsLimit D hc i₀ X₀) (baseChangeConeIsLimit D hc i₀ Y₀) hf hlim 0
    (fun s => topologicalKrullDim_fiber_le_zero_of_locallyQuasiFinite
      (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) s)
  have hlqf : LocallyQuasiFinite ((baseChangeDiagramMap D i₀ f₀).app j) :=
    locallyQuasiFinite_of_forall_topologicalKrullDim_fiber_le_zero _ hj
  refine ⟨j.left, j.hom, ⟨?_, ?_⟩, ?_⟩
  · exact MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) (D.map j.hom) f₀
      inferInstance
  · exact MorphismProperty.overPullbackMap (P := @QuasiCompact) (D.map j.hom) f₀ hfqc
  · exact (baseChangeMap_prop_iff (@LocallyQuasiFinite) (D.map j.hom) X₀ Y₀ f₀).mp hlqf


end AlgebraicGeometry

end
