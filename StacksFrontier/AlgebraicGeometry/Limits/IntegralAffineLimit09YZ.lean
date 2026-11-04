module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfFiniteDomination
public import StacksFrontier.RingTheory.FinitePresentation.IntegralFiniteColimit

/-!
# An integral morphism over an affine base is a limit of finite morphisms of finite presentation

[Stacks, Tag 09YZ] says that an integral morphism `f : X ⟶ S` with `S` quasi-compact and
quasi-separated exhibits `X` as the limit of a directed inverse system of schemes finite and of
finite presentation over `S`. This file proves the case in which the base `S` is **affine**.

Over an affine base the statement is purely ring-theoretic: `X` is affine, `f` corresponds to the
integral ring map `Γ(S, ⊤) ⟶ Γ(X, ⊤)`, and
`Stacks.RingTheory.IntegralFiniteColimit.exists_isColimit_finite_finitePresentation` writes that
ring map as the colimit of a directed system of algebras which are simultaneously finite modules
and of finite presentation. Applying `AlgebraicGeometry.Scheme.Spec`, which preserves limits
because it is a right adjoint, turns that colimit of rings into the required limit of schemes.

The tag is not registered here, because an affine base is strictly stronger than the
quasi-compactness and quasi-separatedness that [Stacks, Tag 09YZ] asks for. The tag's own
statement, at a quasi-compact and quasi-separated base, is
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, which carries the
`@[stacks 09YZ]` attribute and is proved through part (2) of [Stacks, Tag 0817]
(`Stacks.AlgebraicGeometry.Tag0817PartTwo.exists_small_index_finite_finitePresentation`) and the
relative spectrum.

## Main results

* `AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine` is the affine-base case of
  [Stacks, Tag 09YZ]: an integral morphism to an affine scheme carries an
  `AlgebraicGeometry.IntegralLimitPresentation`.

## Implementation notes

The index type, its order, the diagram and the two natural transformations are produced by the
ring-theoretic statement and are therefore variables here, which is what lets the limit-preserving
instance for `AlgebraicGeometry.Scheme.Spec` be synthesised against a variable shape. The two
transporting isomorphisms are `AlgebraicGeometry.Scheme.isoSpec` for the source and the target;
`AlgebraicGeometry.Scheme.toSpecΓ_naturality` is what identifies the composite through a stage
with the original morphism.

Finiteness and finite presentation of a stage are read off `Spec` of the structure map by
`AlgebraicGeometry.IsFinite.SpecMap_iff` and
`AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff`; the isomorphism `S ≅ Spec Γ(S, ⊤)`
appended to it is cancelled because both properties respect isomorphisms.

## References

* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 09YZ] for an affine base.** An integral morphism of schemes whose target is
affine exhibits its source as the limit of a directed inverse system of schemes finite and of
finite presentation over that target.

The hypothesis that the base be affine is strictly stronger than the quasi-compactness and
quasi-separatedness of [Stacks, Tag 09YZ], so this is not the tag and carries no attribute: the
tag's own statement is
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, which carries
`@[stacks 09YZ]`. -/
theorem nonempty_integralLimitPresentation_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegralHom f] [IsAffine S] : Nonempty (IntegralLimitPresentation f) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have hint : (f.appTop).hom.IsIntegral := IsIntegralHom.isIntegral_app f ⊤ (isAffineOpen_top S)
  obtain ⟨Λ, hΛ, hΛne, hΛdir, D, t, c, hcolim, hfin, hfp, hcompat⟩ :=
    Stacks.RingTheory.IntegralFiniteColimit.exists_isColimit_finite_finitePresentation
      f.appTop hint
  have hstage (i : Λᵒᵖ) : IsFinite (Spec.map (t.app i.unop) ≫ S.isoSpec.inv) :=
    have := (IsFinite.SpecMap_iff (t.app i.unop)).mpr (hfin i.unop)
    inferInstance
  have hstagefp (i : Λᵒᵖ) :
      LocallyOfFinitePresentation (Spec.map (t.app i.unop) ≫ S.isoSpec.inv) :=
    have := (LocallyOfFinitePresentation.SpecMap_iff (t.app i.unop)).mpr (hfp i.unop)
    inferInstance
  refine ⟨{
    indexType := Λ
    indexPreorder := hΛ
    indexNonempty := hΛne
    indexDirected := hΛdir
    diagram := D.op ⋙ Scheme.Spec
    structureMap :=
      { app := fun i => Spec.map (t.app i.unop) ≫ S.isoSpec.inv
        naturality := fun i j u => ?_ }
    limitCone :=
      { app := fun i => X.isoSpec.hom ≫ Spec.map (c.app i.unop)
        naturality := fun i j u => ?_ }
    compatible := ?_
    isLimit := ?_
    stageFinite := hstage
    stageFinitePresentation := fun i => by
      have := hstage i
      exact ⟨hstagefp i, inferInstance, inferInstance⟩ }⟩
  · have h := t.naturality u.unop
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h
    simp only [Functor.comp_map, Functor.op_map, Scheme.Spec_map, Quiver.Hom.unop_op,
      Functor.const_obj_map, ← Category.assoc, ← Spec.map_comp, ← h]
    exact (Category.comp_id _).symm
  · have h := c.naturality u.unop
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
    simp only [Functor.comp_map, Functor.op_map, Scheme.Spec_map, Quiver.Hom.unop_op,
      Functor.const_obj_map, Category.assoc, ← Spec.map_comp, h]
    exact Category.id_comp _
  · intro i
    have h : Spec.map (c.app i.unop) ≫ Spec.map (t.app i.unop) = Spec.map f.appTop := by
      rw [← Spec.map_comp, hcompat i.unop]
    rw [Category.assoc, ← Category.assoc (Spec.map (c.app i.unop)), h, Scheme.isoSpec_hom,
      ← Category.assoc, ← Scheme.toSpecΓ_naturality f, Category.assoc]
    simp [← Scheme.isoSpec_hom]
  · refine IsLimit.ofIsoLimit (isLimitOfPreserves Scheme.Spec hcolim.op)
      (Cone.ext X.isoSpec.symm fun i => ?_)
    simp

end AlgebraicGeometry

end
