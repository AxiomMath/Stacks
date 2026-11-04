module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtension
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.BaseChange

/-!
# Affine opens of a base change to an algebraic extension come from a finite stage

Let `Ω/k` be an algebraic extension of fields, let `E₀ ⊆ Ω` be a finite subextension and let
`Z` be a quasi-separated scheme over `E₀`. Every affine open of the base change
`Spec Ω ×_{Spec E₀} Z` is the inverse image of an affine open of `Spec E ×_{Spec E₀} Z` for some
finite subextension `E₀ ⊆ E ⊆ Ω`.

This is [Stacks, Tag 01Z4] part (1) for the inverse system of the base changes of `Z` to the
finite subextensions of `Ω` containing `E₀`: `Spec Ω` is the limit of their spectra
(`Stacks.Chow.isLimit_finiteSubextensionCone`), base change commutes with that limit
(`AlgebraicGeometry.isLimitPullbackCone`, [Stacks, Tag 01YZ]), and the transition morphisms are
affine, being base changes of morphisms of spectra.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_preimage_eq_finiteSubextension`: the statement above.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01YZ](https://stacks.math.columbia.edu/tag/01YZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.Chow

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- **An affine open of a base change to an algebraic extension comes from a finite stage.**
Let `Ω/k` be algebraic, `E₀ ⊆ Ω` a finite subextension and `f : Z ⟶ Spec E₀` a quasi-separated
scheme over `E₀`. Every affine open `W` of `Spec Ω ×_{Spec E₀} Z` is the inverse image, along
the projection to `Spec E ×_{Spec E₀} Z`, of an affine open of the latter, for some finite
subextension `E₀ ⊆ E ⊆ Ω`. -/
theorem exists_isAffineOpen_preimage_eq_finiteSubextension [Algebra.IsAlgebraic k Ω]
    (E₀ : FiniteSubextension k Ω) {Z : Scheme.{u}} (f : Z ⟶ Spec (.of E₀.1))
    [QuasiSeparatedSpace Z]
    (W : (pullback (Spec.map (CommRingCat.ofHom E₀.1.val.toRingHom)) f).Opens)
    (hW : IsAffineOpen W) :
    ∃ (E : FiniteSubextension k Ω) (h : E₀.1 ≤ E.1)
      (U : (pullback (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom))
        f).Opens),
      IsAffineOpen U ∧
        pullback.lift (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom E.1.val.toRingHom))
          (pullback.snd _ _) (by
            rw [Category.assoc, ← Spec.map_comp, ← pullback.condition]
            rfl) ⁻¹ᵁ U = W := by
  let D := finiteSubextensionDiagram k Ω
  let c := finiteSubextensionCone k Ω
  have hc : IsLimit c := isLimit_finiteSubextensionCone k Ω
  let i : (FiniteSubextension k Ω)ᵒᵖ := Opposite.op E₀
  let D' := pullbackDiagram D i f
  let c' := pullbackCone D c i f
  have hc' : IsLimit c' := isLimitPullbackCone D c hc i f
  have : ∀ {j j' : Over i} (g : j ⟶ j'), IsAffineHom (D'.map g) := by
    intro j j' g
    refine MorphismProperty.overPullbackMap (P := @IsAffineHom) f ((Over.post D).map g) ?_
    show IsAffineHom (Spec.map _)
    infer_instance
  have : ∀ j : Over i, QuasiSeparatedSpace (D'.obj j) := by
    intro j
    have : QuasiSeparated (D.map j.hom) := by
      show QuasiSeparated (Spec.map _)
      infer_instance
    have : QuasiSeparated (pullback.snd (D.map j.hom) f) :=
      quasiSeparated_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback (D.map j.hom) f) inferInstance
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd (D.map j.hom) f) _ this
  obtain ⟨j, U, hU, hpre⟩ := exists_isAffineOpen_preimage_eq D' c' hc' W hW
  exact ⟨j.left.unop, leOfHom j.hom.unop, U, hU, hpre⟩

end AlgebraicGeometry

end
