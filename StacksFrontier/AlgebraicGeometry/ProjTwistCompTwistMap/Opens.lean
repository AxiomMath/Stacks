module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Generic

/-!
# The open of the target that the two sides of Tag 01MZ's twist assertion read over

Both sides of Tag 01MZ's assertion about the maps on all twists end in a section of the `n`-th
twist on `Proj 𝒞`, but over two different opens: the three-factor side over the image under
`U(ψ ∘ φ).ι` of `r_{ψφ}⁻¹(T)`, and the nine-factor side over the image under `U(ψ).ι` of
`r_ψ⁻¹` of the image under `U(φ).ι` of `r_φ⁻¹(T)`. This file identifies them, **at the level of
variables**: the two inputs are that the leading morphism is an isomorphism and that the square
of an open immersion and a morphism restricted to it is cartesian on opens.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.iso_image_preimage`
* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.image_preimage_eq_of`

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

universe u

/-- The image under an isomorphism of the inverse image of an open is that open. -/
public theorem iso_image_preimage {X Y : Scheme.{u}} (e : X ≅ Y) (W : Y.Opens) :
    e.hom ''ᵁ (e.hom ⁻¹ᵁ W) = W := by
  rw [← Scheme.Hom.inv_preimage e (e.hom ⁻¹ᵁ W)]
  change (e.inv ≫ e.hom) ⁻¹ᵁ W = W
  rw [e.inv_hom_id]
  rfl

/-- Two equal morphisms have the same image on opens. The two `IsOpenImmersion` instances are
proof-irrelevant, so after `subst` the statement is reflexive; `rw` cannot do this, because the
instance argument of `AlgebraicGeometry.Scheme.Hom.opensFunctor` depends on the morphism and the
motive is not type-correct. -/
public theorem image_congr_morphism {X Y : Scheme.{u}} {f g : X ⟶ Y} [IsOpenImmersion f]
    [IsOpenImmersion g] (h : f = g) (V : X.Opens) : f ''ᵁ V = g ''ᵁ V := by
  subst h
  rfl

/-- **The two opens of the target agree.**

`hqsurj` says the leading morphism is surjective on opens — it is an isomorphism in the
application — and `hmr` is `AlgebraicGeometry.image_morphismRestrict_preimage`, the statement
that the square of the open immersion `jj` and the restriction `p` is cartesian on opens. -/
public theorem image_preimage_eq_of {W U UP UQ Pa Pb Pc : Scheme.{u}}
    (q : W ⟶ U) (dU : U ⟶ Pa) (iU : U ⟶ Pc)
    (p : W ⟶ UP) (dP : UP ⟶ Pa) (iP : UP ⟶ Pb)
    (jj : W ⟶ UQ) (dQ : UQ ⟶ Pb) (iQ : UQ ⟶ Pc)
    [IsOpenImmersion q] [IsOpenImmersion iU] [IsOpenImmersion iP] [IsOpenImmersion jj]
    [IsOpenImmersion iQ]
    (hq : q ≫ dU = p ≫ dP) (ht : q ≫ iU = jj ≫ iQ)
    (hqsurj : ∀ V : U.Opens, q ''ᵁ (q ⁻¹ᵁ V) = V)
    (hmr : ∀ V : UP.Opens, jj ''ᵁ (p ⁻¹ᵁ V) = dQ ⁻¹ᵁ (iP ''ᵁ V))
    (T : Pa.Opens) :
    iU ''ᵁ (dU ⁻¹ᵁ T) = iQ ''ᵁ (dQ ⁻¹ᵁ (iP ''ᵁ (dP ⁻¹ᵁ T))) := by
  refine Eq.trans (congrArg (fun Z : U.Opens => iU ''ᵁ Z) (hqsurj (dU ⁻¹ᵁ T)).symm) ?_
  refine Eq.trans (Scheme.Hom.comp_image q iU (q ⁻¹ᵁ (dU ⁻¹ᵁ T))).symm ?_
  refine Eq.trans (image_congr_morphism ht (q ⁻¹ᵁ (dU ⁻¹ᵁ T))) ?_
  refine Eq.trans (Scheme.Hom.comp_image jj iQ (q ⁻¹ᵁ (dU ⁻¹ᵁ T))) ?_
  refine congrArg (fun Z : UQ.Opens => iQ ''ᵁ Z) ?_
  refine Eq.trans ?_ (hmr (dP ⁻¹ᵁ T))
  exact congrArg (fun Z : W.Opens => jj ''ᵁ Z)
    (congrArg (fun k : W ⟶ Pa => k ⁻¹ᵁ T) hq)

end Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

end
