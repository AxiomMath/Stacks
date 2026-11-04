module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointGeneralizing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber

/-!
# Generic points of fibres over an integral base change

Let `g : X ⟶ T` be a morphism and let `i : T ⟶ S` be integral.  **A point of `X` which is a
generic point of an irreducible component of its own fibre of `g` is a generic point of an
irreducible component of its own fibre of `g ≫ i`.**  The fibre of `g ≫ i` through such a point
is the union of the fibres of `g` over the points of the fibre of `i` below it, and that fibre
of `i` carries no nontrivial specializations, every point of the source of an integral morphism
being closed in its own fibre.

This is the comparison the reduced fibre theorem needs between its two bases.  Its conclusion
speaks of the fibres of `Y ⟶ Spec B`, while the transport of the generic-point condition down
to the scheme below
(`AlgebraicGeometry.mem_genericPoints_asFiber_normalization_pullbackFst`) asks for the condition
over `Spec A`; the two agree because `Spec B ⟶ Spec A` is finite.

## Main results

* `AlgebraicGeometry.eq_of_specializes_of_base_eq_of_isIntegralHom`: two points of the source of
  an integral morphism related by a specialization and lying over the same point are equal.
* `AlgebraicGeometry.mem_genericPoints_asFiber_comp_of_isIntegralHom`: the generic-point
  condition passes from the fibres of `g` to the fibres of `g ≫ i` for `i` integral.

## Implementation notes

The generic-point condition is used in the ambient form of
`AlgebraicGeometry.mem_genericPoints_asFiber_iff` — no proper generalization of the point lies
in the same fibre — in which the comparison of the two fibres is immediate: a generalization
lying in the `g ≫ i`-fibre lies in the `g`-fibre by the first result.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 02NT](https://stacks.math.columbia.edu/tag/02NT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X T S : Scheme.{u}}

/-- **The fibres of an integral morphism carry no nontrivial specializations.**  If `t ⤳ t'` and
the two points have the same image under an integral morphism, they are equal: `t'` lies in the
closure of `{t}` taken in the fibre, and that closure is `{t}` by Tag 02NT. -/
theorem eq_of_specializes_of_base_eq_of_isIntegralHom (i : T ⟶ S) [IsIntegralHom i] {t t' : T}
    (h : t ⤳ t') (hi : i.base t = i.base t') : t = t' := by
  have hF : i.asFiber t ⤳ (i.fiberHomeo (i.base t)).symm ⟨t', hi.symm⟩ := by
    show (i.fiberHomeo (i.base t)).symm ⟨t, rfl⟩ ⤳ _
    exact ((subtype_specializes_iff ..).2 h).map (i.fiberHomeo (i.base t)).symm.continuous
  simpa using (congrArg (i.fiberι (i.base t)) (Set.mem_singleton_iff.mp
    (specializes_iff_forall_closed.mp hF _
      (isClosed_singleton_asFiber_of_isIntegral i t) (Set.mem_singleton _)))).symm

/-- **A generic point of a fibre stays one after composing with an integral morphism.**  Let
`g : X ⟶ T` and let `i : T ⟶ S` be integral.  If `x : X` is a generic point of an irreducible
component of its own fibre of `g`, then it is a generic point of an irreducible component of its
own fibre of `g ≫ i`.

Read in the ambient scheme, the condition says that no proper generalization of `x` lies in the
same fibre.  A generalization `x'` of `x` with `i (g x') = i (g x)` has `g x' ⤳ g x`, so
`g x' = g x` by `AlgebraicGeometry.eq_of_specializes_of_base_eq_of_isIntegralHom`, and then
`x' = x` by the hypothesis. -/
theorem mem_genericPoints_asFiber_comp_of_isIntegralHom (g : X ⟶ T) (i : T ⟶ S)
    [IsIntegralHom i] {x : X}
    (hx : g.asFiber x ∈ genericPoints ↥(g.fiber (g.base x))) :
    (g ≫ i).asFiber x ∈ genericPoints ↥((g ≫ i).fiber ((g ≫ i).base x)) := by
  rw [mem_genericPoints_asFiber_iff] at hx ⊢
  intro x' hspec hfx
  refine hx x' hspec (eq_of_specializes_of_base_eq_of_isIntegralHom i (hspec.map g.continuous) ?_)
  simpa only [Scheme.Hom.comp_apply] using hfx

end AlgebraicGeometry

end
