module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyClosedPoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety

/-!
# Proportionality of two functionals, read as the determinant condition

A point `y` of `𝐏(V)` is the translate `r_g(x)` of a closed point `x` exactly when the functional
cutting out `y` is proportional to `f_x ∘ g`, and over a field proportionality of two functionals
`f` and `h` with `h ≠ 0` is the vanishing of all their `2 × 2` minors

`f(u) · h(v) - f(v) · h(u) = 0`.

This file records that dictionary in both directions, together with the two pieces of bookkeeping
the fibre identification of the Moving Lemma needs around it: that the point cut out by a
functional does not depend on the proof that the functional is nonzero, and that the value of the
section `σ_λ` at a closed point of `𝐏(V)` is a closed point of `ℓ × 𝐏(V)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint_eq_of_minors_eq`: vanishing
  minors identify the two points.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.minors_eq_of_linearFunctionalPoint_eq`: conversely,
  two functionals cutting out the same point have vanishing minors.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_lineSection_base`: the section carries
  closed points to closed points.

## Implementation notes

The minors are written as the equation `f(u) · h(v) = f(v) · h(u)` rather than as a determinant,
which is the shape in which the vanishing of the proportionality sections of the Moving Lemma is
produced. The proof of the forward direction picks a vector on which `h` does not vanish and
reads the minors as the formula `f = (f v₀ / h v₀) · h`; the scalar is nonzero because `f` is, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint_units_smul` then identifies the
two points.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **Vanishing minors identify the two points.** If every `2 × 2` minor of the pair of
functionals `f`, `h` vanishes and both are nonzero, they cut out the same point of `𝐏(V)`. -/
public theorem linearFunctionalPoint_eq_of_minors_eq {f h : Module.Dual k V} (hf : f ≠ 0)
    (hh : h ≠ 0) (hmin : ∀ u v : V, f u * h v = f v * h u) :
    linearFunctionalPoint k V f hf = linearFunctionalPoint k V h hh := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, h v₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hh (LinearMap.ext fun v => hc v)
  have hfv₀ : f v₀ ≠ 0 := by
    intro hz
    refine hf (LinearMap.ext fun u => ?_)
    have := hmin u v₀
    rw [hz, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hv₀
  set c : k := f v₀ / h v₀ with hc
  have hcne : c ≠ 0 := div_ne_zero hfv₀ hv₀
  have hfc : f = (Units.mk0 c hcne : kˣ) • h := by
    refine LinearMap.ext fun u => ?_
    have hmu := hmin u v₀
    change f u = c * h u
    rw [hc, div_mul_eq_mul_div, ← hmu]
    field_simp
  have hcu : ((Units.mk0 c hcne : kˣ) • h : Module.Dual k V) ≠ 0 := hfc ▸ hf
  rw [linearFunctionalPoint_eq_of_eq k V hf hcu hfc]
  exact linearFunctionalPoint_units_smul k V (Units.mk0 c hcne) h hh hcu

/-- **Two functionals cutting out the same point have vanishing minors.** -/
public theorem minors_eq_of_linearFunctionalPoint_eq {f h : Module.Dual k V} (hf : f ≠ 0)
    (hh : h ≠ 0) (heq : linearFunctionalPoint k V f hf = linearFunctionalPoint k V h hh)
    (u v : V) : f u * h v = f v * h u := by
  have hker : ∀ w : V, f w = 0 ↔ h w = 0 := by
    intro w
    rw [← linearFunctionalPoint_ι_mem k V f hf w, ← linearFunctionalPoint_ι_mem k V h hh w, heq]
  obtain ⟨c, hcf⟩ := Module.Dual.exists_units_smul_eq_of_forall_eq_zero_iff hh hker
  have hcv : ∀ w : V, f w = (c : k) * h w := fun w => by
    rw [hcf]
    rfl
  rw [hcv u, hcv v]
  ring

variable [IsAlgClosed k] (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

omit [Nontrivial V] in
/-- The section at a closed point of the line is a morphism over the ground field. -/
public theorem lineSection_comp_movingAmbientToSpec (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) :
    lineSection k V L lam hlam ≫ movingAmbientToSpec k V L =
      projectiveSpaceOfModuleToSpec k V := by
  rw [movingAmbientToSpec, ← Category.assoc, lineSection_comp_ambLine, Category.assoc,
    pointOfClosedPoint_comp, Category.comp_id]

/-- **The section carries closed points to closed points.** -/
public theorem isClosed_lineSection_base (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) {y : projectiveSpaceOfModule k V}
    (hy : IsClosed ({y} : Set (projectiveSpaceOfModule k V))) :
    IsClosed ({(lineSection k V L lam hlam).base y} : Set (movingAmbient k V L)) :=
  isClosed_singleton_image_of_isClosed_singleton (lineSection k V L lam hlam)
    (projectiveSpaceOfModuleToSpec k V) (movingAmbientToSpec k V L)
    (lineSection_comp_movingAmbientToSpec k V L lam hlam) y hy

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
