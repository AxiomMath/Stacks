module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne
public import StacksFrontier.AlgebraicGeometry.ClosedSupportFiniteness.Basic
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Fibres of a compactified fibration over rational points

Let `j' : U ⟶ W` be an open immersion, `ḡ : W ⟶ P` a morphism and `y : Spec k ⟶ P` a rational
point of a scheme `P` over a field `k`. Write `W_y = W ×_P Spec k` for the fibre of `ḡ` over `y`
and `U_y = U ×_W W_y` for the fibre of `j' ≫ ḡ`, with the open immersion `j'_y : U_y ⟶ W_y`.
The rational points of `U_y` are the rational points of `U` lying over `y`, and the rational points
of `U` are the disjoint union, over `y ∈ P(k)`, of those of the `U_y`. This is the bookkeeping of
the fibration step of the trace formula in any dimension, [Stacks, Tag 03UI] (1).

## Main definitions

* `Stacks.EtaleCohomology.rationalPointsFibreEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {U W P : Scheme.{u}} (j' : U ⟶ W) (gb : W ⟶ P)
  (πP : P ⟶ Spec (.of k)) (fU : U ⟶ Spec (.of k)) (hfU : j' ≫ gb ≫ πP = fU)
  (y : Spec (.of k) ⟶ P) (hy : y ≫ πP = 𝟙 _)

/-- The fibre `U_y = U ×_W (W ×_P Spec k)` of `j' ≫ ḡ` over `y`. -/
abbrev fibreScheme : Scheme.{u} := pullback j' (pullback.fst gb y)

/-- The structure morphism `U_y ⟶ Spec k`. -/
abbrev fibreStructure : fibreScheme j' gb y ⟶ Spec (.of k) :=
  pullback.snd j' (pullback.fst gb y) ≫ pullback.snd gb y

include hfU hy in
/-- **The rational points of `U_y` are the rational points of `U` over `y`.** -/
def rationalPointsFibreEquiv :
    rationalPoints (fibreStructure j' gb y) ≃ {x : rationalPoints fU // x.1 ≫ j' ≫ gb = y} where
  toFun x' :=
    have hx : (x'.1 ≫ pullback.fst j' (pullback.fst gb y)) ≫ j' ≫ gb = y := by
      have h : x'.1 ≫ pullback.snd j' (pullback.fst gb y) ≫ pullback.snd gb y = 𝟙 _ := x'.2
      simp only [Category.assoc, pullback.condition_assoc, pullback.condition, reassoc_of% h]
    ⟨⟨x'.1 ≫ pullback.fst _ _, by simp only [← hfU, Category.assoc, reassoc_of% hx, hy]⟩, hx⟩
  invFun x := ⟨pullback.lift x.1.1 (pullback.lift (x.1.1 ≫ j') (𝟙 _)
      (by rw [Category.id_comp, Category.assoc, x.2])) (by rw [pullback.lift_fst]), by
      rw [fibreStructure, pullback.lift_snd_assoc, pullback.lift_snd]⟩
  left_inv x' := by
    apply Subtype.ext
    have h : x'.1 ≫ pullback.snd j' (pullback.fst gb y) ≫ pullback.snd gb y = 𝟙 _ := x'.2
    change pullback.lift _ _ _ = x'.1
    refine pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst, Category.assoc,
        Category.assoc, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc, h]
  right_inv x := Subtype.ext (Subtype.ext (pullback.lift_fst _ _ _))

omit [Field k] in
/-- **The fibres of `g ≫ ι` have dimension at most one** when `ι` is injective on points and all
fibres of `g` have dimension at most one. -/
theorem topologicalKrullDim_comp_fiber_le_one {S : Scheme.{u}} (g : U ⟶ S) (ι : S ⟶ P)
    (hι : Function.Injective ι.base) (hfib : ∀ z, topologicalKrullDim (g.fiber z) ≤ 1) (t : P) :
    topologicalKrullDim ((g ≫ ι).fiber t) ≤ 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ ((g ≫ ι).fiberHomeo t).isHomeomorph]
  change topologicalKrullDim (g.base ⁻¹' (ι.base ⁻¹' {t})) ≤ 1
  rcases ((Set.subsingleton_singleton (a := t)).preimage hι).eq_empty_or_singleton with h | ⟨z, h⟩
  · rw [h, Set.preimage_empty, (topologicalKrullDim_eq_bot_iff_isEmpty _).2 (by simp)]
    exact bot_le
  · rw [h, ← IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo z).isHomeomorph]
    exact hfib z

include hy in
/-- **The fibre `U_y` has dimension at most one** when `j' ≫ ḡ` factors as `g ≫ ι` with `ι`
injective on points and all fibres of `g` of dimension at most one. -/
theorem topologicalKrullDim_fibreScheme_le_one {S : Scheme.{u}} (g : U ⟶ S) (ι : S ⟶ P)
    (hι : Function.Injective ι.base) (hψ : j' ≫ gb = g ≫ ι)
    (hfib : ∀ z, topologicalKrullDim (g.fiber z) ≤ 1) :
    topologicalKrullDim (fibreScheme j' gb y) ≤ 1 := by
  have : IsClosedImmersion y := isClosedImmersion_of_comp_eq_id πP y hy
  let t : P := y.base (Classical.arbitrary _)
  have hsub : Set.range (pullback.fst j' (pullback.fst gb y)).base ⊆ (g ≫ ι).base ⁻¹' {t} := by
    rintro _ ⟨v, rfl⟩
    have h1 : (pullback.fst j' (pullback.fst gb y) ≫ g ≫ ι).base v =
        (pullback.snd j' (pullback.fst gb y) ≫ pullback.snd gb y ≫ y).base v := by
      rw [← hψ, pullback.condition_assoc, pullback.condition]
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg y.base (Subsingleton.elim _ _)
  refine (topologicalKrullDim_le_of_range_subset _ _ hsub).trans ?_
  rw [← IsHomeomorph.topologicalKrullDim_eq _ ((g ≫ ι).fiberHomeo t).isHomeomorph]
  exact topologicalKrullDim_comp_fiber_le_one g ι hι hfib t

/-- **The compactification of the fibre**: `U_y ⟶ W_y` is an open immersion and `W_y` is proper
over `k` when `W` is proper over `P`. -/
def fibreCompactification [IsOpenImmersion j'] [IsProper gb] :
    CompactificationOf (Over.mk (fibreStructure j' gb y)) :=
  ⟨StructuredArrow.mk (Y := Over.mk (pullback.snd gb y))
      (Over.homMk (U := Over.mk (fibreStructure j' gb y))
        (pullback.snd j' (pullback.fst gb y)) rfl),
    ⟨(inferInstance : IsOpenImmersion (pullback.snd j' (pullback.fst gb y))),
      (inferInstance : IsProper (pullback.snd gb y))⟩⟩

end Stacks.EtaleCohomology

end
