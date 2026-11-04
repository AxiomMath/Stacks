module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeInG

/-!
# The base-change comparison morphism of relative `Proj` is functorial in the base

Let `q : S'' ⟶ S'` and `g : S' ⟶ S` be morphisms of schemes, let `s`, `s'` and `s''` be relative
`Proj` situations over them, and let `Φ`, `Ψ` and `Θ` identify the graded algebra of the smaller
situation with the pullback of the graded algebra of the larger one along `g`, along `q` and
along `q ≫ g`. This file proves the **composition law**

```
relativeProjBaseChange q Ψ ≫ relativeProjBaseChange g Φ = relativeProjBaseChange (q ≫ g) Θ
```

whenever `Θ` is, degreewise, the composite of `Φ` and `Ψ` read through the canonical comparison
`q^*(g^*𝒜ₙ) ≅ (q ≫ g)^*𝒜ₙ`.

## Main definitions

* `Stacks.RelativeProj.Situation.CompBaseChangeIndex`: the type of triples
  `W'' ⊆ q⁻¹W'`, `W' ⊆ g⁻¹W` of affine opens.
* `Stacks.RelativeProj.Situation.compBaseChangeCover`: the induced cover of `relativeProj s''` by
  the charts over the first members of those triples.

## Main results

* `Stacks.RelativeProj.Situation.exists_compBaseChangeIndex`: every point of `S''` lies in the
  first member of such a triple.
* `Stacks.RelativeProj.Situation.relativeProjBaseChange_congr`: the comparison morphism depends
  on the invertibility hypothesis only through its being satisfied.
* `Stacks.RelativeProj.Situation.isIso_app_of_canHom_comp`: if `Φ` and `Ψ` are isomorphisms in a
  degree and `Θ` is their composite there, then `Θ` is an isomorphism in that degree.
* `Stacks.RelativeProj.Situation.chartBaseChangeHom_comp`: **the composition law on a chart.**
* `Stacks.RelativeProj.Situation.relativeProjBaseChange_comp`: **the composition law.**

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open HomogeneousIdeal

universe u

namespace Stacks.RelativeProj.Situation

open Stacks.AlgebraicGeometry.ModuleLimits

variable {s s' s'' : Situation.{u}} (g : s'.base ⟶ s.base) (q : s''.base ⟶ s'.base)

/-! ### The index: triples of affine opens `W'' ⊆ q⁻¹W'`, `W' ⊆ g⁻¹W` -/

/-- Triples of an affine open `W''` of `S''`, an affine open `W'` of `S'` and an affine open `W`
of `S` with `W'' ⊆ q⁻¹W'` and `W' ⊆ g⁻¹W`. -/
public abbrev CompBaseChangeIndex (g : s'.base ⟶ s.base) (q : s''.base ⟶ s'.base) : Type u :=
  {t : s''.base.affineOpens × s'.base.affineOpens × s.base.affineOpens //
    t.1.1 ≤ q ⁻¹ᵁ t.2.1.1 ∧ t.2.1.1 ≤ g ⁻¹ᵁ t.2.2.1}

/-- The first member of a triple lies in the preimage of the third along the composite. -/
public theorem CompBaseChangeIndex.le_preimage_comp (t : CompBaseChangeIndex g q) :
    t.1.1.1 ≤ (q ≫ g) ⁻¹ᵁ t.1.2.2.1 := by
  rw [Scheme.Hom.comp_preimage]
  exact fun z hz => t.2.2 (t.2.1 hz)

/-- **Every point of `S''` lies in the first member of some `t : CompBaseChangeIndex g q`.** -/
public theorem exists_compBaseChangeIndex (y : s''.base) :
    ∃ t : CompBaseChangeIndex g q, y ∈ t.1.1.1 := by
  obtain ⟨W, hW, hgy, -⟩ := Opens.isBasis_iff_nbhd.mp s.base.isBasis_affineOpens
    (show g.base (q.base y) ∈ (⊤ : s.base.Opens) from trivial)
  obtain ⟨W', hW', hqy, hle'⟩ := Opens.isBasis_iff_nbhd.mp s'.base.isBasis_affineOpens
    (show q.base y ∈ g ⁻¹ᵁ W from hgy)
  obtain ⟨W'', hW'', hy, hle''⟩ := Opens.isBasis_iff_nbhd.mp s''.base.isBasis_affineOpens
    (show y ∈ q ⁻¹ᵁ W' from hqy)
  exact ⟨⟨(⟨W'', hW''⟩, ⟨W', hW'⟩, ⟨W, hW⟩), hle'', hle'⟩, hy⟩

/-! ### The triple-indexed chart cover of the source -/

/-- The cover of `relativeProj s''` by the charts over the affine opens of `S''` that are the
first member of a triple `W'' ⊆ q⁻¹W'`, `W' ⊆ g⁻¹W` of affine opens. -/
public def compBaseChangeCover : (relativeProj s'').OpenCover :=
  Scheme.Cover.mkOfCovers (CompBaseChangeIndex g q)
    (fun t => Proj (s''.sectionRingGrading t.1.1.1)) (fun t => relativeProjChart s'' t.1.1)
    (fun x => by
      obtain ⟨t, hy⟩ := exists_compBaseChangeIndex g q (relativeProjToBase s'' x)
      obtain ⟨y, hyx⟩ := (mem_opensRange_relativeProjChart s'' t.1.1 x).mpr hy
      exact ⟨t, y, hyx⟩)

/-- The component of `compBaseChangeCover g q` at a triple is the chart over its first member. -/
@[simp] public theorem compBaseChangeCover_f (t : CompBaseChangeIndex g q) :
    (compBaseChangeCover g q).f t = relativeProjChart s'' t.1.1 := rfl

/-- **The comparison morphism depends only on the identification**: equal identifications give
equal comparison morphisms, whatever the proofs of invertibility. -/
public theorem relativeProjBaseChange_congr {Φ₁ Φ₂ : SheafOfModules.GradedAlgebra.UnitalHom
      (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra}
    (hΦ₁ : ∀ m : ℕ, IsIso (Φ₁.app (m : ℤ))) (hΦ₂ : ∀ m : ℕ, IsIso (Φ₂.app (m : ℤ)))
    (e : Φ₁ = Φ₂) :
    relativeProjBaseChange g Φ₁ hΦ₁ = relativeProjBaseChange g Φ₂ hΦ₂ := by
  subst e; rfl

/-! ### The comparison morphism on a chart, indexed by a pair of affine opens -/

variable (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ)))

/-- The restriction of the comparison morphism to the chart over an affine open `W'` of `S'`
with `W' ⊆ g⁻¹W` is the chart comparison morphism over the pair `(W, W')`. -/
public theorem relativeProjChart_comp_relativeProjBaseChange' (W : s.base.affineOpens)
    (W' : s'.base.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1) :
    relativeProjChart s' W' ≫ relativeProjBaseChange g Φ hΦ = chartBaseChangeHom g Φ hΦ W W' h :=
  relativeProjChart_comp_relativeProjBaseChange g Φ hΦ ⟨(W', W), h⟩

/-! ### The composition law -/

section Comp

variable (Ψ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback q s'.algebra) s''.algebra)
  (hΨ : ∀ m : ℕ, IsIso (Ψ.app (m : ℤ)))
  (Θ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback (q ≫ g) s.algebra) s''.algebra)

/-- **The composite identification is an isomorphism wherever the two factors are.** If, in
degree `n`, `Θ` is the composite of `Φ` and `Ψ` through the canonical comparison and `Φ` and `Ψ`
are isomorphisms, then so is `Θ`. -/
public theorem isIso_app_of_canHom_comp (n : ℕ) (hΦn : IsIso (Φ.app (n : ℤ)))
    (hΨn : IsIso (Ψ.app (n : ℤ)))
    (hcomp : canHom q g (q ≫ g) rfl (s.algebra.piece (n : ℤ)) ≫ Θ.app (n : ℤ) =
      (Scheme.Modules.pullback q).map (Φ.app (n : ℤ)) ≫ Ψ.app (n : ℤ)) :
    IsIso (Θ.app (n : ℤ)) := by
  have hiso : IsIso (canHom q g (q ≫ g) rfl (s.algebra.piece (n : ℤ)) ≫ Θ.app (n : ℤ)) := by
    rw [hcomp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ (Scheme.Modules.pullback q) (Φ.app (n : ℤ)) hΦn) hΨn
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    (canHom q g (q ≫ g) rfl (s.algebra.piece (n : ℤ))) (Θ.app (n : ℤ))
    (isIso_canHom q g (q ≫ g) rfl (s.algebra.piece (n : ℤ))) hiso

variable (hΘ : ∀ m : ℕ, IsIso (Θ.app (m : ℤ)))
  (hcomp : ∀ n : ℕ, canHom q g (q ≫ g) rfl (s.algebra.piece (n : ℤ)) ≫ Θ.app (n : ℤ) =
    (Scheme.Modules.pullback q).map (Φ.app (n : ℤ)) ≫ Ψ.app (n : ℤ))

include hcomp in
/-- **The composition law on a chart.** The chart base change along `q` followed by the chart
comparison morphism along `g` is the chart comparison morphism along `q ≫ g`. -/
public theorem chartBaseChangeHom_comp (W : s.base.affineOpens) (W' : s'.base.affineOpens)
    (W'' : s''.base.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1) (h' : W''.1 ≤ q ⁻¹ᵁ W'.1)
    (h'' : W''.1 ≤ (q ≫ g) ⁻¹ᵁ W.1) :
    AlgebraicGeometry.Proj.map (gradedBaseChange q Ψ W'.1 W''.1 h')
          (irrelevant_le_gradedBaseChange q Ψ W' W'' h' hΨ) ≫
        chartBaseChangeHom g Φ hΦ W W' h =
      chartBaseChangeHom (q ≫ g) Θ hΘ W W'' h'' := by
  rw [chartBaseChangeHom, chartBaseChangeHom, ← Category.assoc,
    ← AlgebraicGeometry.Proj.map_comp,
    AlgebraicGeometry.Proj.map_congr
      (gradedBaseChange_comp g q Φ Ψ Θ W.1 W'.1 W''.1 h h' h''
        (fun n a => pieceSectionHom_comp g q Φ Ψ Θ n (hcomp n) W.1 W'.1 W''.1 h h' h'' a)) _
      (irrelevant_le_gradedBaseChange (q ≫ g) Θ W W'' h'' hΘ)]

include hcomp in
/-- **The composition law on one chart of the triple-indexed cover**: the two morphisms out of
`relativeProj s''` agree after composing with the chart over the first member of a triple. -/
public theorem relativeProjChart_comp_relativeProjBaseChange_comp (t : CompBaseChangeIndex g q) :
    relativeProjChart s'' t.1.1 ≫ relativeProjBaseChange q Ψ hΨ ≫
        relativeProjBaseChange g Φ hΦ =
      relativeProjChart s'' t.1.1 ≫ relativeProjBaseChange (q ≫ g) Θ hΘ := by
  rw [← Category.assoc,
    relativeProjChart_comp_relativeProjBaseChange' q Ψ hΨ t.1.2.1 t.1.1 t.2.1,
    chartBaseChangeHom, Category.assoc,
    relativeProjChart_comp_relativeProjBaseChange' g Φ hΦ t.1.2.2 t.1.2.1 t.2.2,
    chartBaseChangeHom_comp g q Φ hΦ Ψ hΨ Θ hΘ hcomp t.1.2.2 t.1.2.1 t.1.1 t.2.2 t.2.1
      (CompBaseChangeIndex.le_preimage_comp g q t),
    relativeProjChart_comp_relativeProjBaseChange' (q ≫ g) Θ hΘ t.1.2.2 t.1.1
      (CompBaseChangeIndex.le_preimage_comp g q t)]

include hcomp in
/-- **The composition law for the base-change comparison morphism of relative `Proj`.**
Base-changing along `g` and then along `q` is base-changing along `q ≫ g`, for the identification
`Θ` that is degreewise the composite of `Φ` and `Ψ`. -/
public theorem relativeProjBaseChange_comp :
    relativeProjBaseChange q Ψ hΨ ≫ relativeProjBaseChange g Φ hΦ =
      relativeProjBaseChange (q ≫ g) Θ hΘ :=
  (compBaseChangeCover g q).hom_ext _ _ fun t =>
    relativeProjChart_comp_relativeProjBaseChange_comp g q Φ hΦ Ψ hΨ Θ hΘ hcomp t

end Comp

end Stacks.RelativeProj.Situation

end
