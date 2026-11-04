module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Comparing two connecting morphisms through a pair of degree-one classes

Let `P → Q → R → P[1]` and `G₃ → G₂ → G₁ → G₃[1]` be distinguished triangles in a
pretriangulated category. Suppose given degree-one classes `γ : P ⟶ G₃[1]`, `e₂ : Q ⟶ G₂[1]` and
`e₁ : R ⟶ G₁[1]` making the first two squares commute:

```
  P ──→ Q ──→ R
  │γ    │e₂   │e₁
  ↓     ↓     ↓
G₃[1] → G₂[1] → G₁[1]
```

In general the third square, the one comparing the two connecting morphisms, need not commute.
It does, up to the sign the shift of a triangle introduces, once every morphism `P ⟶ G₁` is zero.
In that case `e₁` is the unique completion of the morphism of triangles given by `γ` and `e₂`,
and the completion makes the third square commute:

`δ_P ≫ γ[1] = -(e₁ ≫ ∂[1])`.

This is the triangulated core of condition (iv) of [Stacks, Tag 07YY] for deformations of an
algebraic space, as in [Stacks, Remark 0D1P]. There, `P → Q → R` is the fundamental triangle
`L_{A/A₃'} ⊗ 𝒪 → L_{𝒪/A₃'} → L_{𝒪/A}` of [Stacks, Tag 08SZ], and `G₃ → G₂ → G₁` is the
coefficient sequence `𝒪 ⊗ I₃ → 𝒪 ⊗ I₂ → 𝒪 ⊗ I₁`. The class `γ` is that of the thickening
`A₃'`, `e₂` is the class of the lift over `A₂'` read over `A₃'`, and `e₁` is the tangent class of
its restriction to `A₁' = A[I₁]`. The vanishing hypothesis holds because `L_{A/A₃'} ⊗ 𝒪` lies in
degrees `≤ -1`. The obstruction `δ_P ≫ γ[1]` of [Stacks, Tag 08V5] is then the boundary of the
tangent class, up to the sign recorded here.

## Main results

* `CategoryTheory.Pretriangulated.mor₃_comp_shift_eq_neg_comp_shift_mor₃`: the comparison of
  connecting morphisms.
* `DerivedCategory.mor₃_comp_shift_eq_neg_comp_shift_singleδ` and its degree-two `Ext` form
  `DerivedCategory.neg_shiftedHom_comp_eq_comp_singleδ`: the case needed in a derived
  category, where `T'` is the triangle of a short exact sequence of objects and the first vertex
  of `T` lies in degrees `≤ -1`. The vanishing hypothesis then comes from the t-structure.

## References

* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Comparing two connecting morphisms through degree-one classes.** For distinguished
triangles `T = (P → Q → R → P[1])` and `T' = (G₃ → G₂ → G₁ → G₃[1])`, and classes
`γ : P ⟶ G₃[1]`, `e₂ : Q ⟶ G₂[1]`, `e₁ : R ⟶ G₁[1]` making the first two squares commute,
the third square commutes up to sign as soon as every morphism `P ⟶ G₁` vanishes:
`δ_T ≫ γ[1] = -(e₁ ≫ δ_{T'}[1])`. -/
public theorem mor₃_comp_shift_eq_neg_comp_shift_mor₃
    (T : Triangle C) (hT : T ∈ distTriang C) (T' : Triangle C) (hT' : T' ∈ distTriang C)
    (γ : T.obj₁ ⟶ T'.obj₁⟦(1 : ℤ)⟧) (e₂ : T.obj₂ ⟶ T'.obj₂⟦(1 : ℤ)⟧)
    (e₁ : T.obj₃ ⟶ T'.obj₃⟦(1 : ℤ)⟧)
    (h₁ : T.mor₁ ≫ e₂ = γ ≫ T'.mor₁⟦(1 : ℤ)⟧')
    (h₂ : T.mor₂ ≫ e₁ = e₂ ≫ T'.mor₂⟦(1 : ℤ)⟧')
    (hvan : ∀ f : T.obj₁ ⟶ T'.obj₃, f = 0) :
    T.mor₃ ≫ γ⟦(1 : ℤ)⟧' = -(e₁ ≫ T'.mor₃⟦(1 : ℤ)⟧') := by
  obtain ⟨w, hw₂, hw₃⟩ := complete_distinguished_triangle_morphism T _ hT
    (Triangle.shift_distinguished T' hT' 1) γ (-e₂) (by
    change T.mor₁ ≫ (-e₂) = γ ≫ ((1 : ℤ).negOnePow • T'.mor₁⟦(1 : ℤ)⟧')
    simp [h₁])
  let w' : T.obj₃ ⟶ T'.obj₃⟦(1 : ℤ)⟧ := w
  have hw₂' : T.mor₂ ≫ w' = e₂ ≫ T'.mor₂⟦(1 : ℤ)⟧' := by
    refine hw₂.trans ?_
    change (-e₂) ≫ ((1 : ℤ).negOnePow • T'.mor₂⟦(1 : ℤ)⟧') = _
    simp
  have hw₃' : T.mor₃ ≫ γ⟦(1 : ℤ)⟧' = w' ≫ (-(T'.mor₃⟦(1 : ℤ)⟧')) := by
    refine hw₃.trans ?_
    change w' ≫ ((1 : ℤ).negOnePow • T'.mor₃⟦(1 : ℤ)⟧' ≫
      (shiftFunctorComm C 1 (1 : ℤ)).hom.app T'.obj₁) = _
    simp [shiftFunctorComm_eq_refl]
  clear_value w'
  clear hw₂ hw₃
  -- `w` and `e₁` agree after `T.mor₂`, so they differ by a morphism out of `P[1]`, which vanishes
  have hdiff : T.mor₂ ≫ (w' - e₁) = 0 := by
    rw [Preadditive.comp_sub, hw₂', h₂, sub_self]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ T hT (w' - e₁) hdiff
  have hg0 : g = 0 := by
    obtain ⟨g', rfl⟩ := (shiftFunctor C (1 : ℤ)).map_surjective g
    rw [hvan g', Functor.map_zero]
  rw [hg0, comp_zero, sub_eq_zero] at hg
  rw [hw₃', hg, Preadditive.comp_neg]

end CategoryTheory.Pretriangulated

namespace DerivedCategory

open CategoryTheory.Pretriangulated

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- **Comparing a connecting morphism with the boundary of a short exact sequence.** Let
`T = (P → Q → R → P[1])` be a distinguished triangle in `D(𝒜)` whose first vertex lies in degrees
`≤ -1`, and let `0 → G₃ → G₂ → G₁ → 0` be a short exact sequence in `𝒜` with connecting morphism
`∂ : G₁ ⟶ G₃[1]`. If classes `γ : P ⟶ G₃[1]`, `e₂ : Q ⟶ G₂[1]`, `e₁ : R ⟶ G₁[1]` make the first
two squares commute, then `δ_T ≫ γ[1] = -(e₁ ≫ ∂[1])`. -/
public theorem mor₃_comp_shift_eq_neg_comp_shift_singleδ
    (T : Triangle (DerivedCategory 𝒜)) (hT : T ∈ distTriang (DerivedCategory 𝒜))
    {S : ShortComplex 𝒜} (hS : S.ShortExact) [hP : T.obj₁.IsLE (-1)]
    (γ : T.obj₁ ⟶ ((singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧)
    (e₂ : T.obj₂ ⟶ ((singleFunctor 𝒜 0).obj S.X₂)⟦(1 : ℤ)⟧)
    (e₁ : T.obj₃ ⟶ ((singleFunctor 𝒜 0).obj S.X₃)⟦(1 : ℤ)⟧)
    (h₁ : T.mor₁ ≫ e₂ = γ ≫ ((singleFunctor 𝒜 0).map S.f)⟦(1 : ℤ)⟧')
    (h₂ : T.mor₂ ≫ e₁ = e₂ ≫ ((singleFunctor 𝒜 0).map S.g)⟦(1 : ℤ)⟧') :
    T.mor₃ ≫ γ⟦(1 : ℤ)⟧' = -(e₁ ≫ hS.singleδ⟦(1 : ℤ)⟧') :=
  mor₃_comp_shift_eq_neg_comp_shift_mor₃ T hT hS.singleTriangle hS.singleTriangle_distinguished
    γ e₂ e₁ h₁ h₂ fun f => TStructure.t.zero_of_isLE_of_isGE f (-1) 0 (by decide) inferInstance
      (show TStructure.t.IsGE ((singleFunctor 𝒜 0).obj S.X₃) 0 from inferInstance)

/-- **The comparison of connecting morphisms, in degree-two `Ext` form.** Under the hypotheses of
`mor₃_comp_shift_eq_neg_comp_shift_singleδ`, the negative of the degree-two class
`δ_T ∘ γ` is `∂ ∘ e₁`, the image of `e₁` under the connecting map of the short exact sequence.
This is the shape of condition (iv) of [Stacks, Tag 07YY] when the obstruction of the thickening
is `-(δ_T ∘ γ)` and the connecting map of `Ext` groups is composition with `∂`. -/
public theorem neg_shiftedHom_comp_eq_comp_singleδ
    (T : Triangle (DerivedCategory 𝒜)) (hT : T ∈ distTriang (DerivedCategory 𝒜))
    {S : ShortComplex 𝒜} (hS : S.ShortExact) [hP : T.obj₁.IsLE (-1)]
    (γ : ShiftedHom T.obj₁ ((singleFunctor 𝒜 0).obj S.X₁) (1 : ℤ))
    (e₂ : ShiftedHom T.obj₂ ((singleFunctor 𝒜 0).obj S.X₂) (1 : ℤ))
    (e₁ : ShiftedHom T.obj₃ ((singleFunctor 𝒜 0).obj S.X₃) (1 : ℤ))
    (h₁ : T.mor₁ ≫ e₂ = γ ≫ ((singleFunctor 𝒜 0).map S.f)⟦(1 : ℤ)⟧')
    (h₂ : T.mor₂ ≫ e₁ = e₂ ≫ ((singleFunctor 𝒜 0).map S.g)⟦(1 : ℤ)⟧') :
    -(ShiftedHom.comp (a := (1 : ℤ)) T.mor₃ γ (show (1 : ℤ) + 1 = 2 by norm_num)) =
      e₁.comp hS.singleδ (show (1 : ℤ) + 1 = 2 by norm_num) := by
  simp only [ShiftedHom.comp]
  rw [← Category.assoc, mor₃_comp_shift_eq_neg_comp_shift_singleδ T hT hS γ e₂ e₁ h₁ h₂,
    Preadditive.neg_comp, neg_neg, Category.assoc]

end DerivedCategory
