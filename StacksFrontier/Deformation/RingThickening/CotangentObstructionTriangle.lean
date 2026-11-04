module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Cotangent.Triangle.ProductDescent
public import StacksFrontier.Deformation.RingThickening.CotangentAutomorphisms

/-!
# The fundamental triangle of `A' → A → B` and the obstruction class

Let `A' → A → B` be ring maps and `N` a `B`-module. The fundamental triangle of Tag 08QX,

`L_{A/A'} ⊗^𝐋_A B ⟶ L_{B/A'} ⟶ L_{B/A} ⟶ (L_{A/A'} ⊗^𝐋_A B)[1]`,

moved into the module universe in which `Ext^i_B(L_{B/A}, N)` is taken, gives for every class
`η ∈ Ext¹_B(L_{A/A'} ⊗^𝐋_A B, N)` a class `obstructionOf η ∈ Ext²_B(L_{B/A}, N)`, its image under
the connecting map of the long exact sequence of `Ext_B(-, N)`. It vanishes exactly when `η`
comes from `Ext¹_B(L_{B/A'}, N)`. This is the last step of the proof of Tag 08SP, part (1).

## Main definitions

* `Stacks.Deformation.SquareZeroExtensionProblem.liftedFundamentalTriangle`: the fundamental
  triangle of `A' → A → B`, in the module universe of `cotangentExt`.
* `Stacks.Deformation.SquareZeroExtensionProblem.obstructionOf`: the connecting map
  `Ext¹_B(L_{A/A'} ⊗^𝐋_A B, N) → Ext²_B(L_{B/A}, N)`.

## Main results

* `Stacks.exists_eq_mor₁_comp_iff`: in a distinguished triangle `X → Y → Z → X[1]`, a map
  `X → W` extends along `X → Y` exactly when its composite with `Z → X[1]` vanishes.
* `Stacks.Deformation.SquareZeroExtensionProblem.obstructionOf_eq_zero_iff`.

## Implementation notes

The three rings are taken in one universe, as Proposition 08QX is. The triangle lives in the
derived category of `ModuleCat.{u} B`, while the `Ext` groups of `cotangentExt` are taken in
`ModuleCat.{max u u₄} B`; the universe lift is an exact functor, so its derived functor carries
the distinguished triangle to a distinguished triangle.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u u₄

namespace Stacks

/-- **Exactness of `Hom(Y, W) → Hom(X, W) → Hom(Z[-1], W)`.** In a distinguished triangle
`X → Y → Z → X[1]` of a pretriangulated category, a map `η : X → W` factors through `X → Y`
exactly when its shift, composed with `Z → X[1]`, vanishes. -/
theorem exists_eq_mor₁_comp_iff {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {W : C} (η : T.obj₁ ⟶ W) :
    (∃ ζ : T.obj₂ ⟶ W, η = T.mor₁ ≫ ζ) ↔ T.mor₃ ≫ η⟦(1 : ℤ)⟧' = 0 := by
  constructor
  · rintro ⟨ζ, rfl⟩
    rw [Functor.map_comp, ← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]
  · intro h
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT) (η⟦(1 : ℤ)⟧') h
    let g' : (shiftFunctor C (1 : ℤ)).obj T.obj₂ ⟶ (shiftFunctor C (1 : ℤ)).obj W := g
    have hg' : η⟦(1 : ℤ)⟧' = T.mor₁⟦(1 : ℤ)⟧' ≫ (-g') := by
      rw [hg, Triangle.rotate_mor₃]
      exact (Preadditive.neg_comp _ _).trans (Preadditive.comp_neg _ _).symm
    refine ⟨(shiftFunctor C (1 : ℤ)).preimage (-g'),
      (shiftFunctor C (1 : ℤ)).map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage, hg']

namespace Deformation.SquareZeroExtensionProblem

attribute [local instance high] HasDerivedCategory.standard

variable (S : SquareZeroExtensionProblem.{u, u, u, u₄})

/-- The universe lift `D(ModuleCat.{u} B) ⥤ D(ModuleCat.{max u u₄} B)`, the derived functor of the
exact functor `ModuleCat.uliftFunctor`. -/
noncomputable abbrev liftDerived :
    DerivedCategory (ModuleCat.{u} S.B) ⥤ DerivedCategory (ModuleCat.{max u u₄} S.B) :=
  (ModuleCat.uliftFunctor.{u₄} S.B).mapDerivedCategory

/-- The fundamental triangle `L_{A/A'} ⊗^𝐋_A B ⟶ L_{B/A'} ⟶ L_{B/A} ⟶ (L_{A/A'} ⊗^𝐋_A B)[1]` of
Proposition 08QX for the tower `A' → A → B`, in `D(ModuleCat.{u} B)`. -/
noncomputable abbrev fundamentalTriangle :
    Triangle (DerivedCategory (ModuleCat.{u} S.B)) :=
  Triangle.mk (CommAlgCat.fundamentalMor₁.{u} S.A' S.A S.B)
    (CommAlgCat.fundamentalMor₂.{u} S.A' S.A S.B)
    (CommAlgCat.productFundamentalMor₃ S.A' S.A S.B)

/-- The fundamental triangle of `A' → A → B` is distinguished: this is Proposition 08QX. -/
theorem fundamentalTriangle_distinguished :
    S.fundamentalTriangle ∈ distTriang (DerivedCategory (ModuleCat.{u} S.B)) :=
  CommAlgCat.productFundamentalTriangle_distinguished S.A' S.A S.B

/-- The fundamental triangle of `A' → A → B`, moved into `D(ModuleCat.{max u u₄} B)`, where the
`Ext` groups of `cotangentExt` are taken. -/
noncomputable abbrev liftedFundamentalTriangle :
    Triangle (DerivedCategory (ModuleCat.{max u u₄} S.B)) :=
  S.liftDerived.mapTriangle.obj S.fundamentalTriangle

/-- The lifted fundamental triangle is distinguished, the universe lift being exact. -/
theorem liftedFundamentalTriangle_distinguished :
    S.liftedFundamentalTriangle ∈ distTriang (DerivedCategory (ModuleCat.{max u u₄} S.B)) :=
  S.liftDerived.map_distinguished _ S.fundamentalTriangle_distinguished

/-- The third vertex of the lifted fundamental triangle is the lifted cotangent complex
`L_{B/A}` out of which `cotangentExt` is taken. -/
noncomputable def liftedFundamentalTriangleObj₃Iso :
    S.liftedFundamentalTriangle.obj₃ ≅
      DerivedCategory.Q.obj (liftedCotangentComplex.{u, u, u₄, u} S) :=
  (ModuleCat.uliftFunctor.{u₄} S.B).mapDerivedCategoryFactors.app
    (CommAlgCat.cotangentComplex S.A (CommAlgCat.of S.A S.B))

/-- **The connecting map `Ext¹_B(L_{A/A'} ⊗^𝐋_A B, N) → Ext²_B(L_{B/A}, N)`** of the long exact
sequence of `Ext_B(-, N)` attached to the fundamental triangle of `A' → A → B`. -/
noncomputable def obstructionOf
    (η : S.liftedFundamentalTriangle.obj₁ ⟶ (liftedKernelSingle.{u, u, u₄, u} S)⟦(1 : ℤ)⟧) :
    cotangentExt.{u, u, u₄, u} S 2 :=
  S.liftedFundamentalTriangleObj₃Iso.inv ≫ S.liftedFundamentalTriangle.mor₃ ≫ η⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd' (DerivedCategory (ModuleCat.{max u u₄} S.B)) (1 : ℤ) 1 2 rfl).inv.app
      (liftedKernelSingle.{u, u, u₄, u} S)

/-- **Exactness at `Ext¹_B(L_{A/A'} ⊗^𝐋_A B, N)`.** The connecting map kills a class exactly when
it comes from `Ext¹_B(L_{B/A'}, N)` by precomposition with the first morphism of the triangle. -/
theorem obstructionOf_eq_zero_iff
    (η : S.liftedFundamentalTriangle.obj₁ ⟶ (liftedKernelSingle.{u, u, u₄, u} S)⟦(1 : ℤ)⟧) :
    S.obstructionOf η = 0 ↔
      ∃ ζ : S.liftedFundamentalTriangle.obj₂ ⟶ (liftedKernelSingle.{u, u, u₄, u} S)⟦(1 : ℤ)⟧,
        η = S.liftedFundamentalTriangle.mor₁ ≫ ζ := by
  rw [exists_eq_mor₁_comp_iff _ S.liftedFundamentalTriangle_distinguished, obstructionOf]
  constructor
  · intro h
    rw [← cancel_epi S.liftedFundamentalTriangleObj₃Iso.inv, comp_zero,
      ← cancel_mono ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{max u u₄} S.B))
        (1 : ℤ) 1 2 rfl).inv.app (liftedKernelSingle.{u, u, u₄, u} S)), zero_comp]
    simpa only [Category.assoc] using h
  · intro h
    rw [reassoc_of% h, zero_comp, comp_zero]

end Deformation.SquareZeroExtensionProblem

end Stacks

end
