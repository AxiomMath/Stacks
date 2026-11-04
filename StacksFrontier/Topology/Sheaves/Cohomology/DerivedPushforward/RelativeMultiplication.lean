module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductOnCohomology
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductAssociativity
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.RingedSiteDerivedAssociatorToTensor

/-!
# The relative multiplication on the derived direct image of an algebra

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `K ∈ D(𝒪_X)` and
`μ : K ⊗^𝐋_{𝒪_X} K ⟶ K` a multiplication.  The *relative multiplication* is the composite

`Rf_*K ⊗^𝐋_{𝒪_Y} Rf_*K ⟶ Rf_*(K ⊗^𝐋_{𝒪_X} K) ⟶ Rf_*K`

of the relative cup product of Tag 0B68 with `Rf_*μ`, as in Differential Graded Sheaves,
Section 0FU3.  Here it is shown that

* it is associative when `μ` is (`relativeMultiplication_assoc`), for the associativity
  constraints of Tag 0FPB on `D(𝒪_X)` and `D(𝒪_Y)`; this is the associativity of the relative
  cup product, Tag 0FP4, together with its naturality;
* through the Leray identification `Hⁿ(Y, Rf_*K) = Hⁿ(X, K)` it induces the multiplication
  `Hⁱ(X, K) ⊗ Hʲ(X, K) ⟶ Hⁱ⁺ʲ(X, K)` of `μ` on cohomology, the cup product of Cohomology,
  Section 0FKU followed by `μ` (`lerayMap_relativeMultiplication_cupPairing`); this is
  `Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_relativeCupProduct_cupPairing`.

## Main definitions

* `Stacks.Cohomology.LerayCupPairing.relativeMultiplication`

## Main results

* `Stacks.Cohomology.LerayCupPairing.relativeMultiplication_assoc`
* `Stacks.Cohomology.LerayCupPairing.lerayMap_relativeMultiplication_cupPairing`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedRelativeCupProduct (relativeCupProduct derivedAssociator
  relativeCupProduct_assoc relativeCupProduct_natural)
open scoped TensorProduct CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.LerayCupPairing

attribute [local instance] HasDerivedCategory.standard

-- The pullback/pushforward development and the tensor-product development name the structure
-- sheaf of a ringed space differently, by `structureSheafRing` and by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`, as in
-- `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductAssociativity`.
attribute [local implicit_reducible] structureSheafRing

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}

/-- **The relative multiplication** `Rf_*K ⊗^𝐋 Rf_*K ⟶ Rf_*(K ⊗^𝐋 K) ⟶ Rf_*K` of a multiplication
`μ : K ⊗^𝐋 K ⟶ K` on `K ∈ D(𝒪_X)`: the relative cup product of Tag 0B68 followed by `Rf_*μ`. -/
def relativeMultiplication (μ : ((derivedTensorProductFunctor X.sheaf).obj K).obj K ⟶ K) :
    ((derivedTensorProductFunctor Y.sheaf).obj ((derivedPushforward f).obj K)).obj
        ((derivedPushforward f).obj K) ⟶ (derivedPushforward f).obj K :=
  relativeCupProduct f K K ≫ (derivedPushforward f).map μ

section Abstract

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- The uncurried bifunctor on `f ×ₘ 𝟙` is the left whiskering `(T.map f).app`. -/
theorem uncurry_map_prod_id {E : Type*} [Category* E] (T : C ⥤ D ⥤ E) {X X' : C} (f : X ⟶ X')
    (Z : D) : (Functor.uncurry.obj T).map (f ×ₘ 𝟙 Z) = (T.map f).app Z := by
  simp

/-- The uncurried bifunctor on `𝟙 ×ₘ g` is the right whiskering `(T.obj X).map g`. -/
theorem uncurry_map_id_prod {E : Type*} [Category* E] (T : C ⥤ D ⥤ E) (X : C) {Z Z' : D}
    (g : Z ⟶ Z') : (Functor.uncurry.obj T).map (𝟙 X ×ₘ g) = (T.obj X).map g := by
  simp

/-- **The relative multiplication of an associative multiplication is associative**, at the
generality of a functor `P : C ⥤ D`, bifunctors `T_C`, `T_D` with associativity constraints
`a_C`, `a_D`, and a comparison `r : T_D(PK, PM) ⟶ P(T_C(K, M))` which is natural and
associative in the sense of Tag 0FP4.  Nothing about ringed spaces is used. -/
theorem relativeMul_assoc_of_comparison (P : C ⥤ D) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (r : ∀ K M : C, TD.obj (P.obj K, P.obj M) ⟶ P.obj (TC.obj (K, M)))
    (aC : ∀ K L M : C, TC.obj (TC.obj (K, L), M) ⟶ TC.obj (K, TC.obj (L, M)))
    (aD : ∀ K L M : D, TD.obj (TD.obj (K, L), M) ⟶ TD.obj (K, TD.obj (L, M)))
    (hnat : ∀ {K K' M M' : C} (k : K ⟶ K') (m : M ⟶ M'),
      TD.map (P.map k ×ₘ P.map m) ≫ r K' M' = r K M ≫ P.map (TC.map (k ×ₘ m)))
    (hassoc : ∀ K L M : C, TD.map (r K L ×ₘ 𝟙 (P.obj M)) ≫ r (TC.obj (K, L)) M ≫
        P.map (aC K L M) =
      aD (P.obj K) (P.obj L) (P.obj M) ≫ TD.map (𝟙 (P.obj K) ×ₘ r L M) ≫ r K (TC.obj (L, M)))
    {K : C} (μ : TC.obj (K, K) ⟶ K)
    (hμ : TC.map (μ ×ₘ 𝟙 K) ≫ μ = aC K K K ≫ TC.map (𝟙 K ×ₘ μ) ≫ μ) :
    TD.map ((r K K ≫ P.map μ) ×ₘ 𝟙 (P.obj K)) ≫ r K K ≫ P.map μ =
      aD (P.obj K) (P.obj K) (P.obj K) ≫ TD.map (𝟙 (P.obj K) ×ₘ (r K K ≫ P.map μ)) ≫
        r K K ≫ P.map μ := by
  have hR := hnat μ (𝟙 K)
  have hL := hnat (𝟙 K) μ
  rw [P.map_id] at hR hL
  have hA : P.map (TC.map (μ ×ₘ 𝟙 K)) ≫ P.map μ =
      P.map (aC K K K) ≫ P.map (TC.map (𝟙 K ×ₘ μ)) ≫ P.map μ := by
    rw [← P.map_comp, ← P.map_comp, ← P.map_comp, hμ]
  have := Stacks.SheafOfModules.DerivedMonoidal.mul_assoc_of_squares _ _ _ _ _ _ _ _ _ _ _ _
    hR hL (hassoc K K K) hA
  simpa using this

end Abstract

/-- **The relative multiplication of an associative multiplication is associative**: if
`(μ ⊗ 1) ≫ μ = α ≫ (1 ⊗ μ) ≫ μ` in `D(𝒪_X)`, then `(μ_f ⊗ 1) ≫ μ_f = α ≫ (1 ⊗ μ_f) ≫ μ_f` in
`D(𝒪_Y)` for `μ_f = relativeMultiplication f μ`, where `α` is the associativity constraint of
Tag 0FPB (`derivedAssociator`) on either side.  The statement is in the uncurried spelling of the
derived tensor bifunctor, the one `relativeCupProduct_assoc` (Tag 0FP4) is stated in. -/
theorem relativeMultiplication_assoc
    (μ : ((derivedTensorProductFunctor X.sheaf).obj K).obj K ⟶ K)
    (hμ : (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map (μ ×ₘ 𝟙 K) ≫ μ =
      derivedAssociator X K K K ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map (𝟙 K ×ₘ μ) ≫ μ) :
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
        (relativeMultiplication f μ ×ₘ 𝟙 ((derivedPushforward f).obj K)) ≫
        relativeMultiplication f μ =
      derivedAssociator Y ((derivedPushforward f).obj K) ((derivedPushforward f).obj K)
          ((derivedPushforward f).obj K) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
          (𝟙 ((derivedPushforward f).obj K) ×ₘ relativeMultiplication f μ) ≫
          relativeMultiplication f μ :=
  relativeMul_assoc_of_comparison (derivedPushforward f)
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (relativeCupProduct f) (derivedAssociator X) (derivedAssociator Y)
    (fun k m => relativeCupProduct_natural f k m) (relativeCupProduct_assoc f) μ hμ

/-- **The relative multiplication induces the multiplication on cohomology**: for
`ξ ∈ Hⁱ(Y, Rf_*K)` and `η ∈ Hʲ(Y, Rf_*K)`, the Leray identification carries
`Hⁱ⁺ʲ(RΓ(Y, μ_f))(ξ ∪ η)` to `Hⁱ⁺ʲ(RΓ(X, μ))(leray ξ ∪ leray η)`, the cup product of
Section 0FKU on `X` followed by `μ`. -/
theorem lerayMap_relativeMultiplication_cupPairing
    (μ : ((derivedTensorProductFunctor X.sheaf).obj K).obj K ⟶ K) (i j : ℤ)
    (ξ : cohomologyModule ((derivedPushforward f).obj K) i)
    (η : cohomologyModule ((derivedPushforward f).obj K) j) :
    lerayMap f K (i + j)
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (relativeMultiplication f μ))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom (ξ ⊗ₜ η))) =
      ((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections X).map μ)).hom
        ((cupPairing (cupProductOnSpace X) K K i j).hom
          (lerayMap f K i ξ ⊗ₜ lerayMap f K j η)) :=
  (congrArg (lerayMap f K (i + j)) (functor_map_comp₂_apply
      (baseSections Y ⋙ DerivedCategory.homologyFunctor _ (i + j)) (relativeCupProduct f K K)
      ((derivedPushforward f).map μ) _)).trans
    ((lerayMap_naturality f μ (i + j) _).trans
      (congrArg _ (lerayCohomologyIso_relativeCupProduct_cupPairing f K K i j ξ η)))

end Stacks.Cohomology.LerayCupPairing

end
