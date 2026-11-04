module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaDiagonalToProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonalEquiv
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSliceProduct

/-!
# From algebraic-space 2-fibre products back to a representable diagonal (Stacks 045G, (4) ⇒ (1))

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in groupoids
over the big fppf site of `S`. This file proves the implication from condition (4) of Stacks 045G —
the 2-fibre product over `𝒳` of any two scheme-valued points of `𝒳` is representable by an
algebraic space over `S` — to condition (1), that the diagonal `𝒳 ⟶ 𝒳 × 𝒳` is representable by
algebraic spaces, and hence the remaining implication (3) ⇒ (2).

Unlike (1) ⇒ (4), this direction is **not** a chain of equivalences: condition (4) concerns the
2-fibre product of two scheme-valued points *of two different schemes*, and condition (1) wants
the fibre of the diagonal over a single scheme `U`, which cuts out of that product the locus where
the two points of `U` agree. Spelled out over the big fppf site of `S`, writing `U` for a scheme
over `S` and `x`, `y` for two points of `𝒳` over `U`:

```text
(Sch/U)_{fppf} ×_{(x, y), 𝒳 × 𝒳, Δ} 𝒳
  ≅ (Sch/U)_{fppf} ×_{δ, (Sch/U) × (Sch/U), pr₁} ((Sch/U) × (Sch/U) ×_{𝒳 × 𝒳, Δ} 𝒳)
```

with `δ` the diagonal of `(Sch/U)_{fppf}`. That is a *fibre product*, so the proof ends with
Stacks 04T9 (`AlgebraicGeometry.isAlgebraicSpace_of_isPullback`) rather than with a transport of
equivalences, exactly as the quasi-inverse of Stacks 04SG does in
`StacksFrontier/AlgebraicGeometry/Stacks/RepresentabilitySmallerBase.lean`.

The four steps, each a known comparison of 2-fibre products over the site:

1. the point `(x, y)` of `𝒳 × 𝒳` over `U` is the diagonal of `(Sch/U)_{fppf}` followed by the
   product 1-morphism of the two slice points — on the nose, by
   `CategoryTheory.TwoFibreProductOver.sliceDiagonal_comp_prodMap`, so no reindexing is needed;
2. cancelling the middle factor (`CategoryTheory.TwoFibreProductOver.cancelMiddleEquivalenceOver`,
   Stacks 02XD) splits the left-hand side as the displayed fibre product;
3. Stacks 02XE in its equivalence form
   (`CategoryTheory.TwoFibreProductOver.prodDiagComparison`) identifies the outer factor with the
   2-fibre product of the two slice points, which condition (4) presents as an algebraic space
   over `S`, and that algebraic space replaces it
   (`CategoryTheory.TwoFibreProductOver.precomposeSnd`); the middle factor is the slice over
   `U ×_S U` (`CategoryTheory.TwoFibreProductOver.sliceProd`), hence the category of elements of a
   representable presheaf, and that presheaf replaces it
   (`CategoryTheory.TwoFibreProductOver.mapBase`);
4. a 2-fibre product of categories of elements over a category of elements is the category of
   elements of a presheaf fibre product
   (`CategoryTheory.PresheafOfCategories.toTwoFibreProduct`), and
   `CategoryTheory.PresheafOfCategories.isPullback_fibrePresheaf` exhibits that presheaf as a
   fibre product of the restriction of the algebraic space of (4) with a representable presheaf
   over the restriction of the presheaf of points of `U ×_S U` — all three algebraic spaces over
   `U`, so Stacks 04T9 applies.

Condition (2) then follows from the diagonal clause at the one point of `𝒳 × 𝒳` built out of the
chosen pullbacks of two objects of a fibre, which is what the equivalence of conditions
(1) and (2) quantifies over, so the arbitrary point of `𝒳 × 𝒳` of condition (1) never has to be
compared with a diagonal.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_of_hasAlgebraicSpaceSchemePointProducts`:
  **Stacks 045G**, condition (4) implies condition (2).
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_hasAlgebraicSpaceSchemePointProducts`:
  **Stacks 045G**, condition (4) implies condition (1).
* `AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes`:
  **Stacks 045G**, the equivalence of conditions (2) and (3).

## Implementation notes

The one step that could have needed a 2-isomorphism is step 1, and it does not:
`CategoryTheory.TwoFibreProductOver.sliceDiagonal` is built by the universal property of the
product of two copies of `𝒞/U`, whose mediating 1-morphism records the base object as
`CategoryTheory.Over.map U.hom` applied to it, and the comparison isomorphism of an object of a
product over the site is forced to be an `eqToHom`; so composing it with
`CategoryTheory.TwoFibreProductOver.prodMap` of the two slice points reproduces
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.pairFunctor` **definitionally**, the two
remaining components being `Z i` applied to
`CategoryTheory.Over.iteratedSliceForward` of `CategoryTheory.Over.iteratedSliceBackward` of an
object, and that round trip is the identity functor on the nose.

The quasi-inverses of the two comparisons that are only equivalences — the slice of the site over
`U ×_S U` versus the product of two copies of `𝒞/U`, and the 2-fibre product of the two slice
points versus the algebraic space of condition (4) — are produced by
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`, which returns only a
`Nonempty`. That is why the whole construction is one tactic proof rather than a definition
followed by lemmas about it: the representing presheaf depends on a choice of quasi-inverse.

Binary products of the site are not an instance of the ambient library; they come from fibre
products of schemes, and are supplied here by
`AlgebraicGeometry.Stack.hasBinaryProducts_bigFppfOver` as a local instance.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 04T9](https://stacks.math.columbia.edu/tag/04T9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PresheafOfCategories
open CategoryTheory.TwoFibreProductOver CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace CategoryTheory.TwoFibreProductOver

universe v₁ u₁ v₂ u₂

section SliceDiagonal

variable {A : Type u₁} [Category.{v₁} A] {X : A} (U : Over X)

/-- The diagonal of the slice `𝒞/U` of `𝒞 = A/X` at `U`, as a 1-morphism over `𝒞` into the product
of two copies of `𝒞/U`. Its source is written as the slice `A/U.left`, which the iterated-slice
equivalence identifies with `𝒞/U` and which is the shape in which the diagonal clause of
Stacks 02ZW quantifies over scheme-valued points. -/
noncomputable def sliceDiagonal :
    Over U.left ⥤ TwoFibreProductOver (Over.forget U) (Over.forget U) (𝟭 (Over X))
      (Over.forget U) (Over.forget U) :=
  lift (Over.forget U) (Over.forget U) (𝟭 (Over X)) (Over.forget U) (Over.forget U)
    (Over.map U.hom) (Over.iteratedSliceBackward U) (Over.iteratedSliceBackward U)
    rfl rfl (Iso.refl _) (fun _ => IsHomLift.id rfl)

/-- The diagonal of a slice is a 1-morphism over the base. -/
lemma sliceDiagonal_comp_structureFunctor :
    sliceDiagonal U ⋙ structureFunctor (Over.forget U) (Over.forget U) (𝟭 (Over X))
        (Over.forget U) (Over.forget U) = Over.map U.hom :=
  lift_comp_structureFunctor ..

variable {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ Over X} {Z₁ Z₂ : Over U.left ⥤ 𝒳}

/-- A point of `𝒳` over `U`, transported along the iterated-slice equivalence, is a 1-morphism
from the slice `𝒞/U` over the base. -/
lemma iteratedSliceForward_comp_eq_forget (h : Z₁ ⋙ p = Over.map U.hom) :
    (Over.iteratedSliceForward U ⋙ Z₁) ⋙ p = Over.forget U :=
  (congrArg (fun F => Over.iteratedSliceForward U ⋙ F) h).trans
    (Over.iteratedSliceForward_comp_map U)

/-- **A point of `𝒳 × 𝒳` over `U` built from two points of `𝒳` is the diagonal of `𝒞/U` followed
by the product of the two corresponding 1-morphisms out of `𝒞/U`.** This is an equality of
1-morphisms, not merely a 2-isomorphism: both sides record the base object as
`CategoryTheory.Over.map U.hom` applied to the given object, both have an `eqToHom` as comparison
isomorphism, and the two components agree because
`CategoryTheory.Over.iteratedSliceBackward` followed by
`CategoryTheory.Over.iteratedSliceForward` is the identity functor. -/
lemma sliceDiagonal_comp_prodMap (h₁ : Z₁ ⋙ p = Over.map U.hom)
    (h₂ : Z₂ ⋙ p = Over.map U.hom) :
    sliceDiagonal U ⋙ prodMap (Over.iteratedSliceForward U ⋙ Z₁)
        (Over.iteratedSliceForward U ⋙ Z₂) (iteratedSliceForward_comp_eq_forget U h₁)
        (iteratedSliceForward_comp_eq_forget U h₂) =
      DiagonalFibre.pairFunctor h₁ h₂ := rfl

end SliceDiagonal

section DiagonalFibreAsFibrePresheaf

universe v₃ u₃

variable {A : Type u₁} [Category.{v₁} A] {X A' : A} (a : A' ⟶ X)
  {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ Over X}
  {Z : Type u₃} [Category.{v₃} Z] {pZ : Z ⥤ Over X}

/-- The structure functor of the 2-fibre product of a functor fibred in groupoids with itself over
the identity is fibred in groupoids. -/
private theorem isFiberedInGroupoids_structureFunctor_self {X' : A} {q : 𝒳 ⥤ Over X'}
    (hq : q.IsFiberedInGroupoids) :
    (structureFunctor q q (𝟭 (Over X')) q q).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hq hq
    Functor.isFiberedInGroupoids_id rfl rfl

/-- The projection from the category of elements of a presheaf of sets is fibred in groupoids. -/
private theorem isFiberedInGroupoids_discreteProjection {C : Type u₁} [Category.{v₁} C]
    (P : Cᵒᵖ ⥤ Type v₁) : (discreteProjection P).IsFiberedInGroupoids :=
  (isFiberedInSetoids_discreteProjection P).isFiberedInGroupoids

/-- **The base change of the diagonal of `𝒳` along a point of `𝒳 × 𝒳` that factors through a
category of elements is the category of elements of a presheaf fibre product.**

The point of `𝒳 × 𝒳` is `δ ⋙ g` for `δ : A/A' ⥤ Z` and `g : Z ⥤ 𝒳 × 𝒳` 1-morphisms over
`𝒞 = A/X`, and `Z` is assumed to be equivalent over `𝒞` to the category of elements of a presheaf
`HW`, while the base change `Z ×_{g, 𝒳 × 𝒳, Δ} 𝒳` of the diagonal along `g` itself is assumed to be
equivalent over `𝒞` to the category of elements of a presheaf `GP`. The conclusion is that
`A/A' ×_{δ ⋙ g, 𝒳 × 𝒳, Δ} 𝒳` is, over `A/A'`, the category of elements of a presheaf on `A/A'`
which is the fibre product of the restriction of `GP` with the presheaf of points of the final
object over the restriction of `HW`.

Cancelling the middle factor (Stacks 02XD) splits the base change along `δ ⋙ g` as a 2-fibre
product of `A/A'` with `Z ×_{𝒳 × 𝒳} 𝒳` over `Z`; the two hypotheses replace the second and the
middle factor by categories of elements, and
`CategoryTheory.PresheafOfCategories.toTwoFibreProduct` turns the result into a category of
elements. -/
theorem exists_isPullback_nonempty_equivalenceOver_fst_diag
    (hp : p.IsFiberedInGroupoids) (hpZ : pZ.IsFiberedInGroupoids)
    (g : Z ⥤ TwoFibreProductOver p p (𝟭 (Over X)) p p) (hg : g ⋙ ProdP p = pZ)
    (δ : Over A' ⥤ Z) (hδ : δ ⋙ pZ = Over.map a)
    {GP : (Over X)ᵒᵖ ⥤ Type v₁}
    (c : (presheafOfCategories (GP ⋙ typeToCat)).obj ⥤
      TwoFibreProductOver pZ p (ProdP p) g (Diag p))
    (hc : c ⋙ structureFunctor pZ p (ProdP p) g (Diag p) = discreteProjection GP)
    (hcE : c.IsEquivalence)
    {HW : (Over X)ᵒᵖ ⥤ Type v₁}
    (b : Z ⥤ (presheafOfCategories (HW ⋙ typeToCat)).obj)
    (hb : b ⋙ discreteProjection HW = pZ) (hbE : b.IsEquivalence) :
    ∃ F : (Over A')ᵒᵖ ⥤ Type v₁,
      (∃ (τ : (Over.map a).op ⋙ GP ⟶ (Over.map a).op ⋙ HW)
        (ι : F ⟶ (Over.map a).op ⋙ GP) (π : F ⟶ yoneda.obj (Over.mk (𝟙 A')))
        (ρ : yoneda.obj (Over.mk (𝟙 A')) ⟶ (Over.map a).op ⋙ HW), IsPullback ι π τ ρ) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (fst (Over.map a) p (ProdP p) (δ ⋙ g) (Diag p)) (discreteProjection F)) := by
  have hpa : (Over.map a).IsFiberedInGroupoids := Functor.IsFiberedInGroupoids.over_map a
  have hpP : (ProdP p).IsFiberedInGroupoids := isFiberedInGroupoids_structureFunctor_self hp
  have hsf₀ : (structureFunctor pZ p (ProdP p) g (Diag p)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hpZ hp hpP hg rfl
  have hdpG := isFiberedInGroupoids_discreteProjection GP
  have hdpW := isFiberedInGroupoids_discreteProjection HW
  have hfst₀ : fst pZ p (ProdP p) g (Diag p) ⋙ pZ =
      structureFunctor pZ p (ProdP p) g (Diag p) := fst_comp_eq
  -- the two composite legs, and the fact that both are 1-morphisms over `𝒞`
  have hσ : (δ ⋙ b) ⋙ discreteProjection HW = Over.map a := by
    rw [Functor.assoc, hb]; exact hδ
  have hθ : ((c ⋙ fst pZ p (ProdP p) g (Diag p)) ⋙ b) ⋙ discreteProjection HW =
      discreteProjection GP := by
    rw [Functor.assoc, hb, Functor.assoc, hfst₀]; exact hc
  have hcf : (c ⋙ fst pZ p (ProdP p) g (Diag p)) ⋙ pZ = discreteProjection GP := by
    rw [Functor.assoc, hfst₀]; exact hc
  -- step 2: cancelling the middle factor
  have e2 : StacksRepresentableCFG.EquivalenceOver
      (fst (Over.map a) (structureFunctor pZ p (ProdP p) g (Diag p)) pZ δ
        (fst pZ p (ProdP p) g (Diag p)))
      (fst (Over.map a) p (ProdP p) (δ ⋙ g) (Diag p)) :=
    cancelMiddleEquivalenceOver (Over.map a) p (ProdP p) pZ δ (Diag p) g hδ hg
  -- step 3a: the outer factor replaced by the category of elements of `GP`
  let : Functor.IsEquivalence c := hcE
  obtain ⟨e3⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInGroupoids_fst_overMap_of a hdpG hpZ hδ hcf)
    (isFiberedInGroupoids_fst_overMap_of a hsf₀ hpZ hδ hfst₀)
    (precomposeSnd δ (fst pZ p (ProdP p) g (Diag p)) c hc)
    (precomposeSnd_comp_fst δ (fst pZ p (ProdP p) g (Diag p)) c hc)
    (isEquivalence_precomposeSnd hpa hdpG hsf₀ hc hfst₀)
  -- step 3b: the middle factor replaced by the category of elements of `HW`
  let : Functor.IsEquivalence b := hbE
  obtain ⟨e4⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInGroupoids_fst_overMap_of a hdpG hpZ hδ hcf)
    (isFiberedInGroupoids_fst_overMap_of a hdpG hdpW hσ hθ)
    (mapBase δ (c ⋙ fst pZ p (ProdP p) g (Diag p)) b hb)
    (mapBase_comp_fst δ (c ⋙ fst pZ p (ProdP p) g (Diag p)) b hb)
    (isEquivalence_mapBase hb)
  -- step 4: a 2-fibre product of categories of elements is a category of elements
  obtain ⟨e5⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (isFiberedInGroupoids_discreteProjection
      (twoFibreProductPresheaf (δ ⋙ b) hσ ((c ⋙ fst pZ p (ProdP p) g (Diag p)) ⋙ b) hθ))
    (isFiberedInGroupoids_fst_overMap_of a hdpG hdpW hσ hθ)
    (toTwoFibreProduct (δ ⋙ b) hσ ((c ⋙ fst pZ p (ProdP p) g (Diag p)) ⋙ b) hθ)
    (toTwoFibreProduct_comp_fst (δ ⋙ b) hσ ((c ⋙ fst pZ p (ProdP p) g (Diag p)) ⋙ b) hθ)
    (isEquivalence_toTwoFibreProduct (δ ⋙ b) hσ
      ((c ⋙ fst pZ p (ProdP p) g (Diag p)) ⋙ b) hθ)
  refine ⟨_, ⟨_, _, _, _, isPullback_fibrePresheaf
    (Functor.whiskerLeft (Over.map a).op
      (natTransOfBasedFunctor ((c ⋙ fst pZ p (ProdP p) g (Diag p)) ⋙ b) hθ))
    (sectionOfBasedFunctor (δ ⋙ b) hσ)
    (fun f => sectionOfBasedFunctor_map (δ ⋙ b) hσ f) Over.mkIdTerminal⟩,
    ⟨e2.symm.trans (e3.symm.trans (e4.trans e5.symm))⟩⟩

end DiagonalFibreAsFibrePresheaf

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local instance] hasBinaryProducts_bigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The composite of two equivalences is an equivalence, with both hypotheses explicit: the
categories here are total categories of 2-fibre products, for which instance search does not find
the `CategoryTheory.Category` instance appearing in the type. -/
private theorem isEquivalence_comp_of {A : Type*} [Category A] {A' : Type*} [Category A']
    {A'' : Type*} [Category A''] (F : A ⥤ A') (G : A' ⥤ A'')
    (hF : F.IsEquivalence) (hG : G.IsEquivalence) : (F ⋙ G).IsEquivalence :=
  ((@Functor.asEquivalence A _ A' _ F hF).trans
    (@Functor.asEquivalence A' _ A'' _ G hG)).isEquivalence_functor

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- The content of the implication (4) ⇒ (1) of Stacks 045G, stated at the one point of `𝒳 × 𝒳`
that the equivalence of conditions (1) and (2) needs: the pair of two 1-morphisms out of
the big fppf site of a scheme `U` over `S`.

Going through this form is what keeps every term stated with `CategoryTheory.Over.forget U` in
place of `(AlgebraicGeometry.Stack.schemeFibredCategory B S hS U).val.p`, the two being
definitionally equal only after unfolding `CategoryTheory.BasedCategory.ofFunctor`. -/
private theorem exists_isAlgebraicSpace_equivalenceOver_fst_pairFunctor
    (h₄ : HasAlgebraicSpaceSchemePointProducts B S hS 𝒳) (U : BigFppfOver B S hS)
    (Z₁ Z₂ : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.obj)
    (h₁ : Z₁ ⋙ 𝒳.val.p = Over.map U.hom) (h₂ : Z₂ ⋙ 𝒳.val.p = Over.map U.hom) :
    ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 F ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p (ProdP 𝒳.val.p)
            (pairFunctor h₁ h₂) (Diag 𝒳.val.p))
          (discreteProjection F)) := by
  have hp : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  have hfU : (Over.forget U).IsFiberedInGroupoids := Functor.IsFiberedInGroupoids.over_forget U
  have hpT : (Over.map U.hom).IsFiberedInGroupoids := Functor.IsFiberedInGroupoids.over_map U.hom
  have hpSP := isFiberedInGroupoids_structureFunctor_self hfU
  have hpP : (ProdP 𝒳.val.p).IsFiberedInGroupoids := isFiberedInGroupoids_structureFunctor_self hp
  -- the two slice points and the 2-fibre product of condition (4)
  have hx₁ : (Over.iteratedSliceForward U ⋙ Z₁) ⋙ 𝒳.val.p = Over.forget U :=
    iteratedSliceForward_comp_eq_forget U h₁
  have hx₂ : (Over.iteratedSliceForward U ⋙ Z₂) ⋙ 𝒳.val.p = Over.forget U :=
    iteratedSliceForward_comp_eq_forget U h₂
  have hsfP : (structureFunctor (Over.forget U) (Over.forget U) 𝒳.val.p
      (Over.iteratedSliceForward U ⋙ Z₁)
      (Over.iteratedSliceForward U ⋙ Z₂)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfU hfU hp hx₁ hx₂
  obtain ⟨GP, hGP, ⟨eP⟩⟩ := h₄ U U ⟨_, hx₁⟩ ⟨_, hx₂⟩
  -- step 3a: Stacks 02XE identifies the base change of the diagonal along the product point
  have hg : prodMap (Over.iteratedSliceForward U ⋙ Z₁) (Over.iteratedSliceForward U ⋙ Z₂)
        hx₁ hx₂ ⋙ ProdP 𝒳.val.p =
      structureFunctor (Over.forget U) (Over.forget U) (𝟭 (BigFppfOver B S hS))
        (Over.forget U) (Over.forget U) := rfl
  have hsf₀ : (structureFunctor
      (structureFunctor (Over.forget U) (Over.forget U) (𝟭 (BigFppfOver B S hS))
        (Over.forget U) (Over.forget U))
      𝒳.val.p (ProdP 𝒳.val.p)
      (prodMap (Over.iteratedSliceForward U ⋙ Z₁) (Over.iteratedSliceForward U ⋙ Z₂) hx₁ hx₂)
      (Diag 𝒳.val.p)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hpSP hp hpP hg rfl
  obtain ⟨e₀₂⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hsf₀ hsfP
    (prodDiagComparison (Over.iteratedSliceForward U ⋙ Z₁) (Over.iteratedSliceForward U ⋙ Z₂)
      hx₁ hx₂)
    (prodDiagComparison_comp_structureFunctor _ _ _ _)
    (instIsEquivalenceProdDiagComparison _ _ _ _)
  -- the algebraic space of condition (4) as the second factor
  have hc : (e₀₂.trans eP).inv.functor ⋙ structureFunctor
      (structureFunctor (Over.forget U) (Over.forget U) (𝟭 (BigFppfOver B S hS))
        (Over.forget U) (Over.forget U))
      𝒳.val.p (ProdP 𝒳.val.p)
      (prodMap (Over.iteratedSliceForward U ⋙ Z₁) (Over.iteratedSliceForward U ⋙ Z₂) hx₁ hx₂)
      (Diag 𝒳.val.p) = discreteProjection GP := (e₀₂.trans eP).inv.w
  -- the slice over `U ×_S U` as the middle factor
  obtain ⟨eSP⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (Functor.IsFiberedInGroupoids.over_forget (U ⨯ U)) hpSP (sliceProd U U)
    (sliceProd_comp_structureFunctor U U) (instIsEquivalenceSliceProd U U)
  have hb : (eSP.inv.functor ⋙ sliceToElements (U ⨯ U)) ⋙
      discreteProjection (yoneda.obj (U ⨯ U)) =
        structureFunctor (Over.forget U) (Over.forget U) (𝟭 (BigFppfOver B S hS))
          (Over.forget U) (Over.forget U) := eSP.inv.w
  have hbE : (eSP.inv.functor ⋙ sliceToElements (U ⨯ U)).IsEquivalence :=
    isEquivalence_comp_of _ _ eSP.isEquivalence_inv_functor
      (sliceElementsEquivalenceOver (U ⨯ U)).isEquivalence_hom_functor
  -- steps 2 to 4: the fibre of the diagonal as the category of elements of a presheaf fibre
  -- product on the big fppf site of `U`
  obtain ⟨F, ⟨τ, ι, π, ρ, hPB⟩, hE⟩ := exists_isPullback_nonempty_equivalenceOver_fst_diag
    U.hom hp hpSP
    (prodMap (Over.iteratedSliceForward U ⋙ Z₁) (Over.iteratedSliceForward U ⋙ Z₂) hx₁ hx₂)
    hg (sliceDiagonal U) (sliceDiagonal_comp_structureFunctor U)
    (e₀₂.trans eP).inv.functor hc (e₀₂.trans eP).isEquivalence_inv_functor
    (eSP.inv.functor ⋙ sliceToElements (U ⨯ U)) hb hbE
  -- the three inputs to Stacks 04T9
  have hH := isAlgebraicSpace_relocalizeRestrict B U.left.1 S U.left.2 hS U.hom
    (yoneda.obj (U ⨯ U)) (isAlgebraicSpace_yoneda B S hS (U ⨯ U))
  exact ⟨F, isAlgebraicSpace_of_isPullback
    (isAlgebraicSpace_relocalizeRestrict B U.left.1 S U.left.2 hS U.hom GP hGP)
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 (Over.mk (𝟙 U.left)))
    hH.isSheaf hH.diagonal_representable hPB, hE⟩

/-- **Stacks 045G, condition (4) implies condition (2).** If the 2-fibre product over `𝒳` of any
two scheme-valued points of `𝒳` is representable by an algebraic space over `S`, then every
isomorphism sheaf `Isom(x, y)` of two objects of a fibre is an algebraic space over the scheme the
fibre sits over.

The point of `𝒳 × 𝒳` the diagonal clause is applied at is the pair of the chosen-pullback
1-morphisms of `x` and of `y`, for which the presheaf of vertical morphisms is `Isom(x, y)` on the
nose; that is the same choice the equivalence of conditions (1) and (2) makes, which is why
no arbitrary point of `𝒳 × 𝒳` has to be compared with a diagonal here. -/
theorem isAlgebraicSpaceIsomPresheaf_of_hasAlgebraicSpaceSchemePointProducts
    (h₄ : HasAlgebraicSpaceSchemePointProducts B S hS 𝒳) :
    IsAlgebraicSpaceIsomPresheaf B S hS 𝒳 := by
  have hp := 𝒳.isFiberedInGroupoids
  have hpf : 𝒳.val.p.IsFibered := hp.isFibered
  dsimp only [IsAlgebraicSpaceIsomPresheaf]
  intro U x y
  have h₁ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p U x
  have h₂ := Functor.backward_pullbackSliceFunctor_comp 𝒳.val.p U y
  have hY : pairFunctor h₁ h₂ ⋙ ProdP 𝒳.val.p = Over.map U.hom := pairFunctor_comp h₁ h₂
  obtain ⟨F, hF, hE⟩ :=
    exists_isAlgebraicSpace_equivalenceOver_fst_pairFunctor B S hS 𝒳 h₄ U _ _ h₁ h₂
  refine ⟨F, hF, ?_⟩
  obtain ⟨i⟩ := (nonempty_equivalenceOver_fst_iff hp hY F).1 hE
  have c : vertHomPresheaf hp hY ≅
      (Over.iteratedSliceBackward U).op ⋙ 𝒳.val.p.isomPresheaf x y :=
    Functor.vertHomPresheafIsoIsomPresheaf 𝒳.val.p U x y hp
  exact ⟨i.symm.trans (Functor.isoWhiskerRight c uliftFunctor.{u, v})⟩

/-- **Stacks 045G, condition (4) implies condition (1).** If the 2-fibre product over `𝒳` of any
two scheme-valued points of `𝒳` is representable by an algebraic space over `S`, then the diagonal
of `𝒳` is representable by algebraic spaces. -/
theorem hasRepresentableDiagonal_of_hasAlgebraicSpaceSchemePointProducts
    (h₄ : HasAlgebraicSpaceSchemePointProducts B S hS 𝒳) :
    HasRepresentableDiagonal B S hS 𝒳 :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).2
    (isAlgebraicSpaceIsomPresheaf_of_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳 h₄)

/-- **Stacks 045G, condition (3) implies condition (2).** If every 1-morphism to `𝒳` from the
category represented by a scheme over `S` is representable by algebraic spaces, then every
isomorphism sheaf of two objects of a fibre is an algebraic space. This is the previous theorem
composed with the equivalence of conditions (3) and (4). -/
theorem isAlgebraicSpaceIsomPresheaf_of_isRepresentableFromSchemes
    (h₃ : IsRepresentableFromSchemes B S hS 𝒳) :
    IsAlgebraicSpaceIsomPresheaf B S hS 𝒳 :=
  isAlgebraicSpaceIsomPresheaf_of_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳
    ((isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳).1 h₃)

/-- **Stacks 045G, the equivalence of conditions (2) and (3).** Every isomorphism sheaf
`Isom(x, y)` of two objects of a fibre of `𝒳` is an algebraic space over the scheme the fibre sits
over if and only if every 1-morphism to `𝒳` from the category represented by a scheme over `S` is
representable by algebraic spaces. -/
@[stacks 045G "parts (2) and (3)"]
theorem isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes :
    IsAlgebraicSpaceIsomPresheaf B S hS 𝒳 ↔ IsRepresentableFromSchemes B S hS 𝒳 :=
  ⟨isRepresentableFromSchemes_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒳,
    isAlgebraicSpaceIsomPresheaf_of_isRepresentableFromSchemes B S hS 𝒳⟩

end AlgebraicGeometry.Stack

end
