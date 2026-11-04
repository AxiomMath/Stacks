module

public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant

/-!
# Intersection numbers are invariant under isomorphisms

Let `k` be a field and let `g : Y ⟶ X` be an isomorphism of integral schemes proper over `k`,
compatible with the structure morphisms.  Then for invertible `𝒪_X`-modules `𝓛_1, …, 𝓛_d`,
`d = dim Y`,

`(g^*𝓛_1 ⋯ g^*𝓛_d · Y) = (𝓛_1 ⋯ 𝓛_d · X)`.

This is the special case of [Stacks, Tag 0BET] in which the morphism is an isomorphism: the
scheme-theoretic image of `Y` is all of `X` and the degree of `g` is one.  The case `Y = X`
says that the intersection numbers on a proper variety are invariant under its automorphisms
over `k`.

## Main results

* `AlgebraicGeometry.degreeOver_eq_one_of_isIso`: an isomorphism of integral schemes has
  degree one.
* `AlgebraicGeometry.intersectionNumber_pullback_of_isIso`: the invariance of intersection
  numbers under an isomorphism over `k`.

## References

* [Stacks Project, Tag 0BET](https://stacks.math.columbia.edu/tag/0BET)
* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **An isomorphism of integral schemes has degree one**: the extension of function fields it
induces is bijective. -/
public theorem degreeOver_eq_one_of_isIso {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIntegral Y]
    [IsIntegral X] [IsIso g] [LocallyOfFiniteType g] [IsDominant g] :
    degreeOver g = 1 := by
  let : Algebra X.functionField Y.functionField := (dominantFunctionFieldMap g).toAlgebra
  rw [degreeOver_eq_finrank g rfl]
  have hb : Function.Bijective (algebraMap X.functionField Y.functionField) :=
    bijective_dominantFunctionFieldMap_of_isIso g
  exact (AlgEquiv.ofBijective (Algebra.ofId X.functionField Y.functionField)
    hb).toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self _)

/-- **Intersection numbers are invariant under an isomorphism over the base field.**  Let `k`
be a field, let `g : Y ⟶ X` be an isomorphism of schemes proper over `k` with `g ≫ p_X = p_Y`,
let `Y` be integral of dimension `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  Then

`(g^*𝓛_1 ⋯ g^*𝓛_d · Y) = (𝓛_1 ⋯ 𝓛_d · X)`.

This is [Stacks, Tag 0BET] for the isomorphism `g`: the scheme-theoretic image of `Y` is the
whole of `X`, and the degree of `g` is one by `AlgebraicGeometry.degreeOver_eq_one_of_isIso`. -/
public theorem intersectionNumber_pullback_of_isIso (k : Type u) [Field k] {Y X : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k)) [IsProper pY] [IsProper pX]
    (g : Y ⟶ X) [IsIso g] (hg : g ≫ pX = pY) [IsIntegral Y] (d : ℕ)
    (hY : topologicalKrullDim Y = (d : WithBot ℕ∞)) (hX : topologicalKrullDim X ≤ d)
    (L : Fin d → X.Modules) [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    intersectionNumber k pY (𝟙 Y) d hY.le (fun j => (Scheme.Modules.pullback g).obj (L j)) =
      intersectionNumber k pX (𝟙 X) d hX L := by
  have : IsIntegral X := IsIntegral.of_isIso g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : IsDominant g := (isDominant_iff g).mpr
    (Function.Surjective.denseRange g.homeomorph.surjective)
  have : Surjective (𝟙 Y ≫ g) := by
    rw [Category.id_comp]; exact ⟨g.homeomorph.surjective⟩
  have : Surjective (𝟙 Y ≫ g).imageι := surjective_imageι (𝟙 Y ≫ g)
  have : IsIso (𝟙 Y ≫ g).imageι :=
    isIso_of_isClosedImmersion_of_surjective (𝟙 Y ≫ g).imageι
  have : IsIntegral (𝟙 Y ≫ g).image := Stacks.Chow.isIntegral_image (𝟙 Y ≫ g)
  have : IsProper (𝟙 Y ≫ g).toImage := Stacks.Chow.isProper_toImage (𝟙 Y ≫ g)
  have hXd : topologicalKrullDim X = (d : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq g (g.homeomorph.isHomeomorph)).symm.trans hY
  have hIm : topologicalKrullDim (𝟙 Y ≫ g).image = (d : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq (𝟙 Y ≫ g).imageι
      (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨(𝟙 Y ≫ g).imageι.isEmbedding, (𝟙 Y ≫ g).imageι.surjective⟩)).trans hXd
  have hpull := intersectionNumber_pullback_eq_degreeOver_mul k pY pX g hg (𝟙 Y) d hY L hIm
  have hdeg : degreeOver (𝟙 Y ≫ g).toImage = 1 := by
    rw [← degreeOver_eq_degreeOver_of_isIso g (𝟙 Y ≫ g).toImage (𝟙 Y ≫ g).imageι
      ((𝟙 Y ≫ g).toImage_imageι.trans (Category.id_comp g))]
    exact degreeOver_eq_one_of_isIso g
  have hint : intersectionNumber k pX (𝟙 Y ≫ g).imageι d hIm.le L =
      intersectionNumber k pX (𝟙 X) d hX L :=
    intersectionNumber_eq_intersectionNumber_id k pX (𝟙 Y ≫ g).imageι d hIm.le hX L
  rw [hpull, hdeg, hint, Nat.cast_one, one_mul]

end AlgebraicGeometry

end
