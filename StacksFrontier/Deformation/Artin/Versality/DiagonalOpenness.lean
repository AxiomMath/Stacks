module

public import StacksFrontier.Deformation.Artin.RimSchlessinger.DiagonalFibre
public import StacksFrontier.Deformation.Artin.Versality.DiagonalFibreEffective

/-!
# Openness of versality for the diagonal from strong formal effectiveness

Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in groupoids over
`(Sch/S)_{fppf}` such that

1. the second diagonal `Δ_Δ : 𝒳 ⟶ 𝒳 ×_{𝒳 × 𝒳} 𝒳` is representable by algebraic spaces,
2. `𝒳` satisfies (RS*),
3. `𝒳` is limit preserving,
4. for every inverse system `(Rₙ)` as in Stacks 0CXT whose transition kernels are square-zero
   ideals, the functor `𝒳_{Spec lim Rₙ} ⟶ lim 𝒳_{Spec Rₙ}` is fully faithful.

Then the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` satisfies openness of versality. This is Stacks 0CXV.

## Main results

* `Deformation.Artin.isOpenVersality_diagonal_of_isFullyFaithfulOnSquareZeroTowers`: under
  conditions (1)–(4) the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` satisfies openness of versality.

## Implementation notes

Openness of versality of a 1-morphism is Stacks 07XQ (2): for every scheme `V` locally of
finite type over `S` and every object `y` of the target over `V`, openness of versality holds for
`(Sch/V)_{fppf} ×_𝒴 𝒳`, as a category over the big fppf site of `V`. The conclusion is written
out in that form, over the site: `Deformation.Artin.IsOpenVersalityMorphism` asks the structure
functors to be fibred in groupoids over all schemes over `S`, which a category over a big fppf site
is not, since the objects above the cutoff of the site have no lifts.

Condition (4) is `Deformation.Artin.IsFullyFaithfulOnSquareZeroTowers`: the inverse system is
given by the spectra of its rings, a tower of affine schemes of the site over an affine open of
`S` with apex the spectrum of the limit, and full faithfulness is stated on systems of
restrictions.

## References

* [Stacks Project, Tag 0CXV](https://stacks.math.columbia.edu/tag/0CXV)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 07XQ](https://stacks.math.columbia.edu/tag/07XQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.TwoFibreProductOver CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace Deformation.Artin

universe u

/-- Every point of a scheme `V` over `S` has an affine open neighbourhood whose image lies in an
affine open of `S`. -/
theorem exists_isAffineOpenOverAffineOpen (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (V : AlgebraicGeometry.BigFppfOver B S hS)
    (v : V.left.1) :
    ∃ W : V.left.1.Opens, IsAffineOpenOverAffineOpen B S hS V W ∧ IsAffineOpen W ∧ v ∈ W := by
  let f : V.left.1 ⟶ S := B.inclusion.map V.hom
  obtain ⟨G, hG, hfv, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := f.base v) trivial
  obtain ⟨W, hW, hvW, hWG⟩ := exists_isAffineOpen_mem_and_subset (X := V.left.1)
    (U := f ⁻¹ᵁ G) (x := v) hfv
  refine ⟨W, ⟨hW, G, hG, ?_⟩, hW, hvW⟩
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact hWG w.2

/-- Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in groupoids over the big fppf
site of `S` whose second diagonal is representable by algebraic spaces, which satisfies (RS*),
which is limit preserving, and for which the restriction functors
`𝒳_{Spec lim Rₙ} ⟶ lim 𝒳_{Spec Rₙ}` of square-zero towers are fully faithful. Then the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` satisfies openness of versality: for every scheme `V` locally of finite type over
`S` and every object `y` of `𝒳 × 𝒳` over `V`, the 2-fibre product
`(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` satisfies openness of versality — an object over a scheme `U`
locally of finite type over `V` which is versal at a finite type point `u₀` is versal at every
finite type point of an open neighbourhood of `u₀`. -/
@[stacks 0CXV]
theorem isOpenVersality_diagonal_of_isFullyFaithfulOnSquareZeroTowers
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (AlgebraicGeometry.BigFppfOver B S hS))
    (h1 : AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces B S hS
      (AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor B S hS 𝒳
        (CatFiberedInGroupoids.product 𝒳 𝒳)
        (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳)))
    (h2 : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (h3 : IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (h4 : IsFullyFaithfulOnSquareZeroTowers B S hS 𝒳.val.p) :
    ∀ (V : AlgebraicGeometry.BigFppfOver B S hS), LocallyOfFiniteType (B.inclusion.map V.hom) →
      ∀ (y : AlgebraicGeometry.BigFppfOver B V.left.1 V.left.2 ⥤
          (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj),
        y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom →
        let q := TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
          (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
          (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor ⋙
            Over.post B.inclusion
        ∀ (U : Over V.left.1), LocallyOfFiniteType U.hom →
          ∀ (x : TwoFibreProductOver (Over.map V.hom) 𝒳.val.p
              (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
              (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor)
            (hx : q.obj x = U) (u₀ : U.left),
            IsFiniteTypePoint u₀ →
            IsVersalAt U q u₀ x hx →
            ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
              ∀ u ∈ W.1, IsFiniteTypePoint u → IsVersalAt U q u x hx := by
  intro V hV y hy
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
  have : LocallyOfFiniteType (B.inclusion.map V.hom) := hV
  have : IsLocallyNoetherian V.left.1 :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map V.hom)
  let p := TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
    (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
  have hp : p.IsFiberedInGroupoids :=
    AlgebraicGeometry.Stack.fst_isFiberedInGroupoids_overMap V.hom 𝒳.val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
      (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).toFunctor
      𝒳.isFiberedInGroupoids (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
      (AlgebraicGeometry.Stack.diagonalBasedFunctor B S hS 𝒳).w
  have : p.Faithful := faithful_fst
  exact isOpenVersality_of_faithful B V.left.1 V.left.2 p hp
    (satisfiesRSStar_diagonalFibre B S hS 𝒳 V y hy h2)
    (hasAgreementLoci_diagonalFibre B S hS 𝒳 V y hy h1 h3)
    (hasThickeningDescent_diagonalFibre B S hS 𝒳 V y hy h3)
    (IsAffineOpenOverAffineOpen B S hS V) (exists_isAffineOpenOverAffineOpen B S hS V)
    (hasEffectiveThickeningTowers_diagonalFibre B S hS 𝒳 V y hy h4)

end Deformation.Artin

end
