module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementObj
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdOverBase

/-!
# A morphism of presheaves into a finite self-product over an algebraic space

The `n`-fold self-product `U ×_X ⋯ ×_X U` of an object of the spaces-étale site of `X` is a
product taken *in that site*, so its universal property is only available for morphisms whose
source is again an object of the site — that is, for étale morphisms to `X`. The surjectivity
step of [Stacks, Tag 089J] needs it for a source which is not étale over `X`: a point
`Spec K ⟶ X` together with `n` lifts of it to the chart.

This file supplies that. For `n ≥ 1` the underlying presheaf of the self-product has the
universal property of the `n`-fold fibre product over `X` of the underlying presheaf of `U`:
`n` morphisms from a presheaf `F` into the underlying presheaf of `U`, all lying over one
morphism `F ⟶ X`, assemble into a morphism `F ⟶ U ×_X ⋯ ×_X U` with those components.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.exists_lift_underlying_selfProd`: **a family of `n + 1`
  morphisms of presheaves into the underlying presheaf of `U`, lying over one morphism to `X`,
  lifts to the underlying presheaf of the `(n + 1)`-fold self-product over `X`**, with those
  morphisms as its components and lying over the same morphism to `X`.

## What is and is not proved

No declaration here carries a Stacks attribute. The statement is the universal property of the
product `Stacks.FinProd` iterated through
`AlgebraicGeometry.Space.SpacesEtale.isPullback_selfProdSucc`, which already says that the
underlying presheaf of a self-product with one more factor is the fibre product over `X` of the
underlying presheaf of `U` with the underlying presheaf of the smaller self-product.

**The empty self-product is excluded.** It is a final object of the spaces-étale site of `X`,
whose underlying presheaf is `X` itself only up to the isomorphism given by terminality; the
induction below therefore starts at one factor, identified with `U` by
`CategoryTheory.Limits.productUniqueIso`.

Nothing about [Stacks, Tag 089J] is proved here. In particular the lift produced below is not
yet shown to land in the complement of the diagonals: that needs the `n` morphisms to be
pairwise distinct *and* a descent of that distinctness through the point-set description of the
collision locus.

## References

* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **A family of `n + 1` morphisms of presheaves into the underlying presheaf of `U`, lying
over one morphism to `X`, lifts to the underlying presheaf of the `(n + 1)`-fold self-product
of `U` over `X`.**

The induction peels the zeroth factor. One factor is `U` itself, by
`CategoryTheory.Limits.productUniqueIso`; a self-product with one more factor is the fibre
product over `X` of `U` with the previous self-product, by
`AlgebraicGeometry.Space.SpacesEtale.isPullback_selfProdSucc`, and the lift is the one the
cartesian square provides, the required compatibility being that both the zeroth morphism and
the inductive lift lie over the same morphism to `X`.

The source `F` is an arbitrary presheaf: it is *not* required to be étale over `X`, which is
the whole point — in [Stacks, Tag 089J] it is the presheaf represented by the spectrum of a
field. -/
theorem exists_lift_underlying_selfProd (U : SpacesEtale B S hS X)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ξ : F ⟶ X.obj) :
    ∀ (n : ℕ) (v : Fin (n + 1) → (F ⟶ (underlying B S hS X U).obj)),
      (∀ k, v k ≫ U.obj.hom.hom = ξ) →
      ∃ f : F ⟶ (underlying B S hS X (selfProd B S hS X U (n + 1))).obj,
        (∀ k, f ≫ ((toSpaces B S hS X).map (Pi.π (fun _ : Fin (n + 1) ↦ U) k)).hom = v k) ∧
          f ≫ (selfProd B S hS X U (n + 1)).obj.hom.hom = ξ
  | 0, v, hv => by
      refine ⟨v 0 ≫ ((toSpaces B S hS X).map
        (productUniqueIso (fun _ : Fin 1 ↦ U)).inv).hom, fun k ↦ ?_, ?_⟩
      · rw [Category.assoc, ← hom_toSpaces_map_comp]
        simp only [productUniqueIso_inv_π]
        simp only [eqToHom_refl]
        exact congrArg v (Fin.fin_one_eq_zero k).symm
      · rw [Category.assoc, hom_toSpaces_map_comp_structure, hv 0]
  | n + 1, v, hv => by
      obtain ⟨g, hg, hgx⟩ :=
        exists_lift_underlying_selfProd U ξ n (fun k ↦ v k.succ) fun k ↦ hv k.succ
      refine ⟨(isPullback_selfProdSucc B S hS X U (n + 1)).lift (v 0) g
        (by rw [hv 0, hgx]), fun k ↦ ?_, ?_⟩
      · refine Fin.cases ?_ (fun k ↦ ?_) k
        · exact (isPullback_selfProdSucc B S hS X U (n + 1)).lift_fst _ _ _
        · rw [← selfProdTail_comp_π B S hS X U (n + 1) k, hom_toSpaces_map_comp,
            ← Category.assoc, (isPullback_selfProdSucc B S hS X U (n + 1)).lift_snd]
          exact hg k
      · rw [← hom_toSpaces_map_comp_structure B S hS X (Pi.π (fun _ : Fin (n + 2) ↦ U) 0),
          ← Category.assoc, (isPullback_selfProdSucc B S hS X U (n + 1)).lift_fst]
        exact hv 0

end AlgebraicGeometry.Space.SpacesEtale

end
