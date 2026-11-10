module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PostcomposeCospan

/-!
# 2-commutative squares in a strict 2-category, and the canonical comparison

The 2-category `CategoryTheory.CatFiberedInGroupoids` of categories fibred in groupoids over a base
category is *strict*: composition of 1-morphisms is associative and unital on the nose, and every
associator and unitor is an identity 2-cell. This file states the compatibility square of a
pre-morphism of 2-commutative squares and the filler of a square over a postcomposed cospan in
their associator-free forms, and compares any route out of a 2-commutative square with the
canonical comparison of that square into the canonical 2-fibre product.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.preHomOfStrict`: a pre-morphism of 2-commutative squares
  from the associator-free compatibility square.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.postcompose_iso_hom_strict`: the associator-free filler of
  a square read over a postcomposed cospan.
* `CategoryTheory.CatFiberedInGroupoids.twoIso_canonicalPreHom`: the canonical comparison of a
  square with the canonical 2-fibre product is 2-isomorphic to any route out of that square,
  compatibly with the route's own comparison 2-cells.

## Implementation notes

The associators of this 2-category are identities by `rfl` but cannot be rewritten out of a goal:
the motive is not type-correct, and the two instance paths to the hom-quiver of an induced
bicategory (`CategoryTheory.Bicategory.InducedBicategory.bicategory` and its `CategoryStruct`) are
definitionally but not syntactically equal. The strict statements are therefore proved by writing
the goal out with `change`, each associator replaced by an identity 2-cell placed at the syntactic
source or target of the factor it cancels against, and supplying whole-composite cancellations
as terms.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒰 𝒱 𝒳 𝒴 𝒜 𝒞 : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

/-- **A pre-morphism of 2-commutative squares from the associator-free compatibility square
(Stacks 003O).** In the strict 2-category of categories fibred in groupoids the two associators of
the compatibility square of Stacks 003O are identity 2-cells, so the condition on a 1-morphism `k`
of apexes and comparison 2-cells `αf`, `αs` is the three-factor identity below. -/
def preHomOfStrict {p : 𝒰 ⟶ 𝒳} {q : 𝒱 ⟶ 𝒳} {T S : Bicategory.TwoCommSq p q}
    (k : T.pt ⟶ S.pt) (αf : T.fst ≅ k ≫ S.fst) (αs : T.snd ≅ k ≫ S.snd)
    (h : T.iso.hom ≫ αs.hom ▷ q = αf.hom ▷ p ≫ k ◁ S.iso.hom) :
    Bicategory.TwoCommSq.PreHom T S where
  hom := k
  isoFst := αf
  isoSnd := αs
  compat := by
    change T.iso.hom ≫ (αs.hom ▷ q) ≫ 𝟙 ((k ≫ S.snd) ≫ q)
        = (αf.hom ▷ p) ≫ 𝟙 (k ≫ S.fst ≫ p) ≫ (k ◁ S.iso.hom)
    simp only [Category.comp_id]
    exact (Category.id_comp (k ◁ S.iso.hom)).symm ▸ h

/-- **The filler of a square read over a postcomposed cospan, associator-free.** The filler of
`CategoryTheory.Bicategory.TwoCommSq.postcompose` is the composite of the first comparison 2-cell
of the cospan whiskered by the first leg, the given filler whiskered by the comparison 1-morphism,
and the second comparison 2-cell whiskered by the second leg. -/
theorem postcompose_iso_hom_strict {F : 𝒰 ⟶ 𝒳} {G : 𝒱 ⟶ 𝒳}
    (Z : Bicategory.TwoCommSq F G) (f : 𝒳 ⟶ 𝒴)
    {p : 𝒜 ⟶ 𝒴} {q : 𝒞 ⟶ 𝒴} (σ : 𝒰 ⟶ 𝒜) (τ : 𝒱 ⟶ 𝒞)
    (ε : σ ≫ p ≅ F ≫ f) (δ : τ ≫ q ≅ G ≫ f) :
    (Z.postcompose f σ τ ε δ).iso.hom
      = (Z.fst ◁ ε.hom) ≫ (Z.iso.hom ▷ f) ≫ (Z.snd ◁ δ.inv) := by
  change 𝟙 (Z.fst ≫ σ ≫ p) ≫ (Z.fst ◁ ε.hom) ≫ 𝟙 (Z.fst ≫ F ≫ f) ≫
      (Z.iso.hom ▷ f) ≫ 𝟙 ((Z.snd ≫ G) ≫ f) ≫ (Z.snd ◁ δ.inv) ≫ 𝟙 (Z.snd ≫ τ ≫ q) = _
  simp only [Category.id_comp]
  exact congrArg (fun t => (Z.fst ◁ ε.hom) ≫ (Z.iso.hom ▷ f) ≫ t)
    (Category.comp_id (Z.snd ◁ δ.inv))

/-- **A route out of a 2-commutative square is 2-isomorphic to the canonical comparison of that
square with the canonical 2-fibre product (Stacks 003Q).** Let `X` and `Y` be 2-commutative squares
over one cospan and let `w` be a pre-morphism `X ⟶ Y` (Stacks 003O). Then the canonical comparison
of `X` with the canonical 2-fibre product `𝒰 ×_𝒳 𝒱` is 2-isomorphic to `w` followed by the
canonical comparison of `Y`, by a 2-isomorphism inducing `w`'s own two comparison 2-cells. -/
theorem twoIso_canonicalPreHom (p : 𝒰 ⟶ 𝒳) (q : 𝒱 ⟶ 𝒳)
    {X Y : Bicategory.TwoCommSq p q} (w : Bicategory.TwoCommSq.PreHom X Y) :
    ∃ θ : (canonicalPreHom.{v₁, v₂, u₁, u₂} p q X).hom
        ≅ w.hom ≫ (canonicalPreHom.{v₁, v₂, u₁, u₂} p q Y).hom,
      θ.hom ▷ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).fst = w.isoFst.hom ∧
      θ.hom ▷ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd = w.isoSnd.hom := by
  obtain ⟨θ, h₁, h₂⟩ :=
    Bicategory.twoFibreProduct_twoIso_of_preHom
      (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q)
      (canonicalPreHom.{v₁, v₂, u₁, u₂} p q X)
      (w.comp (canonicalPreHom.{v₁, v₂, u₁, u₂} p q Y))
  refine ⟨θ, ?_, ?_⟩
  · refine (Category.id_comp
      (θ.hom ▷ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).fst)).symm.trans (h₁.trans ?_)
    change w.isoFst.hom ≫ 𝟙 (w.hom ≫ Y.fst) ≫ 𝟙 (w.hom ≫ Y.fst) = _
    simp
  · refine (Category.id_comp
      (θ.hom ▷ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} p q).snd)).symm.trans (h₂.trans ?_)
    change w.isoSnd.hom ≫ 𝟙 (w.hom ≫ Y.snd) ≫ 𝟙 (w.hom ≫ Y.snd) = _
    simp

end CategoryTheory.CatFiberedInGroupoids

end
