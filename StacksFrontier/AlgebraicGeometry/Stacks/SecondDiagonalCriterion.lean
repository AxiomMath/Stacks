module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.UliftBasedCategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonalEquiv
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict

/-!
# The second diagonal criterion (Stacks 07WG)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Its *second diagonal* is the relative diagonal

`Δ_Δ : 𝒳 ⟶ 𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳`

of its diagonal. **Stacks 07WG** says that `Δ_Δ` is representable by algebraic spaces if and only
if, for every *representable* category fibred in groupoids `𝒱` over the site and every
1-morphism `g : 𝒱 ⟶ 𝒳 × 𝒳`, the diagonal of

`𝒴 = 𝒳 ×_{Δ, 𝒳 × 𝒳, g} 𝒱`

is representable by algebraic spaces.

The proof is the source's: entirely formal, through the factorization of the diagonal of a
2-fibre product. Writing `r : 𝒴 ⟶ 𝒳` and `s : 𝒴 ⟶ 𝒱` for the two projections, the diagonal of
`𝒴` factors as

`Δ_𝒴 = Δ_{𝒴/𝒱} ≫ ι`,     `ι : 𝒴 ×_𝒱 𝒴 ⟶ 𝒴 × 𝒴`,

on the nose. The right-hand factor `ι` is the first leg of a 2-fibre product square over the
cospan `(s × s, Δ_𝒱)` (**Stacks 02XE**, over the site), hence a base change of `Δ_𝒱`, which is
representable because `𝒱` is representable. The left-hand factor is the first leg of a 2-fibre
product square over the cospan `(r × r, Δ_Δ)` (**Stacks 04YR**, over the site), hence a base
change of the second diagonal. Stacks 0302 turns each square into a representability statement
and Stacks 0301 composes them, which is the implication (1) ⟹ (2).

For the converse, `𝒱` is taken to be the category represented by the scheme `U` a test point of
`𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` lives over, and `g` to be that test point followed by `r ≫ Δ`. The test
point then lifts to a point `w` of `𝒴 ×_𝒱 𝒴` whose image under `r × r` is the original one — the
two components of `w` are the point itself and the point twisted by its own comparison
isomorphism — so the 2-fibre product the criterion asks about is, after cancelling the middle
factor, the one the base change of `Δ_Δ` along `r × r` controls. Representability of that base
change comes from condition (2) by Stacks 0301 run backwards, which is the cancellation lemma
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_postcomp`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_secondDiagonal_iff`: **Stacks 07WG**.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_toProduct`: **Stacks 02XE over the
  site**, for representability — the projection `𝒳 ×_𝒮 𝒴 ⟶ 𝒳 × 𝒴` is representable by algebraic
  spaces as soon as the diagonal of `𝒮` is.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_twoFibreProduct_iff`:
  **Stacks 04YR over the site**, for representability — the relative diagonal of a base change is
  a base change of the relative diagonal, so the two have the same representability.
* `isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_of_isRepresentableCFG`: the diagonal of a
  representable category fibred in groupoids is representable by algebraic spaces.

## Implementation notes

The three categories in the factorization `Δ_𝒴 = Δ_{𝒴/𝒱} ≫ ι` do *not* lie at one universe
pattern: the objects of `𝒴 ×_𝒱 𝒴` carry a morphism of `𝒱`, so its object universe is the maximum
of that of `𝒴` and the morphism universe of `𝒴`, while `𝒴` and `𝒴 × 𝒴` are at the object
universe of `𝒴`. That is exactly the universe shape of
`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp_basedFunctor`, which is why Stacks 0301
is applied in that form rather than in the 2-category form the tag sits on. The same widening is
why `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_postcomp` is stated at
independent universes.

Representability of `Δ_𝒱` is not read off an existing producer, because
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor` is pinned to the
universes of the site, while `𝒱` here is a universe lift of a slice. It is obtained instead by
proving condition (3) of Stacks 045G for `𝒱` — every 1-morphism from a scheme-represented
category to `𝒱` is representable by algebraic spaces, which is Stacks 02ZZ after transporting
the target along the representing equivalence — and then running the equivalences
(3) ⇔ (2) ⇔ (1) of Stacks 045G, all three of which are universe-free.

The comparison 1-morphisms of Stacks 02XE and 04YR are packaged as `BasedFunctor`s with their
`IsEquivalence` instances registered on the packaged form, because instance search does not see
through `CategoryTheory.BasedFunctor.toFunctor` of an anonymous constructor.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u v w a b v₂ w₂ v₃ w₃ v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The diagonal of a representable category fibred in groupoids -/

/-- **Condition (3) of Stacks 045G for a representable category fibred in groupoids.** Every
1-morphism to a representable category fibred in groupoids from the category represented by a
scheme over `S` is representable by algebraic spaces.

Composing with the equivalence of `𝒱` with the category represented by a scheme makes this
Stacks 02ZZ, for which both source and target are represented by algebraic spaces; the
composite and the original have the same representability by Stacks 0457 in the target. -/
theorem isRepresentableFromSchemes_of_isRepresentableCFG
    (𝒱 : CatFiberedInGroupoids.{u, a, u + 1, b} (BigFppfOver B S hS))
    (h : Stacks.RepresentableMorphism.IsRepresentableCFG 𝒱.val.p) :
    IsRepresentableFromSchemes B S hS 𝒱 := by
  obtain ⟨X, E, hE⟩ := h
  obtain ⟨Ginv, hG, ⟨η, -⟩, ⟨ε, -⟩⟩ := hE.exists_inverse
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    𝒱.isFiberedInGroupoids (schemeFibredCategory B S hS X).isFiberedInGroupoids E
    hE.isCartesianFunctor.comm
    (CategoryTheory.Equivalence.mk E Ginv ε.symm η).isEquivalence_functor
  intro U x
  refine (isRepresentableByAlgebraicSpaces_iff_of_equivalenceOver_target B S hS
    (BasedFunctor.comp x ⟨k.hom.functor, k.hom.w⟩) x k (Iso.refl _)).1 ?_
  exact isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp x ⟨k.hom.functor, k.hom.w⟩))
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS X)

/-- **The diagonal of a representable category fibred in groupoids is representable by algebraic
spaces.** This is condition (1) of Stacks 045G, reached from condition (3) along the
equivalences (3) ⇔ (2) ⇔ (1). -/
theorem isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_of_isRepresentableCFG
    (𝒱 : CatFiberedInGroupoids.{u, a, u + 1, b} (BigFppfOver B S hS))
    (h : Stacks.RepresentableMorphism.IsRepresentableCFG 𝒱.val.p) :
    IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒱) :=
  (hasRepresentableDiagonal_iff B S hS 𝒱).1
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒱).2
      ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒱).2
        (isRepresentableFromSchemes_of_isRepresentableCFG B S hS 𝒱 h)))

/-! ### Stacks 04YR over the site: the relative diagonal of a base change -/

section RelativeDiagonalBaseChange

variable (𝒜 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  (𝒱 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS))
  (h : 𝒳.val ⥤ᵇ 𝒜.val) (s : 𝒱.val ⥤ᵇ 𝒜.val)

/-- The second projection of a 2-fibre product, as a 1-morphism of categories over the site. -/
noncomputable def sndBasedFunctor :
    (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s).val ⥤ᵇ 𝒱.val where
  toFunctor := snd 𝒳.val.p 𝒱.val.p 𝒜.val.p h.toFunctor s.toFunctor
  w := snd_comp_eq

/-- The 1-morphism `r × r : (𝒳 ×_𝒜 𝒱) ×_𝒱 (𝒳 ×_𝒜 𝒱) ⟶ 𝒳 ×_𝒜 𝒳` induced by the projection
`r` on both factors; it is the right-hand leg of the base-change square of Stacks 04YR. -/
noncomputable def mapDiagBasedFunctor :
    (twoFibreProduct B S hS 𝒱 (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s)
        (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)
        (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)).val ⥤ᵇ
      (twoFibreProduct B S hS 𝒜 𝒳 𝒳 h h).val where
  toFunctor := mapDiag (p𝒳 := 𝒳.val.p) (p𝒱 := 𝒱.val.p) (p𝒴 := 𝒜.val.p)
    (h := h.toFunctor) (s := s.toFunctor) s.w
  w := rfl

/-- The comparison 1-morphism of Stacks 04YR over the site: it exhibits `𝒳 ×_𝒜 𝒱` as the
2-fibre product of `r × r` and the relative diagonal of `h`. -/
noncomputable def diagonalBaseChangeComparisonBasedFunctor :
    (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s).val ⥤ᵇ
      (twoFibreProduct B S hS (twoFibreProduct B S hS 𝒜 𝒳 𝒳 h h)
        (twoFibreProduct B S hS 𝒱 (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s)
          (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)
          (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)) 𝒳
        (mapDiagBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)
        (relativeDiagonalBasedFunctor B S hS 𝒳 𝒜 h)).val where
  toFunctor := diagonalBaseChangeComparison h.w s.w
  w := rfl

/-- The comparison 1-morphism `diagonalBaseChangeComparisonBasedFunctor` is an equivalence of
categories. -/
noncomputable instance isEquivalence_diagonalBaseChangeComparisonBasedFunctor :
    Functor.IsEquivalence (diagonalBaseChangeComparisonBasedFunctor B S hS 𝒜 𝒳 𝒱 h s).toFunctor :=
  isEquivalence_diagonalBaseChangeComparison h.w s.w

/-- **Stacks 04YR over the site, for representability.** The relative diagonal of the base change
`𝒳 ×_𝒜 𝒱 ⟶ 𝒱` is the first leg of the 2-fibre product square of the cospan `(r × r, Δ_{𝒳/𝒜})`,
so it is representable by algebraic spaces exactly when that base change is. -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_twoFibreProduct_iff :
    IsRepresentableByAlgebraicSpaces B S hS
        (twoFibreProductFst B S hS (twoFibreProduct B S hS 𝒜 𝒳 𝒳 h h)
          (twoFibreProduct B S hS 𝒱 (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s)
            (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)
            (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)) 𝒳
          (mapDiagBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)
          (relativeDiagonalBasedFunctor B S hS 𝒳 𝒜 h)) ↔
      IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) 𝒱
          (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)) :=
  isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS
    (twoFibreProductFst B S hS (twoFibreProduct B S hS 𝒜 𝒳 𝒳 h h)
      (twoFibreProduct B S hS 𝒱 (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s)
        (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)
        (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)) 𝒳
      (mapDiagBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)
      (relativeDiagonalBasedFunctor B S hS 𝒳 𝒜 h))
    _ (diagonalBaseChangeComparisonBasedFunctor B S hS 𝒜 𝒳 𝒱 h s) (Iso.refl _)

/-- **Stacks 04YR over the site, for representability**, in the direction a consumer uses: the
relative diagonal of a base change is representable by algebraic spaces as soon as the relative
diagonal it is a base change of is. -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_twoFibreProduct
    (hd : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 𝒜 h)) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) 𝒱
        (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)) :=
  (isRepresentableByAlgebraicSpaces_relativeDiagonal_twoFibreProduct_iff B S hS 𝒜 𝒳 𝒱 h s).1
    (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS _ _ _ _ _ hd)

end RelativeDiagonalBaseChange

/-! ### Stacks 02XE over the site: a 2-fibre product inside the product -/

section ToProduct

variable (𝒮 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  (F : 𝒳.val ⥤ᵇ 𝒮.val) (G : 𝒴.val ⥤ᵇ 𝒮.val)

/-- The product `F × G : 𝒳 × 𝒴 ⟶ 𝒮 × 𝒮` of two 1-morphisms with a common target. -/
noncomputable def prodMapBasedFunctor :
    (CatFiberedInGroupoids.product 𝒳 𝒴).val ⥤ᵇ (CatFiberedInGroupoids.product 𝒮 𝒮).val where
  toFunctor := prodMap F.toFunctor G.toFunctor F.w G.w
  w := rfl

/-- The projection `𝒳 ×_𝒮 𝒴 ⟶ 𝒳 × 𝒴` of a 2-fibre product onto the product. -/
noncomputable def toProductBasedFunctor :
    (twoFibreProduct B S hS 𝒮 𝒳 𝒴 F G).val ⥤ᵇ (CatFiberedInGroupoids.product 𝒳 𝒴).val where
  toFunctor := toProduct 𝒳.val.p 𝒴.val.p 𝒮.val.p F.toFunctor G.toFunctor
  w := rfl

/-- The comparison 1-morphism of Stacks 02XE over the site: it exhibits `𝒳 ×_𝒮 𝒴` as the 2-fibre
product of `F × G` and the diagonal of `𝒮`. -/
noncomputable def prodDiagComparisonBasedFunctor :
    (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒮 𝒮)
        (CatFiberedInGroupoids.product 𝒳 𝒴) 𝒮
        (prodMapBasedFunctor B S hS 𝒮 𝒳 𝒴 F G) (diagonalBasedFunctor B S hS 𝒮)).val ⥤ᵇ
      (twoFibreProduct B S hS 𝒮 𝒳 𝒴 F G).val where
  toFunctor := prodDiagComparison F.toFunctor G.toFunctor F.w G.w
  w := rfl

/-- The comparison 1-morphism `prodDiagComparisonBasedFunctor` is an equivalence of categories. -/
noncomputable instance isEquivalence_prodDiagComparisonBasedFunctor :
    Functor.IsEquivalence (prodDiagComparisonBasedFunctor B S hS 𝒮 𝒳 𝒴 F G).toFunctor :=
  instIsEquivalenceProdDiagComparison F.toFunctor G.toFunctor F.w G.w

/-- **Stacks 02XE over the site, for representability.** The projection of a 2-fibre product onto
the product is the first leg of the 2-fibre product square of the cospan `(F × G, Δ_𝒮)`, hence a
base change of the diagonal of `𝒮`; so it is representable by algebraic spaces as soon as that
diagonal is. -/
theorem isRepresentableByAlgebraicSpaces_toProduct
    (hd : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒮)) :
    IsRepresentableByAlgebraicSpaces B S hS (toProductBasedFunctor B S hS 𝒮 𝒳 𝒴 F G) :=
  (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS
    (toProductBasedFunctor B S hS 𝒮 𝒳 𝒴 F G)
    (twoFibreProductFst B S hS (CatFiberedInGroupoids.product 𝒮 𝒮)
      (CatFiberedInGroupoids.product 𝒳 𝒴) 𝒮
      (prodMapBasedFunctor B S hS 𝒮 𝒳 𝒴 F G) (diagonalBasedFunctor B S hS 𝒮))
    (prodDiagComparisonBasedFunctor B S hS 𝒮 𝒳 𝒴 F G)
    (BasedNatIso.mkNatIso (prodDiagComparisonToProductIso F.toFunctor G.toFunctor F.w G.w)
      (fun x => isHomLift_prodDiagComparisonToProductIso_hom_app _ _ _ _ x))).2
    (isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS _ _ _ _ _ hd)

end ToProduct

/-- The projection of a 2-fibre product over a representable category fibred in groupoids onto the
product is representable by algebraic spaces. -/
private theorem isRepresentableByAlgebraicSpaces_toProduct_of_isRepresentableCFG
    (𝒱 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))
    (h𝒱 : Stacks.RepresentableMorphism.IsRepresentableCFG 𝒱.val.p)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (F : 𝒳.val ⥤ᵇ 𝒱.val) (G : 𝒴.val ⥤ᵇ 𝒱.val) :
    IsRepresentableByAlgebraicSpaces B S hS (toProductBasedFunctor B S hS 𝒱 𝒳 𝒴 F G) :=
  isRepresentableByAlgebraicSpaces_toProduct B S hS 𝒱 𝒳 𝒴 F G
    (isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_of_isRepresentableCFG B S hS 𝒱 h𝒱)

section Factorization

variable (𝒜 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS))
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  (𝒱 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS))
  (h : 𝒳.val ⥤ᵇ 𝒜.val) (s : 𝒱.val ⥤ᵇ 𝒜.val)

/-- **The diagonal of a 2-fibre product factors through its relative diagonal.** The diagonal of
`𝒳 ×_𝒜 𝒱` is its relative diagonal over `𝒱` followed by the projection onto the product, on the
nose: the relative diagonal sends an object to the pair of itself with the identity comparison in
`𝒱`, and the projection replaces that comparison by the forced `eqToHom` of a product. -/
lemma diagonalBasedFunctor_eq_relativeDiagonal_comp_toProduct :
    diagonalBasedFunctor B S hS (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) =
      BasedFunctor.comp
        (relativeDiagonalBasedFunctor B S hS (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) 𝒱
          (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s))
        (toProductBasedFunctor B S hS 𝒱 (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s)
          (twoFibreProduct B S hS 𝒜 𝒳 𝒱 h s) (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)
          (sndBasedFunctor B S hS 𝒜 𝒳 𝒱 h s)) :=
  rfl

end Factorization


/-! ### The criterion -/

section Criterion

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- The forward implication of **Stacks 07WG**: if the second diagonal of `𝒳` is representable by
algebraic spaces then so is the diagonal of every base change `𝒳 ×_{Δ, 𝒳 × 𝒳, g} 𝒱` of the
diagonal along a 1-morphism out of a representable category fibred in groupoids. -/
theorem isRepresentableByAlgebraicSpaces_diagonal_baseChange_of_secondDiagonal
    (𝒱 : CatFiberedInGroupoids.{u, max u v', u + 1, max (u + 1) w'} (BigFppfOver B S hS))
    (g : 𝒱.val ⥤ᵇ (CatFiberedInGroupoids.product 𝒳 𝒳).val)
    (hd : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
        (diagonalBasedFunctor B S hS 𝒳)))
    (h𝒱 : Stacks.RepresentableMorphism.IsRepresentableCFG 𝒱.val.p) :
    IsRepresentableByAlgebraicSpaces B S hS
      (diagonalBasedFunctor B S hS
        (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒱
          (diagonalBasedFunctor B S hS 𝒳) g)) :=
  isRepresentableByAlgebraicSpaces_comp_basedFunctor B S hS _ _
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_twoFibreProduct B S hS
      (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒱 (diagonalBasedFunctor B S hS 𝒳) g hd)
    (isRepresentableByAlgebraicSpaces_toProduct_of_isRepresentableCFG B S hS 𝒱 h𝒱 _ _ _ _)

end Criterion

/-! ### The converse: a test point of the second diagonal lifts to the base change -/

section Converse

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
  (U : BigFppfOver B S hS)
  (Y : BigFppfOver B U.left.1 U.left.2 ⥤
    TwoFibreProductOver 𝒳.val.p 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
      (diagonalBasedFunctor B S hS 𝒳).toFunctor (diagonalBasedFunctor B S hS 𝒳).toFunctor)
  (hY : Y ⋙ structureFunctor 𝒳.val.p 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
      (diagonalBasedFunctor B S hS 𝒳).toFunctor (diagonalBasedFunctor B S hS 𝒳).toFunctor
    = Over.map U.hom)

/-- The representable category fibred in groupoids the converse of Stacks 07WG is tested with:
the universe lift of the category represented by `U`, at the universes the criterion quantifies
over. -/
noncomputable def testCategory : CatFiberedInGroupoids.{u, max u v', u + 1, max (u + 1) w'}
    (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.ulift.{u, u + 1, u, u + 1, v', w'} (schemeFibredCategory B S hS U)

/-- The test category is representable. -/
lemma isRepresentableCFG_testCategory :
    Stacks.RepresentableMorphism.IsRepresentableCFG (testCategory.{u, v', w'} B S hS U).val.p :=
  Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable _
    ⟨U, ⟨BasedCategory.uliftEquivalenceOver (schemeFibredCategory B S hS U).val⟩⟩

/-- The big fppf site of `U` includes into the test category, by the iterated-slice equivalence
followed by the universe lift. -/
noncomputable def testInclusion :
    BigFppfOver B U.left.1 U.left.2 ⥤ (testCategory.{u, v', w'} B S hS U).val.obj :=
  Over.iteratedSliceBackward U ⋙ BasedCategory.uliftUp (schemeFibredCategory B S hS U).val

/-- The quasi-inverse of `testInclusion`. -/
noncomputable def testProjection :
    (testCategory.{u, v', w'} B S hS U).val.obj ⥤ BigFppfOver B U.left.1 U.left.2 :=
  BasedCategory.uliftDown (schemeFibredCategory B S hS U).val ⋙ Over.iteratedSliceForward U

/-- Including and then projecting is the identity, on the nose. -/
lemma testInclusion_comp_testProjection :
    testInclusion.{u, v', w'} B S hS U ⋙ testProjection.{u, v', w'} B S hS U = 𝟭 _ := rfl

/-- The projection is a 1-morphism from the test category to the big fppf site of `U`. -/
lemma testProjection_comp :
    testProjection.{u, v', w'} B S hS U ⋙ Over.map U.hom =
      (testCategory.{u, v', w'} B S hS U).val.p :=
  congrArg (fun F : Over U ⥤ BigFppfOver B S hS =>
    BasedCategory.uliftDown (schemeFibredCategory B S hS U).val ⋙ F)
    (Over.iteratedSliceForward_comp_map U)

/-- The inclusion is a 1-morphism over the site. -/
lemma testInclusion_comp :
    testInclusion.{u, v', w'} B S hS U ⋙ (testCategory.{u, v', w'} B S hS U).val.p =
      Over.map U.hom :=
  Over.iteratedSliceBackward_forget U

/-- The first component of a test point of the second 2-fibre product. -/
noncomputable abbrev testFst := Y ⋙ fst 𝒳.val.p 𝒳.val.p
  (CatFiberedInGroupoids.product 𝒳 𝒳).val.p (diagonalBasedFunctor B S hS 𝒳).toFunctor
  (diagonalBasedFunctor B S hS 𝒳).toFunctor

/-- The second component of a test point of the second 2-fibre product. -/
noncomputable abbrev testSnd := Y ⋙ snd 𝒳.val.p 𝒳.val.p
  (CatFiberedInGroupoids.product 𝒳 𝒳).val.p (diagonalBasedFunctor B S hS 𝒳).toFunctor
  (diagonalBasedFunctor B S hS 𝒳).toFunctor

include hY in
/-- The first component is a 1-morphism over the site. -/
lemma testFst_comp : testFst B S hS 𝒳 U Y ⋙ 𝒳.val.p = Over.map U.hom := by
  rw [Functor.assoc, fst_comp_eq]; exact hY

include hY in
/-- The second component is a 1-morphism over the site. -/
lemma testSnd_comp : testSnd B S hS 𝒳 U Y ⋙ 𝒳.val.p = Over.map U.hom := by
  rw [Functor.assoc, snd_comp_eq]; exact hY

include hY in
/-- The first component followed by the diagonal is a 1-morphism over the site. -/
lemma testFst_comp_diagonal_comp :
    testFst B S hS 𝒳 U Y ⋙ (diagonalBasedFunctor B S hS 𝒳).toFunctor ⋙
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map U.hom := by
  rw [(diagonalBasedFunctor B S hS 𝒳).w]; exact testFst_comp B S hS 𝒳 U Y hY

/-- The 1-morphism `g : 𝒱 ⟶ 𝒳 × 𝒳` the converse of Stacks 07WG is tested with: the first
component of the test point, followed by the diagonal. -/
noncomputable def testMorphism :
    (testCategory.{u, v', w'} B S hS U).val ⥤ᵇ
      (CatFiberedInGroupoids.product 𝒳 𝒳).val where
  toFunctor := testProjection.{u, v', w'} B S hS U ⋙ testFst B S hS 𝒳 U Y ⋙
    (diagonalBasedFunctor B S hS 𝒳).toFunctor
  w :=
    (congrArg (fun F : BigFppfOver B U.left.1 U.left.2 ⥤ BigFppfOver B S hS =>
        testProjection.{u, v', w'} B S hS U ⋙ F)
      (testFst_comp_diagonal_comp B S hS 𝒳 U Y hY)).trans
      (testProjection_comp.{u, v', w'} B S hS U)

/-- The first of the two points of `𝒴` the test point gives rise to: the test point's first
component, over the test category, with the identity comparison. -/
noncomputable def testFirstPoint : BigFppfOver B U.left.1 U.left.2 ⥤
    TwoFibreProductOver 𝒳.val.p (testCategory.{u, v', w'} B S hS U).val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
      (diagonalBasedFunctor B S hS 𝒳).toFunctor
      (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY).toFunctor :=
  lift 𝒳.val.p (testCategory.{u, v', w'} B S hS U).val.p
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
    (diagonalBasedFunctor B S hS 𝒳).toFunctor
    (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY).toFunctor
    (Over.map U.hom) (testFst B S hS 𝒳 U Y) (testInclusion.{u, v', w'} B S hS U)
    (testFst_comp B S hS 𝒳 U Y hY) (testInclusion_comp.{u, v', w'} B S hS U) (Iso.refl _)
    (fun x => IsHomLift.id
      (Functor.congr_obj (testFst_comp_diagonal_comp B S hS 𝒳 U Y hY) x))

/-- The second of the two points of `𝒴`: the test point's second component, over the test
category, with the test point's own comparison isomorphism as comparison. -/
noncomputable def testSecondPoint : BigFppfOver B U.left.1 U.left.2 ⥤
    TwoFibreProductOver 𝒳.val.p (testCategory.{u, v', w'} B S hS U).val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
      (diagonalBasedFunctor B S hS 𝒳).toFunctor
      (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY).toFunctor :=
  lift 𝒳.val.p (testCategory.{u, v', w'} B S hS U).val.p
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
    (diagonalBasedFunctor B S hS 𝒳).toFunctor
    (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY).toFunctor
    (Over.map U.hom) (testSnd B S hS 𝒳 U Y) (testInclusion.{u, v', w'} B S hS U)
    (testSnd_comp B S hS 𝒳 U Y hY) (testInclusion_comp.{u, v', w'} B S hS U)
    (Functor.isoWhiskerLeft Y (psiIso 𝒳.val.p 𝒳.val.p
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p (diagonalBasedFunctor B S hS 𝒳).toFunctor
      (diagonalBasedFunctor B S hS 𝒳).toFunctor)).symm
    (fun x => by
      have hv := (Y.obj x).vertical
      rw [show (Y.obj x).base = (Over.map U.hom).obj x from Functor.congr_obj hY x] at hv
      exact IsHomLift.lift_id_inv (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
        ((Over.map U.hom).obj x) (Y.obj x).iso)

/-- The point of `𝒴 ×_𝒱 𝒴` the test point gives rise to: the pair of the two points above, with
the identity comparison in the test category. -/
noncomputable def testRelativePoint : BigFppfOver B U.left.1 U.left.2 ⥤
    (twoFibreProduct B S hS (testCategory.{u, v', w'} B S hS U)
      (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))).val.obj :=
  lift _ _ _ _ _ (Over.map U.hom)
    (testFirstPoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
    (testSecondPoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
    (lift_comp_structureFunctor ..) (lift_comp_structureFunctor ..) (Iso.refl _)
    (fun x => IsHomLift.id
      (Functor.congr_obj (testInclusion_comp.{u, v', w'} B S hS U) x))


/-- The point of `𝒴 ×_𝒱 𝒴` is a point over the big fppf site of `U`. -/
lemma testRelativePoint_comp :
    testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY ⋙
        (twoFibreProduct B S hS (testCategory.{u, v', w'} B S hS U)
          (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
            (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
            (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
          (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
            (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
            (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
          (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
            (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
            (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
          (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
            (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
            (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))).val.p =
      Over.map U.hom :=
  lift_comp_structureFunctor ..

/-- The comparison isomorphism of the first point is the identity. -/
@[simp] lemma testRelativePoint_obj_x_iso_hom (x : BigFppfOver B U.left.1 U.left.2) :
    ((testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY).obj x).x.iso.hom = 𝟙 _ := rfl

/-- The comparison isomorphism of the point of `𝒴 ×_𝒱 𝒴` is the identity. -/
@[simp] lemma testRelativePoint_obj_iso_hom (x : BigFppfOver B U.left.1 U.left.2) :
    ((testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY).obj x).iso.hom = 𝟙 _ := rfl

/-- The inverse comparison isomorphism of the second point is the test point's own. -/
@[simp] lemma testRelativePoint_obj_y_iso_inv (x : BigFppfOver B U.left.1 U.left.2) :
    ((testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY).obj x).y.iso.inv =
      (Y.obj x).iso.hom := rfl

/-- **The point of `𝒴 ×_𝒱 𝒴` has the test point as its image under `r × r`**, in the comparison
isomorphism: the composite of the first point's identity comparison, the image of the identity of
the test category and the inverse of the second point's comparison is the test point's own
comparison. -/
lemma testRelativePoint_mapDiag_obj_iso_hom (x : BigFppfOver B U.left.1 U.left.2) :
    ((testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY ⋙
      (mapDiagBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)).toFunctor).obj x).iso.hom
      = (Y.obj x).iso.hom := by
  have h : ((testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY ⋙
      (mapDiagBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)).toFunctor).obj x).iso.hom
      = 𝟙 _ ≫ (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY).toFunctor.map
          (𝟙 ((testInclusion.{u, v', w'} B S hS U).obj x)) ≫ (Y.obj x).iso.hom := rfl
  rw [h, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.id_comp _

/-- The component at `x` of the comparison `w ⋙ (r × r) ≅ Y`. -/
noncomputable def testComparisonApp (x : BigFppfOver B U.left.1 U.left.2) :
    (testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY ⋙
      (mapDiagBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)).toFunctor).obj x ≅ Y.obj x :=
  isoMkVertical (U := (Over.map U.hom).obj x) (Iso.refl _) (Iso.refl _)
    (IsHomLift.id (Functor.congr_obj (testFst_comp B S hS 𝒳 U Y hY) x))
    (IsHomLift.id (Functor.congr_obj (testSnd_comp B S hS 𝒳 U Y hY) x))
    (by
      refine Eq.trans (congrArg (fun t => t ≫ (Y.obj x).iso.hom)
        ((diagonalBasedFunctor B S hS 𝒳).toFunctor.map_id _)) ?_
      refine Eq.trans (Category.id_comp _) ?_
      refine Eq.trans
        (testRelativePoint_mapDiag_obj_iso_hom B S hS 𝒳 U Y hY x).symm ?_
      refine Eq.trans (Category.comp_id _).symm ?_
      exact congrArg (fun t => _ ≫ t)
        ((diagonalBasedFunctor B S hS 𝒳).toFunctor.map_id _).symm)

/-- The `𝒳`-component of `testComparisonApp` is the identity. -/
@[simp] lemma testComparisonApp_hom_a (x : BigFppfOver B U.left.1 U.left.2) :
    (testComparisonApp.{u, v, w, v', w'} B S hS 𝒳 U Y hY x).hom.a = 𝟙 _ := rfl

/-- The second `𝒳`-component of `testComparisonApp` is the identity. -/
@[simp] lemma testComparisonApp_hom_b (x : BigFppfOver B U.left.1 U.left.2) :
    (testComparisonApp.{u, v, w, v', w'} B S hS 𝒳 U Y hY x).hom.b = 𝟙 _ := rfl

/-- **The image of the point of `𝒴 ×_𝒱 𝒴` under `r × r` is the test point**, up to a
2-isomorphism which is the identity in both components. -/
noncomputable def testComparison :
    testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY ⋙
      (mapDiagBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)).toFunctor ≅ Y :=
  NatIso.ofComponents (testComparisonApp.{u, v, w, v', w'} B S hS 𝒳 U Y hY) (by
    intro x x' f
    exact Hom.ext' ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The comparison is a 2-isomorphism over the site. -/
lemma isHomLift_testComparison_hom_app (x : BigFppfOver B U.left.1 U.left.2) :
    (structureFunctor 𝒳.val.p 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p
        (diagonalBasedFunctor B S hS 𝒳).toFunctor
        (diagonalBasedFunctor B S hS 𝒳).toFunctor).IsHomLift
      (𝟙 ((Over.map U.hom).obj x))
      ((testComparison.{u, v, w, v', w'} B S hS 𝒳 U Y hY).hom.app x) :=
  structureFunctor_isHomLift _ (𝟙 ((Over.map U.hom).obj x))
    (IsHomLift.id (Functor.congr_obj (testFst_comp B S hS 𝒳 U Y hY) x))


end Converse

/-! ### Stacks 07WG -/

section Statement

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- The converse implication of **Stacks 07WG**: if the diagonal of every base change of the
diagonal of `𝒳` along a 1-morphism out of a representable category fibred in groupoids is
representable by algebraic spaces, then so is the second diagonal of `𝒳`.

Given a scheme `U` over `S` and a point `Y` of `𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` over the big fppf site of
`U`, the test data are the universe lift of the category represented by `U` and the 1-morphism
`g = Y ≫ r ≫ Δ`. The point `Y` lifts to a point of `𝒴 ×_𝒱 𝒴` whose image under `r × r` is `Y`
itself, up to a vertical 2-isomorphism, and the 2-fibre product the conclusion asks about is that
lifted point's one after cancelling the middle factor. -/
theorem isRepresentableByAlgebraicSpaces_secondDiagonal_of_diagonal_baseChange
    (h : ∀ (𝒱 : CatFiberedInGroupoids.{u, max u v', u + 1, max (u + 1) w'}
        (BigFppfOver B S hS)),
      Stacks.RepresentableMorphism.IsRepresentableCFG 𝒱.val.p →
      ∀ (g : 𝒱.val ⥤ᵇ (CatFiberedInGroupoids.product 𝒳 𝒳).val),
        IsRepresentableByAlgebraicSpaces B S hS
          (diagonalBasedFunctor B S hS
            (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒱
              (diagonalBasedFunctor B S hS 𝒳) g))) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
        (diagonalBasedFunctor B S hS 𝒳)) := by
  dsimp only [IsRepresentableByAlgebraicSpaces]
  intro U Y hY
  have hΔ𝒴 := h (testCategory.{u, v', w'} B S hS U)
    (isRepresentableCFG_testCategory.{u, v', w'} B S hS U)
    (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
  have hι := isRepresentableByAlgebraicSpaces_toProduct_of_isRepresentableCFG B S hS
    (testCategory.{u, v', w'} B S hS U) (isRepresentableCFG_testCategory.{u, v', w'} B S hS U)
    _ _ (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
      (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
      (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)) (sndBasedFunctor B S hS
      (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 (testCategory.{u, v', w'} B S hS U)
      (diagonalBasedFunctor B S hS 𝒳) (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
  have hΔrel := isRepresentableByAlgebraicSpaces_of_postcomp B S hS
    (toProductBasedFunctor B S hS (testCategory.{u, v', w'} B S hS U)
      (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)))
    (diagonalBasedFunctor B S hS
      (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)))
    (relativeDiagonalBasedFunctor B S hS
      (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (testCategory.{u, v', w'} B S hS U)
      (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)))
    (Iso.refl _) hι hΔ𝒴
  obtain ⟨F, hF, ⟨e⟩⟩ :=
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_twoFibreProduct_iff B S hS
      (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 (testCategory.{u, v', w'} B S hS U)
      (diagonalBasedFunctor B S hS 𝒳)
      (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)).2 hΔrel U
      (testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
      (testRelativePoint_comp.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
  have ecancel := cancelMiddleEquivalenceOver (Over.map U.hom) 𝒳.val.p
    (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒳
      (diagonalBasedFunctor B S hS 𝒳) (diagonalBasedFunctor B S hS 𝒳)).val.p
    (twoFibreProduct B S hS (testCategory.{u, v', w'} B S hS U)
      (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))
      (sndBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
        (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
        (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY))).val.p
    (testRelativePoint.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
    (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
      (diagonalBasedFunctor B S hS 𝒳)).toFunctor
    (mapDiagBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
      (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
      (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)).toFunctor
    (testRelativePoint_comp.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
    (mapDiagBasedFunctor B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳
      (testCategory.{u, v', w'} B S hS U) (diagonalBasedFunctor B S hS 𝒳)
      (testMorphism.{u, v, w, v', w'} B S hS 𝒳 U Y hY)).w
  have ereindex := reindexEquivalenceOver (p𝒴 := 𝒳.val.p)
    (p𝒮 := (twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒳
      (diagonalBasedFunctor B S hS 𝒳) (diagonalBasedFunctor B S hS 𝒳)).val.p)
    (G := (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
      (diagonalBasedFunctor B S hS 𝒳)).toFunctor)
    (testComparison.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
    (isHomLift_testComparison_hom_app.{u, v, w, v', w'} B S hS 𝒳 U Y hY)
  exact ⟨F, hF, ⟨@StacksRepresentableCFG.EquivalenceOver.trans _ _ _ _ _ _ _ _ _ _ _
    (@StacksRepresentableCFG.EquivalenceOver.symm _ _ _ _ _ _ _ _
      (@StacksRepresentableCFG.EquivalenceOver.trans _ _ _ _ _ _ _ _ _ _ _
        ecancel ereindex)) e⟩⟩

/-- **Stacks 07WG.** The second diagonal of a category fibred in groupoids `𝒳` over the big fppf
site of `S` — the relative diagonal of its diagonal — is representable by algebraic spaces if and
only if, for every representable category fibred in groupoids `𝒱` over the site and every
1-morphism `g : 𝒱 ⟶ 𝒳 × 𝒳`, the diagonal of the base change `𝒴 = 𝒳 ×_{Δ, 𝒳 × 𝒳, g} 𝒱` is
representable by algebraic spaces. -/
@[stacks 07WG]
theorem isRepresentableByAlgebraicSpaces_secondDiagonal_iff :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
        (diagonalBasedFunctor B S hS 𝒳)) ↔
    ∀ (𝒱 : CatFiberedInGroupoids.{u, max u v', u + 1, max (u + 1) w'}
        (BigFppfOver B S hS))
      (_h𝒱 : Stacks.RepresentableMorphism.IsRepresentableCFG 𝒱.val.p)
      (g : 𝒱.val ⥤ᵇ (CatFiberedInGroupoids.product 𝒳 𝒳).val),
      let 𝒴 := twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒱
        (diagonalBasedFunctor B S hS 𝒳) g
      IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒴) :=
  ⟨fun hd 𝒱 h𝒱 g =>
      isRepresentableByAlgebraicSpaces_diagonal_baseChange_of_secondDiagonal B S hS 𝒳 𝒱 g
        hd h𝒱,
    fun h =>
      isRepresentableByAlgebraicSpaces_secondDiagonal_of_diagonal_baseChange B S hS 𝒳
        (fun 𝒱 h𝒱 g => h 𝒱 h𝒱 g)⟩

end Statement

end AlgebraicGeometry.Stack

end
