module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack

/-!
# Base change of a surjective morphism of algebraic stacks (Stacks 04XH, 04ZU)

Stacks 04XH — a point of `𝒵` and a point of `𝒳` with the same image in `|𝒴|` lift to a point of
a 2-fibre product `𝒵 ×_𝒴 𝒳` — is stated in the source for algebraic stacks. The library proves
it in `StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct` for 2-fibre products in the
larger 2-category of categories fibred in groupoids, where the canonical model of the 2-fibre
product is available. This file transports it to the 2-category of algebraic stacks and deduces
**Stacks 04ZU**: the base change of a surjective 1-morphism of algebraic stacks is surjective.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`: the canonical 2-fibre product
  square of a cospan of algebraic stacks, i.e. the square of
  `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` read in the 2-category of
  algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isAlgebraicStack_twoFibreProductSquare_pt`: the apex
  of that square is an algebraic stack — Stacks 04TF.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_point_of_isTwoFibreProduct`: **Stacks 04XH**
  for a 2-fibre product in the 2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.isSurjective_of_isTwoFibreProduct`: **Stacks 04ZU**.

## Implementation notes

The 2-category of algebraic stacks is a *full* sub-2-category of the 2-category of categories
fibred in groupoids (`CategoryTheory.Bicategory.InducedBicategory`), so being a 2-fibre product
there is a weaker condition: the universal property is tested against fewer squares. A
2-fibre-product square of algebraic stacks therefore cannot be fed to the fibred-in-groupoids
Stacks 04XH directly, and the implication runs the wrong way for transport.

What makes the transport work is that the fibred-in-groupoids proof applies the universal
property to exactly one test square, the canonical one, whose apex is an algebraic stack as soon
as the three corners are (Stacks 04TF). So `AlgebraicGeometry.Stack.exists_point_of_coneHom`
asks only for a cone morphism out of the canonical square — a 1-morphism and two comparison
2-cells, with no invertibility and no compatibility — and that much the algebraic-stacks-level
universal property supplies, applied to
`AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`.

Passing between the two levels is componentwise, since every operation of an induced bicategory
is the underlying operation: `CategoryTheory.Bicategory.InducedBicategory.mkHom` and
`CategoryTheory.Bicategory.InducedBicategory.isoMk` go up, and the `hom` field goes down. The
fibred-in-groupoids witnesses never have to be matched up, because `IsFiberedInGroupoids` is a
proposition: `AlgebraicGeometry.Stack.AlgebraicStacks.points` reads one off the algebraic-stack
condition with `Classical.choose` while the categories-fibred-in-groupoids level carries its own.

Stacks 04ZU is stated for an arbitrary 2-fibre-product square rather than for a chosen model of
the base change, so it applies to the canonical square and to any other model. The surjective
1-morphism is the first leg of the cospan and the conclusion is about the second projection,
which is its base change.

## References

* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

variable {𝒵 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04TF** at the canonical 2-fibre product square: the apex of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` over a cospan of algebraic stacks
is an algebraic stack over `S`. -/
theorem isAlgebraicStack_twoFibreProductSquare_pt (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) :
    IsAlgebraicStack.{u, w} B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        g.hom f.hom).pt.val := by
  obtain ⟨h𝒴fib, h𝒴stack, h𝒴diag, -⟩ := 𝒴.property
  exact isAlgebraicStack_twoFibreProduct B S hS 𝒵.val.val 𝒳.val.val 𝒴.val.val
    g.hom.hom f.hom.hom h𝒴stack h𝒴diag 𝒵.property 𝒳.property

/-- The canonical 2-fibre product square of a cospan of algebraic stacks over `S`: the square of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`, whose apex is an algebraic stack by
Stacks 04TF, read in the 2-category of algebraic stacks. -/
def twoFibreProductSquare (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) : Bicategory.TwoCommSq g f where
  pt := ⟨(CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom).pt,
    isAlgebraicStack_twoFibreProductSquare_pt B S hS g f⟩
  fst := Bicategory.InducedBicategory.mkHom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom).fst
  snd := Bicategory.InducedBicategory.mkHom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom).snd
  iso := Bicategory.InducedBicategory.isoMk
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom).iso

/-- The 2-commutative square of categories fibred in groupoids underlying a 2-commutative square
of algebraic stacks. -/
def toCatFiberedInGroupoids {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P : Bicategory.TwoCommSq g f) :
    Bicategory.TwoCommSq g.hom f.hom where
  pt := P.pt.val
  fst := P.fst.hom
  snd := P.snd.hom
  iso :=
    { hom := P.iso.hom.hom
      inv := P.iso.inv.hom
      hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom P.iso.hom_inv_id
      inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom P.iso.inv_hom_id }

/-- **Stacks 04XH** for a 2-fibre product in the 2-category of algebraic stacks: a point of `𝒵`
and a point of `𝒳` with the same image in `|𝒴|` lift to a point of any 2-fibre product of
`g : 𝒵 ⟶ 𝒴` and `f : 𝒳 ⟶ 𝒴`.

This is the same proposition as
`AlgebraicGeometry.Stack.exists_point_of_isTwoFibreProduct_algebraicStacks`, which writes the
points and the maps on points in longhand instead of through the abbreviations
`AlgebraicGeometry.Stack.AlgebraicStacks.points` and
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap`. -/
@[stacks 04XH]
theorem exists_point_of_isTwoFibreProduct {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (z : points B S hS 𝒵) (x : points B S hS 𝒳)
    (h : pointsMap B S hS g z = pointsMap B S hS f x) :
    ∃ p : points B S hS P.pt,
      pointsMap B S hS P.fst p = z ∧ pointsMap B S hS P.snd p = x := by
  classical
  obtain ⟨β, -⟩ := Quotient.exists_rep (hP.from (twoFibreProductSquare B S hS g f))
  exact Stack.exists_point_of_coneHom B S hS (toCatFiberedInGroupoids B S hS P)
    β.hom.hom β.isoFst.hom.hom β.isoSnd.hom.hom z x h

end AlgebraicStacks

/-- **Stacks 04ZU.** The base change of a surjective 1-morphism of algebraic stacks over `S` is
surjective: in a 2-fibre-product square over the cospan `(g, f)`, if `g` is surjective then so is
the projection to the source of `f`. -/
@[stacks 04ZU]
theorem isSurjective_of_isTwoFibreProduct
    {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : IsSurjective B S hS g) : IsSurjective B S hS P.snd := by
  intro x
  obtain ⟨z, hz⟩ := hg (AlgebraicStacks.pointsMap B S hS f x)
  obtain ⟨p, -, hp⟩ :=
    AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS P hP z x hz
  exact ⟨p, hp⟩

/-- **A 1-morphism of algebraic stacks whose underlying functor is an equivalence of categories
is surjective on points.** By **Stacks 003Z**, part (2) it has a quasi-inverse over the site, and
the induced map on points is a right inverse of the given one. -/
theorem surjective_pointsMap_of_isEquivalence {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (k : 𝒵 ⟶ 𝒳)
    (hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom)) :
    Function.Surjective (AlgebraicStacks.pointsMap B S hS k) := by
  obtain ⟨F, hF, η, ε, -, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒵.val.val.p 𝒳.val.val.p
      𝒵.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor k.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p k.hom) hk
  have hiso : (Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩) : 𝒳 ⟶ 𝒵) ≫ k ≅ 𝟙 𝒳 :=
    Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (BasedNatIso.mkNatIso (F := BasedFunctor.comp ⟨F, hF⟩ k.hom.hom)
        (G := BasedFunctor.id 𝒳.val.val) ε hε))
  have hfun : AlgebraicStacks.pointsMap B S hS k ∘ AlgebraicStacks.pointsMap B S hS
      (Bicategory.InducedBicategory.mkHom
        (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩) : 𝒳 ⟶ 𝒵) = id := by
    rw [← AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS hiso.hom,
      AlgebraicStacks.pointsMap_id]
  exact fun x => ⟨AlgebraicStacks.pointsMap B S hS _ x, congrFun hfun x⟩

/-- **Surjectivity of a 1-morphism of algebraic stacks is unchanged by precomposition with an
equivalence.** If the functor underlying `k : 𝒵 ⟶ 𝒳` is an equivalence of categories and
`f : 𝒳 ⟶ 𝒴` is surjective, then so is `k ≫ f`. -/
theorem isSurjective_comp_of_isEquivalence {𝒵 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (k : 𝒵 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hk : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor k.hom))
    (hf : IsSurjective B S hS f) :
    IsSurjective B S hS (k ≫ f) := by
  rw [IsSurjective, AlgebraicStacks.pointsMap_comp]
  exact hf.comp (surjective_pointsMap_of_isEquivalence B S hS k hk)

end AlgebraicGeometry.Stack

end
