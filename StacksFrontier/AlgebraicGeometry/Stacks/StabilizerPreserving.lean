module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# Stabilizer-preserving morphisms of algebraic stacks under base change (Stacks 0DUB)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site. The
*inertia* of `𝒳` is the category of pairs `(x, α)` with `α` an automorphism of `x` lying over an
identity (`CategoryTheory.RelativeInertia`), and `f` is *stabilizer preserving* when the
canonical comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of Stacks 06R5
(`CategoryTheory.inertiaPullbackComparison`) is an isomorphism.

**Stacks 0DUB, part (2)** says that this condition is stable under base change: in a cartesian
square of algebraic stacks, if the comparison for `f` is an equivalence then so is the
comparison for the base change of `f`.

## Main results

* `AlgebraicGeometry.Stack.nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange`:
  **Stacks 0DUB, part (2)**.

Part (1) of Stacks 0DUB, the pointwise statement about automorphism groups at a point of `|𝒳|`,
is not here: it is stated in terms of the notion of Stacks 0DTW, which the library does not yet
have.

## Implementation notes

All of the mathematics is in
`CategoryTheory.nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange`
(`StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange`), which is stated for a square
of plain categories over a base category whose comparison to the concrete 2-fibre product
`CategoryTheory.TwoFibreProductOver` is fully faithful. What is left here is to supply that
hypothesis for a 2-fibre product in the 2-category of *algebraic stacks*, which is where the
cartesian square of the source lives.

Two steps do it. First the square is pushed down to the 2-category of categories fibred in
groupoids with
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids`, since a
2-fibre product of algebraic stacks is also one of categories fibred in groupoids. Then the
comparison to the concrete 2-fibre product is exhibited as the underlying functor of a
pre-morphism of 2-commutative squares into
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`, whose underlying functor is an
equivalence by `CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`; an equivalence is
fully faithful.

The filler of the square is written out as an explicit `Iso.mk` of natural transformations
rather than taken as a projection of
`AlgebraicGeometry.Stack.AlgebraicStacks.toCatFiberedInGroupoids`, because that definition is
semireducible and a projection of it is opaque to instance search.

## References

* [Stacks Project, Tag 0DUB](https://stacks.math.columbia.edu/tag/0DUB)
* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0DUB, part (2).** In a cartesian square of algebraic stacks, if the canonical
comparison from the inertia of `𝒳` to `𝒳 ×_𝒴 ℐ_𝒴` is an equivalence, then so is the
corresponding comparison for the base change of `f` along `g`.

The base change of `f : 𝒳 ⟶ 𝒴` along `g : 𝒴' ⟶ 𝒴` is the first projection of a 2-fibre product
`P` of the cospan `(g, f)`. -/
@[stacks 0DUB "the inertia map of a base change"]
theorem nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : (CategoryTheory.inertiaPullbackComparison 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).IsEquivalence) :
    Nonempty (CategoryTheory.IsEquivalenceOver
      (RelativeInertia.toBase P.pt.val.val.p)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.toBase 𝒴'.val.val.p)
        P.pt.val.val.p 𝒴'.val.val.p (RelativeInertia.π 𝒴'.val.val.p)
        (CatFiberedInGroupoids.homFunctor P.fst.hom))
      (CategoryTheory.inertiaPullbackComparison P.pt.val.val.p 𝒴'.val.val.p
        (CatFiberedInGroupoids.homFunctor P.fst.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom))) := by
  -- the filler of the square, read in the 2-category of categories fibred in groupoids
  let t : (CatFiberedInGroupoids.homFunctor P.fst.hom ⋙
      CatFiberedInGroupoids.homFunctor g.hom) ≅
      (CatFiberedInGroupoids.homFunctor P.snd.hom ⋙
        CatFiberedInGroupoids.homFunctor f.hom) :=
    { hom := P.iso.hom.hom.hom.toNatTrans
      inv := P.iso.inv.hom.hom.toNatTrans
      hom_inv_id := congrArg (fun m => m.hom.hom.toNatTrans) P.iso.hom_inv_id
      inv_hom_id := congrArg (fun m => m.hom.hom.toNatTrans) P.iso.inv_hom_id }
  have ht : ∀ a, 𝒴.val.val.p.IsHomLift (𝟙 (P.pt.val.val.p.obj a)) (t.hom.app a) :=
    fun a => P.iso.hom.hom.hom.isHomLift' a
  -- the comparison to the concrete 2-fibre product is the mediating functor of a pre-morphism
  -- of 2-commutative squares into the canonical one, hence an equivalence
  let J := TwoFibreProductOver.lift 𝒴'.val.val.p 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom)
    P.pt.val.val.p (CatFiberedInGroupoids.homFunctor P.fst.hom)
    (CatFiberedInGroupoids.homFunctor P.snd.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom) t ht
  have hJ : J.IsEquivalence := by
    refine Bicategory.isEquivalence_of_isTwoFibreProduct
      (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        g.hom f.hom)
      { hom := Bicategory.InducedBicategory.mkHom
          { toFunctor := J
            w := TwoFibreProductOver.lift_comp_structureFunctor .. }
        isoFst := Iso.refl _
        isoSnd := Iso.refl _
        compat := ?_ }
    refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
    funext a
    exact CatFiberedInGroupoids.map_id_comp_id_eq
      (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor f.hom)
      (P.iso.hom.hom.hom.toNatTrans.app a)
  exact CategoryTheory.nonempty_inertiaPullbackComparison_isEquivalenceOver_baseChange
    𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p P.pt.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor P.fst.hom)
    (CatFiberedInGroupoids.homFunctor P.snd.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p P.fst.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p P.snd.hom) t ht
    (Functor.FullyFaithful.ofFullyFaithful _) hf

end AlgebraicGeometry.Stack

end
