module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase

/-!
# The algebraic space of a representable base change

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category
of schemes over `S`, representable by algebraic spaces, and let `y` be a scheme-valued point
of `𝒴` over a scheme `U` of the site. The 2-fibre product `(Sch/U)_{fppf} ×_{y, 𝒴} 𝒳` is then
equivalent, over the big fppf category of `U`, to an algebraic space `F_y` over `U`. Read over
`S` instead, `F_y` carries a canonical morphism `F_y ⟶ U`: its underlying presheaf is the
lower-shriek extension of the representing space, and the structural morphism sends the section
indexed by a factorization through `U` to that factorization.

## Main results

* `AlgebraicGeometry.Stack.exists_algebraicSpace_over_baseChange`: the represented 2-fibre
  product, its algebraic space over `S`, and the canonical map to `U`.

## References

* [Stacks Project, Tag 0402](https://stacks.math.columbia.edu/tag/0402)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

/-- The algebraic space representing the 2-fibre product of a 1-morphism representable by
algebraic spaces with a scheme-valued point `y` of its target, viewed over the original base,
comes with its canonical morphism to `U`. The representing equivalence is over the big fppf
category of `U`. -/
@[stacks 0402]
theorem exists_algebraicSpace_over_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom) :
    ∃ (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
      (Fy : SpacesOverSmallerBase B U.left.1 S U.left.2 hS U.hom),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) ∧
      Fy = (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩ ∧
      ∃ (ι : Fy.1.left ≅ (OverShriek.relocalizePresheafFunctor U.hom).obj F),
        ∀ (W : BigFppfOver B S hS) (s : Fy.1.left.obj (op W)),
          (Fy.1.hom.app (op W) s).left = (ι.hom.app (op W) s).1.1 := by
  obtain ⟨F, hF, hEquiv⟩ := hf U y hy
  let X : AlgebraicSpaces B U.left.1 U.left.2 := ⟨F, hF⟩
  let Fy : SpacesOverSmallerBase B U.left.1 S U.left.2 hS U.hom :=
    (spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj X
  refine ⟨F, hF, Fy, hEquiv, rfl,
    (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app X, fun W s => ?_⟩
  let ι := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app X
  let t := ι.hom.app (op W) s
  have hback : (ι.inv.app (op W)) t = s :=
    congrArg (fun g => g s) (ι.hom_inv_id_app (op W))
  have hcompat : (Fy.1.hom.app (op W)) ((ι.inv.app (op W)) t) =
      Over.homMk t.1.1 t.2 :=
    spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      B U.left.1 S U.left.2 hS U.hom X (op W) t
  rw [hback] at hcompat
  simpa [Fy, t, ι] using congrArg (fun z => z.left) hcompat

end AlgebraicGeometry.Stack

end
