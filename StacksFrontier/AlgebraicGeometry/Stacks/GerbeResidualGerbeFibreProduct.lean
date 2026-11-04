module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Reduced
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeUniversalHomeo
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The residual gerbe of a gerbe is the base change of the residual gerbe (Stacks 0H24)

**Stacks 0H24.** Let `π : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks. Let `x ∈ |𝒳|` with image
`y ∈ |𝒴|`. Assume the residual gerbe `𝒵_y ⊂ 𝒴` of `𝒴` at `y` exists and that `𝒳` is a gerbe
over `𝒴`. Then `𝒵_x = 𝒵_y ×_𝒴 𝒳` is the residual gerbe of `𝒳` at `x`.

In this library the residual gerbe of `𝒴` at `y` is the strictly full subcategory of `𝒴` cut out
by an object property `P` meeting the specification `AlgebraicGeometry.Stack.IsResidualGerbeAt`
of **Stacks 06MT** (closed under isomorphism, algebraic, reduced, locally Noetherian, with
exactly one point, lying over `y`); see `AlgebraicGeometry.Stack.residualGerbe`. The 2-fibre
product `𝒵_y ×_𝒴 𝒳` is realised inside `𝒳` as the strictly full subcategory on the objects `ξ`
with `P (π ξ)`, the inverse image `P.inverseImage π`. The statement proved is that this inverse
image meets the specification of the residual gerbe of `𝒳` at `x`, and that the square formed by
the two residual gerbes, their inclusions, `π` and the induced 1-morphism `𝒵_x ⟶ 𝒵_y` is a
2-fibre product in the 2-category of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.isReducedStack_of_isSmooth`: reducedness of an algebraic stack ascends
  along a smooth 1-morphism.
* `AlgebraicGeometry.Stack.isResidualGerbeAt_inverseImage_of_isGerbeOver`: **Stacks 0H24**.

## Implementation notes

That the inverse image is an algebraic stack and is the 2-fibre product `𝒵_y ×_𝒴 𝒳` is
`AlgebraicGeometry.Stack.isAlgebraicStack_inverseImage` and
`AlgebraicGeometry.Stack.isTwoFibreProduct_inverseImageSquare` (with its two legs exchanged);
the 1-morphism `𝒵_x ⟶ 𝒵_y` of the square is `AlgebraicGeometry.Stack.residualGerbeMap`, the
lift of `π` through the full subcategory `𝒵_y`, whose hypothesis holds by the definition of the
inverse image.

The proof of 0H24 is the source's: the projection `𝒵_x ⟶ 𝒵_y` is a base change of `π`, hence
smooth (**Stacks 0DN8**, **Stacks 075W**) and a gerbe (**Stacks 06QE**). Smoothness carries
reducedness (**Stacks 04YF**) and local Noetherianity (**Stacks 06R6**) from `𝒵_y` to `𝒵_x`;
**Stacks 04XH** produces a point of `𝒵_x` lying over `x` and over the unique point of `𝒵_y`, and
a gerbe is injective on points, so it is the only point of `𝒵_x`. The source deduces the
singleton from Stacks 06R9; only injectivity on points is needed. The inclusion `𝒵_x ⟶ 𝒳` is a
monomorphism, as the source notes, but the specification of Stacks 06MT asks for a strictly full
subcategory rather than a monomorphism, so that fact is not used.

## References

* [Stacks Project, Tag 0H24](https://stacks.math.columbia.edu/tag/0H24)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
* [Stacks Project, Tag 0DN8](https://stacks.math.columbia.edu/tag/0DN8)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Reducedness of an algebraic stack ascends along a smooth 1-morphism. -/
theorem isReducedStack_of_isSmooth {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsSmooth B S hS f) (h𝒴 : IsReducedStack B S hS 𝒴) :
    IsReducedStack B S hS 𝒳 := by
  refine (exists_scheme_atlas_iff_forall_scheme B S hS (fun T : Scheme.{u} => IsReduced T)
    𝒳).2 (fun V a ha => ?_)
  exact (exists_scheme_atlas_iff_forall_scheme B S hS (fun T : Scheme.{u} => IsReduced T) 𝒴).1
    h𝒴 V (a ≫ f) (AlgebraicStacks.isSmooth_comp B S hS a f ha hf)

/-- **Stacks 0H24.** Let `π : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` making `𝒳` a
gerbe over `𝒴`, let `x` be a point of `𝒳` and let `y` be its image in `|𝒴|`. Assume the residual
gerbe `𝒵_y ⊂ 𝒴` of `𝒴` at `y` exists, cut out by the object property `P` of `𝒴` (the
specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of Stacks 06MT). Then
`𝒵_x = 𝒵_y ×_𝒴 𝒳` is the residual gerbe of `𝒳` at `x`:

* the inverse image `P ∘ π` of `P` meets the residual-gerbe specification of `𝒳` at `x`, so the
  residual gerbe `𝒵_x` of `𝒳` at `x` exists and is the strictly full subcategory of `𝒳` on the
  objects sent into `𝒵_y`; and
* the square formed by the 1-morphism `𝒵_x ⟶ 𝒵_y` induced by `π`, the inclusion `𝒵_x ⟶ 𝒳`, and
  the inclusion `𝒵_y ⟶ 𝒴`, which commutes on the nose, is a 2-fibre product: `𝒵_x` with its
  inclusion into `𝒳` is the 2-fibre product `𝒵_y ×_𝒴 𝒳`.

Following the source: the inverse image is algebraic and is the 2-fibre product
(`AlgebraicGeometry.Stack.isAlgebraicStack_inverseImage`,
`AlgebraicGeometry.Stack.isTwoFibreProduct_inverseImageSquare`); its projection to `𝒵_y` is a
base change of `π`, hence smooth (**Stacks 0DN8**, **Stacks 075W**) and a gerbe
(**Stacks 06QE**), so the apex is reduced and locally Noetherian as `𝒵_y` is (**Stacks 04YF**,
**Stacks 06R6**) and has exactly one point, which lies over `x` (**Stacks 04XH** and injectivity
of a gerbe on points). -/
@[stacks 0H24]
theorem isResidualGerbeAt_inverseImage_of_isGerbeOver
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsGerbeOver B S hS f)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (P : ObjectProperty 𝒴.val.val.obj)
    (hP : IsResidualGerbeAt B S hS 𝒴
      (pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
        (Classical.choose 𝒴.property) f.hom.hom x) P) :
    ∃ hQ : IsResidualGerbeAt B S hS 𝒳 x (P.inverseImage f.hom.hom.toFunctor),
      Nonempty (Bicategory.IsTwoFibreProduct
        ({ pt := residualGerbe B S hS 𝒳 x _ hQ
           fst := residualGerbeMap B S hS f hQ.2.choose hP.2.choose (fun _ h => h)
           snd := residualGerbeInclusion B S hS 𝒳 x _ hQ
           iso := Iso.refl _ } :
          Bicategory.TwoCommSq (residualGerbeInclusion B S hS 𝒴 _ P hP) f)) := by
  obtain ⟨hPiso, hPalg, hPred, hPnoeth, z, hz, hzy⟩ := hP
  have hQalg := isAlgebraicStack_inverseImage f P hPalg
  let Sq : Bicategory.TwoCommSq (fullSubcategoryInclusion 𝒴 P hPalg) f :=
    { pt := fullSubcategoryAlgebraicStack 𝒳 (P.inverseImage f.hom.hom.toFunctor) hQalg
      fst := residualGerbeMap B S hS f hQalg hPalg (fun _ h => h)
      snd := fullSubcategoryInclusion 𝒳 (P.inverseImage f.hom.hom.toFunctor) hQalg
      iso := Iso.refl _ }
  have hSq : Bicategory.IsTwoFibreProduct Sq :=
    Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_inverseImageSquare f P hPalg)
  have hsmooth : AlgebraicStacks.IsSmooth B S hS Sq.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS f (fullSubcategoryInclusion 𝒴 P hPalg) Sq hSq
      (AlgebraicStacks.isSmooth_of_isGerbeOver B S hS f hf)
  have hred : IsReducedStack B S hS Sq.pt :=
    isReducedStack_of_isSmooth B S hS Sq.fst hsmooth hPred
  have hnoeth : IsLocallyNoetherianStack B S hS Sq.pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Sq.fst
      (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Sq.fst hsmooth) hPnoeth
  have hgerbe : AlgebraicStacks.IsGerbeOver B S hS Sq.fst :=
    AlgebraicStacks.isGerbeOver_of_isTwoFibreProduct B S hS Sq.swap
      (Bicategory.isTwoFibreProduct_swap hSq) hf
  have hinj := injective_pointsMap_of_isGerbeOver B S hS Sq.fst hgerbe
  obtain ⟨p, hp₁, hp₂⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS Sq hSq z x hzy
  exact ⟨⟨inferInstance, hQalg, hred, hnoeth, p,
    fun p' => hinj ((hz _).trans (hz _).symm), hp₂⟩, ⟨hSq⟩⟩

end AlgebraicGeometry.Stack

end
