module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeUniversalHomeo
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# The residual gerbe of a gerbe (Stacks 0H24)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which makes `𝒳` a gerbe over `𝒴`
(**Stacks 06QC**), let `x` be a point of `𝒳` and let `y = f(x)` be its image in `|𝒴|`. Stacks
0H24 says that the residual gerbe of `𝒳` at `x` exists as soon as the residual gerbe `𝒵_y` of
`𝒴` at `y` does, and that it is then the 2-fibre product `𝒵_y ×_𝒴 𝒳`.

The existence half is what is proved here, in the form in which Stacks 06MT states existence:
condition (1) of Stacks 06MT — some algebraic stack admits a monomorphism to the stack whose
space of points is a singleton over the given point — transports from `𝒴` at `y` to `𝒳` at `x`.
The source's argument is run on the 2-fibre product `𝒵 ×_𝒴 𝒳` of the given one-point substack
`𝒵 ⟶ 𝒴`: the projection to `𝒳` is a monomorphism because it is a base change of `𝒵 ⟶ 𝒴`, and
the projection to `𝒵` is a gerbe by **Stacks 06QE**, which already forces the apex to have a
single point over `x`.

## Main results

* `Stack.AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks`: a base change
  of a monomorphism of algebraic stacks along the canonical 2-fibre product square is a
  monomorphism, i.e. **Stacks 04ZW** is stable under base change.
* `Stack.hasSingletonPointMonomorphism_of_isGerbeOver`: the existence clause of **Stacks 0H24**.

## Implementation notes

The source deduces that the apex has a single point from the fact that the projection to `𝒵` is
a universal homeomorphism (Stacks 06R9), hence in particular a bijection on points. Only
*injectivity* of the map on points is needed, and that is
`AlgebraicGeometry.Stack.injective_pointsMap_of_isGerbeOver`; surjectivity is replaced by the
explicit lift of the pair `(x, z)` supplied by **Stacks 04XH**.

Base change of a monomorphism is proved only for the *canonical* square
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` and not for an arbitrary 2-fibre
product square of algebraic stacks. The argument is that of
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` (Stacks 045C) transcribed with
`CategoryTheory.Mono` in place of the property:
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` is exactly the body of
`AlgebraicGeometry.Stack.HasRelativeProperty` so transcribed, since the locality instance that
the latter demands is unavailable for monomorphisms of algebraic spaces.
That argument runs through `AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver`, whose
hypothesis is a 2-fibre product in the 2-category of categories fibred in groupoids; a 2-fibre
product in the 2-category of algebraic stacks is strictly weaker, so the implication runs the
wrong way. The canonical square is the one square for which the stronger witness
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare` is available
unconditionally, and it is the square the proof of Stacks 0H24 uses.

The identification of the residual gerbe of `𝒳` at `x` with `𝒵_y ×_𝒴 𝒳` — the second assertion
of Stacks 0H24 — is not proved.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 0H24](https://stacks.math.columbia.edu/tag/0H24)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A monomorphism of algebraic stacks over `S` (Stacks 04ZW) is stable under base change**
along the canonical 2-fibre product square of **Stacks 04T2**: if `i : 𝒵 ⟶ 𝒴` is a monomorphism
then so is the projection `𝒳 ×_𝒴 𝒵 ⟶ 𝒳` for every `f : 𝒳 ⟶ 𝒴`.

This is the argument of `AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`
(**Stacks 045C**) with `CategoryTheory.Mono` in place of the property: a scheme-valued point of
`𝒳` and an algebraic space representing the base change of the projection along it also
represent the base change of `i` along the composite point of `𝒴`, so the monomorphism clause
of `i` applies to that algebraic space verbatim. It is stated for the canonical square because
the comparison with the 2-fibre product of categories fibred in groupoids which that argument
goes through is available only there; see the implementation notes. -/
theorem AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (i : 𝒵 ⟶ 𝒴)
    (hi : AlgebraicStacks.IsMonomorphism B S hS i) :
    AlgebraicStacks.IsMonomorphism B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f i).fst := by
  obtain ⟨hirep, hmono⟩ := hi
  have hQ := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    f.hom i.hom
  refine ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
    𝒵.val 𝒴.val 𝒳.val i.hom f.hom _ hQ hirep, ?_⟩
  intro U z hz F hF he
  refine hmono U (z ⋙ f.hom.hom.toFunctor) (by rw [Functor.assoc, f.hom.hom.w, hz]) F hF ?_
  obtain ⟨e⟩ := he
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, u, u + 1} B S hS
    𝒵.val 𝒴.val 𝒳.val i.hom f.hom _ hQ U z hz
  exact ⟨E.symm.trans e⟩

/-- **The existence clause of Stacks 0H24.** Let `f : 𝒳 ⟶ 𝒴` make `𝒳` a gerbe over `𝒴` and let
`x` be a point of `𝒳`. If condition (1) of **Stacks 06MT** holds for `𝒴` at the image of `x`,
then it holds for `𝒳` at `x`; that is, the residual gerbe of `𝒳` at `x` exists as soon as the
residual gerbe of `𝒴` at `f(x)` does.

Writing `i : 𝒵 ⟶ 𝒴` for the one-point monomorphism over `f(x)`, the witness is the 2-fibre
product `𝒳 ×_𝒴 𝒵` with its projection to `𝒳`, which is a monomorphism by
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks`.
Its projection to `𝒵` is again a gerbe (**Stacks 06QE**), hence injective on points, and `𝒵` has
a single point; so the apex has at most one point, and **Stacks 04XH** produces one lying over
`x`. The identification of the residual gerbe with that 2-fibre product is not proved. -/
@[stacks 0H24 "existence clause: condition (1) of Stacks 06MT transports along a gerbe"]
theorem hasSingletonPointMonomorphism_of_isGerbeOver
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsGerbeOver B S hS f)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (hy : HasSingletonPointMonomorphism B S hS 𝒴
      (pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
        (Classical.choose 𝒴.property) f.hom.hom x)) :
    HasSingletonPointMonomorphism B S hS 𝒳 x := by
  obtain ⟨𝒵, i, hi, zpt, hzuniq, hzmap⟩ := hy
  set P := twoFibreProductSquareAlgebraicStacks B S hS f i
  have hPprod : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f i
  have hfst : AlgebraicStacks.IsMonomorphism B S hS P.fst :=
    AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks B S hS f i hi
  have hsnd : AlgebraicStacks.IsGerbeOver B S hS P.snd :=
    AlgebraicStacks.isGerbeOver_of_isTwoFibreProduct B S hS P hPprod hf
  have hinj : Function.Injective (AlgebraicStacks.pointsMap B S hS P.snd) :=
    injective_pointsMap_of_isGerbeOver B S hS P.snd hsnd
  obtain ⟨p, hp₁, hp₂⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hPprod x zpt hzmap.symm
  exact ⟨P.pt, P.fst, hfst, p, fun p' => hinj ((hzuniq _).trans hp₂.symm), hp₁⟩

end AlgebraicGeometry.Stack

end
