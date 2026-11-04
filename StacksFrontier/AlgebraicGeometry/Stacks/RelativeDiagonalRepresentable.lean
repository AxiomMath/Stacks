module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaProjectionRepresentable

/-!
# The relative diagonal of a morphism of algebraic stacks (Stacks 04XS, part 1)

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over the big fppf site of `S`. Then the relative diagonal

`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`

is representable by algebraic spaces (Stacks 02ZW). This is part (1) of **Stacks 04XS**.

Only the second clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` is used, namely that the
*absolute* diagonals of `𝒳` and of `𝒴` are representable by algebraic spaces — condition (1) of
Stacks 045G. Given that, the content is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal`: the relative
diagonal lies over `𝒳 × 𝒳`, the projection `𝒳 ×_𝒴 𝒳 ⟶ 𝒳 × 𝒳` is a base change of the diagonal
of `𝒴` (Stacks 02XE, so Stacks 0302 applies to it), and the composite of `Δ_f` with that
projection is the absolute diagonal of `𝒳`; cancelling a representable postcomposition
(Stacks 02X2) leaves `Δ_f` representable.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_of_isAlgebraicStack`:
  **Stacks 04XS part (1)**, for 1-morphisms of categories fibred in groupoids that are algebraic
  stacks.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks`:
  the same for a 1-morphism of the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of
  Stacks 03YP, which is the form the statement is quoted in. Untagged — it is the previous
  theorem instantiated at `v := u`, `w := u + 1`.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack`: the
  left vertical arrow of the square 04XT inside the source's proof, read off the conclusion:
  for a scheme-valued point `(x, x', α)` of `𝒳 ×_𝒴 𝒳` over `U`, the presheaf
  `Isom_𝒳(x, x') ×_{Isom_𝒴(f x, f x'), α} U` is an algebraic space over `U`. This is what
  part (2) of Stacks 04XS is a statement about.

## Implementation notes

The source proves part (1) through the Isom-sheaf square of Stacks 04XT: for a scheme-valued
point `a = (x, x', α)` of `𝒳 ×_𝒴 𝒳` over `T`, the fibre `𝒳 ×_{𝒳 ×_𝒴 𝒳, a} T` is the fibre
product `Isom_𝒳(x, x') ×_{Isom_𝒴(f x, f x'), α} T`, an algebraic space because both Isom sheaves
are. That square is available here, as
`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.equivalenceOver` and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_iff`, but it is not
the route taken: the cancellation argument recorded above reaches the same conclusion from the
representability of the two absolute diagonals alone, which is literally a clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`, so no statement about Isom presheaves of an
algebraic stack is needed.

The universes are those of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal`, i.e. the saturated
ones Stacks 0302 forces. Instantiating them at `v := u` and `w := u + 1` gives
`CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, the universes
`AlgebraicGeometry.Stack.AlgebraicStacks` is formed at, which is why the 2-category form is a
direct specialisation.

Only **one** declaration carries the Stacks tag under the part key *diagonal_representable*,
namely the general `…_of_isAlgebraicStack`. The `AlgebraicStacks` form below is it instantiated at
`v := u`, `w := u + 1`; its proof is a single application of it, so by the covering-set rule it
is not part of the covering set and is left untagged. It is kept because it is the form
`…Stacks/RelativeDiagonalMonomorphism.lean` consumes, so nothing resolves differently; the tag
simply names the statement that *is* the lemma rather than one of its instances.

Part (2) of Stacks 04XS, that `Δ_f` is locally of finite type, is not proved here; it needs
Stacks 04XR, and it is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDiagonalFiniteType.lean`, which carries the second
part key *diagonal_locally_finite_type*.

## References

* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04XS, part (1).** The relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` of a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over the big fppf site of `S` is representable by
algebraic spaces.

Only the representability of the absolute diagonals of `𝒳` and of `𝒴` — the second clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` — is used, by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal`. -/
@[stacks 04XS "diagonal_representable"]
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_of_isAlgebraicStack
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, t} B S hS 𝒴.val) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom) := by
  obtain ⟨hfib𝒳, -, hΔ𝒳, -⟩ := h𝒳
  obtain ⟨hfib𝒴, -, hΔ𝒴, -⟩ := h𝒴
  exact isRepresentableByAlgebraicSpaces_relativeDiagonal B S hS 𝒳 𝒴 f hΔ𝒳 hΔ𝒴

/-- **Stacks 04XS, part (1), in the 2-category of algebraic stacks.** The relative diagonal of a
1-morphism of the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of Stacks 03YP is
representable by algebraic spaces.

Untagged: this is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_of_isAlgebraicStack`
instantiated at `v := u`, `w := u + 1`, so the part key *diagonal_representable* sits on that
one. See the implementation notes. -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom) :=
  isRepresentableByAlgebraicSpaces_relativeDiagonal_of_isAlgebraicStack.{u, u, u + 1}
    B S hS 𝒳.val 𝒴.val f.hom 𝒳.2 𝒴.2

/-- **The Isom-sheaf square of Stacks 04XT, for a 1-morphism of algebraic stacks.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, let `U` be a scheme over `S` and let `Y` be a
point of `𝒳 ×_{f, 𝒴, f} 𝒳` over the big fppf site of `U` — a triple `(x, x', α)` by 2-Yoneda.
Then the presheaf on the site of `U` of vertical morphisms `x ⟶ x'` whose image under `f` is
`α`, that is the fibre product

`Isom_𝒳(x, x') ×_{Isom_𝒴(f x, f x'), α} U`,

is an algebraic space over `U`.

This is the left vertical arrow of the square labelled 04XT in the source's proof of Stacks
04XS, and it is what part (2) of Stacks 04XS is proved about. It is obtained here by reading
part (1) through the criterion
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_iff` rather than used
to prove it, which is the opposite of the source's order; the comparison is mediated by
`CategoryTheory.uliftFunctor` because the presheaf of vertical morphisms takes values in the
morphism universe of `𝒳` while an algebraic space is a presheaf of `Type u`. -/
theorem isAlgebraicSpace_relVertHomPresheaf_of_isAlgebraicStack
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, t} B S hS 𝒴.val)
    (U : BigFppfOver B S hS)
    (Y : BigFppfOver B U.left.1 U.left.2 ⥤
      TwoFibreProductOver 𝒳.val.p 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.toFunctor)
    (hY : Y ⋙ RelProdP 𝒳.val.p 𝒴.val.p f.hom.toFunctor = Over.map U.hom) :
    ∃ F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 F ∧
        Nonempty (relVertHomPresheaf 𝒴.isFiberedInGroupoids 𝒳.isFiberedInGroupoids hY f.hom.w ⋙
            uliftFunctor.{u, max u v} ≅ F ⋙ uliftFunctor.{max u v, u}) :=
  (isRepresentableByAlgebraicSpaces_relativeDiagonal_iff B S hS 𝒳 𝒴 f.hom).mp
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_of_isAlgebraicStack B S hS 𝒳 𝒴 f h𝒳 h𝒴)
    U Y hY

end AlgebraicGeometry.Stack

end
