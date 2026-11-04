module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict

/-!
# A relative property is invariant under equivalence, in both directions (Stacks 0459)

**Stacks 0459.** Let `P` be a property of morphisms of algebraic spaces over `S` as in
Definition **Stacks 03YK**, and let

```
𝒳' ⟶ 𝒳
 |f'    |f
 v      v
𝒴' ⟶ 𝒴
```

be a 2-commutative square of 1-morphisms of categories fibred in groupoids over the big fppf site
of `S` whose two horizontal 1-morphisms are equivalences, with `f` — equivalently, by
**Stacks 0457**, with `f'` — representable by algebraic spaces. Then `f` has `P` if and only if
`f'` has `P`. The source gives no proof.

One direction is already available: `AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences`
carries the relative property from `f` to `f'`, resting on the pointwise comparison
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalences` — for a scheme-valued point
`y'` of `𝒴'`, the base change of `f'` along `y'` is equivalent *over the big fppf site of the
scheme the point lives on* to the base change of `f` along the transported point `y' ⋙ b`. This
file supplies the other direction and the equivalence.

The reverse direction needs one thing the forward one does not: a point of `𝒴` has to be *pushed
back* to a point of `𝒴'`, and that needs the quasi-inverse of `b`. **Stacks 003Z part (2)**
(`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`) supplies it as a 1-morphism
*over the site*, together with a counit all of whose components are vertical. For a point `y` of
`𝒴` the transported point is `y ⋙ b⁻¹`, and the counit identifies `(y ⋙ b⁻¹) ⋙ b` with `y` by a
2-isomorphism with vertical components — so the comparison of the two base changes is the pointwise
one above followed by a reindexing of the *first* leg of the 2-fibre product, which is
`CategoryTheory.TwoFibreProductOver.reindexEquivalenceOver`.

No hypothesis on `P` is used by the argument, in either direction: the algebraic space whose
structural morphism the relative property tests is literally the same one on both sides. The two
instance hypotheses of `AlgebraicGeometry.Stack.HasRelativeProperty` are in scope only because the
equivalence is stated through that abbreviation.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_of_equivalences_symm`: the reverse of
  `AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, with the relative property written
  out as the quantifier of Stacks 03YK.
* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_equivalences'`: **Stacks 0459**, with the
  representability witness of `f'` an arbitrary one rather than the image of the witness of `f`.

## Implementation notes

The reverse direction is written out as the quantifier of
`AlgebraicGeometry.Stack.HasRelativeProperty` rather than through the abbreviation, as
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` already does, so that neither instance
hypothesis of that abbreviation has to be supplied; the four categories fibred in groupoids then
carry four independent universe pairs, as they do for the forward direction and for Stacks 0457.

The equivalence takes representability of both vertical 1-morphisms as hypotheses, where the source
says "`f` (or equivalently `f'`)". That is a generalisation rather than a weakening:
`AlgebraicGeometry.Stack.HasRelativeProperty` does not use its representability argument in its
body, so the statement quantified over an arbitrary proof for `f'` implies the one in which that
proof is the image of the given one under Stacks 0457. The universes of the two sides are pinned
to two pairs rather than four because Stacks 03YK itself requires a 1-morphism's source and target
to share a universe pair; that is the widest form in which the equivalence can be stated.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Pointwise

variable {𝒳' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
  {𝒴' : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}
  {𝒴 : CatFiberedInGroupoids.{u, v₄, u + 1, w₄} (BigFppfOver B S hS)}

/-- **The reverse of `AlgebraicGeometry.Stack.relativeProperty_of_equivalences`.** In a
2-commutative square whose two horizontal 1-morphisms `a` and `b` are equivalences, the relative
property at `P` passes from `f'` back to `f`.

A point `y` of `𝒴` is pushed back to the point `y ⋙ b⁻¹` of `𝒴'` along the quasi-inverse of `b`
over the site (**Stacks 003Z**, part (2)), whose counit identifies `(y ⋙ b⁻¹) ⋙ b` with `y` by a
2-isomorphism with vertical components. The base change of `f'` along `y ⋙ b⁻¹` is then equivalent
to the base change of `f` along `(y ⋙ b⁻¹) ⋙ b` by
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalences`, and that to the base change
of `f` along `y` by reindexing the first leg
(`CategoryTheory.TwoFibreProductOver.reindexEquivalenceOver`). -/
theorem relativeProperty_of_equivalences_symm (P : MorphismProperty (AlgebraicSpaces B S hS))
    (f' : 𝒳'.val ⥤ᵇ 𝒴'.val) (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f ≅ BasedFunctor.comp f' b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (hP' : ∀ (U : BigFppfOver B S hS)
      (y' : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴'.val.obj)
      (_hy' : y' ⋙ 𝒴'.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.val.p 𝒴'.val.p y' f'.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y f.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  rintro U y hy F hF ⟨E⟩
  -- a quasi-inverse of `b` over the site, with a vertical counit
  obtain ⟨bInv, hbInv, _ηb, εb, _hηb, hεb⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒴'.val.p 𝒴.val.p
      𝒴'.isFiberedInGroupoids 𝒴.isFiberedInGroupoids b.toFunctor b.w
      (inferInstance : b.toFunctor.IsEquivalence)
  -- the point of `𝒴'` that `y` pushes back to
  have hy' : (y ⋙ bInv) ⋙ 𝒴'.val.p = Over.map U.hom := by
    rw [Functor.assoc, hbInv, hy]
  -- the counit identifies `(y ⋙ b⁻¹) ⋙ b` with `y`, vertically
  let θ : (y ⋙ bInv) ⋙ b.toFunctor ≅ y :=
    NatIso.ofComponents (fun z => εb.app (y.obj z)) fun k => εb.hom.naturality (y.map k)
  have hθ (z : BigFppfOver B U.left.1 U.left.2) : 𝒴.val.p.IsHomLift
      (𝟙 ((Over.map U.hom).obj z)) (θ.hom.app z) := by
    have hz : 𝒴.val.p.obj (y.obj z) = (Over.map U.hom).obj z := Functor.congr_obj hy z
    rw [← hz]
    exact hεb (y.obj z)
  -- the pointwise comparison, then the reindexing of the first leg
  obtain ⟨k⟩ :=
    nonempty_equivalenceOver_fst_of_equivalences B S hS f' f a b α U (y ⋙ bInv) hy'
  exact hP' U (y ⋙ bInv) hy' F hF
    ⟨k.trans ((TwoFibreProductOver.reindexEquivalenceOver
      (G := f.toFunctor) θ hθ).trans E)⟩

end Pointwise

section Iff

variable {𝒳' 𝒴' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}

/-- **Stacks 0459.** In a 2-commutative square of categories fibred in groupoids over the big fppf
site of `S` whose two horizontal 1-morphisms are equivalences, a vertical 1-morphism representable
by algebraic spaces has the relative property at `P` of **Stacks 03YK** exactly when the other
one does.

The forward direction is `AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences` and the
reverse one `AlgebraicGeometry.Stack.relativeProperty_of_equivalences_symm`; neither uses any
hypothesis on `P`, which is carried only because the statement mentions the abbreviation.

The representability witness for `f'` is an arbitrary one, which is what distinguishes this from
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_equivalences` of
`StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence`: that form reads the witness
for `f'` off the one for `f` through Stacks 0457, and is the special case of this one at that
witness. -/
@[stacks 0459 "the same biconditional assembled from the two one-directional statements"]
theorem hasRelativeProperty_iff_of_equivalences' (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f.hom ≅ BasedFunctor.comp f'.hom b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hf' : IsRepresentableByAlgebraicSpaces B S hS f'.hom) :
    HasRelativeProperty.{u, v₂, w₂} B S hS P f hf ↔
      HasRelativeProperty.{u, v₁, w₁} B S hS P f' hf' :=
  ⟨hasRelativeProperty_of_equivalences B S hS P f' f a b α hf hf',
    relativeProperty_of_equivalences_symm B S hS P f'.hom f.hom a b α⟩

end Iff

end AlgebraicGeometry.Stack

end
