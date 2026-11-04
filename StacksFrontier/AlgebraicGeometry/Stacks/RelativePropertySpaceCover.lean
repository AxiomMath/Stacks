module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented

/-!
# Testing a relative property on one base change by an algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a property of morphisms of
algebraic spaces over `S` which is stable under base change and local on the target for the fppf
precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big
fppf site of `S` which is representable by algebraic spaces. Stacks 04XC tests the relative
property of Stacks 03YK on *every* base change of `f` by a stack representable by an algebraic
space. Properties of Stacks, Lemma 04XD says that *one* such base change suffices, provided the
1-morphism `g : 𝒲 ⟶ 𝒴` it is taken along is surjective, flat and locally of finite presentation:
writing `𝒲` for an algebraic space `W` over `S` and `V` for the algebraic space representing
`𝒲 ×_𝒴 𝒳`, the morphism `V ⟶ W` has `P` exactly when `f` has it relatively.

Here the hypothesis on `g` is *local essential surjectivity*, the hypothesis of Stacks 045D:
every object of a fibre of `𝒴` becomes, after restriction to a covering sieve, isomorphic to the
image of an object of `𝒲`. It is implied by `g` being surjective, flat and locally of finite
presentation.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_of_prop_representingMap_of_localEssSurj`: if
  `V ⟶ W` has `P`, then `f` has the relative property `P`.
* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap_of_localEssSurj`: the
  equivalence.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
  [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
  (𝒳 𝒴 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)

/-- Let `P` be a property of morphisms of algebraic spaces over `S` stable under base
change and local on the target for the fppf precoverage, let `f : 𝒳 ⟶ 𝒴` be representable by
algebraic spaces and let `g : 𝒲 ⟶ 𝒴` be a 1-morphism along which every object of a fibre of `𝒴`
becomes, after restriction to a covering sieve, isomorphic to the image of an object of `𝒲`. Fix
a 2-fibre product square over the cospan `(g, f)` whose apex and whose `𝒲` are representable by
algebraic spaces `V` and `W`. If the induced morphism `V ⟶ W` of representing presheaves has `P`,
then `f` has the relative property `P` of Stacks 03YK. -/
theorem hasRelativeProperty_of_prop_representingMap_of_localEssSurj
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒲.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1,
            𝒴.val.p.IsHomLift k φ)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p)
    (hprop : P (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :
      (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS))) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P f hf :=
  hasRelativeProperty_of_baseChange.{u, u, u, u} B S hS 𝒳 𝒴 𝒲 P f g Q hQ hf hg
    ((hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P Q.fst
      (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u} B S hS 𝒳 𝒴 𝒲 f g Q hQ hf)
      V W hV hW eV eW).2 hprop)

/-- In the situation of `hasRelativeProperty_of_prop_representingMap_of_localEssSurj`, `f` has
the relative property `P` of Stacks 03YK exactly when the morphism `V ⟶ W` of representing
presheaves induced by the first projection of the square has `P` as a morphism of algebraic spaces
over `S`. -/
theorem hasRelativeProperty_iff_prop_representingMap_of_localEssSurj
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒲.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1,
            𝒴.val.p.IsHomLift k φ)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (eV : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.p (presheafOfCategories (V ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      𝒲.val.p (presheafOfCategories (W ⋙ typeToCat)).p) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P f hf ↔
      P (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒲 V W eV eW Q.fst) :
        (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ (⟨W, hW⟩ : AlgebraicSpaces B S hS)) :=
  ⟨fun hP => prop_representingMap_of_hasRelativeProperty.{u, u} B S hS P f hf hP 𝒲 g Q hQ
      V W hV hW eV eW,
    hasRelativeProperty_of_prop_representingMap_of_localEssSurj B S hS P 𝒳 𝒴 𝒲 f g hf hg
      Q hQ V W hV hW eV eW⟩

end AlgebraicGeometry.Stack

end
