module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor

/-!
# Transporting an equivalence of comparison functors along a cube of categories

Consider two 2-commutative squares of categories over the cospans `F, G` and `F₁, G₁`,

```
  X ---fst--> A            X₁ ---fst₁--> A₁
  |           |F           |             |F₁
 snd          v           snd₁           v
  v           B            v             B₁
  C ----G---> B            C₁ ----G₁---> B₁
```

given as `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver`s `S` and `S₁`, together with
functors `Φ_X, Φ_A, Φ_B, Φ_C` from the corners of the first to those of the second and natural
isomorphisms filling the four side faces of the cube they span. When the top and bottom faces
and the four side faces paste to the same 2-cell (the cube coherence `h`), the comparison functor
`X ⥤ A ×_B C` of the first square followed by the functor induced on 2-fibre products
(Stacks 02XA) is the comparison functor of the second square preceded by `Φ_X`.

Hence, if `Φ_X, Φ_A, Φ_C` are equivalences and `Φ_B` is fully faithful, the comparison functor of
the second square is an equivalence as soon as that of the first one is: the induced functor is
an equivalence by Stacks 02XB (3).

## Main results

* `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.comparisonCubeIso`: the natural
  isomorphism between the two composites around the cube.
* `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.isEquivalence_of_cube`: **the transport
  of the equivalence of comparison functors along the cube.**

## References

* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
* [Stacks Project, Tag 02XB](https://stacks.math.columbia.edu/tag/02XB)
-/

@[expose] public section

namespace CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

variable {X A B C X₁ A₁ B₁ C₁ : Type*}
  [Category X] [Category A] [Category B] [Category C]
  [Category X₁] [Category A₁] [Category B₁] [Category C₁]
  {F : A ⥤ B} {G : C ⥤ B} (S : CatCommSqOver F G X)
  {F₁ : A₁ ⥤ B₁} {G₁ : C₁ ⥤ B₁} (S₁ : CatCommSqOver F₁ G₁ X₁)
  (ΦX : X ⥤ X₁) (ΦA : A ⥤ A₁) (ΦB : B ⥤ B₁) (ΦC : C ⥤ C₁)
  (θfst : S.fst ⋙ ΦA ≅ ΦX ⋙ S₁.fst) (θsnd : S.snd ⋙ ΦC ≅ ΦX ⋙ S₁.snd)
  (θF : F ⋙ ΦB ≅ ΦA ⋙ F₁) (θG : G ⋙ ΦB ≅ ΦC ⋙ G₁)

/-- **The two composites around a cube of categories agree.** The comparison functor of `S`
followed by the functor induced on 2-fibre products by `Φ_A, Φ_B, Φ_C` is the comparison functor
of `S₁` preceded by `Φ_X`, provided the faces of the cube paste to the same 2-cell. -/
noncomputable def comparisonCubeIso
    (h : ∀ x : X, ΦB.map (S.iso.hom.app x) ≫ θG.hom.app (S.snd.obj x) ≫
        G₁.map (θsnd.hom.app x) =
      θF.hom.app (S.fst.obj x) ≫ F₁.map (θfst.hom.app x) ≫ S₁.iso.hom.app (ΦX.obj x)) :
    (toFunctorToCategoricalPullback F G X).obj S ⋙
        CategoricalPullback.map F G ΦA ΦC ΦB F₁ G₁ θG.symm θF ≅
      ΦX ⋙ (toFunctorToCategoricalPullback F₁ G₁ X₁).obj S₁ :=
  NatIso.ofComponents
    (fun x => CategoricalPullback.mkIso (θfst.app x) (θsnd.app x) (by
      refine (cancel_epi (θF.hom.app (S.fst.obj x))).1 ?_
      change θF.hom.app (S.fst.obj x) ≫ F₁.map (θfst.hom.app x) ≫ S₁.iso.hom.app (ΦX.obj x) =
        θF.hom.app (S.fst.obj x) ≫ (θF.inv.app (S.fst.obj x) ≫ ΦB.map (S.iso.hom.app x) ≫
          θG.hom.app (S.snd.obj x)) ≫ G₁.map (θsnd.hom.app x)
      simpa using (h x).symm))
    (fun {x y} u => by
      refine CategoricalPullback.hom_ext ?_ ?_
      · exact θfst.hom.naturality u
      · exact θsnd.hom.naturality u)

/-- **Transport of an equivalence of comparison functors along a cube of categories.** If the
faces of the cube paste to the same 2-cell, `Φ_X`, `Φ_A` and `Φ_C` are equivalences and `Φ_B` is
fully faithful, then the comparison functor `X₁ ⥤ A₁ ×_{B₁} C₁` of `S₁` is an equivalence as soon
as the comparison functor `X ⥤ A ×_B C` of `S` is. -/
theorem isEquivalence_of_cube
    (h : ∀ x : X, ΦB.map (S.iso.hom.app x) ≫ θG.hom.app (S.snd.obj x) ≫
        G₁.map (θsnd.hom.app x) =
      θF.hom.app (S.fst.obj x) ≫ F₁.map (θfst.hom.app x) ≫ S₁.iso.hom.app (ΦX.obj x))
    [ΦX.IsEquivalence] [ΦA.IsEquivalence] [ΦC.IsEquivalence] [ΦB.Full] [ΦB.Faithful]
    (hS : ((toFunctorToCategoricalPullback F G X).obj S).IsEquivalence) :
    ((toFunctorToCategoricalPullback F₁ G₁ X₁).obj S₁).IsEquivalence := by
  have := hS
  have : (CategoricalPullback.map F G ΦA ΦC ΦB F₁ G₁ θG.symm θF).IsEquivalence :=
    induced_isEquivalence_of_isEquivalence _ _ _ _ _
  have : (ΦX ⋙ (toFunctorToCategoricalPullback F₁ G₁ X₁).obj S₁).IsEquivalence :=
    Functor.isEquivalence_of_iso (comparisonCubeIso S S₁ ΦX ΦA ΦB ΦC θfst θsnd θF θG h)
  exact Functor.isEquivalence_of_comp_left ΦX _

end CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
