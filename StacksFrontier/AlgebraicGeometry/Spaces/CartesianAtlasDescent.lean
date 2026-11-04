module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent

/-!
# Cartesian squares descend along a surjective étale atlas

Let

```
A' --φ--> A
|π'       |π
v         v
Y  --f--> X
```

be a commutative square of sheaves on the big fppf site of a scheme `S`, and let
`u : h_U ⟶ Y` be a surjective étale atlas of `Y` with kernel pair `R ⇉ U`. If the base change
`V = U ×_Y A'` of the atlas is represented, with a represented kernel pair `R' ⇉ V` lying over
`R ⇉ U`, and the composite square `V ⟶ A` over `U ⟶ X` is cartesian, then the square itself is
cartesian. The comparison `A' ⟶ Y ×_X A` becomes the identity of `V` after the base change along
the atlas, and its inverse descends from `V` along the atlas `V ⟶ Y ×_X A`.

## Main results

* `CategoryTheory.IsKernelPair.of_isPullback`: the kernel pair of a base change is the base
  change of the kernel pair.
* `AlgebraicGeometry.Space.isPullback_of_isPullback_atlas`: cartesian squares descend along a
  surjective étale atlas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.IsKernelPair

variable {C : Type*} [Category C]

/-- **The kernel pair of a base change is the base change of the kernel pair.** If `a : V ⟶ W` is
the base change of `u : U ⟶ Y` along `q : W ⟶ Y`, `(s, t)` is a kernel pair of `u` and
`(s', t')` is a pair of maps out of `R'` equalized by `a` lying over `(s, t)`, with the square of
`s'` over `s` cartesian, then `(s', t')` is a kernel pair of `a`. -/
theorem of_isPullback {V W U Y R R' : C} {a : V ⟶ W} {q : W ⟶ Y} {p : V ⟶ U} {u : U ⟶ Y}
    (ha : IsPullback a p q u) {s t : R ⟶ U} (hR : IsKernelPair u s t) {s' t' : R' ⟶ V}
    {pR : R' ⟶ R} (hs : IsPullback s' pR p s) (ht : t' ≫ p = pR ≫ t) (hst : s' ≫ a = t' ≫ a) :
    IsKernelPair a s' t' := by
  have hcomp := hs.paste_vert hR
  rw [← ht, ← ha.w] at hcomp
  exact IsPullback.of_bot hcomp hst ha

end CategoryTheory.IsKernelPair

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Cartesian squares descend along a surjective étale atlas.** A commutative square
`φ : A' ⟶ A` over `f : Y ⟶ X` of sheaves is cartesian as soon as it is after the base change
along a surjective étale atlas `u : h_U ⟶ Y`: the base change `V = U ×_Y A'` and a kernel pair
`R' ⇉ V` over the kernel pair `R ⇉ U` of the atlas being represented, and the composite square
`V ⟶ A` over `U ⟶ X` being cartesian. -/
theorem isPullback_of_isPullback_atlas {A' A Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A')
    (hA : Presheaf.IsSheaf (BigFppfOver.topology B S hS) A)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {φ : A' ⟶ A} {π' : A' ⟶ Y} {π : A ⟶ X} {f : Y ⟶ X} (w : φ ≫ π = π' ≫ f)
    {U R V R' : BigFppfOver B S hS} {u : yoneda.obj U ⟶ Y}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf u)
    {s t : R ⟶ U} (hR : IsPullback (yoneda.map s) (yoneda.map t) u u)
    {a : yoneda.obj V ⟶ A'} {p : V ⟶ U} (ha : IsPullback a (yoneda.map p) π' u)
    (hbig : IsPullback (a ≫ φ) (yoneda.map p) π (u ≫ f))
    {s' t' : R' ⟶ V} {pR : R' ⟶ R}
    (hs' : IsPullback (yoneda.map s') (yoneda.map pR) (yoneda.map p) (yoneda.map s))
    (ht' : t' ≫ p = pR ≫ t) (hst : yoneda.map s' ≫ a = yoneda.map t' ≫ a) :
    IsPullback φ π' π f := by
  have hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback π f) := by
    refine ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf (BigFppfOver.topology B S hS))
      (limit.isLimit _) ?_
    rintro (_ | _ | _)
    · exact hX
    · exact hA
    · exact hY
  let c : A' ⟶ pullback π f := pullback.lift φ π' w
  have ha' : IsPullback (a ≫ c) (yoneda.map p) (pullback.snd π f) u := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback π f)
    · rw [Category.assoc, pullback.lift_fst]
      exact hbig
    · rw [Category.assoc, pullback.lift_snd]
      exact ha.w
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hsa := MorphismProperty.of_isPullback ha.flip hsurj
  have hea := MorphismProperty.of_isPullback ha.flip hetale
  have hsa' := MorphismProperty.of_isPullback ha'.flip hsurj
  have hea' := MorphismProperty.of_isPullback ha'.flip hetale
  have hst' : yoneda.map s' ≫ a ≫ c = yoneda.map t' ≫ a ≫ c := by
    rw [← Category.assoc, hst, Category.assoc]
  have hK : IsKernelPair (a ≫ c) (yoneda.map s') (yoneda.map t') :=
    IsKernelPair.of_isPullback ha' hR hs' (by rw [← Functor.map_comp, ht', Functor.map_comp])
      hst'
  obtain ⟨d, hd, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS hQ (a ≫ c) hK hsa' hea'
    hA' a hst
  have hcd : c ≫ d = 𝟙 A' :=
    hom_ext_of_etale_atlas B S hS hA' hA' a hsa hea (by rw [← Category.assoc, hd, Category.comp_id])
  have hdc : d ≫ c = 𝟙 (pullback π f) :=
    hom_ext_of_etale_atlas B S hS hQ hQ (a ≫ c) hsa' hea'
      (by rw [← Category.assoc, hd, Category.comp_id])
  exact IsPullback.of_iso_pullback ⟨w⟩ ⟨c, d, hcd, hdc⟩ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Space

end
