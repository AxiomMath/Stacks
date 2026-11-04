module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaIntegralHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite

/-!
# Integral morphisms out of a finite coproduct of algebraic spaces

Let `fᵢ : F i ⟶ Y`, for `i` in a finite index type, be integral morphisms of algebraic spaces
over a scheme `S`, and let `G` be their coproduct as a sheaf of sets on the big fppf site of `S`.
Then the induced morphism `G ⟶ Y` is integral. This is the integral counterpart of Stacks 0CZ2,
which the library has for *finite* morphisms as
`AlgebraicGeometry.Space.isFinite_coproduct`, and it is the integrality half of the last step of
the proof of Stacks 09YB, where the cover of `X` is produced as a coproduct `Z' ⨿ T`.

The surjectivity half of that step needs no coproduct structure at all and is proved here too:
a morphism is surjective as soon as the images of enough morphisms factoring through it cover the
point space of the target.

## Main results

* `AlgebraicGeometry.Space.isIntegralHom_coproduct`: a morphism out of a finite coproduct of
  algebraic spaces whose restriction to each summand is integral is integral.
* `AlgebraicGeometry.Space.isSurjective_of_iUnion_range_pointsMap_eq_univ`: a morphism whose
  image on points contains the images of a family of morphisms through it covering the target is
  surjective.

## Implementation notes

**The integral statement follows the finite one exactly.** Over an affine test object each
summand contributes an affine object `V i` of the site with integral projection `p i` to the
test object; their coproduct in the site carries the induced morphism `d`, integral by
`AlgebraicGeometry.isIntegralHom_sigmaDesc_of_finite` and with affine source because an
integral morphism is affine and an affine morphism with affine target has affine source.
Universality of finite coproducts of sheaves identifies that coproduct with the base change.

The scheme-level input is `AlgebraicGeometry.isIntegralHom_sigmaDesc_of_finite` of
`StacksFrontier.AlgebraicGeometry.Limits.SigmaIntegralHom`, which proves it for a family that is
merely *locally finite* over the target. A second, private, copy of that statement also sits in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalization`, proved there by induction
on the index type for Stacks 0824 and usable nowhere else; it is left where it is, because the
instance search of that file is written against its shape.

The index type is in the same universe as the schemes, which the scheme-level statement requires;
the finite families this is applied to are two-member ones, so nothing is lost. Compare
`AlgebraicGeometry.Space.isFinite_coproduct`, whose scheme-level input
`AlgebraicGeometry.isFinite_sigmaDesc` has no such restriction.

**Surjectivity is not about coproducts.** `AlgebraicGeometry.Space.IsSurjective` is surjectivity
of the map on points of Tag 03BU, and the map on points is functorial, so the image of a
composite is contained in the image of its second factor. Nothing about the summands being a
coproduct, or even a jointly epimorphic family, is used; the hypothesis is exactly that the
images cover, which is how the source checks surjectivity of `Z' ⨿ T ⟶ X`.

## References

* [Stacks Project, Tag 0CZ2](https://stacks.math.columbia.edu/tag/0CZ2)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Surjectivity from a covering family of images.** A morphism `f : G ⟶ Y` of presheaves on
the big fppf site of `S` is surjective as soon as there is a family of morphisms `ιᵢ : F i ⟶ G`
for which the images of the composites `ιᵢ ≫ f` cover the point space of `Y`.

This is how the proof of Stacks 09YB checks that `Z' ⨿ T ⟶ X` is surjective: the two summands
cover between them. No relation between the `F i` and `G` beyond the given morphisms is used. -/
theorem isSurjective_of_iUnion_range_pointsMap_eq_univ {I : Type v}
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (ι : ∀ i, F i ⟶ G) (f : G ⟶ Y) (fᵢ : ∀ i, F i ⟶ Y) (hf : ∀ i, ι i ≫ f = fᵢ i)
    (hcov : (⋃ i, Set.range (pointsMap B S hS (F i) (fᵢ i))) = Set.univ) :
    IsSurjective B S hS f := by
  intro y
  obtain ⟨-, ⟨i, rfl⟩, x, hx⟩ := hcov.symm ▸ Set.mem_univ y
  refine ⟨pointsMap B S hS (F i) (ι i) x, ?_⟩
  rwa [← pointsMap_comp_apply, hf i]

/-- **Stacks 0CZ2 for integral morphisms.** Let `fᵢ : F i ⟶ Y`, for `i` in a finite index type,
be integral morphisms of algebraic spaces over `S`, and let `G` be their coproduct as a sheaf of
sets on the big fppf site of `S`. Then the induced morphism `G ⟶ Y` is integral.

The proof is that of `AlgebraicGeometry.Space.isFinite_coproduct` with
`AlgebraicGeometry.isIntegralHom_sigmaDesc_of_finite` in place of
`AlgebraicGeometry.isFinite_sigmaDesc`: over an affine test object the base change is the
morphism induced out of a finite coproduct of affine schemes by integral morphisms, which is
integral, and its source is affine because an integral morphism is affine. -/
theorem isIntegralHom_coproduct {I : Type u} [Finite I]
    (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i)) (hY : IsAlgebraicSpace B S hS Y)
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (fᵢ : ∀ i, F i ⟶ Y) (f : G.obj ⟶ Y) (hf : ∀ i, (ι i).hom ≫ f = fᵢ i)
    (hint : ∀ i, IsIntegralHom B S hS (fᵢ i)) :
    IsIntegralHom B S hS f := by
  classical
  have := AlgebraicGeometry.BigFppfOver.hasSheafify_type B S hS
  intro U hU ξ
  choose V p a hpb hV hp using fun i ↦ hint i U hU ξ
  let T := BigFppfOver.toScheme B S hS
  let J := BigFppfOver.topology B S hS
  let Fs : I → Sheaf J (Type u) := fun i ↦ ⟨F i, (hF i).isSheaf⟩
  let Ys : Sheaf J (Type u) := ⟨Y, hY.isSheaf⟩
  -- the coproduct of the representing objects, with its projection to the test object
  let W := BigFppfOver.sigmaObj B S hS V
  let d : W ⟶ U := Cofan.IsColimit.desc (BigFppfOver.isColimit_sigmaCofan B S hS V) p
  have hdfac : ∀ i, BigFppfOver.sigmaIncl B S hS V i ≫ d = p i := fun i ↦
    Cofan.IsColimit.fac (BigFppfOver.isColimit_sigmaCofan B S hS V) p i
  have hdfacS : ∀ i, Sigma.ι (fun j ↦ T.obj (V j)) i ≫ T.map d = T.map (p i) := by
    intro i
    have h : T.map (BigFppfOver.sigmaIncl B S hS V i) ≫ T.map d = T.map (p i) := by
      rw [← Functor.map_comp, hdfac]
    exact (congrArg (· ≫ T.map d) (BigFppfOver.toScheme_map_sigmaIncl B S hS V i)).symm.trans h
  have hd : T.map d = Sigma.desc fun i ↦ T.map (p i) :=
    Sigma.hom_ext _ _ fun i ↦ (hdfacS i).trans (Sigma.ι_desc (fun j ↦ T.map (p j)) i).symm
  have : ∀ i, _root_.AlgebraicGeometry.IsIntegralHom (T.map (p i)) := hp
  have hdint : _root_.AlgebraicGeometry.IsIntegralHom (T.map d) := by
    rw [hd]
    exact isIntegralHom_sigmaDesc_of_finite _
  have _hdaff : _root_.AlgebraicGeometry.IsAffineHom (T.map d) := inferInstance
  have _hUaff : IsAffine (T.obj U) := hU
  have hWaff : IsAffine (T.obj W) :=
    AlgebraicGeometry.isAffine_of_isAffineHom (T.map d)
  -- the base change of the coproduct, by universality of finite coproducts of sheaves
  have hcolim := BigFppfOver.isColimit_yoneda_sigmaCofan B S hS V
  let as : ∀ i, J.yoneda.obj (V i) ⟶ Fs i := fun i ↦ ⟨a i⟩
  let fs : ∀ i, Fs i ⟶ Ys := fun i ↦ ⟨fᵢ i⟩
  have hsq : ∀ i, IsPullback (as i) (J.yoneda.map (p i)) (fs i)
      (⟨ξ⟩ : J.yoneda.obj U ⟶ Ys) := fun i ↦ isPullback_sheaf_of_hom (hpb i)
  have hwhole := (FinitaryPreExtensive.isUniversal_finiteCoproducts
    hG).isPullback_of_isColimit_right fs (⟨f⟩ : G ⟶ Ys) (⟨ξ⟩ : J.yoneda.obj U ⟶ Ys) as
    (fun i ↦ J.yoneda.map (p i)) hsq hcolim (fun i ↦ Sheaf.hom_ext (hf i))
  have hdesc : Cofan.IsColimit.desc hcolim (fun i ↦ J.yoneda.map (p i)) = J.yoneda.map d := by
    refine Cofan.IsColimit.hom_ext hcolim _ _ fun i ↦ ?_
    rw [Cofan.IsColimit.fac]
    simp only [Cofan.inj, Cofan.mk_ι_app]
    rw [← Functor.map_comp, hdfac]
  rw [hdesc] at hwhole
  exact ⟨W, d, (Cofan.IsColimit.desc hcolim fun i ↦ as i ≫ ι i).hom,
    hwhole.map (sheafToPresheaf J (Type u)), hWaff, hdint⟩

end AlgebraicGeometry.Space

end
