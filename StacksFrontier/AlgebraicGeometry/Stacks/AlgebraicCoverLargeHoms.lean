module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentationBootstrap
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyMono
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationAlgebraicStack

/-!
# Algebraicity along a smooth surjective cover, for stacks with large morphism types

Let `q : 𝒲 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`. If `𝒲` is an algebraic stack, `𝒴` is a stack whose diagonal is representable by
algebraic spaces, and `q` is representable by algebraic spaces, surjective and smooth, then `𝒴` is
an algebraic stack: a surjective smooth scheme atlas of `𝒲` followed by `q` is one of `𝒴`, by
Stacks 0301 and Stacks 045B. This is the step "hence it suffices to prove the result for `𝒳'`" of
the proof of Stacks 0DLN, where `q` is surjective and étale, so smooth by Stacks 04XX and
Stacks 045F.

`AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothSurjectiveAlgebraicCover` states this when the
total categories have the universes of the site. The categories this file is for, such as
`Complexes_{X/B}` of Stacks 0DLE, have morphisms in the universe of the objects of the site, so the
statement here allows the total categories of `𝒲` and `𝒴` any universes dominating those of the
site.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_smoothSurjectiveCoverLargeHoms`: the statement for
  `q` surjective and smooth.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_etaleSurjectiveCoverLargeHoms`: the same for `q`
  surjective and étale.

## Implementation notes

The scheme atlas `a : (Sch/U)_fppf ⟶ 𝒲` lives in the universes of the site, and Stacks 045B
(`AlgebraicGeometry.Stack.hasRelativeProperty_comp`) composes 1-morphisms of one 2-category. The
proof therefore lifts `(Sch/U)_fppf` to the universes of `𝒲` along the universe-lifting
equivalence `CategoryTheory.ULiftHomULiftCategory.equiv`, as the proof of Stacks 0300 does,
composes there, and carries the relative properties back with Stacks 0457 and 0459
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences` and
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`). The two composites of that
equivalence are identity functors on the nose, so every 2-commutativity datum is an identity.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045F](https://stacks.math.columbia.edu/tag/045F)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Algebraicity along a smooth surjective cover, in large universes.** Let `q : 𝒲 ⟶ 𝒴` be a
1-morphism of categories fibred in groupoids over the big fppf site of `S`, whose total
categories have universes dominating those of the site. If `𝒲` is an algebraic stack, `𝒴` is a
stack for the fppf topology with diagonal representable by algebraic spaces, and `q` is
representable by algebraic spaces, surjective and smooth, then `𝒴` is an algebraic stack. -/
theorem isAlgebraicStack_of_smoothSurjectiveCoverLargeHoms
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) w} (BigFppfOver B S hS)}
    (q : 𝒲 ⟶ 𝒴)
    (h𝒲 : IsAlgebraicStack.{u, t} B S hS 𝒲.val)
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiagonal : HasRepresentableDiagonal B S hS 𝒴)
    (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom)
    (hsurj : HasRelativeProperty.{u, max u v, max (u + 1) w, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) q hq)
    (hsmooth : HasRelativeProperty.{u, max u v, max (u + 1) w, u} B S hS
      (Space.smoothMorphismProperty B S hS) q hq) :
    IsAlgebraicStack.{u, t} B S hS 𝒴.val := by
  obtain ⟨_h𝒲fib, -, -, U, a, ha, hAtlas⟩ := h𝒲
  let 𝒵 := schemeFibredCategory B S hS U
  -- the category represented by `U`, lifted to the universes of `𝒲`
  let _i₁ : Category.{u} (ULift.{max (u + 1) w} 𝒵.val.obj) := uliftCategory _
  let _i₂ : Category.{max u v} (ULiftHom.{max u v} (ULift.{max (u + 1) w} 𝒵.val.obj)) :=
    ULiftHom.category
  let e : 𝒵.val.obj ≌ ULiftHom.{max u v} (ULift.{max (u + 1) w} 𝒵.val.obj) :=
    ULiftHomULiftCategory.equiv _
  have hfunctor : e.functor ⋙ (e.inverse ⋙ 𝒵.val.p) = 𝒵.val.p := rfl
  let 𝒵base : BasedCategory.{max u v, max (u + 1) w} (BigFppfOver B S hS) :=
    BasedCategory.ofFunctor (e.inverse ⋙ 𝒵.val.p)
  have h𝒵fib : 𝒵base.p.IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.of_isEquivalenceOver hfunctor
      { inv := e.inverse
        inv_over := rfl
        unitIso := Iso.refl _
        counitIso := Iso.refl _
        unit_vertical := fun _ => by
          simp only [Iso.refl_hom, NatTrans.id_app]; exact IsHomLift.id rfl
        counit_vertical := fun _ => by
          simp only [Iso.refl_hom, NatTrans.id_app]; exact IsHomLift.id rfl } 𝒵.2
  let 𝒵' : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) w} (BigFppfOver B S hS) :=
    ⟨𝒵base, h𝒵fib⟩
  let up : 𝒵.val ⥤ᵇ 𝒵'.val := { toFunctor := e.functor, w := hfunctor }
  let down : 𝒵'.val ⥤ᵇ 𝒵.val := { toFunctor := e.inverse, w := rfl }
  have hup : up.toFunctor.IsEquivalence := inferInstanceAs e.functor.IsEquivalence
  have hdown : down.toFunctor.IsEquivalence := inferInstanceAs e.inverse.IsEquivalence
  have hid𝒲 : (BasedFunctor.id 𝒲.val).toFunctor.IsEquivalence :=
    inferInstanceAs (𝟭 𝒲.val.obj).IsEquivalence
  have hid𝒴 : (BasedFunctor.id 𝒴.val).toFunctor.IsEquivalence :=
    inferInstanceAs (𝟭 𝒴.val.obj).IsEquivalence
  -- the lifted atlas of `𝒲`
  let a' : 𝒵' ⟶ 𝒲 := Bicategory.InducedBicategory.mkHom (BasedFunctor.comp down a)
  have ha' : IsRepresentableByAlgebraicSpaces B S hS a'.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (f' := a'.hom) (f := a)
      (a := down) (b := BasedFunctor.id _) (Iso.refl _)).mp ha
  have lift := fun P => relativeProperty_of_equivalences B S hS P
    (𝒳' := 𝒵') (𝒴' := 𝒲) (𝒳 := 𝒵) (𝒴 := 𝒲) a'.hom a down (BasedFunctor.id _) (Iso.refl _)
  have ha'surj : HasRelativeProperty.{u, max u v, max (u + 1) w, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) a' ha' :=
    lift _ fun V y hy F hF hh => (hAtlas V y hy F hF hh).1
  have ha'smooth : HasRelativeProperty.{u, max u v, max (u + 1) w, u} B S hS
      (Space.smoothMorphismProperty B S hS) a' ha' :=
    lift _ fun V y hy F hF hh => (hAtlas V y hy F hF hh).2
  -- the composite with `q`, in the universes of `𝒲`
  have hc : IsRepresentableByAlgebraicSpaces B S hS (a' ≫ q).hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS a' q ha' hq
  have hcsurj := hasRelativeProperty_comp.{u, max u v, max (u + 1) w, u} B S hS
    (Space.surjectiveMorphismProperty B S hS) a' q ha' hq ha'surj hsurj
  have hcsmooth := hasRelativeProperty_comp.{u, max u v, max (u + 1) w, u} B S hS
    (Space.smoothMorphismProperty B S hS) a' q ha' hq ha'smooth hsmooth
  -- back to the category represented by `U`
  let atlas : 𝒵.val ⥤ᵇ 𝒴.val := BasedFunctor.comp a q.hom
  have hatlas : IsRepresentableByAlgebraicSpaces B S hS atlas :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (f' := atlas) (f := (a' ≫ q).hom)
      (a := up) (b := BasedFunctor.id _) (Iso.refl _)).mp hc
  have lift' := fun P => relativeProperty_of_equivalences B S hS P
    (𝒳' := 𝒵) (𝒴' := 𝒴) (𝒳 := 𝒵') (𝒴 := 𝒴) atlas (a' ≫ q).hom up (BasedFunctor.id _)
    (Iso.refl _)
  exact ⟨𝒴.2, ⟨hstack, hstack.isStackInGroupoids 𝒴.2⟩, hdiagonal, U, atlas, hatlas,
    fun V y hy F hF hh => ⟨lift' _ hcsurj V y hy F hF hh, lift' _ hcsmooth V y hy F hF hh⟩⟩

/-- **Algebraicity along an étale surjective cover, in large universes.** Let `q : 𝒲 ⟶ 𝒴` be a
1-morphism of categories fibred in groupoids over the big fppf site of `S`, whose total
categories have universes dominating those of the site. If `𝒲` is an algebraic stack, `𝒴` is a
stack for the fppf topology with diagonal representable by algebraic spaces, and `q` is
representable by algebraic spaces, surjective and étale, then `𝒴` is an algebraic stack.

Étale morphisms of algebraic spaces are smooth (Stacks 04XX), so `q` is smooth by Stacks 045F. -/
theorem isAlgebraicStack_of_etaleSurjectiveCoverLargeHoms
    {𝒲 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) w} (BigFppfOver B S hS)}
    (q : 𝒲 ⟶ 𝒴)
    (h𝒲 : IsAlgebraicStack.{u, t} B S hS 𝒲.val)
    (hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiagonal : HasRepresentableDiagonal B S hS 𝒴)
    (hq : IsRepresentableByAlgebraicSpaces B S hS q.hom)
    (hsurj : HasRelativeProperty.{u, max u v, max (u + 1) w, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) q hq)
    (hetale : HasRelativeProperty.{u, max u v, max (u + 1) w, u} B S hS
      (Space.etaleMorphisms B S hS) q hq) :
    IsAlgebraicStack.{u, t} B S hS 𝒴.val :=
  isAlgebraicStack_of_smoothSurjectiveCoverLargeHoms B S hS q h𝒲 hstack hdiagonal hq hsurj
    (hasRelativeProperty_mono.{u, max u v, max (u + 1) w} B S hS
      (fun _ Y _ hf => Space.isSmooth_of_isEtale B S hS Y.property hf) hq hetale)

end AlgebraicGeometry.Stack

end
