module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory

/-!
# Two 1-morphisms to an algebraic space agreeing on the charts of an atlas

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, let `q : 𝒳 ⟶ F` be a
1-morphism to the category attached to a presheaf `F` with a surjective étale atlas
`b : yoneda.obj U ⟶ F`, and fix a covering family `π i : V i ⟶ U` of the atlas. Two 1-morphisms
`f, g : 𝒳 ⟶ W` to the category attached to a sheaf `W` are equal as soon as they agree at every
object of `𝒳` whose image under `q` is carried by one of the charts `yoneda.map (π i) ≫ b`.

This is the extensionality statement a descent along charts needs: it reduces an identity of
1-morphisms out of `𝒳` to a pointwise identity which is only required at objects visible in a
chart, and it is where the atlas hypothesis on `F` is spent.

## Main results

* `AlgebraicGeometry.Stack.hom_ext_of_atlas_charts`: the extensionality statement above.

## Implementation notes

A 1-morphism into the category attached to a presheaf is determined by the family of elements it
names (`AlgebraicGeometry.Stack.hom_ext_of_section`), so the claim is pointwise at each object
`x` of `𝒳`. The element named by `q` at `x` is a section `s : yoneda.obj T ⟶ F` over
`T = p x`; pulling the atlas back along it gives a surjective étale atlas `yoneda.map p` of
`yoneda.obj T`, and pulling the covering family back along `p` gives a covering of its source. So
the two elements named by `f` and `g` at `x`, read as morphisms out of `yoneda.obj T`, may be
compared locally — by `AlgebraicGeometry.Space.hom_ext_of_etale_atlas` and then
`AlgebraicGeometry.Space.hom_ext_of_cover` — and locally each comparison is an instance of the
hypothesis, applied to a lift of the chart morphism to `𝒳`, which exists because `𝒳` is fibred in
groupoids.

The hypothesis is stated with the element named by `q` rather than with a morphism of `𝒳`,
because that is what the local comparison produces: the chart morphism factors the section, and
the factoring morphism of the site is the datum the hypothesis receives.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Two 1-morphisms to the category attached to a sheaf agreeing on the charts of a surjective
étale atlas of the target of a third one are equal.** -/
theorem hom_ext_of_atlas_charts
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
    (q : 𝒳 ⟶ fibredCategory B S hS F)
    (f g : 𝒳 ⟶ fibredCategory B S hS W)
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ F)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    {I : Type u} (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ U)
    (hcover : Sieve.generate (Presieve.ofArrows V π) ∈ BigFppfOver.topology B S hS U)
    (hlocal : ∀ (i : I) (x : 𝒳.val.obj) (t : 𝒳.val.p.obj x ⟶ V i),
      sectionOfBasedFunctor q.hom.toFunctor q.hom.w x = (yoneda.map (π i) ≫ b).app _ t →
      sectionOfBasedFunctor f.hom.toFunctor f.hom.w x =
        sectionOfBasedFunctor g.hom.toFunctor g.hom.w x) : f = g := by
  classical
  refine hom_ext_of_section B S hS f g fun x => ?_
  set T := 𝒳.val.p.obj x
  set s : yoneda.obj T ⟶ F := yonedaEquiv.symm (sectionOfBasedFunctor q.hom.toFunctor q.hom.w x)
  set hp := MorphismProperty.relative.rep hb
  set r : hp.pullback s ⟶ U := yoneda.preimage (hp.fst s) with hrdef
  set p : hp.pullback s ⟶ T := hp.snd s
  have hs : IsPullback (yoneda.map r) (yoneda.map p) b s := by
    rw [hrdef, yoneda.map_preimage]
    exact hp.isPullback s
  refine yonedaEquiv.symm.injective ?_
  refine Space.hom_ext_of_etale_atlas B S hS (isAlgebraicSpace_yoneda B S hS T).isSheaf hW
    (yoneda.map p) 
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hs hsurj)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hs hb) ?_
  have hc : Sieve.generate (Presieve.ofArrows (fun i => pullback r (π i))
      fun i => pullback.fst r (π i)) ∈ BigFppfOver.topology B S hS (hp.pullback s) := by
    change Sieve.ofArrows _ _ ∈ _
    rw [Sieve.ofArrows_eq_pullback_of_isPullback π fun i => IsPullback.of_hasPullback r (π i)]
    exact (BigFppfOver.topology B S hS).pullback_stable r hcover
  refine Space.hom_ext_of_cover B S hS hW _ _ _ hc fun i => ?_
  obtain ⟨y, m, hm⟩ := 𝒳.2.exists_lift (pullback.fst r (π i) ≫ p) x rfl
  have hd := IsHomLift.domain_eq 𝒳.val.p (pullback.fst r (π i) ≫ p) m
  have hmap : 𝒳.val.p.map m = eqToHom hd ≫ (pullback.fst r (π i) ≫ p) := by
    simpa using IsHomLift.fac' 𝒳.val.p (pullback.fst r (π i) ≫ p) m
  have he : yoneda.map (pullback.fst r (π i) ≫ p) ≫ s =
      yoneda.map (pullback.snd r (π i)) ≫ yoneda.map (π i) ≫ b := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← hs.w]
    simp only [← Category.assoc, ← Functor.map_comp, pullback.condition]
  have hy : sectionOfBasedFunctor q.hom.toFunctor q.hom.w y =
      (yoneda.map (π i) ≫ b).app _ (eqToHom hd ≫ pullback.snd r (π i)) := by
    rw [← sectionOfBasedFunctor_map q.hom.toFunctor q.hom.w m, hmap]
    have he' := congrArg
      (fun k => k.app (Opposite.op (𝒳.val.p.obj y)) (eqToHom hd)) he
    change s.app _ (eqToHom hd ≫ (pullback.fst r (π i) ≫ p)) =
      b.app _ ((eqToHom hd ≫ pullback.snd r (π i)) ≫ π i) at he'
    change F.map (eqToHom hd ≫ (pullback.fst r (π i) ≫ p)).op
      (sectionOfBasedFunctor q.hom.toFunctor q.hom.w x) =
      b.app _ ((eqToHom hd ≫ pullback.snd r (π i)) ≫ π i)
    exact he'
  have hv := hlocal i y (eqToHom hd ≫ pullback.snd r (π i)) hy
  rw [← sectionOfBasedFunctor_map f.hom.toFunctor f.hom.w m,
    ← sectionOfBasedFunctor_map g.hom.toFunctor g.hom.w m, hmap] at hv
  have hv' := congrArg (fun z => W.map (eqToHom hd.symm).op z) hv
  have hw : W.map (pullback.fst r (π i) ≫ p).op
      (sectionOfBasedFunctor f.hom.toFunctor f.hom.w x) =
      W.map (pullback.fst r (π i) ≫ p).op
        (sectionOfBasedFunctor g.hom.toFunctor g.hom.w x) := by
    simpa only [← types_comp_apply, ← Functor.map_comp, ← op_comp, Category.assoc,
      eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
      Category.comp_id] using hv'
  have hnat : ∀ k : 𝒳 ⟶ fibredCategory B S hS W,
      yoneda.map (pullback.fst r (π i) ≫ p) ≫
        yonedaEquiv.symm (sectionOfBasedFunctor k.hom.toFunctor k.hom.w x) =
      yonedaEquiv.symm (W.map (pullback.fst r (π i) ≫ p).op
        (sectionOfBasedFunctor k.hom.toFunctor k.hom.w x)) := fun k =>
    yonedaEquiv_symm_naturality_left _ W _
  convert ((hnat f).trans (congrArg yonedaEquiv.symm hw)).trans (hnat g).symm using 1 <;>
    simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Stack

end
