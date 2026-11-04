module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSitePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverFromAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence

/-!
# Affine morphisms after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'` and let `f : Y ⟶ X` be a morphism of
algebraic spaces over `S` defined using `B`. If `f` is affine, so is the morphism `f' : Y' ⟶ X'`
that Stacks 03FP attaches to it, so enlarging the big fppf site is a functor on algebraic spaces
affine over `X`.

The key point is that every *affine* étale chart of `X'` has a scheme belonging to the smaller
site `B`: it is quasi-compact and covered, through a surjective étale morphism, by its base
change to a transported atlas of `X`, which is étale over an object of `B`
(`AlgebraicGeometry.Space.size_le_of_compact_of_fppf_factorsThrough`). Over such a chart the base
change of `f'` is the transport of a base change of `f`
(`AlgebraicGeometry.Space.isPullback_changeBigSiteChart`), which is affine because `f` is.

## Main results

* `AlgebraicGeometry.Space.size_lt_cutoff_of_isAffineChart_changeBigSite`: the scheme of an
  affine étale chart of `X'` belongs to `B`.
* `AlgebraicGeometry.Space.isAffineHom_changeBigSite_map`: enlarging the site preserves affine
  morphisms.
* `AlgebraicGeometry.Space.changeBigSiteAffineOver`: the resulting functor on algebraic spaces
  affine over `X`.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The scheme of an affine étale chart of `X'` belongs to the smaller site.** -/
theorem size_lt_cutoff_of_isAffineChart_changeBigSite
    (V : SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)
    (hV : IsAffine ((BigFppfOver.toScheme B' S (largerContains h hS)).obj V.obj.left)) :
    ((BigFppfOver.toScheme B' S (largerContains h hS)).obj V.obj.left).size < B.cutoff := by
  let G := changeBigSiteSmallEtale B B' h S hS X
  let hS' : B'.Contains S := largerContains h hS
  let K' := BigFppfOver.toScheme B' S hS'
  obtain ⟨U₀, q, hqs, hqe⟩ := X.property.exists_atlas
  let A : SmallEtale B S hS X.obj := ⟨CostructuredArrow.mk q, hqe⟩
  let ψ := (G.obj A).obj.hom
  have hψe : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) K') ψ := (G.obj A).property
  have hψs : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) K') ψ :=
    presheaf_surjective_changeBigSiteChart B B' h S hS X (U := CostructuredArrow.mk q) hqs hqe
  let P := hψe.rep.pullback V.obj.hom
  let p₁ : P ⟶ (G.obj A).obj.left := hψe.rep.fst' V.obj.hom
  let p₂ : P ⟶ V.obj.left := hψe.rep.snd V.obj.hom
  have hpb : IsPullback (yoneda.map p₁) (yoneda.map p₂) ψ V.obj.hom :=
    hψe.rep.isPullback' V.obj.hom
  have hp₂e : Etale (K'.map p₂) := hψe.property V.obj.hom (yoneda.map p₁) p₂ hpb
  have hp₂s : Surjective (K'.map p₂) := hψs.property V.obj.hom (yoneda.map p₁) p₂ hpb
  have hp₁e : Etale (K'.map p₁) := V.property.property ψ (yoneda.map p₂) p₁ hpb.flip
  have := hp₁e
  have := hp₂e
  have : CompactSpace (K'.obj V.obj.left) := inferInstance
  let E : FppfCovering.{u} (K'.obj V.obj.left) :=
    { ι := PUnit
      X _ := K'.obj P
      f _ := K'.map p₂
      flat _ := inferInstance
      lfp _ := inferInstance
      jointly_surjective t := by
        obtain ⟨x, hx⟩ := hp₂s.surj t
        exact ⟨PUnit.unit, x, hx⟩ }
  exact (size_le_of_compact_of_fppf_factorsThrough (K'.map p₁) (K'.map p₂) E
    (fun _ => 𝟙 _) (fun _ => Category.id_comp _)).trans_lt U₀.left.property

/-- **Enlarging the big fppf site preserves affine morphisms.** An affine étale chart of `X'`
belongs to the smaller site, so it is the transport of a point of `X` with values in an affine
object of `B`; the base change of `f` along that point is affine because `f` is, and its transport
is the base change of `f'` along the chart. -/
theorem isAffineHom_changeBigSite_map {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsAffineHom B S hS f.hom) :
    IsAffineHom B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom := by
  refine isAffineHom_of_affineChart B' S (largerContains h hS)
    ((changeBigSite B B' h S hS).obj Y).property _ fun V hV => ?_
  have hsmall := size_lt_cutoff_of_isAffineChart_changeBigSite B B' h S hS X V hV
  let T : BigFppfOver B S hS :=
    BigFppfOver.mk B S hS hsmall (B'.inclusion.map V.obj.left.hom)
  let x : X.obj.obj (op T) := (changeBigSiteSectionEquiv B B' h S hS X T).symm
    (yonedaEquiv V.obj.hom)
  let g : yoneda.obj T ⟶ X.obj := yonedaEquiv.symm x
  obtain ⟨W, p, q, hpb⟩ := hf ⟨T, hV⟩ g
  have hg : (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk g)).hom = V.obj.hom := by
    apply yonedaEquiv.injective
    refine (chartElement_changeBigSiteChart B B' h S hS X (CostructuredArrow.mk g)).trans ?_
    show changeBigSiteSectionEquiv B B' h S hS X T (yonedaEquiv (yonedaEquiv.symm x)) = _
    rw [Equiv.apply_symm_apply]
    exact Equiv.apply_symm_apply _ _
  refine ⟨⟨(inclusionOver h S hS).obj W.obj, W.property⟩,
    (changeBigSiteChart B B' h S hS Y (CostructuredArrow.mk p)).hom,
    (inclusionOver h S hS).map q, ?_⟩
  rw [← hg]
  exact isPullback_changeBigSiteChart B B' h S hS f p q g hpb

end AlgebraicGeometry.Space

end
