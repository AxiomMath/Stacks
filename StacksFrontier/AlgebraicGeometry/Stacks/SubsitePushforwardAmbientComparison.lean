module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardFormula
public import StacksFrontier.CategoryTheory.Sites.SectionsAlongAFunctorConnected

/-!
# Comparing the pushforward along a subsite functor with the ambient pushforward

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over a base, let `𝒳' ⊆ 𝒳` and `𝒴' ⊆ 𝒴` be full
subcategories with `f(𝒳') ⊆ 𝒴'`, and let `f' : 𝒳' ⥤ 𝒴'` be the restriction. For a presheaf of
sets `ℱ` on `𝒳` and an object `y` of `𝒴'` lying over `V`, three identifications meet at the
primed 2-fibre product `(V ×_{y, 𝒴} 𝒳)'`, the full subcategory of `V ×_{y, 𝒴} 𝒳` cut out by
membership of `𝒳'`:

* `f'_*(ℱ|_{𝒳'})(y) = Γ((V ×_{y, 𝒴} 𝒳)', (pr')^{-1}ℱ)`, the formula of **Stacks 07AU**;
* `f_*ℱ(y) = Γ(V ×_{y, 𝒴} 𝒳, pr^{-1}ℱ)`, the formula of **Stacks 06W6**;
* `Γ((V ×_{y, 𝒴} 𝒳)', (pr')^{-1}ℱ) = Γ(V ×_{y, 𝒴} 𝒳, pr^{-1}ℱ)`, the degree-zero clause of
  **Stacks 07AK** for the inclusion of the primed 2-fibre product.

Composing them gives the value at `y` of the pushforward along `f'` of the restriction of `ℱ`,
identified with the value at `y` of the pushforward along `f`. This is assertion (b) of
**Stacks 07AT**, one object of the subsite of `𝒴` at a time, for a sheaf of sets.

## Main definitions

* `CategoryTheory.SubsitePushforward.ambientProjection`: the projection
  `pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` of which `pr'` is the restriction.

## Main results

* `CategoryTheory.SubsitePushforward.primedSectionsAmbientEquiv`: the third identification, the
  comparison of global sections over the primed 2-fibre product with those over the whole
  2-fibre product.
* `CategoryTheory.SubsitePushforward.primedPushforwardAmbientEquiv`: the composite of the three.

## Implementation notes

The topology on `V ×_{y, 𝒴} 𝒳` for which `pr^{-1}ℱ` is a sheaf, and the two local-factorization
conditions of `Stacks.Sites.bijective_sectionsPrecomp_of_hasLocallyConnectedFactorizations` for
the inclusion of the primed subcategory, are hypotheses here. They are exactly the geometric
input the source leaves unverified, and each is a genuine condition on the site rather than a
weakening of the content: the first is the sheaf condition the statement is about, and the other
two are the content of the hypotheses (1) and (2) of **Stacks 07AK** at the primed subcategory.

Local connectedness is taken in the zigzag form of
`Stacks.Sites.HasLocallyConnectedFactorizations` rather than the dominating form of
`Stacks.Sites.HasConnectedLocalFactorizations`: the dominating form already fails for
`(Sch/A¹ × A¹)_{fppf}` with its full subcategory of the objects flat over the second
projection, while the zigzag form holds there; see
`StacksFrontier.CategoryTheory.Sites.SectionsAlongAFunctorConnected`.

The projection of the 2-fibre product restricts to `pr'` strictly:
`CategoryTheory.SubsitePushforward.ι_comp_ambientProjection` is a definitional equality, so the
restriction of `pr^{-1}ℱ` along the inclusion of the primed subcategory *is* `(pr')^{-1}` of the
restriction of `ℱ`, and the three identifications compose with no transport.

## References

* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AU](https://stacks.math.columbia.edu/tag/07AU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SubsitePushforward

attribute [local implicit_reducible] Functor.Fiber

universe u₁ u₂ u₃ v₁ v₂ v₃ w

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳)
  (c : p𝒴.ChoiceOfPullbacks) {Q : ObjectProperty 𝒴} (y : Q.FullSubcategory)

/-- **The projection `pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳`** of the 2-fibre product, the one of which
`CategoryTheory.SubsitePushforward.primedProjection` is the restriction. -/
def ambientProjection : ambientTwoFibreProduct p𝒳 p𝒴 f c y ⥤ 𝒳 :=
  TwoFibreProductOver.snd (Over.forget (p𝒴.obj y.obj)) p𝒳 p𝒴
    (c.sliceFunctor ⟨y.obj, rfl⟩) f

/-- The projection of the 2-fibre product restricts to `pr'` on the primed subcategory. -/
lemma ι_comp_ambientProjection :
    (primedProperty p𝒳 p𝒴 f P c y).ι ⋙ ambientProjection p𝒳 p𝒴 f c y =
      primedProjection p𝒳 p𝒴 f P c y ⋙ P.ι :=
  rfl

/-- Restricting `pr^{-1}ℱ` to the primed 2-fibre product is `(pr')^{-1}` of the restriction of
`ℱ` to the subsite of `𝒳`. -/
lemma primedProjection_op_comp (ℱ : 𝒳ᵒᵖ ⥤ Type w) :
    (primedProjection p𝒳 p𝒴 f P c y).op ⋙ (P.ι.op ⋙ ℱ) =
      (primedProperty p𝒳 p𝒴 f P c y).ι.op ⋙
        ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ) :=
  rfl

/-- **The degree-zero clause of Stacks 07AK at the primed 2-fibre product.** If `pr^{-1}ℱ` is a
sheaf for a topology on `V ×_{y, 𝒴} 𝒳` in which every object is covered by objects admitting a
morphism to the primed subcategory, and in which any two such morphisms are locally connected,
then the global sections of `(pr')^{-1}ℱ` over the primed 2-fibre product are the global
sections of `pr^{-1}ℱ` over the whole 2-fibre product. -/
def primedSectionsAmbientEquiv (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    (J : GrothendieckTopology (ambientTwoFibreProduct p𝒳 p𝒴 f c y))
    (hℱ : Presieve.IsSheaf J ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ))
    (hfac : Stacks.Sites.HasLocalFactorizations J (primedProperty p𝒳 p𝒴 f P c y).ι)
    (hconn : Stacks.Sites.HasLocallyConnectedFactorizations J
      (primedProperty p𝒳 p𝒴 f P c y).ι) :
    Presheaf.globalSections ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ (P.ι.op ⋙ ℱ)) ≃
      Presheaf.globalSections ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ) :=
  (Presheaf.globalSectionsEquivSections
      ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ (P.ι.op ⋙ ℱ))).trans
    ((Stacks.Sites.sectionsEquivOfHasLocallyConnectedFactorizations J hℱ hfac hconn).symm.trans
      (Presheaf.globalSectionsEquivSections
        ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ)).symm)

/-- **Assertion (b) of Stacks 07AT, at one object of the subsite of `𝒴` and for a presheaf of
sets, given the local-factorization conditions.** The value at `y` of the pushforward along the
restriction `f' : 𝒳' ⥤ 𝒴'` of the restriction of `ℱ` to `𝒳'` is the value at `y` of the
pushforward of `ℱ` along `f`.

The identification is the formula of **Stacks 07AU** at `f'`, followed by the comparison of
global sections over the primed 2-fibre product with those over the whole 2-fibre product,
followed by the formula of **Stacks 06W6** at `f`. -/
def primedPushforwardAmbientEquiv {Q : ObjectProperty 𝒴}
    (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj)) (h𝒴 : p𝒴.IsFiberedInGroupoids)
    (hf : f ⋙ p𝒴 = p𝒳) (y : Q.FullSubcategory) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    (J : GrothendieckTopology (ambientTwoFibreProduct p𝒳 p𝒴 f c y))
    (hℱ : Presieve.IsSheaf J ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ))
    (hfac : Stacks.Sites.HasLocalFactorizations J (primedProperty p𝒳 p𝒴 f P c y).ι)
    (hconn : Stacks.Sites.HasLocallyConnectedFactorizations J
      (primedProperty p𝒳 p𝒴 f P c y).ι)
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
      (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w, (P.ι ⋙ f).op.HasPointwiseRightKanExtension G]
    [∀ G : 𝒳ᵒᵖ ⥤ Type w, f.op.HasPointwiseRightKanExtension G] :
    ((subsiteFunctor f P hPQ).op.ran.obj (P.ι.op ⋙ ℱ)).obj (op y) ≃
      (f.op.ran.obj ℱ).obj (op y.obj) :=
  ((subsitePushforwardSectionsEquiv p𝒳 p𝒴 f P hPQ h𝒴 hf c y (P.ι.op ⋙ ℱ)).trans
      (primedSectionsAmbientEquiv p𝒳 p𝒴 f P c y ℱ J hℱ hfac hconn)).trans
    (Presheaf.pushforwardSectionsEquiv p𝒳 p𝒴 f h𝒴 hf c ⟨y.obj, rfl⟩ ℱ).symm

end CategoryTheory.SubsitePushforward

namespace AlgebraicGeometry.Stack

universe u w a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace FlatFppf

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

/-- The flat objects of the 2-fibre product `V ×_{y, 𝒴} 𝒳`, read as a property of its
objects. -/
abbrev primedObjectProperty (y : FlatFppf B S hS 𝒴) :
    ObjectProperty (SubsitePushforward.ambientTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor (ambientChoiceOfPullbacks B S hS 𝒴) y) :=
  SubsitePushforward.primedProperty 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (flatObject B S hS 𝒳.val) (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- The 2-fibre product `V ×_{y, 𝒴} 𝒳` of which
`AlgebraicGeometry.Stack.FlatFppf.primedTwoFibreProduct` is the full subcategory of the objects
whose `𝒳`-component is flat. -/
abbrev ambientTwoFibreProduct (y : FlatFppf B S hS 𝒴) :=
  SubsitePushforward.ambientTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- The projection `pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` of the 2-fibre product to the objects of `𝒳`. -/
abbrev ambientProjection (y : FlatFppf B S hS 𝒴) :
    ambientTwoFibreProduct B S hS f y ⥤ 𝒳.val.val.obj :=
  SubsitePushforward.ambientProjection 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- **Assertion (b) of Stacks 07AT for the flat-fppf site, at one flat object `y` of `𝒴` and for
a presheaf of sets, given the local-factorization conditions.** For a flat 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks and a presheaf `ℱ` on the fppf site of `𝒳`, the value at `y` of
the pushforward along the restriction `f'` of `f` to the flat-fppf sites of the restriction of
`ℱ` to the flat-fppf site of `𝒳` is the value at `y` of the pushforward of `ℱ` along `f`.

The hypotheses are a topology on the 2-fibre product `V ×_{y, 𝒴} 𝒳` for which `pr^{-1}ℱ` is a
sheaf, and the two local-factorization conditions for the inclusion of the flat objects of that
2-fibre product. -/
def primedPushforwardAmbientEquiv (y : FlatFppf B S hS 𝒴)
    (ℱ : (𝒳.val.val.obj)ᵒᵖ ⥤ Type a)
    (J : GrothendieckTopology (ambientTwoFibreProduct B S hS f y))
    (hℱ : Presieve.IsSheaf J ((ambientProjection B S hS f y).op ⋙ ℱ))
    (hfac : Stacks.Sites.HasLocalFactorizations J (primedObjectProperty B S hS f y).ι)
    (hconn : Stacks.Sites.HasLocallyConnectedFactorizations J (primedObjectProperty B S hS f y).ι)
    [∀ G : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (primedSiteFunctor B S hS f hf).op.HasPointwiseRightKanExtension G]
    [∀ G : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (inclusion B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension G]
    [∀ G : (𝒳.val.val.obj)ᵒᵖ ⥤ Type a,
      f.hom.hom.toFunctor.op.HasPointwiseRightKanExtension G] :
    (((primedSiteFunctor B S hS f hf).op.ran.obj
        ((inclusion B S hS 𝒳).op ⋙ ℱ)).obj (op y)) ≃
      ((f.hom.hom.toFunctor.op.ran.obj ℱ).obj (op y.obj)) :=
  SubsitePushforward.primedPushforwardAmbientEquiv 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (ambientChoiceOfPullbacks B S hS 𝒴)
    (flatObject_map B S hS f hf) 𝒴.val.isFiberedInGroupoids f.hom.hom.w y ℱ J hℱ hfac hconn

end FlatFppf

namespace LisseEtale

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- The smooth objects of the 2-fibre product `V ×_{y, 𝒴} 𝒳`, read as a property of its
objects. -/
abbrev primedObjectProperty (y : LisseEtale.{u, w} B S hS 𝒴) :
    ObjectProperty (SubsitePushforward.ambientTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor (ambientChoiceOfPullbacks B S hS 𝒴) y) :=
  SubsitePushforward.primedProperty 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (smoothObject.{u, w} B S hS 𝒳) (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- The 2-fibre product `V ×_{y, 𝒴} 𝒳` of which
`AlgebraicGeometry.Stack.LisseEtale.primedTwoFibreProduct` is the full subcategory of the objects
whose `𝒳`-component is smooth. -/
abbrev ambientTwoFibreProduct (y : LisseEtale.{u, w} B S hS 𝒴) :=
  SubsitePushforward.ambientTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- The projection `pr : V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` of the 2-fibre product to the objects of `𝒳`. -/
abbrev ambientProjection (y : LisseEtale.{u, w} B S hS 𝒴) :
    ambientTwoFibreProduct B S hS f y ⥤ 𝒳.val.val.obj :=
  SubsitePushforward.ambientProjection 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor
    (ambientChoiceOfPullbacks B S hS 𝒴) y

/-- **Assertion (b) of Stacks 07AT for the lisse-étale site, at one smooth object `y` of `𝒴` and
for a presheaf of sets, given the local-factorization conditions.** For a smooth 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks and a presheaf `ℱ` on the étale site of `𝒳`, the value at `y` of
the pushforward along the restriction `f'` of `f` to the lisse-étale sites of the restriction of
`ℱ` to the lisse-étale site of `𝒳` is the value at `y` of the pushforward of `ℱ` along `f`.

The hypotheses are a topology on the 2-fibre product `V ×_{y, 𝒴} 𝒳` for which `pr^{-1}ℱ` is a
sheaf, and the two local-factorization conditions for the inclusion of the smooth objects of
that 2-fibre product. -/
def primedPushforwardAmbientEquiv (y : LisseEtale.{u, w} B S hS 𝒴)
    (ℱ : (𝒳.val.val.obj)ᵒᵖ ⥤ Type a)
    (J : GrothendieckTopology (ambientTwoFibreProduct B S hS f y))
    (hℱ : Presieve.IsSheaf J ((ambientProjection B S hS f y).op ⋙ ℱ))
    (hfac : Stacks.Sites.HasLocalFactorizations J (primedObjectProperty B S hS f y).ι)
    (hconn : Stacks.Sites.HasLocallyConnectedFactorizations J (primedObjectProperty B S hS f y).ι)
    [∀ G : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (primedSiteFunctor.{u, w} B S hS f hf).op.HasPointwiseRightKanExtension G]
    [∀ G : (LisseEtale.{u, w} B S hS 𝒳)ᵒᵖ ⥤ Type a,
      (inclusion.{u, w} B S hS 𝒳 ⋙ f.hom.hom.toFunctor).op.HasPointwiseRightKanExtension G]
    [∀ G : (𝒳.val.val.obj)ᵒᵖ ⥤ Type a,
      f.hom.hom.toFunctor.op.HasPointwiseRightKanExtension G] :
    (((primedSiteFunctor.{u, w} B S hS f hf).op.ran.obj
        ((inclusion.{u, w} B S hS 𝒳).op ⋙ ℱ)).obj (op y)) ≃
      ((f.hom.hom.toFunctor.op.ran.obj ℱ).obj (op y.obj)) :=
  SubsitePushforward.primedPushforwardAmbientEquiv 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳) (ambientChoiceOfPullbacks B S hS 𝒴)
    (smoothObject_map.{u, w} B S hS f hf) 𝒴.val.isFiberedInGroupoids f.hom.hom.w y ℱ J hℱ hfac
    hconn

end LisseEtale

end AlgebraicGeometry.Stack

end
