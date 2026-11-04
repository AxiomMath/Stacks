module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcompProductFunctor

/-!
# The two parallel arrows of Stacks 03M8 as morphisms of functors and of sections

Let `τ : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `ρ : R ⟶ X` be a second étale morphism and let `θ : R ⟶ U` satisfy
`θ ≫ τ = ρ`.  `AlgebraicGeometry.Space.postcompBaseChangeOverMap` is the morphism

`(V ×_X R) read over X ⟶ (V ×_X U) read over X`

induced by `θ`, one object `V` of the spaces-étale site of `X` at a time, and
`AlgebraicGeometry.Space.postcompBaseChangeOverMap_prodIsoApp` identifies it, under the product
comparison, with `prod.map θ (𝟙 V)`.  This file makes that family a morphism of *functors* and
carries it to the two readings the proof of Stacks 03M8 uses: the composite setting
`a = τ ≫ f`, `b = ρ ≫ f` for a second morphism `f : X ⟶ Y`, and the induced morphism of
presheaves of sections, whose target form is the one the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage` takes as a parallel arrow.

With `R = U ×_X U` and `θ` one of its two projections `t, s : R ⟶ U` this is the arrow
`V ×_Y U ⟶ V ×_Y R` of the asserted sequence of Stacks 03M8, read on sections; the two
projections give the two parallel arrows whose difference is the source's `t^* - s^*`.

## Main definitions

* `AlgebraicGeometry.Space.postcompBaseChangeOverMapNat` is the family
  `AlgebraicGeometry.Space.postcompBaseChangeOverMap` as a morphism of functors
  `(V ↦ V ×_X R) ⟶ (V ↦ V ×_X U)` on the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat` is the same morphism for the
  composite setting `a = τ ≫ f`, `b = ρ ≫ f`, as a morphism of functors from the spaces-étale
  site of `Y`.

## Main results

* `AlgebraicGeometry.Space.postcompBaseChangeOverMap_naturality` is the naturality itself: the
  induced morphisms commute with base change of a morphism of the site.  Both projections of the
  target product see the same composite, which is what pins it down.
* `AlgebraicGeometry.Space.postcompBaseChangeOverMapNat_prodIso` and
  `AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat_prodIso`: under the product
  comparison the morphism is `CategoryTheory.Limits.prod.functor.map θ`, that is
  `prod.map θ (𝟙 V)` at every object — the arrow the fork of
  `AlgebraicGeometry.Space.isLimitForkProdOfEtalePresentation` carries.
* `AlgebraicGeometry.Space.postcompBaseChangeCompSectionsIso_naturality` is the same statement
  on presheaves of sections with arbitrary coefficients, in the form a transport consumes: the
  morphism of sections induced by the comparison of base changes corresponds, under
  `AlgebraicGeometry.Space.postcompBaseChangeCompSectionsIso`, to restriction along
  `prod.map θ (𝟙)`.
* `AlgebraicGeometry.Space.postcompBaseChangeChartSectionsIso_naturality` is that statement
  restricted along the comparison functor of Stacks 03G1 for `Y`, where its right-hand side is
  **literally the parallel arrow of the fork** of
  `AlgebraicGeometry.Space.isLimitForkDirectImage`.

## Implementation notes

The naturality square is checked on the two projections of the target, by
`AlgebraicGeometry.Space.isPullbackOverEtale_hom_ext`, and not through any product API: the
target is the postcomposed base change itself, whose universal property is the universal
property of the cartesian square of the base-change datum.  So this file, like
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtalePostcompProduct.lean`, needs no
`CategoryTheory.Limits.HasBinaryProducts` instance for the two statements about
`AlgebraicGeometry.Space.postcompBaseChangeOverMapNat` itself; the product only enters where the
comparison does.

The composite morphism is assembled from the morphism over `X` by whiskering with base change
along `f` and conjugating by two instances of
`AlgebraicGeometry.Space.spacesBaseChange_comp` — the same two instances
`AlgebraicGeometry.Space.postcompBaseChangeCompProdIso` is assembled from, which is why the
compatibility of the two with the comparison reduces to the compatibility over `X` after one
cancellation `(spacesBaseChange_comp τ f).hom ≫ (spacesBaseChange_comp τ f).inv = 𝟙`.  It is
*not* defined as the conjugate of `prod.functor.map θ` by the comparison, which would make the
compatibility vacuous.

The naturality obligations are discharged with `CategoryTheory.NatTrans.ext` applied to a
`funext`, not with `ext`: the coefficients below are sheaves of sets and `ext` descends past the
components into elements, where the goal is no longer the equality of natural transformations
being proved.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    {ρ : R ⟶ X} (hρ : IsEtale B S hS ρ.hom) (θ : R ⟶ U) (hθ : θ ≫ τ = ρ)

/-! ### The comparison of two postcomposed base changes is natural -/

section

variable (bcρ : SpacesBaseChange B S hS ρ) (bcτ : SpacesBaseChange B S hS τ)

/-- **The comparison of two postcomposed base changes is natural in the object of the site.**
For a morphism `k : V ⟶ V'` of the spaces-étale site of `X`, base changing `k` along `ρ` and
then mapping to the base change along `τ` is mapping to the base change along `τ` and then base
changing `k` along `τ`.

Both sides are morphisms into the postcomposed base change of `V'` along `τ`, which is a
cartesian square over `τ`, so they agree as soon as their composites with the two projections
do; and those composites are the naturality of the two projections,
`AlgebraicGeometry.Space.postcompBaseChange_map_fst` and
`AlgebraicGeometry.Space.postcompBaseChange_map_snd`, against the two components
`AlgebraicGeometry.Space.postcompBaseChangeOverMap_fst` and
`AlgebraicGeometry.Space.postcompBaseChangeOverMap_snd` of the comparison. -/
theorem postcompBaseChangeOverMap_naturality {V V' : SpacesEtale B S hS X} (k : V ⟶ V') :
    (spacesEtalePostcomp B S hS ρ hρ).map (bcρ.functor.map k) ≫
        postcompBaseChangeOverMap B S hS τ hτ hρ θ hθ bcρ bcτ V' =
      postcompBaseChangeOverMap B S hS τ hτ hρ θ hθ bcρ bcτ V ≫
        (spacesEtalePostcomp B S hS τ hτ).map (bcτ.functor.map k) := by
  refine isPullbackOverEtale_hom_ext B S hS τ hτ
    (postcompBaseChangeFst B S hS τ hτ bcτ V') (postcompBaseChangeSnd B S hS τ hτ bcτ V')
    (isPullback_postcompBaseChange B S hS τ hτ bcτ V') ?_ ?_
  · rw [Category.assoc, postcompBaseChangeOverMap_fst, ← Category.assoc,
      postcompBaseChange_map_fst, Category.assoc, postcompBaseChange_map_fst,
      postcompBaseChangeOverMap_fst]
  · rw [Category.assoc, postcompBaseChangeOverMap_snd, postcompBaseChange_map_snd,
      Category.assoc, postcompBaseChange_map_snd, ← Category.assoc,
      postcompBaseChangeOverMap_snd]

/-- **The arrow `V ×_X R ⟶ V ×_X U` of Stacks 03M8 as a morphism of functors.**  The family
`AlgebraicGeometry.Space.postcompBaseChangeOverMap`, which for each object `V` of the
spaces-étale site of `X` maps the base change of `V` along `ρ` read over `X` to the base change
of `V` along `τ` read over `X`, is a morphism of the two composite functors.

Its naturality is `AlgebraicGeometry.Space.postcompBaseChangeOverMap_naturality`. -/
noncomputable def postcompBaseChangeOverMapNat :
    bcρ.functor ⋙ spacesEtalePostcomp B S hS ρ hρ ⟶
      bcτ.functor ⋙ spacesEtalePostcomp B S hS τ hτ where
  app V := postcompBaseChangeOverMap B S hS τ hτ hρ θ hθ bcρ bcτ V
  naturality _ _ k := postcompBaseChangeOverMap_naturality B S hS τ hτ hρ θ hθ bcρ bcτ k

/-- **The morphism of functors is `prod.functor.map θ`.**  Under the product comparison
`AlgebraicGeometry.Space.postcompBaseChangeProdIso` the morphism
`AlgebraicGeometry.Space.postcompBaseChangeOverMapNat` is the morphism of binary-product
functors induced by `θ`, read as a morphism `R ⟶ U` of the spaces-étale site of `X`.

This is `AlgebraicGeometry.Space.postcompBaseChangeOverMap_prodIsoApp` at every object; the
component of `CategoryTheory.Limits.prod.functor.map θ` at `V` is `prod.map θ (𝟙 V)` by
`Eq.refl`. -/
theorem postcompBaseChangeOverMapNat_prodIso :
    postcompBaseChangeOverMapNat B S hS τ hτ hρ θ hθ bcρ bcτ ≫
        (postcompBaseChangeProdIso B S hS τ hτ bcτ).hom =
      (postcompBaseChangeProdIso B S hS ρ hρ bcρ).hom ≫
        prod.functor.map (etaleOverMap B S hS τ hτ hρ θ hθ) := by
  refine NatTrans.ext (funext fun V ↦ ?_)
  exact postcompBaseChangeOverMap_prodIsoApp B S hS τ hτ bcτ hρ θ hθ bcρ V

end

/-! ### The composite setting `a = τ ≫ f`, `b = ρ ≫ f` -/

variable (f : X ⟶ Y)

/-- **The arrow `V ×_Y R ⟶ V ×_Y U` of Stacks 03M8 as a morphism of functors.**  For a second
morphism `f : X ⟶ Y` and `a = τ ≫ f`, `b = ρ ≫ f`, the base change along `b` of an object `V`
of the spaces-étale site of `Y`, read over `X`, maps to the base change along `a` of `V` read
over `X`, naturally in `V`.

It is `AlgebraicGeometry.Space.postcompBaseChangeOverMapNat` whiskered with base change along
`f` and conjugated by the two composition isomorphisms
`AlgebraicGeometry.Space.spacesBaseChange_comp` of `ρ` and of `τ` with `f` — the same two that
`AlgebraicGeometry.Space.postcompBaseChangeCompProdIso` is assembled from. -/
noncomputable def postcompBaseChangeCompOverMapNat :
    (spacesBaseChange B S hS (ρ ≫ f)).functor ⋙ spacesEtalePostcomp B S hS ρ hρ ⟶
      (spacesBaseChange B S hS (τ ≫ f)).functor ⋙ spacesEtalePostcomp B S hS τ hτ :=
  Functor.whiskerRight (spacesBaseChange_comp B S hS ρ f).inv
      (spacesEtalePostcomp B S hS ρ hρ) ≫
    Functor.whiskerLeft (spacesBaseChange B S hS f).functor
      (postcompBaseChangeOverMapNat B S hS τ hτ hρ θ hθ (spacesBaseChange B S hS ρ)
        (spacesBaseChange B S hS τ)) ≫
    Functor.whiskerRight (spacesBaseChange_comp B S hS τ f).hom
      (spacesEtalePostcomp B S hS τ hτ)

/-- **The composite morphism of functors is `prod.functor.map θ` over the base change along
`f`.**  Under the comparison `AlgebraicGeometry.Space.postcompBaseChangeCompProdIso`, which
reads `V ×_Y U` over `X` as the product `U ⨯ (V ×_Y X)`, the morphism
`AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat` is the morphism of products induced
by `θ`.

In the proof of Stacks 03M8, with `R = U ×_X U` and `θ` one of its projections `t, s`, this says
that the arrow `V ×_Y U ⟶ V ×_Y R` of the asserted sequence is the arrow `prod.map t (𝟙)` of the
sequence of `AlgebraicGeometry.Space.isLimitForkDirectImage`.

Both sides begin with the same conjugating isomorphism, and the two middle occurrences of
`AlgebraicGeometry.Space.spacesBaseChange_comp` of `τ` cancel, so the statement reduces to
`AlgebraicGeometry.Space.postcompBaseChangeOverMap_prodIsoApp` at the base change of `V` along
`f`. -/
theorem postcompBaseChangeCompOverMapNat_prodIso :
    postcompBaseChangeCompOverMapNat B S hS τ hτ hρ θ hθ f ≫
        (postcompBaseChangeCompProdIso B S hS τ hτ f).hom =
      (postcompBaseChangeCompProdIso B S hS ρ hρ f).hom ≫
        Functor.whiskerLeft (spacesBaseChange B S hS f).functor
          (prod.functor.map (etaleOverMap B S hS τ hτ hρ θ hθ)) := by
  refine NatTrans.ext (funext fun V ↦ ?_)
  have hcancel : (spacesEtalePostcomp B S hS τ hτ).map
        ((spacesBaseChange_comp B S hS τ f).hom.app V) ≫
      (spacesEtalePostcomp B S hS τ hτ).map
        ((spacesBaseChange_comp B S hS τ f).inv.app V) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact (spacesEtalePostcomp B S hS τ hτ).map_id _
  simp only [postcompBaseChangeCompOverMapNat, postcompBaseChangeCompProdIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.assoc, Category.id_comp]
  rw [← Category.assoc ((spacesEtalePostcomp B S hS τ hτ).map
      ((spacesBaseChange_comp B S hS τ f).hom.app V)), hcancel, Category.id_comp]
  exact congrArg (fun m ↦ (spacesEtalePostcomp B S hS ρ hρ).map
      ((spacesBaseChange_comp B S hS ρ f).inv.app V) ≫ m)
    (postcompBaseChangeOverMap_prodIsoApp B S hS τ hτ (spacesBaseChange B S hS τ) hρ θ hθ
      (spacesBaseChange B S hS ρ) ((spacesBaseChange B S hS f).functor.obj V))

/-- The inverse form of `AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat_prodIso`,
which is the direction a restriction of sections consumes: the comparison of the products,
followed by the morphism of base changes, is the morphism of products followed by the
comparison.

It is the previous statement with the two isomorphisms moved across. -/
theorem postcompBaseChangeCompProdIso_inv_comp :
    (postcompBaseChangeCompProdIso B S hS ρ hρ f).inv ≫
        postcompBaseChangeCompOverMapNat B S hS τ hτ hρ θ hθ f =
      Functor.whiskerLeft (spacesBaseChange B S hS f).functor
          (prod.functor.map (etaleOverMap B S hS τ hτ hρ θ hθ)) ≫
        (postcompBaseChangeCompProdIso B S hS τ hτ f).inv :=
  (Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2
      (postcompBaseChangeCompOverMapNat_prodIso B S hS τ hτ hρ θ hθ f)).trans
      (Category.assoc _ _ _))

/-! ### The two parallel arrows on sections -/

variable {A : Type w} [Category.{w'} A]

/-- **The parallel arrow of Stacks 03M8 on sections.**  For a presheaf `P` on the spaces-étale
site of `X` with arbitrary coefficients, restriction of sections along
`AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat` corresponds, under the identification
`AlgebraicGeometry.Space.postcompBaseChangeCompSectionsIso` of the sections over the base
changes with the sections over the products, to restriction along `prod.map θ (𝟙)`.

So the map `(V ↦ P(V ×_Y U)) ⟶ (V ↦ P(V ×_Y R))` of sections induced by `θ` is the map of the
sequence of `AlgebraicGeometry.Space.isLimitForkProdOfEtalePresentation`.  It is
`AlgebraicGeometry.Space.postcompBaseChangeCompProdIso_inv_comp` with the opposite
transformation whiskered into `P`. -/
theorem postcompBaseChangeCompSectionsIso_naturality (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A) :
    Functor.whiskerRight
          (NatTrans.op (postcompBaseChangeCompOverMapNat B S hS τ hτ hρ θ hθ f)) P ≫
        (postcompBaseChangeCompSectionsIso B S hS ρ hρ f P).hom =
      (postcompBaseChangeCompSectionsIso B S hS τ hτ f P).hom ≫
        Functor.whiskerLeft (spacesBaseChange B S hS f).functor.op
          (Functor.whiskerRight
            (NatTrans.op (prod.functor.map (etaleOverMap B S hS τ hτ hρ θ hθ))) P) := by
  refine NatTrans.ext (funext fun V ↦ ?_)
  refine ((P.map_comp _ _).symm.trans ?_).trans (P.map_comp _ _)
  exact congrArg (fun m ↦ P.map (Quiver.Hom.op m))
    (congrFun (congrArg NatTrans.app
      (postcompBaseChangeCompProdIso_inv_comp B S hS τ hτ hρ θ hθ f)) V.unop)

/-- **The parallel arrow of Stacks 03M8 on the sections over the étale charts of the target.**
The previous statement restricted along the comparison functor of Stacks 03G1 for `Y`: its
right-hand side is the parallel arrow of the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage`, whose source and target are the sections of
`P` over `U ⨯ (V ×_Y X)` and `R ⨯ (V ×_Y X)` for the étale scheme charts `V` of `Y`. -/
theorem postcompBaseChangeChartSectionsIso_naturality (P : (SpacesEtale B S hS X)ᵒᵖ ⥤ A) :
    Functor.whiskerLeft (comparisonFunctor B S hS Y).op
          (Functor.whiskerRight
            (NatTrans.op (postcompBaseChangeCompOverMapNat B S hS τ hτ hρ θ hθ f)) P) ≫
        Functor.whiskerLeft (comparisonFunctor B S hS Y).op
          (postcompBaseChangeCompSectionsIso B S hS ρ hρ f P).hom =
      Functor.whiskerLeft (comparisonFunctor B S hS Y).op
          (postcompBaseChangeCompSectionsIso B S hS τ hτ f P).hom ≫
        Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
          (Functor.whiskerRight
            (NatTrans.op (prod.functor.map (etaleOverMap B S hS τ hτ hρ θ hθ))) P) :=
  congrArg (Functor.whiskerLeft (comparisonFunctor B S hS Y).op)
    (postcompBaseChangeCompSectionsIso_naturality B S hS τ hτ hρ θ hθ f P)

/-! ### The vocabulary of an étale scheme chart -/

/-- An étale scheme chart of `X`, read as an object of the spaces-étale site by the comparison
functor of Stacks 03G1, is the source of its own structure morphism read as an étale morphism:
the two spellings `AlgebraicGeometry.Space.etaleOverObj` and
`AlgebraicGeometry.Space.comparisonFunctor` of one object agree by `Eq.refl`. -/
theorem etaleOverObj_comparisonFunctor_obj (W : SmallEtale B S hS X.1) :
    etaleOverObj B S hS ((comparisonFunctor B S hS X).obj W).1.hom
        ((comparisonFunctor B S hS X).obj W).2 =
      (comparisonFunctor B S hS X).obj W := rfl

/-- A morphism of étale scheme charts of `X`, read in the spaces-étale site by the comparison
functor of Stacks 03G1, is the morphism `AlgebraicGeometry.Space.etaleOverMap` attached to its
underlying morphism of algebraic spaces.  It holds by `Eq.refl`.

So the two parallel arrows of Stacks 03M8, which the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage` carries in the form
`prod.functor.map ((comparisonFunctor X).map t)`, are the arrows
`prod.functor.map (etaleOverMap …)` of
`AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat_prodIso`. -/
theorem etaleOverMap_comparisonFunctor_map {U' R' : SmallEtale B S hS X.1} (t : R' ⟶ U') :
    etaleOverMap B S hS ((comparisonFunctor B S hS X).obj U').1.hom
        ((comparisonFunctor B S hS X).obj U').2
        ((comparisonFunctor B S hS X).obj R').2
        ((comparisonFunctor B S hS X).map t).hom.left
        (Over.w ((comparisonFunctor B S hS X).map t).hom) =
      (comparisonFunctor B S hS X).map t := rfl

end AlgebraicGeometry.Space

end
