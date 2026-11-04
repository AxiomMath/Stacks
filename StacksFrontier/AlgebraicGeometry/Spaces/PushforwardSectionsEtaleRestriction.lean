module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcompProductNaturality

/-!
# The middle and right terms of Stacks 03M8 are the sections of `a_*(F|_U)` and `b_*(F|_R)`

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `τ : U ⟶ X` be étale and put `a = τ ≫ f`.  Stacks 03M8 asserts the exactness of

`0 → f_*F → a_*(F|_U) → b_*(F|_R)`,

and `AlgebraicGeometry.Space.isLimitForkDirectImage` proves it with the middle and right terms
written as the sections of the extension of `F` over the products `U ⨯ (V ×_Y X)` and
`R ⨯ (V ×_Y X)` of the spaces-étale site of `X`, which is the form the source's proof displays.
This file identifies those two terms with the sections of `a_*(G|_U)` and `b_*(G|_R)` for a
sheaf of *sets* `G` on the small étale site of `X` at the universe of the structure rings — the
identification that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PushforwardPresentationExact.lean` record as owed, for the
sheaves of sets underlying the modules of the source statement.

The identification is the composite of two steps, and both are available:

* the extension to the spaces-étale site of an étale restriction is the spaces-étale
  restriction of the extension, which is `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso`
  read through the comparison equivalence of Stacks 03G1 for `U`; and
* the base change along `a` of an object of the spaces-étale site of `Y`, read back over `X`, is
  the product `U ⨯ (V ×_Y X)`, which is
  `AlgebraicGeometry.Space.postcompBaseChangeCompProdIso`.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso` is the first step as an
  isomorphism of functors: `(G|_U)^{ext} ≅ (G^{ext})|_U`.
* `AlgebraicGeometry.Space.directImageEtaleRestrictionBaseChangeIso` reads the presheaf of
  sections of `a_*(G|_U)` as the sections of the extension of `G` over the base change along `a`
  read over `X`.
* `AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso` is the identification itself:
  the presheaf of sections of `a_*(G|_U)` **is the middle term of the fork of**
  `AlgebraicGeometry.Space.isLimitForkDirectImage`.  Taken at `ρ : R ⟶ X` in place of
  `τ : U ⟶ X` it is the same identification for the right term `b_*(G|_R)`.
* `AlgebraicGeometry.Space.directImageEtaleRestrictionParallel` is the arrow
  `a_*(G|_U) ⟶ b_*(G|_R)` of sections induced by a factorization `θ : R ⟶ U` of `ρ` through `τ`,
  read in that spelling.

## Main results

* `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction_counit_app_eq`: the counit of
  the adjunction of sites is `AlgebraicGeometry.Space.postcompBaseChangeSnd`, hence the second
  projection of the binary product `U ⨯ W`.  It holds by `Eq.refl`, and it is the bridge the
  implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleCounitFork.lean` record as missing between the
  counit spelling of the fork and the product spelling.
* `AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso_obj` reads the identification
  over a single étale scheme chart `V` of `Y`: the sections of `a_*(G|_U)` over `V` are the
  sections of the extension of `G` over `U ⨯ (V ×_Y X)`.
* `AlgebraicGeometry.Space.directImageEtaleRestrictionParallel_sectionsIso`: under the
  identification the arrow of sections induced by `θ` **is the parallel arrow of that fork**,
  namely restriction along `prod.map θ (𝟙)`.  With `R = U ×_X U` and `θ` one of its two
  projections `t, s` this is the source's `t^*` and `s^*`.

## Implementation notes

Everything is stated on *presheaves* of sections and not on sheaves: the target of the product
comparison is restriction along `W ↦ U ⨯ W`, and that functor is not shown to be continuous, so
the middle and right terms of the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage` are presheaves on the small étale site of `Y`
and nothing more.  The sheaf-level content enters only in the first step, where the comparison
equivalence of Stacks 03G1 for `U` is used to move the extension past the restriction; the
isomorphism it produces is carried to presheaves by `CategoryTheory.sheafToPresheaf`.

The three reindexings that relate the spelling of
`AlgebraicGeometry.Space.smallEtaleDirectImage` to the spelling of the fork hold by `Eq.refl`:
restriction along a composite of functors of sites is the composite of the restrictions on the
nose, `(F ⋙ G).op` is `F.op ⋙ G.op`, and composition of functors is associative.  So no
`CategoryTheory.eqToHom` appears below and the two isomorphisms compose directly.

What is **not** here is the identification of
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel` with the *canonical* arrow
`a_*(G|_U) ⟶ b_*(G|_R)` — the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `θ`, pushed forward along `a`
and followed by the composition comparison of direct images of Stacks 03G2, part (3).  That
comparison, and the `𝒪_Y`-linearity which would lift the whole diagram from sheaves of sets to
`Mod(𝒪_Y)`, are what still separate this file from the `a_*`/`b_*` reading of Stacks 03M8 in
`Mod(𝒪_Y)`; the registration of the tag therefore stays on
`AlgebraicGeometry.Space.isLimitForkDirectImage`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X U R Y : AlgebraicSpaces B S hS} (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    {ρ : R ⟶ X} (hρ : IsEtale B S hS ρ.hom) (θ : R ⟶ U) (hθ : θ ≫ τ = ρ) (f : X ⟶ Y)

/-! ### The counit of the base-change adjunction is the second projection -/

/-- **The counit of `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` is the
projection of the postcomposed base change to the base.**  For an étale `τ : U ⟶ X` and an
object `W` of the spaces-étale site of `X`, the component at `W` of that counit is
`AlgebraicGeometry.Space.postcompBaseChangeSnd` of the canonical base-change datum, and it holds
by `Eq.refl`.

This is the identification that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleCounitFork.lean` record as the bridge between
the counit spelling of the fork of Stacks 03M8 and the product spelling: the counit is the
projection, and by
`AlgebraicGeometry.Space.isLimitBinaryFanPostcompBaseChange` the projection is the second
projection of the binary product `U ⨯ W` of the spaces-étale site of `X`.  The underlying
morphism of algebraic spaces was already identified with the cartesian projection by
`AlgebraicGeometry.Space.toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit`; this
lifts that identification from the underlying algebraic spaces to the morphisms of the site. -/
theorem spacesEtalePostcompBaseChangeAdjunction_counit_app_eq (W : SpacesEtale B S hS X) :
    (spacesEtalePostcompBaseChangeAdjunction B S hS τ hτ).counit.app W =
      postcompBaseChangeSnd B S hS τ hτ (spacesBaseChange B S hS τ) W := rfl

/-! ### The extension of an étale restriction is the restriction of the extension -/

/-- **The extension to the spaces-étale site of an étale restriction is the spaces-étale
restriction of the extension.**  For an étale morphism `τ : U ⟶ X` of algebraic spaces,
restricting a sheaf of sets on the small étale site of `X` along small étale postcomposition
with `τ` and then extending it to the spaces-étale site of `U` by the comparison equivalence of
Stacks 03G1 is extending it to the spaces-étale site of `X` and then restricting along
spaces-étale postcomposition with `τ`.

It is `AlgebraicGeometry.Space.smallEtaleSetRestrictionConjIso`, which writes small étale
restriction as the conjugate of spaces-étale restriction, with the comparison equivalence for
`U` cancelled against its own inverse. -/
noncomputable def spacesEtaleExtensionRestrictionIso :
    smallEtaleSetRestriction B S hS τ hτ ⋙
        (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse ≅
      (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse ⋙
        spacesEtaleSetRestriction B S hS τ hτ :=
  Functor.isoWhiskerRight (smallEtaleSetRestrictionConjIso B S hS τ hτ)
      (smallEtaleComparisonRestriction B S hS U).asEquivalence.inverse ≪≫
    Functor.isoWhiskerLeft (smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse
      (Functor.isoWhiskerLeft (spacesEtaleSetRestriction B S hS τ hτ)
          (smallEtaleComparisonRestriction B S hS U).asEquivalence.unitIso.symm ≪≫
        Functor.rightUnitor _)

/-! ### The sections of `a_*(G|_U)` -/

/-- **The sections of `a_*(G|_U)` are the sections of the extension of `G` over the base change
along `a`, read over `X`.**  For `a = τ ≫ f` and a sheaf of sets `G` on the small étale site of
`X` at the universe of the structure rings, the presheaf on the small étale site of `Y` of
sections of the direct image along `a` of the étale restriction of `G` to `U` is the presheaf
`V ↦ G^{ext}((V ×_Y U) read over X)`.

`AlgebraicGeometry.Space.smallEtaleDirectImage` is extension to the spaces-étale site followed
by restriction along spaces-étale base change and then along the comparison functor of
Stacks 03G1, so the only step is
`AlgebraicGeometry.Space.spacesEtaleExtensionRestrictionIso`; the three reindexings are
`Eq.refl`. -/
noncomputable def directImageEtaleRestrictionBaseChangeIso
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((smallEtaleDirectImage B S hS (τ ≫ f)).obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj G)).obj ≅
      (comparisonFunctor B S hS Y).op ⋙
        (((spacesBaseChange B S hS (τ ≫ f)).functor ⋙
            spacesEtalePostcomp B S hS τ hτ).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) :=
  Functor.isoWhiskerLeft (comparisonFunctor B S hS Y).op
    (Functor.isoWhiskerLeft (spacesBaseChange B S hS (τ ≫ f)).functor.op
      ((sheafToPresheaf (SpacesEtale.topology B S hS U) (Type u)).mapIso
        ((spacesEtaleExtensionRestrictionIso B S hS τ hτ).app G)))

/-- **The middle term of Stacks 03M8 is the sections of `a_*(G|_U)`.**  For `a = τ ≫ f` the
presheaf on the small étale site of `Y` of sections of `a_*(G|_U)` is the middle term

`V ↦ G^{ext}(U ⨯ (V ×_Y X))`

of the fork of `AlgebraicGeometry.Space.isLimitForkDirectImage`.  Read at `ρ : R ⟶ X` in place
of `τ : U ⟶ X` it is the same statement for the right term `b_*(G|_R)`.

It is `AlgebraicGeometry.Space.directImageEtaleRestrictionBaseChangeIso` followed by the
geometric comparison `AlgebraicGeometry.Space.postcompBaseChangeCompSectionsIso`. -/
noncomputable def directImageEtaleRestrictionSectionsIso
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((smallEtaleDirectImage B S hS (τ ≫ f)).obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj G)).obj ≅
      (chartBaseChangeFunctor B S hS f).op ⋙
        ((prod.functor.obj (etaleOverObj B S hS τ hτ)).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) :=
  directImageEtaleRestrictionBaseChangeIso B S hS τ hτ f G ≪≫
    Functor.isoWhiskerLeft (comparisonFunctor B S hS Y).op
      (postcompBaseChangeCompSectionsIso B S hS τ hτ f
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj)

/-- The middle term of the fork of `AlgebraicGeometry.Space.isLimitForkDirectImage`, read over a
single étale scheme chart `V` of `Y`, is the set of sections of the extension of `G` over the
product `U ⨯ (V ×_Y X)` of the spaces-étale site of `X`, where `V ×_Y X` is
`AlgebraicGeometry.Space.chartBaseChange`.  It holds by `Eq.refl`.

So `AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso` reads the sections of
`a_*(G|_U)` over `V` as `G^{ext}(U ⨯ (V ×_Y X))`, which is what the proof of Stacks 03M8
displays. -/
theorem directImageEtaleRestrictionSectionsIso_obj
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : SmallEtale B S hS Y.1) :
    ((chartBaseChangeFunctor B S hS f).op ⋙
        ((prod.functor.obj (etaleOverObj B S hS τ hτ)).op ⋙
          ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
            G).obj)).obj (op V) =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj.obj
        (op (etaleOverObj B S hS τ hτ ⨯ chartBaseChange B S hS f V)) := rfl

/-! ### The two parallel arrows in the `a_*`/`b_*` spelling -/

/-- **The arrow `a_*(G|_U) ⟶ b_*(G|_R)` of sections induced by a factorization of `ρ` through
`τ`.**  For `θ : R ⟶ U` with `θ ≫ τ = ρ`, restriction of sections along
`AlgebraicGeometry.Space.postcompBaseChangeCompOverMapNat`, read in the spelling of the direct
images along `a = τ ≫ f` and `b = ρ ≫ f` by
`AlgebraicGeometry.Space.directImageEtaleRestrictionBaseChangeIso`.

With `R = U ×_X U` and `θ` one of its two projections `t, s : R ⟶ U` this is the source's `t^*`
and `s^*` on sections. -/
noncomputable def directImageEtaleRestrictionParallel
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((smallEtaleDirectImage B S hS (τ ≫ f)).obj
        ((smallEtaleSetRestriction B S hS τ hτ).obj G)).obj ⟶
      ((smallEtaleDirectImage B S hS (ρ ≫ f)).obj
        ((smallEtaleSetRestriction B S hS ρ hρ).obj G)).obj :=
  (directImageEtaleRestrictionBaseChangeIso B S hS τ hτ f G).hom ≫
    Functor.whiskerLeft (comparisonFunctor B S hS Y).op
      (Functor.whiskerRight
        (NatTrans.op (postcompBaseChangeCompOverMapNat B S hS τ hτ hρ θ hθ f))
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) ≫
    (directImageEtaleRestrictionBaseChangeIso B S hS ρ hρ f G).inv

/-- **The arrow of sections induced by `θ` is the parallel arrow of the fork of Stacks 03M8.**
Under the identification `AlgebraicGeometry.Space.directImageEtaleRestrictionSectionsIso` of the
sections of `a_*(G|_U)` and `b_*(G|_R)` with the middle and right terms of the fork of
`AlgebraicGeometry.Space.isLimitForkDirectImage`, the arrow
`AlgebraicGeometry.Space.directImageEtaleRestrictionParallel` is restriction along
`prod.map θ (𝟙)`, which is the parallel arrow of that fork.

With `R = U ×_X U` and `θ` one of its projections this is the identification of the source's
`t^*` and `s^*` with the two arrows of the displayed sequence of sections; the comparison of the
geometric arrow with `prod.map θ (𝟙)` is
`AlgebraicGeometry.Space.postcompBaseChangeChartSectionsIso_naturality`, and
`AlgebraicGeometry.Space.etaleOverMap_comparisonFunctor_map` writes the latter in the spelling
`prod.functor.map ((comparisonFunctor X).map t)` the fork carries. -/
theorem directImageEtaleRestrictionParallel_sectionsIso
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    directImageEtaleRestrictionParallel B S hS τ hτ hρ θ hθ f G ≫
        (directImageEtaleRestrictionSectionsIso B S hS ρ hρ f G).hom =
      (directImageEtaleRestrictionSectionsIso B S hS τ hτ f G).hom ≫
        Functor.whiskerLeft (chartBaseChangeFunctor B S hS f).op
          (Functor.whiskerRight
            (NatTrans.op (prod.functor.map (etaleOverMap B S hS τ hτ hρ θ hθ)))
            ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj G).obj) := by
  rw [directImageEtaleRestrictionParallel, directImageEtaleRestrictionSectionsIso,
    directImageEtaleRestrictionSectionsIso, Iso.trans_hom, Iso.trans_hom, Category.assoc,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_hom,
    postcompBaseChangeChartSectionsIso_naturality B S hS τ hτ hρ θ hθ f]

end AlgebraicGeometry.Space

end
