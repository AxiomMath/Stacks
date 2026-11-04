module

public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.AffineSections

/-!
# Global sections of the internal hom

Let `X` be a scheme and let `G`, `M` be `𝒪_X`-modules. A section of `SheafHom(G, M)` over an open
`U` is a morphism `G|_U ⟶ M|_U` of modules on the slice site over `U`. For `U = ⊤` the slice site
is the site of `X` itself, so a *global* section of `SheafHom(G, M)` ought to be nothing but a
morphism `G ⟶ M`. This file proves that, as an isomorphism of abelian groups, and records its
naturality in the target.

Nothing here is geometric: no finiteness, coherence or quasi-coherence hypothesis is imposed on
`G` or `M`. The statement is the degenerate case `U = ⊤` of the comparison of
[Stacks, Tag 0882], and it is the step that turns a computation with the internal hom into a
statement about morphisms of modules.

## Main definitions

* `Stacks.Algebraization.restrictFunctorTopFullyFaithful` — restriction along `(⊤ : X.Opens).ι` is
  fully faithful.
* `Stacks.Algebraization.overFunctorTopFullyFaithful` — passing to the slice site over `⊤` is
  fully faithful on sheaves of modules.
* `Stacks.Algebraization.topOverForget` — passage to the slice site over `⊤`, followed by the
  forgetful functor to presheaves of modules. Its hom-sets are, on the nose, the global sections
  of the internal hom.
* `Stacks.Algebraization.internalHomSectionsTopEquiv` — **the comparison**: the global sections of
  `SheafHom(G, M)` are the morphisms `G ⟶ M`, as abelian groups.

## Main results

* `Stacks.Algebraization.internalHomSectionsTopEquiv_map` — the comparison is natural in the
  target: the internal hom of `f : M ⟶ N` acts on global sections by postcomposition with `f`.

## Implementation notes

`(⊤ : X.Opens).ι` is an isomorphism of schemes, namely `AlgebraicGeometry.Scheme.topIso X`, so
restriction along it is an equivalence of module categories; in particular it is fully faithful.
Mathlib's `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` identifies passage to the slice site
over `U`, followed by `AlgebraicGeometry.Scheme.Modules.overEquiv`, with restriction along `U.ι`,
and `overEquiv` is an equivalence; so passage to the slice site over `⊤` is fully faithful too.

The comparison is then assembled as the inverse of the hom-set bijection of
`topOverForget`, which is fully faithful and additive. Taking it in that direction is what makes
both the additivity and the naturality cheap: the forward map is `(topOverForget X).map`, whose
additivity and functoriality are definitional, while the hom-set of `topOverForget` *is* the
module of global sections of the internal hom, and the action of `SheafHom(G, -)` on a morphism
`f` *is* postcomposition with `(topOverForget X).map f`, both on the nose.

## References

* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ

/-! ### Modules on the slice site over the whole space -/

/-- **Restriction along `(⊤ : X.Opens).ι` is fully faithful.** The open immersion
`(⊤ : X.Opens).ι` is an isomorphism of schemes (`AlgebraicGeometry.Scheme.topIso`), restriction
agrees with pullback (`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), and pullback
along an isomorphism is an equivalence. -/
public noncomputable def restrictFunctorTopFullyFaithful (X : Scheme.{u}) :
    (Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).FullyFaithful :=
  have : (Scheme.Modules.pullback (⊤ : X.Opens).ι).IsEquivalence :=
    Stacks.Coherent.pullback_isEquivalence_of_iso (Scheme.topIso X)
  (Functor.FullyFaithful.ofFullyFaithful (Scheme.Modules.pullback (⊤ : X.Opens).ι)).ofIso
    (Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).symm

/-- **Passage to the slice site over `⊤` is fully faithful.** By
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` the composite of `SheafOfModules.overFunctor`
with the equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv` is restriction along
`(⊤ : X.Opens).ι`, which is fully faithful by `restrictFunctorTopFullyFaithful`; a functor whose
composite with a faithful functor is fully faithful is itself fully faithful. -/
public noncomputable def overFunctorTopFullyFaithful (X : Scheme.{u}) :
    (SheafOfModules.overFunctor X.ringCatSheaf (⊤ : X.Opens)).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := (Scheme.Modules.overEquiv (⊤ : X.Opens)).functor)
    ((restrictFunctorTopFullyFaithful X).ofIso
      (Scheme.Modules.overFunctorEquiv (⊤ : X.Opens)).symm)

/-- An `𝒪_X`-module read as a presheaf of modules on the slice site over `⊤`. A morphism between
two values of this functor is exactly a global section of the internal hom of its arguments,
which is what makes it the right vehicle for `internalHomSectionsTopEquiv`. -/
public abbrev topOverForget (X : Scheme.{u}) :=
  SheafOfModules.overFunctor X.ringCatSheaf (⊤ : X.Opens) ⋙
    SheafOfModules.forget (X.ringCatSheaf.over (⊤ : X.Opens))

/-- `topOverForget` is additive: both of its factors act on morphisms componentwise. -/
public instance topOverForget_additive (X : Scheme.{u}) : (topOverForget X).Additive where
  map_add := by intros; rfl

/-- **The global sections of `SheafHom(G, M)` are the morphisms `G ⟶ M`.** This is the hom-set
bijection of the fully faithful additive functor `topOverForget`, read backwards: a morphism
`G ⟶ M` is sent to its image under `topOverForget`, and that image is literally a global section
of the internal hom. -/
public noncomputable def internalHomSectionsTopMapAddEquiv {X : Scheme.{u}} (G M : X.Modules) :
    (G ⟶ M) ≃+ ((sheafHomFunctor X G).obj M).val.obj (op (⊤ : X.Opens)) :=
  AddEquiv.ofBijective (M := (G ⟶ M))
    (N := ((sheafHomFunctor X G).obj M).val.obj (op (⊤ : X.Opens)))
    (topOverForget X).mapAddHom
    ((overFunctorTopFullyFaithful X).comp
      (SheafOfModules.fullyFaithfulForget _)).homEquiv.bijective

/-- **The global sections of `SheafHom(G, M)` are the morphisms `G ⟶ M`.** A section of the
internal hom over an open `U` is a morphism of modules on the slice site over `U`; for `U = ⊤`
that site is the site of `X`, so such a section is a morphism `G ⟶ M`. No hypothesis on `G` or
`M` is needed: this is the degenerate case of the comparison of [Stacks, Tag 0882]. -/
public noncomputable def internalHomSectionsTopEquiv {X : Scheme.{u}} (G M : X.Modules) :
    ((sheafHomFunctor X G).obj M).val.obj (op (⊤ : X.Opens)) ≃+ (G ⟶ M) :=
  (internalHomSectionsTopMapAddEquiv G M).symm

/-- A morphism `G ⟶ M` is recovered from the global section of `SheafHom(G, M)` it defines. -/
public theorem internalHomSectionsTopEquiv_mapAddEquiv {X : Scheme.{u}} (G M : X.Modules)
    (g : G ⟶ M) : internalHomSectionsTopEquiv G M (internalHomSectionsTopMapAddEquiv G M g) = g :=
  (internalHomSectionsTopMapAddEquiv G M).symm_apply_apply g

/-- **The comparison is natural in the target.** The internal hom of `f : M ⟶ N` acts on global
sections by postcomposition with `f`: the morphism `G ⟶ N` attached to the image of a global
section `s` of `SheafHom(G, M)` is the morphism attached to `s`, followed by `f`. -/
public theorem internalHomSectionsTopEquiv_map {X : Scheme.{u}} (G : X.Modules)
    {M N : X.Modules} (f : M ⟶ N)
    (s : ((sheafHomFunctor X G).obj M).val.obj (op (⊤ : X.Opens))) :
    internalHomSectionsTopEquiv G N
        (((sheafHomFunctor X G).map f).val.app (op ⊤) s) =
      internalHomSectionsTopEquiv G M s ≫ f := by
  have hL : internalHomSectionsTopMapAddEquiv G N
        (internalHomSectionsTopEquiv G N (((sheafHomFunctor X G).map f).val.app (op ⊤) s)) =
      ((sheafHomFunctor X G).map f).val.app (op ⊤) s :=
    (internalHomSectionsTopMapAddEquiv G N).apply_symm_apply _
  have h1 : (topOverForget X).map (internalHomSectionsTopEquiv G M s ≫ f) =
      (topOverForget X).map (internalHomSectionsTopEquiv G M s) ≫ (topOverForget X).map f :=
    (topOverForget X).map_comp _ _
  have h2 : (topOverForget X).map (internalHomSectionsTopEquiv G M s) ≫
        (topOverForget X).map f =
      ((sheafHomFunctor X G).map f).val.app (op ⊤) s :=
    congrArg (fun k : (topOverForget X).obj G ⟶ (topOverForget X).obj M =>
        k ≫ (topOverForget X).map f)
      ((internalHomSectionsTopMapAddEquiv G M).apply_symm_apply s)
  exact (internalHomSectionsTopMapAddEquiv G N).injective (hL.trans (h1.trans h2).symm)

end Stacks.Algebraization

end
