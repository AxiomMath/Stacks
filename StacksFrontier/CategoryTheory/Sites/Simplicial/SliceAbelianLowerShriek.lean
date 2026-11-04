module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableLowerShriek

/-!
# Extension by zero from a simplicial slice to the base site

Let `(C, J)` be a site and let `K` be a simplicial object of `SR(C)`, so that the simplicial
family of sites `n ↦ C/K_n` carries an augmentation `a` towards `(C, J)` given by the degree-zero
localization functor. In simplicial degree `p` the localization functor
`j_p : C/K_p ⥤ C` is continuous, so restriction along it has a left adjoint: the extension by
zero `j_{p!}` on abelian sheaves.

The component inclusion `C/K_p ⥤ (C/K)_total` followed by the localization functor `j_total` of
the total site is `j_p`, so the composite `a_! ∘ g_{p!}` of the two extensions by zero is
`j_{p!}`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriek`: the extension by zero
  `j_{p!} : Ab(C/K_p) ⥤ Ab(C)`.
* `CategoryTheory.SimplicialSemiRepresentable.sliceAbelianLowerShriekAdjunction`: the adjunction
  `j_{p!} ⊣ j_p^{-1}`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.componentFunctor_comp_totalForget`: the component
  inclusion of degree `p` followed by `j_total` is `j_p`.
* `CategoryTheory.SimplicialSemiRepresentable.componentLowerShriekCompAugmentationAbelianIso`:
  `g_{p!}` followed by `a_!` is `j_{p!}`.

## Implementation notes

All three functors are left adjoints of restriction along a continuous site functor, and the
composite of the two restrictions is the third restriction, by
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` applied to the equality of site functors
`componentFunctor_comp_totalForget`. Uniqueness of left adjoints — in the form
`CategoryTheory.Adjunction.leftAdjointCompIso` — turns that identification of the right adjoints
into the asserted isomorphism of the left adjoints.

The equality of site functors is `ι_comp_totalForget` read at `op p`. It is stated there for
`Grothendieck.ι (slices K) (op p)`, which is the component inclusion of the situation attached to
`K`; the total topology of that situation is carried by `(situation J K).totalCategory`, that is
`Cat.of (Grothendieck (slices K))`, whose category instance is `Cat.str` rather than
`Grothendieck.instCategory`. The two instances are definitionally equal but not syntactically, so
nothing which must be found by instance search may be stated at only one of the two spellings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- The component inclusion `C/K_p ⥤ (C/K)_total` of simplicial degree `p`, followed by the
localization functor `j_total` of the total site, is the localization functor `j_p`. This is
`ι_comp_totalForget` read at the component inclusion of the simplicial-site situation attached to
`K`. -/
theorem componentFunctor_comp_totalForget (p : SimplexCategory) :
    SimplicialSiteSituation.componentFunctor (situation J K) p ⋙ totalForget K =
      sliceForget K (op p) :=
  ι_comp_totalForget K (op p)

/-- Continuity of `j_total`, stated with the total category spelled as
`(situation J K).totalCategory` and so carrying the `Cat.str` category instance rather than
`Grothendieck.instCategory`. -/
theorem totalForget_isContinuous_totalCategory :
    @Functor.IsContinuous _ (Cat.str ((situation J K).totalCategory)) _ _ (totalForget K)
      ((situation J K).totalTopology) J :=
  totalForget_isContinuous J K

/-- Continuity of `j_p`, stated with its source spelled as `(situation J K).component p`, which
carries the `Cat.str` instance of that `Cat`-valued expression rather than that of
`(slices K).obj (op p)`. -/
theorem sliceForget_isContinuous_component (p : SimplexCategory) :
    @Functor.IsContinuous _ (Cat.str ((situation J K).component p)) _ _ (sliceForget K (op p))
      ((situation J K).componentTopology p) J :=
  sliceForget_isContinuous J K p

/-- The extension by zero `j_{p!} : Ab(C/K_p) ⥤ Ab(C)` along the localization functor
`j_p : C/K_p ⥤ C` of the simplicial degree `p`: the sheaf pullback of abelian sheaves along `j_p`,
that is the left Kan extension along `j_p` followed by sheafification. -/
def sliceAbelianLowerShriek (p : SimplexCategory) :
    Sheaf ((situation J K).componentTopology p) AddCommGrpCat.{u} ⥤
      Sheaf J AddCommGrpCat.{u} :=
  Functor.sheafPullbackConstruction.sheafPullback (sliceForget K (op p)) AddCommGrpCat.{u}
    ((situation J K).componentTopology p) J

/-- The extension by zero `j_{p!}` is left adjoint to the inverse image `j_p^{-1}`, which is
restriction along `j_p`. -/
def sliceAbelianLowerShriekAdjunction (p : SimplexCategory) :
    sliceAbelianLowerShriek J K p ⊣
      (sliceForget K (op p)).sheafPushforwardContinuous AddCommGrpCat.{u}
        ((situation J K).componentTopology p) J :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (sliceForget K (op p))
    AddCommGrpCat.{u} ((situation J K).componentTopology p) J

/-- **Lower shriek from a simplicial slice factors through the total site.** The extension by zero
`g_{p!}` from the component of degree `p` to the total site, followed by the extension by zero
`a_!` along the augmentation, is the extension by zero `j_{p!}` along the localization functor
`j_p`. -/
def componentLowerShriekCompAugmentationAbelianIso (p : SimplexCategory) :
    SimplicialSiteSituation.componentLowerShriekAb (situation J K) p ⋙
        augmentationAbelianLowerShriek J K ≅
      sliceAbelianLowerShriek J K p :=
  haveI := totalForget_isContinuous_totalCategory J K
  haveI := sliceForget_isContinuous_component J K p
  Adjunction.leftAdjointCompIso
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (SimplicialSiteSituation.componentFunctor (situation J K) p) AddCommGrpCat.{u}
      ((situation J K).componentTopology p) ((situation J K).totalTopology))
    (augmentationAbelianLowerShriekAdjunction J K)
    (sliceAbelianLowerShriekAdjunction J K p)
    (Functor.sheafPushforwardContinuousComp'
      (eqToIso (componentFunctor_comp_totalForget J K p)) AddCommGrpCat.{u}
      ((situation J K).componentTopology p) ((situation J K).totalTopology) J)

end CategoryTheory.SimplicialSemiRepresentable

end
