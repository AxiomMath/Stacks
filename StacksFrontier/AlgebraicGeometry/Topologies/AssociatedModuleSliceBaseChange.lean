module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleSliceConditions
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentCore

/-!
# Base change of the associated module to a slice of a site of schemes

Let `S` be a scheme, let `toOver : C ⥤ Over S` present a site of schemes over `S` as in
Tag 03OJ, let `X` be an object of the site and write `g : (toOver.obj X).left ⟶ S` for its
structure morphism.  The slice `Over X` is again a site of schemes, over the *new* base
`(toOver.obj X).left`, by `Stacks.Sites.sliceToOver`; all four conditions of Tag 03OJ are
inherited (`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleSliceConditions`).

**This file identifies the associated module of the base change with the restriction of the
associated module**: for a quasi-coherent module `F` on `S`,

`(g⁺F)ᵃ ≅ Fᵃ|_{C/X}`,

where the right-hand side is the restriction along `CategoryTheory.Over.forget X`.  This is the
step which lets the local statement of Tag 03OJ, applied on the slice at a member of a covering,
be compared with the module one started from; the transition isomorphisms of the descent datum
that the tag's essential surjectivity assembles are built from it.

The identification exists in the tree for the inclusion of an *open* subscheme into the big fppf
site (`AlgebraicGeometry.BigFppfOver.associatedModuleOverIso`) and its two small-site twins, by a
square of ringed sites and `SheafOfModules.pullbackSquareIso`.  Nothing of that machinery is
needed here, because at this presentation the associated module is given by an explicit formula:
its sections over `T` are `Γ(T, T.hom⁺ F)`, and the whole content is the comparison of `h⁺(g⁺F)`
with `(h ≫ g)⁺F`.  That comparison is already available as
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso`, base change of the presheaf of Tag 03DS along
`CategoryTheory.Over.map g`, whose naturality is
`Stacks.Sites.pullbackSectionsMap_baseChange`.

## Main definitions

* `Stacks.Sites.sliceToOverCompOverMapIso`: reading an object of the slice as a scheme over the
  new base and then as a scheme over `S` is reading it as a scheme over `S` directly.  The two
  functors are not equal — the structure morphism of the first is the composite
  `T.left ⟶ (toOver.obj X).left ⟶ S` and of the second is the structure morphism of `T.left` —
  and `CategoryTheory.Over.w` is exactly the isomorphism between them.
* `Stacks.Sites.sliceAssociatedPresheafIso`: **`(g⁺F)ᵃ ≅ Fᵃ|_{C/X}` for the associated
  presheaves** of Tag 03DS.
* `CategoryTheory.PresheafOfModules.isoOfPresheafIso`: an isomorphism of the underlying abelian
  presheaves of two presheaves of modules whose components are linear is an isomorphism of
  presheaves of modules.
* `Stacks.Sites.sliceAssociatedModulePresheafIso`: **`(g⁺F)ᵃ ≅ Fᵃ|_{C/X}` for the associated
  presheaves of modules** of Tag 03DU, over the structure presheaf of the slice.

## Main results

* `Stacks.Sites.structurePresheaf_sliceToOver`: the structure presheaf of the slice *is* the
  restriction of the structure presheaf along `CategoryTheory.Over.forget X`, on the nose.  This
  is what makes the module-level statement an isomorphism of presheaves of modules over one ring
  presheaf and not a comparison across two.
* `Stacks.Sites.sliceAssociatedPresheafIso_hom_app_apply`: the comparison on a section — the
  pullback map along the triangle `CategoryTheory.Over.w`, followed by the inverse of the
  composition isomorphism of the pullback pseudofunctor.  It holds by `rfl`, which is what makes
  the linearity of the comparison a two-line computation: the pullback map on sections is
  semilinear over the map on global functions induced by its arrow
  (`AlgebraicGeometry.pullbackSectionsMap_smul`), that arrow is the identity here
  (`Stacks.Sites.sliceToOverCompOverMapIso_hom_app_left`), and the comparison of pullbacks is a
  morphism of modules (`AlgebraicGeometry.Scheme.Modules.Hom.app_smul`).

## Implementation notes

The quasi-coherence of `g⁺F` is Stacks 01BG, available as the instance
`Stacks.Modules.instIsQuasicoherentPullbackObj`, so it is never a hypothesis here.

`Stacks.Sites.sliceToOver` is `CategoryTheory.Over.post (toOver ⋙ Over.forget S)`, and
`CategoryTheory.Over.post` of a composite is the composite of the `CategoryTheory.Over.post`s on
the nose; that, with `CategoryTheory.Functor.op_comp`, is why the two whiskerings below compose
without any transport.

No `@[stacks]` attribute is claimed.  Base change of `Fᵃ` to a slice is a step in the proof of
the second assertion of Tag 03OJ, not an assertion of the source; the single registration of
that tag remains the one at
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcCoveringSiteSheaves`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
-/

@[expose] public section

open CategoryTheory Opposite

universe v v₁ u₁ u

namespace CategoryTheory.PresheafOfModules

/-- **An isomorphism of the underlying abelian presheaves which is linear on components is an
isomorphism of presheaves of modules.**  Only the linearity of the forward direction is assumed:
a bijective linear map has a linear inverse. -/
public noncomputable def isoOfPresheafIso {C : Type u₁} [Category.{v₁} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {M₁ M₂ : PresheafOfModules.{v} R} (α : M₁.presheaf ≅ M₂.presheaf)
    (h : ∀ (T : Cᵒᵖ) (r : R.obj T) (m : M₁.obj T), α.hom.app T (r • m) = r • α.hom.app T m) :
    M₁ ≅ M₂ where
  hom := PresheafOfModules.homMk α.hom h
  inv := PresheafOfModules.homMk α.inv (fun T r m => by
    have hgf : ∀ x : M₁.obj T, α.inv.app T (α.hom.app T x) = x :=
      fun x => congr($(congrArg (fun β => NatTrans.app β T) α.hom_inv_id) x)
    have hfg : ∀ y : M₂.obj T, α.hom.app T (α.inv.app T y) = y :=
      fun y => congr($(congrArg (fun β => NatTrans.app β T) α.inv_hom_id) y)
    have hinj : ∀ a b : M₁.obj T, α.hom.app T a = α.hom.app T b → a = b :=
      fun a b hab => (hgf a).symm.trans ((congrArg (α.inv.app T) hab).trans (hgf b))
    refine hinj _ _ ((hfg (r • m)).trans ?_)
    exact (congrArg (fun z => r • z) (hfg m)).symm.trans (h T r (α.inv.app T m)).symm)
  hom_inv_id := by
    refine PresheafOfModules.hom_ext fun T => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact congr($(congrArg (fun β => NatTrans.app β T) α.hom_inv_id) x)
  inv_hom_id := by
    refine PresheafOfModules.hom_ext fun T => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact congr($(congrArg (fun β => NatTrans.app β T) α.inv_hom_id) x)

end CategoryTheory.PresheafOfModules

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
  (F : S.Modules) [F.IsQuasicoherent] (X : C)

/-- **The structure presheaf of a slice is the restriction of the structure presheaf.**  The
underlying scheme of an object of the slice is the underlying scheme of its image in `C`
(`Stacks.Sites.sliceToOver_comp_forget`), so this holds on the nose. -/
public theorem structurePresheaf_sliceToOver :
    structurePresheaf ((toOver.obj X).left) (sliceToOver S toOver X) =
      (Over.forget X).op ⋙ structurePresheaf S toOver :=
  rfl

/-- **Reading an object of the slice at `X` as a scheme over the underlying scheme of `X` and
then as a scheme over `S` is reading it as a scheme over `S` directly.**  The two functors agree
on underlying schemes but not on structure morphisms — one is the composite through
`(toOver.obj X).left`, the other the structure morphism itself — and the triangle
`CategoryTheory.Over.w` of the image of the structure morphism of the slice object is the
isomorphism between them. -/
public def sliceToOverCompOverMapIso :
    sliceToOver S toOver X ⋙ Over.map (toOver.obj X).hom ≅ Over.forget X ⋙ toOver :=
  NatIso.ofComponents
    (fun T => Over.isoMk (Iso.refl _)
      ((Category.id_comp _).trans (Over.w (toOver.map T.hom)).symm))
    (fun {T T'} h => Over.OverMorphism.ext (by
      change (toOver.map h.left).left ≫ 𝟙 ((sliceToOver S toOver X).obj T').left =
        𝟙 ((sliceToOver S toOver X).obj T).left ≫ (toOver.map h.left).left
      exact (Category.comp_id _).trans (Category.id_comp _).symm))

/-- The comparison of `Stacks.Sites.sliceToOverCompOverMapIso` is the identity on underlying
schemes. -/
@[simp]
public theorem sliceToOverCompOverMapIso_hom_app_left (T : Over X) :
    ((sliceToOverCompOverMapIso S toOver X).hom.app T).left = 𝟙 _ :=
  rfl

/-- The comparison of `Stacks.Sites.sliceToOverCompOverMapIso` fixes the global functions, being
the identity on underlying schemes. -/
public theorem sliceToOverCompOverMapIso_hom_app_left_appTop (T : Over X)
    (r : Γ((toOver.obj T.left).left, ⊤)) :
    ((sliceToOverCompOverMapIso S toOver X).hom.app T).left.appTop r = r :=
  rfl

/-- **Base change of the associated presheaf of Tag 03DS to a slice of the site.**  The presheaf
of pullback sections of the base change `g⁺F` of a quasi-coherent module on `S` to the underlying
scheme of an object `X` of the site, formed on the slice at `X`, is the restriction along
`CategoryTheory.Over.forget X` of the presheaf of pullback sections of `F`.

It is `Stacks.Sites.quasiCoherentPresheafBaseChangeIso` — base change along
`CategoryTheory.Over.map g` — restricted along the slice functor, after the triangle
`Stacks.Sites.sliceToOverCompOverMapIso` has been used to see the slice inside the schemes over
`S` in the two ways that produce the two sides. -/
public noncomputable def sliceAssociatedPresheafIso :
    (Over.forget X).op ⋙ associatedPresheaf S F toOver ≅
      associatedPresheaf ((toOver.obj X).left)
        ((Scheme.Modules.pullback (toOver.obj X).hom).obj F) (sliceToOver S toOver X) :=
  Functor.isoWhiskerRight (NatIso.op (sliceToOverCompOverMapIso S toOver X))
      (quasiCoherentPresheafFunctor S F) ≪≫
    Functor.isoWhiskerLeft (sliceToOver S toOver X).op
      (quasiCoherentPresheafBaseChangeIso F (toOver.obj X))

/-- **The base-change comparison on a section.**  It is the pullback map on global sections along
the triangle `Stacks.Sites.sliceToOverCompOverMapIso`, followed by the inverse of the composition
isomorphism of the pullback pseudofunctor.  Both factors are identified by `rfl`: the objectwise
identifications of `AlgebraicGeometry.quasiCoherentPresheaf` are identities. -/
public theorem sliceAssociatedPresheafIso_hom_app_apply (T : (Over X)ᵒᵖ)
    (m : ((Over.forget X).op ⋙ associatedPresheaf S F toOver).obj T) :
    (sliceAssociatedPresheafIso S toOver F X).hom.app T m =
      ((Scheme.Modules.pullbackComp (((sliceToOver S toOver X).obj T.unop).hom)
            (toOver.obj X).hom).inv.app F).app ⊤
        (pullbackSectionsMap F ((sliceToOverCompOverMapIso S toOver X).hom.app T.unop) m) :=
  rfl

/-- **The associated presheaf of modules of Tag 03DU on the slice at `X`**, read over the
restriction along `CategoryTheory.Over.forget X` of the structure presheaf of the site rather than
over the structure presheaf of the slice.  The two ring presheaves are *equal*
(`Stacks.Sites.structurePresheaf_sliceToOver`), so this is the same presheaf of modules; naming it
at this spelling of the base ring is what lets it be compared with a restriction without any
transport, and is what keeps `simp` and `rw` usable on the comparison below. -/
public noncomputable def sliceAssociatedModulePresheaf :
    PresheafOfModules.{u} ((Over.forget X).op ⋙ structurePresheaf S toOver) :=
  associatedModulePresheaf ((toOver.obj X).left)
    ((Scheme.Modules.pullback (toOver.obj X).hom).obj F) (sliceToOver S toOver X)

/-- The underlying abelian presheaf of `Stacks.Sites.sliceAssociatedModulePresheaf` is the
associated presheaf of Tag 03DS of the base change, on the slice. -/
@[simp]
public theorem sliceAssociatedModulePresheaf_presheaf :
    (sliceAssociatedModulePresheaf S toOver F X).presheaf =
      associatedPresheaf ((toOver.obj X).left)
        ((Scheme.Modules.pullback (toOver.obj X).hom).obj F) (sliceToOver S toOver X) :=
  rfl

/-- **Base change of the associated presheaf of modules of Tag 03DU to a slice of the site**:
`(g⁺F)ᵃ ≅ Fᵃ|_{C/X}`.  Both sides are presheaves of modules over the structure presheaf of the
slice, which by `Stacks.Sites.structurePresheaf_sliceToOver` *is* the restriction of the
structure presheaf of the site, so no comparison of base rings takes place.

This is the transition datum that the essential surjectivity of Tag 03OJ needs: a quasi-coherent
module on the site which is `Fᵃ` on the slice at a member of a covering has to be compared, on
the overlaps, with the module it is `Fᵃ` of on the other member, and both comparisons go through
this isomorphism. -/
public noncomputable def sliceAssociatedModulePresheafIso :
    (PresheafOfModules.pushforward₀ (Over.forget X) (structurePresheaf S toOver)).obj
        (associatedModulePresheaf S F toOver) ≅
      sliceAssociatedModulePresheaf S toOver F X :=
  PresheafOfModules.isoOfPresheafIso (sliceAssociatedPresheafIso S toOver F X)
    (fun T r m => by
      refine Eq.trans (sliceAssociatedPresheafIso_hom_app_apply S toOver F X T (r • m)) ?_
      refine Eq.trans (congrArg (fun z => ((Scheme.Modules.pullbackComp
          (((sliceToOver S toOver X).obj T.unop).hom) (toOver.obj X).hom).inv.app F).app ⊤ z)
        ((pullbackSectionsMap_smul F
            ((sliceToOverCompOverMapIso S toOver X).hom.app T.unop) r m).trans
          (congrArg (fun c => c • pullbackSectionsMap F
            ((sliceToOverCompOverMapIso S toOver X).hom.app T.unop) m)
            (sliceToOverCompOverMapIso_hom_app_left_appTop S toOver X T.unop r)))) ?_
      exact Scheme.Modules.Hom.app_smul _ r _)

end Stacks.Sites

end
