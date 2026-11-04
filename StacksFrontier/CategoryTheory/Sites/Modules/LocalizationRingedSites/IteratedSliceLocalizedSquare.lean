module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.IteratedSlice
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The localized morphism of Stacks 04J0 at an iterated slice

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C` which defines a morphism of sites, let `V` be an object of `D` and `b : V' ⟶ V` a
morphism of `D`. Write `W = V'/V` for the corresponding object of the localized site `D/V` and
`W' = u'(W) = u(V')/u(V)` for its image under the localized functor `u' = Over.post u`.

Stacks 04J0 localizes the morphism of ringed sites `f` at `V`, giving `f' : (C/u(V), O_{u(V)})
⟶ (D/V, O'_V)`, and then localizes `f'` at the object `W` of its target, giving a morphism of
ringed topoi `((C/u(V))/W', O_{W'}) ⟶ ((D/V)/W, O_W)`. Both source and target are iterated
slices, and the identifications of Stacks 04IY turn them into the localizations of `(C, O)` at
`u(V')` and of `(D, O')` at `V'`. This file proves that under those identifications the twice
localized morphism *is* the morphism obtained by localizing `f` at `V'` once.

## The route

The two composites have the same direct image up to a canonical isomorphism, and that
isomorphism comes from a strict square of restriction functors. The inverse image of the
iterated-slice morphism of ringed topoi is restriction along `Over.iteratedSliceForward W`;
since that functor is one half of an equivalence of sites, restriction along the other half,
`Over.iteratedSliceBackward W`, is a right adjoint of it
(`AlgebraicGeometry.RingedSite.iteratedSliceBackwardAdjunction`). The direct image of a
localized morphism is also a restriction, and the two site functors
`Over.iteratedSliceBackward W ⋙ Over.post (Over.post u)` and
`Over.post u ⋙ Over.iteratedSliceBackward W'` are canonically isomorphic
(`AlgebraicGeometry.RingedSite.Hom.iteratedSlicePostIso`) — they differ only by the comparison
of `u(a ≫ b)` with `u(a) ≫ u(b)`. Restriction turns that into an isomorphism of the two
composites of direct images with the iterated-slice direct images replaced by restriction along
`Over.iteratedSliceBackward`, and uniqueness of right adjoints puts the chosen direct images
back.

Compatibility with the three structure maps is then a computation with units: both
iterated-slice structure maps are units, uniqueness of right adjoints carries them to the units
of the restriction adjunctions, and those units are *identities*, because the counit of the
iterated-slice equivalence is one. What is left is the identity of the two restrictions of
`f♯`, which holds by definition.

Nothing below asks `u` to be left exact: the localized morphism of Stacks 04J0 exists in Stacks
03CF's own generality, and `Over.post u` is continuous whenever `u` is, which is why
`CategoryTheory.Functor.isContinuous_overPost_of_isContinuous` is taken as a local instance.

## Main definitions

* `AlgebraicGeometry.RingedSite.iteratedSliceBackwardAdjunction`: restriction along
  `Over.iteratedSliceForward W` is left adjoint to restriction along
  `Over.iteratedSliceBackward W`.
* `AlgebraicGeometry.RingedSite.Hom.iteratedSlicePostIso`: the square of site functors relating
  the two iterated-slice embeddings with the two localizations of `u`.
* `AlgebraicGeometry.RingedSite.Hom.iteratedSliceRestrictionSquare`: the same square, read as
  restriction functors on sheaves.
* `AlgebraicGeometry.RingedSite.iteratedSliceBackwardComparison`: the comparison of the direct
  image of the iterated-slice morphism of ringed topoi with restriction along
  `Over.iteratedSliceBackward`.
* `AlgebraicGeometry.RingedSite.Hom.iteratedSliceLocalizedComparison`: the comparison of the two
  composite direct images.
* `AlgebraicGeometry.RingedSite.Hom.iteratedSliceLocalizedSquare`: the square itself, as a
  2-isomorphism of ringed topoi.

## Main results

* `AlgebraicGeometry.RingedSite.iteratedSliceBackwardAdjunction_unit_app`: the unit of that
  adjunction is the identity.
* `AlgebraicGeometry.RingedSite.Hom.iteratedSliceRestrictionSquare_hom_app_structureSheaf`: the
  comparison of the two restriction composites is the identity at the structure sheaf.
* `AlgebraicGeometry.RingedSite.Hom.iteratedSliceBackward_map_forgetFSharp`: restricting the
  structure map of the twice localized morphism along `Over.iteratedSliceBackward W` gives the
  structure map of the morphism localized at `V'`.
* `AlgebraicGeometry.RingedSite.forgetFSharp_iteratedSliceBackwardComparison` and
  `.forgetFSharp_eq_iteratedSliceBackwardComparison_inv`: the structure map of the
  iterated-slice morphism of ringed topoi is the inverse of that comparison at the structure
  sheaf.
* `AlgebraicGeometry.RingedSite.Hom.iteratedSliceLocalizedCommutes`: the comparison of the two
  composite direct images is compatible with the three structure maps.

## References

* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

/-- **Stacks 04IY on sheaves.** Restriction along `Over.iteratedSliceForward W` is left adjoint
to restriction along `Over.iteratedSliceBackward W`: the two functors of sites are the two
halves of the iterated-slice equivalence, and restriction along adjoint continuous functors is
adjoint.

This is the adjunction that gives the inverse image of the iterated-slice morphism of ringed
topoi a right adjoint which is again a *restriction*, so that a strict square of site functors
produces a square of direct images. -/
noncomputable def iteratedSliceBackwardAdjunction (Z : RingedSite.{u, u, u}) {U : Z.C}
    (W : Over U) :
    (Over.iteratedSliceForward W).sheafPushforwardContinuous (Type u)
        ((Z.J.over U).over W) (Z.J.over W.left) ⊣
      (Over.iteratedSliceBackward W).sheafPushforwardContinuous (Type u)
        (Z.J.over W.left) ((Z.J.over U).over W) :=
  Adjunction.sheafPushforwardContinuous
    (show Over.iteratedSliceForward W ⊣ Over.iteratedSliceBackward W from
      W.iteratedSliceEquiv.toAdjunction) ((Z.J.over U).over W) (Z.J.over W.left)

/-- The unit of `iteratedSliceBackwardAdjunction` is the identity: it is restriction of the
sheaf along the counit of the iterated-slice equivalence, which is an identity morphism. -/
theorem iteratedSliceBackwardAdjunction_unit_app (Z : RingedSite.{u, u, u}) {U : Z.C}
    (W : Over U) (G : Sheaf (Z.J.over W.left) (Type u)) :
    (Z.iteratedSliceBackwardAdjunction W).unit.app G = 𝟙 G :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ G.obj.map_id _))

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {V' V : Y.C} (b : V' ⟶ V)

/-- Continuity of the twice localized functor `Over.post (Over.post u)`, registered at the
spelling `(Over.post u).obj (Over.mk b)` of the slice object of `C/u(V)`: instance search does
not see through `Over.post` and `Over.mk` to the form Mathlib's instance is stated at. -/
instance isContinuous_overPost_overPost :
    (Over.post (X := Over.mk b) (Over.post (X := V) f.u)).IsContinuous
      ((Y.J.over V).over (Over.mk b))
      ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))) :=
  Functor.isContinuous_overPost_of_isContinuous (Y.J.over V) (X.J.over (f.u.obj V))
    (Over.post (X := V) f.u) (Over.mk b)

/-- Continuity of `Over.iteratedSliceBackward (V'/V)` with its source topology spelled at `V'`
rather than at `(V'/V).left`. -/
@[sga "3 IV 4.5.1" "partial"]
instance isContinuous_iteratedSliceBackward_overMk :
    (Over.iteratedSliceBackward (Over.mk b)).IsContinuous (Y.J.over V')
      ((Y.J.over V).over (Over.mk b)) :=
  inferInstanceAs ((Over.mk b).iteratedSliceBackward.IsContinuous
    (Y.J.over (Over.mk b).left) ((Y.J.over V).over (Over.mk b)))

/-- Continuity of `Over.iteratedSliceBackward (u(V')/u(V))` with its source topology spelled at
`u(V')` rather than at `((Over.post u).obj (V'/V)).left`. -/
@[sga "3 IV 4.5.1" "partial"]
instance isContinuous_iteratedSliceBackward_overPost :
    (Over.iteratedSliceBackward ((Over.post (X := V) f.u).obj (Over.mk b))).IsContinuous
      (X.J.over (f.u.obj V'))
      ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))) :=
  inferInstanceAs (((Over.post (X := V) f.u).obj (Over.mk b)).iteratedSliceBackward.IsContinuous
    (X.J.over ((Over.post (X := V) f.u).obj (Over.mk b)).left)
    ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))))

/-- **The square of site functors.** Embedding `D/V'` into the iterated slice `(D/V)/(V'/V)`
and then localizing `u` twice is localizing `u` at `V'` and then embedding into the iterated
slice `(C/u(V))/(u(V')/u(V))`.

The two functors are not equal on the nose: one of them sends an object `a : A ⟶ V'` to the
object of `C/u(V)` with structure morphism `u(a ≫ b)` and the other to the one with structure
morphism `u(a) ≫ u(b)`. They are canonically isomorphic, by the identity on underlying objects
of `C`. -/
def Hom.iteratedSlicePostIso :
    Over.iteratedSliceBackward (Over.mk b) ⋙
        Over.post (X := Over.mk b) (Over.post (X := V) f.u) ≅
      Over.post (X := V') f.u ⋙
        Over.iteratedSliceBackward ((Over.post (X := V) f.u).obj (Over.mk b)) :=
  NatIso.ofComponents
    (fun _ ↦ Over.isoMk (Over.isoMk (Iso.refl _)
        ((Category.id_comp _).trans (f.u.map_comp _ _).symm))
      (Over.OverMorphism.ext (Category.id_comp _)))
    (fun _ ↦ Over.OverMorphism.ext (Over.OverMorphism.ext
      ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- Continuity of the composite along the bottom of `Hom.iteratedSlicePostIso`, transported
from the composite along its top. -/
instance isContinuous_overPost_comp_iteratedSliceBackward :
    (Over.post (X := V') f.u ⋙
        Over.iteratedSliceBackward ((Over.post (X := V) f.u).obj (Over.mk b))).IsContinuous
      (Y.J.over V')
      ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))) :=
  haveI : (Over.iteratedSliceBackward (Over.mk b) ⋙
      Over.post (X := Over.mk b) (Over.post (X := V) f.u)).IsContinuous (Y.J.over V')
      ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))) :=
    Functor.isContinuous_comp (Over.iteratedSliceBackward (Over.mk b))
      (Over.post (X := Over.mk b) (Over.post (X := V) f.u)) (Y.J.over V')
      ((Y.J.over V).over (Over.mk b))
      ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b)))
  Functor.isContinuous_of_iso (f.iteratedSlicePostIso b) _ _

/-- **The square of direct images.** `Hom.iteratedSlicePostIso` read through restriction of
sheaves: the direct image of the twice localized morphism followed by restriction along
`Over.iteratedSliceBackward (V'/V)` is restriction along
`Over.iteratedSliceBackward (u(V')/u(V))` followed by the direct image of the morphism
localized at `V'`. -/
noncomputable def Hom.iteratedSliceRestrictionSquare :
    (Over.post (X := Over.mk b) (Over.post (X := V) f.u)).sheafPushforwardContinuous (Type u)
        ((Y.J.over V).over (Over.mk b))
        ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))) ⋙
      (Over.iteratedSliceBackward (Over.mk b)).sheafPushforwardContinuous (Type u)
        (Y.J.over V') ((Y.J.over V).over (Over.mk b)) ≅
    (Over.iteratedSliceBackward
          ((Over.post (X := V) f.u).obj (Over.mk b))).sheafPushforwardContinuous (Type u)
        (X.J.over (f.u.obj V'))
        ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))) ⋙
      (Over.post (X := V') f.u).sheafPushforwardContinuous (Type u)
        (Y.J.over V') (X.J.over (f.u.obj V')) :=
  Functor.sheafPushforwardContinuousComp' (f.iteratedSlicePostIso b) (Type u) (Y.J.over V')
    ((Y.J.over V).over (Over.mk b))
    ((X.J.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b)))

/-- At the structure sheaf the comparison of the two restriction composites is the identity:
its component there is the structure sheaf of `(C, O)` applied to an identity morphism of
`C`. -/
theorem Hom.iteratedSliceRestrictionSquare_hom_app_structureSheaf :
    (f.iteratedSliceRestrictionSquare b).hom.app
        (((X.over (f.u.obj V)).over
          ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
            ((X.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))).O) = 𝟙 _ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦
    (((X.over (f.u.obj V)).over
      ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
        ((X.over (f.u.obj V)).over
          ((Over.post (X := V) f.u).obj (Over.mk b))).O).obj.map_id _))

/-- The structure map of the twice localized morphism, restricted along
`Over.iteratedSliceBackward (V'/V)`, is the structure map of the morphism localized at `V'`:
both are `f♯` read on the slice `D/V'`, so the identity holds by definition. -/
theorem Hom.iteratedSliceBackward_map_forgetFSharp :
    ((Over.iteratedSliceBackward (Over.mk b)).sheafPushforwardContinuous (Type u)
          (Y.J.over V') ((Y.J.over V).over (Over.mk b))).map
        (AlgebraicGeometry.RingedToposHom.forgetFSharp
          ((f.localized V).localizedRingedToposHom (Over.mk b))) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp (f.localizedRingedToposHom V') :=
  rfl

/-- The comparison of the direct image of the iterated-slice morphism of ringed topoi with
restriction along `Over.iteratedSliceBackward`, on the source site. -/
noncomputable def iteratedSliceBackwardComparison (Z : RingedSite.{u, u, u}) {U : Z.C}
    (W : Over U) :
    (Z.iteratedSliceRingedToposHom W).toToposHom.pushforward ≅
      (Over.iteratedSliceBackward W).sheafPushforwardContinuous (Type u)
        (Z.J.over W.left) ((Z.J.over U).over W) :=
  Adjunction.rightAdjointUniq (Z.iteratedSliceMorphismOfTopoi W).adj
    (Z.iteratedSliceBackwardAdjunction W)

/-- The structure map of the iterated-slice morphism of ringed topoi, followed by the
comparison of its direct image with restriction along `Over.iteratedSliceBackward`, is the
identity: the structure map is the unit of one adjunction, uniqueness of right adjoints carries
it to the unit of the other, and that unit is the identity. -/
theorem forgetFSharp_iteratedSliceBackwardComparison (Z : RingedSite.{u, u, u}) {U : Z.C}
    (W : Over U) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp (Z.iteratedSliceRingedToposHom W) ≫
        (Z.iteratedSliceBackwardComparison W).hom.app
          (((Z.over U).over W).ringedTopos.forgetRing.obj ((Z.over U).over W).O) =
      𝟙 ((Z.over W.left).ringedTopos.forgetRing.obj (Z.over W.left).O) := by
  have hunit : AlgebraicGeometry.RingedToposHom.forgetFSharp (Z.iteratedSliceRingedToposHom W) =
      (Z.iteratedSliceMorphismOfTopoi W).adj.unit.app
        ((Z.over W.left).ringedTopos.forgetRing.obj (Z.over W.left).O) :=
    Z.forgetRing_iteratedSliceRingedToposHom_fSharp W
  rw [hunit]
  refine (Adjunction.unit_rightAdjointUniq_hom_app (Z.iteratedSliceMorphismOfTopoi W).adj
    (Z.iteratedSliceBackwardAdjunction W) _).trans ?_
  exact Z.iteratedSliceBackwardAdjunction_unit_app W _

/-- Read backwards: the structure map of the iterated-slice morphism of ringed topoi *is* the
inverse of the comparison of its direct image with restriction along
`Over.iteratedSliceBackward`, at the structure sheaf. -/
theorem forgetFSharp_eq_iteratedSliceBackwardComparison_inv (Z : RingedSite.{u, u, u}) {U : Z.C}
    (W : Over U) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp (Z.iteratedSliceRingedToposHom W) =
      (Z.iteratedSliceBackwardComparison W).inv.app
        (((Z.over U).over W).ringedTopos.forgetRing.obj ((Z.over U).over W).O) := by
  have h := congrArg (fun m ↦ m ≫ (Z.iteratedSliceBackwardComparison W).inv.app
      (((Z.over U).over W).ringedTopos.forgetRing.obj ((Z.over U).over W).O))
    (Z.forgetFSharp_iteratedSliceBackwardComparison W)
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using
    h.trans (Category.id_comp _)

/-- The comparison of the two composite direct images: the direct images of the two
iterated-slice morphisms are replaced by restriction along `Over.iteratedSliceBackward`, where
the square commutes by `Hom.iteratedSliceRestrictionSquare`. -/
noncomputable def Hom.iteratedSliceLocalizedComparison :
    (AlgebraicGeometry.RingedToposHom.comp
        (X := ((X.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
        (Y := ((Y.over V).over (Over.mk b)).ringedTopos)
        (Z := (Y.over V').ringedTopos)
        (Y.iteratedSliceRingedToposHom (Over.mk b))
        ((f.localized V).localizedRingedToposHom (Over.mk b))).toToposHom.pushforward ≅
      (AlgebraicGeometry.RingedToposHom.comp
        (X := ((X.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
        (Y := (X.over (f.u.obj V')).ringedTopos)
        (Z := (Y.over V').ringedTopos)
        (f.localizedRingedToposHom V')
        (X.iteratedSliceRingedToposHom
          ((Over.post (X := V) f.u).obj (Over.mk b)))).toToposHom.pushforward :=
  (Functor.isoWhiskerLeft
      ((f.localized V).localizedRingedToposHom (Over.mk b)).toToposHom.pushforward
      (Y.iteratedSliceBackwardComparison (Over.mk b))).trans
    ((f.iteratedSliceRestrictionSquare b).trans
      (Functor.isoWhiskerRight
        (X.iteratedSliceBackwardComparison ((Over.post (X := V) f.u).obj (Over.mk b)))
        (f.localizedRingedToposHom V').toToposHom.pushforward).symm)

/-- The comparison of the two composite direct images is compatible with the three structure
maps: both composite structure maps become the structure map of the morphism localized at `V'`
once the two iterated-slice structure maps are replaced, by
`forgetFSharp_iteratedSliceBackwardComparison`, with identities. -/
theorem Hom.iteratedSliceLocalizedCommutes :
    AlgebraicGeometry.RingedToposHom.forgetFSharp
          (AlgebraicGeometry.RingedToposHom.comp
            (X := ((X.over (f.u.obj V)).over
              ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
            (Y := ((Y.over V).over (Over.mk b)).ringedTopos)
            (Z := (Y.over V').ringedTopos)
            (Y.iteratedSliceRingedToposHom (Over.mk b))
            ((f.localized V).localizedRingedToposHom (Over.mk b))) ≫
        (f.iteratedSliceLocalizedComparison b).hom.app
          (((X.over (f.u.obj V)).over
            ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
              ((X.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))).O) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp
          (X := ((X.over (f.u.obj V)).over
            ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
          (Y := (X.over (f.u.obj V')).ringedTopos)
          (Z := (Y.over V').ringedTopos)
          (f.localizedRingedToposHom V')
          (X.iteratedSliceRingedToposHom ((Over.post (X := V) f.u).obj (Over.mk b)))) := by
  have hE : (f.iteratedSliceLocalizedComparison b).hom.app
        (((X.over (f.u.obj V)).over
          ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
            ((X.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))).O) =
      (Y.iteratedSliceBackwardComparison (Over.mk b)).hom.app
          (((f.localized V).localizedRingedToposHom
            (Over.mk b)).toToposHom.pushforward.obj
              (((X.over (f.u.obj V)).over
                ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
                  ((X.over (f.u.obj V)).over
                    ((Over.post (X := V) f.u).obj (Over.mk b))).O)) ≫
        (f.iteratedSliceRestrictionSquare b).hom.app
            (((X.over (f.u.obj V)).over
              ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
                ((X.over (f.u.obj V)).over
                  ((Over.post (X := V) f.u).obj (Over.mk b))).O) ≫
          (f.localizedRingedToposHom V').toToposHom.pushforward.map
            ((X.iteratedSliceBackwardComparison
                ((Over.post (X := V) f.u).obj (Over.mk b))).inv.app
              (((X.over (f.u.obj V)).over
                ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
                  ((X.over (f.u.obj V)).over
                    ((Over.post (X := V) f.u).obj (Over.mk b))).O)) :=
    rfl
  have h1 : AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp
          (X := ((X.over (f.u.obj V)).over
            ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
          (Y := ((Y.over V).over (Over.mk b)).ringedTopos)
          (Z := (Y.over V').ringedTopos)
          (Y.iteratedSliceRingedToposHom (Over.mk b))
          ((f.localized V).localizedRingedToposHom (Over.mk b))) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp
          (Y.iteratedSliceRingedToposHom (Over.mk b)) ≫
        (Y.iteratedSliceRingedToposHom (Over.mk b)).toToposHom.pushforward.map
          (AlgebraicGeometry.RingedToposHom.forgetFSharp
            ((f.localized V).localizedRingedToposHom (Over.mk b))) :=
    AlgebraicGeometry.RingedToposHom.forgetFSharp_comp
      (Y.iteratedSliceRingedToposHom (Over.mk b))
      ((f.localized V).localizedRingedToposHom (Over.mk b))
  have h2 : AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp
          (X := ((X.over (f.u.obj V)).over
            ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
          (Y := (X.over (f.u.obj V')).ringedTopos)
          (Z := (Y.over V').ringedTopos)
          (f.localizedRingedToposHom V')
          (X.iteratedSliceRingedToposHom ((Over.post (X := V) f.u).obj (Over.mk b)))) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp (f.localizedRingedToposHom V') ≫
        (f.localizedRingedToposHom V').toToposHom.pushforward.map
          (AlgebraicGeometry.RingedToposHom.forgetFSharp
            (X.iteratedSliceRingedToposHom
              ((Over.post (X := V) f.u).obj (Over.mk b)))) :=
    AlgebraicGeometry.RingedToposHom.forgetFSharp_comp (f.localizedRingedToposHom V')
      (X.iteratedSliceRingedToposHom ((Over.post (X := V) f.u).obj (Over.mk b)))
  refine Eq.trans ?_ h2.symm
  refine Eq.trans (congrArg (fun m ↦ m ≫ (f.iteratedSliceLocalizedComparison b).hom.app
    (((X.over (f.u.obj V)).over
      ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
        ((X.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))).O)) h1) ?_
  have hA : (AlgebraicGeometry.RingedToposHom.forgetFSharp
          (Y.iteratedSliceRingedToposHom (Over.mk b)) ≫
        (Y.iteratedSliceRingedToposHom (Over.mk b)).toToposHom.pushforward.map
          (AlgebraicGeometry.RingedToposHom.forgetFSharp
            ((f.localized V).localizedRingedToposHom (Over.mk b)))) ≫
      (Y.iteratedSliceBackwardComparison (Over.mk b)).hom.app
        (((f.localized V).localizedRingedToposHom (Over.mk b)).toToposHom.pushforward.obj
          (((X.over (f.u.obj V)).over
            ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
              ((X.over (f.u.obj V)).over
                ((Over.post (X := V) f.u).obj (Over.mk b))).O)) =
    AlgebraicGeometry.RingedToposHom.forgetFSharp (f.localizedRingedToposHom V') := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z ↦ AlgebraicGeometry.RingedToposHom.forgetFSharp
        (Y.iteratedSliceRingedToposHom (Over.mk b)) ≫ z)
      ((Y.iteratedSliceBackwardComparison (Over.mk b)).hom.naturality
        (AlgebraicGeometry.RingedToposHom.forgetFSharp
          ((f.localized V).localizedRingedToposHom (Over.mk b))))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z ↦ z ≫ _)
      (Y.forgetFSharp_iteratedSliceBackwardComparison (Over.mk b))) ?_
    exact (Category.id_comp _).trans (f.iteratedSliceBackward_map_forgetFSharp b)
  have hB : (f.iteratedSliceRestrictionSquare b).hom.app
          (((X.over (f.u.obj V)).over
            ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
              ((X.over (f.u.obj V)).over
                ((Over.post (X := V) f.u).obj (Over.mk b))).O) ≫
        (f.localizedRingedToposHom V').toToposHom.pushforward.map
          ((X.iteratedSliceBackwardComparison
              ((Over.post (X := V) f.u).obj (Over.mk b))).inv.app
            (((X.over (f.u.obj V)).over
              ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos.forgetRing.obj
                ((X.over (f.u.obj V)).over
                  ((Over.post (X := V) f.u).obj (Over.mk b))).O)) =
      (f.localizedRingedToposHom V').toToposHom.pushforward.map
        (AlgebraicGeometry.RingedToposHom.forgetFSharp
          (X.iteratedSliceRingedToposHom ((Over.post (X := V) f.u).obj (Over.mk b)))) := by
    refine Eq.trans (congrArg (fun z ↦ z ≫ _)
      (f.iteratedSliceRestrictionSquare_hom_app_structureSheaf b)) ?_
    refine Eq.trans (Category.id_comp _) ?_
    exact congrArg (f.localizedRingedToposHom V').toToposHom.pushforward.map
      (X.forgetFSharp_eq_iteratedSliceBackwardComparison_inv
        ((Over.post (X := V) f.u).obj (Over.mk b))).symm
  rw [hE]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫ _) hA) ?_
  exact congrArg (fun z ↦ _ ≫ z) hB

/-- **Stacks 04J0 at an iterated slice.** With `W = V'/V` and `W' = u'(W) = u(V')/u(V)`, the
square

```
  ((Sh(C/u(V))/W'), O_{W'}) --iterated slice--> (Sh(C/u(V')), O_{u(V')})
        | (f'_V)'_W                                   | f'_{V'}
  ((Sh(D/V)/W), O_W)        --iterated slice--> (Sh(D/V'), O'_{V'})
```

commutes, as a square of ringed topoi: localizing the localized morphism of Stacks 04J0 at `W`
is, read through the two iterated-slice identifications of Stacks 04IY, the morphism obtained
by localizing at `V'` directly.

The two direct images are identified by `Hom.iteratedSliceLocalizedComparison`, and
compatibility with the three structure maps is `Hom.iteratedSliceLocalizedCommutes`. -/
noncomputable def Hom.iteratedSliceLocalizedSquare :
    AlgebraicGeometry.RingedToposHom.TwoIso
      (A := ((X.over (f.u.obj V)).over ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
      (B := (Y.over V').ringedTopos)
      (AlgebraicGeometry.RingedToposHom.comp
        (X := ((X.over (f.u.obj V)).over
          ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
        (Y := ((Y.over V).over (Over.mk b)).ringedTopos)
        (Z := (Y.over V').ringedTopos)
        (Y.iteratedSliceRingedToposHom (Over.mk b))
        ((f.localized V).localizedRingedToposHom (Over.mk b)))
      (AlgebraicGeometry.RingedToposHom.comp
        (X := ((X.over (f.u.obj V)).over
          ((Over.post (X := V) f.u).obj (Over.mk b))).ringedTopos)
        (Y := (X.over (f.u.obj V')).ringedTopos)
        (Z := (Y.over V').ringedTopos)
        (f.localizedRingedToposHom V')
        (X.iteratedSliceRingedToposHom ((Over.post (X := V) f.u).obj (Over.mk b)))) where
  e := f.iteratedSliceLocalizedComparison b
  commutes := f.iteratedSliceLocalizedCommutes b

end AlgebraicGeometry.RingedSite

end
