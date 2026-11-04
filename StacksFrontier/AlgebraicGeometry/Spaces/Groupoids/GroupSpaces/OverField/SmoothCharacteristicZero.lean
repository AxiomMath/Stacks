module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.SmoothCharacteristicZero
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase

/-!
# Group algebraic spaces over a field of characteristic zero are smooth

Cartier's theorem, Stacks 047N, says that a locally algebraic group scheme `G` over a field `k`
of characteristic `0` is smooth over `k`. This file carries it from the formalism of group
schemes, a scheme `G` with a structure morphism `f : G ⟶ Spec k` and a group object structure on
`Over.mk f`, to the formalism of group algebraic spaces, a group object of the slice of presheaves
on the big fppf site of `Spec k` over the final algebraic space whose underlying presheaf is an
algebraic space. As a consequence, the quotient stack `[X/G]` of an action of such a group on an
algebraic space over `Spec k` is an algebraic stack.

## Main definitions

* `AlgebraicGeometry.Space.grpObjOfIsoYoneda`: a group object over the final algebraic space
  whose underlying presheaf is represented by an object `T` of the site makes `T`, read as a
  scheme over the base, a group scheme.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda`: over the final
  algebraic space, the group algebraic space `G_B` attached to a group scheme `G` of the site by
  Stacks 043I is represented by `G` itself, so it is a scheme
  (`AlgebraicGeometry.Space.GroupAlgebraicSpace.isRepresentable_ofGroupSchemeInSite`) and an
  algebraic space
  (`AlgebraicGeometry.Space.GroupAlgebraicSpace.isAlgebraicSpace_ofGroupSchemeInSite`).

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_hom_iff_of_iso_yoneda`: a property of
  morphisms of schemes, étale local on the source and target, holds for the structure morphism
  of a presheaf over the final algebraic space represented by `T` exactly when it holds for the
  structure morphism of `T` as a scheme over the base. In particular
  `AlgebraicGeometry.Space.isSmooth_hom_iff_smooth_of_iso_yoneda` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_hom_iff_of_iso_yoneda`.
* `AlgebraicGeometry.Space.isSmooth_hom_of_charZero_of_iso_yoneda` and
  `AlgebraicGeometry.Space.isSmooth_hom_of_charZero`: **Stacks 047N** for group objects over
  the final algebraic space over `Spec k`, whose underlying presheaf is a scheme locally of
  finite type over `k`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.isSmooth_of_charZero`: **Stacks 047N** for a
  group algebraic space over `Spec k` which is a scheme locally of finite type over `k`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.isSmooth_ofGroupSchemeInSite_of_charZero`: the
  group algebraic space attached to a locally algebraic group scheme over `k` of the site, in the
  formalism of Stacks 047N, is smooth over `Spec k`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfAction_of_charZero`: the quotient
  stack `[X/G]` of an action of a group algebraic space `G` over `Spec k`, `k` of characteristic
  `0`, which is a scheme locally of finite type over `k`, on an algebraic space `X` over `Spec k`
  is an algebraic stack.

## Implementation notes

The final algebraic space over `S` is the presheaf represented by the base object of the site,
so the slice over it is equivalent to the category of presheaves
(`CategoryTheory.Over.equivalenceOfIsTerminal`), and the Yoneda embedding followed by the
inverse of that equivalence is a fully faithful functor from the big fppf site of `S` to the
slice which preserves finite products. A group object of the slice isomorphic to the image of
`T` therefore pulls back to a group object structure on `T`
(`CategoryTheory.Functor.FullyFaithful.grpObj`), which the inclusion of the site into schemes
over `S`, a functor preserving finite limits, carries to a group scheme over `S`
(`CategoryTheory.Functor.grpObjObj`). Only the existence of a group structure on the scheme is
used by Stacks 047N, so no comparison of the group laws is needed.

The structure morphism of the presheaf, precomposed with the representing isomorphism, is the
image under the Yoneda embedding of the structure morphism of `T` to the base object, the target
being final. A property étale local on the source and target is insensitive to the isomorphism
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iso_comp_iff`) and holds for the image of a
morphism of the site exactly when it holds for the underlying morphism of schemes
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`).

## References

* [Stacks Project, Tag 047N](https://stacks.math.columbia.edu/tag/047N)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe w u

namespace AlgebraicGeometry.Space

section Representable

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- The final algebraic space over `S` is a final presheaf on the big fppf site of `S`. -/
noncomputable def terminalSpace_obj_isTerminal :
    IsTerminal (terminalSpace C S hS).obj :=
  baseTerminal_yonedaIsTerminal C S hS

/-- A presheaf over the final algebraic space represented by `T`: its structure morphism,
precomposed with the representing isomorphism, is the image under the Yoneda embedding of the
structure morphism of `T`, the target being final. -/
theorem iso_hom_comp_hom_eq_yoneda_map (G : Over (terminalSpace C S hS).obj)
    (T : BigFppfOver C S hS) (e : yoneda.obj T ≅ G.left) :
    e.hom ≫ G.hom = yoneda.map (toBaseTerminal C S hS T) :=
  terminalSpace_obj_isTerminal.hom_ext _ _

/-- A property of morphisms of schemes which is étale local on the source and target holds, in
the sense of Stacks 03MJ, for the structure morphism of a presheaf over the final algebraic
space over `S` represented by an object `T` of the site exactly when it holds for the structure
morphism of `T`, read as a scheme over `S`. -/
theorem holdsOnEveryEtaleChart_hom_iff_of_iso_yoneda {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) (G : Over (terminalSpace C S hS).obj)
    (T : BigFppfOver C S hS) (e : yoneda.obj T ≅ G.left) :
    HoldsOnEveryEtaleChart C S hS P G.hom ↔ P ((toSchemeOver C S hS).obj T).hom := by
  rw [← holdsOnEveryEtaleChart_iso_comp_iff C S hS P e.hom G.hom,
    iso_hom_comp_hom_eq_yoneda_map G T e]
  exact holdsOnEveryEtaleChart_yoneda_map_iff C S hS hP (toBaseTerminal C S hS T)

/-- The structure morphism of a presheaf over the final algebraic space over `S` represented by
an object `T` of the site is a smooth morphism of algebraic spaces exactly when `T` is smooth
over `S`. -/
theorem isSmooth_hom_iff_smooth_of_iso_yoneda (G : Over (terminalSpace C S hS).obj)
    (T : BigFppfOver C S hS) (e : yoneda.obj T ≅ G.left) :
    IsSmooth C S hS G.hom ↔ Smooth ((toSchemeOver C S hS).obj T).hom :=
  holdsOnEveryEtaleChart_hom_iff_of_iso_yoneda Smooth.isEtaleLocalOnSourceAndTarget G T e

/-- The structure morphism of a presheaf over the final algebraic space over `S` represented by
an object `T` of the site is locally of finite type as a morphism of algebraic spaces exactly
when `T` is locally of finite type over `S`. -/
theorem isLocallyOfFiniteType_hom_iff_of_iso_yoneda (G : Over (terminalSpace C S hS).obj)
    (T : BigFppfOver C S hS) (e : yoneda.obj T ≅ G.left) :
    IsLocallyOfFiniteType C S hS G.hom ↔
      LocallyOfFiniteType ((toSchemeOver C S hS).obj T).hom :=
  holdsOnEveryEtaleChart_hom_iff_of_iso_yoneda
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget G T e

/-- The Yoneda embedding of the big fppf site of `S`, landing in the slice over the final
algebraic space. -/
noncomputable abbrev yonedaToOverTerminalSpace :
    BigFppfOver C S hS ⥤ Over (terminalSpace C S hS).obj :=
  yoneda ⋙ (Over.equivalenceOfIsTerminal terminalSpace_obj_isTerminal).inverse

/-- The Yoneda embedding of the big fppf site of `S` into the slice over the final algebraic
space is fully faithful. -/
noncomputable def yonedaToOverTerminalSpaceFullyFaithful :
    (yonedaToOverTerminalSpace (C := C) (S := S) (hS := hS)).FullyFaithful :=
  Yoneda.fullyFaithful.comp
    (Over.equivalenceOfIsTerminal terminalSpace_obj_isTerminal).fullyFaithfulInverse

/-- **A group object over the final algebraic space represented by an object of the site is a
group scheme.** If the underlying presheaf of a group object `G` of the slice over the final
algebraic space over `S` is represented by an object `T` of the big fppf site, then `T`, read
as a scheme over `S`, carries a group object structure in schemes over `S`. -/
@[instance_reducible]
noncomputable def grpObjOfIsoYoneda (G : Over (terminalSpace C S hS).obj) [GrpObj G]
    (T : BigFppfOver C S hS) (e : yoneda.obj T ≅ G.left) :
    GrpObj ((toSchemeOver C S hS).obj T) :=
  letI : CartesianMonoidalCategory (BigFppfOver C S hS) := Over.cartesianMonoidalCategory _
  letI : (yonedaToOverTerminalSpace (C := C) (S := S) (hS := hS)).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  letI : GrpObj (yonedaToOverTerminalSpace.obj T) :=
    GrpObj.ofIso (Over.isoMk e (terminalSpace_obj_isTerminal.hom_ext _ _)).symm
  letI : GrpObj T := yonedaToOverTerminalSpaceFullyFaithful.grpObj T
  letI : PreservesFiniteLimits C.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks C.inclusion
  letI : PreservesFiniteLimits (toSchemeOver C S hS) :=
    PreservesFiniteLimits.overPost (F := C.inclusion) (X := C.obj hS)
  letI : (toSchemeOver C S hS).Monoidal := Functor.Monoidal.ofChosenFiniteProducts _
  Functor.grpObjObj

end Representable

section CharacteristicZero

variable {k : Type u} [Field k] [CharZero k] {C : BigFppfSite.{u}}
  {hk : C.Contains (Spec (.of k))}

/-- **Stacks 047N** for a group object over the final algebraic space over `Spec k`, `k` of
characteristic `0`, whose underlying presheaf is represented by an object `T` of the site
locally of finite type over `k`: its structure morphism is smooth. -/
theorem isSmooth_hom_of_charZero_of_iso_yoneda (G : Over (terminalSpace C (Spec (.of k)) hk).obj)
    [GrpObj G] (T : BigFppfOver C (Spec (.of k)) hk) (e : yoneda.obj T ≅ G.left)
    (hT : LocallyOfFiniteType ((toSchemeOver C (Spec (.of k)) hk).obj T).hom) :
    IsSmooth C (Spec (.of k)) hk G.hom := by
  let : GrpObj (Over.mk ((toSchemeOver C (Spec (.of k)) hk).obj T).hom) :=
    grpObjOfIsoYoneda G T e
  exact (isSmooth_hom_iff_smooth_of_iso_yoneda G T e).2
    (smooth_of_groupScheme_of_charZero k _ _)

/-- **Stacks 047N** for a group object over the final algebraic space over `Spec k`, `k` of
characteristic `0`, whose underlying presheaf is a scheme and whose structure morphism is
locally of finite type: its structure morphism is smooth. -/
@[ega "IV 15.6.10" "special case",
  sga "3 VIA 1.1" "special case",
  sga "3 VIA 6.9" "special case",
  sga "3 VIB 1.6.1" "special case",
  sga "3 XV 6.5" "partial",
  sga "3 XVII 5.5" "partial"]
theorem isSmooth_hom_of_charZero (G : Over (terminalSpace C (Spec (.of k)) hk).obj)
    [GrpObj G] [G.left.IsRepresentable]
    (hlft : IsLocallyOfFiniteType C (Spec (.of k)) hk G.hom) :
    IsSmooth C (Spec (.of k)) hk G.hom :=
  isSmooth_hom_of_charZero_of_iso_yoneda G _ G.left.reprW
    ((isLocallyOfFiniteType_hom_iff_of_iso_yoneda G _ G.left.reprW).1 hlft)

/-- **Stacks 047N.** Let `k` be a field of characteristic `0` and let `G` be a group algebraic
space over `Spec k` which is a scheme locally of finite type over `k`. Then the structure
morphism `G ⟶ Spec k` is smooth.

The group scheme structure on the representing scheme is obtained from the group structure of
`G` by `AlgebraicGeometry.Space.grpObjOfIsoYoneda`, and the smoothness of the scheme is
`AlgebraicGeometry.smooth_of_groupScheme_of_charZero`. -/
@[stacks 047N "group algebraic spaces over `Spec k` which are schemes locally of finite type \
over `k`",
  sga "3 VIA 1.1" "special case",
  sga "3 VIA 6.9" "special case",
  sga "3 VIB 1.6.1" "special case",
  sga "3 VIIA 8.4" "more general",
  sga "3 XV 6.5" "special case",
  sga "3 XVII 5.5" "more general"]
theorem GroupAlgebraicSpace.isSmooth_of_charZero
    (G : GroupAlgebraicSpace C (Spec (.of k)) hk (terminalSpace C (Spec (.of k)) hk).obj
      (terminalSpace C (Spec (.of k)) hk).property)
    [G.obj.X.left.IsRepresentable]
    (hlft : IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) :
    IsSmooth C (Spec (.of k)) hk G.obj.X.hom :=
  isSmooth_hom_of_charZero G.obj.X hlft

end CharacteristicZero

section GroupSchemeInSite

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- The product of the final algebraic space with a presheaf represented by an object of the site
is represented by that object. -/
noncomputable def terminalSpaceProdIsoYoneda {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {G : BigFppfOver C S hS} (r : F.RepresentableBy G) :
    yoneda.obj G ≅ (terminalSpace C S hS).obj ⨯ F where
  hom := prod.lift (terminalSpace_obj_isTerminal.from _) r.toIso.hom
  inv := prod.snd ≫ r.toIso.inv
  hom_inv_id := by rw [prod.lift_snd_assoc, Iso.hom_inv_id]
  inv_hom_id := prod.hom_ext (terminalSpace_obj_isTerminal.hom_ext _ _) (by simp)

/-- **The group algebraic space attached to a group scheme of the site is represented by it.**
Over the final algebraic space, the underlying presheaf `B ⨯ G` of the group algebraic space
`G_B` of Stacks 043I is isomorphic to the presheaf represented by `G`, the first factor being
final. -/
noncomputable def GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda (G : BigFppfOver C S hS)
    (hG : GrpObj ((toSchemeOver C S hS).obj G)) :
    yoneda.obj G ≅ (GroupAlgebraicSpace.ofGroupSchemeInSite C S hS
      (terminalSpace C S hS).obj (terminalSpace C S hS).property G hG).obj.X.left :=
  terminalSpaceProdIsoYoneda (pointsOnSiteRepresentableBy C S hS G hG)

/-- Over the final algebraic space, the group algebraic space `G_B` of Stacks 043I attached to a
group scheme `G` of the site is a scheme: its underlying presheaf is represented by `G`. -/
theorem GroupAlgebraicSpace.isRepresentable_ofGroupSchemeInSite (G : BigFppfOver C S hS)
    (hG : GrpObj ((toSchemeOver C S hS).obj G)) :
    (GroupAlgebraicSpace.ofGroupSchemeInSite C S hS
      (terminalSpace C S hS).obj (terminalSpace C S hS).property G hG).obj.X.left.IsRepresentable :=
  Functor.IsRepresentable.mk' (GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda G hG)

/-- The underlying presheaf of the group algebraic space `G_B` of Stacks 043I attached to a
group scheme `G` of the site, over the final algebraic space, is an algebraic space. -/
theorem GroupAlgebraicSpace.isAlgebraicSpace_ofGroupSchemeInSite (G : BigFppfOver C S hS)
    (hG : GrpObj ((toSchemeOver C S hS).obj G)) :
    IsAlgebraicSpace C S hS (GroupAlgebraicSpace.ofGroupSchemeInSite C S hS
      (terminalSpace C S hS).obj (terminalSpace C S hS).property G hG).obj.X.left :=
  isAlgebraicSpace_of_iso C S hS (GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda G hG)
    (isAlgebraicSpace_yoneda C S hS G)

variable {k : Type u} [Field k] [CharZero k] {hk : C.Contains (Spec (.of k))}

/-- **Stacks 047N** in the formalism of group schemes, read on group algebraic spaces. Let `k`
be a field of characteristic `0` and let `G` be a locally algebraic group scheme over `k` lying in
the big fppf site, that is, an object of the site whose structure morphism to `Spec k` is locally
of finite type, with a group object structure in schemes over `Spec k`. Then the group algebraic
space over `Spec k` attached to `G` by Stacks 043I is smooth over `Spec k`. -/
@[sga "3 VIA 1.1" "special case",
  sga "3 VIB 1.6.1" "special case",
  sga "3 VIIA 8.4" "more general",
  sga "3 XV 6.5" "special case",
  sga "3 XVII 5.5" "partial"]
theorem GroupAlgebraicSpace.isSmooth_ofGroupSchemeInSite_of_charZero
    (G : BigFppfOver C (Spec (.of k)) hk) (hG : GrpObj ((toSchemeOver C (Spec (.of k)) hk).obj G))
    (hlft : LocallyOfFiniteType ((toSchemeOver C (Spec (.of k)) hk).obj G).hom) :
    IsSmooth C (Spec (.of k)) hk
      (GroupAlgebraicSpace.ofGroupSchemeInSite C (Spec (.of k)) hk
        (terminalSpace C (Spec (.of k)) hk).obj (terminalSpace C (Spec (.of k)) hk).property
        G hG).obj.X.hom :=
  isSmooth_hom_of_charZero_of_iso_yoneda _ G (GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda G hG)
    hlft

end GroupSchemeInSite

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {k : Type u} [Field k] [CharZero k] {C : BigFppfSite.{u}}
  {hk : C.Contains (Spec (.of k))}

/-- **The quotient stack of a group scheme over a field of characteristic `0` is algebraic.**
Let `k` be a field of characteristic `0`, let `G` be a group algebraic space over `Spec k`
which is a scheme locally of finite type over `k`, acting on an algebraic space `X` over
`Spec k`. Then the quotient stack `[X/G]` of Stacks 044Q part (2) is an algebraic stack.

`G` is smooth over `Spec k` by Stacks 047N
(`AlgebraicGeometry.Space.isSmooth_hom_of_charZero`), so Stacks 04TK applies to the action
groupoid (`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfAction`), with the
bootstrap theorem Stacks 04S6 supplied by `AlgebraicGeometry.Stack.bootstrap04S6`. -/
theorem isAlgebraicStack_quotientStackOfAction_of_charZero
    (G X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C (Spec (.of k)) hk G.left)
    (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left) [G.left.IsRepresentable]
    (hlft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.hom) :
    IsAlgebraicStack.{u, w} C (Spec (.of k)) hk
      (quotientStackOfAction (Space.terminalSpace C (Spec (.of k)) hk) G X hG hX) :=
  isAlgebraicStack_quotientStackOfAction _ G X hG hX (Space.isSmooth_hom_of_charZero G hlft)

end AlgebraicGeometry.Stack

end
