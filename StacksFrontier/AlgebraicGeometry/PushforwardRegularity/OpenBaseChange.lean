module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange

/-!
# Base change along an open immersion of the target, for an arbitrary square

For a morphism of schemes `f : X ⟶ S` and an open `U` of `S`,
`StacksFrontier/AlgebraicGeometry/AffineBaseChange/BaseChange.lean` proves that the canonical
base-change morphism of the *restriction* square
```
f ⁻¹ᵁ U --ι--> X
|f ∣_ U        |f
U       --ι--> S
```
is an isomorphism. This file does two things. First it observes that the proof uses the
cartesianness of the square only through the comparison isomorphism
`f _* (-) ∣_ g ≅ f' _* ((-) ∣_ g')`, so the whole argument goes through for an arbitrary
commutative square whose two horizontal arrows are open immersions once such a comparison is
supplied. Second it supplies that comparison for the *pullback* square
```
X ×_S U --fst--> X
|snd             |f
U       --ι-->   S
```
by transporting the restriction square's comparison along
`AlgebraicGeometry.pullbackRestrictIsoRestrict`, and concludes that the base-change morphism of
`IsPullback.of_hasPullback f U.ι` is an isomorphism at every module.

That is the shape of base change that the stalk comparison map
`(f _* F)_s ⟶ ((snd) _* (fst)^* F)_t` of [Stacks, Tag 0EY0] is built from, and
`isIso_openStalkComparison` records that this comparison map is an isomorphism.

## Main definitions

* `pushforwardEquivalence`: the direct image along an isomorphism of schemes, as an
  equivalence of module categories.
* `restrictPushforwardIsoId`: restricting along an isomorphism of schemes and then pushing
  forward again is the identity.
* `RestrictPushforwardIso`: the comparison isomorphism through which cartesianness enters.
* `openMate`: the base-change morphism formed with the restriction adjunctions rather than the
  pullback--pushforward adjunctions.
* `compIsoOfIso`: precomposing both horizontal arrows of the square with an isomorphism does
  not change `(-) ∣_ g' ⋙ f' _*`.
* `restrictPushforwardIsoPullback`: the comparison isomorphism for the pullback square.
* `openStalkComparison`: the comparison map on stalks.

## Main results

* `isIso_baseChangeNatTrans_app`: base change along an open immersion of the target, for an
  arbitrary square with a comparison isomorphism.
* `isIso_baseChangeNatTrans_pullback`: the same for the square `X ×_S U ⟶ U`.
* `isIso_openStalkComparison`: the stalk comparison map is an isomorphism.
* `quasiCompact_pullback_snd`, `quasiSeparated_pullback_snd`: the restriction of a
  quasi-compact (quasi-separated) morphism over an open of the target is again quasi-compact
  (quasi-separated).

## Implementation notes

`RestrictPushforwardIso` is an `abbrev` for an `Iso` of functors, taken as an explicit
argument rather than as a `variable`, because the morphism `f'` it mentions occurs in the
proofs of `isIso_unit_restrict` and nowhere in their statements, so `variable` would not bind
it.

The universe is the single scheme universe `u` throughout; nothing here is universe
polymorphic beyond what `AlgebraicGeometry.Scheme.Modules` already is.

`pushforwardEquivalence` is built from `pushforwardComp`, `pushforwardCongr` and
`pushforwardId` rather than from a general "pseudofunctors send isomorphisms to equivalences"
lemma, which Mathlib's `Scheme.Modules.pseudofunctor` does not come with.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.OpenBaseChange

/-! ### Direct image along an isomorphism of schemes -/

/-- The direct image along an isomorphism of schemes is an equivalence of module categories. -/
noncomputable def pushforwardEquivalence {Y Z : Scheme.{u}} (e : Y ≅ Z) : Y.Modules ≌ Z.Modules :=
  .mk (Scheme.Modules.pushforward e.hom) (Scheme.Modules.pushforward e.inv)
    (Scheme.Modules.pushforwardComp e.hom e.inv ≪≫
      Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫ Scheme.Modules.pushforwardId Y).symm
    (Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
      Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Z)

/-- Restriction along an isomorphism of schemes is isomorphic to the direct image along the
inverse isomorphism. -/
noncomputable def restrictFunctorIsoPushforwardInv {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    Scheme.Modules.restrictFunctor e.hom ≅ Scheme.Modules.pushforward e.inv :=
  Adjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction e.hom)
    (pushforwardEquivalence e).symm.toAdjunction

/-- Restricting along an isomorphism of schemes and then pushing forward again is the
identity. -/
noncomputable def restrictPushforwardIsoId {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    Scheme.Modules.restrictFunctor e.hom ⋙ Scheme.Modules.pushforward e.hom ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (restrictFunctorIsoPushforwardInv e)
      (Scheme.Modules.pushforward e.hom) ≪≫
    (pushforwardEquivalence e).counitIso

/-! ### Base change for a square whose two horizontal arrows are open immersions -/

section OpenSquare

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  [IsOpenImmersion g] [IsOpenImmersion g']

/-- The base-change morphism of a commutative square whose horizontal arrows are open
immersions, formed with respect to the restriction adjunctions instead of the
pullback--pushforward adjunctions. -/
noncomputable def openMate (w : g' ≫ f = f' ≫ g) :
    TwoSquare (Scheme.Modules.pushforward f) (Scheme.Modules.restrictFunctor g')
      (Scheme.Modules.restrictFunctor g) (Scheme.Modules.pushforward f') :=
  (mateEquiv (Scheme.Modules.restrictAdjunction g')
      (Scheme.Modules.restrictAdjunction g)).symm
    (AffinePushforward.pushforwardSquareIso w).hom

/-- The canonical base-change morphism is `openMate` whiskered with the two comparisons of
restriction and inverse image. -/
lemma baseChangeNatTrans_eq_openMate (w : g' ≫ f = f' ≫ g) :
    AffinePushforward.baseChangeNatTrans w =
      TwoSquare.whiskerLeft (TwoSquare.whiskerRight (openMate w)
          (Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g)
            (Scheme.Modules.restrictAdjunction g)).hom)
        (Adjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction g')
          (Scheme.Modules.pullbackPushforwardAdjunction g')).hom := by
  have e1 := Stacks.CategoryTheory.mateEquiv_symm_congr_left
    (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.restrictAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom)
  have e2 := Stacks.CategoryTheory.mateEquiv_symm_congr_right
    (Scheme.Modules.restrictAdjunction g')
    (Scheme.Modules.restrictAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (TwoSquare.mk _ _ _ _ (AffinePushforward.pushforwardSquareIso w).hom)
  rw [e2] at e1
  exact e1

/-- The three factors of `openMate`. -/
lemma openMate_app (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (openMate w).app M =
      (Scheme.Modules.restrictFunctor g).map ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictAdjunction g').unit.app M)) ≫
        (Scheme.Modules.restrictFunctor g).map
          ((AffinePushforward.pushforwardSquareIso w).hom.app
            ((Scheme.Modules.restrictFunctor g').obj M)) ≫
        (Scheme.Modules.restrictAdjunction g).counit.app
          ((Scheme.Modules.pushforward f').obj
            ((Scheme.Modules.restrictFunctor g').obj M)) := by
  simp [openMate, mateEquiv]

/-- The comparison isomorphism the cartesianness of the square is used through: restricting
the direct image along `g` agrees with the direct image along `f'` of the restriction along
`g'`. -/
abbrev RestrictPushforwardIso (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [IsOpenImmersion g] [IsOpenImmersion g'] : Type _ :=
  Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor g ≅
    Scheme.Modules.restrictFunctor g' ⋙ Scheme.Modules.pushforward f'

/-- The unit of the restriction adjunction at `X'` becomes invertible after applying `f _*` and
restricting along `g`.  Only the naturality of `κ` is used. -/
theorem isIso_unit_restrict (κ : RestrictPushforwardIso g' f' f g) (M : X.Modules) :
    IsIso ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor g).map
      ((Scheme.Modules.restrictAdjunction g').unit.app M)) := by
  have ht := (Scheme.Modules.restrictAdjunction g').left_triangle_components M
  have h0 : IsIso ((Scheme.Modules.restrictFunctor g').map
      ((Scheme.Modules.restrictAdjunction g').unit.app M) ≫
      (Scheme.Modules.restrictAdjunction g').counit.app
        ((Scheme.Modules.restrictFunctor g').obj M)) := by
    rw [ht]
    infer_instance
  have h1 : IsIso ((Scheme.Modules.restrictFunctor g').map
      ((Scheme.Modules.restrictAdjunction g').unit.app M)) :=
    IsIso.of_isIso_comp_right _
      ((Scheme.Modules.restrictAdjunction g').counit.app
        ((Scheme.Modules.restrictFunctor g').obj M))
  have h2 : IsIso ((Scheme.Modules.restrictFunctor g' ⋙
      Scheme.Modules.pushforward f').map
      ((Scheme.Modules.restrictAdjunction g').unit.app M)) :=
    Functor.map_isIso (Scheme.Modules.pushforward f') _
  have hnat := κ.hom.naturality ((Scheme.Modules.restrictAdjunction g').unit.app M)
  have h3 : IsIso ((Scheme.Modules.pushforward f ⋙
      Scheme.Modules.restrictFunctor g).map
      ((Scheme.Modules.restrictAdjunction g').unit.app M) ≫ κ.hom.app _) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (κ.hom.app _)

/-- `openMate` is invertible at every module. -/
theorem isIso_openMate_app (κ : RestrictPushforwardIso g' f' f g)
    (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    IsIso ((openMate w).app M) := by
  rw [openMate_app]
  have : IsIso ((Scheme.Modules.restrictFunctor g).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction g').unit.app M))) := isIso_unit_restrict κ M
  infer_instance

/-- The three factors of the canonical base-change morphism. -/
lemma baseChangeNatTrans_app (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (AffinePushforward.baseChangeNatTrans w).app M =
      (Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g)
          (Scheme.Modules.restrictAdjunction g)).hom.app
          ((Scheme.Modules.pushforward f).obj M) ≫
        (openMate w).app M ≫
        (Scheme.Modules.pushforward f').map
          ((Adjunction.leftAdjointUniq (Scheme.Modules.restrictAdjunction g')
            (Scheme.Modules.pullbackPushforwardAdjunction g')).hom.app M) := by
  rw [show (AffinePushforward.baseChangeNatTrans w) = _ from baseChangeNatTrans_eq_openMate w]
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

/-- **Base change along an open immersion of the target.** For a commutative square of schemes
whose two horizontal arrows are open immersions, and which is cartesian to the extent of
carrying a natural isomorphism `f _* (-) ∣_ g ≅ (f' _*) ((-) ∣_ g')`, the canonical
base-change morphism is an isomorphism at every module. -/
theorem isIso_baseChangeNatTrans_app (κ : RestrictPushforwardIso g' f' f g)
    (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    IsIso ((AffinePushforward.baseChangeNatTrans w).app M) := by
  rw [baseChangeNatTrans_app w M]
  have := isIso_openMate_app κ w M
  infer_instance

/-- Precomposing the two horizontal arrows of the square with an isomorphism does not change
the functor `(-) ∣_ g' ⋙ f' _*`. -/
noncomputable def compIsoOfIso {X'' : Scheme.{u}} (e : X'' ≅ X') (g' : X' ⟶ X) (f' : X' ⟶ S')
    [IsOpenImmersion g'] :
    Scheme.Modules.restrictFunctor (e.hom ≫ g') ⋙
        Scheme.Modules.pushforward (e.hom ≫ f') ≅
      Scheme.Modules.restrictFunctor g' ⋙ Scheme.Modules.pushforward f' :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorComp e.hom g')
      (Scheme.Modules.pushforward (e.hom ≫ f')) ≪≫
    Functor.isoWhiskerLeft
      (Scheme.Modules.restrictFunctor g' ⋙ Scheme.Modules.restrictFunctor e.hom)
      (Scheme.Modules.pushforwardComp e.hom f').symm ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.restrictFunctor g')
      (Functor.isoWhiskerRight (restrictPushforwardIsoId e) (Scheme.Modules.pushforward f'))

end OpenSquare

/-! ### The square cutting out the preimage of an open of the target -/

section Pullback

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)

/-- The comparison isomorphism for the cartesian square `pullback f U.ι`, obtained from the one
for the restriction square by precomposing with `pullbackRestrictIsoRestrict`. -/
noncomputable def restrictPushforwardIsoPullback :
    RestrictPushforwardIso (pullback.fst f U.ι) (pullback.snd f U.ι) f U.ι :=
  AffinePushforward.restrictPushforwardIso f U ≪≫
    (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorCongr
        (pullbackRestrictIsoRestrict_hom_ι f U).symm)
          (Scheme.Modules.pushforward (pullback.snd f U.ι)) ≪≫
      Functor.isoWhiskerLeft
        (Scheme.Modules.restrictFunctor
          ((pullbackRestrictIsoRestrict f U).hom ≫ (f ⁻¹ᵁ U).ι))
        (Scheme.Modules.pushforwardCongr
          (pullbackRestrictIsoRestrict_hom_morphismRestrict f U).symm) ≪≫
      compIsoOfIso (pullbackRestrictIsoRestrict f U) (f ⁻¹ᵁ U).ι (f ∣_ U)).symm

/-- **The base-change morphism of the square `X ×_S U ⟶ U` is an isomorphism.** This is the
form of base change along an open immersion of the target that the cartesian square
`IsPullback.of_hasPullback f U.ι` needs. -/
theorem isIso_baseChangeNatTrans_pullback (M : X.Modules) :
    IsIso ((AffinePushforward.baseChangeNatTrans
      (IsPullback.of_hasPullback f U.ι).w).app M) :=
  isIso_baseChangeNatTrans_app (restrictPushforwardIsoPullback f U) _ M

/-- The restriction over `U` of a quasi-compact morphism is quasi-compact. -/
instance quasiCompact_pullback_snd [QuasiCompact f] : QuasiCompact (pullback.snd f U.ι) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback f U.ι) inferInstance

/-- The restriction over `U` of a quasi-separated morphism is quasi-separated. -/
instance quasiSeparated_pullback_snd [QuasiSeparated f] : QuasiSeparated (pullback.snd f U.ι) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
    (IsPullback.of_hasPullback f U.ι) inferInstance

/-- An isomorphism of `𝒪ₓ`-modules induces an isomorphism of the underlying abelian
presheaves. -/
lemma isIso_mapPresheaf {Y : Scheme.{u}} {M N : Y.Modules} (h : M ⟶ N) [IsIso h] :
    IsIso h.mapPresheaf :=
  Functor.map_isIso (Scheme.Modules.toPresheaf Y) h

variable (F : X.Modules) (t : U.toScheme)

/-- The comparison map from the stalk of `f _* F` at a point of `U` to the stalk at that point
of the direct image along `X ×_S U ⟶ U` of the inverse image of `F`.  It is the composition of
the identification of the stalk of a restriction, the comparison of restriction with inverse
image, and the canonical base-change morphism. -/
noncomputable def openStalkComparison :
    TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pushforward f).obj F).val.presheaf (U.ι.base t) ⟶
      TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pushforward (pullback.snd f U.ι)).obj
          ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj F)).val.presheaf t :=
  (Scheme.Modules.restrictStalkNatIso U.ι t).inv.app ((Scheme.Modules.pushforward f).obj F) ≫
    (TopCat.Presheaf.stalkFunctor Ab.{u} t).map
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
        ((Scheme.Modules.pushforward f).obj F)).mapPresheaf ≫
    (TopCat.Presheaf.stalkFunctor Ab.{u} t).map
      ((AffinePushforward.baseChangeNatTrans
        (IsPullback.of_hasPullback f U.ι).w).app F).mapPresheaf

/-- **The comparison map on stalks is an isomorphism.** All three of its factors are: the first
two are components of natural isomorphisms, and the third is the base-change morphism of the
square `X ×_S U ⟶ U`, which `isIso_baseChangeNatTrans_pullback` shows to be invertible. -/
instance isIso_openStalkComparison : IsIso (openStalkComparison f U F t) := by
  have a1 : IsIso ((Scheme.Modules.restrictStalkNatIso U.ι t).inv.app
      ((Scheme.Modules.pushforward f).obj F)) := inferInstance
  have a2 : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} t).map
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
        ((Scheme.Modules.pushforward f).obj F)).mapPresheaf) := by
    have := isIso_mapPresheaf ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
      ((Scheme.Modules.pushforward f).obj F))
    exact Functor.map_isIso _ _
  have a3 : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} t).map
      ((AffinePushforward.baseChangeNatTrans
        (IsPullback.of_hasPullback f U.ι).w).app F).mapPresheaf) := by
    have := isIso_baseChangeNatTrans_pullback f U F
    have := isIso_mapPresheaf ((AffinePushforward.baseChangeNatTrans
      (IsPullback.of_hasPullback f U.ι).w).app F)
    exact Functor.map_isIso _ _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ a1 (@IsIso.comp_isIso _ _ _ _ _ _ _ a2 a3)

end Pullback

end Stacks.AlgebraicGeometry.OpenBaseChange

end
