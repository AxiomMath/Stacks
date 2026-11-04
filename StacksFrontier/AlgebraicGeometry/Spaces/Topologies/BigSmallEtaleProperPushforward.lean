module

public import StacksFrontier.CategoryTheory.Adjunction.MateCube
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleCohomologicalDescent
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Inverse image to the big étale topos and direct image along a proper morphism

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a morphism of
its objects. The commutative square of Tag 0DF6, part (3),
`f_{small,*} ∘ π_{Y,*} = π_{X,*} ∘ f_{big,*}`, has a canonical *mate*

`π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹`,

here `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleBaseChange`. By Stacks 0DGD, part (1),
it is an isomorphism when `f` is proper; this is shown granted Stacks 0A3U, proper base change for
étale sheaves of sets on schemes, taken as the hypothesis `h0A3U`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtalePullbackSquare`: the square of Tag 0DF6,
  part (3), with the big direct image written as restriction along `Over.pullback f`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleBaseChange`: its mate across the
  adjunctions `π_Y⁻¹ ⊣ π_{Y,*}` and `π_X⁻¹ ⊣ π_{X,*}`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtalePushforwardIso`: the isomorphism
  `π_X⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_Y⁻¹` of Stacks 0DGD, part (1), granted Stacks 0A3U.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleBaseChange_cube`: for a cartesian square
  `Y' = Y ×_X X'`, the base change of the mate along `g_{big}` is, through the inverse-image
  squares conjugate to Tag 0DF6 for `g` and `g'`, the mate for `f'` composed with the proper
  base change map of Stacks 0DG0.
* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleBaseChange`: the mate is an
  isomorphism for `f` proper, granted Stacks 0A3U.

## References

* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 0DF6](https://stacks.math.columbia.edu/tag/0DF6)
* [Stacks Project, Tag 0DGC](https://stacks.math.columbia.edu/tag/0DGC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TwoSquare

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-! ### The square of Tag 0DF6 with the big direct image as a restriction -/

/-- The square `f_{small,*} ∘ π_{Y,*} ≅ π_{X,*} ∘ f_{big,*}` of Stacks 0DF6, part (3), with the
big étale direct image `f_{big,*}` written as restriction along `Over.pullback f`; it is the
identity. -/
def bigSmallEtalePullbackSquare {X Y : T.Spaces} (f : Y ⟶ X) :
    (bigToSmallEtaleMorphism T Y).pushforward ⋙ (smallEtaleMorphism T f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology X)
          (T.bigEtaleTopology Y) ⋙ (bigToSmallEtaleMorphism T X).pushforward :=
  Iso.refl _

/-- The canonical base-change map `π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹`, with `f_{big,*}`
written as restriction along `Over.pullback f`: the mate of the square
`AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtalePullbackSquare` across the adjunctions
`π_Y⁻¹ ⊣ π_{Y,*}` and `π_X⁻¹ ⊣ π_{X,*}` (Stacks 07A7 for this square). -/
def bigToSmallEtaleBaseChange {X Y : T.Spaces} (f : Y ⟶ X) :
    (smallEtaleMorphism T f).pushforward ⋙ (bigToSmallEtaleMorphism T X).inverseImage ⟶
      (bigToSmallEtaleMorphism T Y).inverseImage ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology X)
          (T.bigEtaleTopology Y) :=
  ((mateEquiv (bigToSmallEtaleMorphism T Y).adj (bigToSmallEtaleMorphism T X).adj).symm
    (bigSmallEtalePullbackSquare T f).hom).natTrans

/-! ### The cube of mates -/

section Cube

variable {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
  (sq : IsPullback g' f' f g)

/-- The comparison of the two composites of the big étale direct images around a commuting
square, as restrictions along `Over.pullback`: restriction along the comparison
`CategoryTheory.overPullbackCompSquare` of the two composites of base change of slices. -/
def bigEtalePullbackCompSquare :
    (Over.pullback g').sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology Y)
          (T.bigEtaleTopology Y') ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology X)
          (T.bigEtaleTopology Y) ⟶
      (Over.pullback f').sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology X')
          (T.bigEtaleTopology Y') ⋙
        (Over.pullback g).sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology X)
          (T.bigEtaleTopology X') :=
  letI := Functor.isContinuous_comp (Over.pullback f) (Over.pullback g')
    (T.bigEtaleTopology X) (T.bigEtaleTopology Y) (T.bigEtaleTopology Y')
  letI := Functor.isContinuous_comp (Over.pullback g) (Over.pullback f')
    (T.bigEtaleTopology X) (T.bigEtaleTopology X') (T.bigEtaleTopology Y')
  Functor.sheafPushforwardContinuousNatTrans (overPullbackCompSquare g' f' f g sq.w)
    (Type (u + 1)) (T.bigEtaleTopology X) (T.bigEtaleTopology Y')

/-- **The cube of direct images commutes.** Around the cartesian square `Y' = Y ×_X X'`, the
composite of the big composition square with Tag 0DF6 for `f` equals the composite of Tag 0DF6
for `g'` (inverted), the small composition square, Tag 0DF6 for `f'` and Tag 0DF6 for `g`. -/
theorem bigSmallEtale_pushforwardCube :
    TwoSquare.mk _ _ _ _ (bigEtalePullbackCompSquare T f g g' f' sq) ≫ₕ
        TwoSquare.mk _ _ _ _ (bigSmallEtalePullbackSquare T f).hom =
      ((TwoSquare.mk _ _ _ _ (bigSmallEtalePullbackSquare T f').hom ≫ₕ
          TwoSquare.mk _ _ _ _ (Space.spacesPushforwardCompSquare T.fppfSite S T.fppf_mem
            g' f' f g sq.w)).whiskerBottom
                (bigSmallEtalePullbackSquare T g).hom).whiskerTop
        (bigSmallEtalePullbackSquare T g').inv := by
  rw [Space.spacesPushforwardCompSquare_eq]
  ext H U x
  change H.obj.map ((overPullbackCompSquare g' f' f g sq.w).app
      ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).obj U.unop)).op x = _
  change _ = H.obj.map ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y').map
      ((Space.spacesBaseChangeCompSquare T.fppfSite S T.fppf_mem g' f' f g sq.w).app U.unop)).op x
  rw [Space.spacesBaseChangeCompSquare_app_map]
  rfl

/-- **The cube of mates for Stacks 0DGD.** For a cartesian square `Y' = Y ×_X X'`, the base
change of `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleBaseChange` along `g_{big}`,
followed by the Beck–Chevalley map of the big sites, is the proper base change map of
Stacks 0DG0 for the square followed by the mate for `f'`, read through the two inverse-image
squares conjugate to Tag 0DF6 for `g` and for `g'`. -/
theorem bigToSmallEtaleBaseChange_cube :
    TwoSquare.mk _ _ _ _ (bigToSmallEtaleBaseChange T f) ≫ᵥ
        (mateEquiv ((Over.mapPullbackAdj g').sheafPushforwardContinuous (E := Type (u + 1))
            (T.bigEtaleTopology Y') (T.bigEtaleTopology Y))
          ((Over.mapPullbackAdj g).sheafPushforwardContinuous (E := Type (u + 1))
            (T.bigEtaleTopology X') (T.bigEtaleTopology X))).symm
          (TwoSquare.mk _ _ _ _ (bigEtalePullbackCompSquare T f g g' f' sq)) =
      ((TwoSquare.mk _ _ _ _ (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem
            g' f' f g sq) ≫ᵥ TwoSquare.mk _ _ _ _ (bigToSmallEtaleBaseChange T f')).whiskerRight
          ((conjugateEquiv ((smallEtaleMorphism T g).adj.comp (bigToSmallEtaleMorphism T X').adj)
            ((bigToSmallEtaleMorphism T X).adj.comp
              ((Over.mapPullbackAdj g).sheafPushforwardContinuous (E := Type (u + 1))
                (T.bigEtaleTopology X') (T.bigEtaleTopology X)))).symm
            (bigSmallEtalePullbackSquare T g).hom)).whiskerLeft
        ((conjugateEquiv ((bigToSmallEtaleMorphism T Y).adj.comp
              ((Over.mapPullbackAdj g').sheafPushforwardContinuous (E := Type (u + 1))
                (T.bigEtaleTopology Y') (T.bigEtaleTopology Y)))
            ((smallEtaleMorphism T g').adj.comp (bigToSmallEtaleMorphism T Y').adj)).symm
          (bigSmallEtalePullbackSquare T g').inv) := by
  refine mateEquiv_symm_vComp_eq_of_cube (bigToSmallEtaleMorphism T Y).adj
    (bigToSmallEtaleMorphism T X).adj (bigToSmallEtaleMorphism T Y').adj
    (bigToSmallEtaleMorphism T X').adj _ _ (smallEtaleMorphism T g').adj
    (smallEtaleMorphism T g).adj _ _ _ _ _ _ ?_
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact bigSmallEtale_pushforwardCube T f g g' f' sq

/-- The Beck–Chevalley map of the big étale sites, the mate of
`AlgebraicGeometry.BigEtaleSpaceSite.bigEtalePullbackCompSquare`, is the restriction along the
Beck–Chevalley isomorphism of slices. -/
theorem mateEquiv_symm_bigEtalePullbackCompSquare :
    letI := Functor.isContinuous_comp (Over.pullback f') (Over.map g')
      (T.bigEtaleTopology X') (T.bigEtaleTopology Y') (T.bigEtaleTopology Y)
    letI := Functor.isContinuous_comp (Over.map g) (Over.pullback f)
      (T.bigEtaleTopology X') (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
    (mateEquiv ((Over.mapPullbackAdj g').sheafPushforwardContinuous (E := Type (u + 1))
          (T.bigEtaleTopology Y') (T.bigEtaleTopology Y))
        ((Over.mapPullbackAdj g).sheafPushforwardContinuous (E := Type (u + 1))
          (T.bigEtaleTopology X') (T.bigEtaleTopology X))).symm
        (TwoSquare.mk _ _ _ _ (bigEtalePullbackCompSquare T f g g' f' sq)) =
      TwoSquare.mk
        ((Over.pullback f).sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology X)
          (T.bigEtaleTopology Y))
        ((Over.map g').sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology Y')
          (T.bigEtaleTopology Y))
        ((Over.map g).sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology X')
          (T.bigEtaleTopology X))
        ((Over.pullback f').sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology X')
          (T.bigEtaleTopology Y'))
        (Functor.sheafPushforwardContinuousNatTrans
          (Over.beckChevalleyIso sq).hom (Type (u + 1)) (T.bigEtaleTopology X')
          (T.bigEtaleTopology Y)) := by
  rw [Equiv.symm_apply_eq, mateEquiv_sheafPushforwardContinuousNatTrans (Over.mapPullbackAdj g)
    (Over.mapPullbackAdj g') (T.bigEtaleTopology X') (T.bigEtaleTopology X)
    (T.bigEtaleTopology Y') (T.bigEtaleTopology Y) (TwoSquare.mk _ _ _ _
      (Over.beckChevalleyIso sq).hom), mateEquiv_beckChevalleyIso]
  rfl

end Cube

/-! ### Invertibility of the base-change map -/

/-- The unit `𝟭 ⟶ π_{X,*} ∘ π_X⁻¹` of the adjunction of `π_X` is invertible (Stacks 0DGC). -/
theorem isIso_bigToSmallEtaleMorphism_unit (X : T.Spaces) :
    IsIso (bigToSmallEtaleMorphism T X).adj.unit :=
  (bigToSmallEtaleMorphism T X).adj.isIso_unit_of_iso
    (bigToSmall_inverseImage_comp_pushforwardIso T X)

/-- After restriction to the spaces-étale site, the base-change map is invertible, for every
morphism `f`. -/
theorem isIso_map_bigToSmallEtaleBaseChange_app {X Y : T.Spaces} (f : Y ⟶ X)
    (K : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1))) :
    IsIso ((bigToSmallEtaleMorphism T X).pushforward.map
      ((bigToSmallEtaleBaseChange T f).app K)) := by
  have := isIso_bigToSmallEtaleMorphism_unit T X
  have := isIso_bigToSmallEtaleMorphism_unit T Y
  have : IsIso (TwoSquare.mk _ _ _ _ (bigSmallEtalePullbackSquare T f).hom).natTrans :=
    inferInstanceAs (IsIso (bigSmallEtalePullbackSquare T f).hom)
  exact isIso_map_mateEquiv_symm_app_of_isIso_unit (bigToSmallEtaleMorphism T Y).adj
    (bigToSmallEtaleMorphism T X).adj _ K

/-- **Stacks 0DGD, part (1), granted Stacks 0A3U, as invertibility of the mate.** Let
`f : Y ⟶ X` be a proper morphism of algebraic spaces of the big étale site. Then the canonical
map `π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹` is an isomorphism. Stacks 0A3U is the hypothesis
`h0A3U`. -/
theorem isIso_bigToSmallEtaleBaseChange {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    IsIso (bigToSmallEtaleBaseChange T f) := by
  suffices h : ∀ K, IsIso ((bigToSmallEtaleBaseChange T f).app K) from
    NatIso.isIso_of_isIso_app _
  intro K
  suffices hV : ∀ V : Over X, IsIso (((bigToSmallEtaleBaseChange T f).app K).hom.app (op V)) by
    have : IsIso ((sheafToPresheaf _ _).map ((bigToSmallEtaleBaseChange T f).app K)) :=
      NatIso.isIso_of_isIso_app (((bigToSmallEtaleBaseChange T f).app K).hom)
    exact isIso_of_reflects_iso ((bigToSmallEtaleBaseChange T f).app K)
      (sheafToPresheaf _ _)
  intro V
  have sq := IsPullback.of_hasPullback f V.hom
  have := Functor.isContinuous_comp (Over.pullback (pullback.snd f V.hom))
    (Over.map (pullback.fst f V.hom)) (T.bigEtaleTopology V.left)
    (T.bigEtaleTopology (pullback f V.hom)) (T.bigEtaleTopology Y)
  have := Functor.isContinuous_comp (Over.map V.hom) (Over.pullback f)
    (T.bigEtaleTopology V.left) (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
  have hb : IsIso ((mateEquiv
      ((Over.mapPullbackAdj (pullback.fst f V.hom)).sheafPushforwardContinuous
        (E := Type (u + 1)) (T.bigEtaleTopology (pullback f V.hom)) (T.bigEtaleTopology Y))
      ((Over.mapPullbackAdj V.hom).sheafPushforwardContinuous (E := Type (u + 1))
        (T.bigEtaleTopology V.left) (T.bigEtaleTopology X))).symm
      (TwoSquare.mk _ _ _ _ (bigEtalePullbackCompSquare T f V.hom (pullback.fst f V.hom)
        (pullback.snd f V.hom) sq))).natTrans := by
    rw [mateEquiv_symm_bigEtalePullbackCompSquare]
    exact (Functor.sheafPushforwardContinuousIso (Over.beckChevalleyIso sq).symm (Type (u + 1))
      (T.bigEtaleTopology V.left) (T.bigEtaleTopology Y)).isIso_hom
  have hs : IsIso ((mateEquiv (smallEtaleMorphism T (pullback.fst f V.hom)).adj
      (smallEtaleMorphism T V.hom).adj).symm (TwoSquare.mk _ _ _ _
        (Space.spacesPushforwardCompSquare T.fppfSite S T.fppf_mem (pullback.fst f V.hom)
          (pullback.snd f V.hom) f V.hom sq.w))).natTrans :=
    Space.isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange T.fppfSite S T.fppf_mem
      h0A3U f hf V.hom (pullback.fst f V.hom) (pullback.snd f V.hom) sq
  have h := isIso_map_map_mateEquiv_symm_app_of_cube (bigToSmallEtaleMorphism T Y).adj
    (bigToSmallEtaleMorphism T X).adj (bigToSmallEtaleMorphism T (pullback f V.hom)).adj
    (bigToSmallEtaleMorphism T V.left).adj _ _ (smallEtaleMorphism T (pullback.fst f V.hom)).adj
    (smallEtaleMorphism T V.hom).adj _ _ _ _ _ _
    (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact bigSmallEtale_pushforwardCube T f V.hom (pullback.fst f V.hom)
          (pullback.snd f V.hom) sq)
    hb hs (fun M => isIso_map_bigToSmallEtaleBaseChange_app T (pullback.snd f V.hom) M) K
  let W := (Over.map V.hom).obj ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem V.left).obj
    (Space.SpacesEtale.final T.fppfSite S T.fppf_mem V.left))
  have h1 : IsIso ((sheafToPresheaf _ _).map ((bigToSmallEtaleMorphism T V.left).pushforward.map
      (((Over.map V.hom).sheafPushforwardContinuous (Type (u + 1)) (T.bigEtaleTopology V.left)
        (T.bigEtaleTopology X)).map ((bigToSmallEtaleBaseChange T f).app K)))) :=
    @Functor.map_isIso _ _ _ _ _ _ (sheafToPresheaf _ _) _ h
  have h2 : IsIso (((bigToSmallEtaleBaseChange T f).app K).hom.app (op W)) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ h1
      (op (Space.SpacesEtale.final T.fppfSite S T.fppf_mem V.left))
  let e : W ≅ V := Over.isoMk (Iso.refl _) (by simp [W, Space.SpacesEtale.final])
  exact (NatTrans.isIso_app_iff_of_iso _ e.op).mp h2

/-- **Stacks 0DGD, part (1), granted Stacks 0A3U.** For a proper morphism `f : Y ⟶ X` of
algebraic spaces of the big étale site, the canonical base-change map is an isomorphism of functors
`π_X⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_Y⁻¹` from sheaves on the spaces-étale site of `Y` to sheaves
on the big étale site of `X`. Here `f_{big,*}` is the direct image of the big étale morphism of
Tag 0DF5, identified with restriction along `Over.pullback f` by
`CategoryTheory.StacksRelocalization.sheafPushforwardOverMapIso`. Stacks 0A3U is the
hypothesis `h0A3U`. -/
def bigToSmallEtalePushforwardIso {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    (smallEtaleMorphism T f).pushforward ⋙ (bigToSmallEtaleMorphism T X).inverseImage ≅
      (bigToSmallEtaleMorphism T Y).inverseImage ⋙ (bigEtaleMorphism T f).pushforward :=
  haveI := isIso_bigToSmallEtaleBaseChange T f hf h0A3U
  asIso (bigToSmallEtaleBaseChange T f) ≪≫
    Functor.isoWhiskerLeft _ (StacksRelocalization.sheafPushforwardOverMapIso T.topology f).symm

end AlgebraicGeometry.BigEtaleSpaceSite

end
