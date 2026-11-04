module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleProperBaseChangeChow

/-!
# Inverse image to the big étale topos and derived direct image along a proper morphism, for
torsion complexes

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a proper
morphism of its objects. Stacks 0DGD, part (2), says that
`π_X⁻¹ R f_{small,*} K = R f_{big,*} π_Y⁻¹ K` for `K` in `D⁺(Y_étale)` with torsion cohomology
sheaves. It is proved here with two inputs taken as hypotheses: the proper base change theorem
for étale sheaves of sets on schemes, Stacks 0A3U (`h0A3U`), and the compatibility of the
cohomology of a proper morphism of schemes with base change, Stacks 095T (`h095T`).

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleDerivedBaseChange_app`: given
  `h0A3U` and `h095T`, the base-change map `π_X⁻¹ R f_{small,*} K ⟶ R f_{big,*} π_Y⁻¹ K` is
  invertible.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleDerivedPushforwardIso`: Stacks 0DGD,
  part (2), given `h0A3U` and `h095T`, as an isomorphism.

## References

* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Homology.DerivedSquare (totalRightDerived)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard bigToSmallAbelianInverseImage_additive
  smallEtaleAbelianInverseImage_additive

/-- **Stacks 0DGD, part (2), with Stacks 0A3U and Stacks 095T as hypotheses.** Let `f : Y ⟶ X`
be a proper morphism of algebraic spaces of the big étale site. Assume the proper base change
theorem for étale sheaves of sets on schemes (`h0A3U`, Stacks 0A3U) and that the cohomology of a
proper morphism of schemes commutes with base change (`h095T`, Stacks 095T). Then for every
bounded below `K` on the spaces-étale site of `Y` with torsion cohomology sheaves the canonical
base-change map `π_X⁻¹ R f_{small,*} K ⟶ R f_{big,*} π_Y⁻¹ K` is an isomorphism. -/
theorem isIso_bigToSmallEtaleDerivedBaseChange_app {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)
    (K : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hK : K.IsGE n) (hT : HasTorsionCohomology T K) :
    IsIso ((bigToSmallEtaleDerivedBaseChange T f).app K) := by
  obtain ⟨L', hL'⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage K)
  obtain ⟨I, q, hI, hq⟩ := Stacks.Cohomology.Localization.enoughKInjectives L'
  have hqi : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  let e : K ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) :=
    (DerivedCategory.Qh.objObjPreimageIso K).symm ≪≫ eqToIso (by rw [← hL']) ≪≫
      asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q))
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  have := isIso_bigToSmallEtaleAbelianBaseChange T f hf h0A3U
  refine (isIso_bigToSmallEtaleDerivedBaseChange_app_iff T f I).mpr ?_
  refine isIso_of_isIso_mapDerivedCategory_smallEtaleRestriction T _ fun V => ?_
  have sq := IsPullback.of_hasPullback f V.hom
  refine (isIso_map_totalRightDerivedUnit_bigEtalePushforward_iff T f V.hom
    (pullback.fst f V.hom) (pullback.snd f V.hom) sq _).mpr ?_
  refine (NatTrans.isIso_app_iff_of_iso _
    (pulledAbelianInverseImageHomotopyIso T (pullback.fst f V.hom) _)).mpr ?_
  have := isIso_spacesEtaleAbelianBaseChange T f V.hom (pullback.fst f V.hom)
    (pullback.snd f V.hom) sq
    (Space.isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange T.fppfSite S T.fppf_mem
      h0A3U f hf V.hom (pullback.fst f V.hom) (pullback.snd f V.hom) sq)
  exact (isIso_spacesEtaleDerivedBaseChange_app_iff T f V.hom (pullback.fst f V.hom)
    (pullback.snd f V.hom) sq I).mp ((NatTrans.isIso_app_iff_of_iso _ e).mp
      (isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_representable T h0A3U h095T f hf
        V.hom (pullback.fst f V.hom) (pullback.snd f V.hom) sq K n hK hT))

/-- **Stacks 0DGD, part (2), with Stacks 0A3U and Stacks 095T as hypotheses `h0A3U` and
`h095T`**, as an isomorphism `π_X⁻¹ R f_{small,*} K ≅ R f_{big,*} π_Y⁻¹ K` for `K` bounded below
with torsion cohomology sheaves: the canonical base-change map
`AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleDerivedBaseChange`. -/
def bigToSmallEtaleDerivedPushforwardIso {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)
    (K : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hK : K.IsGE n) (hT : HasTorsionCohomology T K) :
    (CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X)).mapDerivedCategory.obj
        ((totalRightDerived (smallEtalePushforward T f)).obj K) ≅
      (totalRightDerived (bigEtalePushforward T f)).obj
        ((CategoryTheory.Sites.abelianInverseImage
          (bigToSmallEtaleMorphism T Y)).mapDerivedCategory.obj K) :=
  haveI := isIso_bigToSmallEtaleDerivedBaseChange_app T f hf h0A3U h095T K n hK hT
  asIso ((bigToSmallEtaleDerivedBaseChange T f).app K)

end AlgebraicGeometry.BigEtaleSpaceSite

end
