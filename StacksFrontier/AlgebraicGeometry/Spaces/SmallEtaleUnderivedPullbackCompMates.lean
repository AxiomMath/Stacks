module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.CategoryTheory.Adjunction.CounitMatesComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIsoComparison

/-!
# The degreewise composition isomorphism of pullbacks of algebraic spaces, unfolded

`AlgebraicGeometry.Space.smallEtaleUnderivedPullbackCompIso f g`, the degreewise composition
isomorphism `g^* ⋙ f^* ≅ (f ≫ g)^*` of pullbacks of complexes of modules on the small étale sites,
is the compositor of Stacks 03D6 for the morphisms of small étale ringed topoi, acting degreewise,
followed by the 2-isomorphism `pullbackModulesCompTransport` of Stacks 03G8. This file records
that identification through the equation lemma of the definition, in the spelling in which the
compositor is the degreewise action of `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleUnderivedPullbackCompIso_eq_transport`: the equation lemma.
* `AlgebraicGeometry.Space.smallEtaleUnderivedPullbackCompIso_counit`: read through the counits
  of the degreewise adjunctions, `smallEtaleUnderivedPullbackCompIso` is the mate of
  `modulePushforwardCompIso'`.
* `AlgebraicGeometry.Space.smallEtaleUnderivedPullbackCompIso_counit_of_eq`: the same, along an
  equality `f ≫ g = h`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **`smallEtaleUnderivedPullbackCompIso` unfolded**: the degreewise action of the compositor
`(g ∘ f)^* ≅ g^* ⋙ f^*` of the morphisms of small étale ringed topoi, followed by that of
`pullbackModulesCompTransport`. -/
theorem smallEtaleUnderivedPullbackCompIso_eq_transport (f : X ⟶ Y) (g : Y ⟶ Z) :
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS f)
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS g)
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS f g)
    haveI := RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS (f ≫ g))
    smallEtaleUnderivedPullbackCompIso B S hS f g =
      Functor.mapHomotopyCategoryCompIso
        (RingedToposHom.pullbackModulesCompIso (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)).symm
        (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
          (ComplexShape.up ℤ) := by
  rw [smallEtaleUnderivedPullbackCompIso]
  rfl

/-- The compositor `(g ∘ f)^* ≅ g^* ⋙ f^*` of the morphisms of small étale ringed topoi is the
uniqueness isomorphism of the left adjoints of the composite direct image, by its definition. -/
theorem pullbackModulesCompIso_smallEtale_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    RingedToposHom.pullbackModulesCompIso (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g) =
      ((RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHomComp B S hS f g)).ofNatIsoRight
          (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g))).leftAdjointUniq
        ((RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y)
            (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS g)).comp
          (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
            (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))) :=
  rfl

/-- `pullbackModulesCompTransport` is the uniqueness isomorphism of the left adjoints of the
direct image along `f ≫ g`, transported along `pushforwardModulesCompTransport`, by its
definition. -/
theorem pullbackModulesCompTransport_eq_leftAdjointUniq (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackModulesCompTransport B S hS f g =
      (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHomComp B S hS f g)).leftAdjointUniq
        ((RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS (f ≫ g))).ofNatIsoRight
          (pushforwardModulesCompTransport B S hS f g).symm) := by
  rw [pullbackModulesCompTransport]

/-- **The mates identity for `smallEtaleUnderivedPullbackCompIso`.** Read through the counits
of the degreewise adjunctions, the degreewise composition isomorphism of pullbacks is the mate of
the composition isomorphism `modulePushforwardCompIso'` of direct images. -/
theorem smallEtaleUnderivedPullbackCompIso_counit (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (smallEtalePullbackMapHomotopy B S hS f).map
        ((smallEtalePullbackMapHomotopy B S hS g).map
            ((Functor.mapHomotopyCategoryCompIso (modulePushforwardCompIso' B S hS f g)
              (ComplexShape.up ℤ)).inv.app K) ≫
          (smallEtaleMapHomotopyAdjunction B S hS g).counit.app
            ((smallEtalePushforwardMapHomotopy B S hS f).obj K)) ≫
        (smallEtaleMapHomotopyAdjunction B S hS f).counit.app K =
      (smallEtaleUnderivedPullbackCompIso B S hS f g).hom.app
          ((smallEtalePushforwardMapHomotopy B S hS (f ≫ g)).obj K) ≫
        (smallEtaleMapHomotopyAdjunction B S hS (f ≫ g)).counit.app K := by
  have hc : modulePushforwardCompIso' B S hS f g =
      (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm ≪≫
        pushforwardModulesCompTransport B S hS f g := by
    rw [pushforwardModulesCompTransport_eq]
    rfl
  have k := Adjunction.counit_comp_of_eq_leftAdjointUniq _ _ _ _ _
    (pullbackModulesCompIso_smallEtale_eq B S hS f g)
  have ht := Adjunction.counit_comp_of_eq_leftAdjointUniq_ofNatIsoRight _ _ _ _
    (pullbackModulesCompTransport_eq_leftAdjointUniq B S hS f g)
  have H := Adjunction.mapHomotopyCategory_counit_mates_of_eq
    (af := (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)))
    (ag := (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS Y)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS g)))
    (ac := (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHomComp B S hS f g)))
    (ah := (RingedToposHom.pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS (f ≫ g))))
    (pc := RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g))
    (pm := RingedToposHom.pullbackModulesCompIso (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
      (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g))
    (tp := pushforwardModulesCompTransport B S hS f g)
    (T := pullbackModulesCompTransport B S hS f g)
    (c := modulePushforwardCompIso' B S hS f g)
    (AF := smallEtaleMapHomotopyAdjunction B S hS f)
    (AG := smallEtaleMapHomotopyAdjunction B S hS g)
    (AH := smallEtaleMapHomotopyAdjunction B S hS (f ≫ g))
    (e' := smallEtaleUnderivedPullbackCompIso B S hS f g)
    hc k ht rfl rfl rfl (smallEtaleUnderivedPullbackCompIso_eq_transport B S hS f g) K
  convert H using 4

/-- The composition isomorphism `f_* ⋙ g_* ≅ h_*` of degreewise direct images on unbounded
homotopy categories, for `f ≫ g = h`: the degreewise action of `modulePushforwardCompIso'`
followed by the transport along `f ≫ g = h`. -/
def smallEtalePushforwardMapHomotopyCompIso (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (w : f ≫ g = h) :
    smallEtalePushforwardMapHomotopy B S hS f ⋙ smallEtalePushforwardMapHomotopy B S hS g ≅
      smallEtalePushforwardMapHomotopy B S hS h :=
  Functor.mapHomotopyCategoryCompIso (modulePushforwardCompIso' B S hS f g ≪≫
    eqToIso (congrArg (fun k ↦ (smallEtaleRingedToposHom B S hS k).pushforwardModules) w))
    (ComplexShape.up ℤ)

/-- **The mates identity for `smallEtaleUnderivedPullbackCompIso`, along `f ≫ g = h`.** The
form of `smallEtaleUnderivedPullbackCompIso_counit` in which the composite is transported to a
morphism `h` equal to `f ≫ g`, on both sides. -/
theorem smallEtaleUnderivedPullbackCompIso_counit_of_eq (f : X ⟶ Y) (g : Y ⟶ Z) {h : X ⟶ Z}
    (w : f ≫ g = h)
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (ComplexShape.up ℤ)) :
    (smallEtalePullbackMapHomotopy B S hS f).map
        ((smallEtalePullbackMapHomotopy B S hS g).map
            ((smallEtalePushforwardMapHomotopyCompIso B S hS f g w).inv.app K) ≫
          (smallEtaleMapHomotopyAdjunction B S hS g).counit.app
            ((smallEtalePushforwardMapHomotopy B S hS f).obj K)) ≫
        (smallEtaleMapHomotopyAdjunction B S hS f).counit.app K =
      (smallEtaleUnderivedPullbackCompIso B S hS f g ≪≫
          smallEtaleUnderivedPullbackCongr B S hS w).hom.app
          ((smallEtalePushforwardMapHomotopy B S hS h).obj K) ≫
        (smallEtaleMapHomotopyAdjunction B S hS h).counit.app K := by
  subst w
  rw [smallEtalePushforwardMapHomotopyCompIso, eqToIso_refl, Iso.trans_refl,
    smallEtaleUnderivedPullbackCongr, eqToIso_refl, Iso.trans_refl]
  exact smallEtaleUnderivedPullbackCompIso_counit B S hS f g K

end AlgebraicGeometry.Space

end
