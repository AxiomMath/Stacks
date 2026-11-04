module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Quot.PullSheafHomRelHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroUnderivedBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
public import StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# The composition comparison of the derived pullback datum

The pullback pseudofunctor datum `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` of
derived pullbacks along morphisms of algebraic spaces has as composition comparison the
comparison of two left derived functors of degreewise pullback along a composite, induced by the
universal property. This file proves that it is the inverse of the composition isomorphism
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso` of Stacks 0D6D.

Both are characterized on the images of complexes (by `CategoryTheory.Functor.leftDerived_ext`),
so the claim reduces to the underived statement: the composition comparison of the inverse
images of `𝒪`-modules of Stacks 03LU, read in the spelling of the morphisms of small étale ringed
topoi, is the inverse of the compositor of Stacks 03D8 followed by the transport
`AlgebraicGeometry.Space.pullbackModulesCompTransport`. All three comparisons involved are
comparisons of left adjoints, so this is a computation with
`CategoryTheory.Adjunction.leftAdjointUniq`, whose only input is the definition of the
comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of the direct images.

## Main results

* `AlgebraicGeometry.Space.modulePullbackDataTopos_compIso_symm_eq`: the underived statement.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_eq`: **the composition
  comparison of the derived pullback datum is the inverse of the composition isomorphism of
  Stacks 0D6D.**
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataCompIsoEq`: the same, as the
  proposition `AlgebraicGeometry.Space.SmallEtaleDerivedPullbackDataCompIsoEq`.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]

/-- Transporting an adjunction along the identity of its left adjoint does not change it. -/
theorem ofNatIsoLeft_refl {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    adj.ofNatIsoLeft (Iso.refl L) = adj := by
  apply Adjunction.ext
  simp [Adjunction.ofNatIsoLeft]

variable {CX CY CZ : Type*} [Category* CX] [Category* CY] [Category* CZ]
  {Pf : CY ⥤ CX} {Pg : CZ ⥤ CY} {Pfg Pgf : CZ ⥤ CX} {Ff : CX ⥤ CY} {Fg : CY ⥤ CZ}
  {Ffg Fgf : CX ⥤ CZ} (af : Pf ⊣ Ff) (ag : Pg ⊣ Fg) (afg : Pfg ⊣ Ffg) (agf : Pgf ⊣ Fgf)
  (cF : Fgf ≅ Ff ⋙ Fg) (tF : Fgf ≅ Ffg)

/-- Let `Pg ⋙ Pf`, `Pgf` and `Pfg` be left adjoint to `Ff ⋙ Fg`, `Fgf` and `Ffg`, and let
`cF : Fgf ≅ Ff ⋙ Fg` and `tF : Fgf ≅ Ffg`. The inverse of the comparison of `Pgf` with the
composite (through `cF`), followed by the comparison of `Pgf` with `Pfg` (through `tF`), is the
comparison of the composite with `Pfg` through `cF⁻¹ ≪≫ tF`. -/
theorem leftAdjointUniq_comp_ofNatIsoRight_symm_trans :
    leftAdjointUniq ((ag.comp af).ofNatIsoRight (cF.symm ≪≫ tF)) afg =
      (leftAdjointUniq (agf.ofNatIsoRight cF) (ag.comp af)).symm ≪≫
        leftAdjointUniq agf (afg.ofNatIsoRight tF.symm) := by
  have key : ∀ {L L' : CZ ⥤ CX} {R R' : CX ⥤ CZ} (a : L ⊣ R) (b : L' ⊣ R') (e : R ≅ R'),
      leftAdjointUniq (a.ofNatIsoRight e) b = leftAdjointUniq a (b.ofNatIsoRight e.symm) := by
    intro L L' R R' a b e
    rw [← leftAdjointUniq_ofNatIsoRight_congr a (b.ofNatIsoRight e.symm) e,
      ofNatIsoRight_trans, Iso.symm_self_id, ofNatIsoRight_refl]
  have e₁ : (leftAdjointUniq (agf.ofNatIsoRight cF) (ag.comp af)).symm = _ :=
    (Iso.ext (Stacks.CategoryTheory.leftAdjointUniq_inv _ _)).trans (key _ _ cF.symm).symm
  rw [e₁, ← key agf afg tF,
    ← leftAdjointUniq_ofNatIsoRight_congr ((ag.comp af).ofNatIsoRight cF.symm) agf tF,
    ofNatIsoRight_trans]
  exact Iso.ext (leftAdjointUniq_trans _ _ _).symm

/-- **Two comparisons of left adjoints of a composite, compared across a change of spelling.**
Let `a'f`, `a'g`, `a'fg` be adjunctions whose left adjoints are equal to those of `af`, `ag`,
`afg` and which are these adjunctions transported along those equalities and along isomorphisms
`σf`, `σg`, `σfg` of the right adjoints; let `mC` compare the composite of the transported right
adjoints with the third, compatibly (`hσ`) with `cF⁻¹ ≪≫ tF`. Then the comparison of the left
adjoints of the transported data through `mC`, read back along the equalities, is the inverse of
the comparison of `Pgf` with the composite (through `cF`) followed by the comparison of `Pgf`
with `Pfg` (through `tF`). -/
theorem leftAdjointUniq_comp_transport_eq
    {P'f : CY ⥤ CX} {P'g : CZ ⥤ CY} {P'fg : CZ ⥤ CX} {F'f : CX ⥤ CY} {F'g : CY ⥤ CZ}
    {F'fg : CX ⥤ CZ} (a'f : P'f ⊣ F'f) (a'g : P'g ⊣ F'g) (a'fg : P'fg ⊣ F'fg)
    (mC : F'f ⋙ F'g ≅ F'fg) (hf : Pf = P'f) (hg : Pg = P'g) (hfg : Pfg = P'fg)
    (hcomp : P'g ⋙ P'f = Pg ⋙ Pf) (σf : Ff ≅ F'f) (σg : Fg ≅ F'g) (σfg : Ffg ≅ F'fg)
    (haf : a'f = (af.ofNatIsoLeft (eqToIso hf)).ofNatIsoRight σf)
    (hag : a'g = (ag.ofNatIsoLeft (eqToIso hg)).ofNatIsoRight σg)
    (hafg : a'fg = (afg.ofNatIsoLeft (eqToIso hfg)).ofNatIsoRight σfg)
    (hσ : (Functor.isoWhiskerRight σf Fg ≪≫ Functor.isoWhiskerLeft F'f σg) ≪≫ mC =
      cF.symm ≪≫ tF ≪≫ σfg) :
    (eqToIso hfg ≪≫ (leftAdjointUniq ((a'g.comp a'f).ofNatIsoRight mC) a'fg).symm ≪≫
        eqToIso hcomp).symm =
      (leftAdjointUniq (agf.ofNatIsoRight cF) (ag.comp af)).symm ≪≫
        leftAdjointUniq agf (afg.ofNatIsoRight tF.symm) := by
  subst hf hg hfg
  simp only [eqToIso_refl, ofNatIsoLeft_refl] at haf hag hafg
  subst haf hag hafg
  rw [Iso.trans_assoc] at hσ
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl, Iso.symm_symm_eq]
  rw [← leftAdjointUniq_comp_ofNatIsoRight_symm_trans, comp_ofNatIsoRight_left,
    comp_ofNatIsoRight_right, ofNatIsoRight_trans, ofNatIsoRight_trans, hσ, ← Iso.trans_assoc,
    ← ofNatIsoRight_trans _ (cF.symm ≪≫ tF) σfg, leftAdjointUniq_ofNatIsoRight_congr]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

/-- Whiskering two transports along equalities of functors, followed by the transport back, is
the identity, also in front of an isomorphism. -/
theorem isoWhisker_eqToIso_trans_eqToIso_trans {A B C : Type*} [Category* A] [Category* B]
    [Category* C] {F F' : A ⥤ B} {G G' : B ⥤ C} {H : A ⥤ C} (a : F = F') (b : G = G')
    (c : F' ⋙ G' = F ⋙ G) (e : F ⋙ G ≅ H) :
    (isoWhiskerRight (eqToIso a) G ≪≫ isoWhiskerLeft F' (eqToIso b)) ≪≫ eqToIso c ≪≫ e = e := by
  subst a b
  ext
  simp

end CategoryTheory.Functor

namespace Stacks.Homology

/-- Let `c : H ≅ G ⋙ F` be the inverse of `d ≪≫ t` for `d : G ⋙ F ≅ K` and `t : K ≅ H`. Then the
inverse of the isomorphism `H ≅ G ⋙ F` induced by `c` on homotopy categories is the one induced
by `d` followed by the one induced by `t`. -/
theorem mapHomotopyCategoryIso_trans_compIso_symm_symm_eq {A₁ A₂ A₃ : Type*} [Category* A₁]
    [Category* A₂] [Category* A₃] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
    {F : A₂ ⥤ A₁} {G : A₃ ⥤ A₂} {H K : A₃ ⥤ A₁} [hF : F.Additive] [hG : G.Additive]
    [hH : H.Additive] [hK : K.Additive] (c : H ≅ G ⋙ F) (d : G ⋙ F ≅ K) (t : K ≅ H)
    (hU : c.symm = d ≪≫ t) :
    (mapHomotopyCategoryIso c (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ F)) (ComplexShape.up ℤ)).symm).symm =
      Functor.mapHomotopyCategoryCompIso d (ComplexShape.up ℤ) ≪≫
        mapHomotopyCategoryIso t (ComplexShape.up ℤ) := by
  have e : (mapHomotopyCategoryIso c (ComplexShape.up ℤ)).symm =
      mapHomotopyCategoryIso c.symm (ComplexShape.up ℤ) := Iso.ext rfl
  rw [Iso.trans_symm, Iso.symm_symm_eq, e, mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso,
    Iso.refl_trans, hU, ← mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso]

end Stacks.Homology

namespace CategoryTheory.PullbackData.LeftDerived

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {A : Type u₁} [Category.{v₁} A] {K : A → Type u₂} [∀ a, Category.{v₂} (K a)]
  {D : A → Type u₃} [∀ a, Category.{v₃} (D a)] {P : PullbackData A K} (E : P.LeftDerived D)

/-- **The composition comparison of a datum of left derived functors is determined on the images
of the localization functors**: a transformation `τ : Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*` which, followed by
the comparison along `f ≫ g`, is the comparison for `g`, then the one for `f`, then the inverse
`κ` of the underived composition comparison, is the comparison `E.compHom f g`. -/
theorem compHom_eq_of_app {a b c : A} (f : a ⟶ b) (g : b ⟶ c)
    (κ : P.pull g ⋙ P.pull f ≅ P.pull (f ≫ g)) (hκ : (P.compIso f g).symm = κ)
    (τ : E.L g ⋙ E.L f ⟶ E.L (f ≫ g))
    (h : ∀ M, τ.app ((E.Q c).obj M) ≫ (E.α (f ≫ g)).app M =
      (E.L f).map ((E.α g).app M) ≫ (E.α f).app ((P.pull g).obj M) ≫
        (E.Q a).map (κ.hom.app M)) :
    E.compHom f g = τ := by
  subst hκ
  refine ((E.L (f ≫ g)).leftDerived_ext (E.α (f ≫ g)) (E.W c) _ _ _ ?_).symm
  unfold compHom
  rw [Functor.leftDerived_fac]
  ext M
  exact (h M).trans (E.compCounit_app f g M).symm

end CategoryTheory.PullbackData.LeftDerived

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The underived statement -/

/-- The pullback of modules along the composite of the morphisms of small étale ringed topoi of
two morphisms of algebraic spaces is additive. -/
instance smallEtaleRingedToposHom_comp_pullbackModules_additive {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((smallEtaleRingedToposHom B S hS g).comp
      (smallEtaleRingedToposHom B S hS f)).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS f g)

/-- **The adjunction of Stacks 03LU is the adjunction of the morphism of small étale ringed
topoi**, transported along the equalities of the two spellings of the inverse and the direct
image. -/
theorem modulePullbackAdjunction_eq_ofNatIsoLeft_eqToIso {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) :
    modulePullbackAdjunction B S hS f =
      ((RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS f)).ofNatIsoLeft
        (eqToIso (toModulesHom_pullbackModules_eq_modulePullback B S hS f))).ofNatIsoRight
        (eqToIso (pushforwardModules_eq_modulePushforward B S hS f)) :=
  (modulePullbackAdjunction_eq_transport f).trans
    (congrArg (fun e => ((RingedToposHom.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS f)).ofNatIsoLeft
        (smallEtaleToposPullbackSpellingIso f)).ofNatIsoRight e)
      (smallEtaleToposPushforwardSpellingIso_eq_eqToIso f))

/-- The composition comparison of direct images of Stacks 03LU, preceded by the transports along
the equalities of the two spellings of the direct images, is the inverse of the compositor of
the morphisms of small étale ringed topoi followed by the transport
`AlgebraicGeometry.Space.pushforwardModulesCompTransport`. -/
theorem isoWhisker_eqToIso_trans_modulePushforwardCompIso {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Functor.isoWhiskerRight (eqToIso (pushforwardModules_eq_modulePushforward B S hS f))
        (smallEtaleRingedToposHom B S hS g).pushforwardModules ≪≫
      Functor.isoWhiskerLeft (modulePushforward B S hS f)
        (eqToIso (pushforwardModules_eq_modulePushforward B S hS g))) ≪≫
        modulePushforwardCompIso B S hS f g =
      (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pushforwardModulesCompTransport B S hS f g ≪≫
        eqToIso (pushforwardModules_eq_modulePushforward B S hS (f ≫ g)) := by
  rw [modulePushforwardCompIso]
  exact Functor.isoWhisker_eqToIso_trans_eqToIso_trans _ _ _ _

private theorem modulePullbackDataTopos_compIso_symm_unfold {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((modulePullbackDataTopos B S hS).compIso f g).symm =
      (eqToIso (toModulesHom_pullbackModules_eq_modulePullback B S hS (f ≫ g)) ≪≫
        (Adjunction.leftAdjointUniq (((modulePullbackAdjunction B S hS g).comp
          (modulePullbackAdjunction B S hS f)).ofNatIsoRight (modulePushforwardCompIso B S hS f g))
          (modulePullbackAdjunction B S hS (f ≫ g))).symm ≪≫
        eqToIso (congrArg₂ (fun (a : Modules.{u, u} B S hS Z.1 Z.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2)
          (b : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2) => a ⋙ b)
          (toModulesHom_pullbackModules_eq_modulePullback B S hS g).symm
          (toModulesHom_pullbackModules_eq_modulePullback B S hS f).symm)).symm :=
  rfl

private theorem pullbackModulesCompIso_symm_trans_unfold {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f g =
      (Adjunction.leftAdjointUniq ((RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHomComp B S hS f g)).ofNatIsoRight
          (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g)))
        ((RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g)).comp
          (RingedToposHom.pullbackAdjPushforwardModules
            (smallEtaleRingedToposHom B S hS f)))).symm ≪≫
      Adjunction.leftAdjointUniq (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHomComp B S hS f g))
        ((RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS (f ≫ g))).ofNatIsoRight
            (pushforwardModulesCompTransport B S hS f g).symm) :=
  rfl

/-- **The underived composition comparison**: the composition comparison of
`AlgebraicGeometry.Space.modulePullbackDataTopos`, the inverse images of `𝒪`-modules of Stacks
03LU read through the morphisms of small étale ringed topoi, is the inverse of the compositor of
Stacks 03D8 followed by the transport `AlgebraicGeometry.Space.pullbackModulesCompTransport`.

All the comparisons are comparisons of left adjoints, and the comparison of direct images of
Stacks 03LU is by definition the compositor of direct images followed by
`AlgebraicGeometry.Space.pushforwardModulesCompTransport`, read through the two spellings of the
direct images (`CategoryTheory.Adjunction.leftAdjointUniq_comp_transport_eq`). -/
theorem modulePullbackDataTopos_compIso_symm_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    ((modulePullbackDataTopos B S hS).compIso f g).symm =
      (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f g :=
  (modulePullbackDataTopos_compIso_symm_unfold B S hS f g).trans
    ((Adjunction.leftAdjointUniq_comp_transport_eq
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (f ≫ g)))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B S hS f g))
      (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g))
      (pushforwardModulesCompTransport B S hS f g)
      (modulePullbackAdjunction B S hS f) (modulePullbackAdjunction B S hS g)
      (modulePullbackAdjunction B S hS (f ≫ g)) (modulePushforwardCompIso B S hS f g)
      (toModulesHom_pullbackModules_eq_modulePullback B S hS f)
      (toModulesHom_pullbackModules_eq_modulePullback B S hS g)
      (toModulesHom_pullbackModules_eq_modulePullback B S hS (f ≫ g))
      _ (eqToIso (pushforwardModules_eq_modulePushforward B S hS f))
      (eqToIso (pushforwardModules_eq_modulePushforward B S hS g))
      (eqToIso (pushforwardModules_eq_modulePushforward B S hS (f ≫ g)))
      (modulePullbackAdjunction_eq_ofNatIsoLeft_eqToIso B S hS f)
      (modulePullbackAdjunction_eq_ofNatIsoLeft_eqToIso B S hS g)
      (modulePullbackAdjunction_eq_ofNatIsoLeft_eqToIso B S hS (f ≫ g))
      (isoWhisker_eqToIso_trans_modulePushforwardCompIso B S hS f g)).trans
      (pullbackModulesCompIso_symm_trans_unfold B S hS f g).symm)

/-! ### On homotopy categories -/

private theorem mapHomotopyCategory_compIso_symm_unfold {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((modulePullbackDataTopos B S hS).mapHomotopyCategory.compIso f g).symm =
      (Stacks.Homology.mapHomotopyCategoryIso ((modulePullbackDataTopos B S hS).compIso f g)
          (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm).symm :=
  rfl

private theorem pullbackMapHomotopyCompIso_unfold {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g) =
      Functor.mapHomotopyCategoryCompIso (RingedToposHom.pullbackModulesCompIso
        (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)).symm
        (ComplexShape.up ℤ) :=
  rfl

/-- The underived statement on homotopy categories: the inverse of the composition comparison of
the datum of degreewise pullbacks is the composition isomorphism of degreewise pullbacks along
morphisms of ringed topoi followed by the transport
`AlgebraicGeometry.Space.pullbackModulesCompTransport`, applied degreewise. -/
theorem modulePullbackDataTopos_mapHomotopyCategory_compIso_symm_eq
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((modulePullbackDataTopos B S hS).mapHomotopyCategory.compIso f g).symm =
      pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
          (ComplexShape.up ℤ) :=
  (mapHomotopyCategory_compIso_symm_unfold B S hS f g).trans
    ((Stacks.Homology.mapHomotopyCategoryIso_trans_compIso_symm_symm_eq
      (hF := modulePullbackDataTopos_additive B S hS f)
      (hG := modulePullbackDataTopos_additive B S hS g)
      (hH := modulePullbackDataTopos_additive B S hS (f ≫ g))
      (hK := smallEtaleRingedToposHom_comp_pullbackModules_additive B S hS f g)
      ((modulePullbackDataTopos B S hS).compIso f g)
      (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm (pullbackModulesCompTransport B S hS f g)
      (modulePullbackDataTopos_compIso_symm_eq B S hS f g)).trans
      (congrArg (· ≪≫ Stacks.Homology.mapHomotopyCategoryIso
        (pullbackModulesCompTransport B S hS f g) (ComplexShape.up ℤ))
        (pullbackMapHomotopyCompIso_unfold B S hS f g).symm))

/-! ### The derived statement -/

/-- The composition comparison
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_hom_app_comparison_compTransport`
in the spelling of the datum `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived`. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_app_comp_comparison
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : HomotopyCategory (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app
          (((derivedModulePullbackLeftDerived B S hS).Q Z).obj M) ≫
        ((derivedModulePullbackLeftDerived B S hS).α (f ≫ g)).app M =
      ((derivedModulePullbackLeftDerived B S hS).L f).map
          (((derivedModulePullbackLeftDerived B S hS).α g).app M) ≫
        ((derivedModulePullbackLeftDerived B S hS).α f).app
          (((modulePullbackDataTopos B S hS).mapHomotopyCategory.pull g).obj M) ≫
        ((derivedModulePullbackLeftDerived B S hS).Q X).map
          ((pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS f)
            (smallEtaleRingedToposHom B S hS g) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
            (ComplexShape.up ℤ)).hom.app M) :=
  smallEtaleDerivedModulePullbackCompIso_hom_app_comparison_compTransport B f g M

/-- **The composition comparison of the derived pullback datum is the inverse of the composition
isomorphism of Stacks 0D6D.** For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the
comparison `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`,
induced by the universal property of the left derived functor along `f ≫ g`, is the inverse of
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`.

Both are characterized at the images of complexes
(`CategoryTheory.PullbackData.LeftDerived.compHom_eq_of_app`), where they agree because the
underived comparisons do (`AlgebraicGeometry.Space.modulePullbackDataTopos_compIso_symm_eq`). -/
theorem smallEtaleDerivedPullbackData_compIso_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (smallEtaleDerivedPullbackData B S hS).compIso f g =
      (smallEtaleDerivedModulePullbackCompIso B S hS f g).symm :=
  congrArg Iso.symm (Iso.ext ((derivedModulePullbackLeftDerived B S hS).compHom_eq_of_app f g _
    (modulePullbackDataTopos_mapHomotopyCategory_compIso_symm_eq B S hS f g)
    (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comp_comparison B S hS f g)))

/-- **The composition comparison of the derived pullback datum is the inverse of the composition
isomorphism of Stacks 0D6D**, as the proposition
`AlgebraicGeometry.Space.SmallEtaleDerivedPullbackDataCompIsoEq`. -/
theorem smallEtaleDerivedPullbackDataCompIsoEq : SmallEtaleDerivedPullbackDataCompIsoEq B S hS :=
  fun f g => smallEtaleDerivedPullbackData_compIso_eq B S hS f g

end AlgebraicGeometry.Space

end
