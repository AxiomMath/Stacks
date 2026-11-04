module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages

/-!
# The higher-direct-image comparison on a pair of injective resolutions, in degree zero

Let `f : X ⟶ Y` be a morphism of ringed spaces and `M` a sheaf of `𝒪_X`-modules. Given an
injective resolution `I` of `M`, an injective resolution `J` of the underlying abelian sheaf of
`M` and a comparison `φ` of the two extending the identity, the degree-zero comparison
`Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso f 0`
between the direct image of `M` forgotten to abelian sheaves and the direct image of its
underlying abelian sheaf carries the class of a degree-zero cocycle of `f_* I` to the class of
its image under `φ` ([Stacks, Tag 01F1] (2)).

## Main results

* `rightDerivedZeroCompForgetIso_cycles`: for left exact `F`, `W` and `e : F ⋙ G ≅ T ⋙ W`, the
  canonical map of `W` into the degree-zero cycles of the complex of `J` is the canonical map of
  `F` into those of the complex of `I`, pushed through `G` and along any cocycle comparison
  induced by `φ`.
* `rightDerivedZeroCompForgetIso_cocycles`: the same statement on degree-zero homology.
* `rightDerived_modulePushforward_forget_iso_cocycles_zero`: the higher-direct-image comparison
  in degree zero carries the class of a cocycle to the class of its image under `φ`.

## Implementation notes

`CategoryTheory.InjectiveResolution.isoRightDerivedObj` has
`(HomologicalComplex.homologyFunctor _ _ 0).obj K` as an endpoint where
`HomologicalComplex.homologyπ` has `K.homology 0`; the two are definitionally but not
syntactically equal, so reassociations across that junction go through the private lemmas
`comp_assoc_inv_hom` and `glue_zero`, whose statements mention no complex.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.ModulePushforwardComparison

/-! ### Reassociations across the homology junction -/

/-- `(a ≫ b ≫ c.inv) ≫ c.hom = a ≫ b` for an isomorphism `c`. -/
private theorem comp_assoc_inv_hom {E : Type*} [Category* E] {V W Z Z' : E}
    (a : Z' ⟶ Z) (b : Z ⟶ W) (c : V ≅ W) : (a ≫ b ≫ c.inv) ≫ c.hom = a ≫ b := by
  simp

/-- If `t ≫ dJ = jt ≫ π`, `g ≫ jt = u ≫ c` and `a ≫ b ≫ u = 𝟙 _`, then
`a ≫ (b ≫ g ≫ t) ≫ dJ = c ≫ π`. -/
private theorem glue_zero {E : Type*} [Category* E] {P₁ P₂ P₃ P₄ P₅ P₆ Q : E}
    (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (g : P₃ ⟶ P₄) (t : P₄ ⟶ P₅) (dJ : P₅ ⟶ P₆)
    (u : P₃ ⟶ P₁) (jt : P₄ ⟶ Q) (π : Q ⟶ P₆) (c : P₁ ⟶ Q)
    (h1 : t ≫ dJ = jt ≫ π) (h2 : g ≫ jt = u ≫ c) (h3 : a ≫ b ≫ u = 𝟙 P₁) :
    a ≫ (b ≫ g ≫ t) ≫ dJ = c ≫ π := by
  have hlast : a ≫ b ≫ u ≫ c ≫ π = c ≫ π := by
    rw [← Category.assoc b, ← Category.assoc a, h3, Category.id_comp]
  simp only [Category.assoc]
  rw [h1, ← Category.assoc g, h2]
  simpa only [Category.assoc] using hlast

/-! ### The degree-zero comparison on a pair of injective resolutions -/

section Abstract

variable {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} {C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [HasInjectiveResolutions C₁] [Abelian C₂]
  [Abelian C₃] [HasInjectiveResolutions C₃] [Abelian C₄]
  (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (T : C₁ ⥤ C₃) (W : C₃ ⥤ C₄)
  [F.Additive] [G.Additive] [T.Additive] [W.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits W]
  (e : F ⋙ G ≅ T ⋙ W)

omit [HasInjectiveResolutions C₁] [HasInjectiveResolutions C₃] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits W] in
/-- Let `F` and `W` be left exact and `e : F ⋙ G ≅ T ⋙ W`. Given an injective resolution `I` of
`M`, an injective resolution `J` of `T.obj M` and a comparison `φ` of the image of `I` with `J`
extending the identity, any map `c` on degree-zero cycles induced by `φ` carries the canonical
map of `F`, pushed through `G`, to the canonical map of `W` read through `e`. -/
theorem rightDerivedZeroCompForgetIso_cycles {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    (c : G.obj (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles 0) ⟶
      ((W.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).cycles 0)
    (hc : c ≫ HomologicalComplex.iCycles
          ((W.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) 0 =
        G.map (HomologicalComplex.iCycles
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0) ≫
          e.hom.app (I.cocomplex.X 0) ≫ W.map (φ.f 0)) :
    e.hom.app M ≫ J.toRightDerivedZero' W = G.map (I.toRightDerivedZero' F) ≫ c := by
  have hnat : G.map (I.toRightDerivedZero' F ≫ HomologicalComplex.iCycles
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0) ≫
        e.hom.app (I.cocomplex.X 0) =
      e.hom.app M ≫ W.map (T.map (I.ι.f 0)) := by
    rw [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    exact e.hom.naturality (I.ι.f 0)
  refine (cancel_mono (HomologicalComplex.iCycles
    ((W.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) 0)).1 ?_
  rw [Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles, Category.assoc,
    hc, ← Category.assoc, ← G.map_comp, ← Category.assoc, hnat, Category.assoc,
    ← W.map_comp]
  exact (congrArg (fun g => e.hom.app M ≫ W.map g) hφ).symm

omit [G.Additive] in
/-- The comparison `F.rightDerived 0 ⋙ G ≅ T ⋙ W.rightDerived 0` built from `e` and the two
canonical isomorphisms of left exact functors with their zeroth right derived functors sends the
class of a degree-zero cocycle of the complex of `I` to the class of its image under any cocycle
comparison `c` induced by `φ`. -/
theorem rightDerivedZeroCompForgetIso_cocycles {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0)
    (c : G.obj (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles 0) ⟶
      ((W.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).cycles 0)
    (hc : c ≫ HomologicalComplex.iCycles
          ((W.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) 0 =
        G.map (HomologicalComplex.iCycles
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0) ≫
          e.hom.app (I.cocomplex.X 0) ≫ W.map (φ.f 0)) :
    G.map (HomologicalComplex.homologyπ
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0 ≫
        (I.isoRightDerivedObj F 0).inv) ≫
        (Functor.isoWhiskerRight F.rightDerivedZeroIsoSelf G ≪≫ e ≪≫
          Functor.isoWhiskerLeft T W.rightDerivedZeroIsoSelf.symm).hom.app M ≫
        (J.isoRightDerivedObj W 0).hom =
      c ≫ HomologicalComplex.homologyπ
        ((W.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) 0 := by
  have hW : W.toRightDerivedZero.app (T.obj M) ≫ (J.isoRightDerivedObj W 0).hom =
      J.toRightDerivedZero' W ≫ (CochainComplex.isoHomologyπ₀
        ((W.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)).hom := by
    rw [J.toRightDerivedZero_eq W]
    exact comp_assoc_inv_hom _ _ _
  have hw : I.toRightDerivedZero' F ≫
      ((CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            I.cocomplex)).hom ≫ (I.isoRightDerivedObj F 0).inv) ≫
        F.rightDerivedZeroIsoSelf.hom.app M = 𝟙 _ := by
    have h := Functor.rightDerivedZeroIsoSelf_inv_hom_id_app F M
    rw [I.toRightDerivedZero_eq F] at h
    rwa [← Category.assoc]
  have hv : ((CochainComplex.isoHomologyπ₀ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex)).hom ≫ (I.isoRightDerivedObj F 0).inv) ≫
        F.rightDerivedZeroIsoSelf.hom.app M ≫ I.toRightDerivedZero' F = 𝟙 _ := by
    rw [← Category.assoc, ← IsIso.inv_eq_of_hom_inv_id hw]
    exact IsIso.inv_hom_id _
  have hfold : G.map ((CochainComplex.isoHomologyπ₀
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).hom ≫
        (I.isoRightDerivedObj F 0).inv) ≫
        G.map (F.rightDerivedZeroIsoSelf.hom.app M) ≫
        G.map (I.toRightDerivedZero' F) = 𝟙 _ := by
    rw [← G.map_comp, ← G.map_comp, hv, G.map_id]
  exact glue_zero _ (G.map (F.rightDerivedZeroIsoSelf.hom.app M)) (e.hom.app M)
    (W.toRightDerivedZero.app (T.obj M)) (J.isoRightDerivedObj W 0).hom
    (G.map (I.toRightDerivedZero' F)) (J.toRightDerivedZero' W) _ c hW
    (rightDerivedZeroCompForgetIso_cycles F G T W e I J φ hφ c hc) hfold

end Abstract

/-! ### The direct image of a sheaf of modules on a pair of injective resolutions -/

section Pushforward

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Let `I` be an injective resolution of a sheaf of modules `M`, `J` an injective resolution of
its underlying abelian sheaf and `φ` a comparison of the two extending the identity. The
degree-zero comparison `rightDerived_modulePushforward_forget_iso f 0` sends the class of a
degree-zero cocycle of `f_* I` to the class of its image under any cocycle comparison `c` induced
by `φ`. -/
theorem rightDerived_modulePushforward_forget_iso_cocycles_zero
    (M : SheafOfModules.{u} (structureSheafRing X)) (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf (structureSheafRing X)).obj M))
    (φ : ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : (SheafOfModules.toSheaf (structureSheafRing X)).map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    let E := modulePushforward f
    let G := SheafOfModules.toSheaf (structureSheafRing Y)
    let A := (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)
    let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    ∀ (c : G.obj (K.cycles 0) ⟶ L.cycles 0)
      (_ : c ≫ L.iCycles 0 = G.map (K.iCycles 0) ≫ A.map (φ.f 0)),
      G.map (K.homologyπ 0 ≫ (I.isoRightDerivedObj E 0).inv) ≫
          (rightDerived_modulePushforward_forget_iso f 0).hom.app M ≫
          (J.isoRightDerivedObj A 0).hom =
        c ≫ L.homologyπ 0 := by
  intro _ _ _ _ _ c hc
  have hid : (modulePushforwardCompToSheafIso f).hom.app (I.cocomplex.X 0) ≫
        ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).map (φ.f 0) =
      ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).map (φ.f 0) :=
    Category.id_comp _
  exact rightDerivedZeroCompForgetIso_cocycles (modulePushforward f)
    (SheafOfModules.toSheaf (structureSheafRing Y)) (SheafOfModules.toSheaf (structureSheafRing X))
    ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier))
    (modulePushforwardCompToSheafIso f) I J φ hφ c
    (hc.trans (congrArg (fun g => (SheafOfModules.toSheaf (structureSheafRing Y)).map
      (HomologicalComplex.iCycles
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) 0) ≫ g) hid.symm))

end Pushforward

end Stacks.Cohomology.ModulePushforwardComparison

end
