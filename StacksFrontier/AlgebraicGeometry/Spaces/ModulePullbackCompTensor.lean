module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardModulesIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqCompOfNatIsoRight
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# Pullback of a tensor product along a composite of morphisms of algebraic spaces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` of a big fppf
site.  The inverse image of modules of Stacks 03LU carries the tensor product to the tensor
product, `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` (Stacks 03EL), and is compatible with composition,
`g^* ⋙ f^* ≅ (f ≫ g)^*` (Stacks 03LU).  This file proves that the two comparisons are compatible:
the comparison of Stacks 03EL for `f ≫ g` is the comparison for `g` pulled back along `f`,
followed by the comparison for `f`, read through the composition comparison in each place.

The composition law for the comparison of Stacks 03EL is known for morphisms of ringed topoi,
against the comparison of pullbacks attached to a comparison of the geometric direct images
(`Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`).  What is proved here is that the
composition comparison of Stacks 03LU for algebraic spaces,
`AlgebraicGeometry.Space.modulePullbackCompIso`, *is* that comparison of pullbacks, at the
comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of the small étale direct
images of Stacks 03G2, part (3).

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_eq_pullbackModulesCompIso`: the composition
  comparison of Stacks 03LU is the comparison of pullbacks of the modules development at the
  composition comparison of the small étale direct images.

Combined with `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`, the first result is the
compatibility of the comparison of Stacks 03EL with the composition comparison of Stacks 03LU.

## Implementation notes

Both comparisons of pullbacks are comparisons of left adjoints, so they agree as soon as the
comparisons of direct images they are induced by correspond; that reduction is
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp_eq_symm`.  The direct images
correspond on underlying sheaves of sets, where every identification of spellings is the
identity; that is `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso_comp_comparison`,
proved with the ringed topoi as variables, and it is applied here after the two transports along
equalities of functors that `AlgebraicGeometry.Space.modulePushforwardIso` and
`AlgebraicGeometry.Space.modulePushforwardCompIso` carry have been eliminated.  Unfolding those
transports at the concrete small étale ringed topoi instead does not terminate.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules (pushforwardModules pullbackAdjPushforwardModules)

/-- A comparison of composites transported along equalities `p_f`, `p_g`, `p_fg` of functors,
with the comparisons of a second presentation `R4` given by transports of isomorphisms
`i : R4 ≅ R2`, satisfies the compatibility of
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp_eq_symm` as soon as the
untransported data do. -/
theorem CategoryTheory.Functor.comp_hom_app_eq_of_eqToIso
    {CX CY CZ : Type*} [Category CX] [Category CY] [Category CZ]
    {R4f R2f Pf : CX ⥤ CY} {R4g R2g Pg : CY ⥤ CZ} {R4fg R2fg Pfg : CX ⥤ CZ}
    (i_f : R4f ≅ R2f) (i_g : R4g ≅ R2g) (i_fg : R4fg ≅ R2fg)
    (p_f : R2f = Pf) (p_g : R2g = Pg) (p_fg : R2fg = Pfg)
    (P2 : R2f ⋙ R2g ≅ R2fg) (C4 : R4f ⋙ R4g ≅ R4fg)
    (mf : R4f ≅ Pf) (mg : R4g ≅ Pg) (mfg : R4fg ≅ Pfg) (mc : Pf ⋙ Pg ≅ Pfg)
    (hmf : mf = i_f ≪≫ eqToIso p_f) (hmg : mg = i_g ≪≫ eqToIso p_g)
    (hmfg : mfg = i_fg ≪≫ eqToIso p_fg) (hmc : mc = Functor.compIsoCongr p_f p_g p_fg P2)
    (key : ∀ M, (R4g.map (i_f.hom.app M) ≫ i_g.hom.app (R2f.obj M)) ≫ P2.hom.app M =
      C4.hom.app M ≫ i_fg.hom.app M) (M : CX) :
    (R4g.map (mf.hom.app M) ≫ mg.hom.app (Pf.obj M)) ≫ mc.hom.app M =
      C4.hom.app M ≫ mfg.hom.app M := by
  subst hmf hmg hmfg hmc p_f p_g p_fg
  simpa [Functor.compIsoCongr] using key M

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- The composition comparison `smallToposMorphismTypeU_comp` of the small étale direct images of
Stacks 03G2, part (3), as a comparison of the direct images of the morphisms of ringed topoi
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom`, which is the shape the comparison of
pullbacks of the modules development consumes. -/
noncomputable abbrev smallEtaleCompPushforwardIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforward ⋙
        (smallEtaleRingedToposModulesHom B S hS g).toToposHom.pushforward ≅
      (smallEtaleRingedToposModulesHom B S hS (f ≫ g)).toToposHom.pushforward :=
  smallToposMorphismTypeU_comp B S hS f g

/-- The direct-image form of the structure map of
`AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom` is, on underlying sheaves of sets, the
structure map of the morphism of small étale ringed topoi of Stacks 03G8. -/
theorem fSharpSet_smallEtaleRingedToposModulesHom_eq_forgetRing (f : X ⟶ Y) :
    Stacks.Sheaves.RingedToposModules.fSharpSet (smallEtaleRingedToposModulesHom B S hS f) =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map (smallEtaleRingedToposHom B S hS f).fSharp :=
  RingedToposHom.ringFsharp_forget (smallEtaleRingedToposHom B S hS f)

/-- **Stacks 03G8, compatibility with composition, in the shape of the modules development**: the
composition comparison of the small étale direct images carries the composite structure map to
the structure map of the composite. -/
theorem fSharpSetComp_smallEtaleCompPushforwardIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.Sheaves.RingedToposModules.fSharpSetComp (smallEtaleRingedToposModulesHom B S hS f)
        (smallEtaleRingedToposModulesHom B S hS g) ≫
      (smallEtaleCompPushforwardIso B S hS f g).hom.app
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).ringSheaf =
    Stacks.Sheaves.RingedToposModules.fSharpSet
      (smallEtaleRingedToposModulesHom B S hS (f ≫ g)) := by
  have h1 := RingedToposHom.comp_fSharp_forget
    (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f)
  have h2 : (smallEtaleRingedTopos B S hS Z).forgetRing.map
      ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app
        (smallEtaleRingedTopos B S hS X).O) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) :=
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS Z.1) _ (smallToposMorphismTypeU_comp B S hS f g)
  have h3 := congrArg (fun m ↦ (smallEtaleRingedTopos B S hS Z).forgetRing.map m)
    (smallEtaleRingedToposHom_comp_fSharp B S hS f g)
  simp only [Functor.map_comp, h2, h1] at h3
  have e := Stacks.Sheaves.RingedToposModules.fSharpSetComp_eq
    (smallEtaleRingedToposModulesHom B S hS f) (smallEtaleRingedToposModulesHom B S hS g)
  rw [fSharpSet_smallEtaleRingedToposModulesHom_eq_forgetRing,
    fSharpSet_smallEtaleRingedToposModulesHom_eq_forgetRing] at e
  rw [e, fSharpSet_smallEtaleRingedToposModulesHom_eq_forgetRing]
  exact h3

/-- The comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` of direct images of sheaves of modules of the modules
development, at the composition comparison of the small étale direct images. -/
noncomputable abbrev smallEtalePushforwardModulesCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso
    (smallEtaleRingedToposModulesHom B S hS f) (smallEtaleRingedToposModulesHom B S hS g)
    (smallEtaleRingedToposModulesHom B S hS (f ≫ g)) (smallEtaleCompPushforwardIso B S hS f g)
    (fSharpSetComp_smallEtaleCompPushforwardIso B S hS f g)

/-- **The composition comparison of Stacks 03LU for direct images and that of the modules
development correspond** under the identification
`AlgebraicGeometry.Space.modulePushforwardIso` of the two direct images. -/
theorem modulePushforwardIso_comp_modulePushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    ((pushforwardModules (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposModulesHom B S hS g)).map
        ((modulePushforwardIso B S hS f).hom.app M) ≫
      (modulePushforwardIso B S hS g).hom.app ((modulePushforward B S hS f).obj M)) ≫
        (modulePushforwardCompIso B S hS f g).hom.app M =
      (smallEtalePushforwardModulesCompIso B S hS f g).hom.app M ≫
        (modulePushforwardIso B S hS (f ≫ g)).hom.app M :=
  Functor.comp_hom_app_eq_of_eqToIso
    (smallEtaleRingedToposHom B S hS f).pushforwardModulesIso
    (smallEtaleRingedToposHom B S hS g).pushforwardModulesIso
    (smallEtaleRingedToposHom B S hS (f ≫ g)).pushforwardModulesIso
    (pushforwardModules_eq_modulePushforward B S hS f)
    (pushforwardModules_eq_modulePushforward B S hS g)
    (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
    (pushforwardModulesCompAt B S hS f g) (smallEtalePushforwardModulesCompIso B S hS f g)
    (modulePushforwardIso B S hS f) (modulePushforwardIso B S hS g)
    (modulePushforwardIso B S hS (f ≫ g)) (modulePushforwardCompIso B S hS f g)
    (modulePushforwardIso_eq_eqToIso B S hS f)
    (modulePushforwardIso_eq_eqToIso B S hS g)
    (modulePushforwardIso_eq_eqToIso B S hS (f ≫ g))
    (modulePushforwardCompIso_eq_compIsoCongr B S hS f g)
    (fun N ↦ RingedToposHom.pushforwardModulesIso_comp_comparison _ _ _
      (smallEtaleCompPushforwardIso B S hS f g)
      (fSharpSetComp_smallEtaleCompPushforwardIso B S hS f g) _ N
      (moduleSheafFunctor_map_pushforwardModulesCompAt_hom_app B S hS f g N)) M

/-- `AlgebraicGeometry.Space.modulePullbackCompIso` unfolded to the comparison of left adjoints it
is defined as. -/
private theorem modulePullbackCompIso_eq_leftAdjointUniq_unfold (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackCompIso B S hS f g =
      Adjunction.leftAdjointUniq
        (((modulePullbackAdjunction B S hS g).comp
            (modulePullbackAdjunction B S hS f)).ofNatIsoRight
          (modulePushforwardCompIso B S hS f g)) (modulePullbackAdjunction B S hS (f ≫ g)) :=
  rfl

/-- `AlgebraicGeometry.Space.modulePullbackAdjunction` unfolded to the transport it is defined
as. -/
private theorem modulePullbackAdjunction_eq_ofNatIsoRight (f : X ⟶ Y) :
    modulePullbackAdjunction B S hS f =
      (pullbackAdjPushforwardModules (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposModulesHom B S hS f)).ofNatIsoRight (modulePushforwardIso B S hS f) :=
  rfl

/-- **The composition comparison of Stacks 03LU is the comparison of pullbacks of the modules
development.**  For `f : X ⟶ Y` and `g : Y ⟶ Z`, the comparison `g^* ⋙ f^* ≅ (f ≫ g)^*` is the
inverse of `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` at the morphisms of small
étale ringed topoi of Stacks 03G8 and the composition comparison of their direct images of
Stacks 03G2, part (3). -/
theorem modulePullbackCompIso_eq_pullbackModulesCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackCompIso B S hS f g =
      (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso
        (smallEtaleRingedToposModulesHom B S hS f) (smallEtaleRingedToposModulesHom B S hS g)
        (smallEtaleRingedToposModulesHom B S hS (f ≫ g)) (smallEtaleCompPushforwardIso B S hS f g)
        (fSharpSetComp_smallEtaleCompPushforwardIso B S hS f g)).symm := by
  rw [modulePullbackCompIso_eq_leftAdjointUniq_unfold,
    modulePullbackAdjunction_eq_ofNatIsoRight B S hS f,
    modulePullbackAdjunction_eq_ofNatIsoRight B S hS g,
    modulePullbackAdjunction_eq_ofNatIsoRight B S hS (f ≫ g)]
  exact Adjunction.leftAdjointUniq_ofNatIsoRight_comp_eq_symm _ _ _ _ _ _ _ _
    (modulePushforwardIso_comp_modulePushforwardCompIso B S hS f g)

end AlgebraicGeometry.Space

end
