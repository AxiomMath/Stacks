module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImageUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInclusionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalMapAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMoveRestriction

/-!
# The conormal inclusions restrict along a morphism of first order thickenings

Let `(h, h') : (Z₂ ⊂ X₂) ⟶ (Z ⊂ X)` be a morphism of first order thickenings of algebraic spaces,
`i₂ ≫ h' = h ≫ i`.  On the small étale site of `Z` there are two ways from the conormal module
`𝒞_{Z/X}` to the sheaf of sets `h_*(i₂^{-1}𝒪_{X₂})`:

* the transpose `𝒞_{Z/X} ⟶ h_*𝒞_{Z₂/X₂}` of the conormal map of the square
  ([Stacks Project, Tag 04CP]) followed by the direct image of the inclusion
  `𝒞_{Z₂/X₂} ⟶ i₂^{-1}𝒪_{X₂}`;
* the inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` followed by the transported comorphism
  `i^{-1}𝒪_X ⟶ h_*(i₂^{-1}𝒪_{X₂})` of the square.

`AlgebraicGeometry.Space.conormalSetInclusion_restriction` proves that they agree.  This is the
input on conormal modules of the restriction of the action of [Stacks Project, Tag 061C].

## Implementation notes

The direct image along `i` is faithful on sheaves of sets and the unit `𝓘_X ⟶ i_*i^*𝓘_X` is an
isomorphism for a first order thickening, so the equation is checked on the image of a section
of `𝓘_X`.  There the two sides are computed separately: the conormal side
(`AlgebraicGeometry.Space.pushforward_conormalSetInclusion_restriction_conormal_app`) and the
ring side (`AlgebraicGeometry.Space.pushforward_conormalSetInclusion_restriction_ring_app`).

The composite `h ≫ i` has two spellings, one in `AlgebraicSpaces B S hS` (that of the comparison
of iterated direct images) and one in the full subcategory it unfolds to (that of the square).
Identifying the values of the comorphism read in the direct images along the two spellings is a
kernel timeout.  So the ring side is taken from
`AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening_algebraicSpaces`, the
defining identity of the transported comorphism restated, at variables, in the
`AlgebraicSpaces B S hS` spelling; and composites of morphisms of sheaves are evaluated on sections
with their factors given explicitly.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Cancelling the first factor of a composite of natural isomorphisms evaluated at an object
and followed by a morphism. -/
theorem _root_.CategoryTheory.Iso.inv_app_comp_trans_hom_app_comp {𝒜 ℬ : Type*} [Category 𝒜]
    [Category ℬ] {F₁ F₂ F₃ : 𝒜 ⥤ ℬ} (A : F₁ ≅ F₂) (R : F₂ ≅ F₃) (M : 𝒜) {N : ℬ}
    (k : F₃.obj M ⟶ N) :
    A.inv.app M ≫ (A ≪≫ R).hom.app M ≫ k = R.hom.app M ≫ k := by
  simp

/-- The transpose along `f^* ⊣ f_*` of a morphism of modules, evaluated on a local section: the
unit followed by the direct image of the morphism. -/
theorem modulePullbackAdjunction_homEquiv_val_app {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (g : (modulePullback B S hS f).obj M ⟶ N) (V : (SmallEtale B S hS Y.1)ᵒᵖ) (t : M.val.obj V) :
    (((modulePullbackAdjunction B S hS f).homEquiv M N) g).val.app V t =
      ((modulePushforward B S hS f).map g).val.app V
        (((modulePullbackAdjunction B S hS f).unit.app M).val.app V t) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- A morphism into the iterated direct image followed by the comparison of [Stacks Project, Tag
03LU], evaluated on a local section: the comparison of [Stacks Project, Tag 03G2], part (3), applied
to the value of the morphism. -/
private theorem modulePushforwardCompIso_hom_app_comp_val_app {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules.{u, u} B S hS X.1 X.2) {M : Modules.{u, u} B S hS Z.1 Z.2}
    (a : M ⟶ (modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj N))
    (V : (SmallEtale B S hS Z.1)ᵒᵖ) (y : M.val.obj V) :
    (a ≫ ((modulePushforwardCompIso B S hS f g).hom.app N)).val.app V y =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj N)).hom.app V
        (a.val.app V y) :=
  (modules_comp_val_app B S hS _ _ V y).trans
    (modulePushforwardCompIso_hom_app_val_app B S hS f g N V _)

universe uu vv in
/-- A morphism of sheaves of rings on a section, read on underlying sheaves of sets.  Stated
over an abstract site so that the kernel checks the `rfl` once. -/
theorem sheafCompose_forget_map_hom_app_apply_ringCat {Cc : Type uu} [Category.{vv} Cc]
    {Jc : GrothendieckTopology Cc} {A Bb : Sheaf Jc RingCat.{u}} (a : A ⟶ Bb) (V : Ccᵒᵖ)
    (z : ToType (A.obj.obj V)) :
    ((sheafCompose Jc (CategoryTheory.forget RingCat.{u})).map a).hom.app V z = a.hom.app V z :=
  rfl

section Ring

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (c : X ⟶ W)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)

/-- The comparison `(f ≫ g)_*O ⟶ g_*(f_*O)` of iterated direct images of a sheaf of rings is,
on underlying sheaves of sets, the comparison of [Stacks Project, Tag 03G2], part (3). -/
theorem sheafCompose_map_pushforwardRingSheafCompInv {V₁ V₂ V₃ : AlgebraicSpaces B S hS}
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS V₃.1) (CategoryTheory.forget RingCat.{u})).map
        (pushforwardRingSheafCompInv B S hS f g O) =
      (smallToposMorphismTypeU_comp B S hS f g).inv.app
        ((sheafCompose (SmallEtale.topology B S hS V₁.1) (CategoryTheory.forget RingCat.{u})).obj
          O) := by
  simp only [pushforwardRingSheafCompInv]
  rfl

/-- `AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening` with the
composite `e₀ ≫ j` taken in `AlgebraicSpaces B S hS`, the spelling of the comparison of iterated
direct images that follows it. -/
theorem ringUnit_comp_map_restrictedSharpThroughThickening_algebraicSpaces :
    ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheaf B S hS W) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc) =
      structureSharpThroughThickeningAt B S hS Z c (@CategoryStruct.comp
          (AlgebraicSpaces B S hS) _ _ _ _ e₀ (subspaceInclusion B S hS W W₀)) hc ≫
        pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc

/-- `AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening` on underlying
sheaves of sets, with the unit of `j^{-1} ⊣ j_*` written through the morphism of topoi of
[Stacks Project, Tag 03G2], part (3). -/
theorem sheafCompose_map_ringUnit_comp_restrictedSharpThroughThickening :
    (sheafCompose (SmallEtale.topology B S hS W.1) (CategoryTheory.forget RingCat.{u})).map
        (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheaf B S hS W)) ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)) =
    (sheafCompose (SmallEtale.topology B S hS W.1) (CategoryTheory.forget RingCat.{u})).map
        (structureSharpThroughThickeningAt B S hS Z c
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀
              (subspaceInclusion B S hS W W₀)) hc) ≫
      (smallToposMorphismTypeU_comp B S hS e₀ (subspaceInclusion B S hS W W₀)).inv.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) :=
  (congrArg (_ ≫ ·) (ringSheafMap_pullbackRingSheafMap _ _
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)).symm).trans
    ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (sheafCompose (SmallEtale.topology B S hS W.1)
          (CategoryTheory.forget RingCat.{u})).map
        (ringUnit_comp_map_restrictedSharpThroughThickening_algebraicSpaces B S hS Z W₀ c e₀
          hc)).trans
      ((Functor.map_comp _ _ _).trans
        (congrArg (_ ≫ ·) (sheafCompose_map_pushforwardRingSheafCompInv B S hS e₀
          (subspaceInclusion B S hS W W₀) _)))))

/-- The unit `𝒪_W ⟶ j_*j^{-1}𝒪_W` of the inclusion of a closed subspace, on underlying sheaves
of sets, written through the morphism of topoi of [Stacks Project, Tag 03G2], part (3). -/
theorem sheafCompose_map_thickeningRingUnit_eq :
    (sheafCompose (SmallEtale.topology B S hS W.1) (CategoryTheory.forget RingCat.{u})).map
        (thickeningRingUnit B S hS W₀) =
      (sheafCompose (SmallEtale.topology B S hS W.1) (CategoryTheory.forget RingCat.{u})).map
        (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheaf B S hS W)) :=
  rfl

/-- `AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening` on underlying
sheaves of sets: the unit `𝒪_W ⟶ j_*j^{-1}𝒪_W` followed by the direct image of the transported
comorphism is the comorphism read in the direct image along `e₀ ≫ j`, followed by the comparison
`(e₀ ≫ j)_* ≅ j_*(e₀)_*` of [Stacks Project, Tag 03G2], part (3). -/
theorem sheafCompose_map_thickeningRingUnit_comp_restrictedSharpThroughThickening :
    (sheafCompose (SmallEtale.topology B S hS W.1) (CategoryTheory.forget RingCat.{u})).map
        (thickeningRingUnit B S hS W₀) ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)) =
    (sheafCompose (SmallEtale.topology B S hS W.1) (CategoryTheory.forget RingCat.{u})).map
        (structureSharpThroughThickeningAt B S hS Z c
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ e₀
              (subspaceInclusion B S hS W W₀)) hc) ≫
      (smallToposMorphismTypeU_comp B S hS e₀ (subspaceInclusion B S hS W W₀)).inv.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) :=
  (congrArg (· ≫ _) (sheafCompose_map_thickeningRingUnit_eq B S hS W₀)).trans
    (sheafCompose_map_ringUnit_comp_restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc)

end Ring

section Square

variable {X₂ X : AlgebraicSpaces B S hS} (Z₂ : ClosedSubspaces B S hS X₂.1)
  (Z : ClosedSubspaces B S hS X.1) (h' : X₂ ⟶ X)
  (h : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X₂ Z₂ ≫ h' = h ≫ subspaceInclusion B S hS X Z)
  (hZ₂ : IsFirstOrderThickening B S hS X₂ Z₂.1) (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- The unit `𝓘_X ⟶ i_*i^*𝓘_X` followed by the direct image of the conormal inclusion is the
unit `𝒪_X ⟶ i_*i^{-1}𝒪_X` on the defining ideal, read on underlying sheaves of sets. -/
theorem pushforward_conormalSetInclusion_unit_app (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj V) :
    ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (conormalSetInclusion B S hS Z hZ)).hom.app V
        (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app V t) =
      ((sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
        (thickeningRingUnit B S hS Z)).hom.app V ((definingIdealSheaf B S hS X Z).ι.val.app V t) :=
  (map_conormalSetInclusion_unit B S hS Z hZ V t).trans
    (sheafCompose_forget_map_hom_app_apply_ringCat (thickeningRingUnit B S hS Z) V _).symm

/-- `sheafCompose_map_thickeningRingUnit_comp_restrictedSharpThroughThickening`
for the square `i₂ ≫ h' = h ≫ i`, on a section of `𝒪_X`. -/
theorem pushforward_restrictedSharpThroughThickening_thickeningRingUnit_app
    (V : (SmallEtale B S hS X.1)ᵒᵖ) (x : ToType ((structureRingSheaf B S hS X).obj.obj V)) :
    ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq))).hom.app V
      (((sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
          (thickeningRingUnit B S hS Z)).hom.app V x) =
    ((smallToposMorphismTypeU_comp B S hS h (subspaceInclusion B S hS X Z)).inv.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))).hom.app V
      (((sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
        (structureSharpThroughThickeningAt B S hS Z₂ h'
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h
              (subspaceInclusion B S hS X Z)) hsq)).hom.app V x) :=
  (setSheaf_comp_hom_app_apply ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).map (thickeningRingUnit B S hS Z))
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq))) V x).symm.trans
    ((setSheafHom_congr_app_apply
      (sheafCompose_map_thickeningRingUnit_comp_restrictedSharpThroughThickening B S hS Z₂ Z
        h' h hsq) V x).trans (setSheaf_comp_hom_app_apply
          ((sheafCompose (SmallEtale.topology B S hS X.1) (CategoryTheory.forget RingCat.{u})).map
              (structureSharpThroughThickeningAt B S hS Z₂ h'
            (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h
                (subspaceInclusion B S hS X Z)) hsq))
          ((smallToposMorphismTypeU_comp B S hS h (subspaceInclusion B S hS X Z)).inv.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))) V x))

/-- **The ring side of the restriction of the conormal inclusions**, on a section `t` of the
defining ideal `𝓘_X`: the unit `𝓘_X ⟶ i_*i^*𝓘_X`, the direct image of the conormal inclusion and
the direct image of the transported comorphism `σ` of the square take `t` to the comorphism of
`h'` read through the thickening, evaluated at `t`, through the comparison of iterated direct
images. -/
theorem pushforward_conormalSetInclusion_restriction_ring_app (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj V) :
    ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq))).hom.app V
      (((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (conormalSetInclusion B S hS Z hZ)).hom.app V
        (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app V t)) =
    ((smallToposMorphismTypeU_comp B S hS h (subspaceInclusion B S hS X Z)).inv.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))).hom.app V
      ((structureSharpThroughThickeningAt B S hS Z₂ h'
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h
            (subspaceInclusion B S hS X Z)) hsq).hom.app V
        ((definingIdealSheaf B S hS X Z).ι.val.app V t)) :=
  (congrArg (((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq))).hom.app V)
      (pushforward_conormalSetInclusion_unit_app B S hS Z hZ V t)).trans
    ((pushforward_restrictedSharpThroughThickening_thickeningRingUnit_app B S hS Z₂ Z h' h hsq V
      _).trans (congrArg (((smallToposMorphismTypeU_comp B S hS h
        (subspaceInclusion B S hS X Z)).inv.app
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))).hom.app V)
      (sheafCompose_forget_map_hom_app_apply_ringCat _ V _)))

/-- **The conormal side of the restriction of the conormal inclusions**, on a section `t` of the
defining ideal `𝓘_X`: the unit `𝓘_X ⟶ i_*i^*𝓘_X`, the direct image of the transpose of the
conormal map `γ` of the square and the iterated direct image of the conormal inclusion of `Z₂`
take `t` to the comorphism of `h'` read through the thickening, evaluated at `t`, through the
comparison of iterated direct images. -/
theorem pushforward_conormalSetInclusion_restriction_conormal_app
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj V) :
    ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        ((smallToposMorphismTypeU B S hS h).pushforward.map
          (conormalSetInclusion B S hS Z₂ hZ₂))).hom.app V
      (((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
          ((modulePullbackAdjunction B S hS h).homEquiv
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules) (conormalModule B S hS X₂ Z₂)
            (conormalMap B S hS Z₂ Z h' h hsq)))).hom.app V
        (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app V t)) =
    ((smallToposMorphismTypeU_comp B S hS h (subspaceInclusion B S hS X Z)).inv.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))).hom.app V
      ((structureSharpThroughThickeningAt B S hS Z₂ h'
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h
            (subspaceInclusion B S hS X Z)) hsq).hom.app V
        ((definingIdealSheaf B S hS X Z).ι.val.app V t)) := by
  -- the conormal side
  have e3 := pushforward_conormalSetInclusion_homEquiv_trans B S hS Z₂ Z h' h hsq hZ₂
    (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h (subspaceInclusion B S hS X Z)) hsq V t
  have e6 := (congrArg (fun φ ↦ (modulePullbackCompIso B S hS h
      (subspaceInclusion B S hS X Z)).inv.app (definingIdealSheaf B S hS X Z).toSheafOfModules ≫ φ)
      (conormalMap_eq_trans_hom_app_comp B S hS Z₂ Z h' h hsq)).trans
    (Iso.inv_app_comp_trans_hom_app_comp _ _ _ _)
  have e7a := (congrArg ((modulePullbackAdjunction B S hS
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h
          (subspaceInclusion B S hS X Z))).homEquiv (definingIdealSheaf B S hS X Z).toSheafOfModules
        ((modulePullback B S hS (subspaceInclusion B S hS X₂ Z₂)).obj
          (definingIdealSheaf B S hS X₂ Z₂).toSheafOfModules)) e6.symm).trans
    (homEquiv_modulePullbackCompIso_inv_app_comp B S hS h (subspaceInclusion B S hS X Z)
      (definingIdealSheaf B S hS X Z).toSheafOfModules (conormalModule B S hS X₂ Z₂)
      (conormalMap B S hS Z₂ Z h' h hsq))
  have e78 := ((modules_val_app_congr B S hS
    (M := (definingIdealSheaf B S hS X Z).toSheafOfModules)
    (N := (modulePushforward B S hS (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h
        (subspaceInclusion B S hS X Z))).obj
      ((modulePullback B S hS (subspaceInclusion B S hS X₂ Z₂)).obj
        (definingIdealSheaf B S hS X₂ Z₂).toSheafOfModules)) e7a V t).trans
    (modulePushforwardCompIso_hom_app_comp_val_app B S hS h (subspaceInclusion B S hS X Z)
      (conormalModule B S hS X₂ Z₂) _ V t)).trans
    (congrArg (fun y ↦ ((smallToposMorphismTypeU_comp B S hS h
      (subspaceInclusion B S hS X Z)).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS))).obj
          (conormalModule B S hS X₂ Z₂))).hom.app V y)
      (modulePullbackAdjunction_homEquiv_val_app B S hS _ _ _ _ V t))
  have e10 := congrArg (((smallToposMorphismTypeU B S hS
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h
          (subspaceInclusion B S hS X Z))).pushforward.map
        (conormalSetInclusion B S hS Z₂ hZ₂)).hom.app V) e78
  have e11 := e10.symm.trans e3
  have e12 := ((setSheaf_comp_hom_app_apply _ _ V _).symm.trans
    ((setSheafHom_congr_app_apply
      ((smallToposMorphismTypeU_comp B S hS h (subspaceInclusion B S hS X Z)).hom.naturality
        (conormalSetInclusion B S hS Z₂ hZ₂)) V _).trans
      (setSheaf_comp_hom_app_apply _ _ V _))).trans e11
  have e13 := (Sheaf.iso_inv_hom_app_apply
    ((smallToposMorphismTypeU_comp B S hS h (subspaceInclusion B S hS X Z)).app
      ((sheafCompose (SmallEtale.topology B S hS
          (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
              (CategoryTheory.forget RingCat.{u})).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))) V _).symm.trans
    (congrArg (((smallToposMorphismTypeU_comp B S hS h (subspaceInclusion B S hS X Z)).app
      ((sheafCompose (SmallEtale.topology B S hS
          (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
              (CategoryTheory.forget RingCat.{u})).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))).inv.hom.app V)
      e12)
  exact e13

/-- **The conormal inclusions restrict along a morphism of first order thickenings**, as
sheaves of sets on the small étale site of `Z`: for a square `i₂ ≫ h' = h ≫ i`, the transpose
`𝒞_{Z/X} ⟶ h_*𝒞_{Z₂/X₂}` of the conormal map followed by the direct image of the inclusion
`𝒞_{Z₂/X₂} ⟶ i₂^{-1}𝒪_{X₂}` is the inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` followed by the transported
comorphism `i^{-1}𝒪_X ⟶ h_*(i₂^{-1}𝒪_{X₂})` of the square. -/
theorem conormalSetInclusion_restriction :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
        ((modulePullbackAdjunction B S hS h).homEquiv
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
            (definingIdealSheaf B S hS X Z).toSheafOfModules) (conormalModule B S hS X₂ Z₂)
          (conormalMap B S hS Z₂ Z h' h hsq)) ≫
      (smallToposMorphismTypeU B S hS h).pushforward.map (conormalSetInclusion B S hS Z₂ hZ₂) =
    conormalSetInclusion B S hS Z hZ ≫
      (sheafCompose (SmallEtale.topology B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).map
        (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) := by
  have := (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2).faithful
  have hI :=
    (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS _ Z.2.2 _).1
      (essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening B S hS Z hZ)
  refine (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map_injective
    ?_
  refine ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).mapIso
    (@asIso _ _ _ _ ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
      (definingIdealSheaf B S hS X Z).toSheafOfModules) hI)).cancel_iso_hom_left _ _ |>.1 ?_
  refine Sheaf.hom_ext_sections
    fun V (t : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj V) ↦ ?_
  refine (setSheaf_comp_hom_app_apply _ _ V _).trans
    (Eq.trans ?_ (setSheaf_comp_hom_app_apply _ _ V _).symm)
  refine (setSheafHom_congr_app_apply (Functor.map_comp _ _ _) V _).trans
    (Eq.trans ?_ (setSheafHom_congr_app_apply (Functor.map_comp _ _ _) V _).symm)
  refine (setSheaf_comp_hom_app_apply _ _ V _).trans
    (Eq.trans ?_ (setSheaf_comp_hom_app_apply _ _ V _).symm)
  exact (pushforward_conormalSetInclusion_restriction_conormal_app B S hS Z₂ Z h' h hsq hZ₂ V
    t).trans (pushforward_conormalSetInclusion_restriction_ring_app B S hS Z₂ Z h' h hsq hZ V
        t).symm

/-- The transpose along `h^* ⊣ h_*` on underlying sheaves of sets does not depend on how its
source is written: for `A = A'` and heterogeneously equal `γ`, `γ'`, as a heterogeneous
equality.  Stated with the equation explicit, so that `AlgebraicGeometry.Space.conormalModule`
and its unfolding are identified once, by a propositional equation, and never inside a value. -/
theorem moduleSheafFunctor_map_homEquiv_comp_heq
    {A A' : Modules.{u, u} B S hS Z.1.toFunctor Z.2.1} (hA : A = A')
    {N : Modules.{u, u} B S hS Z₂.1.toFunctor Z₂.2.1}
    (γ : (modulePullback B S hS h).obj A ⟶ N) (γ' : (modulePullback B S hS h).obj A' ⟶ N)
    (hγ : HEq γ γ')
    {T : Sheaf (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
      (Type u)}
    (k : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj
              ((modulePushforward B S hS h).obj N) ⟶ T) :
    HEq ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
              ((modulePullbackAdjunction B S hS h).homEquiv A N γ) ≫ k)
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
              ((modulePullbackAdjunction B S hS h).homEquiv A' N γ') ≫ k) := by
  subst hA
  obtain rfl := eq_of_heq hγ
  rfl

/-- `AlgebraicGeometry.Space.conormalSetInclusion_restriction` with the source of the transpose
written as the conormal module `𝒞_{Z/X}`, the spelling of the derivations of
[Stacks Project, Tag 0619] it is used with. -/
theorem conormalSetInclusion_restriction_conormalModule :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
        ((modulePullbackAdjunction B S hS h).homEquiv (conormalModule B S hS X Z)
          (conormalModule B S hS X₂ Z₂) (conormalMap B S hS Z₂ Z h' h hsq)) ≫
      (smallToposMorphismTypeU B S hS h).pushforward.map (conormalSetInclusion B S hS Z₂ hZ₂) =
    conormalSetInclusion B S hS Z hZ ≫
      (sheafCompose (SmallEtale.topology B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).map
        (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) :=
  eq_of_heq ((moduleSheafFunctor_map_homEquiv_comp_heq B S hS Z₂ Z h
      (conormalModule_eq B S hS X Z) (conormalMap B S hS Z₂ Z h' h hsq)
      (conormalMap B S hS Z₂ Z h' h hsq) HEq.rfl
      ((smallToposMorphismTypeU B S hS h).pushforward.map
        (conormalSetInclusion B S hS Z₂ hZ₂))).trans
    (heq_of_eq (conormalSetInclusion_restriction B S hS Z₂ Z h' h hsq hZ₂ hZ)))

end Square

/-- A morphism of modules on a local section, in the two ways of applying its components. -/
theorem modulesHom_val_app_hom_eq {Y : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (a : M ⟶ N) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (t : M.val.obj U) : (a.val.app U).hom t = a.val.app U t :=
  rfl

section Target

variable {X₂ X W : AlgebraicSpaces B S hS} (Z₂ : ClosedSubspaces B S hS X₂.1)
  (Z : ClosedSubspaces B S hS X.1) (W₀ : ClosedSubspaces B S hS W.1) (h' : X₂ ⟶ X)
  (h : (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (hsq : subspaceInclusion B S hS X₂ Z₂ ≫ h' = h ≫ subspaceInclusion B S hS X Z)
  (hZ₂ : IsFirstOrderThickening B S hS X₂ Z₂.1) (hZ : IsFirstOrderThickening B S hS X Z.1)

/-- The inclusion of the ideal of values on the small étale site of `W₀`, on sections: the
direct image along `e₀` of the conormal inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` of sheaves of sets. -/
theorem restrictedSquareZeroValues_ι_eq_conormalSetInclusion
    {V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (m : ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)).val.obj V) :
    (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι m =
      ((smallToposMorphismTypeU B S hS e₀).pushforward.map
        (conormalSetInclusion B S hS Z hZ)).hom.app V m :=
  (restrictedSquareZeroValues_ι B S hS Z W₀ e₀ hZ m).trans
    ((pullbackModuleMap_val_app_apply (SmallEtale.topology B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
        (smallToposMorphismTypeU B S hS e₀).pushforward _ (conormalInverseImageι B S hS Z hZ) V
        m).trans
      (setSheafHom_congr_app_apply (congrArg (smallToposMorphismTypeU B S hS e₀).pushforward.map
        (moduleSheafFunctor_map_conormalInverseImageι B S hS Z hZ)) V m))

/-- The comparison `g_*(f_*O) ⟶ (f ≫ g)_*O` of iterated direct images of a sheaf of rings is,
on underlying sheaves of sets, the comparison of [Stacks Project, Tag 03G2], part (3). -/
theorem sheafCompose_map_pushforwardRingSheafCompHom {V₁ V₂ V₃ : AlgebraicSpaces B S hS}
    (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃) (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS V₃.1) (CategoryTheory.forget RingCat.{u})).map
        (pushforwardRingSheafCompHom B S hS f g O) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((sheafCompose (SmallEtale.topology B S hS V₁.1) (CategoryTheory.forget RingCat.{u})).obj
          O) := by
  simp only [pushforwardRingSheafCompHom, Functor.map_comp,
    sheafCompose_map_pullbackRingSheafComp_hom]
  rfl

/-- **R3 on sheaves of sets on the small étale site of `W₀`**:
`AlgebraicGeometry.Space.conormalSetInclusion_restriction` pushed forward along `e₀` and read
through the comparison `(e₀)_*h_* ≅ (h ≫ e₀)_*` of [Stacks Project, Tag 03G2], part (3). -/
theorem pushforward_conormalSetInclusion_restriction :
    (smallToposMorphismTypeU B S hS e₀).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
          ((modulePullbackAdjunction B S hS h).homEquiv (conormalModule B S hS X Z)
            (conormalModule B S hS X₂ Z₂) (conormalMap B S hS Z₂ Z h' h hsq))) ≫
      (smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS))).obj
          (conormalModule B S hS X₂ Z₂)) ≫
      (smallToposMorphismTypeU B S hS
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)).pushforward.map
        (conormalSetInclusion B S hS Z₂ hZ₂) =
    (smallToposMorphismTypeU B S hS e₀).pushforward.map (conormalSetInclusion B S hS Z hZ) ≫
      (smallToposMorphismTypeU B S hS e₀).pushforward.map
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq)) ≫
      (smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))) := by
  have nat := (smallToposMorphismTypeU_comp B S hS h e₀).hom.naturality
    (conormalSetInclusion B S hS Z₂ hZ₂)
  exact (congrArg ((smallToposMorphismTypeU B S hS e₀).pushforward.map
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
          ((modulePullbackAdjunction B S hS h).homEquiv (conormalModule B S hS X Z)
            (conormalModule B S hS X₂ Z₂) (conormalMap B S hS Z₂ Z h' h hsq))) ≫ ·) nat.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))))
        ((Functor.map_comp (smallToposMorphismTypeU B S hS e₀).pushforward _ _).symm.trans
          ((congrArg (smallToposMorphismTypeU B S hS e₀).pushforward.map
            (conormalSetInclusion_restriction_conormalModule B S hS Z₂ Z h' h hsq hZ₂ hZ)).trans
            (Functor.map_comp (smallToposMorphismTypeU B S hS e₀).pushforward _ _)))).trans
                (Category.assoc _ _ _)))

/-- The map `ρ = (e₀)_*σ` followed by the comparison of iterated direct images, on underlying
sheaves of sets. -/
theorem sheafCompose_map_pushforward_restrictedSharpThroughThickening_comp :
    (sheafCompose (SmallEtale.topology B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
      (CategoryTheory.forget RingCat.{u})).map ((pushforwardRingFunctor
          (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))) =
      (smallToposMorphismTypeU B S hS e₀).pushforward.map ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq)) ≫
              ((smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))) :=
  (Functor.map_comp _ _ _).trans
    (congrArg₂ (· ≫ ·) (ringSheafMap_pullbackRingSheafMap _ _ _)
      (sheafCompose_map_pushforwardRingSheafCompHom B S hS h e₀ _))

/-- **R3: the ideal inclusions under the conormal map of a morphism of thickenings**, on the
small étale site of `W₀`.  For `m` a local section of `(e₀)_*𝒞_{Z/X}`, the inclusion into
`(h ≫ e₀)_*(i₂^{-1}𝒪_{X₂})` of the image of `m` under the direct image of the transpose of the
conormal map `γ` is the image of the inclusion of `m` into `(e₀)_*(i^{-1}𝒪_X)` under
`ρ = (e₀)_*σ` followed by the comparison of iterated direct images. -/
theorem restrictedSquareZeroValues_ι_conormalMap_restriction
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (m : ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)).val.obj V) :
    (restrictedSquareZeroValues B S hS Z₂ W₀
        (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) hZ₂).ι
      ((((modulePushforward B S hS e₀).map
          ((modulePullbackAdjunction B S hS h).homEquiv (conormalModule B S hS X Z)
            (conormalModule B S hS X₂ Z₂) (conormalMap B S hS Z₂ Z h' h hsq)) ≫
        (modulePushforwardCompIso B S hS h e₀).hom.app (conormalModule B S hS X₂ Z₂)).val.app
          V).hom m) =
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))).hom.app V
      ((restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι m) := by
  refine (restrictedSquareZeroValues_ι_eq_conormalSetInclusion B S hS Z₂ W₀
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀) hZ₂ _).trans
    (Eq.trans ?_ (congrArg (((pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))).hom.app V)
      (restrictedSquareZeroValues_ι_eq_conormalSetInclusion B S hS Z W₀ e₀ hZ m)).symm)
  refine Eq.trans ?_ (sheafCompose_forget_map_hom_app_apply_ringCat ((pushforwardRingFunctor
      (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq) ≫
        pushforwardRingSheafCompHom B S hS h e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))) V _)
  refine Eq.trans ?_ (setSheafHom_congr_app_apply
    (sheafCompose_map_pushforward_restrictedSharpThroughThickening_comp B S hS Z₂ Z W₀ h' h e₀
      hsq).symm V _)
  refine Eq.trans ?_ (setSheaf_comp_hom_app_apply
      ((smallToposMorphismTypeU B S hS e₀).pushforward.map ((sheafCompose
          (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq)))
              ((smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))) V _).symm
  refine (congrArg (((smallToposMorphismTypeU B S hS
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)).pushforward.map
        (conormalSetInclusion B S hS Z₂ hZ₂)).hom.app V)
    ((modulesHom_val_app_hom_eq B S hS _ V m).trans
      (modulePushforwardCompIso_hom_app_comp_val_app B S hS h e₀ (conormalModule B S hS X₂ Z₂) _
        V m))).trans ?_
  have key := setSheafHom_congr_app_apply
    (pushforward_conormalSetInclusion_restriction B S hS Z₂ Z W₀ h' h e₀ hsq hZ₂ hZ) V m
  refine (setSheaf_comp_hom_app_apply ((smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS))).obj
          (conormalModule B S hS X₂ Z₂)))
        ((smallToposMorphismTypeU B S hS
          (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)).pushforward.map
            (conormalSetInclusion B S hS Z₂ hZ₂)) V _).symm.trans ?_
  refine (setSheaf_comp_hom_app_apply ((smallToposMorphismTypeU B S hS e₀).pushforward.map
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map
          ((modulePullbackAdjunction B S hS h).homEquiv (conormalModule B S hS X Z)
            (conormalModule B S hS X₂ Z₂) (conormalMap B S hS Z₂ Z h' h hsq))))
                (((smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS))).obj
          (conormalModule B S hS X₂ Z₂))) ≫
              ((smallToposMorphismTypeU B S hS
                (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ h e₀)).pushforward.map
                  (conormalSetInclusion B S hS Z₂ hZ₂))) V m).symm.trans ?_
  refine key.trans ?_
  refine (setSheaf_comp_hom_app_apply ((smallToposMorphismTypeU B S hS e₀).pushforward.map
      (conormalSetInclusion B S hS Z hZ)) ((smallToposMorphismTypeU B S hS e₀).pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq)) ≫
              ((smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂))))) V m).trans ?_
  exact setSheaf_comp_hom_app_apply ((smallToposMorphismTypeU B S hS e₀).pushforward.map
      ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).map
          (restrictedSharpThroughThickening B S hS Z₂ Z h' h hsq)))
              ((smallToposMorphismTypeU_comp B S hS h e₀).hom.app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z₂.1.toFunctor, Z₂.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X₂ Z₂)))) V _

end Target

end AlgebraicGeometry.Space

end
