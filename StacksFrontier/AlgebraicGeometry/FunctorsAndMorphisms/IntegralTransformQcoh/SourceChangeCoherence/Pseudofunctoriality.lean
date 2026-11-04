module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeCoherence.ChainComp
import all StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence

/-!
# Pseudo-functoriality of the source-change isomorphism of an integral transform

Let `R` be a commutative ring, let `X` be an affine scheme over `R`, let `f : X' ⟶ X` be a
morphism of schemes over `R` whose underlying morphism of schemes is affine and let `Y` be a
scheme over `R`.  For a quasi-coherent kernel `K` on `X ×_R Y` the integral transform of `K`
precomposed with the direct image along `f` is the integral transform of the inverse image of
`K` on `X' ×_R Y`.  This file proves that this identification is compatible with composition of the
morphism `f`.

## Main results

* `AlgebraicGeometry.whiskerRight_quasicoherentIntegralTransformSourceChangeIso_hom`: after
  forgetting quasi-coherence of the values, the source-change isomorphism is affine change of
  source for the formula of Tag 0FZB, conjugated by the comparison isomorphisms.
* `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso_comp_of_formula`: change of
  source along a composite of affine morphisms is the composite of the two changes of source,
  granted the corresponding identity for the formula of Tag 0FZB.
* `AlgebraicGeometry.integralTransformFormulaSourceChangeIso_hom`: affine change of source for
  the formula of Tag 0FZB, with its five factors written out as whiskerings.
* `AlgebraicGeometry.pushforwardComp_hom_comp_pushforwardCongr_inv_comp_inv`: the comparison of
  the direct images along a composite of morphisms of schemes over a base cancels the comparison
  along the two spellings of that composite.
* `AlgebraicGeometry.sourceChangeChain_comp'`:
  `AlgebraicGeometry.sourceChangeChain_comp` with that comparison already cancelled.
* `AlgebraicGeometry.integralTransformFormulaSourceChangeIso_comp` and
  `AlgebraicGeometry.integralTransformFormulaSourceChangeIso_comp_app`: affine change of source
  for the formula of Tag 0FZB is compatible with composition of the morphism, as an identity of
  morphisms of functors and at every quasi-coherent module.
* `AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso_comp`: **pseudo-functoriality
  of the source-change isomorphism of Tag 0FZF**, unconditionally: change of source along a
  composite of affine morphisms is the composite of the two changes of source, up to the
  identification of the two iterated inverse images of the kernel.

## References

* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.IntegralTransformQcoh
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjectionFormula
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry

attribute [local implicit_reducible] TopCat.Sheaf
  AlgebraicGeometry.Scheme.Modules CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf structureSheafRing
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.Modules.Hom

/-! ### Affine change of source along a composite -/

section SourceChangeComp

open Stacks.AlgebraicGeometry.AffinePushforward

/-- A morphism whose composite with a retraction on the left is the identity may be cancelled
from the front of a factorisation. -/
private theorem cancel_head {E : Type*} [Category E] {A B C : E} (v : A ⟶ B) (w : B ⟶ A)
    (b : B ⟶ C) (r : A ⟶ C) (h : b = w ≫ r) (hw : v ≫ w = 𝟙 A) : v ≫ b = r := by
  rw [h, ← Category.assoc, hw, Category.id_comp]

/-- An identity may be removed from the front of a factorisation. -/
private theorem id_head' {E : Type*} [Category E] {A B : E} (e : A ⟶ A) (he : e = 𝟙 A)
    (x y : A ⟶ B) (h : x = e ≫ y) : x = y := by
  rw [h, he, Category.id_comp]

/-- A triple composite whose first two factors are themselves composites is the corresponding
quintuple composite. -/
private theorem regroup5 {E : Type*} [Category E] {A1 A2 A3 A4 A5 A6 : E}
    (x : A1 ⟶ A2) (y : A2 ⟶ A3) (z : A3 ⟶ A4) (w : A4 ⟶ A5) (v : A5 ⟶ A6)
    {p : A1 ⟶ A3} {q : A3 ⟶ A5} {v' : A5 ⟶ A6} (hp : p = x ≫ y) (hq : q = z ≫ w)
    (hv : v' = v) : p ≫ q ≫ v' = x ≫ y ≫ z ≫ w ≫ v := by
  subst hp hq hv
  simp only [Category.assoc]

/-- A factorisation whose first factor is a whiskered composite, read at one object. -/
private theorem chain_head_split {C D E : Type*} [Category C] [Category D] [Category E]
    {F G H : C ⥤ D} (p : F ⟶ G) (b : G ⟶ H) (W : D ⥤ E) {T : C ⥤ E}
    (r : H ⋙ W ⟶ T) {lhs : F ⋙ W ⟶ T}
    (hch : lhs = Functor.whiskerRight (p ≫ b) W ≫ r) (M : C) :
    lhs.app M = (Functor.whiskerRight p W).app M ≫ (Functor.whiskerRight b W ≫ r).app M := by
  rw [hch, Functor.whiskerRight_comp, Category.assoc, NatTrans.comp_app]

/-- The comparison of the direct images along a composite of morphisms of schemes, restricted
along a functor and whiskered by two further functors, is the identity at every object. -/
private theorem whiskerRight_pushforwardComp_hom_app {C D D' : Type*} [Category C]
    [Category D] [Category D'] {A B E : Scheme.{u}} (g : A ⟶ B) (k : B ⟶ E)
    (P : C ⥤ A.Modules) (V : E.Modules ⥤ D) (W : D ⥤ D') (M : C) :
    (Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerLeft P
        (Scheme.Modules.pushforwardComp g k).hom) V) W).app M = 𝟙 _ :=
  (congrArg (fun z => W.map (V.map (NatTrans.app z (P.obj M))))
    (pushforwardComp_hom_eq_id g k)).trans
      ((congrArg W.map (V.map_id _)).trans (W.map_id _))

/-- `AlgebraicGeometry.sourceChangeChain_comp` with the comparison of the two composite direct
images already cancelled from the base-change morphism of the composite, so that no correction
of the two spellings of the composite direct image appears. -/
theorem sourceChangeChain_comp' {D₂ D₁ D₀ A₁ B₁ C₁ Y₁ : Type*} [Category D₂] [Category D₁]
    [Category D₀] [Category A₁] [Category B₁] [Category C₁] [Category Y₁]
    {Pf' : D₁ ⥤ D₀} {Pf'' : D₂ ⥤ D₁} {P : D₀ ⥤ C₁} {P' : D₁ ⥤ B₁} {P'' : D₂ ⥤ A₁}
    {A : A₁ ⥤ B₁} {B : B₁ ⥤ C₁} {S : A₁ ⥤ C₁} {Q : C₁ ⥤ Y₁} {Q' : B₁ ⥤ Y₁} {Q'' : A₁ ⥤ Y₁}
    {L Rr : C₁ ⥤ C₁} {L' R' : B₁ ⥤ B₁} {L'' R'' Ls Rs : A₁ ⥤ A₁}
    (β : L ≅ Rr) (β' : L' ≅ R') (β'' : L'' ≅ R'') (βs : Ls ≅ Rs)
    (π' : B ⋙ Rr ⟶ R' ⋙ B) (π'' : A ⋙ R' ⟶ R'' ⋙ A) (πs : S ⋙ Rr ⟶ Rs ⋙ S)
    (ε' : B ⋙ Q ⟶ Q') (ε'' : A ⋙ Q' ⟶ Q'') (εs : S ⋙ Q ⟶ Q'')
    (κ : S ≅ A ⋙ B) (τ : L'' ⟶ Ls) (σ : R'' ⟶ Rs)
    (bc' : Pf' ⋙ P ⟶ P' ⋙ B) (bc'' : Pf'' ⋙ P' ⟶ P'' ⋙ A)
    (bcs : (Pf'' ⋙ Pf') ⋙ P ⟶ P'' ⋙ S)
    (Hbc : bcs = (Functor.whiskerLeft Pf'' bc' ≫ Functor.whiskerRight bc'' B) ≫
      Functor.whiskerLeft P'' κ.inv)
    (Hβ : β''.inv ≫ τ = σ ≫ βs.inv)
    (Hπ : Functor.whiskerRight κ.hom Rr ≫ Functor.whiskerLeft A π' ≫
        Functor.whiskerRight π'' B ≫ Functor.whiskerRight σ (A ⋙ B) =
      πs ≫ Functor.whiskerLeft Rs κ.hom)
    (Hε : εs = Functor.whiskerRight κ.hom Q ≫ Functor.whiskerLeft A ε' ≫ ε'')
    (γ : B ⋙ L ⋙ Q ⟶ L' ⋙ Q')
    (hγ : γ = Functor.whiskerLeft B (Functor.whiskerRight β.hom Q) ≫
      Functor.whiskerRight π' Q ≫ Functor.whiskerRight β'.inv (B ⋙ Q) ≫
      Functor.whiskerLeft L' ε')
    (t : P'' ⋙ L'' ⋙ Q'' ⟶ P'' ⋙ Ls ⋙ Q'')
    (ht : t = Functor.whiskerLeft P'' (Functor.whiskerRight τ Q'')) :
    Functor.whiskerLeft Pf'' (Functor.whiskerRight bc' (L ⋙ Q)) ≫
        Functor.whiskerLeft (Pf'' ⋙ P') γ ≫
        Functor.whiskerRight bc'' (L' ⋙ Q') ≫
        Functor.whiskerLeft P'' (Functor.whiskerLeft A (Functor.whiskerRight β'.hom Q') ≫
          Functor.whiskerRight π'' Q' ≫ Functor.whiskerRight β''.inv (A ⋙ Q') ≫
          Functor.whiskerLeft L'' ε'') ≫ t =
      Functor.whiskerRight bcs (L ⋙ Q) ≫
        Functor.whiskerLeft P'' (Functor.whiskerLeft S (Functor.whiskerRight β.hom Q) ≫
          Functor.whiskerRight πs Q ≫ Functor.whiskerRight βs.inv (S ⋙ Q) ≫
          Functor.whiskerLeft Ls εs) := by
  refine sourceChangeChain_comp β β' β'' βs π' π'' πs ε' ε'' εs κ τ σ bc' bc'' bcs
    (𝟙 _) rfl ?_ Hβ Hπ Hε γ hγ t ht
  rw [Hbc, Functor.whiskerRight_id', Category.id_comp]

/-- Affine change of source for the formula of Tag 0FZB, with the five factors written out as
whiskerings of the base-change morphism of Tag 02KG, the braiding, the projection-formula
morphism of Tag 0FZE, the inverse braiding and the normalisation of the two composite direct
images. -/
theorem integralTransformFormulaSourceChangeIso_hom (R : Type u) [CommRing R]
    (X X' Y : Over (Spec (.of R))) (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    (integralTransformFormulaSourceChangeIso R X X' Y f K).hom =
      Functor.whiskerLeft (SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι
        (Functor.whiskerRight (baseChangeNatTrans (isPullback_sourceChangeMap R X X' Y f).w)
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                (pullback X.hom Y.hom).toRingedSpace.sheaf).obj (K.obj)) ⋙
              Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≫
          Functor.whiskerLeft (Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))
            (Functor.whiskerLeft (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f))
                (Functor.whiskerRight
                  ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                      ((pullback X.hom Y.hom)).presheaf ((pullback X.hom Y.hom)).ringCatSheaf.2
                      (K.obj))).hom
                  (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))) ≫
              Functor.whiskerRight
                (projectionFormulaSourceNatTrans (sourceChangeMap R X X' Y f) K.obj)
                (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≫
              Functor.whiskerRight
                ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                    ((pullback X'.hom Y.hom)).presheaf ((pullback X'.hom Y.hom)).ringCatSheaf.2
                    (((Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).obj K.obj)))).inv
                (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f) ⋙
                  Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≫
              Functor.whiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                  (pullback X'.hom Y.hom).toRingedSpace.sheaf).obj (((Scheme.Modules.pullback
                  (sourceChangeMap R X X' Y f)).obj K.obj))))
                (Scheme.Modules.pushforwardComp (sourceChangeMap R X X' Y f)
                    (pullback.snd X.hom Y.hom) ≪≫
                  Scheme.Modules.pushforwardCongr
                    (sourceChangeMap_comp_snd R X X' Y f)).hom)) := rfl

/-- The inverse comparison of the inverse images along two equal morphisms is the identity when
the equality is reflexive. -/
private theorem pullbackCongr_rfl_inv {A B : Scheme.{u}} {f : A ⟶ B} (hf : f = f) :
    (Scheme.Modules.pullbackCongr hf).inv = 𝟙 _ := rfl

/-- The comparison of the inverse images along two equal morphisms, taken along the symmetric
equality, is the inverse comparison. -/
private theorem pullbackCongr_symm_inv {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) :
    (Scheme.Modules.pullbackCongr h.symm).inv = (Scheme.Modules.pullbackCongr h).hom := by
  subst h
  rw [pullbackCongr_rfl_hom, pullbackCongr_rfl_inv]

/-- The morphism `eqToHom h` attached to a self-equality `h : A = A` is the identity. -/
private theorem eqToHom_eq_id {C : Type*} [Category C] {A : C} (h : A = A) :
    eqToHom h = 𝟙 A :=
  rfl

section Comp

variable (R : Type u) [CommRing R] (X X' X'' Y : Over (Spec (.of R)))
  (f' : X' ⟶ X) (f'' : X'' ⟶ X') [IsAffineHom f'.left] [IsAffineHom f''.left]
  (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))

omit [IsAffineHom f'.left] [IsAffineHom f''.left] in
/-- The comparison of the two iterated inverse images of a kernel along a composite of
source-change morphisms is the comparison of the inverse images along a composite, followed by
the comparison of the inverse images along the two spellings of the composite. -/
theorem sourceChangeKernelCompIso_inv_hom :
    (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv.hom =
      (Scheme.Modules.pullbackComp (sourceChangeMap R X' X'' Y f'')
          (sourceChangeMap R X X' Y f')).hom.app K.obj ≫
        (Scheme.Modules.pullbackCongr
          (sourceChangeMap_comp R X X' X'' Y f' f'')).hom.app K.obj := by
  rw [← pullbackCongr_symm_inv (sourceChangeMap_comp R X X' X'' Y f' f'')]
  rfl

/-- The comparison of the direct images on quasi-coherent modules along a composite of affine
morphisms, applied to the formula of Tag 0FZB, is the identity at every quasi-coherent
module. -/
theorem whiskerRight_eqToIso_quasicoherentPushforward_app
    (M : Scheme.QuasicoherentModules X''.left) :
    (Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f' f'' rfl)).hom
        (integralTransformFormula R X Y K.obj)).app M = 𝟙 _ := by
  rw [Functor.whiskerRight_app, eqToIso.hom, eqToHom_app]
  exact (congrArg (integralTransformFormula R X Y K.obj).map (eqToHom_eq_id _)).trans
    ((integralTransformFormula R X Y K.obj).map_id _)

omit [IsAffineHom f'.left] [IsAffineHom f''.left] in
/-- The base-change morphism of the source-change square of a composite, restricted along the
inclusion of quasi-coherent modules, is the horizontal composite of the two base-change
morphisms. -/
private theorem baseChangeNatTrans_sourceChange_vpaste :
    Functor.whiskerLeft (SheafOfModules.isQuasicoherent X''.left.ringCatSheaf).ι
        (baseChangeNatTrans (isPullback_sourceChangeMap R X X'' Y (f'' ≫ f')).w) =
      Functor.whiskerRight (Functor.whiskerLeft
          (SheafOfModules.isQuasicoherent X''.left.ringCatSheaf).ι
          ((Scheme.Modules.pushforwardCongr
              (rfl : f''.left ≫ f'.left = (f'' ≫ f').left)).inv ≫
            (Scheme.Modules.pushforwardComp f''.left f'.left).inv))
          (Scheme.Modules.pullback (pullback.fst X.hom Y.hom)) ≫
        (Functor.whiskerLeft ((SheafOfModules.isQuasicoherent X''.left.ringCatSheaf).ι ⋙
              Scheme.Modules.pushforward f''.left)
            (baseChangeNatTrans (isPullback_sourceChangeMap R X X' Y f').w) ≫
          Functor.whiskerRight (Functor.whiskerLeft
              (SheafOfModules.isQuasicoherent X''.left.ringCatSheaf).ι
              (baseChangeNatTrans (isPullback_sourceChangeMap R X' X'' Y f'').w))
            (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f'))) ≫
        Functor.whiskerLeft ((SheafOfModules.isQuasicoherent X''.left.ringCatSheaf).ι ⋙
            Scheme.Modules.pullback (pullback.fst X''.hom Y.hom))
          ((Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'')
              (sourceChangeMap R X X' Y f')).hom ≫
            (Scheme.Modules.pushforwardCongr
              (sourceChangeMap_comp R X X' X'' Y f' f'')).hom) :=
  congrArg (Functor.whiskerLeft (SheafOfModules.isQuasicoherent X''.left.ringCatSheaf).ι)
    (baseChangeNatTrans_vpaste (isPullback_sourceChangeMap R X X' Y f').w
      (isPullback_sourceChangeMap R X' X'' Y f'').w
      (isPullback_sourceChangeMap R X X'' Y (f'' ≫ f')).w rfl
      (sourceChangeMap_comp R X X' X'' Y f' f''))

section SourceChangeCorrection

variable {C : Type*} [Category C] (Iota : C ⥤ X''.left.Modules)

omit [IsAffineHom f'.left] [IsAffineHom f''.left] in
/-- **The comparison of the direct images along a composite of morphisms of schemes over a base
cancels the comparison along the two spellings of that composite.** -/
theorem pushforwardComp_hom_comp_pushforwardCongr_inv_comp_inv :
    (Scheme.Modules.pushforwardComp f''.left f'.left).hom ≫
        ((Scheme.Modules.pushforwardCongr
              (rfl : f''.left ≫ f'.left = (f'' ≫ f').left)).inv ≫
          (Scheme.Modules.pushforwardComp f''.left f'.left).inv) = 𝟙 _ := by
  rw [pushforwardCongr_rfl_inv, Category.id_comp, Iso.hom_inv_id]

omit [IsAffineHom f'.left] [IsAffineHom f''.left] in
/-- `AlgebraicGeometry.pushforwardComp_hom_comp_pushforwardCongr_inv_comp_inv` restricted along a
functor into the modules on the source. -/
private theorem whiskerLeft_pushforwardComp_hom_comp_pushforwardCongr_inv_comp_inv :
    Functor.whiskerLeft Iota (Scheme.Modules.pushforwardComp f''.left f'.left).hom ≫
        Functor.whiskerLeft Iota
          ((Scheme.Modules.pushforwardCongr
                (rfl : f''.left ≫ f'.left = (f'' ≫ f').left)).inv ≫
            (Scheme.Modules.pushforwardComp f''.left f'.left).inv) = 𝟙 _ :=
  (Functor.whiskerLeft_comp Iota _ _).symm.trans
    ((congrArg (Functor.whiskerLeft Iota)
      (pushforwardComp_hom_comp_pushforwardCongr_inv_comp_inv R X X' X'' f' f'')).trans
      (Functor.whiskerLeft_id' _))

omit [IsAffineHom f'.left] [IsAffineHom f''.left] in
/-- `AlgebraicGeometry.baseChangeNatTrans_sourceChange_vpaste` restricted along an arbitrary
functor into the modules on the source rather than along the inclusion of quasi-coherent
modules. -/
private theorem baseChangeNatTrans_sourceChange_vpaste' :
    Functor.whiskerLeft Iota (baseChangeNatTrans (isPullback_sourceChangeMap R X X'' Y (f'' ≫
        f')).w) =
      Functor.whiskerRight (Functor.whiskerLeft Iota
          ((Scheme.Modules.pushforwardCongr
              (rfl : f''.left ≫ f'.left = (f'' ≫ f').left)).inv ≫
            (Scheme.Modules.pushforwardComp f''.left f'.left).inv)) (Scheme.Modules.pullback
                (pullback.fst X.hom Y.hom)) ≫
        (Functor.whiskerLeft (Iota ⋙ Scheme.Modules.pushforward f''.left) (baseChangeNatTrans
            (isPullback_sourceChangeMap R X X' Y f').w) ≫
          Functor.whiskerRight (Functor.whiskerLeft Iota (baseChangeNatTrans
              (isPullback_sourceChangeMap R X' X'' Y f'').w)) (Scheme.Modules.pushforward
              (sourceChangeMap R X X' Y f'))) ≫
        Functor.whiskerLeft (Iota ⋙ (Scheme.Modules.pullback (pullback.fst X''.hom Y.hom)))
          ((Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'') (sourceChangeMap R X X'
              Y f')).hom ≫
            (Scheme.Modules.pushforwardCongr
              (sourceChangeMap_comp R X X' X'' Y f' f'')).hom) :=
  congrArg (Functor.whiskerLeft Iota)
    (baseChangeNatTrans_vpaste (isPullback_sourceChangeMap R X X' Y f').w
      (isPullback_sourceChangeMap R X' X'' Y f'').w
      (isPullback_sourceChangeMap R X X'' Y (f'' ≫ f')).w rfl
      (sourceChangeMap_comp R X X' X'' Y f' f''))

omit [IsAffineHom f'.left] [IsAffineHom f''.left] in
/-- `AlgebraicGeometry.baseChangeNatTrans_sourceChange_vpaste'` with the comparison of the two
spellings of the composite direct image moved to the other side of the equation, where it
cancels. -/
private theorem baseChangeNatTrans_sourceChange_vpaste_normalised :
    (Functor.whiskerRight (Functor.whiskerLeft Iota
            (Scheme.Modules.pushforwardComp f''.left f'.left).hom) (Scheme.Modules.pullback
                (pullback.fst X.hom Y.hom))) ≫ Functor.whiskerLeft Iota (baseChangeNatTrans
                (isPullback_sourceChangeMap R X X'' Y (f'' ≫ f')).w) =
      (Functor.whiskerLeft (Iota ⋙ Scheme.Modules.pushforward f''.left) (baseChangeNatTrans
          (isPullback_sourceChangeMap R X X' Y f').w) ≫
        Functor.whiskerRight (Functor.whiskerLeft Iota (baseChangeNatTrans
            (isPullback_sourceChangeMap R X' X'' Y f'').w)) (Scheme.Modules.pushforward
            (sourceChangeMap R X X' Y f'))) ≫
      Functor.whiskerLeft (Iota ⋙ (Scheme.Modules.pullback (pullback.fst X''.hom Y.hom)))
        ((Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'') (sourceChangeMap R X X' Y
            f')).hom ≫
          (Scheme.Modules.pushforwardCongr
            (sourceChangeMap_comp R X X' X'' Y f' f'')).hom) :=
  cancel_head _ _ _ _
    (baseChangeNatTrans_sourceChange_vpaste' R X X' X'' Y f' f'' Iota)
    ((Functor.whiskerRight_comp _ _ _).symm.trans
      (whiskerRight_eq_id _ _
        (whiskerLeft_pushforwardComp_hom_comp_pushforwardCongr_inv_comp_inv
          R X X' X'' f' f'' Iota)))

omit [IsAffineHom f'.left] [IsAffineHom f''.left] in
/-- The comparison of the two spellings of the composite direct image, whiskered into the
formula of Tag 0FZB, is the identity at every object. -/
private theorem whiskerRight_sourceChange_pushforwardComp_hom_app (M : C) :
    (Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerLeft Iota
            (Scheme.Modules.pushforwardComp f''.left f'.left).hom) (Scheme.Modules.pullback
                (pullback.fst X.hom Y.hom)))
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            (Limits.pullback X.hom Y.hom).toRingedSpace.sheaf).obj (K.obj))) ⋙
            (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)))).app M = 𝟙 _ :=
  whiskerRight_pushforwardComp_hom_app _ _ _ _ _ M

omit [IsAffineHom f'.left] [IsAffineHom f''.left] in
/-- **The five-fold chain of Tag 0FZB along a composite of source-change morphisms**, restricted
along an arbitrary functor into the modules on the source: the chain for the composite is the
composite of the two chains, the comparison of the two spellings of the composite direct image
being carried in front of the base-change morphism. -/
private theorem sourceChangeChain_integralTransformFormula
    [CompactSpace X''.left] [QuasiSeparatedSpace X''.left] :
    Functor.whiskerLeft (Iota ⋙ Scheme.Modules.pushforward f''.left) (Functor.whiskerRight
        (baseChangeNatTrans (isPullback_sourceChangeMap R X X' Y f').w)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
            (Limits.pullback X.hom Y.hom).toRingedSpace.sheaf).obj (K.obj))) ⋙
            (Scheme.Modules.pushforward
        (pullback.snd X.hom Y.hom)))) ≫
        Functor.whiskerLeft ((Iota ⋙ Scheme.Modules.pushforward f''.left) ⋙
            (Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))) (Functor.whiskerLeft
            (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f')) (Functor.whiskerRight
            ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                ((Limits.pullback X.hom Y.hom)).presheaf
                ((Limits.pullback X.hom Y.hom)).ringCatSheaf.2 (K.obj))).hom
            (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))) ≫
            Functor.whiskerRight (projectionFormulaSourceNatTrans (sourceChangeMap R X X' Y f')
                K.obj) (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≫
            Functor.whiskerRight ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                ((Limits.pullback X'.hom Y.hom)).presheaf
                ((Limits.pullback X'.hom Y.hom)).ringCatSheaf.2 (((Scheme.Modules.pullback
                (sourceChangeMap R X X' Y f')).obj K.obj)))).inv
                ((Scheme.Modules.pushforward (sourceChangeMap R X X' Y f')) ⋙
                (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))) ≫
            Functor.whiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                (Limits.pullback X'.hom
                Y.hom).toRingedSpace.sheaf).obj (((Scheme.Modules.pullback
                    (sourceChangeMap R X X' Y f')).obj K.obj))))
                (Scheme.Modules.pushforwardComp (sourceChangeMap R X X' Y f') (pullback.snd X.hom
                Y.hom) ≪≫
          Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X X' Y f')).hom) ≫
        Functor.whiskerRight (Functor.whiskerLeft Iota (baseChangeNatTrans
            (isPullback_sourceChangeMap R X' X'' Y f'').w))
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                (Limits.pullback X'.hom Y.hom).toRingedSpace.sheaf).obj (((Scheme.Modules.pullback
            (sourceChangeMap R X X' Y f')).obj K.obj)))) ⋙ (Scheme.Modules.pushforward (pullback.snd
            X'.hom Y.hom))) ≫
        Functor.whiskerLeft (Iota ⋙ (Scheme.Modules.pullback (pullback.fst X''.hom Y.hom)))
            (Functor.whiskerLeft (Scheme.Modules.pushforward (sourceChangeMap R X' X'' Y f''))
            (Functor.whiskerRight ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                ((Limits.pullback X'.hom Y.hom)).presheaf
                ((Limits.pullback X'.hom Y.hom)).ringCatSheaf.2 (((Scheme.Modules.pullback
                (sourceChangeMap R X X' Y f')).obj K.obj)))).hom
            (Scheme.Modules.pushforward (pullback.snd X'.hom Y.hom))) ≫
          Functor.whiskerRight (projectionFormulaSourceNatTrans (sourceChangeMap R X' X'' Y f'')
              ((Scheme.Modules.pullback (sourceChangeMap R X X' Y f')).obj K.obj))
              (Scheme.Modules.pushforward (pullback.snd X'.hom Y.hom)) ≫ Functor.whiskerRight
              ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                  ((Limits.pullback X''.hom Y.hom)).presheaf
                  ((Limits.pullback X''.hom Y.hom)).ringCatSheaf.2 (((Scheme.Modules.pullback
                  (sourceChangeMap R X' X'' Y f'')).obj
                    (sourceChangeKernel R X X' Y f' K).obj)))).inv
              ((Scheme.Modules.pushforward (sourceChangeMap R X' X'' Y f''))
              ⋙ (Scheme.Modules.pushforward (pullback.snd X'.hom Y.hom))) ≫
          Functor.whiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
              (Limits.pullback X''.hom
              Y.hom).toRingedSpace.sheaf).obj (((Scheme.Modules.pullback
                  (sourceChangeMap R X' X'' Y f'')).obj (sourceChangeKernel R
              X X' Y f' K).obj)))) (Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'')
              (pullback.snd X'.hom Y.hom) ≪≫
          Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X' X'' Y f'')).hom) ≫
              (Functor.whiskerLeft (Iota ⋙ (Scheme.Modules.pullback (pullback.fst X''.hom Y.hom)))
              (Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  ((Limits.pullback X''.hom Y.hom)).toRingedSpace.sheaf).map
              (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv.hom)
              (Scheme.Modules.pushforward (pullback.snd X''.hom Y.hom)))) =
      Functor.whiskerRight ((Functor.whiskerRight (Functor.whiskerLeft Iota
            (Scheme.Modules.pushforwardComp f''.left f'.left).hom) (Scheme.Modules.pullback
                (pullback.fst X.hom Y.hom))) ≫ (Functor.whiskerLeft Iota (baseChangeNatTrans
                (isPullback_sourceChangeMap R X X'' Y (f'' ≫ f')).w)))
                ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                    (Limits.pullback X.hom Y.hom).toRingedSpace.sheaf).obj (K.obj))) ⋙
                    (Scheme.Modules.pushforward
                (pullback.snd X.hom Y.hom))) ≫
        Functor.whiskerLeft (Iota ⋙ (Scheme.Modules.pullback (pullback.fst X''.hom Y.hom)))
            (Functor.whiskerLeft (Scheme.Modules.pushforward (sourceChangeMap R X X'' Y (f'' ≫ f')))
              (Functor.whiskerRight ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                ((Limits.pullback X.hom Y.hom)).presheaf
                ((Limits.pullback X.hom Y.hom)).ringCatSheaf.2 (K.obj))).hom
                (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))) ≫
          Functor.whiskerRight (projectionFormulaSourceNatTrans (sourceChangeMap R X X'' Y (f'' ≫
              f')) K.obj) (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) ≫
              Functor.whiskerRight ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                  ((Limits.pullback X''.hom Y.hom)).presheaf
                  ((Limits.pullback X''.hom Y.hom)).ringCatSheaf.2 (((Scheme.Modules.pullback
                  (sourceChangeMap R X X'' Y (f'' ≫ f'))).obj K.obj)))).inv
              ((Scheme.Modules.pushforward (sourceChangeMap R X X'' Y (f'' ≫ f'))) ⋙
              (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))) ≫
          Functor.whiskerLeft (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
              (Limits.pullback X''.hom
              Y.hom).toRingedSpace.sheaf).obj (((Scheme.Modules.pullback (sourceChangeMap R X X'' Y
                  (f'' ≫ f'))).obj K.obj))))
              (Scheme.Modules.pushforwardComp (sourceChangeMap R X X'' Y (f'' ≫ f')) (pullback.snd
              X.hom Y.hom) ≪≫
          Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X X'' Y (f'' ≫ f'))).hom) :=
  sourceChangeChain_comp'
    (Pf' := Scheme.Modules.pushforward f'.left)
    (Pf'' := (Iota ⋙ Scheme.Modules.pushforward f''.left))
    (P := (Scheme.Modules.pullback (pullback.fst X.hom Y.hom)))
    (P' := (Scheme.Modules.pullback (pullback.fst X'.hom Y.hom)))
    (P'' := (Iota ⋙ (Scheme.Modules.pullback (pullback.fst X''.hom Y.hom))))
    (A := (Scheme.Modules.pushforward (sourceChangeMap R X' X'' Y f'')))
    (B := (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f')))
    (S := (Scheme.Modules.pushforward (sourceChangeMap R X X'' Y (f'' ≫ f'))))
    (Q := (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)))
    (Q' := (Scheme.Modules.pushforward (pullback.snd X'.hom Y.hom)))
    (Q'' := (Scheme.Modules.pushforward (pullback.snd X''.hom Y.hom)))
    ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
        ((Limits.pullback X.hom Y.hom)).presheaf ((Limits.pullback X.hom Y.hom)).ringCatSheaf.2
        (K.obj)))
    ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
        ((Limits.pullback X'.hom Y.hom)).presheaf ((Limits.pullback X'.hom Y.hom)).ringCatSheaf.2
        (((Scheme.Modules.pullback (sourceChangeMap R X X' Y f')).obj K.obj))))
    ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
        ((Limits.pullback X''.hom Y.hom)).presheaf
        ((Limits.pullback X''.hom Y.hom)).ringCatSheaf.2
        (((Scheme.Modules.pullback (sourceChangeMap R X' X'' Y f'')).obj
          (sourceChangeKernel R X X' Y f' K).obj))))
    ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
        ((Limits.pullback X''.hom Y.hom)).presheaf
        ((Limits.pullback X''.hom Y.hom)).ringCatSheaf.2
        (((Scheme.Modules.pullback (sourceChangeMap R X X'' Y (f'' ≫ f'))).obj K.obj))))
    (projectionFormulaSourceNatTrans (sourceChangeMap R X X' Y f') K.obj)
        (projectionFormulaSourceNatTrans (sourceChangeMap R X' X'' Y f'') ((Scheme.Modules.pullback
        (sourceChangeMap R X X' Y f')).obj K.obj)) (projectionFormulaSourceNatTrans
        (sourceChangeMap R X X'' Y (f'' ≫ f')) K.obj)
    (Scheme.Modules.pushforwardComp (sourceChangeMap R X X' Y f') (pullback.snd X.hom Y.hom) ≪≫
          Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X X' Y f')).hom
              (Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'') (pullback.snd X'.hom
              Y.hom) ≪≫
          Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X' X'' Y f'')).hom
              (Scheme.Modules.pushforwardComp (sourceChangeMap R X X'' Y (f'' ≫ f')) (pullback.snd
              X.hom Y.hom) ≪≫
          Scheme.Modules.pushforwardCongr (sourceChangeMap_comp_snd R X X'' Y (f'' ≫ f'))).hom
    (Scheme.Modules.pushforwardComp (sourceChangeMap R X' X'' Y f'') (sourceChangeMap R X X' Y f')
        ≪≫
      Scheme.Modules.pushforwardCongr (sourceChangeMap_comp R X X' X'' Y f' f'')).symm
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((Limits.pullback X''.hom Y.hom)).toRingedSpace.sheaf).map
        (sourceChangeKernelCompIso R X X' X'' Y f' f''
        K).inv.hom)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((Limits.pullback X''.hom Y.hom).toRingedSpace).sheaf).flip.map
        (sourceChangeKernelCompIso R X X'
        X'' Y f' f'' K).inv.hom)
    (baseChangeNatTrans (isPullback_sourceChangeMap R X X' Y f').w) (Functor.whiskerLeft Iota
        (baseChangeNatTrans (isPullback_sourceChangeMap R X' X'' Y f'').w))
    ((Functor.whiskerRight (Functor.whiskerLeft Iota
            (Scheme.Modules.pushforwardComp f''.left f'.left).hom) (Scheme.Modules.pullback
                (pullback.fst X.hom Y.hom))) ≫ (Functor.whiskerLeft Iota (baseChangeNatTrans
                (isPullback_sourceChangeMap R X X'' Y (f'' ≫ f')).w)))
    (baseChangeNatTrans_sourceChange_vpaste_normalised R X X' X'' Y f' f'' Iota)
    ((square_inv _ _ _ _ (tensorLeftIsoTensorRightScheme_naturality (Limits.pullback X''.hom Y.hom)
        (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv.hom)).symm)
    (projectionFormulaSourceNatTrans_comp' (sourceChangeMap R X' X'' Y f'') (sourceChangeMap R X X'
        Y f')
      (sourceChangeMap_comp R X X' X'' Y f' f'') K.obj
      (sourceChangeKernelCompIso_inv_hom R X X' X'' Y f' f'' K))
    (pushforwardSourceChangeIso_comp' R X X' X'' Y f' f'')
    _ rfl (Functor.whiskerLeft (Iota ⋙ (Scheme.Modules.pullback (pullback.fst X''.hom Y.hom)))
        (Functor.whiskerRight ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((Limits.pullback X''.hom Y.hom)).toRingedSpace.sheaf).map
        (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv.hom) (Scheme.Modules.pushforward
        (pullback.snd X''.hom Y.hom)))) rfl

end SourceChangeCorrection

/-- **Affine change of source for the pullback--tensor--pushforward formula of Tag 0FZB is
compatible with composition of the morphism**, at every quasi-coherent module: change of source
along a composite `X'' ⟶ X' ⟶ X` of affine morphisms is the composite of the two changes of
source, up to the identification of the two iterated inverse images of the kernel. -/
theorem integralTransformFormulaSourceChangeIso_comp_app
    [CompactSpace X''.left] [QuasiSeparatedSpace X''.left]
    (M : Scheme.QuasicoherentModules X''.left) :
    (Functor.whiskerLeft (quasicoherentPushforward f''.left)
          (integralTransformFormulaSourceChangeIso R X X' Y f' K).hom ≫
        (integralTransformFormulaSourceChangeIso R X' X'' Y f''
          (sourceChangeKernel R X X' Y f' K)).hom ≫
        (formulaFunctor R X'' Y).map
          (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv.hom).app M =
      (integralTransformFormulaSourceChangeIso R X X'' Y (f'' ≫ f') K).hom.app M := by
  simp only [integralTransformFormulaSourceChangeIso_hom]
  exact id_head' _
    (whiskerRight_sourceChange_pushforwardComp_hom_app R X X' X'' Y f' f'' K
      (SheafOfModules.isQuasicoherent X''.left.ringCatSheaf).ι M) _ _
    (chain_head_split (Functor.whiskerRight (Functor.whiskerLeft (SheafOfModules.isQuasicoherent
        X''.left.ringCatSheaf).ι
            (Scheme.Modules.pushforwardComp f''.left f'.left).hom) (Scheme.Modules.pullback
                (pullback.fst X.hom Y.hom))) (Functor.whiskerLeft (SheafOfModules.isQuasicoherent
                X''.left.ringCatSheaf).ι (baseChangeNatTrans (isPullback_sourceChangeMap R X X'' Y
                (f'' ≫ f')).w)) ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
                    (Limits.pullback X.hom
                Y.hom).toRingedSpace.sheaf).obj (K.obj))) ⋙
                (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom))) _
      ((regroup5 _ _ _ _ _ rfl rfl
          (formulaFunctor_map R X'' Y
            (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv.hom)).trans
        (sourceChangeChain_integralTransformFormula R X X' X'' Y f' f'' K
          (SheafOfModules.isQuasicoherent X''.left.ringCatSheaf).ι)) M)

/-- **Affine change of source for the pullback--tensor--pushforward formula of Tag 0FZB is
compatible with composition of the morphism.** -/
theorem integralTransformFormulaSourceChangeIso_comp
    [CompactSpace X''.left] [QuasiSeparatedSpace X''.left] :
    Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f' f'' rfl)).hom
          (integralTransformFormula R X Y K.obj) ≫
        Functor.whiskerLeft (quasicoherentPushforward f''.left)
          (integralTransformFormulaSourceChangeIso R X X' Y f' K).hom ≫
        (integralTransformFormulaSourceChangeIso R X' X'' Y f''
          (sourceChangeKernel R X X' Y f' K)).hom ≫
        (formulaFunctor R X'' Y).map
          (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv.hom =
      (integralTransformFormulaSourceChangeIso R X X'' Y (f'' ≫ f') K).hom :=
  NatTrans.ext (funext fun M =>
    (id_head' _ (whiskerRight_eqToIso_quasicoherentPushforward_app R X X' X'' Y f' f'' K M)
        _ _ (NatTrans.comp_app _ _ M)).trans
      (integralTransformFormulaSourceChangeIso_comp_app R X X' X'' Y f' f'' K M))

end Comp

end SourceChangeComp

/-! ### Iterated change of source -/

section Iterated

/-- Whiskering on the right after whiskering on the left is whiskering on the left after
whiskering on the right. -/
private alias whiskerRight_whiskerLeft_eq := whiskerRight_whiskerLeft_eq'

/-- The associator of three functors is carried to an identity by whiskering on the right. -/
private theorem whiskerRight_associator_hom {C D E E' E'' : Type*} [Category C] [Category D]
    [Category E] [Category E'] [Category E''] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
    (I : E' ⥤ E'') :
    Functor.whiskerRight (Functor.associator F G H).hom I = 𝟙 _ :=
  NatTrans.ext (funext fun _ => I.map_id _)

/-- A factorisation of a right-whiskered natural transformation into three morphisms stays one
after whiskering on the left. -/
theorem whiskerRight_whiskerLeft_comp₃ {C D E E' : Type*} [Category C] [Category D]
    [Category E] [Category E'] (P : C ⥤ D) (I : E ⥤ E') {F G : D ⥤ E} (α : F ⟶ G)
    {A B : D ⥤ E'} (a : F ⋙ I ⟶ A) (b : A ⟶ B) (c : B ⟶ G ⋙ I)
    (h : Functor.whiskerRight α I = a ≫ b ≫ c) :
    Functor.whiskerRight (Functor.whiskerLeft P α) I =
      Functor.whiskerLeft P a ≫ Functor.whiskerLeft P b ≫ Functor.whiskerLeft P c :=
  (whiskerRight_whiskerLeft_eq P α I).trans
    ((congrArg (Functor.whiskerLeft P) h).trans (whiskerLeft_comp₃ P a b c))

/-- The exchange law for whiskering, in the form where the left-hand whiskering is by a composite
of two functors and the right-hand one is performed in two steps. -/
theorem whisker_exchange_pair {C D D' E E' : Type*} [Category C] [Category D]
    [Category D'] [Category E] [Category E'] (P : C ⥤ D') (Q : D' ⥤ D) {F : C ⥤ D}
    (ε : F ⟶ P ⋙ Q) (W : D ⥤ E) (I : E ⥤ E') {J : D ⥤ E'} (β : W ⋙ I ⟶ J) :
    Functor.whiskerRight (Functor.whiskerRight ε W) I ≫
        Functor.whiskerRight (Functor.associator P Q W).hom I ≫
        Functor.whiskerLeft P (Functor.whiskerLeft Q β) =
      Functor.whiskerLeft F β ≫ Functor.whiskerRight ε J := by
  rw [whiskerRight_associator_hom, Category.id_comp]
  exact (Functor.whiskerLeft_comp_whiskerRight ε β).symm

/-- A five-fold composite in which three consecutive factors are themselves triple composites
through retracting pairs, and whose first two factors absorb into a given morphism, collapses to
a triple composite. -/
theorem five_chain {E : Type*} [Category E]
    {A A₁ A₂ N₀ N₀' N₁ N₂ N₃ L₁ L₂ L₃ : E}
    {g1 : A ⟶ A₁} {g2 : A₁ ⟶ A₂} {U : A₂ ⟶ N₀'} {u : A ⟶ N₀} {ex : N₀ ⟶ N₀'}
    {Φ' : N₀' ⟶ N₁} {Φ'' : N₁ ⟶ N₂} {Ψ : N₂ ⟶ N₃} {Φ : N₀ ⟶ N₃}
    {p₁ : N₁ ⟶ L₁} {q₁ : L₁ ⟶ N₁} {p₂ : N₂ ⟶ L₂} {q₂ : L₂ ⟶ N₂} {z : N₃ ⟶ L₃}
    {Λ : A ⟶ L₃} {g3 : A₂ ⟶ L₁} {g4 : L₁ ⟶ L₂} {g5 : L₂ ⟶ L₃}
    (hΛ : Λ = u ≫ Φ ≫ z)
    (h3 : g3 = U ≫ Φ' ≫ p₁) (h4 : g4 = q₁ ≫ Φ'' ≫ p₂) (h5 : g5 = q₂ ≫ Ψ ≫ z)
    (h1 : p₁ ≫ q₁ = 𝟙 N₁) (h2 : p₂ ≫ q₂ = 𝟙 N₂)
    (hex : g1 ≫ g2 ≫ U = u ≫ ex) (hΦ : ex ≫ Φ' ≫ Φ'' ≫ Ψ = Φ) :
    Λ = g1 ≫ g2 ≫ g3 ≫ g4 ≫ g5 := by
  subst hΛ h3 h4 h5 hΦ
  simp only [Category.assoc]
  rw [← Category.assoc p₁ q₁, h1, Category.id_comp, ← Category.assoc p₂ q₂, h2,
    Category.id_comp, ← Category.assoc g2 U, ← Category.assoc g1 (g2 ≫ U), hex]
  simp only [Category.assoc]

/-- Morphisms of functors into quasi-coherent modules are determined by their images under the
inclusion of quasi-coherent modules. -/
theorem whiskerRight_isQuasicoherentι_injective (R : Type u) [CommRing R]
    (Y Z : Over (Spec (.of R)))
    {A B : Scheme.QuasicoherentModules Z.left ⥤ Scheme.QuasicoherentModules Y.left}
    {a b : A ⟶ B}
    (h : Functor.whiskerRight a (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι =
      Functor.whiskerRight b (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι) : a = b :=
  ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
    (Scheme.QuasicoherentModules Z.left)).map_injective h

/-- **The source-change isomorphism of Tag 0FZF, after forgetting quasi-coherence of the
values**, is affine change of source for the pullback--tensor--pushforward formula of Tag 0FZB,
conjugated by the two comparison isomorphisms. -/
theorem whiskerRight_quasicoherentIntegralTransformSourceChangeIso_hom (R : Type u) [CommRing R]
    (X X' Y : Over (Spec (.of R))) [IsAffine X.left] (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    let : IsAffine X'.left := isAffine_of_isAffineHom f.left
    Functor.whiskerRight (quasicoherentIntegralTransformSourceChangeIso R X X' Y f K).hom
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι =
      Functor.whiskerLeft (quasicoherentPushforward f.left)
          (quasicoherentIntegralTransformData R X Y K).comparison.hom ≫
        (integralTransformFormulaSourceChangeIso R X X' Y f K).hom ≫
        (quasicoherentIntegralTransformData R X' Y
          (sourceChangeKernel R X X' Y f K)).comparison.inv := by
  let : IsAffine X'.left := isAffine_of_isAffineHom f.left
  exact ((SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).fullyFaithfulι.whiskeringRight
    (Scheme.QuasicoherentModules X'.left)).map_preimage _

attribute [local implicit_reducible] AlgebraicGeometry.integralTransformQcohFunctor
  AlgebraicGeometry.IntegralTransformQcoh.liftFunctorAlongFullyFaithful

variable (R : Type u) [CommRing R] (X X' X'' Y : Over (Spec (.of R))) [IsAffine X.left]
  (f' : X' ⟶ X) (f'' : X'' ⟶ X') [IsAffineHom f'.left] [IsAffineHom f''.left]
  (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))

/-- **Pseudo-functoriality of the source-change isomorphism of Tag 0FZF**, granted the
corresponding identity for the pullback--tensor--pushforward formula of Tag 0FZB: change of
source along a composite `X'' ⟶ X' ⟶ X` of affine morphisms is the composite of the two changes
of source, up to the identification of the two iterated inverse images of the kernel. -/
theorem quasicoherentIntegralTransformSourceChangeIso_comp_of_formula
    (hform :
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f' f'' rfl)).hom
            (integralTransformFormula R X Y K.obj) ≫
          Functor.whiskerLeft (quasicoherentPushforward f''.left)
            (integralTransformFormulaSourceChangeIso R X X' Y f' K).hom ≫
          (integralTransformFormulaSourceChangeIso R X' X'' Y f''
            (sourceChangeKernel R X X' Y f' K)).hom ≫
          (formulaFunctor R X'' Y).map
            (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv.hom =
        (integralTransformFormulaSourceChangeIso R X X'' Y (f'' ≫ f') K).hom) :
    let : IsAffine X'.left := isAffine_of_isAffineHom f'.left
    let : IsAffine X''.left := isAffine_of_isAffineHom f''.left
    (quasicoherentIntegralTransformSourceChangeIso R X X'' Y (f'' ≫ f') K).hom =
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f' f'' rfl)).hom
          (quasicoherentIntegralTransform R X Y K) ≫
        ((quasicoherentPushforward (Over.Hom.left f'')).associator
              (quasicoherentPushforward (Over.Hom.left f'))
              (quasicoherentIntegralTransform R X Y K)).hom ≫
          (quasicoherentPushforward (Over.Hom.left f'')).whiskerLeft
              (quasicoherentIntegralTransformSourceChangeIso R X X' Y f' K).hom ≫
            (quasicoherentIntegralTransformSourceChangeIso R X' X'' Y f''
                (sourceChangeKernel R X X' Y f' K)).hom ≫
              (integralTransformQcohFunctor R X'' Y).map
                (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv := by
  let : IsAffine X'.left := isAffine_of_isAffineHom f'.left
  let : IsAffine X''.left := isAffine_of_isAffineHom f''.left
  refine whiskerRight_isQuasicoherentι_injective R Y X'' ?_
  simp only [Functor.whiskerRight_comp]
  have hL := whiskerRight_quasicoherentIntegralTransformSourceChangeIso_hom R X X'' Y
    (f'' ≫ f') K
  have h3' := whiskerRight_quasicoherentIntegralTransformSourceChangeIso_hom R X X' Y f' K
  have h3 := whiskerRight_whiskerLeft_comp₃ (quasicoherentPushforward f''.left)
    (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
    (quasicoherentIntegralTransformSourceChangeIso R X X' Y f' K).hom _ _ _ h3'
  have h4 := whiskerRight_quasicoherentIntegralTransformSourceChangeIso_hom R X' X'' Y f''
    (sourceChangeKernel R X X' Y f' K)
  have h5 := whiskerRight_integralTransformQcohFunctor_map R Y X'' _ _
    (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv
  have hex := whisker_exchange_pair (quasicoherentPushforward f''.left)
    (quasicoherentPushforward f'.left)
    (eqToIso (quasicoherentPushforward_eq_comp f' f'' rfl)).hom
    (quasicoherentIntegralTransform R X Y K)
    (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι
    (quasicoherentIntegralTransformData R X Y K).comparison.hom
  refine five_chain hL h3 h4 h5 ?_ ?_ hex hform
  · rw [← Functor.whiskerLeft_comp, Iso.inv_hom_id]
    exact NatTrans.ext (funext fun _ => rfl)
  · exact Iso.inv_hom_id _

/-- **Pseudo-functoriality of the source-change isomorphism of Tag 0FZF**: change of source
along a composite `X'' ⟶ X' ⟶ X` of affine morphisms is the composite of the two changes of
source, up to the identification of the two iterated inverse images of the kernel. -/
theorem quasicoherentIntegralTransformSourceChangeIso_comp :
    let : IsAffine X'.left := isAffine_of_isAffineHom f'.left
    let : IsAffine X''.left := isAffine_of_isAffineHom f''.left
    (quasicoherentIntegralTransformSourceChangeIso R X X'' Y (f'' ≫ f') K).hom =
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f' f'' rfl)).hom
          (quasicoherentIntegralTransform R X Y K) ≫
        ((quasicoherentPushforward (Over.Hom.left f'')).associator
              (quasicoherentPushforward (Over.Hom.left f'))
              (quasicoherentIntegralTransform R X Y K)).hom ≫
          (quasicoherentPushforward (Over.Hom.left f'')).whiskerLeft
              (quasicoherentIntegralTransformSourceChangeIso R X X' Y f' K).hom ≫
            (quasicoherentIntegralTransformSourceChangeIso R X' X'' Y f''
                (sourceChangeKernel R X X' Y f' K)).hom ≫
              (integralTransformQcohFunctor R X'' Y).map
                (sourceChangeKernelCompIso R X X' X'' Y f' f'' K).inv := by
  let : IsAffine X'.left := isAffine_of_isAffineHom f'.left
  let : IsAffine X''.left := isAffine_of_isAffineHom f''.left
  exact quasicoherentIntegralTransformSourceChangeIso_comp_of_formula R X X' X'' Y f' f'' K
    (integralTransformFormulaSourceChangeIso_comp R X X' X'' Y f' f'' K)

end Iterated

end AlgebraicGeometry

end
