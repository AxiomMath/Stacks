module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
public import StacksCore.Tactic.StacksAttribute

/-!
# The structure sheaf of a pointed smooth projective curve after base change

Let `k` be a field and `X` a smooth projective curve over `k` with a `k`-rational point. Then
`𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every `k`-scheme `T`.

## Main results

* `Stacks.AlgebraicGeometry.AffinePushforward.unitToPushforwardUnit_eq_baseChangeNatTrans`: the
  comparison `𝒪 ⟶ f_*𝒪` of a commutative square's right edge is the base-change morphism of the
  square, conjugated by the identifications of the inverse images of the structure sheaves.
* `Stacks.AlgebraicGeometry.AffinePushforward.isIso_unitToPushforwardUnit_of_isPullback`:
  `f_*𝒪_X = 𝒪_S` is inherited by a base change along a flat morphism.
* `AlgebraicGeometry.isIso_c_of_section_of_universallyClosed`: a universally closed morphism from
  an integral scheme to the spectrum of a field which admits a section has `f_*𝒪_X = 𝒪_S`.
* `AlgebraicGeometry.isIso_c_baseChange_of_isCurve_of_section`: for a smooth projective curve
  `f : X ⟶ Spec k` with a `k`-rational point, `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an isomorphism for every
  `k`-scheme `T`.

## Implementation notes

The conclusion is stated as `IsIso (pullback.snd f g).toLRSHom.toHom.c`, invertibility of the
comparison of sheaves of rings, while flat base change in degree zero
(`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`) is stated
for sheaves of modules. The two spellings are identified by
`Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit`.

Smoothness and dimension one are not used: it suffices that `X` is integral and `f` universally
closed, so that `Γ(X, 𝒪_X)` is a field.

## References

* [Stacks Project, Tag 0B9U](https://stacks.math.columbia.edu/tag/0B9U)
* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffinePushforward

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The comparison `𝒪 ⟶ h_*𝒪` is unchanged by transport along an equality of morphisms. -/
private theorem unitToPushforwardUnit_pushforwardCongr {a b : X' ⟶ S} (e : a = b) :
    Scheme.Modules.unitToPushforwardUnit a ≫
        (Scheme.Modules.pushforwardCongr e).hom.app (Scheme.unitModule X') =
      Scheme.Modules.unitToPushforwardUnit b := by
  subst e
  have hcongr : Scheme.Modules.pushforwardCongr (rfl : a = a) = Iso.refl _ := by
    ext M U; simp
  rw [hcongr, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

/-- The unit of the pullback--pushforward adjunction of `h` at `𝒪_B`, followed by the image under
`h_*` of the identification `h^*𝒪_B ≅ 𝒪_A`, is the comparison `𝒪_B ⟶ h_*𝒪_A`. -/
private theorem unit_app_comp_pullbackUnitIso {A B : Scheme.{u}} (h : A ⟶ B) :
    (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app (Scheme.unitModule B) ≫
        (Scheme.Modules.pushforward h).map (Scheme.Modules.pullbackUnitIso h).hom =
      Scheme.Modules.unitToPushforwardUnit h := by
  simpa only [Adjunction.homEquiv_unit] using Scheme.Modules.pullbackUnitIso_homEquiv h

/-- **The base-change morphism computes the comparison `𝒪_{S'} ⟶ f'_*𝒪_{X'}`.** For a
commutative square `g' ≫ f = f' ≫ g` of schemes, the comparison of the right edge is obtained
from the comparison of the left edge by applying `g^*`, following with the base-change morphism
at the structure sheaf of `X`, and identifying the inverse images of the two structure sheaves
with structure sheaves. -/
theorem unitToPushforwardUnit_eq_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pullbackUnitIso g).hom ≫ Scheme.Modules.unitToPushforwardUnit f' =
      (Scheme.Modules.pullback g).map (Scheme.Modules.unitToPushforwardUnit f) ≫
        (baseChangeNatTrans w).app (Scheme.unitModule X) ≫
        (Scheme.Modules.pushforward f').map (Scheme.Modules.pullbackUnitIso g').hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  conv_lhs => rw [← Category.assoc, unit_app_comp_pullbackUnitIso g]
  calc Scheme.Modules.unitToPushforwardUnit g ≫
        (Scheme.Modules.pushforward g).map (Scheme.Modules.unitToPushforwardUnit f')
      = Scheme.Modules.unitToPushforwardUnit (f' ≫ g) ≫
          (Scheme.Modules.pushforwardComp f' g).inv.app (Scheme.unitModule X') := by
        rw [← Scheme.Modules.unitToPushforwardUnit_comp f' g]; simp
    _ = Scheme.Modules.unitToPushforwardUnit (g' ≫ f) ≫
          (Scheme.Modules.pushforwardCongr w).hom.app (Scheme.unitModule X') ≫
          (Scheme.Modules.pushforwardComp f' g).inv.app (Scheme.unitModule X') := by
        rw [← Category.assoc, unitToPushforwardUnit_pushforwardCongr w]
    _ = Scheme.Modules.unitToPushforwardUnit f ≫
          (Scheme.Modules.pushforward f).map (Scheme.Modules.unitToPushforwardUnit g') ≫
          (Scheme.Modules.pushforwardComp g' f).hom.app (Scheme.unitModule X') ≫
          (Scheme.Modules.pushforwardCongr w).hom.app (Scheme.unitModule X') ≫
          (Scheme.Modules.pushforwardComp f' g).inv.app (Scheme.unitModule X') := by
        rw [← Scheme.Modules.unitToPushforwardUnit_comp g' f]; simp
    _ = Scheme.Modules.unitToPushforwardUnit f ≫
          (Scheme.Modules.pushforward f).map (Scheme.Modules.unitToPushforwardUnit g') ≫
          (pushforwardSquareIso w).hom.app (Scheme.unitModule X') := by
        rw [show (pushforwardSquareIso w).hom.app (Scheme.unitModule X') =
          (Scheme.Modules.pushforwardComp g' f).hom.app (Scheme.unitModule X') ≫
            (Scheme.Modules.pushforwardCongr w).hom.app (Scheme.unitModule X') ≫
            (Scheme.Modules.pushforwardComp f' g).inv.app (Scheme.unitModule X') from by
              simp [pushforwardSquareIso]]
    _ = Scheme.Modules.unitToPushforwardUnit f ≫
          (Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app (Scheme.unitModule X) ≫
              (Scheme.Modules.pushforward g').map (Scheme.Modules.pullbackUnitIso g').hom) ≫
          (pushforwardSquareIso w).hom.app (Scheme.unitModule X') := by
        rw [unit_app_comp_pullbackUnitIso g']
    _ = Scheme.Modules.unitToPushforwardUnit f ≫
          (Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
              (Scheme.unitModule X)) ≫
          (pushforwardSquareIso w).hom.app
            ((Scheme.Modules.pullback g').obj (Scheme.unitModule X)) ≫
          (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f').map
            (Scheme.Modules.pullbackUnitIso g').hom) := by
        rw [Functor.map_comp, Category.assoc]
        refine congrArg (fun z => Scheme.Modules.unitToPushforwardUnit f ≫
          (Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app
              (Scheme.unitModule X)) ≫ z) ?_
        exact (pushforwardSquareIso w).hom.naturality
          (Scheme.Modules.pullbackUnitIso g').hom
    _ = Scheme.Modules.unitToPushforwardUnit f ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
              ((Scheme.Modules.pushforward f).obj (Scheme.unitModule X)) ≫
            (Scheme.Modules.pushforward g).map
              ((baseChangeNatTrans w).app (Scheme.unitModule X))) ≫
          (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f').map
            (Scheme.Modules.pullbackUnitIso g').hom) := by
        rw [← FlatBaseChangeCohomology.pushforward_unit_comp_pushforwardSquareIso w
          (Scheme.unitModule X)]
        simp
    _ = _ := by
        have hnat : (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
              (Scheme.unitModule S) ≫
            (Scheme.Modules.pushforward g).map ((Scheme.Modules.pullback g).map
              (Scheme.Modules.unitToPushforwardUnit f)) =
            Scheme.Modules.unitToPushforwardUnit f ≫
              (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
                ((Scheme.Modules.pushforward f).obj (Scheme.unitModule X)) :=
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality
            (Scheme.Modules.unitToPushforwardUnit f)).symm
        simp only [← Category.assoc]
        rw [hnat]

/-- **`f_*𝒪_X = 𝒪_S` is inherited by a flat base change.** For a cartesian square whose base
change `g` is flat and whose quasi-compact quasi-separated right edge `f` satisfies
`f_*𝒪_X = 𝒪_S`, the base change `f'` satisfies `f'_*𝒪_{X'} = 𝒪_{S'}`. -/
@[sga "7 VII 1.3.8" "partial"]
theorem isIso_unitToPushforwardUnit_of_isPullback (H : IsPullback g' f' f g)
    [Flat g] [QuasiCompact f] [QuasiSeparated f]
    (hf : IsIso (Scheme.Modules.unitToPushforwardUnit f)) :
    IsIso (Scheme.Modules.unitToPushforwardUnit f') := by
  have hbc : IsIso ((baseChangeNatTrans H.w).app (Scheme.unitModule X)) :=
    FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H (Scheme.unitModule X)
  have hrhs : IsIso ((Scheme.Modules.pullback g).map
      (Scheme.Modules.unitToPushforwardUnit f) ≫
      (baseChangeNatTrans H.w).app (Scheme.unitModule X) ≫
      (Scheme.Modules.pushforward f').map (Scheme.Modules.pullbackUnitIso g').hom) := by
    have : IsIso ((Scheme.Modules.pullback g).map
      (Scheme.Modules.unitToPushforwardUnit f)) := inferInstance
    infer_instance
  have hcomp : IsIso ((Scheme.Modules.pullbackUnitIso g).hom ≫
      Scheme.Modules.unitToPushforwardUnit f') := by
    rw [unitToPushforwardUnit_eq_baseChangeNatTrans H.w]; exact hrhs
  exact IsIso.of_isIso_comp_left (Scheme.Modules.pullbackUnitIso g).hom
    (Scheme.Modules.unitToPushforwardUnit f')

end Stacks.AlgebraicGeometry.AffinePushforward

namespace AlgebraicGeometry

/-- **A universally closed morphism from an integral scheme to the spectrum of a field which
admits a section has only constant functions.** The comparison of sheaves of rings of `f` is an
isomorphism, that is, `f_*𝒪_X = 𝒪_S`. -/
theorem isIso_c_of_section_of_universallyClosed {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    IsIso f.toLRSHom.toHom.c := by
  let _ : Field Γ(X, ⊤) := (isField_of_universallyClosed k f).toField
  set α : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  set β : Γ(X, ⊤) →+* k := (Scheme.ΓSpecIso (.of k)).hom.hom.comp σ.appTop.hom
  have hring : σ.appTop.hom.comp f.appTop.hom = RingHom.id _ :=
    congrArg CommRingCat.Hom.hom (congrArg Scheme.Hom.appTop hσ)
  have hleft : Function.LeftInverse β α := by
    intro x
    have h : σ.appTop.hom (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x)) =
        (Scheme.ΓSpecIso (.of k)).inv.hom x := DFunLike.congr_fun hring _
    show (Scheme.ΓSpecIso (.of k)).hom.hom
      (σ.appTop.hom (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x))) = x
    rw [h]
    simp
  have hαiso : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨hleft.injective, fun y => ⟨β y, β.injective (hleft (β y))⟩⟩
  have hf : IsIso f.appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  exact (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_bijective_appTop f).2
    (ConcreteCategory.bijective_of_isIso f.appTop)

/-- Let `k` be a field and let `X` be a smooth projective curve over `k` with a `k`-rational
point, given as a section `σ` of its structure morphism `f`. Then `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an
isomorphism for every `k`-scheme `T`. -/
@[stacks 0B9U]
theorem isIso_c_baseChange_of_isCurve_of_section {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) :
    IsIso (pullback.snd f g).toLRSHom.toHom.c := by
  have hf : IsIso (Scheme.Modules.unitToPushforwardUnit f) :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      f).1 (isIso_c_of_section_of_universallyClosed f σ hσ)
  exact (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
    (pullback.snd f g)).2
    (Stacks.AlgebraicGeometry.AffinePushforward.isIso_unitToPushforwardUnit_of_isPullback
      (IsPullback.of_hasPullback f g) hf)

end AlgebraicGeometry

end
