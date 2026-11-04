module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactInclusionDerivedEquivalence
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# Derived direct images and exact inclusions of abelian subcategories

Let `ι_V : 𝒜_V ⥤ ℳ_V` and `ι_W : 𝒜_W ⥤ ℳ_W` be exact functors of abelian categories, let
`q_E : ℳ_V ⥤ ℳ_W` be an additive functor and `q : 𝒜_V ⥤ 𝒜_W` a lift of it, `q ⋙ ι_W ≅ ι_V ⋙ q_E`.
Let `(Φ, βΦ)` be a total right derived functor of `q` and `(Rq, βq)` one of `q_E`.  The typical
case is the direct image `j_*` along a morphism of algebraic spaces, restricted to the
quasi-coherent modules: `Φ` is the right derived functor of `j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` and
`Rq` is `Rj_*`.

This file constructs the **canonical comparison** `Φ ⋙ D(ι_W) ⟶ D(ι_V) ⋙ Rq` of the square of
[Stacks, Tag 09TG], and proves that it is invertible exactly when `βq` is invertible at the image
of every K-injective complex of `𝒜_V`; that is, when `Rq` is computed by `q_E` on the K-injective
complexes of `𝒜_V`.

It then proves the step of the proof of [Stacks, Tag 09TG] that uses this square.  Suppose that
`𝒜_V` and `𝒜_X` are full subcategories with right adjoints `Q_V`, `Q_X` of the inclusions and
derived coherators `R_V`, `R_X`, and that `q_E` is right adjoint to an exact `p_E` lifting to
`p ⊣ q`.  If the comparison of `R_V` is invertible at every complex `ι_V K` — which is what the
affine case provides — and if `Rq` is computed by `q_E` on K-injective complexes of `𝒜_V`, then
the comparison of `R_X` is invertible at `ι_X(q I)` for every K-injective complex `I` of `𝒜_V`.
The proof compares the two right derived functors `Rq ⋙ R_X` and `R_V ⋙ Φ` of the isomorphic
functors `q_E ⋙ Q_X` and `Q_V ⋙ q`, at the complex `ι_V I`.

## Main definitions

* `Stacks.DerivedCoherator.pushforwardSquareComparison` — the canonical comparison
  `Φ ⋙ D(ι_W) ⟶ D(ι_V) ⋙ Rq`.

## Main results

* `Stacks.DerivedCoherator.isIso_pushforwardSquareComparison_iff` — it is invertible if and only
  if `βq` is invertible at the image of every K-injective complex of `𝒜_V`.
* `Stacks.DerivedCoherator.isIso_comparison_pushforward_of_kInjective` — the comparison of the
  derived coherator `R_X` is invertible at `ι_X(q I)`.

## References

* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedCoherator

/-! ### The canonical comparison of the square -/

section Square

universe w

variable {𝒜V 𝒜W ℳV ℳW : Type*} [Category* 𝒜V] [Category* 𝒜W] [Category* ℳV] [Category* ℳW]
  [Abelian 𝒜V] [Abelian 𝒜W] [Abelian ℳV] [Abelian ℳW]
  [HasDerivedCategory 𝒜V] [HasDerivedCategory 𝒜W] [HasDerivedCategory ℳV]
  [HasDerivedCategory ℳW] [IsGrothendieckAbelian.{w} 𝒜V]
  (ιV : 𝒜V ⥤ ℳV) [ιV.Additive] [PreservesFiniteLimits ιV] [PreservesFiniteColimits ιV]
  (ιW : 𝒜W ⥤ ℳW) [ιW.Additive] [PreservesFiniteLimits ιW] [PreservesFiniteColimits ιW]
  (q : 𝒜V ⥤ 𝒜W) [q.Additive] (qE : ℳV ⥤ ℳW) [qE.Additive] (e : q ⋙ ιW ≅ ιV ⋙ qE)
  (Φ : DerivedCategory 𝒜V ⥤ DerivedCategory 𝒜W)
  (βΦ : q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Φ)
  [Φ.IsRightDerivedFunctor βΦ (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ))]
  (Rq : DerivedCategory ℳV ⥤ DerivedCategory ℳW)
  (βq : qE.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rq)

/-- The comparison exhibiting `Φ ⋙ D(ι_W)` as a right derived functor of `q ⋙ ι_W`. -/
def squareSourceUnit :
    q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙ ιW.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ Φ ⋙ ιW.mapDerivedCategory :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight βΦ ιW.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

omit [IsGrothendieckAbelian.{w} 𝒜V]
  [Φ.IsRightDerivedFunctor βΦ (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ))] in
/-- The component of `squareSourceUnit` at `X` is the image under `D(ι_W)` of the comparison
`βΦ` at `X`. -/
lemma squareSourceUnit_app (X : HomotopyCategory 𝒜V (ComplexShape.up ℤ)) :
    (squareSourceUnit ιW q Φ βΦ).app X = ιW.mapDerivedCategory.map (βΦ.app X) := by
  simp [squareSourceUnit]

/-- `Φ ⋙ D(ι_W)` is a right derived functor of `q ⋙ ι_W`: at a K-injective complex the
comparison `βΦ` is invertible. -/
lemma isRightDerivedFunctor_squareSource :
    (Φ ⋙ ιW.mapDerivedCategory).IsRightDerivedFunctor (squareSourceUnit ιW q Φ βΦ)
      (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => by
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Φ βΦ I
    rw [squareSourceUnit_app]
    infer_instance

/-- The isomorphism `q ⋙ Qh ⋙ D(ι_W) ≅ ι_V ⋙ q_E ⋙ Qh` on the homotopy category of `𝒜_V`. -/
def squareTargetIsoLeft :
    q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙ ιW.mapDerivedCategory ≅
      ιV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ qE.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  Functor.isoWhiskerLeft _ ιW.mapDerivedCategoryFactorsh ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (ιV ⋙ qE)) (ComplexShape.up ℤ)).symm)
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- The isomorphism `ι_V ⋙ Qh ⋙ Rq ≅ Qh ⋙ D(ι_V) ⋙ Rq` on the homotopy category of `𝒜_V`. -/
def squareTargetIsoRight :
    ιV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙ Rq ≅
      DerivedCategory.Qh ⋙ ιV.mapDerivedCategory ⋙ Rq :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ιV.mapDerivedCategoryFactorsh.symm Rq ≪≫
    Functor.associator _ _ _

/-- The map along which `pushforwardSquareComparison` is defined: on a complex `K` of `𝒜_V` it
is the comparison `βq` of `Rq` at `ι_V K`, read through `q K` and `ι_V K`. -/
def squareTargetMap :
    q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙ ιW.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ ιV.mapDerivedCategory ⋙ Rq :=
  (squareTargetIsoLeft ιV ιW q qE e).hom ≫
    Functor.whiskerLeft (ιV.mapHomotopyCategory (ComplexShape.up ℤ)) βq ≫
    (squareTargetIsoRight ιV Rq).hom

omit [IsGrothendieckAbelian.{w} 𝒜V] in
/-- The component of `squareTargetMap` at `X` is invertible exactly when the comparison `βq` of
`Rq` is invertible at `ι_V X`. -/
lemma isIso_squareTargetMap_app_iff (X : HomotopyCategory 𝒜V (ComplexShape.up ℤ)) :
    IsIso ((squareTargetMap ιV ιW q qE e Rq βq).app X) ↔
      IsIso (βq.app ((ιV.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) := by
  have h : (squareTargetMap ιV ιW q qE e Rq βq).app X =
      (squareTargetIsoLeft ιV ιW q qE e).hom.app X ≫
        βq.app ((ιV.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        (squareTargetIsoRight ιV Rq).hom.app X := by
    simp [squareTargetMap]
  rw [h, isIso_comp_left_iff, isIso_comp_right_iff]

/-- **The canonical comparison of the square of [Stacks, Tag 09TG]**,
`Φ ⋙ D(ι_W) ⟶ D(ι_V) ⋙ Rq`: the unique natural transformation out of the right derived functor
`Φ ⋙ D(ι_W)` of `q ⋙ ι_W` which on a complex `K` of `𝒜_V` is the comparison of `Rq` at `ι_V K`.
The square *commutes* when this comparison is invertible. -/
def pushforwardSquareComparison :
    Φ ⋙ ιW.mapDerivedCategory ⟶ ιV.mapDerivedCategory ⋙ Rq :=
  have := isRightDerivedFunctor_squareSource ιW q Φ βΦ
  (Φ ⋙ ιW.mapDerivedCategory).rightDerivedDesc (squareSourceUnit ιW q Φ βΦ)
    (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ)) (ιV.mapDerivedCategory ⋙ Rq)
    (squareTargetMap ιV ιW q qE e Rq βq)

/-- The defining factorisation of `pushforwardSquareComparison`, at a complex `X` of `𝒜_V`:
after `squareSourceUnit` it is `squareTargetMap`. -/
lemma pushforwardSquareComparison_fac_app (X : HomotopyCategory 𝒜V (ComplexShape.up ℤ)) :
    (squareSourceUnit ιW q Φ βΦ).app X ≫
        (pushforwardSquareComparison ιV ιW q qE e Φ βΦ Rq βq).app (DerivedCategory.Qh.obj X) =
      (squareTargetMap ιV ιW q qE e Rq βq).app X := by
  have := isRightDerivedFunctor_squareSource ιW q Φ βΦ
  exact (Φ ⋙ ιW.mapDerivedCategory).rightDerived_fac_app (squareSourceUnit ιW q Φ βΦ)
    (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ)) (ιV.mapDerivedCategory ⋙ Rq)
    (squareTargetMap ιV ιW q qE e Rq βq) X

/-- **The square of [Stacks, Tag 09TG] commutes exactly when `Rq` is computed by `q_E` on the
K-injective complexes of `𝒜_V`.**  At a K-injective complex `I` the comparison `βΦ` is
invertible, so the defining factorisation of the canonical comparison identifies it there with
`βq` at `ι_V I`; and a transformation of functors on `D(𝒜_V)` is invertible as soon as it is at
the K-injective complexes. -/
theorem isIso_pushforwardSquareComparison_iff :
    IsIso (pushforwardSquareComparison ιV ιW q qE e Φ βΦ Rq βq) ↔
      ∀ (I : CochainComplex 𝒜V ℤ), I.IsKInjective →
        IsIso (βq.app ((ιV.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I))) := by
  constructor
  · intro hc I hI
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Φ βΦ I
    have h := pushforwardSquareComparison_fac_app ιV ιW q qE e Φ βΦ Rq βq
      ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I)
    rw [← isIso_squareTargetMap_app_iff ιV ιW q qE e Rq βq, ← h, squareSourceUnit_app]
    infer_instance
  · intro h
    refine Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives _ fun I hI => ?_
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Φ βΦ I
    have hfac := pushforwardSquareComparison_fac_app ιV ιW q qE e Φ βΦ Rq βq
      ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I)
    have ht : IsIso ((squareTargetMap ιV ιW q qE e Rq βq).app
        ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I)) :=
      (isIso_squareTargetMap_app_iff ιV ιW q qE e Rq βq _).2 (h I hI)
    rw [← hfac, squareSourceUnit_app] at ht
    exact IsIso.of_isIso_comp_left (ιW.mapDerivedCategory.map (βΦ.app _)) _

end Square

/-! ### The comparison of the derived coherator on a derived direct image -/

section Coherator

universe w₁ w₂ w₃

variable {𝒜X ℳX 𝒜V ℳV : Type*} [Category* 𝒜X] [Category* ℳX] [Category* 𝒜V] [Category* ℳV]
  [Abelian 𝒜X] [Abelian ℳX] [Abelian 𝒜V] [Abelian ℳV]
  [HasDerivedCategory 𝒜X] [HasDerivedCategory ℳX] [HasDerivedCategory 𝒜V]
  [HasDerivedCategory ℳV]
  [IsGrothendieckAbelian.{w₁} ℳX] [IsGrothendieckAbelian.{w₂} ℳV]
  [IsGrothendieckAbelian.{w₃} 𝒜V]
  (ιX : 𝒜X ⥤ ℳX) [ιX.Additive] [PreservesFiniteLimits ιX] [PreservesFiniteColimits ιX]
  (ιV : 𝒜V ⥤ ℳV) [ιV.Additive] [PreservesFiniteLimits ιV] [PreservesFiniteColimits ιV]
  [ιV.Full] [ιV.Faithful]
  {QX : ℳX ⥤ 𝒜X} [QX.Additive] (adjX : ιX ⊣ QX)
  {QV : ℳV ⥤ 𝒜V} [QV.Additive] (adjV : ιV ⊣ QV)
  (RX : DerivedCategory ℳX ⥤ DerivedCategory 𝒜X)
  (βX : QX.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RX)
  [RX.IsRightDerivedFunctor βX (HomotopyCategory.quasiIso ℳX (ComplexShape.up ℤ))]
  (RV : DerivedCategory ℳV ⥤ DerivedCategory 𝒜V)
  (βV : QV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RV)
  [RV.IsRightDerivedFunctor βV (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ))]
  {pE : ℳX ⥤ ℳV} [pE.Additive] [PreservesFiniteLimits pE] [PreservesFiniteColimits pE]
  {qE : ℳV ⥤ ℳX} [qE.Additive] (adjE : pE ⊣ qE)
  {p : 𝒜X ⥤ 𝒜V} {q : 𝒜V ⥤ 𝒜X} [q.Additive] (adjP : p ⊣ q) (eP : ιX ⋙ pE ≅ p ⋙ ιV)
  (e : q ⋙ ιX ≅ ιV ⋙ qE)
  (Rq : DerivedCategory ℳV ⥤ DerivedCategory ℳX)
  (βq : qE.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rq)
  [Rq.IsRightDerivedFunctor βq (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ))]

/-- The two right adjoints `q_E ⋙ Q_X` and `Q_V ⋙ q` of the isomorphic functors
`ι_X ⋙ p_E` and `p ⋙ ι_V` agree. -/
def pushforwardCoheratorIso : qE ⋙ QX ≅ QV ⋙ q :=
  (adjX.comp adjE).rightAdjointUniq ((adjP.comp adjV).ofNatIsoLeft eP.symm)

/-- The comparison exhibiting `Rq ⋙ R_X` as a right derived functor of `q_E ⋙ Q_X`. -/
def pushforwardCoheratorUnit :
    (qE ⋙ QX).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rq ⋙ RX :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (qE ⋙ QX))
      (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (qE.mapHomotopyCategory (ComplexShape.up ℤ)) βX ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight βq RX ≫ (Functor.associator _ _ _).hom

omit [IsGrothendieckAbelian.{w₁} ℳX] [IsGrothendieckAbelian.{w₂} ℳV]
  [RX.IsRightDerivedFunctor βX (HomotopyCategory.quasiIso ℳX (ComplexShape.up ℤ))]
  [Rq.IsRightDerivedFunctor βq (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ))] in
/-- The component of `pushforwardCoheratorUnit` at `X`: the comparison `βX` at `q_E X`, then
the image under `R_X` of the comparison `βq` at `X`. -/
lemma pushforwardCoheratorUnit_app (X : HomotopyCategory ℳV (ComplexShape.up ℤ)) :
    (pushforwardCoheratorUnit RX βX Rq βq).app X =
      (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (qE ⋙ QX))
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _).hom.app X ≫
        βX.app ((qE.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫ RX.map (βq.app X) := by
  simp [pushforwardCoheratorUnit]

include adjE in
/-- `Rq ⋙ R_X` is a right derived functor of `q_E ⋙ Q_X`: `q_E` preserves K-injective complexes,
being right adjoint to an exact functor. -/
lemma isRightDerivedFunctor_pushforwardCoheratorUnit :
    (Rq ⋙ RX).IsRightDerivedFunctor (pushforwardCoheratorUnit RX βX Rq βq)
      (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => by
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Rq βq I
    have := CochainComplex.isKInjective_mapHomologicalComplex_of_exact qE pE adjE I
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RX βX
      ((qE.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    rw [pushforwardCoheratorUnit_app]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)

variable (Φ : DerivedCategory 𝒜V ⥤ DerivedCategory 𝒜X)
  (βΦ : q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Φ)
  [Φ.IsRightDerivedFunctor βΦ (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ))]

/-- The comparison exhibiting `R_V ⋙ Φ` as a right derived functor of `Q_V ⋙ q`. -/
def coheratorPushforwardUnit :
    (QV ⋙ q).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RV ⋙ Φ :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (QV ⋙ q))
      (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (QV.mapHomotopyCategory (ComplexShape.up ℤ)) βΦ ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight βV Φ ≫ (Functor.associator _ _ _).hom

omit [IsGrothendieckAbelian.{w₂} ℳV] [IsGrothendieckAbelian.{w₃} 𝒜V]
  [RV.IsRightDerivedFunctor βV (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ))]
  [Φ.IsRightDerivedFunctor βΦ (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ))] in
/-- The component of `coheratorPushforwardUnit` at `X`: the comparison `βΦ` at `Q_V X`, then
the image under `Φ` of the comparison `βV` at `X`. -/
lemma coheratorPushforwardUnit_app (X : HomotopyCategory ℳV (ComplexShape.up ℤ)) :
    (coheratorPushforwardUnit RV βV Φ βΦ).app X =
      (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (QV ⋙ q))
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _).hom.app X ≫
        βΦ.app ((QV.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫ Φ.map (βV.app X) := by
  simp [coheratorPushforwardUnit]

include adjV in
omit [ιV.Full] [ιV.Faithful] in
/-- `R_V ⋙ Φ` is a right derived functor of `Q_V ⋙ q`: `Q_V` preserves K-injective complexes,
being right adjoint to the exact `ι_V`. -/
lemma isRightDerivedFunctor_coheratorPushforwardUnit :
    (RV ⋙ Φ).IsRightDerivedFunctor (coheratorPushforwardUnit RV βV Φ βΦ)
      (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => by
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RV βV I
    have := CochainComplex.isKInjective_mapHomologicalComplex_of_exact QV ιV adjV I
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Φ βΦ
      ((QV.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    rw [coheratorPushforwardUnit_app]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)

include adjX adjV adjE adjP eP e Φ βΦ in
omit [PreservesFiniteLimits ιX] [PreservesFiniteColimits ιX] in
/-- **The comparison of the derived coherator `R_X` is invertible at `ι_X(q I)`** for every
K-injective complex `I` of `𝒜_V`, as soon as the comparison of `R_V` is invertible at every
complex `ι_V K` and `Rq` is computed by `q_E` on the K-injective complexes of `𝒜_V`.

The right derived functors `Rq ⋙ R_X` and `R_V ⋙ Φ` of the isomorphic functors `q_E ⋙ Q_X` and
`Q_V ⋙ q` agree compatibly with their comparisons.  At `ι_V I` the comparison of `R_V ⋙ Φ` is
invertible — `Q_V ι_V I ≅ I` is K-injective and `R_V` has invertible comparison at `ι_V I` —
so that of `Rq ⋙ R_X` is, and its second factor, the comparison of `Rq` at `ι_V I`, is invertible
by hypothesis. -/
theorem isIso_comparison_pushforward_of_kInjective_of_rightDerived
    (hV : ∀ K : HomotopyCategory 𝒜V (ComplexShape.up ℤ),
      IsIso (βV.app ((ιV.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    (hq : ∀ (I : CochainComplex 𝒜V ℤ), I.IsKInjective →
      IsIso (βq.app ((ιV.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I))))
    (I : CochainComplex 𝒜V ℤ) [I.IsKInjective] :
    IsIso (βX.app ((ιX.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((q.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I)))) := by
  have h₁ := isRightDerivedFunctor_pushforwardCoheratorUnit (RX := RX) (βX := βX) (adjE := adjE)
    (Rq := Rq) (βq := βq)
  have h₂ := isRightDerivedFunctor_coheratorPushforwardUnit (ιV := ιV) (adjV := adjV) (RV := RV)
    (βV := βV) (Φ := Φ) (βΦ := βΦ)
  set X := (ιV.mapHomotopyCategory (ComplexShape.up ℤ)).obj
    ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I) with hX
  -- the comparison of `R_V ⋙ Φ` at `ι_V I` is invertible
  have hu : IsIso adjV.unit := adjV.unit_isIso_of_L_fully_faithful
  have hKI : CochainComplex.IsKInjective ((QV.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((ιV.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    CochainComplex.isKInjective_of_iso (HomologicalComplex.Hom.isoOfComponents
      (fun n => asIso (adjV.unit.app (I.X n))) (fun i j _ => by simp))
  have hΦ := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ Φ βΦ
    ((QV.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((ιV.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  have hVX := hV ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I)
  have hu₂ : IsIso ((coheratorPushforwardUnit RV βV Φ βΦ).app X) := by
    rw [coheratorPushforwardUnit_app]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hΦ inferInstance)
  -- hence so is the comparison of `Rq ⋙ R_X`
  have hfac := Functor.rightDerivedNatTrans_app (Rq ⋙ RX) (RV ⋙ Φ)
    (pushforwardCoheratorUnit RX βX Rq βq) (coheratorPushforwardUnit RV βV Φ βΦ)
    (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ))
    (Functor.whiskerRight (Stacks.Homology.mapHomotopyCategoryIso
      (pushforwardCoheratorIso (adjX := adjX) (adjV := adjV) (adjE := adjE) (adjP := adjP)
        (eP := eP)) (ComplexShape.up ℤ)).hom DerivedCategory.Qh) X
  set θ := Functor.rightDerivedNatTrans (Rq ⋙ RX) (RV ⋙ Φ)
    (pushforwardCoheratorUnit RX βX Rq βq) (coheratorPushforwardUnit RV βV Φ βΦ)
    (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ))
    (Functor.whiskerRight (Stacks.Homology.mapHomotopyCategoryIso
      (pushforwardCoheratorIso (adjX := adjX) (adjV := adjV) (adjE := adjE) (adjP := adjP)
        (eP := eP)) (ComplexShape.up ℤ)).hom DerivedCategory.Qh)
  have hθ : IsIso θ := (Functor.rightDerivedNatIso (Rq ⋙ RX) (RV ⋙ Φ)
    (pushforwardCoheratorUnit RX βX Rq βq) (coheratorPushforwardUnit RV βV Φ βΦ)
    (HomotopyCategory.quasiIso ℳV (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
      (pushforwardCoheratorIso (adjX := adjX) (adjV := adjV) (adjE := adjE) (adjP := adjP)
        (eP := eP)) (ComplexShape.up ℤ)) DerivedCategory.Qh)).isIso_hom
  have hu₁ : IsIso ((pushforwardCoheratorUnit RX βX Rq βq).app X) := by
    have : IsIso ((pushforwardCoheratorUnit RX βX Rq βq).app X ≫
        θ.app (DerivedCategory.Qh.obj X)) := by
      rw [hfac]
      exact IsIso.comp_isIso' (by simp only [Functor.whiskerRight_app]; infer_instance) hu₂
    exact IsIso.of_isIso_comp_right _ (θ.app (DerivedCategory.Qh.obj X))
  -- and the comparison of `Rq` at `ι_V I` is invertible
  have hqX : IsIso (βq.app X) := hq I inferInstance
  rw [pushforwardCoheratorUnit_app] at hu₁
  have h₃ : IsIso (βX.app ((qE.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
      RX.map (βq.app X)) := IsIso.of_isIso_comp_left
    ((Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (qE ⋙ QX))
      (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫ Functor.associator _ _ _).hom.app X) _
  have h₄ : IsIso (βX.app ((qE.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) :=
    IsIso.of_isIso_comp_right _ (RX.map (βq.app X))
  -- finally `q_E (ι_V I) ≅ ι_X (q I)`
  have e' : (ιX.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((q.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I)) ≅
      (qE.mapHomotopyCategory (ComplexShape.up ℤ)).obj X :=
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (ιV ⋙ qE))
        (ComplexShape.up ℤ)).symm).app _
  exact (NatTrans.isIso_app_iff_of_iso βX e').2 h₄

omit [IsGrothendieckAbelian.{w₃} 𝒜V] in
/-- A total right derived functor of an additive functor out of a Grothendieck abelian category
exists. -/
lemma hasRightDerivedFunctor_of_isGrothendieckAbelian {A B : Type*} [Category* A]
    [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [IsGrothendieckAbelian.{w₃} A] (F : A ⥤ B) [F.Additive] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0}
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    Stacks.Cohomology.Localization.enoughKInjectives).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

include adjX adjV adjE adjP eP e in
omit [PreservesFiniteLimits ιX] [PreservesFiniteColimits ιX] in
/-- **The comparison of the derived coherator `R_X` is invertible at `ι_X(q I)`** for every
K-injective complex `I` of `𝒜_V`, as soon as the comparison of `R_V` is invertible at every
complex `ι_V K` and `Rq` is computed by `q_E` on the K-injective complexes of `𝒜_V`.  This is
`isIso_comparison_pushforward_of_kInjective_of_rightDerived` at the chosen total right derived
functor of `q`. -/
theorem isIso_comparison_pushforward_of_kInjective
    (hV : ∀ K : HomotopyCategory 𝒜V (ComplexShape.up ℤ),
      IsIso (βV.app ((ιV.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    (hq : ∀ (I : CochainComplex 𝒜V ℤ), I.IsKInjective →
      IsIso (βq.app ((ιV.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I))))
    (I : CochainComplex 𝒜V ℤ) [I.IsKInjective] :
    IsIso (βX.app ((ιX.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((q.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient 𝒜V (ComplexShape.up ℤ)).obj I)))) :=
  have := hasRightDerivedFunctor_of_isGrothendieckAbelian.{w₃} q
  isIso_comparison_pushforward_of_kInjective_of_rightDerived (ιX := ιX) (ιV := ιV) (adjX := adjX)
    (adjV := adjV) (RX := RX) (βX := βX) (RV := RV) (βV := βV) (adjE := adjE) (adjP := adjP)
    (eP := eP) (e := e) (Rq := Rq) (βq := βq)
    (Φ := (q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
      DerivedCategory.Qh (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ)))
    (βΦ := (q.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso 𝒜V (ComplexShape.up ℤ))) hV hq I

end Coherator

end Stacks.DerivedCoherator
