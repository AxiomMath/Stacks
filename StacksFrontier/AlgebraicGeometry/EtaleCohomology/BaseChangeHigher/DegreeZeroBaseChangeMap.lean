module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactRightDerivedPlusSingleHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.DerivedSquareUnitSingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting

/-!
# The base change map on higher direct images, in degree zero

For a commutative square of schemes

```
Y  --h-->  X'
|e         |f'
T  --g-->  S
```

the base change map `Stacks.EtaleCohomology.higherBaseChangeMapAb` in degree `q` is the
degree-`q` cohomology of the derived base change comparison of [Stacks, Tag 0F02]. In degree
zero, `R⁰g_* = g_*` and `R⁰h_* = h_*`, and this file proves that the base change map is then the
underived base change map `Stacks.EtaleCohomology.smallEtaleBaseChangeAb`, the mate of the
identification of the two composite direct images around the square.

The identification `g_* ≅ R⁰g_*` used is `Stacks.EtaleCohomology.smallEtaleRightDerivedZeroIso`:
the canonical isomorphism `g_* ≅ H⁰(Rg_*((-)[0]))` of [Stacks, Tag 05TD] (3), read in the
injective-resolution indexing through `Stacks.DerivedIndexing.rightDerivedIso`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleRightDerivedZeroIso` — `g_* ≅ R⁰g_*`.

## Main results

* `Stacks.EtaleCohomology.higherBaseChangeMapAb_zero` — **the base change map in degree zero is
  the underived one.**

## Implementation notes

The proof is the descent of the underived map along the derived-functor unit on complexes
concentrated in degree zero, `Stacks.Cohomology.BaseChange.unitSingle_comp_derived`, read by
`H⁰`. The two identifications of the source and target of the base change map with cohomology of
derived composites are compared with the derived-functor units by
`Stacks.DerivedFunctor.isoRightDerivedPlusSingle_hom_app_comp_exactRightDerivedPlusHomologyIso`
and `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom`; the comparison of the two
indexings of the right derived functors cancels.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- forced by `Stacks.EtaleCohomology.higherBaseChangeMapAb`
-- (`BaseChangeHigher/BaseChangeCondition.lean:154`)
attribute [local instance] HasDerivedCategory.standard

/-- `R⁰g_*`, the zeroth right derived functor of the direct image of abelian sheaves on the small
étale sites. It is named so that a statement about `R⁰g_*` in a module whose imports carry further
instances of `HasSheafify` or `EnoughInjectives` for these sites still refers to the same functor
as the higher direct images of `Stacks.EtaleCohomology.higherBaseChangeMapAb`: the abelian
structure and the injective resolutions inside `CategoryTheory.Functor.rightDerived` are those
found here. -/
abbrev smallEtaleRightDerivedZero {T S : Scheme.{u}} (g : T ⟶ S) :
    Sheaf (smallEtaleTopology T) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology S) Ab.{u + 1} :=
  (smallEtalePushforwardAb g).rightDerived 0

/-- **`g_* ≅ R⁰g_*`** for the direct image of abelian sheaves on the small étale sites: the
canonical isomorphism `g_* ≅ H⁰(Rg_*((-)[0]))` of [Stacks, Tag 05TD] (3), the direct image being
left exact, read in the injective-resolution indexing of the right derived functors. -/
def smallEtaleRightDerivedZeroIso {T S : Scheme.{u}} (g : T ⟶ S) :
    smallEtalePushforwardAb g ≅ (smallEtalePushforwardAb g).rightDerived 0 :=
  haveI : (smallEtalePushforwardAb g).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb g⟩⟩
  (smallEtalePushforwardAb g).isoRightDerivedPlusSingle 0 ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).symm

/-- Solving `t = r ≫ x` for `x ≫ t⁻¹`, for two isomorphisms `t` and `r`. -/
private theorem comp_inv_eq_of_hom_eq {E : Type*} [Category* E] {A B C : E} (t : A ≅ B) (r : A ≅ C)
    (x : C ⟶ B) (h : t.hom = r.hom ≫ x) : x ≫ t.inv = r.inv := by
  rw [← cancel_epi r.hom, ← Category.assoc, ← h, Iso.hom_inv_id, Iso.hom_inv_id]

/-- The rearrangement behind `higherBaseChangeMapAb_zero`, stated on variables. -/
private theorem degreeZero_algebra {E : Type*} [Category* E]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ O₁₂ : E}
    {a₁ : O₁ ⟶ O₂} {BC : O₂ ⟶ O₃} {τ : O₁ ⟶ O₄} {νh : O₄ ⟶ O₃}
    {sH : O₂ ⟶ O₅} {Hd : O₅ ⟶ O₆} {tI : O₆ ⟶ O₃}
    {fr : O₂ ⟶ O₇} {fr' : O₇ ⟶ O₂} {xI : O₇ ⟶ O₅} {fi : O₁ ⟶ O₇}
    {fs : O₁ ⟶ O₈} {fH : O₈ ⟶ O₇} {xI' : O₈ ⟶ O₉} {HR : O₉ ⟶ O₅}
    {s' : O₁ ⟶ O₁₀} {Hf : O₁₀ ⟶ O₉} {Hτ : O₁₀ ⟶ O₁₁} {Hh : O₁₁ ⟶ O₁₂} {He : O₁₂ ⟶ O₆}
    {rI : O₁₂ ⟶ O₃} {s'' : O₄ ⟶ O₁₁}
    (F1 : BC = sH ≫ Hd ≫ tI) (F2 : sH = fr ≫ xI) (F3 : a₁ = fi ≫ fr') (F4 : fr' ≫ fr = 𝟙 _)
    (F5 : fi = fs ≫ fH) (F6 : fH ≫ xI = xI' ≫ HR) (F7 : fs ≫ xI' = s' ≫ Hf)
    (F8 : Hf ≫ HR ≫ Hd = Hτ ≫ Hh ≫ He) (F9 : He ≫ tI = rI) (F10 : s' ≫ Hτ = τ ≫ s'')
    (F11 : νh = s'' ≫ Hh ≫ rI) :
    a₁ ≫ BC = τ ≫ νh := by
  subst F1 F2 F3 F5 F11
  simp only [Category.assoc]
  rw [reassoc_of% F4, reassoc_of% F6, reassoc_of% F7, reassoc_of% F8, F9, reassoc_of% F10]

/-- **The base change map on higher direct images, in degree zero, is the underived base change
map.** Read through the identifications `g_* ≅ R⁰g_*` and `h_* ≅ R⁰h_*` of
`smallEtaleRightDerivedZeroIso`, the base change map `(f')⁻¹R⁰g_* ⟶ R⁰h_*e⁻¹` of
`higherBaseChangeMapAb` is the mate `(f')⁻¹g_* ⟶ h_*e⁻¹` of the identification of the two
composite direct images around the square. -/
theorem higherBaseChangeMapAb_zero {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (M : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtalePullbackAb f').map ((smallEtaleRightDerivedZeroIso g).hom.app M) ≫
        (higherBaseChangeMapAb f' g h e w 0).app M =
      (smallEtaleBaseChangeAb f' g h e w).app M ≫
        (smallEtaleRightDerivedZeroIso h).hom.app ((smallEtalePullbackAb e).obj M) := by
  have : (smallEtalePushforwardAb g).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb g⟩⟩
  have : (smallEtalePushforwardAb h).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb h⟩⟩
  have : IsIso (smallEtalePullbackAb f').rightDerivedFunctorPlusUnit :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso (smallEtalePullbackAb f')
  let HX := DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0
  let HS := DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0
  let sgT := DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0
  let sgS := DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0
  let sgX := DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0
  let Rf := (smallEtalePullbackAb f').rightDerivedFunctorPlus
  let Rh := (smallEtalePushforwardAb h).rightDerivedFunctorPlus
  let rDg := Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0
  let rDh := Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) 0
  let uG := (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (smallEtalePushforwardAb g)).app M
  let uF := (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (smallEtalePullbackAb f')).app
    ((smallEtalePushforwardAb g).obj M)
  let uH := (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (smallEtalePushforwardAb h)).app
    ((smallEtalePullbackAb e).obj M)
  let uE := (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (smallEtalePullbackAb e)).app M
  let τ := (smallEtaleBaseChangeAb f' g h e w).app M
  let dBC := (smallEtaleDerivedBaseChangeAb f' g h e w).app (sgT.obj M)
  let xE := Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb f') 0
  let iRg := ((smallEtalePushforwardAb g).isoRightDerivedPlusSingle 0).hom.app M
  have F1 : (higherBaseChangeMapAb f' g h e w 0).app M =
      (baseChangeSourceIso f' g 0).hom.app M ≫ HX.map dBC ≫
        (baseChangeTargetIso h e 0).inv.app M := rfl
  have F2 : (baseChangeSourceIso f' g 0).hom.app M =
      (smallEtalePullbackAb f').map (rDg.hom.app M) ≫
        xE.inv.app ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj (sgT.obj M)) :=
    baseChangeSourceIso_hom_app f' g 0 M
  have F3 : (smallEtalePullbackAb f').map ((smallEtaleRightDerivedZeroIso g).hom.app M) =
      (smallEtalePullbackAb f').map iRg ≫ (smallEtalePullbackAb f').map (rDg.inv.app M) :=
    (smallEtalePullbackAb f').map_comp _ _
  have F4 : (smallEtalePullbackAb f').map (rDg.inv.app M) ≫
      (smallEtalePullbackAb f').map (rDg.hom.app M) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have F5 : (smallEtalePullbackAb f').map iRg =
      (smallEtalePullbackAb f').map
          ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
            ((smallEtalePushforwardAb g).obj M)) ≫
        (smallEtalePullbackAb f').map (HS.map uG) :=
    (congrArg (smallEtalePullbackAb f').map
      (Stacks.DerivedFunctor.isoRightDerivedPlusSingle_zero_hom_app
        (smallEtalePushforwardAb g) M)).trans ((smallEtalePullbackAb f').map_comp _ _)
  have F6 : (smallEtalePullbackAb f').map (HS.map uG) ≫
      xE.inv.app ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj (sgT.obj M)) =
        xE.inv.app (sgS.obj ((smallEtalePushforwardAb g).obj M)) ≫ HX.map (Rf.map uG) :=
    xE.inv.naturality uG
  have F7 : (smallEtalePullbackAb f').map
        ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((smallEtalePushforwardAb g).obj M)) ≫
      xE.inv.app (sgS.obj ((smallEtalePushforwardAb g).obj M)) =
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
            ((smallEtalePullbackAb f').obj ((smallEtalePushforwardAb g).obj M)) ≫
          HX.map uF :=
    ((Iso.comp_inv_eq (xE.app (sgS.obj ((smallEtalePushforwardAb g).obj M)))).mpr
      (Stacks.DerivedFunctor.isoRightDerivedPlusSingle_hom_app_comp_exactRightDerivedPlusHomologyIso
        (smallEtalePullbackAb f') ((smallEtalePushforwardAb g).obj M)).symm).trans
      (Stacks.DerivedFunctor.isoRightDerivedPlusSingle_zero_hom_app (smallEtalePullbackAb f')
        ((smallEtalePushforwardAb g).obj M))
  have hU := Stacks.Cohomology.BaseChange.unitSingle_comp_derived (smallEtalePushforwardAb g)
    (smallEtalePushforwardAb h) (smallEtalePullbackAb f') (smallEtalePullbackAb e)
    (smallEtaleBaseChangeAb f' g h e w)
    (asIso (smallEtalePullbackAb f').rightDerivedFunctorPlusUnit) rfl M
  have F8 : HX.map uF ≫ HX.map (Rf.map uG) ≫ HX.map dBC =
      HX.map (sgX.map τ) ≫ HX.map uH ≫ HX.map (Rh.map uE) := by
    rw [← HX.map_comp, ← HX.map_comp, ← HX.map_comp, ← HX.map_comp]
    exact (congrArg HX.map hU).symm
  have F9 : HX.map (Rh.map uE) ≫ (baseChangeTargetIso h e 0).inv.app M =
      rDh.inv.app ((smallEtalePullbackAb e).obj M) := by
    have ht := baseChangeTargetIso_hom_app h e 0 M
    rw [NatTrans.congr_app (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom
      (smallEtalePullbackAb e)) M] at ht
    exact comp_inv_eq_of_hom_eq ((baseChangeTargetIso h e 0).app M)
      (rDh.app ((smallEtalePullbackAb e).obj M)) _ ht
  have F10 : (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
        ((smallEtalePullbackAb f').obj ((smallEtalePushforwardAb g).obj M)) ≫ HX.map (sgX.map τ) =
      τ ≫ (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
        ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb e).obj M)) :=
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.naturality τ).symm
  have F11 : (smallEtaleRightDerivedZeroIso h).hom.app ((smallEtalePullbackAb e).obj M) =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app
          ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb e).obj M)) ≫
        HX.map uH ≫ rDh.inv.app ((smallEtalePullbackAb e).obj M) := by
    refine (congrArg (· ≫ rDh.inv.app ((smallEtalePullbackAb e).obj M))
      (Stacks.DerivedFunctor.isoRightDerivedPlusSingle_zero_hom_app
        (smallEtalePushforwardAb h) ((smallEtalePullbackAb e).obj M))).trans ?_
    exact Category.assoc _ _ _
  exact degreeZero_algebra F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11

end Stacks.EtaleCohomology

end
