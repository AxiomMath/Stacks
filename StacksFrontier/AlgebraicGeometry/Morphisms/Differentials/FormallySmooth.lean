module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The differentials of a formally smooth morphism split off

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S` the canonical maps form an exact sequence

```
f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0
```

of `𝒪_X`-modules. When `f` is formally smooth the first map is in addition a monomorphism, so
the sequence is short exact.

## Main results

* `AlgebraicGeometry.Scheme.Hom.formallySmooth_stalkMap_of_formallySmooth`: the stalk maps of a
  formally smooth morphism of schemes are formally smooth ring maps.
* `AlgebraicGeometry.Scheme.Hom.isScalarTower_stalkMap`: the local rings of `X`, `Y` and `S` at
  a point form a tower along the stalk maps of `f` and `g`.
* `AlgebraicGeometry.Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv`: the stalk of
  `f^* Ω_{Y/S}` is the base change `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} Ω[𝒪_{Y,f x}⁄𝒪_{S,g(f x)}]`, by an
  identification carrying the germ of `1 ⊗ d s` to `1 ⊗ D (germ s)` and the stalk of the
  canonical map `f^* Ω_{Y/S} ⟶ Ω_{X/S}` to `KaehlerDifferential.mapBaseChange`. No formal
  smoothness is used; this is the stalk computation on its own.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_mono_of_formallySmooth`: the canonical
  map `f^* Ω_{Y/S} ⟶ Ω_{X/S}` of a formally smooth `f` is a monomorphism.
* `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_shortExact`: the sequence above is short
  exact. Since a smooth morphism is formally smooth, this covers the smooth case as well.

## Implementation notes

Monomorphy is checked on stalks, and the stalk computation it rests on is
`exists_relativeDifferentialsPullbackStalkEquiv`. At a point `x` of `X` the stalk of the canonical
map is the base-change map
`𝒪_{X,x} ⊗_{𝒪_{Y,f x}} Ω[𝒪_{Y,f x}⁄𝒪_{S,g(f x)}] ⟶ Ω[𝒪_{X,x}⁄𝒪_{S,g(f x)}]` of the tower of
local rings: the stalks of `Ω_{Y/S}` and of `Ω_{X/S}` are computed by
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`, the stalk of the
pullback by `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, and the stalk of
the canonical map is identified with `KaehlerDifferential.mapBaseChange` by comparing the two on
the universal differentials of germs. The stalk map of a formally smooth morphism of schemes is a
formally smooth ring map, so `KaehlerDifferential.mapBaseChange_injective` applies.

The comparison is propagated from those generators by two inductions rather than by an equality
of linear maps: `Submodule.span_induction` against
`KaehlerDifferential.span_range_derivation`, with the scalar quantified inside the induction
hypothesis so that the scalar-multiplication step is `TensorProduct.smul_tmul`, and then
`TensorProduct.induction_on`. Only additivity of the maps involved is needed, so no
restriction of scalars along `𝒪_{Y,f x} ⟶ 𝒪_{X,x}` appears.

The stalk of the pullback is named through a presheaf of modules whose ring presheaf is
*written out* as `𝒪_X ⋙ forget₂ CommRingCat RingCat`. The module structure on a stalk is found
by instance search only when the ring presheaf is visible in that shape, and the structure sheaf
of a scheme presents it through `AlgebraicGeometry.Scheme.ringCatSheaf`, which search does not
unfold.

## References

* [Stacks Project, Tag 02K4](https://stacks.math.columbia.edu/tag/02K4)
* [Stacks Project, Tag 06B6](https://stacks.math.columbia.edu/tag/06B6)
* [Stacks Project, Tag 0H79](https://stacks.math.columbia.edu/tag/0H79)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeDifferentialStalk Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}}

/-- **The stalk maps of a formally smooth morphism of schemes are formally smooth.** -/
theorem formallySmooth_stalkMap_of_formallySmooth {f : X ⟶ Y} (hf : FormallySmooth f) (x : X) :
    (f.stalkMap x).hom.FormallySmooth := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.base.hom.continuous)
  have hVU' : V ≤ f ⁻¹ᵁ U := hVU
  let : IsAffine (V : Scheme.{u}) := hV
  let : IsAffine (U : Scheme.{u}) := hU
  have happ : (f.appLE U V hVU').hom.FormallySmooth :=
    (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U V hVU')).mp
      ((formallySmooth_iff_appTop_formallySmooth (f.resLE U V hVU')).mp (hf.resLE V U hVU'))
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU').hom.toAlgebra
  let : Algebra.FormallySmooth Γ(Y, U) Γ(X, V) := happ
  exact (formallySmooth_stalkMap_iff U hU V hV hVU' hxV).mpr
    (inferInstance : Algebra.FormallySmooth Γ(Y, U)
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal))

/-- A morphism of sheaves of modules on a scheme which is a monomorphism on every stalk is a
monomorphism. -/
private theorem mono_of_stalk_mono {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, Mono ((TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{u}) x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom)) : Mono φ :=
  (SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map
    ((TopCat.Presheaf.mono_iff_stalk_mono _).2 h)

/-- **The local rings of `X`, `Y` and `S` at a point form a tower** along the stalk maps of
`f : X ⟶ Y` and `g : Y ⟶ S`: the stalk map of the composite is the composite of the stalk
maps. -/
theorem isScalarTower_stalkMap (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    letI : Algebra (ToType (S.presheaf.stalk (g.base (f.base x))))
      (ToType (Y.sheaf.presheaf.stalk (f.base x))) := algebraStalkMap g (f.base x)
    letI : Algebra (ToType (Y.sheaf.presheaf.stalk (f.base x)))
      (ToType (X.sheaf.presheaf.stalk x)) := (f.stalkMap x).hom.toAlgebra
    letI : Algebra (ToType (S.presheaf.stalk (g.base (f.base x))))
      (ToType (X.sheaf.presheaf.stalk x)) := algebraStalkMap (f ≫ g) x
    IsScalarTower (ToType (S.presheaf.stalk (g.base (f.base x))))
      (ToType (Y.sheaf.presheaf.stalk (f.base x))) (ToType (X.sheaf.presheaf.stalk x)) := by
  let : Algebra (ToType (S.presheaf.stalk (g.base (f.base x))))
    (ToType (Y.sheaf.presheaf.stalk (f.base x))) := algebraStalkMap g (f.base x)
  let : Algebra (ToType (Y.sheaf.presheaf.stalk (f.base x)))
    (ToType (X.sheaf.presheaf.stalk x)) := (f.stalkMap x).hom.toAlgebra
  let : Algebra (ToType (S.presheaf.stalk (g.base (f.base x))))
    (ToType (X.sheaf.presheaf.stalk x)) := algebraStalkMap (f ≫ g) x
  exact IsScalarTower.of_algebraMap_eq fun r =>
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x)) r

/-- **The stalk at `x` of `f^*Ω_{Y/S}` is the base change
`𝒪_{X,x} ⊗_{𝒪_{Y,f x}} Ω[𝒪_{Y,f x}⁄𝒪_{S,g(f x)}]` of the tower of local rings**, by an
identification carrying the germ of the section `1 ⊗ d s` to the pure tensor `1 ⊗ D(germ s)`
and carrying the stalk of the canonical map `f^*Ω_{Y/S} ⟶ Ω_{X/S}` to
`KaehlerDifferential.mapBaseChange`.

The identification is not canonical on the nose, so it is produced together with the two
formulas that pin it down, as in
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`. It is stated additively,
the three objects being modules over three different rings. -/
@[ega "IV 17.11.1" "partial"]
theorem exists_relativeDifferentialsPullbackStalkEquiv (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))] :
    letI : Algebra (ToType (S.presheaf.stalk (g.base (f.base x))))
      (ToType (Y.sheaf.presheaf.stalk (f.base x))) := algebraStalkMap g (f.base x)
    letI : Algebra (ToType (Y.sheaf.presheaf.stalk (f.base x)))
      (ToType (X.sheaf.presheaf.stalk x)) := (f.stalkMap x).hom.toAlgebra
    letI : Algebra (ToType (S.presheaf.stalk (g.base (f.base x))))
      (ToType (X.sheaf.presheaf.stalk x)) := algebraStalkMap (f ≫ g) x
    letI := isScalarTower_stalkMap f g x
    let P : _root_.PresheafOfModules (X.sheaf.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      ((Scheme.Modules.pullback f).obj (relativeDifferentials g)).val
    ∃ e : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf x) ≃+
        (ToType (X.sheaf.presheaf.stalk x)) ⊗[ToType (Y.sheaf.presheaf.stalk (f.base x))]
          Ω[ToType (Y.sheaf.presheaf.stalk (f.base x))⁄
            ToType (S.presheaf.stalk (g.base (f.base x)))],
      (∀ (U : Y.Opens) (hx : f.base x ∈ U) (s : Γ(Y, U)),
          e (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) P.presheaf (f ⁻¹ᵁ U) x hx
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
                  (relativeDifferentials g)).val.app (op U)
                ((universalRelativeDerivation g).d s))) =
            (1 : ToType (X.sheaf.presheaf.stalk x)) ⊗ₜ
              KaehlerDifferential.D (ToType (S.presheaf.stalk (g.base (f.base x))))
                (ToType (Y.sheaf.presheaf.stalk (f.base x)))
                (Y.sheaf.presheaf.germ U (f.base x) hx s)) ∧
        ∀ m, KaehlerDifferential.mapBaseChange
              (ToType (S.presheaf.stalk (g.base (f.base x))))
              (ToType (Y.sheaf.presheaf.stalk (f.base x)))
              (ToType (X.sheaf.presheaf.stalk x)) (e m) =
            relativeDifferentialsStalkKaehlerEquiv (f ≫ g) x
              (Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom X.sheaf.presheaf x
                (relativeDifferentialsMap f g (f ≫ g) (𝟙 S)
                  (Category.comp_id (f ≫ g)).symm).val m) := by
  classical
  set c₁ := relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm with hc₁
  let ΩYS : Y.Modules := relativeDifferentials g
  let ΩXS : X.Modules := relativeDifferentials (f ≫ g)
  let P' : _root_.PresheafOfModules (X.sheaf.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    ((Scheme.Modules.pullback f).obj ΩYS).val
  let R : Type u := ToType (S.presheaf.stalk (g.base (f.base x)))
  let A : Type u := ToType (Y.sheaf.presheaf.stalk (f.base x))
  let B : Type u := ToType (X.sheaf.presheaf.stalk x)
  let : Algebra R A := algebraStalkMap g (f.base x)
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let : Algebra R B := algebraStalkMap (f ≫ g) x
  let : IsScalarTower R A B := isScalarTower_stalkMap f g x
  let M : Type u :=
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ΩYS.val.presheaf (f.base x))
  let P : Type u := ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P'.presheaf x)
  let T : Type u := ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ΩXS.val.presheaf x)
  let eA : M ≃ₗ[A] Ω[A⁄R] := relativeDifferentialsStalkKaehlerEquiv g (f.base x)
  let eB : T ≃ₗ[B] Ω[B⁄R] := relativeDifferentialsStalkKaehlerEquiv (f ≫ g) x
  obtain ⟨ePull, hPullGerm⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom ΩYS x
  let ePull' : P ≃ₗ[B] B ⊗[A] M := ePull
  let stalkC₁ : P →ₗ[B] T :=
    Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom X.sheaf.presheaf x c₁.val
  let eT : B ⊗[A] M ≃ₗ[A] B ⊗[A] Ω[A⁄R] := TensorProduct.congr (LinearEquiv.refl A B) eA
  have hD : ∀ (U : Y.Opens) (hx : f.base x ∈ U) (s : Γ(Y, U)),
      eA (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ΩYS.val.presheaf U (f.base x) hx
        ((universalRelativeDerivation g).d s)) =
        KaehlerDifferential.D R A (Y.sheaf.presheaf.germ U (f.base x) hx s) := fun U hx s =>
    relativeDifferentialsStalkKaehlerEquiv_germ_d g (f.base x) (OrderDual.toDual ⟨U, hx⟩) s
  have hgen : ∀ (b : B) (a : A),
      KaehlerDifferential.mapBaseChange R A B (eT (b ⊗ₜ[A] eA.symm (KaehlerDifferential.D R A a)))
        = eB (stalkC₁ (ePull'.symm (b ⊗ₜ[A] eA.symm (KaehlerDifferential.D R A a)))) := by
    intro b a
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.sheaf.presheaf a
    set dY := (universalRelativeDerivation g).d s with hdY
    set mY := TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ΩYS.val.presheaf U (f.base x) hxU dY
      with hmY
    set dX := (universalRelativeDerivation (f ≫ g)).d ((f.app U).hom s) with hdX
    set mX := TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ΩXS.val.presheaf (f ⁻¹ᵁ U) x hxU dX
      with hmX
    have heB : eB mX = KaehlerDifferential.D R B
        (X.sheaf.presheaf.germ (f ⁻¹ᵁ U) x hxU ((f.app U).hom s)) :=
      relativeDifferentialsStalkKaehlerEquiv_germ_d (f ≫ g) x
        (OrderDual.toDual ⟨f ⁻¹ᵁ U, hxU⟩) ((f.app U).hom s)
    have hunit : ePull'.symm ((1 : B) ⊗ₜ[A] mY) =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) P'.presheaf (f ⁻¹ᵁ U) x hxU
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ΩYS).val.app (op U) dY) := by
      rw [LinearEquiv.symm_apply_eq]
      exact (hPullGerm U hxU dY).symm
    have hd : ((Scheme.Modules.pushforward f).map c₁).val.app (op U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app ΩYS).val.app (op U) dY)
          = dX := by
      have h := relativeDifferentialsMap_app_d (f := f) (p := g) (p' := f ≫ g) (𝟙 S)
        (Category.comp_id (f ≫ g)).symm U s
      rwa [Adjunction.homEquiv_unit] at h
    have hc : stalkC₁ (ePull'.symm ((1 : B) ⊗ₜ[A] mY)) = mX := by
      rw [hunit]
      refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply (f ⁻¹ᵁ U) x hxU
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map c₁.val) _) ?_
      exact congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) ΩXS.val.presheaf
        (f ⁻¹ᵁ U) x hxU) hd
    have hstalk : (algebraMap A B) (Y.sheaf.presheaf.germ U (f.base x) hxU s) =
        X.sheaf.presheaf.germ (f ⁻¹ᵁ U) x hxU ((f.app U).hom s) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (f.germ_stalkMap U x hxU)) s
    rw [← hD U hxU s, LinearEquiv.symm_apply_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, hD U hxU s, KaehlerDifferential.mapBaseChange_tmul]
    simp only [KaehlerDifferential.map_D]
    rw [hstalk]
    have hb : b ⊗ₜ[A] mY = b • ((1 : B) ⊗ₜ[A] mY) := by
      rw [TensorProduct.smul_tmul']
      show b ⊗ₜ[A] mY = (b * 1) ⊗ₜ[A] mY
      rw [mul_one]
    rw [hb, map_smul, map_smul, map_smul, hc, heB]
  have hspan : ∀ (ω : Ω[A⁄R]) (b : B),
      KaehlerDifferential.mapBaseChange R A B (eT (b ⊗ₜ[A] eA.symm ω))
        = eB (stalkC₁ (ePull'.symm (b ⊗ₜ[A] eA.symm ω))) := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact fun b => hgen b a
    | zero => intro b; simp
    | add y z _ _ ihy ihz =>
      intro b
      simp only [map_add, TensorProduct.tmul_add, ihy b, ihz b]
    | smul a y _ ihy =>
      intro b
      rw [map_smul, ← TensorProduct.smul_tmul]
      exact ihy (a • b)
  have hBridge : ∀ w : B ⊗[A] M,
      KaehlerDifferential.mapBaseChange R A B (eT w) = eB (stalkC₁ (ePull'.symm w)) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      have h := hspan (eA m) b
      rwa [LinearEquiv.symm_apply_apply] at h
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  refine ⟨ePull'.toAddEquiv.trans eT.toAddEquiv, ?_, ?_⟩
  · intro U hx s
    refine (congrArg eT (hPullGerm U hx _)).trans ?_
    exact (TensorProduct.congr_tmul ..).trans (congrArg _ (hD U hx s))
  · intro m
    show KaehlerDifferential.mapBaseChange R A B (eT (ePull' m)) = _
    rw [hBridge (ePull' m), LinearEquiv.symm_apply_apply]
    rfl

/-- **The canonical map `f^* Ω_{Y/S} ⟶ Ω_{X/S}` of a formally smooth morphism `f : X ⟶ Y` is a
monomorphism.** -/
@[ega "0 20.6.2" "partial"]
theorem relativeDifferentialsMap_mono_of_formallySmooth (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : FormallySmooth f) :
    Mono (relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm) := by
  classical
  refine mono_of_stalk_mono _ fun x => ?_
  let R : Type u := ToType (S.presheaf.stalk (g.base (f.base x)))
  let A : Type u := ToType (Y.sheaf.presheaf.stalk (f.base x))
  let B : Type u := ToType (X.sheaf.presheaf.stalk x)
  let : Algebra R A := algebraStalkMap g (f.base x)
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let : Algebra R B := algebraStalkMap (f ≫ g) x
  let : IsScalarTower R A B := isScalarTower_stalkMap f g x
  let : Algebra.FormallySmooth A B := formallySmooth_stalkMap_of_formallySmooth hf x
  obtain ⟨e, -, hbridge⟩ := exists_relativeDifferentialsPullbackStalkEquiv f g x
  rw [AddCommGrpCat.mono_iff_injective]
  show Function.Injective (Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom
    X.sheaf.presheaf x
    (relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm).val)
  intro z₁ z₂ hz
  refine e.injective (KaehlerDifferential.mapBaseChange_injective R A B ?_)
  rw [hbridge, hbridge, hz]

/-- For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S` with `f` formally smooth, the canonical
sequence `0 ⟶ f^* Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0` of `𝒪_X`-modules is short exact. The case of a
smooth `f` is the special case obtained from
`Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth`. -/
@[stacks 06B6, stacks 02K4, ega "IV 17.2.3"]
theorem toRelativeDifferentials_shortExact (f : X ⟶ Y) (g : Y ⟶ S) (hf : FormallySmooth f) :
    ∃ h : relativeDifferentialsMap f g (f ≫ g) (𝟙 S) (Category.comp_id (f ≫ g)).symm ≫
        f.toRelativeDifferentials g = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  obtain ⟨h, hexact⟩ := toRelativeDifferentials_exact f g
  exact ⟨h, ShortComplex.ShortExact.mk' hexact
    (relativeDifferentialsMap_mono_of_formallySmooth f g hf)
    (toRelativeDifferentials_epi f g)⟩

end AlgebraicGeometry.Scheme.Hom

end
