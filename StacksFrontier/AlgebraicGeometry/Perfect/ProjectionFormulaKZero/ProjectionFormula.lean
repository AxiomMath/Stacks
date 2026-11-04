module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectionFormulaKZero.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectionFormulaKZero.NoetherianComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectKGroupPullback
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula on `K`-groups

Let `f : X ⟶ Y` be a proper morphism of locally Noetherian schemes. For `α ∈ K'₀(X)` and
`β ∈ K₀(Y)`,

  `f_*(α · f^*β) = f_*α · β`,

where `f_* : K'₀(X) ⟶ K'₀(Y)` is the proper pushforward of [Stacks, Tag 0FDL],
`f^* : K₀(Y) ⟶ K₀(X)` is induced by the derived pullback of perfect objects, and
`K₀(X) × K'₀(X) ⟶ K'₀(X)` is the product of [Stacks, Tag 0FDK]. This is [Stacks, Tag 0FDM].

## Main results

* `AlgebraicGeometry.ParityEulerClass.perfectCoherentSMul_parityEulerClass`: the product of the
  class of a perfect object `P` with the parity Euler class of `M` is `χ(P ⊗^𝐋 M)`.
* `AlgebraicGeometry.properPushforward_perfectCoherentSMul_perfectPullbackKZero`:
  **[Stacks, Tag 0FDM]**.

## The proof

Both sides are biadditive, so it suffices to take `α = [ℱ]` for a coherent `𝒪_X`-module `ℱ` and
`β = [P]` for a perfect object `P` of `D(𝒪_Y)`. Then

* `f_*([ℱ] · f^*[P]) = f_* χ(Lf^*P ⊗^𝐋 ℱ) = χ(Rf_*(Lf^*P ⊗^𝐋 ℱ))`, by the definition of the
  product and the compatibility of `f_*` with `Rf_*` (Remark 0FDL);
* `f_*[ℱ] · [P] = χ(Rf_* ℱ) · [P] = χ(P ⊗^𝐋 Rf_* ℱ)`, by the same compatibility and the
  definition of the product (Remark 0FDK);
* `Rf_*(ℱ ⊗^𝐋 Lf^*P) ≅ Rf_* ℱ ⊗^𝐋 P` is the derived projection formula, [Stacks, Tag 08EU] at a
  perfect object `P`, where it holds for an arbitrary morphism of ringed spaces
  ([Stacks, Tag 0B54]); and the parity Euler class only depends on the isomorphism class.

## References

* [Stacks Project, Tag 0FDM](https://stacks.math.columbia.edu/tag/0FDM)
* [Stacks Project, Tag 0FDL](https://stacks.math.columbia.edu/tag/0FDL)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry

namespace ParityEulerClass

attribute [local instance 100000] HasDerivedCategory.standard

variable {Y : Scheme.{u}}

/-- **The product of `[P]` with a parity Euler class**: for a perfect object `P` and `M` with
locally bounded coherent cohomology, `[P] · χ(M) = χ(P ⊗^𝐋 M)`. This is the dévissage of the
parity Euler class along the exact functor `P ⊗^𝐋 -`, which commutes with direct sums. -/
theorem perfectCoherentSMul_parityEulerClass [IsLocallyNoetherian Y]
    (P : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory Y)
    (M : DerivedCategory Y.Modules) (hM : IsLocallyBoundedCoherent M) :
    perfectCoherentSMul Y (Pretriangulated.K0.cls P) (parityEulerClass M) =
      parityEulerClass (((TorFormula.derivedTensor Y).obj P.obj).obj M) := by
  let : ((TorFormula.derivedTensor Y).obj P.obj).CommShift ℤ :=
    (derivedTensorStructureAtScheme Y).commShiftRight P.obj
  let : ((TorFormula.derivedTensor Y).obj P.obj).IsTriangulated :=
    (derivedTensorStructureAtScheme Y).isTriangulatedRight P.obj
  have hσ : ∀ K : ULift.{u} ℕ → DerivedCategory Y.Modules,
      (∀ k, IsLocallyBoundedCoherent (K k)) →
        IsIso (sigmaComparison ((TorFormula.derivedTensor Y).obj P.obj) K) := fun K _ => by
    have hp : PreservesColimitsOfShape (Discrete (ULift.{u} ℕ))
        ((TorFormula.derivedTensor Y).obj P.obj) :=
      Stacks.Cohomology.ProjectionFormulaQCohCoproducts.preservesColimitsOfShape_derivedTensor_obj
        Y.toRingedSpace (ULift.{u} ℕ) P.obj
    have : PreservesColimit (Discrete.functor K) ((TorFormula.derivedTensor Y).obj P.obj) :=
      hp.preservesColimit
    exact (inferInstance : IsIso
      (PreservesCoproduct.iso ((TorFormula.derivedTensor Y).obj P.obj) K).inv)
  rw [parityEulerClass_map_eq ((TorFormula.derivedTensor Y).obj P.obj)
    (fun L hL => hL.derivedTensor P.property) hσ M hM, parityEulerClass_eq hM, map_sub,
    perfectCoherentSMul_cls_mk P (parityObject M hM 0),
    perfectCoherentSMul_cls_mk P (parityObject M hM 1)]
  rfl

variable {X : Scheme.{u}}

/-- **The projection formula on generators**: `f_*([ℱ] · f^*[P]) = f_*[ℱ] · [P]` for a coherent
`𝒪_X`-module `ℱ` and a perfect object `P` of `D(𝒪_Y)`. -/
theorem properPushforward_perfectCoherentSMul_cls_mk (f : X ⟶ Y) [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [IsProper f]
    (P : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory Y)
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    ProperPushforwardKZero.properPushforward f (perfectCoherentSMul X
        (RingedSpace.perfectPullbackKZero f.toLRSHom.toShHom (Pretriangulated.K0.cls P))
        (KZero.mk _ F)) =
      perfectCoherentSMul Y (Pretriangulated.K0.cls P)
        (ProperPushforwardKZero.properPushforward f (KZero.mk _ F)) := by
  have hF : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  let LP : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory X :=
    ⟨(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).obj P.obj,
      RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback f.toLRSHom.toShHom P.obj
        P.property⟩
  have hpull : RingedSpace.perfectPullbackKZero f.toLRSHom.toShHom (Pretriangulated.K0.cls P) =
      Pretriangulated.K0.cls LP :=
    RingedSpace.perfectPullbackKZero_cls f.toLRSHom.toShHom P
  have hiso := Stacks.Cohomology.ProjectionFormulaPerfect.isIso_projectionFormulaMap_of_isPerfect
    f.toLRSHom.toShHom ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj) P.obj P.property
  rw [hpull, perfectCoherentSMul_cls_mk LP F,
    properPushforward_parityEulerClass f _
      (isLocallyBoundedCoherent_derivedTensor_single LP.property _ hF),
    properPushforward_mk_eq f F,
    perfectCoherentSMul_parityEulerClass P _
      ((isLocallyBoundedCoherent_single F.obj hF).derivedPushforward f)]
  exact (parityEulerClass_congr ((derivedPushforwardModules f).mapIso
      ((derivedTensorStructureAtScheme X).braiding _ _))).trans
    ((parityEulerClass_congr (@asIso _ _ _ _ _ hiso)).symm.trans
      (parityEulerClass_congr ((derivedTensorStructureAtScheme Y).braiding _ _)))

end ParityEulerClass

open ParityEulerClass in
/-- **[Stacks, Tag 0FDM]: the projection formula on `K`-groups.** Let `f : X ⟶ Y` be a proper
morphism of locally Noetherian schemes. Then

  `f_*(α · f^*β) = f_*α · β`

for `α ∈ K'₀(X)` and `β ∈ K₀(Y)`. Here `f_* : K'₀(X) ⟶ K'₀(Y)` is the proper pushforward of
[Stacks, Tag 0FDL] (`AlgebraicGeometry.ProperPushforwardKZero.properPushforward`),
`f^* : K₀(Y) ⟶ K₀(X)` is induced by the derived pullback of perfect objects
(`AlgebraicGeometry.RingedSpace.perfectPullbackKZero`), and `K₀(X) × K'₀(X) ⟶ K'₀(X)` is the
product of [Stacks, Tag 0FDK] given by the derived tensor product
(`AlgebraicGeometry.ParityEulerClass.perfectCoherentSMul`); on a Noetherian scheme that product is
the scalar multiplication of the module structure of
`AlgebraicGeometry.exists_module_coherentKZero`
(`AlgebraicGeometry.ParityEulerClass.perfectCoherentSMul_eq_smul`).

Both sides are biadditive, so it suffices to treat `α = [ℱ]` and `β = [P]`, which is
`AlgebraicGeometry.ParityEulerClass.properPushforward_perfectCoherentSMul_cls_mk`: the derived
projection formula `Rf_*(ℱ ⊗^𝐋 Lf^*P) ≅ Rf_*ℱ ⊗^𝐋 P` of [Stacks, Tag 08EU], here at a perfect
object `P` where it is [Stacks, Tag 0B54], read through the identification `f_*[ℱ] = [Rf_*ℱ]` of
Remark 0FDL and the definition of the product in Remark 0FDK. -/
@[stacks 0FDM]
theorem properPushforward_perfectCoherentSMul_perfectPullbackKZero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsProper f]
    (α : CoherentKZero X) (β : PerfectKZero Y) :
    ProperPushforwardKZero.properPushforward f
        (perfectCoherentSMul X (RingedSpace.perfectPullbackKZero f.toLRSHom.toShHom β) α) =
      perfectCoherentSMul Y β (ProperPushforwardKZero.properPushforward f α) := by
  have h₁ : ∀ F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
      ((ProperPushforwardKZero.properPushforward f).comp
          (((perfectCoherentSMul X).flip (KZero.mk _ F)).comp
            (RingedSpace.perfectPullbackKZero f.toLRSHom.toShHom)) :
          PerfectKZero Y →+ CoherentKZero Y) =
        (perfectCoherentSMul Y).flip (ProperPushforwardKZero.properPushforward f (KZero.mk _ F)) :=
    fun F => QuotientAddGroup.addMonoidHom_ext _ (FreeAbelianGroup.lift_ext _ _ fun P =>
      properPushforward_perfectCoherentSMul_cls_mk f P F)
  have h₂ : (ProperPushforwardKZero.properPushforward f).comp
        (perfectCoherentSMul X (RingedSpace.perfectPullbackKZero f.toLRSHom.toShHom β)) =
      (perfectCoherentSMul Y β).comp (ProperPushforwardKZero.properPushforward f) :=
    KZero.hom_ext fun F => DFunLike.congr_fun (h₁ F) β
  exact DFunLike.congr_fun h₂ α

end AlgebraicGeometry
