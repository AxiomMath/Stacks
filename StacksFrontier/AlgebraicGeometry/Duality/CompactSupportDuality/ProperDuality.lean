module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.Linearity
public import StacksFrontier.AlgebraicGeometry.Duality.CompactSupportDuality.ProDuality
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# Duality on a proper scheme over a field as a perfect composition pairing

Let `q : X ⟶ Spec k` be proper over a field and `ω_X^• = q^!𝒪_{Spec k}`. Part (5) of
[Stacks, Tag 0FVV] in degree zero, `Hom_X(N, ω_X^•) = Hom_k(H^0(X, N), k)`, is restated here in
the form the proof of [Stacks, Tag 0G5A] consumes: at the standard model of `D(𝒪_X)`, and with
`H^0(X, N)` written as `Hom_X(𝒪_X, N)`. There is a linear form `t : Hom_X(𝒪_X, ω_X^•) ⟶ k`, the
trace, such that for every `N` with quasi-coherent cohomology the composition pairing
`Hom_X(𝒪_X, N) × Hom_X(N, ω_X^•) ⟶ k`, `(a, g) ↦ t(a ≫ g)`, is perfect in the sense that
`g ↦ t(- ≫ g)` is a bijection onto the dual of `Hom_X(𝒪_X, N)`.

## Main definitions

* `AlgebraicGeometry.derivedGlobalSectionsOverModelIso`: `RΓ(X, -)` at the locally small and at
  the standard model agree.
* `AlgebraicGeometry.properTrace`: the trace `t : Hom_X(𝒪_X, ω_X^•) ⟶ k`.

## Main results

* `AlgebraicGeometry.bijective_compPairing_properTrace`: the perfectness of the composition
  pairing.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StacksDraft.DerivedModel Stacks.Duality

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]

/-- **`RΓ(X, -)` read at two models.** The `k`-linear derived global sections at the locally
small models of `D(𝒪_X)` and `D(k)`, followed by the comparison of the two models of `D(k)`, is
the comparison of the two models of `D(𝒪_X)` followed by the derived global sections at the
standard models: both are right derived functors of `k`-linear global sections
(`StacksDraft.DerivedModel.rightDerivedModelIso`). -/
def derivedGlobalSectionsOverModelIso :
    derivedGlobalSectionsOver q ⋙
      (modelEquiv ModuleCat.hasDerivedCategory
        (HasDerivedCategory.standard (ModuleCat.{u} k))).functor ≅
      (modelEquiv (Scheme.Modules.hasDerivedCategory X)
        (HasDerivedCategory.standard X.Modules)).functor ⋙
      (@derivedGlobalSectionsOver k _ X q (HasDerivedCategory.standard X.Modules)
        (HasDerivedCategory.standard (ModuleCat.{u} k))) :=
  rightDerivedModelIso (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (derivedGlobalSectionsOverUnit q)
    (@derivedGlobalSectionsOverUnit k _ X q (HasDerivedCategory.standard X.Modules)
      (HasDerivedCategory.standard (ModuleCat.{u} k)))
    (Localization.compUniqFunctor _ _ _)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _))

/-- **`H^0(X, -)` read at two models**, naturally: at the locally small model it is `H^0(X, -)` at
the standard model after the comparison of models. -/
def homologyZeroModelNatIso :
    derivedGlobalSectionsOver q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0 ≅
      (modelEquiv (Scheme.Modules.hasDerivedCategory X)
        (HasDerivedCategory.standard X.Modules)).functor ⋙
      (@derivedGlobalSectionsOver k _ X q (HasDerivedCategory.standard X.Modules)
        (HasDerivedCategory.standard (ModuleCat.{u} k))) ⋙
      (@DerivedCategory.homologyFunctor (ModuleCat.{u} k) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} k)) 0) :=
  Functor.isoWhiskerLeft _ (modelEquivCompHomologyFunctorIso ModuleCat.hasDerivedCategory
      (HasDerivedCategory.standard (ModuleCat.{u} k)) 0).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedGlobalSectionsOverModelIso q) _ ≪≫ Functor.associator _ _ _

/-- The relative dualizing complex at the locally small model, as an object of `D_QCoh`. -/
local notation "ωLS" =>
  relativeDualizingComplex q (isQuasicoherent_homology_derivedPushforward_of_qcqs q)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- **The trace** `t : Hom_X(𝒪_X, ω_X^•) ⟶ k` at the standard model: `Hom(𝒪_X, -) = H^0(X, -)`
(`AlgebraicGeometry.structureSheafHomLinearEquiv`), the comparison of models, and the linear form
that part (5) of [Stacks, Tag 0FVV] attaches to the identity of `ω_X^•`. -/
def properTrace :
    letI : Linear k X.Modules := modulesLinear k (Over.mk q)
    (@derivedUnitObject X (HasDerivedCategory.standard X.Modules) ⟶
      standardRelativeDualizingComplex q) →ₗ[k] k :=
  letI : Linear k X.Modules := modulesLinear k (Over.mk q)
  (dualityEquiv q ωLS 0 ((shiftFunctorZero (DerivedCategory X.Modules) ℤ).inv.app (ωLS).obj) ∘ₗ
      ((homologyZeroModelNatIso q).app (ωLS).obj).inv.hom) ∘ₗ
    (structureSheafHomLinearEquiv q (standardRelativeDualizingComplex q)).toLinearMap

/-- **[Stacks, Tag 0FVV] part (5) in degree zero, as a perfect composition pairing.** Let `X` be
proper over a field `k` and `N` an object of `D(𝒪_X)`, at the standard model, with
quasi-coherent cohomology. Then `g ↦ (a ↦ t(a ≫ g))` is a bijection from `Hom_X(N, ω_X^•)` onto
the `k`-linear dual of `Hom_X(𝒪_X, N)`, where `t` is the trace `AlgebraicGeometry.properTrace`.

Under `Hom_X(𝒪_X, -) = H^0(X, -)` and the comparison of models this is
`Stacks.Duality.dualityEquiv` in degree zero, by its naturality
(`Stacks.Duality.dualityEquiv_comp`) applied to the identity of `ω_X^•`. -/
theorem bijective_compPairing_properTrace
    (N : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules))
    (hN : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) i).obj N).IsQuasicoherent) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk q)
    Function.Bijective (ProSeq.compPairing (properTrace q) N) := by
  let : Linear k X.Modules := modulesLinear k (Over.mk q)
  let G := modelEquiv (Scheme.Modules.hasDerivedCategory X)
    (HasDerivedCategory.standard X.Modules)
  let N' := G.inverse.obj N
  have hN' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj N').IsQuasicoherent :=
    fun i => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((modelEquivCompHomologyFunctorIso (Scheme.Modules.hasDerivedCategory X)
        (HasDerivedCategory.standard X.Modules) i).app N').symm ≪≫
        (@DerivedCategory.homologyFunctor X.Modules _ _
          (HasDerivedCategory.standard X.Modules) i).mapIso (G.counitIso.app N)).symm (hN i)
  let K' : quasiCoherentDerivedCategory X := ⟨N', hN'⟩
  let e₀ := (shiftFunctorZero (DerivedCategory X.Modules) ℤ).inv.app (ωLS).obj
  let L := (structureSheafHomLinearEquiv q (G.functor.obj N')).trans
    ((homologyZeroModelNatIso q).app N').symm.toLinearEquiv
  have key : ∀ (g' : N' ⟶ (ωLS).obj)
      (a : @derivedUnitObject X (HasDerivedCategory.standard X.Modules) ⟶ G.functor.obj N'),
      properTrace q (a ≫ G.functor.map g') = dualityEquiv q K' 0 (g' ≫ e₀) (L a) := by
    intro g' a
    have h1 : structureSheafHomLinearEquiv q (standardRelativeDualizingComplex q)
        (a ≫ G.functor.map g') =
        ((@DerivedCategory.homologyFunctor (ModuleCat.{u} k) _ _
          (HasDerivedCategory.standard (ModuleCat.{u} k)) 0).map
          ((@derivedGlobalSectionsOver k _ X q
            (HasDerivedCategory.standard X.Modules)
            (HasDerivedCategory.standard (ModuleCat.{u} k))).map (G.functor.map g'))).hom
          (structureSheafHomLinearEquiv q (G.functor.obj N') a) :=
      structureSheafHomAddEquiv_comp q a _
    have h2 := ConcreteCategory.congr_hom ((homologyZeroModelNatIso q).inv.naturality g')
      (structureSheafHomLinearEquiv q (G.functor.obj N') a)
    change dualityEquiv q (ωLS) 0 e₀ (((homologyZeroModelNatIso q).app (ωLS).obj).inv.hom
      (structureSheafHomLinearEquiv q (standardRelativeDualizingComplex q)
        (a ≫ G.functor.map g'))) = _
    rw [h1]
    refine (congrArg (dualityEquiv q (ωLS) 0 e₀) h2).trans ?_
    exact (dualityEquiv_comp q K' (ωLS) 0 g' e₀ _).symm
  have hA : Function.Bijective (ProSeq.compPairing (properTrace q) (G.functor.obj N')) := by
    have hc : (ProSeq.compPairing (properTrace q) (G.functor.obj N') :
        (G.functor.obj N' ⟶ standardRelativeDualizingComplex q) →
          Module.Dual k
            (@derivedUnitObject X (HasDerivedCategory.standard X.Modules) ⟶ G.functor.obj N')) =
        L.dualMap ∘ dualityEquiv q K' 0 ∘ (· ≫ e₀) ∘ G.fullyFaithfulFunctor.preimage := by
      funext g
      ext a
      change properTrace q (a ≫ g) = dualityEquiv q K' 0 (G.fullyFaithfulFunctor.preimage g ≫ e₀)
        (L a)
      refine (congrArg (fun g₀ => properTrace q (a ≫ g₀))
        (G.fullyFaithfulFunctor.map_preimage g).symm).trans ?_
      exact key _ a
    rw [hc]
    refine L.dualMap.bijective.comp ((dualityEquiv q K' 0).bijective.comp
      (Function.Bijective.comp ?_ G.fullyFaithfulFunctor.homEquiv.symm.bijective))
    exact ⟨fun g g' h => (cancel_mono e₀).1 h, fun h => ⟨h ≫ inv e₀, by simp⟩⟩
  let eN : G.functor.obj N' ≅ N := G.counitIso.app N
  exact ProSeq.bijective_compPairing_of_iso (properTrace q) eN hA

end AlgebraicGeometry

end
