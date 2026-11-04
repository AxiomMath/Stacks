module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Homothety
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Biduality at module universe equal to the ring universe

[Stacks, Tag 0A7C] is available in this library as
`Dualizing.isIso_dualizingBidualityMor_of_finiteCohomology`, for the tensor--Hom adjunction
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` of [stacks 0A63]. That adjunction is a
transport of the fixed K-flat/K-injective construction over `ULift A`, so its internal Hom is
not the internal Hom `StacksDraft.DerivedHom.DerivedInternalHom.Model.hom` that the derived
tensor--Hom diagonal of [stacks 0BYN] and its invertibility criterion [stacks 0ATK] are stated
for. This file supplies biduality for that second adjunction, at module universe equal to the
ring universe, where it is defined.

## Main results

* `Dualizing.torAmplitude_derivedHomSelf_of_isDualizingComplex` — for an arbitrary derived
  tensor--Hom adjunction, `RHom(ω, ω) ⊗ᴸ N[0]` is `N[0]`, so it has Tor amplitude `[0, 0]`.
* `Dualizing.isIso_bidualityMor_of_isDualizingComplex` — **biduality for the same-universe
  adjunction**: `K ⟶ RHom_A(RHom_A(K, ω), ω)` is invertible for `ω` dualizing and `K` with
  finite cohomology modules.

## Implementation notes

Every hypothesis of the abstract criterion `Dualizing.isIso_bidualityMor` holds for an arbitrary
adjunction or for the fixed same-universe one: the unitor naturality and the unitor/associator
triangle are `StacksDraft.DerivedHom.derivedHomAdjunction_isUnitorNatural` and
`StacksDraft.DerivedHom.derivedHomAdjunction_unitorTriangle`, the derived homothety of a
dualizing complex is invertible for an arbitrary adjunction by
`Dualizing.isIso_derivedHomothety_of_isDualizingComplex`, and the internalized evaluation
morphism of [stacks 0A69] is invertible by
`StacksDraft.DerivedHom.isIso_internalCurryMor_of_truncLE_pseudoCoherent`, which is stated for
the same-universe adjunction. The Tor-amplitude hypothesis of the last one holds because
`RHom(ω, ω)` is the tensor unit.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A69](https://stacks.math.columbia.edu/tag/0A69)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **Derived Hom from a dualizing complex to itself has Tor amplitude `[0, 0]`**, for an
arbitrary derived tensor--Hom adjunction. The derived homothety of a dualizing complex is
invertible, so `RHom(ω, ω)` is the tensor unit and tensoring it with a module placed in degree
zero returns that module in degree zero. This is the hypothesis `hTor` of
`StacksDraft.DerivedHom.isIso_internalCurryMor_of_truncLE_pseudoCoherent`. -/
theorem torAmplitude_derivedHomSelf_of_isDualizingComplex (d : DerivedHomData A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) :
    ∃ a b : ℤ, ∀ (N : ModuleCat.{u} A) (i : ℤ), i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (d.tensor.obj (d.hom.obj (Opposite.op ω, ω),
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) := by
  have := isIso_derivedHomothety_of_isDualizingComplex d ω hω
  let e := asIso (derivedHomothety d.toDerivedHomAdjunction
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex A))) d.tensorUnitLeft ω)
  refine ⟨0, 0, fun N i hi => ?_⟩
  have hi' : i ≠ 0 := fun h => hi (by simp [h])
  have hten : d.tensor.obj (d.hom.obj (Opposite.op ω, ω),
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N :=
    d.tensor.mapIso (Iso.prod e.symm (Iso.refl _)) ≪≫
      d.tensorUnitLeft ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso hten)
  rcases lt_or_gt_of_ne hi' with h | h
  · exact DerivedCategory.isZero_of_isGE _ 0 i h
  · exact DerivedCategory.isZero_of_isLE _ 0 i h

/-- **Biduality for the same-universe tensor--Hom adjunction**, [stacks 0A7C] for
`StacksDraft.DerivedHom.derivedHomAdjunction`: for `ω` a dualizing complex and `K` an object
whose cohomology modules are all finite, the canonical morphism
`K ⟶ RHom_A(RHom_A(K, ω), ω)` is invertible. -/
@[sga "6 III 4.9.2" "special case"]
theorem isIso_bidualityMor_of_isDualizingComplex
    (ω K : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    IsIso (bidualityMor (derivedHomAdjunction (R := A)).toDerivedHomAdjunction ω K) :=
  isIso_bidualityMor _ _ _
    (derivedHomAdjunction_isUnitorNatural (R := A))
    (derivedHomAdjunction_unitorTriangle (R := A)) ω K
    (isIso_derivedHomothety_of_isDualizingComplex (derivedHomAdjunction (R := A)) ω hω)
    (isIso_internalCurryMor_of_truncLE_pseudoCoherent K ω ω
      hω.finiteInjectiveDimension hω.finiteInjectiveDimension
      (torAmplitude_derivedHomSelf_of_isDualizingComplex (derivedHomAdjunction (R := A)) ω hω)
      (fun n => isPseudoCoherent_truncLEObj K hK n))

end Dualizing

end
