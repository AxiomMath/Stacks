module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.Basic

/-!
# The base ring and the local rings of the source of a modification

In Situation [Stacks, Tag 0AX8], let `f : X → S = Spec(A)` be the modification. For every point
`x` of `X` the composite `A → 𝒪_{S, f(x)} → 𝒪_{X,x}` is injective, and it sends the maximal
ideal `𝔪` of `A` into the maximal ideal of `𝒪_{X,x}` when `x` lies over the closed point.

## Main results

* `AlgebraicGeometry.VanishingSituation.baseToStalk_injective`: the map `A → 𝒪_{X,x}` is
  injective. Composed with the specialization map `𝒪_{X,x} → 𝒪_{X,η}` to the local ring at the
  generic point `η` of the integral scheme `X`, it is the map `A → 𝒪_{S,f(η)} → 𝒪_{X,η}`, the
  first arrow being a localization of the domain `A` and the second an isomorphism because the
  modification is birational.
* `AlgebraicGeometry.VanishingSituation.baseToStalk_mem_maximalIdeal`: at a point over the closed
  point, `𝔪` maps into the maximal ideal of `𝒪_{X,x}`, both arrows being local homomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.VanishingSituation

variable (V : VanishingSituation.{u})

/-- **The map `A → 𝒪_{X,x}` is injective** for every point `x` of the source of the
modification. -/
theorem baseToStalk_injective (x : V.X) :
    Function.Injective (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x).hom := by
  have : IsIntegral V.X := V.modification.source_isIntegral
  set η := genericPoint V.X
  have hη : η ∈ genericPoints V.X := by simp [η, genericPoints_eq_singleton]
  have hsp : η ⤳ x := genericPoint_specializes x
  have : IsIso (V.f.stalkMap η) := V.modification.isBirational.isIso_stalkMap η hη
  have hfsp := V.f.base.hom.map_specializes hsp
  have hnat : V.base.presheaf.stalkSpecializes hfsp ≫ V.f.stalkMap η =
      V.f.stalkMap x ≫ V.X.presheaf.stalkSpecializes hsp :=
    V.f.stalkSpecializes_stalkMap η x hsp
  have hstalk : StructureSheaf.toStalk V.A (V.f x) ≫
      V.base.presheaf.stalkSpecializes hfsp = StructureSheaf.toStalk V.A (V.f η) :=
    StructureSheaf.toStalk_stalkSpecializes hfsp
  have hcomp : (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x) ≫
      V.X.presheaf.stalkSpecializes hsp = StructureSheaf.toStalk V.A (V.f η) ≫
        V.f.stalkMap η := by
    calc _ = StructureSheaf.toStalk V.A (V.f x) ≫
          (V.f.stalkMap x ≫ V.X.presheaf.stalkSpecializes hsp) := Category.assoc _ _ _
      _ = StructureSheaf.toStalk V.A (V.f x) ≫
          (V.base.presheaf.stalkSpecializes hfsp ≫ V.f.stalkMap η) :=
            congrArg (fun k => StructureSheaf.toStalk V.A (V.f x) ≫ k) hnat.symm
      _ = (StructureSheaf.toStalk V.A (V.f x) ≫
          V.base.presheaf.stalkSpecializes hfsp) ≫ V.f.stalkMap η := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun k => k ≫ V.f.stalkMap η) hstalk
  have hloc : Function.Injective (StructureSheaf.toStalk V.A (V.f η)).hom := by
    let p : PrimeSpectrum V.A := V.f η
    let _ : Algebra V.A (V.base.presheaf.stalk p) := (StructureSheaf.toStalk V.A p).hom.toAlgebra
    have : IsLocalization.AtPrime (V.base.presheaf.stalk p) p.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk V.A p
    exact IsLocalization.injective (V.base.presheaf.stalk p) p.asIdeal.primeCompl_le_nonZeroDivisors
  refine Function.Injective.of_comp (f := (V.X.presheaf.stalkSpecializes hsp).hom) ?_
  convert (ConcreteCategory.bijective_of_isIso (V.f.stalkMap η)).1.comp hloc using 1
  exact funext fun a ↦ congrArg (fun k => k.hom a) hcomp

/-- **The maximal ideal of `A` maps into the maximal ideal of `𝒪_{X,x}`** at a point `x` of the
source lying over the closed point. -/
theorem baseToStalk_mem_maximalIdeal (x : V.X) (hx : V.f x = V.closedPoint)
    {a : V.A} (ha : a ∈ V.maximalIdeal) :
    (StructureSheaf.toStalk V.A (V.f x) ≫ V.f.stalkMap x).hom a ∈
      IsLocalRing.maximalIdeal (V.X.presheaf.stalk x) := by
  let p : PrimeSpectrum V.A := V.f x
  let _ : Algebra V.A (V.base.presheaf.stalk p) := (StructureSheaf.toStalk V.A p).hom.toAlgebra
  have : IsLocalization.AtPrime (V.base.presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk V.A p
  have hmem : (StructureSheaf.toStalk V.A p).hom a ∈
      IsLocalRing.maximalIdeal (V.base.presheaf.stalk p) := by
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (V.base.presheaf.stalk p) p.asIdeal a).mpr ?_
    rwa [show p = IsLocalRing.closedPoint V.A from hx]
  exact map_nonunit (V.f.stalkMap x).hom _ hmem

end AlgebraicGeometry.VanishingSituation
