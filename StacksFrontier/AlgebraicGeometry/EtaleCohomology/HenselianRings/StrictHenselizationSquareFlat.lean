module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs

/-!
# The morphism of strict henselizations of a flat morphism is flat

Let `f : X ⟶ S` be a flat morphism of schemes and `x` a geometric point of `X`. The induced
homomorphism of étale local rings `𝒪^{sh}_{S,f(x)} ⟶ 𝒪^{sh}_{X,x}` is flat, hence so is the
morphism of strict henselizations `Spec 𝒪^{sh}_{X,x} ⟶ Spec 𝒪^{sh}_{S,f(x)}`.

Write `A = 𝒪_{S,f(x)}`, `B = 𝒪_{X,x}`, `A' = 𝒪^{sh}_{S,f(x)}` and `B' = 𝒪^{sh}_{X,x}`. The
homomorphism `A' ⟶ B'` factors through `A' ⊗_A B`. The first factor `A' ⟶ A' ⊗_A B` is a base
change of the flat homomorphism `A ⟶ B`. Both `A' ⊗_A B` (a base change of the ind-étale
`A ⟶ A'`) and `B'` are ind-étale over `B`, so `B'` is ind-étale over `A' ⊗_A B` (Stacks 08HS),
hence flat over it.

## Main results

* `AlgebraicGeometry.flat_etaleLocalRingHom` — the homomorphism of étale local rings induced by a
  flat morphism is flat.
* `AlgebraicGeometry.flat_strictHenselizationSquareMap` — the morphism of strict henselizations
  induced by a flat morphism is flat.

## References

* [Stacks Project, Tag 08HS](https://stacks.math.columbia.edu/tag/08HS)
* [Stacks Project, Tag 0F00](https://stacks.math.columbia.edu/tag/0F00)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TensorProduct

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X)

/-- **The homomorphism of étale local rings induced by a flat morphism is flat.** It factors as
the base change `𝒪^{sh}_{S,f(x)} ⟶ 𝒪^{sh}_{S,f(x)} ⊗_{𝒪_{S,f(x)}} 𝒪_{X,x}` of the flat
`𝒪_{S,f(x)} ⟶ 𝒪_{X,x}`, followed by a homomorphism of ind-étale `𝒪_{X,x}`-algebras, which is
ind-étale (Stacks 08HS) and therefore flat. -/
theorem flat_etaleLocalRingHom [Flat f] : (etaleLocalRingHom B hX hS f x).Flat := by
  let RS := ↥(S.presheaf.stalk ((x.map f).hom (closedPoint (x.map f).residueField)))
  let RX := ↥(X.presheaf.stalk (x.hom (closedPoint x.residueField)))
  let AS := ↥(etaleLocalRing B S hS (x.map f))
  let AX := ↥(etaleLocalRing B X hX x)
  let φ₀ : RS →+* RX := (f.stalkMap (x.hom (closedPoint x.residueField))).hom
  let ιS : RS →+* AS := structureSheafStalkFromLocalRing B S hS (x.map f)
  let ιX : RX →+* AX := structureSheafStalkFromLocalRing B X hX x
  let φ : AS →+* AX := etaleLocalRingHom B hX hS f x
  have hφ : φ.comp ιS = ιX.comp φ₀ := etaleLocalRingHom_comp_fromLocalRing B hX hS f x
  let : Algebra RS RX := φ₀.toAlgebra
  let : Algebra RS AX := (ιX.comp φ₀).toAlgebra
  have : IsScalarTower RS RX AX := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hflat₀ : Module.Flat RS RX := Flat.stalkMap f (x.hom (closedPoint x.residueField))
  -- the two factors
  let C := AS ⊗[RS] RX
  let φAlg : AS →ₐ[RS] AX :=
    { toRingHom := φ, commutes' := fun r => congrArg (fun k : RS →+* AX => k r) hφ }
  let ιXAlg : RX →ₐ[RS] AX := { toRingHom := ιX, commutes' := fun _ => rfl }
  let ψ : C →ₐ[RS] AX := Algebra.TensorProduct.lift φAlg ιXAlg fun _ _ => mul_comm _ _
  let : Algebra RX C := Algebra.TensorProduct.rightAlgebra
  let : Algebra C AX := ψ.toRingHom.toAlgebra
  have : IsScalarTower RX C AX := IsScalarTower.of_algebraMap_eq fun r => by
    show ιX r = ψ ((1 : AS) ⊗ₜ[RS] r)
    refine Eq.trans ?_ (Algebra.TensorProduct.lift_tmul φAlg ιXAlg _ (1 : AS) r).symm
    show ιX r = φ 1 * ιX r
    exact (by rw [map_one, one_mul])
  -- `C` and `AX` are ind-étale over `RX`
  have hC : StacksDraft.IndEtale RX C := by
    have h := StacksDraft.indEtale_tensorProduct (A := RS) (B := AS) RX
      (indEtale_etaleLocalRing B S hS (x.map f))
    refine StacksDraft.indEtale_of_equiv (RingEquiv.refl RX)
      (Algebra.TensorProduct.comm RS RX AS).toRingEquiv (fun r => ?_) h
    rfl
  have hAX : StacksDraft.IndEtale RX AX := indEtale_etaleLocalRing B X hX x
  have hCAX : StacksDraft.IndEtale C AX := StacksDraft.indEtale_of_comp hC hAX
  have hψ : Module.Flat C AX :=
    CommAlgCat.flat_of_ind_etale (StacksDraft.indEtale_iff.mp hCAX)
  have h₁ : (algebraMap AS C).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h₂ : (algebraMap C AX).Flat := RingHom.flat_algebraMap_iff.mpr hψ
  have hcomp : (algebraMap C AX).comp (algebraMap AS C) = φ := by
    ext a
    show ψ (a ⊗ₜ[RS] (1 : RX)) = φ a
    refine (Algebra.TensorProduct.lift_tmul φAlg ιXAlg _ a (1 : RX)).trans ?_
    show φ a * ιX 1 = φ a
    exact (by rw [map_one, mul_one])
  show φ.Flat
  rw [← hcomp]
  exact h₁.comp h₂

/-- **The morphism of strict henselizations induced by a flat morphism is flat**: it is the
spectrum of the flat homomorphism of étale local rings `flat_etaleLocalRingHom`. -/
theorem flat_strictHenselizationSquareMap [Flat f] :
    Flat (strictHenselizationSquareMap B hX hS f x) :=
  Flat.SpecMap_iff.mpr (flat_etaleLocalRingHom B hX hS f x)

end AlgebraicGeometry

end
