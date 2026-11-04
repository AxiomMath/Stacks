module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentDerivedHom
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.Homothety
public import StacksFrontier.RingTheory.Dualizing.Gluing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyOfUnitHom
import StacksCore.Tactic.StacksAttribute

/-!
# The homothety of a dualizing complex on an affine scheme

Let `R` be a Noetherian ring, `X = Spec R`, and let `ω` be a dualizing complex for `R` in the
sense of [Stacks, Tag 0A7B]. This file proves that the homothety of [Stacks, Tag 08DI]

`𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(ω̃, ω̃)`

is an isomorphism, and hence that the evaluation morphism `e_{ω̃, ω̃}` is one. The underlying
isomorphism of objects is

`R𝓗om_{𝒪_X}(ω̃, ω̃) ≅ (R𝐻om_R(ω, ω))~ ≅ (R[0])~ = 𝒪_X[0]`,

by the comparison of [Stacks, Tag 0A6H] (3)(a) at the pair `(ω, ω)`.

Everything here is at `CategoryTheory.HasDerivedCategory.standard`, which is the model both
[Stacks, Tag 08DI] and the comparison of [Stacks, Tag 0A6H] (3)(a) are stated at, so no model
comparison enters either.

## Main definitions

* `Stacks.Duality.derivedTildeDerivedSheafHomSelfUnitIso` — the object isomorphism
  `R𝓗om_{𝒪_{Spec R}}(ω̃, ω̃) ≅ 𝒪_{Spec R}[0]`.

## Main results

* `Stacks.Duality.isIso_derivedSheafHomothety_derivedTilde` — **the homothety of `ω̃` is an
  isomorphism.**
* `Stacks.Duality.tensorHomBijective_tensorUnit_derivedTilde` — equivalently, `𝒪_X[0]` is an
  internal hom from `ω̃` to `ω̃` through the left unitor.
* `Stacks.Duality.isIso_derivedSheafHomCounit_derivedTilde_self` — the evaluation morphism
  `e_{ω̃, ω̃} : R𝓗om_{𝒪_X}(ω̃, ω̃) ⊗^L_{𝒪_X} ω̃ ⟶ ω̃` is an isomorphism. This is the evaluation
  hypothesis `hev` of [Stacks, Tag 0ATP] over an affine scheme, at the diagonal.
* `Stacks.Duality.isIso_derivedSheafHomCounit_derivedTilde` — and at a pair `(ω̃, M)` with
  `ω̃ ⊗^L_{𝒪_X} L ≅ M` for an invertible `L`.

## Implementation notes

The unit of `D(R)` for the tensor–Hom adjunction that [Stacks, Tag 0A6H] (3)(a) is stated
against is `DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ))`, which is the single
complex `R[0]`; derived sheafification is moved past the single functor by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and `R̃` is the structure sheaf by
`AlgebraicGeometry.tildeSelf`. The unit of
`Stacks.SheafOfModules.derivedMonoidalStructure` *is* the structure sheaf in degree zero, by
`Stacks.SheafOfModules.tensorUnit_derivedMonoidalStructure`, so no comparison stands at the other
end either.

## What this file does not contain

The evaluation morphism at a pair of *dualizing* complexes `(ω̃, ω̃')` is an isomorphism by
`Stacks.Duality.isIso_derivedSheafHomCounit_derivedTilde_pair`, which feeds the invertible
object of `Stacks.Duality.exists_isInvertible_tensor_iso_derivedTildeStandard` to
`Stacks.Duality.isIso_derivedSheafHomCounit_derivedTilde`.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

universe u

namespace Stacks.Duality

variable (R : CommRingCat.{u}) [IsNoetherianRing R]
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]

/-! ### Derived sheafification at the standard model -/

/-- **Derived sheafification on `Spec R`**, read into the spelling of the category of
`𝒪_{Spec R}`-modules that the derived internal hom of [Stacks, Tag 08DI] and the derived monoidal
structure of [Stacks, Tag 0FPT] are stated for, and at
`CategoryTheory.HasDerivedCategory.standard` on both sides.

`AlgebraicGeometry.tildeDS` is the same functor read at the locally small sheaf model; the two
agree on objects and not on morphisms. -/
abbrev derivedTildeStructureSheafModules (R : CommRingCat.{u}) :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (StructureSheafModules (Spec R).sheaf) :=
  (tilde.functor R).mapDerivedCategory

/-! ### The object computation -/

/-- **The derived internal hom of a dualizing complex on `Spec R` to itself is the structure
sheaf**:

`R𝓗om_{𝒪_{Spec R}}(ω̃, ω̃) ≅ 𝒪_{Spec R}[0]`,

an isomorphism of *objects* obtained from the comparison of [Stacks, Tag 0A6H] (3)(a) at the
pair `(ω, ω)`. -/
def derivedTildeDerivedSheafHomSelfUnitIso {ω : DerivedCategory (ModuleCat.{u} R)}
    (hω : Dualizing.IsDualizingComplex ω) :
    letI := derivedMonoidalStructure (Spec R).sheaf
    ((derivedSheafHom (Spec R).sheaf).obj
          (op ((derivedTildeStructureSheafModules R).obj ω))).obj
        ((derivedTildeStructureSheafModules R).obj ω) ≅
      𝟙_ (DerivedCategory (StructureSheafModules (Spec R).sheaf)) := by
  let := derivedMonoidalStructure (Spec R).sheaf
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))
  let h := Dualizing.derivedHomothety d.toDerivedHomAdjunction
    (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex (R : Type u))))
    d.tensorUnitLeft ω
  have : IsIso h := Dualizing.isIso_derivedHomothety_of_isDualizingComplex d ω hω
  exact affinePseudoCoherentDerivedSheafHomIso R ω ω
        (Dualizing.isPseudoCoherent_of_isDualizingComplex ω hω) hω.bounded.1 ≪≫
      (derivedTildeStructureSheafModules R).mapIso (asIso h).symm ≪≫
      ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of (R : Type u) R) ≪≫
      (DerivedCategory.singleFunctor (StructureSheafModules (Spec R).sheaf) 0).mapIso tildeSelf

/-! ### The homothety and the evaluation morphism -/

/-- **The homothety of a dualizing complex on an affine scheme is an isomorphism.** Let `R` be a
Noetherian ring and `ω` a dualizing complex for `R`. Then

`𝒪_{Spec R}[0] ⟶ R𝓗om_{𝒪_{Spec R}}(ω̃, ω̃)`

is an isomorphism. -/
theorem isIso_derivedSheafHomothety_derivedTilde {ω : DerivedCategory (ModuleCat.{u} R)}
    (hω : Dualizing.IsDualizingComplex ω) :
    IsIso (derivedSheafHomothety (Spec R).sheaf
      ((derivedTildeStructureSheafModules R).obj ω)) :=
  isIso_derivedSheafHomothety_of_iso_tensorUnit (Spec R).sheaf _
    (derivedTildeDerivedSheafHomSelfUnitIso R hω)

/-- **`𝒪_{Spec R}[0]` is an internal hom from `ω̃` to `ω̃` through the left unitor**, for `ω` a
dualizing complex over a Noetherian ring: the map

`(Z ⟶ 𝒪_X[0]) → (Z ⊗^L_{𝒪_X} ω̃ ⟶ ω̃)`, `b ↦ b ▷ ω̃ ≫ λ_ ω̃`

is a bijection for every object `Z` of `D(𝒪_X)`. -/
theorem tensorHomBijective_tensorUnit_derivedTilde {ω : DerivedCategory (ModuleCat.{u} R)}
    (hω : Dualizing.IsDualizingComplex ω) :
    letI := derivedMonoidalStructure (Spec R).sheaf
    ∀ Z : DerivedCategory (StructureSheafModules (Spec R).sheaf),
      Function.Bijective
        fun b : Z ⟶ 𝟙_ (DerivedCategory (StructureSheafModules (Spec R).sheaf)) =>
          b ▷ ((derivedTildeStructureSheafModules R).obj ω) ≫
            (λ_ ((derivedTildeStructureSheafModules R).obj ω)).hom :=
  tensorHomBijective_tensorUnit_of_iso_tensorUnit (Spec R).sheaf _
    (derivedTildeDerivedSheafHomSelfUnitIso R hω)

/-- **The evaluation morphism of [Stacks, Tag 08DI] at a dualizing complex on an affine scheme
and itself is an isomorphism**:

`e_{ω̃, ω̃} : R𝓗om_{𝒪_{Spec R}}(ω̃, ω̃) ⊗^L_{𝒪_{Spec R}} ω̃ ⟶ ω̃`.

This is the evaluation hypothesis `hev` of
`Stacks.SheafOfModules.exists_isInvertible_tensor_iso_of_affineLocal` ([Stacks, Tag 0ATP]) over
an affine scheme, at the diagonal. -/
theorem isIso_derivedSheafHomCounit_derivedTilde_self {ω : DerivedCategory (ModuleCat.{u} R)}
    (hω : Dualizing.IsDualizingComplex ω) :
    IsIso (derivedSheafHomCounit (Spec R).sheaf
      ((derivedTildeStructureSheafModules R).obj ω)
      ((derivedTildeStructureSheafModules R).obj ω)) :=
  isIso_derivedSheafHomCounit_self_of_iso_tensorUnit (Spec R).sheaf _
    (derivedTildeDerivedSheafHomSelfUnitIso R hω)

/-- **The evaluation morphism of [Stacks, Tag 08DI] at a dualizing complex on an affine scheme
and a target differing from it by an invertible object is an isomorphism**: if `L` is an
invertible object of `D(𝒪_{Spec R})` ([Stacks, Tag 0FFN]) and `ω̃ ⊗^L_{𝒪_X} L ≅ M`, then

`e_{ω̃, M} : R𝓗om_{𝒪_{Spec R}}(ω̃, M) ⊗^L_{𝒪_{Spec R}} ω̃ ⟶ M`

is an isomorphism. -/
theorem isIso_derivedSheafHomCounit_derivedTilde {ω : DerivedCategory (ModuleCat.{u} R)}
    (hω : Dualizing.IsDualizingComplex ω)
    (M : DerivedCategory (StructureSheafModules (Spec R).sheaf))
    {L : DerivedCategory (StructureSheafModules (Spec R).sheaf)}
    (hL : letI := derivedMonoidalStructure (Spec R).sheaf; MonoidalCategory.IsInvertible L)
    (u : letI := derivedMonoidalStructure (Spec R).sheaf
      (derivedTildeStructureSheafModules R).obj ω ⊗ L ≅ M) :
    IsIso (derivedSheafHomCounit (Spec R).sheaf
      ((derivedTildeStructureSheafModules R).obj ω) M) :=
  isIso_derivedSheafHomCounit_of_iso_tensorUnit (Spec R).sheaf _ M hL u
    (derivedTildeDerivedSheafHomSelfUnitIso R hω)

end Stacks.Duality

end
