module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShiftedSumIsProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedLimitOfTruncations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent

/-!
# A sum of shifted modules with affine-acyclic summands is their product (towards Stacks 08IZ)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `ℱ_n`, `n ≥ 0`, be sheaves
of `𝒪_𝒳`-modules on its big fppf site.  This file proves that the canonical map

`⊕_n ℱ_n[n] ⟶ ∏_n ℱ_n[n]`

is an isomorphism in `D(𝒪_𝒳)` as soon as the objects lying over an affine scheme cover `𝒳_fppf`
and `H^q(x, ℱ_n) = 0` for `q > 0` and every such object `x`.  The canonical map is
`Pi.lift (Sigma.π ...)`, the map whose component from the `m`-th summand to the `n`-th factor is
the identity for `m = n` and zero otherwise.

This is the argument of **Stacks 08IZ**: the sum is the derived limit of its canonical
truncations (**Stacks 0D6P** with `d = 0`, the argument of **Stacks 08IY**), and those
truncations are the finite partial sums, whose limit is the product
(`Stacks.ShiftedSum.isIso_piLift_sigmaPi_of_distTriang_truncation`).  **Stacks 08IZ** itself, for
an algebraic stack and modules that are locally quasi-coherent with the flat base change property
of **Stacks 0762**, with the vanishing proved rather than assumed, is
`AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedSingleFamily_algebraicStack` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ShiftedSumOfModulesAlgebraicStack.lean`.

## Main results

* `AlgebraicGeometry.Stack.shiftedSingleFamily`: the family `n ↦ ℱ_n[n]` in `D(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedSingleFamily_of_isZero_rightDerived`:
  the sum-to-product isomorphism from the affine vanishing of the summands.
* `AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedLqcFbc`: the same at hom universe
  `u + 1`, for summands satisfying the presheaf reading
  `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange` of the flat base change
  property, with the vanishing `AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules` as a
  hypothesis.

## The index set

The family is indexed by `n ≥ 0`, which is the case the source applies — immediately after 08IZ,
to `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]` — and the case the source's proof supports: for a family indexed by all
of `ℤ` the truncation `τ_{≥ -N}(⊕_n ℱ_n[n])` is not a finite partial sum.  See the implementation
notes of `StacksFrontier/Algebra/Homology/DerivedCategory/ShiftedSumIsProduct.lean`.

## Instance hypotheses

`HasSheafify`, `WEqualsLocallyBijective` and `EnoughInjectives` on the fppf modules of `𝒳`, and
`IsGrothendieckAbelian` for those modules, which supplies the countable direct sums and products
of `D(𝒪_𝒳)` (**Stacks 07D9**) through `Stacks.Injectives.hasCoproducts_derivedCategory`,
`Stacks.Injectives.hasProducts_derivedCategory` and `CategoryTheory.Limits.hasCoproducts_shrink`.
For an algebraic stack all of them hold, and they are discharged in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ShiftedSumOfModulesAlgebraicStack.lean`.

## References

* [Stacks Project, Tag 08IZ](https://stacks.math.columbia.edu/tag/08IZ)
* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 0D6P](https://stacks.math.columbia.edu/tag/0D6P)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe m u v w

namespace AlgebraicGeometry.Stack

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (fppfSiteModules B S hS p hp)]
  [IsGrothendieckAbelian.{m} (fppfSiteModules B S hS p hp)]

/-- The family `n ↦ ℱ_n[n]` in `D(𝒪_𝒳)`: the sheaf `ℱ_n` of `𝒪_𝒳`-modules placed in
cohomological degree `-n`. -/
def shiftedSingleFamily [HasDerivedCategory (fppfSiteModules B S hS p hp)]
    (F : ℕ → fppfSiteModules B S hS p hp) :
    ℕ → DerivedCategory (fppfSiteModules B S hS p hp) :=
  fun n => (DerivedCategory.singleFunctor (fppfSiteModules B S hS p hp) (-(n : ℤ))).obj (F n)

/-- **The argument of Stacks 08IZ from the affine vanishing of its summands.** Let
`p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids whose objects lying over an affine
scheme cover `𝒳_fppf`, and let `ℱ_n`, `n ≥ 0`, be `𝒪_𝒳`-modules with `H^q(x, ℱ_n) = 0` for
`q > 0` and every object `x` lying over an affine scheme.  Then the canonical map

`⊕_n ℱ_n[n] ⟶ ∏_n ℱ_n[n]`

is an isomorphism in `D(𝒪_𝒳)`.

The cohomology sheaves of the sum are the `ℱ_n`, so the sum is the derived limit of its canonical
truncations (**Stacks 0D6P** with `d = 0`, the argument of **Stacks 08IY**), and those truncations
are the finite partial sums, whose limit is the product
(`Stacks.ShiftedSum.isIso_piLift_sigmaPi_of_distTriang_truncation`). -/
theorem isIso_coproductToProduct_shiftedSingleFamily_of_isZero_rightDerived
    (F : ℕ → fppfSiteModules B S hS p hp)
    (hcov : (BigFppfOver.associatedTopology B S hS p .fppf).HasEnoughObjects
      (fun x => IsAffineOver B S hS (p.obj x)))
    (hvan : ∀ n : ℕ, ∀ V : 𝒳, IsAffineOver B S hS (p.obj V) → ∀ q : ℕ, 0 < q →
      IsZero (((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp)
        (.op V)).rightDerived q).obj (F n))) :
    IsIso (Pi.lift (Sigma.π (shiftedSingleFamily B S hS p hp F))) := by
  classical
  have hge : ∀ n : ℕ, (shiftedSingleFamily B S hS p hp F n).IsGE (-(n : ℤ)) := by
    intro n
    dsimp only [shiftedSingleFamily]
    infer_instance
  have hle : ∀ n : ℕ, (shiftedSingleFamily B S hS p hp F n).IsLE (-(n : ℤ)) := by
    intro n
    dsimp only [shiftedSingleFamily]
    infer_instance
  -- the countable sums and products of `D(𝒪_𝒳)` of Stacks 07D9
  have : HasCoproducts.{0} (DerivedCategory (fppfSiteModules B S hS p hp)) :=
    hasCoproducts_shrink.{0, m} (C := DerivedCategory (fppfSiteModules B S hS p hp))
  have : HasProducts.{0} (DerivedCategory (fppfSiteModules B S hS p hp)) :=
    hasProducts_shrink.{0, m} (C := DerivedCategory (fppfSiteModules B S hS p hp))
  -- the vanishing hypothesis of Stacks 0D6P for the sum, from `hvan`
  have hvan' : ∀ V : 𝒳, IsAffineOver B S hS (p.obj V) → ∀ q : ℕ, 0 < q → ∀ r : ℤ,
      IsZero (((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp)
        (.op V)).rightDerived q).obj
          ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) r).obj
            (∐ shiftedSingleFamily B S hS p hp F))) := by
    intro V hV q hq r
    rcases le_or_gt r 0 with hr | hr
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = -(n : ℤ) := ⟨(-r).toNat, by omega⟩
      have hiso : (DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp)
          (-(n : ℤ))).obj (∐ shiftedSingleFamily B S hS p hp F) ≅ F n :=
        Stacks.ShiftedSum.homologyCoproductIso (shiftedSingleFamily B S hS p hp F) hge hle n ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (fppfSiteModules B S hS p hp) (-(n : ℤ))).app (F n)
      exact (hvan n V hV q hq).of_iso
        (((SheafOfModules.evaluation (fppfSiteRingSheaf B S hS p hp) (.op V)).rightDerived
          q).mapIso hiso)
    · have hz := Stacks.ShiftedSum.isZero_homologyCoproduct_of_pos
        (shiftedSingleFamily B S hS p hp F) hle r hr
      have : Injective ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) r).obj
          (∐ shiftedSingleFamily B S hS p hp F)) :=
        ⟨fun g f _ => ⟨0, by rw [comp_zero]; exact (hz.eq_of_tgt g 0).symm⟩⟩
      obtain ⟨q', rfl⟩ : ∃ q' : ℕ, q = q' + 1 := ⟨q - 1, by omega⟩
      exact Functor.isZero_rightDerived_obj_injective_succ _ q' _
  -- Stacks 08IY for the sum, in the form of the Milnor triangle based at the sum itself
  have hprodTower : HasProduct fun N : ℕ =>
      (Stacks.DerivedLimit.truncGETower (fppfSiteModules B S hS p hp)
        (∐ shiftedSingleFamily B S hS p hp F)).obj ⟨N⟩ :=
    Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower
      (fppfSiteRingSheaf B S hS p hp) (∐ shiftedSingleFamily B S hS p hp F)
  obtain ⟨connecting, htriangle⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower (fppfSiteModules B S hS p hp)
      (∐ shiftedSingleFamily B S hS p hp F))
    (fun N : ℕ => (DerivedCategory.TStructure.t.truncGEπ (-(N : ℤ))).app
      (∐ shiftedSingleFamily B S hS p hp F))
    (fun N => Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map
      (∐ shiftedSingleFamily B S hS p hp F) (homOfLE (Nat.le_succ N)).op)
    (fun L c pr d hT hcn =>
      Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
        (fppfSiteRingSheaf B S hS p hp) (∐ shiftedSingleFamily B S hS p hp F)
        (fun x => IsAffineOver B S hS (p.obj x)) hcov
        (fun V hV q hq r => hvan' V hV q hq r) L c pr d hT hcn)
  simp only [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ] at htriangle
  exact Stacks.ShiftedSum.isIso_piLift_sigmaPi_of_distTriang_truncation
    (shiftedSingleFamily B S hS p hp F) hge hle connecting htriangle

end

section

variable {𝒳 : Type v} [Category.{u + 1} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (fppfSiteModules B S hS p hp)]
  [IsGrothendieckAbelian.{m} (fppfSiteModules B S hS p hp)]

/-- **The sum-to-product isomorphism of Stacks 08IZ, at hom universe `u + 1`, from the affine
vanishing as a hypothesis.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and
let `ℱ_n`, `n ≥ 0`, be sheaves of `𝒪_𝒳`-modules on its big fppf site which satisfy the presheaf
reading `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange` of
locally quasi-coherent with the flat base change property.  If `hvan`, the affine vanishing
`AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules`, holds, then the canonical map

`⊕_n ℱ_n[n] ⟶ ∏_n ℱ_n[n]`

is an isomorphism in `D(𝒪_𝒳)`.

This is not Stacks 08IZ: it takes the affine vanishing as the hypothesis `hvan`, and it reads the
flat base change property at the presheaf level, which is stronger than **Stacks 0762**.
**Stacks 08IZ** itself, for an algebraic stack with the source's reading of 0762 and with no
vanishing hypothesis, is
`AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedSingleFamily_algebraicStack` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ShiftedSumOfModulesAlgebraicStack.lean`. -/
theorem isIso_coproductToProduct_shiftedLqcFbc (F : ℕ → fppfSiteModules B S hS p hp)
    (hF : ∀ n : ℕ, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp (F n).val)
    (hvan : HasAffineAcyclicLqcFbcModules B E h S hS p hp) :
    IsIso (Pi.lift (Sigma.π (shiftedSingleFamily B S hS p hp F))) :=
  isIso_coproductToProduct_shiftedSingleFamily_of_isZero_rightDerived B S hS p hp F
    (hasEnoughObjects_isAffineOver B S hS p hp)
    (fun n V hV q hq => hvan (F n) (hF n) V hV q hq)

end

end AlgebraicGeometry.Stack

end
