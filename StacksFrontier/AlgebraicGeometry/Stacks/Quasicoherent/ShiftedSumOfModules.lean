module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShiftedSumIsProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedLimitOfTruncations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent

/-!
# A sum of shifted modules in `LQCoh^fbc` is their product (Stacks 08IZ)

Let `𝒳` be an algebraic stack and let `ℱ_n`, `n ≥ 0`, be sheaves of `𝒪_𝒳`-modules on the big fppf
site of `𝒳` which are locally quasi-coherent (**Stacks 06WJ**) and have the flat base change
property (**Stacks 0762**).  **Stacks 08IZ** says that the canonical map

`⊕_n ℱ_n[n] ⟶ ∏_n ℱ_n[n]`

is an isomorphism in `D(𝒪_𝒳)`.  The canonical map is `Pi.lift (Sigma.π ...)`, the map whose
component from the `m`-th summand to the `n`-th factor is the identity for `m = n` and zero
otherwise.

The source's one-line proof is the citation of **Stacks 08IY**: the sum is the derived limit of
its canonical truncations, and those truncations are the finite partial sums, whose limit is the
product.  Here 08IY enters exactly as it is formalized, through
`AlgebraicGeometry.Stack.isIso_to_isDerivedLimit_truncGETower_of_lqcFbc` and the covering class
`AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver`
(`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedLimitOfTruncations.lean`), and the
rest of the argument is
`Stacks.ShiftedSum.isIso_piLift_sigmaPi_of_distTriang_truncation`.

## The index set

The source writes `ℱ_n` without saying over what the index `n` runs.  It is read here as `n ≥ 0`,
which is the case the section applies — immediately afterwards, to `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]` — and
the case the source's proof supports: for a family indexed by all of `ℤ` the truncation
`τ_{≥ -N}(⊕_n ℱ_n[n])` is not a finite partial sum, and the identification of the sum with the
product then needs the comparison on K-injective resolutions rather than 08IY alone.  See the
implementation notes of
`StacksFrontier/Algebra/Homology/DerivedCategory/ShiftedSumIsProduct.lean`.

## Main results

* `AlgebraicGeometry.Stack.shiftedSingleFamily`: the family `n ↦ ℱ_n[n]` in `D(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedLqcFbc`: **Stacks 08IZ**.

## What is carried

The hypothesis `hvan` is `AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules`, *the same
predicate the library's 08IY carries*: the vanishing `H^p(x, ℱ) = 0` for `p > 0`, `ℱ` in
`LQCoh^fbc(𝒪_𝒳)` and `x` an object lying over an affine scheme, which the source obtains from
**Stacks 075R**, **Stacks 075F**, **Stacks 0756** and **Stacks 01XB**, none of which this
repository has.  Carrying the same predicate is deliberate: whoever discharges it discharges it
for 08IY and for this statement at once.

The instance hypotheses are those of 08IY — `HasSheafify`, `WEqualsLocallyBijective` and
`EnoughInjectives` on the fppf modules of `𝒳`, satisfiable by
`AlgebraicGeometry.Stack.enoughInjectives_fppfSiteModules_of_univLE` — together with
`IsGrothendieckAbelian` for those modules, which is what supplies the countable direct sums and
products of `D(𝒪_𝒳)` (**Stacks 07D9**), and which is carried as an instance in the same way by
`StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/AcyclicObject.lean`.  The four
(co)products the statement needs are *not* hypotheses: they are produced from that instance by
`Stacks.Injectives.hasCoproducts_derivedCategory`,
`Stacks.Injectives.hasProducts_derivedCategory` and
`CategoryTheory.Limits.hasCoproducts_shrink`.

## References

* [Stacks Project, Tag 08IZ](https://stacks.math.columbia.edu/tag/08IZ)
* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
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

variable {𝒳 : Type v} [Category.{u + 1} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (fppfSiteModules B S hS p hp)]
  [IsGrothendieckAbelian.{m} (fppfSiteModules B S hS p hp)]

/-- The family `n ↦ ℱ_n[n]` in `D(𝒪_𝒳)`: the sheaf `ℱ_n` of `𝒪_𝒳`-modules placed in
cohomological degree `-n`. -/
def shiftedSingleFamily (F : ℕ → fppfSiteModules B S hS p hp) :
    ℕ → DerivedCategory (fppfSiteModules B S hS p hp) :=
  fun n => (DerivedCategory.singleFunctor (fppfSiteModules B S hS p hp) (-(n : ℤ))).obj (F n)

/-- **Stacks 08IZ.** Let `𝒳` be an algebraic stack and let `ℱ_n`, `n ≥ 0`, be sheaves of
`𝒪_𝒳`-modules on its big fppf site which are locally quasi-coherent (**Stacks 06WJ**) and have
the flat base change property (**Stacks 0762**).  Then the canonical map

`⊕_n ℱ_n[n] ⟶ ∏_n ℱ_n[n]`

is an isomorphism in `D(𝒪_𝒳)`.

The vanishing `hvan` is the hypothesis the library's **Stacks 08IY** carries, and it is carried in
exactly that form; see this file's module documentation. -/
@[stacks 08IZ "the sum of a family of shifted LQCoh^fbc modules, indexed by n ≥ 0 as the \
source's proof supports, maps isomorphically to their product in D(𝒪_𝒳); the affine \
acyclicity the library's Stacks 08IY carries is carried here as that same predicate"]
theorem isIso_coproductToProduct_shiftedLqcFbc (F : ℕ → fppfSiteModules B S hS p hp)
    (hF : ∀ n : ℕ, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp (F n).val)
    (hvan : HasAffineAcyclicLqcFbcModules B E h S hS p hp) :
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
      have hval : (F n).val ≅
          ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) (-(n : ℤ))).obj
            (∐ shiftedSingleFamily B S hS p hp F)).val :=
        (SheafOfModules.forget (fppfSiteRingSheaf B S hS p hp)).mapIso hiso.symm
      have hlqc := isLocallyQuasicoherent_of_iso B E h S hS p hp hval (hF n).1
      have hfbc : HasFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)
          ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) (-(n : ℤ))).obj
            (∐ shiftedSingleFamily B S hS p hp F)).val :=
        hasFlatBaseChangeProperty_of_iso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) hval (hF n).2
      exact hvan _ ⟨hlqc, hfbc⟩ V hV q hq
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
        (fun x => IsAffineOver B S hS (p.obj x))
        (hasEnoughObjects_isAffineOver B S hS p hp)
        (fun V hV q hq r => hvan' V hV q hq r) L c pr d hT hcn)
  simp only [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ] at htriangle
  exact Stacks.ShiftedSum.isIso_piLift_sigmaPi_of_distTriang_truncation
    (shiftedSingleFamily B S hS p hp F) hge hle connecting htriangle

end

end AlgebraicGeometry.Stack

end
