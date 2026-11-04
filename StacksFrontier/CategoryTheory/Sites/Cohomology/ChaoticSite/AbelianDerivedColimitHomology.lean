module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian

/-!
# The cohomology of derived lower shriek at abelian coefficients

Let `C` be a small category with the chaotic topology and let `U_•` be a cosimplicial object of
`C` which is a point resolution. This file composes the two legs that relate the left derived
functors of the colimit over `Cᵒᵖ` to derived lower shriek into the single statement

`H^{-n}(Lπ_!(ℱ[0])) ≅ (L_n π_!)(ℱ)`, naturally in the abelian presheaf `ℱ`,

where `ℱ[0]` is the abelian presheaf placed in cohomological degree zero, `Lπ_!` is the total
left derived functor of the colimit over `Cᵒᵖ` and `H^m` is the `m`-th cohomology of the derived
category of abelian groups.

The two legs are
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit`, which identifies
`Q(ℱ(U_•))` with `Lπ_!(ℱ[0])` in `D(Ab)`, and `Stacks.ChaoticSite.leftDerivedColimitNatIso`,
which is [Stacks, Tag 08Q9]: the degreewise identification of `L_nπ_!` with the homology of the
Moore complex of `ℱ(U_•)`. Passing between them costs the reindexing of the Moore complex as a
cochain complex over `ℤ`, which puts the simplicial degree `n` in cohomological degree `-n`, and
the factorisation `DerivedCategory.homologyFunctorFactors` of the cohomology of the derived
category through the cohomology of a complex.

## Main definitions

* `Stacks.ChaoticSite.AbelianValued.mooreCochainHomologyNatIso`: the reindexing,
  `H^{-n}(ℱ(U_•)) ≅ H_n(ℱ(U_•))` as an isomorphism of functors.
* `Stacks.ChaoticSite.AbelianValued.mooreCochainHomologyNatIsoLeftDerivedColim`: the reindexing
  leg, `H^{-n}(ℱ(U_•)) ≅ (L_nπ_!)(ℱ)` as an isomorphism of functors. This is the abelian-group
  analogue of `Stacks.ChaoticSite.GeneralValued.mooreCochainHomologyLeftDerivedColimIso`, which
  is the same statement at module coefficients and at one presheaf.
* `Stacks.ChaoticSite.AbelianValued.homologyTotalDerivedColimitSingleNatIso`: the composite,
  `H^{-n}(Lπ_!(ℱ[0])) ≅ (L_nπ_!)(ℱ)` as an isomorphism of functors.

## Main results

* `Stacks.ChaoticSite.AbelianValued.leftDerivedColim_map_eq_zero`: a morphism of abelian
  presheaves which `H^{-n}∘Lπ_!` kills is killed by `L_nπ_!`. This is the naturality of the
  composite, read as the implication a consumer checking a vanishing statement needs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite.AbelianValued

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The reindexing of the Moore complex of `ℱ(U_•)` in cohomology, naturally in `ℱ`**: the
extended Moore complex carries the simplicial degree `n` in cohomological degree `-n`, so its
`H^{-n}` is `H_n(ℱ(U_•))`. This is `HomologicalComplex.extendHomologyIso` along
`ComplexShape.embeddingUpIntLE 0`, which is natural because extending a complex is a functor. -/
def mooreCochainHomologyNatIso (n : ℕ) (m : ℤ) (hm : m = -(n : ℤ)) :
    mooreCochainComplex U ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) m ≅
      cosimplicialMooreComplex U ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  NatIso.ofComponents
    (fun F => ((cosimplicialMooreComplex U).obj F).extendHomologyIso
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) (j := n) (j' := m) (by simp [hm]))
    (fun a => HomologicalComplex.extendHomologyIso_hom_naturality
      ((cosimplicialMooreComplex U).map a) (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (by simp [hm]))

/-- **`H^{-n}` of the extended Moore complex of `ℱ(U_•)` is `(L_nπ_!)(ℱ)`, naturally in `ℱ`.**
The two steps are the reindexing
`Stacks.ChaoticSite.AbelianValued.mooreCochainHomologyNatIso` and [Stacks, Tag 08Q9],
`Stacks.ChaoticSite.leftDerivedColimitNatIso`. This is the abelian-group analogue of
`Stacks.ChaoticSite.GeneralValued.mooreCochainHomologyLeftDerivedColimIso`. -/
def mooreCochainHomologyNatIsoLeftDerivedColim (hU : IsPointResolution U) (n : ℕ) (m : ℤ)
    (hm : m = -(n : ℤ)) :
    mooreCochainComplex U ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) m ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n :=
  mooreCochainHomologyNatIso U n m hm ≪≫ (leftDerivedColimitNatIso U hU n).symm

/-- **The cohomology of derived lower shriek at abelian coefficients**: for `C` a small category
with the chaotic topology and `U_•` a point resolution of `C`,

`H^{-n}(Lπ_!(ℱ[0])) ≅ (L_nπ_!)(ℱ)`,

**naturally in the abelian presheaf `ℱ`**. The composite of the derived form of
[Stacks, Tag 08Q9] at abelian coefficients, which identifies `Lπ_!(ℱ[0])` with `Q(ℱ(U_•))` in
`D(Ab)`, with the reindexing leg
`Stacks.ChaoticSite.AbelianValued.mooreCochainHomologyNatIsoLeftDerivedColim`; the two are tied
together by `DerivedCategory.homologyFunctorFactors`. -/
def homologyTotalDerivedColimitSingleNatIso (hU : IsPointResolution U) (n : ℕ) (m : ℤ)
    (hm : m = -(n : ℤ)) :
    HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit C AddCommGrpCat.{u} ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} m ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n :=
  (Functor.isoWhiskerRight (mooreCochainNatIsoDerivedColimit U hU)
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m)).symm ≪≫
    Functor.isoWhiskerLeft (mooreCochainComplex U)
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} m) ≪≫
    mooreCochainHomologyNatIsoLeftDerivedColim U hU n m hm

/-- **`L_nπ_!` kills a morphism of abelian presheaves that `H^{-n}∘Lπ_!` kills.** This is the
naturality square of
`Stacks.ChaoticSite.AbelianValued.homologyTotalDerivedColimitSingleNatIso` at `a`, which is the
form a consumer checking a vanishing statement on the derived side needs. -/
theorem leftDerivedColim_map_eq_zero (hU : IsPointResolution U) (n : ℕ)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (a : F ⟶ G)
    (ha : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(n : ℤ))).map
        ((totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u})
            (ComplexShape.up ℤ) 0).map a))) = 0) :
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map a = 0 := by
  have e := homologyTotalDerivedColimitSingleNatIso U hU n (-(n : ℤ)) rfl
  rw [← cancel_epi (e.hom.app F), comp_zero, ← e.hom.naturality a]
  dsimp only [Functor.comp_map]
  rw [ha, zero_comp]

end Stacks.ChaoticSite.AbelianValued

end
