module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.EilenbergZilber
public import StacksFrontier.Homology.KFlat.DiagramResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedExternalTensorProductFormula
public import StacksFrontier.Homology.DerivedCategory.Monoidal.MapDerivedCategoryMonoidal
public import StacksFrontier.Homology.RestrictionMapHomologicalComplexKFlat
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek to the point preserves derived tensor products

Let `C` be a small category with the chaotic topology and `R` a commutative ring, as in
Example 08PF, so that modules over `R̲` are the presheaves `Cᵒᵖ ⥤ R-Mod` and the derived lower
shriek `Lπ_! = Stacks.CategoryHomology.totalDerivedColimit` is the total left derived functor of
the colimit over `Cᵒᵖ`.  Tag 08QC asserts that if `C` carries a cosimplicial object `U_•` to which
Tag 08Q9 applies, then

`Lπ_!(K₁ ⊗^L_{R̲} K₂) = Lπ_!(K₁) ⊗^L_R Lπ_!(K₂)`

for all `K₁, K₂ ∈ D(R̲)`.  This file proves it, as an isomorphism of bifunctors
`D(R̲) × D(R̲) ⥤ D(R)`.

The proof is the source's.  Write `g : C → C × C` for the diagonal and `g_i` for the two
projections.  The inverse image `g^{-1}` is strong monoidal on derived categories (Tag 07A4), so
it carries `g₁^{-1}K₁ ⊗^L g₂^{-1}K₂` to `K₁ ⊗^L K₂`; the diagonal image of `U_•` is again a point
resolution (Tag 08Q4), so `Lπ_! ∘ g^{-1} = L(π × π)_!` (Tag 08QA); and Tag 08QB computes
`L(π × π)_!(g₁^{-1}K₁ ⊗^L g₂^{-1}K₂)` as `Lπ_!K₁ ⊗^L Lπ_!K₂`.

## Main definitions

* `CategoryTheory.Functor.tensorIsoOfDiagonal`: the formal skeleton of the reduction along the
  diagonal, which assembles a tensor comparison out of the three inputs above.
* `Stacks.ChaoticSite.inverseImageAlongAFunctorDerivedMonoidal`: **Tag 07A4 for a functor of
  chaotic sites on the unbounded derived categories**: restriction along it is strong monoidal
  for the derived tensor products.
* `Stacks.ChaoticSite.totalDerivedColimitTensorIsoOfExternal`: the reduction of Tag 08QC to
  Tag 08QB.
* `Stacks.ChaoticSite.totalDerivedColimitTensorIso`: **Tag 08QC**.

## Implementation notes

The derived tensor products are `CochainComplex.KFlatMonoidal.derivedMonoidal`.  Over `R` the
K-flat resolutions it needs are Stacks 06Y4
(`CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso`), and over the presheaf categories
of `C` and of `C × C` they are Stacks 06YS for the chaotic site
(`Stacks.CategoryHomology.exists_kFlat_quasiIso_diagrams`); neither is an assumption.

The site and the ring live in one universe `u` and the coefficients are `ModuleCat.{u} R`, the
universe in which `Stacks.CategoryHomology.totalDerivedColimit` and the repository's
Tag 08QA (`Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageUnboundedNatIso`) and
Tag 08QB are stated.

The statement is an isomorphism of bifunctors, so naturality in both arguments is part of its
type; the source writes an equality of objects and constructs the identification by the chain
of isomorphisms above, which is the isomorphism given here.  The canonical oplax comparison
`Stacks.CategoryHomology.totalDerivedColimitTensorComparison`, and the restricted form
`Stacks.ChaoticSite.isIso_totalDerivedColimitTensorComparison` of the tag about it, are stated in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.EilenbergZilber` for coefficient
categories whose objects and morphisms share a universe, which excludes `ModuleCat.{u} R`.

## References

* [Stacks Project, Tag 08QC](https://stacks.math.columbia.edu/tag/08QC)
* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08Q4](https://stacks.math.columbia.edu/tag/08Q4)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

/-! ### The formal skeleton of the reduction along the diagonal -/

namespace CategoryTheory.Functor

section Diagonal

universe v₄ v₅ v₆ u₄ u₅ u₆

variable {D : Type u₄} [Category.{v₄} D] {E : Type u₅} [Category.{v₅} E]
  {P : Type u₆} [Category.{v₆} P]

/-- **A tensor comparison assembled from a diagonal.**  Let `L : D ⥤ P` and `L' : E ⥤ P` be
functors, let `d : E ⥤ D` be a "diagonal restriction" split by two "external image" functors
`r₁ r₂ : D ⥤ E`, and let `T`, `T'`, `S` be tensor bifunctors on `D`, `E` and `P`.  Given

* `eT`, that `d` carries `T'` to `T`;
* `eL`, that `d` followed by `L` is `L'`;
* `eP`, the external tensor formula for `L'` on a pair of external images;

there is a comparison `T ⋙ L ≅ L.prod L ⋙ S`.

This is the formal skeleton of the proof of [Stacks, Tag 08QC]: at the chaotic site of a
category `C` with `d` the inverse image along the diagonal, `r_i` the inverse images along the
two projections of `C × C`, and `L`, `L'` the derived lower shrieks to the point, `eT` is
[Stacks, Tag 07A4], `eL` is [Stacks, Tag 08QA] for the diagonal, and `eP` is
[Stacks, Tag 08QB].  Nothing of the monoidal structures themselves is used: the three inputs
are isomorphisms of functors and the conclusion is obtained by whiskering them together. -/
def tensorIsoOfDiagonal (L : D ⥤ P) (L' : E ⥤ P) (d : E ⥤ D) (r₁ r₂ : D ⥤ E)
    (T : D × D ⥤ D) (T' : E × E ⥤ E) (S : P × P ⥤ P)
    (e₁ : r₁ ⋙ d ≅ 𝟭 D) (e₂ : r₂ ⋙ d ≅ 𝟭 D) (eT : T' ⋙ d ≅ d.prod d ⋙ T)
    (eL : d ⋙ L ≅ L') (eP : r₁.prod r₂ ⋙ T' ⋙ L' ≅ L.prod L ⋙ S) :
    T ⋙ L ≅ L.prod L ⋙ S :=
  let er : r₁.prod r₂ ⋙ d.prod d ≅ 𝟭 (D × D) := NatIso.prod e₁ e₂
  let e : r₁.prod r₂ ⋙ T' ⋙ d ≅ T :=
    Functor.isoWhiskerLeft (r₁.prod r₂) eT ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight er T ≪≫ Functor.leftUnitor T
  (Functor.isoWhiskerRight e L).symm ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (r₁.prod r₂)
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T' eL) ≪≫ eP

end Diagonal

/-- The tensor bifunctor of a monoidal category is the uncurried form of `curriedTensor`. -/
@[simps!]
def tensorIsoUncurry (D : Type*) [Category D] [MonoidalCategory D] :
    MonoidalCategory.tensor D ≅ Functor.uncurry.obj (curriedTensor D) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp [MonoidalCategory.tensorHom_def])

end CategoryTheory.Functor

namespace Stacks.ChaoticSite

open Stacks.CategoryHomology CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CochainComplex.symmetricCategory

universe u

/-! ### Restriction along a functor is monoidal on derived categories -/

section Restriction

variable (C C' : Type u) [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C) (R : Type u)
  [CommRing R]

/-- Restriction of presheaves of modules along a functor is strong monoidal for the sectionwise
tensor product. -/
instance inverseImageAlongAFunctor_monoidal :
    (inverseImageAlongAFunctor C C' f R).Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (ModuleCat.{u} R)).obj f.op).Monoidal

/-- **[Stacks, Tag 07A4] for a morphism of chaotic sites, on the unbounded derived categories.**
The inverse image `g^{-1}` along a functor `f : C' ⥤ C` of chaotic sites is strong monoidal for
the derived tensor products of `D(C, R̲)` and `D(C', R̲)`.

It is `CategoryTheory.Functor.mapDerivedCategoryMonoidal` applied to restriction along `f`: that
functor is exact and strong monoidal for the sectionwise tensor product, and it carries K-flat
complexes to K-flat complexes because K-flatness is a sectionwise condition
(`CochainComplex.KFlatBifunctor.kFlat_whiskeringLeftMapHomologicalComplex`).  The derived tensor
products exist by `Stacks.CategoryHomology.exists_kFlat_quasiIso_diagrams`. -/
@[instance_reducible, sga "4 XVII 4.2.8" "(i) stalk formula"]
def inverseImageAlongAFunctorDerivedMonoidal :
    letI := derivedMonoidal (Cᵒᵖ ⥤ ModuleCat.{u} R) (exists_kFlat_quasiIso_diagrams (J := Cᵒᵖ))
    letI := derivedMonoidal (C'ᵒᵖ ⥤ ModuleCat.{u} R) (exists_kFlat_quasiIso_diagrams (J := C'ᵒᵖ))
    (inverseImageAlongAFunctor C C' f R).mapDerivedCategory.Monoidal :=
  letI : ∀ n : ℤ, PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ⁻¹' {n})) (inverseImageAlongAFunctor C C' f R) := fun _ =>
    inferInstanceAs (PreservesColimitsOfShape _
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ (ModuleCat.{u} R)).obj f.op))
  Functor.mapDerivedCategoryMonoidal (inverseImageAlongAFunctor C C' f R)
    (fun K hK => kFlat_whiskeringLeftMapHomologicalComplex f.op K hK)
    (exists_kFlat_quasiIso_diagrams (J := Cᵒᵖ)) (exists_kFlat_quasiIso_diagrams (J := C'ᵒᵖ))

end Restriction

/-! ### The Eilenberg–Zilber isomorphism -/

section EilenbergZilber

variable (C : Type u) [SmallCategory C] (R : Type u) [CommRing R]

/-- The derived diagonal restriction of the first external image is the identity. -/
def projFstDerivedDiagIso :
    (projFstInverseImage C C R).mapDerivedCategory ⋙
        (inverseImageAlongAFunctor (C × C) C (Functor.diag C) R).mapDerivedCategory ≅
      𝟭 (DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u} R)) :=
  Functor.mapDerivedCategoryCompIsoId _ _ rfl

/-- The derived diagonal restriction of the second external image is the identity. -/
def projSndDerivedDiagIso :
    (projSndInverseImage C C R).mapDerivedCategory ⋙
        (inverseImageAlongAFunctor (C × C) C (Functor.diag C) R).mapDerivedCategory ≅
      𝟭 (DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u} R)) :=
  Functor.mapDerivedCategoryCompIsoId _ _ rfl

/-- **The reduction of [Stacks, Tag 08QC] to [Stacks, Tag 08QB].**  On the chaotic site of a
category carrying a cosimplicial point resolution `U_•`, any identification `eP` of
`L(π × π)_!(g₁^{-1}K₁ ⊗^L g₂^{-1}K₂)` with `Lπ_!K₁ ⊗^L Lπ_!K₂`, natural in both variables, yields
`Lπ_!(K₁ ⊗^L K₂) ≅ Lπ_!K₁ ⊗^L Lπ_!K₂`, natural in both variables.

This is the proof of the source, run by `CategoryTheory.Functor.tensorIsoOfDiagonal`: the inverse
image `g^{-1}` along the diagonal carries `g₁^{-1}K₁ ⊗^L g₂^{-1}K₂` to `K₁ ⊗^L K₂`
([Stacks, Tag 07A4], `Stacks.ChaoticSite.inverseImageAlongAFunctorDerivedMonoidal`), and
`Lπ_! ∘ g^{-1} = L(π × π)_!` ([Stacks, Tag 08QA],
`Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageUnboundedNatIso`), applicable because
the diagonal image of `U_•` is a point resolution of `C × C` ([Stacks, Tag 08Q4],
`Stacks.ChaoticSite.isPointResolution_comp_diag`). -/
def totalDerivedColimitTensorIsoOfExternal
    (U : CosimplicialObject C) (hU : IsPointResolution U) :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal (Cᵒᵖ ⥤ ModuleCat.{u} R) (exists_kFlat_quasiIso_diagrams (J := Cᵒᵖ))
    letI := derivedMonoidal ((C × C)ᵒᵖ ⥤ ModuleCat.{u} R)
      (exists_kFlat_quasiIso_diagrams (J := (C × C)ᵒᵖ))
    ∀ (_eP : (projFstInverseImage C C R).mapDerivedCategory.prod
          (projSndInverseImage C C R).mapDerivedCategory ⋙
          MonoidalCategory.tensor (DerivedCategory ((C × C)ᵒᵖ ⥤ ModuleCat.{u} R)) ⋙
            totalDerivedColimit (C × C) (ModuleCat.{u} R) ≅
        (totalDerivedColimit C (ModuleCat.{u} R)).prod (totalDerivedColimit C (ModuleCat.{u} R)) ⋙
          MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u} R))),
    MonoidalCategory.tensor (DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u} R)) ⋙
        totalDerivedColimit C (ModuleCat.{u} R) ≅
      (totalDerivedColimit C (ModuleCat.{u} R)).prod (totalDerivedColimit C (ModuleCat.{u} R)) ⋙
        MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u} R)) :=
  letI := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  letI := derivedMonoidal (Cᵒᵖ ⥤ ModuleCat.{u} R) (exists_kFlat_quasiIso_diagrams (J := Cᵒᵖ))
  letI := derivedMonoidal ((C × C)ᵒᵖ ⥤ ModuleCat.{u} R)
    (exists_kFlat_quasiIso_diagrams (J := (C × C)ᵒᵖ))
  letI := inverseImageAlongAFunctorDerivedMonoidal (C × C) C (Functor.diag C) R
  fun eP => Functor.tensorIsoOfDiagonal (totalDerivedColimit C (ModuleCat.{u} R))
    (totalDerivedColimit (C × C) (ModuleCat.{u} R))
    (inverseImageAlongAFunctor (C × C) C (Functor.diag C) R).mapDerivedCategory
    (projFstInverseImage C C R).mapDerivedCategory
    (projSndInverseImage C C R).mapDerivedCategory _ _ _
    (projFstDerivedDiagIso C R) (projSndDerivedDiagIso C R)
    (Functor.Monoidal.μNatIso
      (inverseImageAlongAFunctor (C × C) C (Functor.diag C) R).mapDerivedCategory).symm
    (ModuleValued.derivedColimitInverseImageUnboundedNatIso (Functor.diag C) hU
      (isPointResolution_comp_diag U hU)) eP

/-- The canonical comparison of [Stacks, Tag 08QB] on `C × C`, as an isomorphism of bifunctors
once it is known to be invertible, with the tensor products written through
`MonoidalCategory.tensor`. -/
def derivedExternalTensorIsoOfIsIso
    (h : IsIso (derivedExternalTensorComparisonNatTrans C C R
      (exists_kFlat_quasiIso_diagrams (J := (C × C)ᵒᵖ)))) :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal ((C × C)ᵒᵖ ⥤ ModuleCat.{u} R)
      (exists_kFlat_quasiIso_diagrams (J := (C × C)ᵒᵖ))
    (projFstInverseImage C C R).mapDerivedCategory.prod
          (projSndInverseImage C C R).mapDerivedCategory ⋙
          MonoidalCategory.tensor (DerivedCategory ((C × C)ᵒᵖ ⥤ ModuleCat.{u} R)) ⋙
            totalDerivedColimit (C × C) (ModuleCat.{u} R) ≅
        (totalDerivedColimit C (ModuleCat.{u} R)).prod (totalDerivedColimit C (ModuleCat.{u} R)) ⋙
          MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u} R)) :=
  letI := derivedMonoidal (ModuleCat.{u} R)
    (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
  letI := derivedMonoidal ((C × C)ᵒᵖ ⥤ ModuleCat.{u} R)
    (exists_kFlat_quasiIso_diagrams (J := (C × C)ᵒᵖ))
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Functor.tensorIsoUncurry _) _) ≪≫
    asIso (derivedExternalTensorComparisonNatTrans C C R
      (exists_kFlat_quasiIso_diagrams (J := (C × C)ᵒᵖ))) ≪≫
    Functor.isoWhiskerLeft _ (Functor.tensorIsoUncurry _).symm

/-- **[Stacks, Tag 08QC].**  Let `C` be a small category with the chaotic topology and `R` a
commutative ring, as in Example 08PF, and suppose `C` carries a cosimplicial object `U_•` to which
Tag 08Q9 applies: for every object `W` the simplicial set `Mor_C(U_•, W)` is homotopy equivalent
to a point.  Then derived lower shriek to the point preserves derived tensor products:

`Lπ_!(K₁ ⊗^L_{R̲} K₂) ≅ Lπ_!(K₁) ⊗^L_R Lπ_!(K₂)`

for all `K₁, K₂ ∈ D(R̲)`, naturally in both, as an isomorphism of bifunctors
`D(Cᵒᵖ ⥤ R-Mod) × D(Cᵒᵖ ⥤ R-Mod) ⥤ D(R)`.

It is `Stacks.ChaoticSite.totalDerivedColimitTensorIsoOfExternal` (Tags 07A4, 08Q4 and 08QA along
the diagonal) applied to [Stacks, Tag 08QB] on `C × C`,
`Stacks.CategoryHomology.isIso_derivedExternalTensorComparisonNatTrans`. -/
@[stacks 08QC]
def totalDerivedColimitTensorIso (U : CosimplicialObject C) (hU : IsPointResolution U) :
    letI := derivedMonoidal (ModuleCat.{u} R)
      (CochainComplex.DerivedTensor.OneSided.exists_kFlat_quasiIso R)
    letI := derivedMonoidal (Cᵒᵖ ⥤ ModuleCat.{u} R) (exists_kFlat_quasiIso_diagrams (J := Cᵒᵖ))
    MonoidalCategory.tensor (DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u} R)) ⋙
        totalDerivedColimit C (ModuleCat.{u} R) ≅
      (totalDerivedColimit C (ModuleCat.{u} R)).prod (totalDerivedColimit C (ModuleCat.{u} R)) ⋙
        MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u} R)) :=
  totalDerivedColimitTensorIsoOfExternal C R U hU
    (derivedExternalTensorIsoOfIsIso C R (isIso_derivedExternalTensorComparisonNatTrans C C R))

end EilenbergZilber

end Stacks.ChaoticSite

end
