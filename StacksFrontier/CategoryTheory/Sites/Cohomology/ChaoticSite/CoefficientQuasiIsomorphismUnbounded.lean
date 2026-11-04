module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FreeYonedaCompactObject
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsCoextension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CoefficientQuasiIsomorphism
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryDirectSums
public import StacksFrontier.Homology.Devissage.CompactGenerationFromProjectiveSeparators
import StacksCore.Tactic.StacksAttribute

/-!
# Homology of a category under a coefficient map it inverts, on the unbounded derived category

Let `C` be a small category carrying the chaotic topology, let `U_•` be a cosimplicial object of
`C` which is a point resolution (the hypothesis of [Stacks, Tag 08Q9]), and let `a : 𝒪 ⟶ 𝒪'` be a
morphism of presheaves of rings — on a chaotic site, of sheaves of rings — such that derived lower
shriek of abelian sheaves inverts `Lπ_!(𝒪) ⟶ Lπ_!(𝒪')`. This file proves [Stacks, Tag 08RX]:
for **every** object `K` of the unbounded derived category `D(𝒪)` the canonical comparison

`Lπ_!(K) ⟶ Lπ_!(K ⊗^L_𝒪 𝒪')`

of `Stacks.ChaoticSite.derivedColimitTensorComparison` is an isomorphism in `D(Ab)`. As in the
source, `Lπ_!` here is the derived lower shriek of the underlying complex of abelian sheaves,
`Stacks.ChaoticSite.abelianDerivedColimitOfModules`. The generator step of the source's proof is
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_extensionByZero` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CoefficientQuasiIsomorphism`.

## Main results

* `Stacks.ChaoticSite.isIso_leftDerivedColimit_map_of_isIso_totalDerivedColimit`: the second
  hypothesis of Tag 08RX, read in `D(Ab)`, gives it in every degree.
* `Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app`: **Tag 08RX** —
  `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_𝒪 𝒪')` is invertible for every object `K` of `D(Mod(𝒪))`.
* `Stacks.ChaoticSite.isIso_derivedColimitTensorComparison` and
  `Stacks.ChaoticSite.derivedColimitTensorNatIso`: the comparison is an isomorphism of functors,
  and the resulting identification `Lπ_! ≅ (- ⊗^L_𝒪 𝒪') ⋙ Lπ_!` of functors
  `D(Mod(𝒪)) ⥤ D(Ab)`, which is the canonical and functorial form [Stacks, Tag 09CZ] uses.

## How the conclusion for an arbitrary `K` is reached

The source reduces an arbitrary object `K` of `D(𝒪)` to the generators `j_{W!}𝒪_W`, using that
`Lπ_!` commutes with colimits (Derived Categories, Proposition 13.29.2). Here that reduction is
the dévissage along compact generators of
`StacksDraft.CompactDevissage.isIso_of_isIso_app_single_anyModel`, run on `D(Mod(𝒪))`:

* the generators of `D(Mod(𝒪))` are the free presheaves of modules on the representables placed
  in degree zero, which is the chaotic site's reading of `j_{W!}𝒪_W`. They are projective by
  `PresheafOfModules.freeYonedaProjective`, separating by
  `PresheafOfModules.freeYoneda.isSeparating` and compact by
  `PresheafOfModules.isCompactObject_freeYoneda`;
* both functors being compared are exact and commute with direct sums: for `Lπ_!` this is
  `Stacks.CategoryHomology.totalDerivedColimit_preservesColimitsOfSize` together with
  `Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory` for the
  forgetful functor, and for `- ⊗^L_𝒪 𝒪'` it is
  `Stacks.ChaoticSite.derivedExtendScalars_preservesColimitsOfSize`, both functors being left
  adjoints; restriction of scalars is a left adjoint too, by
  `Stacks.PresheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction`;
* what is devissaged is the unit `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_𝒪 𝒪')` read before the identification
  `Stacks.ChaoticSite.restrictScalarsDerivedColimitIso`, namely the whiskering of
  `(derivedExtendScalarsAdjunction a).unit` on the right by `abelianDerivedColimitOfModules 𝒪`.
  It is compatible with the shift because the derived change-of-coefficients adjunction is
  (`CategoryTheory.Adjunction.CommShift`), and the remaining factor of the comparison is an
  isomorphism, which is `Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_iff`;
* at a generator the invertibility is
  `Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single`, the degree-zero case of
  the tag, proved on Moore double complexes from the generator step.

The second hypothesis of the tag is taken in the form the source states it, invertibility of
`Lπ_!(𝒪) ⟶ Lπ_!(𝒪')` in `D(Ab)`; it is turned into the degreewise form the generator step uses
by `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff`,
`Stacks.ChaoticSite.quasiIso_mooreCochainComplex_map_iff` and
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_iff`, which is
`isIso_leftDerivedColimit_map_of_isIso_totalDerivedColimit` below.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The second hypothesis of Tag 08RX in `D(Ab)` gives it in every degree.** If derived lower
shriek, as a functor to the unbounded derived category `D(Ab)`, inverts a morphism of abelian
presheaves placed in degree zero, then `L_nπ_!` inverts it for every `n`.

The two readings are compared through the Moore complex of the evaluation on the point
resolution: `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff` says the
first is the quasi-isomorphy of that Moore complex, and
`Stacks.ChaoticSite.quasiIso_mooreCochainComplex_map_iff` with
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_iff` say the second is its invertibility on
homology in every degree. -/
lemma isIso_leftDerivedColimit_map_of_isIso_totalDerivedColimit (hU : IsPointResolution U)
    {P P' : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (b : P ⟶ P')
    (hb : IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map b)))
    (n : ℕ) :
    IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).map b) := by
  rw [isIso_leftDerivedColimit_map_iff U hU]
  exact (quasiIso_mooreCochainComplex_map_iff U b).1
    ((AbelianValued.isIso_totalDerivedColimit_single_map_iff U hU b).1 hb) n

variable {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O')

/-- **Tag 08RX.** Let `C` be a small category with the chaotic topology and let `a : 𝒪 ⟶ 𝒪'` be a
morphism of presheaves of rings on `C` (on a chaotic site, of sheaves of rings). Assume

1. there is a cosimplicial object `U_•` of `C` as in Tag 08Q9, i.e. a point resolution: every
   `Mor_C(U_•, W)` is homotopy equivalent to the constant simplicial set on a singleton, and
2. `Lπ_!(𝒪) ⟶ Lπ_!(𝒪')` is an isomorphism in `D(Ab)`, where `Lπ_!` is derived lower shriek of
   abelian sheaves applied to the underlying morphism of abelian presheaves placed in degree zero.

Then for **every** object `K` of the unbounded derived category `D(𝒪) = D(Mod(𝒪))` the canonical
comparison

`Lπ_!(K) ⟶ Lπ_!(K ⊗^L_𝒪 𝒪')`

of `Stacks.ChaoticSite.derivedColimitTensorComparison` (induced by `K ⟶ K ⊗^L_𝒪 𝒪'`) is an
isomorphism in `D(Ab)`.

The comparison is `Lπ_!` applied to the unit of the derived change-of-coefficients adjunction,
followed by the identification `Stacks.ChaoticSite.restrictScalarsDerivedColimitIso` of `Lπ_!` on
`𝒪'`-modules with `Lπ_!` on their underlying `𝒪`-modules
(`Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_iff`); so the assertion is the
invertibility of the whiskered unit, which is a morphism of exact direct-sum-preserving functors
on `D(Mod(𝒪))` compatible with the shift. The free presheaves of modules on the representables —
the generators `j_{W!}𝒪_W` of the source's proof — are projective, separating and compact, so the
dévissage along compact generators of
`StacksDraft.CompactDevissage.isIso_of_isIso_app_single_anyModel` reduces the assertion to those
generators placed in degree zero, where it is
`Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single`. -/
@[stacks 08RX]
theorem isIso_derivedColimitTensorComparison_app (hU : IsPointResolution U)
    (ha : IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
        (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u})))))
    (K : DerivedCategory (PresheafOfModules.{u} O)) :
    IsIso ((derivedColimitTensorComparison a).app K) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (PresheafOfModules.{u} O) :=
    HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) (PresheafOfModules.toPresheaf O)
  have := (derivedExtendScalarsAdjunction a).commShift_of_rightAdjoint ℤ
  have : PreservesColimitsOfSize.{u, u} (PresheafOfModules.restrictScalars.{u} a) :=
    (Stacks.PresheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction
      a).leftAdjoint_preservesColimits
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (PresheafOfModules.toPresheaf.{u} O).mapDerivedCategory := fun J ↦
    Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory _ J
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory := fun J ↦
    Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory _ J
  have key : IsIso (Functor.whiskerRight (derivedExtendScalarsAdjunction a).unit
      (abelianDerivedColimitOfModules O)) := by
    refine StacksDraft.CompactDevissage.isIso_of_isIso_app_single_anyModel
      (fun W : C ↦ (PresheafOfModules.free.{u} O).obj (yoneda.obj W))
      (fun W ↦ PresheafOfModules.isCompactObject_freeYoneda W)
      (PresheafOfModules.freeYoneda.isSeparating O) _ fun W ↦ ?_
    exact (isIso_derivedColimitTensorComparison_app_iff a _).1
      (isIso_derivedColimitTensorComparison_app_single U a hU
        (isIso_leftDerivedColimit_map_of_isIso_totalDerivedColimit U hU _ ha) _)
  exact (isIso_derivedColimitTensorComparison_app_iff a K).2
    (inferInstanceAs (IsIso ((Functor.whiskerRight (derivedExtendScalarsAdjunction a).unit
      (abelianDerivedColimitOfModules O)).app K)))

/-- **Tag 08RX as the invertibility of the comparison of functors.** -/
theorem isIso_derivedColimitTensorComparison (hU : IsPointResolution U)
    (ha : IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
        (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u}))))) :
    IsIso (derivedColimitTensorComparison a) := by
  have : ∀ K, IsIso ((derivedColimitTensorComparison a).app K) := fun K ↦
    isIso_derivedColimitTensorComparison_app U a hU ha K
  exact NatIso.isIso_of_isIso_app _

/-- **The identification `Lπ_!(K) = Lπ_!(K ⊗^L_𝒪 𝒪')` of Tag 08RX**, as an isomorphism of
functors `D(Mod(𝒪)) ⥤ D(Ab)` whose underlying morphism is the canonical comparison
`Stacks.ChaoticSite.derivedColimitTensorComparison`. This is the canonical, functorial
identification that [Stacks, Tag 09CZ] uses. -/
def derivedColimitTensorNatIso (hU : IsPointResolution U)
    (ha : IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
        (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u}))))) :
    abelianDerivedColimitOfModules O ≅
      derivedExtendScalars a ⋙ abelianDerivedColimitOfModules O' :=
  haveI := isIso_derivedColimitTensorComparison U a hU ha
  asIso (derivedColimitTensorComparison a)

/-- The underlying morphism of `Stacks.ChaoticSite.derivedColimitTensorNatIso` is the canonical
comparison. -/
@[simp]
lemma derivedColimitTensorNatIso_hom (hU : IsPointResolution U)
    (ha : IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) 0).map
        (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u}))))) :
    (derivedColimitTensorNatIso U a hU ha).hom = derivedColimitTensorComparison a :=
  rfl

end Stacks.ChaoticSite

end
