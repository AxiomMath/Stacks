module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SpecChartCover
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ModelCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.DualityAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.StdBiduality

/-!
# Duality for a dualizing complex on a locally Noetherian algebraic space

Let `X` be a locally Noetherian algebraic space and `K` a dualizing complex on `X`
(Stacks 0E4Z). This file proves Stacks 0E51: `K` lies in `D_Coh(𝒪_X)`,
`D = R𝓗om_{𝒪_X}(-, K)` induces an anti-equivalence of `D_Coh(𝒪_X)` with itself which comes with
the canonical biduality isomorphism `id → D ∘ D`, and if `X` is quasi-compact then `D` exchanges
`D^+_Coh(𝒪_X)` and `D^-_Coh(𝒪_X)` and induces an anti-equivalence of `D^b_Coh(𝒪_X)`.

## The argument

Everything is read on the equi-universe model of the small étale ringed site of `X`, along the
derived equivalence `AlgebraicGeometry.Space.modelDerivedEquivalence` through which
`R𝓗om_{𝒪_X}` is defined. The model is covered by the étale charts with scheme `Spec R`
(`AlgebraicGeometry.Space.specChartObj_coversTop`), and the slice at each carries a full duality
chart for `K` (`AlgebraicGeometry.Space.specFullChart`: Stacks 0A89 on `Spec R`, transported to
the small étale site by Stacks 0E50 and 08JP). The general results on ringed sites with duality
charts (`AlgebraicGeometry.RingedSite.coherentDerived_of_charts`,
`AlgebraicGeometry.RingedSite.coherentDerived_dual_of_charts`,
`AlgebraicGeometry.RingedSite.isIso_derivedBiduality_of_charts`) give the first two clauses on
the model; on a quasi-compact space a single such chart covers
(`AlgebraicGeometry.Space.exists_specChartIndex_coversTop`), and the bounds are those of
`AlgebraicGeometry.RingedSite.exists_upper_bound_dual_of_charts` and
`AlgebraicGeometry.RingedSite.exists_lower_bound_dual_of_charts`. Finally `D_Coh(𝒪_X)` is read
on the model by `AlgebraicGeometry.Space.coherentDerived_iff_model` (Stacks 07UB).

## Main definitions

* `AlgebraicGeometry.Space.dualFunctor`: `D = R𝓗om_{𝒪_X}(-, K)`.
* `AlgebraicGeometry.Space.derivedBiduality`: the biduality `id ⟶ D ∘ D` of `D(𝒪_X)`, the
  biduality of the model (Stacks 0A89) conjugated by the model equivalence.

## Main results

* `AlgebraicGeometry.Space.dualizingComplex_duality`: **Stacks 0E51.**

## References

* [Stacks Project, Tag 0E51](https://stacks.math.columbia.edu/tag/0E51)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The duality functor `D = R𝓗om_{𝒪_X}(-, K)`** of `D(𝒪_X)`. -/
abbrev dualFunctor (K : DerivedModules B S hS F hF) :
    (DerivedModules B S hS F hF)ᵒᵖ ⥤ DerivedModules B S hS F hF :=
  (derivedSheafHomBifunctor B S hS F hF).flip.obj K

/-- The duality functor `R𝓗om(-, K)` of the model. -/
abbrev modelDualFunctor (K : ModelDerivedModules B S hS F hF) :
    (ModelDerivedModules B S hS F hF)ᵒᵖ ⥤ ModelDerivedModules B S hS F hF :=
  RingedSite.stdDual (smallEtaleModelRingedSite B S hS F hF) K

/-- The biduality of the model (Stacks 0A89), as a natural transformation `𝟭 ⟶ D ∘ D`. -/
abbrev modelBiduality (K : ModelDerivedModules B S hS F hF) :
    𝟭 _ ⟶ (modelDualFunctor B S hS F hF K).rightOp ⋙ modelDualFunctor B S hS F hF K :=
  RingedSite.stdBiduality (smallEtaleModelRingedSite B S hS F hF) K

/-- The duality functor of `D(𝒪_X)` is the duality functor of the model conjugated by the model
equivalence. -/
theorem dualFunctor_eq_conjDual (K : DerivedModules B S hS F hF) :
    dualFunctor B S hS F hF K = (modelDerivedEquivalence B S hS F hF).conjDual
      (modelDualFunctor B S hS F hF ((modelDerivedEquivalence B S hS F hF).functor.obj K)) :=
  rfl

/-- **The biduality `id ⟶ D ∘ D` of `D(𝒪_X)`**, `L ⟶ R𝓗om(R𝓗om(L, K), K)`: the biduality of the
model (Stacks 0A89) conjugated by the model equivalence, through which `R𝓗om_{𝒪_X}` is
defined. -/
def derivedBiduality (K : DerivedModules B S hS F hF) :
    𝟭 _ ⟶ (dualFunctor B S hS F hF K).rightOp ⋙ dualFunctor B S hS F hF K :=
  (modelDerivedEquivalence B S hS F hF).conjBiduality _
    (modelBiduality B S hS F hF ((modelDerivedEquivalence B S hS F hF).functor.obj K))

/-! ### Vanishing of cohomology sheaves along the model equivalence -/

/-- A cohomology sheaf of an object of `D(𝒪_X)` vanishes if and only if the corresponding
cohomology sheaf of its transport to the model does. -/
theorem isZero_homology_iff_model (n : ℤ) (L : DerivedModules B S hS F hF) :
    IsZero ((derivedHomology B S hS F hF n).obj L) ↔
      IsZero ((RingedSite.stdHomology (smallEtaleModelRingedSite B S hS F hF) n).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj L)) := by
  let := additive_modulesEquivModelModules_functor B S hS F hF
  let E := modulesEquivModelModules B S hS F hF
  refine ⟨fun h => (Functor.map_isZero E.functor h).of_iso
    (modelDerivedHomologyIso B S hS F hF n L), fun h => ?_⟩
  let : E.inverse.Additive := E.inverse_additive
  exact (Functor.map_isZero E.inverse
    (h.of_iso (modelDerivedHomologyIso B S hS F hF n L).symm)).of_iso (E.unitIso.app _)

/-- A cohomology sheaf of the transport back from the model vanishes when the corresponding
cohomology sheaf on the model does. -/
theorem isZero_homology_inverse (n : ℤ) (X : ModelDerivedModules B S hS F hF)
    (h : IsZero ((RingedSite.stdHomology (smallEtaleModelRingedSite B S hS F hF) n).obj X)) :
    IsZero ((derivedHomology B S hS F hF n).obj
      ((modelDerivedEquivalence B S hS F hF).inverse.obj X)) :=
  (isZero_homology_iff_model B S hS F hF n _).2 (h.of_iso
    ((RingedSite.stdHomology (smallEtaleModelRingedSite B S hS F hF) n).mapIso
      ((modelDerivedEquivalence B S hS F hF).counitIso.app X)))

/-- A vanishing range for the model dual of the transport of `L` gives one for the dual of `L`. -/
private theorem isZero_homology_dualFunctor_of_model (K L : DerivedModules B S hS F hF)
    {P Q : ℤ → Prop} (hm : ∀ n, P n → IsZero ((derivedHomology B S hS F hF n).obj L))
    (hb : (∀ n, P n → IsZero ((RingedSite.stdHomology (smallEtaleModelRingedSite B S hS F hF) n).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj L))) → ∀ j, Q j →
      IsZero ((RingedSite.stdHomology (smallEtaleModelRingedSite B S hS F hF) j).obj
        ((modelDualFunctor B S hS F hF ((modelDerivedEquivalence B S hS F hF).functor.obj K)).obj
          (op ((modelDerivedEquivalence B S hS F hF).functor.obj L))))) :
    ∀ j, Q j →
      IsZero ((derivedHomology B S hS F hF j).obj ((dualFunctor B S hS F hF K).obj (op L))) :=
  fun j hj => isZero_homology_inverse B S hS F hF j _
    (hb (fun n hn => (isZero_homology_iff_model B S hS F hF n L).1 (hm n hn)) j hj)

variable (hN : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T))

include hN in
/-- The transport back from the model of an object of `D_Coh` of the model lies in `D_Coh(𝒪_X)`. -/
theorem coherentDerived_inverse {X : ModelDerivedModules B S hS F hF}
    (h : RingedSite.coherentDerived (smallEtaleModelRingedSite B S hS F hF) X) :
    coherentDerived B S hS F hF ((modelDerivedEquivalence B S hS F hF).inverse.obj X) :=
  (coherentDerived_iff_model B S hS F hF hN _).2
    (RingedSite.coherentDerived_of_iso (smallEtaleModelRingedSite B S hS F hF)
      ((modelDerivedEquivalence B S hS F hF).counitIso.app X).symm h)

section Dualizing

variable (K : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
  (hK : IsDualizingComplexOnSpace B S hS F hF hN K)

include hK in
/-- **Clause (1) of Stacks 0E51**: a dualizing complex lies in `D_Coh(𝒪_X)`. -/
theorem coherentDerived_of_isDualizingComplexOnSpace : coherentDerived B S hS F hF K.obj :=
  (coherentDerived_iff_model B S hS F hF hN K.obj).2
    (RingedSite.coherentDerived_of_charts (smallEtaleModelRingedSite B S hS F hF)
      (specChartObj_coversTop B S hS F hF) (specFullChart B S hS F hF hN K hK))

include hK in
/-- `D = R𝓗om(-, K)` preserves `D_Coh(𝒪_X)`. -/
theorem coherentDerived_dualFunctor {L : DerivedModules B S hS F hF}
    (hL : coherentDerived B S hS F hF L) :
    coherentDerived B S hS F hF ((dualFunctor B S hS F hF K.obj).obj (op L)) :=
  coherentDerived_inverse B S hS F hF hN
    (RingedSite.coherentDerived_dual_of_charts (smallEtaleModelRingedSite B S hS F hF)
      (specChartObj_coversTop B S hS F hF) (specFullChart B S hS F hF hN K hK)
      ((coherentDerived_iff_model B S hS F hF hN L).1 hL))

include hK in
/-- The biduality `L ⟶ D(D(L))` is an isomorphism on `D_Coh(𝒪_X)`. -/
theorem isIso_derivedBiduality_app {L : DerivedModules B S hS F hF}
    (hL : coherentDerived B S hS F hF L) :
    IsIso ((derivedBiduality B S hS F hF K.obj).app L) := by
  have h₁ : IsIso ((modelBiduality B S hS F hF
      ((modelDerivedEquivalence B S hS F hF).functor.obj K.obj)).app
        ((modelDerivedEquivalence B S hS F hF).functor.obj L)) :=
    (RingedSite.isIso_stdBiduality_app_iff (smallEtaleModelRingedSite B S hS F hF) _ _).2
      (RingedSite.isIso_derivedBiduality_of_charts (smallEtaleModelRingedSite B S hS F hF)
        (specChartObj_coversTop B S hS F hF) (specFullChart B S hS F hF hN K hK)
        ((coherentDerived_iff_model B S hS F hF hN L).1 hL))
  exact (modelDerivedEquivalence B S hS F hF).isIso_conjBiduality_app
    (modelDualFunctor B S hS F hF ((modelDerivedEquivalence B S hS F hF).functor.obj K.obj))
    (modelBiduality B S hS F hF ((modelDerivedEquivalence B S hS F hF).functor.obj K.obj)) L h₁

include hK in
/-- **On a quasi-compact space the dual of an object of `D^+_Coh(𝒪_X)` is bounded above,
uniformly**: one chart with scheme `Spec R` covers, and on it `ω` has finite injective
dimension. -/
theorem exists_upper_bound_dualFunctor (hqc : IsQuasiCompactSpace B S hS F) :
    ∃ b : ℤ, ∀ (m : ℤ) (L : DerivedModules B S hS F hF), coherentDerived B S hS F hF L →
      (∀ n : ℤ, n < m → IsZero ((derivedHomology B S hS F hF n).obj L)) →
        ∀ j : ℤ, b - m < j →
          IsZero ((derivedHomology B S hS F hF j).obj
            ((dualFunctor B S hS F hF K.obj).obj (op L))) := by
  obtain ⟨k, hk⟩ := exists_specChartIndex_coversTop B S hS F hF hqc
  obtain ⟨b, hb⟩ := RingedSite.exists_upper_bound_dual_of_charts
    (smallEtaleModelRingedSite B S hS F hF) hk (fun _ => specFullChart B S hS F hF hN K hK k)
  exact ⟨b, fun m L hL hm => isZero_homology_dualFunctor_of_model B S hS F hF K.obj L hm
    (hb m _ ((coherentDerived_iff_model B S hS F hF hN L).1 hL))⟩

include hK in
/-- **On a quasi-compact space the dual of an object of `D^-_Coh(𝒪_X)` is bounded below,
uniformly**: one chart with scheme `Spec R` covers, and on it `ω` is bounded below. -/
theorem exists_lower_bound_dualFunctor (hqc : IsQuasiCompactSpace B S hS F) :
    ∃ a : ℤ, ∀ (m : ℤ) (L : DerivedModules B S hS F hF), coherentDerived B S hS F hF L →
      (∀ n : ℤ, m < n → IsZero ((derivedHomology B S hS F hF n).obj L)) →
        ∀ j : ℤ, j < a - m →
          IsZero ((derivedHomology B S hS F hF j).obj
            ((dualFunctor B S hS F hF K.obj).obj (op L))) := by
  obtain ⟨k, hk⟩ := exists_specChartIndex_coversTop B S hS F hF hqc
  obtain ⟨a, ha⟩ := RingedSite.exists_lower_bound_dual_of_charts
    (smallEtaleModelRingedSite B S hS F hF) hk (fun _ => specFullChart B S hS F hF hN K hK k)
  exact ⟨a, fun m L hL hm => isZero_homology_dualFunctor_of_model B S hS F hF K.obj L hm
    (ha m _ ((coherentDerived_iff_model B S hS F hF hN L).1 hL))⟩

end Dualizing

/-! ### Stacks 0E51 -/

/-- `D^+_Coh(𝒪_X)`. -/
def coherentDerivedPlus : ObjectProperty (DerivedModules B S hS F hF) :=
  fun L => coherentDerived B S hS F hF L ∧ IsBoundedBelow B S hS F hF L

/-- `D^-_Coh(𝒪_X)`. -/
def coherentDerivedMinus : ObjectProperty (DerivedModules B S hS F hF) :=
  fun L => coherentDerived B S hS F hF L ∧ IsBoundedAbove B S hS F hF L

/-- `D^b_Coh(𝒪_X)`. -/
def coherentDerivedBounded : ObjectProperty (DerivedModules B S hS F hF) :=
  fun L => coherentDerived B S hS F hF L ∧ IsBoundedBelow B S hS F hF L ∧
    IsBoundedAbove B S hS F hF L

/-- **Stacks 0E51.** Let `X` be a locally Noetherian algebraic space and `K` a dualizing complex
on `X` (Stacks 0E4Z). Then

* `K` is an object of `D_Coh(𝒪_X)`;
* `D = R𝓗om_{𝒪_X}(-, K)` carries `D_Coh(𝒪_X)` to itself and induces an anti-equivalence
  `D : D_Coh(𝒪_X)ᵒᵖ ≌ D_Coh(𝒪_X)`, which comes equipped with the canonical isomorphism
  `id → D ∘ D` whose components are the biduality morphisms `L ⟶ R𝓗om(R𝓗om(L, K), K)`;
* if `X` is quasi-compact, `D` carries `D^+_Coh(𝒪_X)` to `D^-_Coh(𝒪_X)` and `D^-_Coh(𝒪_X)` to
  `D^+_Coh(𝒪_X)` (and induces an anti-equivalence between them), and induces an
  anti-equivalence `D^b_Coh(𝒪_X)ᵒᵖ ≌ D^b_Coh(𝒪_X)`. -/
@[stacks 0E51]
theorem dualizingComplex_duality (K : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K) :
    coherentDerived B S hS F hF K.obj ∧
    ∃ hD : ∀ L, coherentDerived B S hS F hF L →
        coherentDerived B S hS F hF ((dualFunctor B S hS F hF K.obj).obj (op L)),
      (∃ e : (coherentDerived B S hS F hF).FullSubcategoryᵒᵖ ≌
          (coherentDerived B S hS F hF).FullSubcategory,
        e.functor = (coherentDerived B S hS F hF).lift
          ((coherentDerived B S hS F hF).ι.op ⋙ dualFunctor B S hS F hF K.obj)
          (fun L => hD _ L.unop.2)) ∧
      (∃ η : 𝟭 (coherentDerived B S hS F hF).FullSubcategory ≅
          ((coherentDerived B S hS F hF).lift
            ((coherentDerived B S hS F hF).ι.op ⋙ dualFunctor B S hS F hF K.obj)
            (fun L => hD _ L.unop.2)).rightOp ⋙
          (coherentDerived B S hS F hF).lift
            ((coherentDerived B S hS F hF).ι.op ⋙ dualFunctor B S hS F hF K.obj)
            (fun L => hD _ L.unop.2),
        ∀ L, (coherentDerived B S hS F hF).ι.map (η.hom.app L) =
          (derivedBiduality B S hS F hF K.obj).app L.1) ∧
      (IsQuasiCompactSpace B S hS F →
        (∀ L, coherentDerivedPlus B S hS F hF L →
          coherentDerivedMinus B S hS F hF ((dualFunctor B S hS F hF K.obj).obj (op L))) ∧
        (∀ L, coherentDerivedMinus B S hS F hF L →
          coherentDerivedPlus B S hS F hF ((dualFunctor B S hS F hF K.obj).obj (op L))) ∧
        (∃ (hpm : ∀ L, coherentDerivedPlus B S hS F hF L →
            coherentDerivedMinus B S hS F hF ((dualFunctor B S hS F hF K.obj).obj (op L)))
          (e : (coherentDerivedPlus B S hS F hF).FullSubcategoryᵒᵖ ≌
            (coherentDerivedMinus B S hS F hF).FullSubcategory),
          e.functor = (coherentDerivedMinus B S hS F hF).lift
            ((coherentDerivedPlus B S hS F hF).ι.op ⋙ dualFunctor B S hS F hF K.obj)
            (fun L => hpm _ L.unop.2)) ∧
        (∃ (hb : ∀ L, coherentDerivedBounded B S hS F hF L →
            coherentDerivedBounded B S hS F hF ((dualFunctor B S hS F hF K.obj).obj (op L)))
          (e : (coherentDerivedBounded B S hS F hF).FullSubcategoryᵒᵖ ≌
            (coherentDerivedBounded B S hS F hF).FullSubcategory),
          e.functor = (coherentDerivedBounded B S hS F hF).lift
            ((coherentDerivedBounded B S hS F hF).ι.op ⋙ dualFunctor B S hS F hF K.obj)
            (fun L => hb _ L.unop.2))) := by
  let D := dualFunctor B S hS F hF K.obj
  let β := derivedBiduality B S hS F hF K.obj
  have hD : ∀ L, coherentDerived B S hS F hF L →
      coherentDerived B S hS F hF (D.obj (op L)) :=
    fun L hL => coherentDerived_dualFunctor B S hS F hF hN K hK hL
  have hβ : ∀ L, coherentDerived B S hS F hF L → IsIso (β.app L) :=
    fun L hL => isIso_derivedBiduality_app B S hS F hF hN K hK hL
  refine ⟨coherentDerived_of_isDualizingComplexOnSpace B S hS F hF hN K hK, hD,
    ⟨dualityAntiEquivalence D β _ _ hD hD hβ hβ, rfl⟩,
    ⟨dualityBidualityIso D β _ hD hβ, dualityBidualityIso_hom_app D β _ hD hβ⟩, fun hqc => ?_⟩
  obtain ⟨b, hb⟩ := exists_upper_bound_dualFunctor B S hS F hF hN K hK hqc
  obtain ⟨a, ha⟩ := exists_lower_bound_dualFunctor B S hS F hF hN K hK hqc
  have hpm : ∀ L, coherentDerivedPlus B S hS F hF L →
      coherentDerivedMinus B S hS F hF (D.obj (op L)) := by
    rintro L ⟨hL, m, hm⟩
    exact ⟨hD L hL, b - m, hb m L hL hm⟩
  have hmp : ∀ L, coherentDerivedMinus B S hS F hF L →
      coherentDerivedPlus B S hS F hF (D.obj (op L)) := by
    rintro L ⟨hL, m, hm⟩
    exact ⟨hD L hL, a - m, ha m L hL hm⟩
  have hbb : ∀ L, coherentDerivedBounded B S hS F hF L →
      coherentDerivedBounded B S hS F hF (D.obj (op L)) := by
    rintro L ⟨hL, h₁, h₂⟩
    exact ⟨hD L hL, (hmp L ⟨hL, h₂⟩).2, (hpm L ⟨hL, h₁⟩).2⟩
  exact ⟨hpm, hmp,
    ⟨hpm, dualityAntiEquivalence D β _ _ hpm hmp (fun L hL => hβ L hL.1) (fun L hL => hβ L hL.1),
      rfl⟩,
    ⟨hbb, dualityAntiEquivalence D β _ _ hbb hbb (fun L hL => hβ L hL.1) (fun L hL => hβ L hL.1),
      rfl⟩⟩

end AlgebraicGeometry.Space

end
