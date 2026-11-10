module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.DegreePairingSymmetry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusEquality
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Unconditional
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierPullbackCorollaries
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionBasicOpenTrivial
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceGenericFibre
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Reduced

/-!
# Intersection numbers after contracting a component of the special fibre

In the situation of [Stacks, Tag 0C61] let `f : X ⟶ X'` contract an irreducible component `C_n`
of the special fibre, and let `C'_i = f(C_i)` for `i < n` be the components of the special fibre
of the contracted model `X'` (`Stacks.Models.RegularProperModelSituation.contractedSituation`,
`Stacks.Models.RegularProperModelSituation.contractedComponentEquiv`). This file proves part (1)
of [Stacks, Tag 0C6C]:

`(C'_i · C'_j) = (C_i · C_j) - (C_i · C_n)(C_j · C_n) / (C_n · C_n)`.

The pullback `f^{-1}C'_j` is an effective Cartier divisor on `X` supported on `C_j ∪ C_n`, and it
is `C_j + e_j C_n` for some `e_j ≥ 0`: the coefficient of `C_j` is one because `f` is an
isomorphism of local rings at the generic point of `C_j`. Since `𝒪_X(f^{-1}C'_j) ≅ f^*𝒪_{X'}(C'_j)`
and a pullback along `f` is trivial on `C_n`, which `f` contracts to a point,
`0 = (C_n · C_j) + e_j (C_n · C_n)`. On `C_i`, `i < n`, the degree of the pullback is the degree of
`𝒪_{X'}(C'_j)` on `C'_i`, because `C_i ⟶ C'_i` is an isomorphism at the generic points
([Stacks, Tag 0AYU]); so `(C'_i · C'_j) = (C_i · C_j) + e_j (C_i · C_n)`. Eliminating `e_j` gives
the formula.

## Main results

* `AlgebraicGeometry.exists_pullback_ι_iso_unit` — an invertible module is trivial near every
  point.
* `AlgebraicGeometry.invertibleCurveDegree_pullback_eq_zero_of_forall_eq` — the pullback of an
  invertible module along a morphism with one-point image has degree zero.
* `Stacks.Models.RegularProperModelSituation.contractedSpecialFiberIntersectionMatrix` —
  [Stacks, Tag 0C6C] (1).

## References

* [Stacks Project, Tag 0C6C](https://stacks.math.columbia.edu/tag/0C6C)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0BCP](https://stacks.math.columbia.edu/tag/0BCP)
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Pullbacks along morphisms with one-point image -/

/-- **An invertible module is trivial near every point.** -/
public theorem exists_pullback_ι_iso_unit {X : Scheme.{u}} (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  have : ∀ y : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace y) :=
    fun y => X.isLocalRing y
  have := hL
  obtain ⟨I, V, hV, e⟩ :=
    (Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible
      (X := X.toRingedSpace) L).exists_trivializing_cover
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ V).mp hV).exists_mem x
  obtain ⟨eU⟩ := e i
  let W : X.Opens := V i
  have eW : L.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W) := eU
  refine ⟨W, hi, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app L).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv W).app L).symm ≪≫
    (Scheme.Modules.overEquiv W).functor.mapIso eW ≪≫
    (Scheme.Modules.overFunctorEquiv W).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso W.ι

/-- **The pullback of an invertible module along a morphism with one-point image is trivial.** -/
public theorem nonempty_pullback_iso_unit_of_forall_eq {X Y : Scheme.{u}} (g : X ⟶ Y) (y : Y)
    (hg : ∀ x, g x = y) (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property L) :
    Nonempty ((Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨U, hyU, ⟨e⟩⟩ := exists_pullback_ι_iso_unit L hL y
  have hrange : Set.range g ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [hg x, Scheme.Opens.range_ι]
    exact hyU
  let g' := IsOpenImmersion.lift U.ι g hrange
  have hcomp : g' ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hrange
  exact ⟨((Scheme.Modules.pullbackCongr hcomp).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp g' U.ι).app L).symm ≪≫
    (Scheme.Modules.pullback g').mapIso e ≪≫ Scheme.Modules.pullbackUnitIso g'⟩

end AlgebraicGeometry

namespace Stacks.Models

namespace RegularProperModelSituation

open Stacks.Divisors (IsEffectiveCartierDivisor)
open Stacks.AlgebraicGeometry.ComponentDegrees (genericPointsOne genericPointsOne_eq_singleton)

variable (S : RegularProperModelSituation.{u}) {N : irreducibleComponents S.specialFiber}
  {X' : Scheme.{u}} {f : S.X ⟶ X'}

/-- The components of the special fibre of the contracted model are integral. -/
public instance isIntegral_contractedSituation_specialFiberComponentIdeal
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (W : irreducibleComponents (S.contractedSituation hf).specialFiber) :
    IsIntegral ((S.contractedSituation hf).specialFiberComponentIdeal W).subscheme :=
  (S.contractedSituation hf).toRegularModelSituation.isIntegral_specialFiberComponentIdeal W

/-! ### Multiplicities of inverse images -/

/-- The order of the inverse image of an ideal sheaf of `X'` along `C_i ≠ C_n` is its order
along `C'_i`: the contraction is an isomorphism of local rings at the generic point of `C_i`. -/
public theorem effectiveCartierMultiplicity_comap_contraction
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (I : X'.IdealSheafData) (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    effectiveCartierMultiplicity (I.comap f) (S.specialFiberComponentPrimeDivisor Z.1) =
      effectiveCartierMultiplicity I ((S.contractedSituation hf).specialFiberComponentPrimeDivisor
        (S.contractedComponentEquiv hf Z)) := by
  have := S.isIso_stalkMap_genericPoint_specialFiberComponentPrimeDivisor hf Z
  simp only [effectiveCartierMultiplicity]
  rw [length_quotient_stalk_comap_of_isIso_stalkMap,
    S.contraction_genericPoint_specialFiberComponentPrimeDivisor hf Z]

/-- **`f^{-1} C'_j = C_j + e_j C_n`.** The inverse image along the contraction of the component
`C'_j` of `X'_k` is the sum of `C_j` and a multiple of `C_n`. -/
public theorem exists_comap_contractedComponent_eq
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (W : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    IsEffectiveCartierDivisor (((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf W)).comap f) ∧
      ∃ e : ℕ, ((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf W)).comap f =
        S.specialFiberComponentIdeal W.1 * S.specialFiberComponentIdeal N ^ e := by
  classical
  let T := S.contractedSituation hf
  let D' := T.specialFiberComponentIdeal (S.contractedComponentEquiv hf W)
  have : IsIntegral S.X := S.toRegularModelSituation.isIntegral_X
  have hD' : IsEffectiveCartierDivisor D' :=
    T.isEffectiveCartierDivisor_specialFiberComponent _
  -- the inverse image is supported in the special fibre of `X`
  have hsupp : ∀ x : S.X, x ∈ (D'.comap f).supportSet → x ∈ S.specialFiberIdeal.supportSet := by
    intro x hx
    have hx' : x ∈ ((D'.comap f).support : Set S.X) := hx
    rw [Scheme.IdealSheafData.support_comap] at hx'
    have hle : T.specialFiberIdeal ≤ D' :=
      T.toRegularModelSituation.specialFiberIdeal_le_specialFiberComponentIdeal _
    have hk : f x ∈ (T.specialFiberIdeal.support : Set X') :=
      Scheme.IdealSheafData.support_antitone hle hx'
    change x ∈ (S.specialFiberIdeal.support : Set S.X)
    rw [S.specialFiberIdeal_eq_comap_contraction hf, Scheme.IdealSheafData.support_comap]
    exact hk
  have hpb : IsEffectiveCartierDivisor (D'.comap f) :=
    Stacks.Divisors.isPullbackDefined_of_isReduced f D' hD' fun ξ hξ hmem =>
      notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor S.specialFiberIdeal
        inferInstance hξ (hsupp ξ (by
          change ξ ∈ ((D'.comap f).support : Set S.X)
          rw [Scheme.IdealSheafData.support_comap]
          exact hmem))
  refine ⟨hpb, ?_⟩
  obtain ⟨a, ha⟩ := exists_finsupp_eq_prod_of_support_cover (D'.comap f) hpb
    (fun Y => S.specialFiberComponentIdeal Y)
    (fun Y => ⟨inferInstance, S.isEffectiveCartierDivisor_specialFiberComponent Y⟩)
    fun x hx => S.exists_mem_supportSet_specialFiberComponentIdeal (hsupp x hx)
  have hprod : (a.prod fun Y n => S.specialFiberComponentIdeal Y ^ n) =
      ∏ Y, S.specialFiberComponentIdeal Y ^ a Y :=
    Finsupp.prod_fintype _ _ fun _ => pow_zero _
  rw [hprod] at ha
  have hmult : ∀ Y, effectiveCartierMultiplicity (D'.comap f)
      (S.specialFiberComponentPrimeDivisor Y) = (a Y : ℤ) := by
    intro Y
    rw [ha, S.effectiveCartierMultiplicity_prod_specialFiberComponentIdeal_pow, ite_eq_left
      (Finset.mem_univ Y)]
  -- the coefficient of `C_j` is one
  have haW : a W.1 = 1 := by
    have h1 := hmult W.1
    rw [S.effectiveCartierMultiplicity_comap_contraction hf D' W] at h1
    have h2 := T.effectiveCartierMultiplicity_prod_specialFiberComponentIdeal_pow
      {S.contractedComponentEquiv hf W} (fun _ => 1) (S.contractedComponentEquiv hf W)
    rw [Finset.prod_singleton, pow_one, ite_eq_left (Finset.mem_singleton_self _)] at h2
    exact_mod_cast h1.symm.trans h2
  -- no other component than `C_j` and `C_n` occurs
  have haY : ∀ Y, Y ≠ W.1 → Y ≠ N → a Y = 0 := by
    intro Y hYW hYN
    have h1 := hmult Y
    rw [S.effectiveCartierMultiplicity_comap_contraction hf D' ⟨Y, hYN⟩,
      effectiveCartierMultiplicity_eq_zero_of_notMem_support] at h1
    · exact_mod_cast h1.symm
    · refine T.genericPoint_specialFiberComponent_notMem_support fun h => hYW ?_
      have := (S.contractedComponentEquiv hf).injective h.symm
      exact congrArg Subtype.val this
  refine ⟨a N, ?_⟩
  rw [ha, Finset.prod_eq_mul W.1 N W.2 (fun Y _ hY => by rw [haY Y hY.1 hY.2, pow_zero])
    (fun h => (h (Finset.mem_univ _)).elim) (fun h => (h (Finset.mem_univ _)).elim), haW,
    pow_one]

/-! ### Degrees of pullbacks along the contraction -/

/-- **A pullback along the contraction has degree zero on `C_n`**: the contraction carries `C_n`
to a point, near which an invertible module is trivial. -/
public theorem componentDegree_pullback_contraction_exceptional
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) (L : X'.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property L)
    (hL' : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L)) :
    componentDegree S.k (S.specialFiberComponentIdeal N) (S.specialFiberComponentToSpec N)
        (S.isProper_specialFiberComponentToSpec N)
        (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent N)
        ((Scheme.Modules.pullback f).obj L) hL' = 0 := by
  obtain ⟨z, -, -, -, hsupp, -⟩ := hf.exists_centre
  have hconst : ∀ c, ((S.specialFiberComponentIdeal N).subschemeι ≫ f) c = z := fun c =>
    (hsupp _).1 (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨c, rfl⟩)
  obtain ⟨e⟩ := nonempty_pullback_iso_unit_of_forall_eq _ z hconst L hL
  exact @invertibleCurveDegree_eq_zero_of_iso_unit S.k _ _ _ _ _ _
    (isInvertible_restrict _ _ hL') (((Scheme.Modules.pullbackComp _ f).app L) ≪≫ e)

/-- The morphism `C_i ⟶ C'_i` lies over the residue field. -/
public theorem contractedComponentMap_specialFiberComponentToSpec
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    S.contractedComponentMap hf Z ≫ (S.contractedSituation hf).specialFiberComponentToSpec
        (S.contractedComponentEquiv hf Z) = S.specialFiberComponentToSpec Z.1 := by
  let T := S.contractedSituation hf
  have h1 : S.contractedComponentMap hf Z ≫ T.specialFiberComponentι
      (S.contractedComponentEquiv hf Z) =
        S.specialFiberComponentι Z.1 ≫ S.contractionSpecialFiberMap hf := by
    have : IsClosedImmersion T.specialFiberι :=
      T.toRegularModelSituation.isClosedImmersion_specialFiberι
    apply (cancel_mono T.specialFiberι).mp
    rw [Category.assoc, T.specialFiberComponentι_specialFiberι,
      S.contractedComponentMap_subschemeι, Category.assoc,
      S.contractionSpecialFiberMap_specialFiberι, ← Category.assoc,
      S.specialFiberComponentι_specialFiberι]
  have h2 : S.contractionSpecialFiberMap hf ≫ T.specialFiberToSpec = S.specialFiberToSpec := by
    simp only [contractionSpecialFiberMap, pullback.map]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  change _ ≫ T.specialFiberComponentι _ ≫ T.specialFiberToSpec =
    S.specialFiberComponentι _ ≫ S.specialFiberToSpec
  rw [← Category.assoc, h1, Category.assoc, h2]

/-- The morphism `C_i ⟶ C'_i` carries the generic point to the generic point. -/
public theorem contractedComponentMap_genericPoint
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    S.contractedComponentMap hf Z (genericPoint (S.specialFiberComponentIdeal Z.1).subscheme) =
      genericPoint ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).subscheme := by
  apply ((S.contractedSituation hf).specialFiberComponentIdeal
    (S.contractedComponentEquiv hf Z)).subschemeι.isClosedEmbedding.injective
  have h := congrArg (fun φ => φ (genericPoint (S.specialFiberComponentIdeal Z.1).subscheme))
    (S.contractedComponentMap_subschemeι hf Z)
  exact h.trans (S.contraction_genericPoint_specialFiberComponentPrimeDivisor hf Z)

/-- The morphism `C_i ⟶ C'_i` is an isomorphism of local rings at the generic point: the local
ring of `C'_i` there is a field, and the contraction is an isomorphism of local rings of the
ambient models. -/
public theorem isIso_stalkMap_contractedComponentMap
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    IsIso ((S.contractedComponentMap hf Z).stalkMap
      (genericPoint (S.specialFiberComponentIdeal Z.1).subscheme)) := by
  let C' := ((S.contractedSituation hf).specialFiberComponentIdeal
    (S.contractedComponentEquiv hf Z)).subscheme
  let η := genericPoint (S.specialFiberComponentIdeal Z.1).subscheme
  have hgen := S.contractedComponentMap_genericPoint hf Z
  have := S.isIso_stalkMap_genericPoint_specialFiberComponentPrimeDivisor hf Z
  have : IsIso (f.stalkMap ((S.specialFiberComponentIdeal Z.1).subschemeι η)) := this
  have hsurj : Function.Surjective ((S.contractedComponentMap hf Z ≫
      ((S.contractedSituation hf).specialFiberComponentIdeal
        (S.contractedComponentEquiv hf Z)).subschemeι).stalkMap η).hom := by
    rw [S.contractedComponentMap_subschemeι hf Z, Scheme.Hom.stalkMap_comp]
    exact (SurjectiveOnStalks.stalkMap_surjective _ _).comp
      (ConcreteCategory.bijective_of_isIso (f.stalkMap _)).2
  rw [Scheme.Hom.stalkMap_comp] at hsurj
  have hsurj' : Function.Surjective ((S.contractedComponentMap hf Z).stalkMap η).hom :=
    Function.Surjective.of_comp hsurj
  have hinj : Function.Injective ((S.contractedComponentMap hf Z).stalkMap η).hom := by
    let : IsSimpleRing (C'.presheaf.stalk (S.contractedComponentMap hf Z η)) := by
      rw [hgen]
      exact inferInstanceAs (IsSimpleRing C'.functionField)
    exact RingHom.injective _
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj'⟩

/-- **The degree of a pullback along the contraction on `C_i ≠ C_n` is the degree on `C'_i`**
([Stacks, Tag 0AYU]): the morphism `C_i ⟶ C'_i` is an isomorphism at the generic points. -/
public theorem componentDegree_pullback_contraction
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    (Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) (L : X'.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property L)
    (hL' : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L)) :
    componentDegree S.k (S.specialFiberComponentIdeal Z.1) (S.specialFiberComponentToSpec Z.1)
        (S.isProper_specialFiberComponentToSpec Z.1)
        (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z.1)
        ((Scheme.Modules.pullback f).obj L) hL' =
      componentDegree S.k ((S.contractedSituation hf).specialFiberComponentIdeal
          (S.contractedComponentEquiv hf Z))
        ((S.contractedSituation hf).specialFiberComponentToSpec (S.contractedComponentEquiv hf Z))
        ((S.contractedSituation hf).isProper_specialFiberComponentToSpec _)
        (RegularModelSituation.topologicalKrullDim_specialFiberComponent
          (S.contractedSituation hf).toRegularModelSituation _) L hL := by
  let T := S.contractedSituation hf
  let W := S.contractedComponentEquiv hf Z
  let q := S.contractedComponentMap hf Z
  let ι := (S.specialFiberComponentIdeal Z.1).subschemeι
  let ι' := (T.specialFiberComponentIdeal W).subschemeι
  let C := (S.specialFiberComponentIdeal Z.1).subscheme
  let C' := (T.specialFiberComponentIdeal W).subscheme
  let E := (Scheme.Modules.pullback ι').obj L
  have := hL
  have hEs : Stacks.SheafOfModules.IsInvertible C'.presheaf
      (structureSheafRing C'.toRingedSpace).property E := Stacks.Modules.isInvertible_pullback ι' L
  have := hEs
  have hqEs : Stacks.SheafOfModules.IsInvertible C.presheaf
      (structureSheafRing C.toRingedSpace).property ((Scheme.Modules.pullback q).obj E) :=
    Stacks.Modules.isInvertible_pullback q E
  have hE : AlgebraicGeometry.SheafOfModules.IsInvertible C'.presheaf C'.ringCatSheaf.2 E :=
    isInvertible_restrict _ L hL
  have : IsIntegral C := inferInstance
  have : IsIntegral C' := inferInstance
  let e : (Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback f).obj L) ≅
      (Scheme.Modules.pullback q).obj E :=
    (Scheme.Modules.pullbackComp ι f).app L ≪≫
      (Scheme.Modules.pullbackCongr (S.contractedComponentMap_subschemeι hf Z).symm).app L ≪≫
      ((Scheme.Modules.pullbackComp q ι').app L).symm
  have hC :=
    genericPointsOne_eq_singleton C (S.topologicalKrullDim_specialFiberComponent_eq_one Z.1)
  have hbij : Set.BijOn q (genericPointsOne C) (genericPointsOne C') := by
    rw [hC,
      genericPointsOne_eq_singleton C' (T.topologicalKrullDim_specialFiberComponent_eq_one W)]
    exact Set.bijOn_singleton.mpr (S.contractedComponentMap_genericPoint hf Z)
  have hstalk : ∀ c ∈ genericPointsOne C, IsIso (q.stalkMap c) := by
    intro c hc
    rw [hC, Set.mem_singleton_iff] at hc
    subst hc
    exact S.isIso_stalkMap_contractedComponentMap hf Z
  have : IsProper (T.specialFiberComponentToSpec W) := T.isProper_specialFiberComponentToSpec W
  change @invertibleCurveDegree S.k _ C (S.specialFiberComponentToSpec Z.1) _ _
      ((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback f).obj L))
      (isInvertible_restrict _ _ hL') =
    @invertibleCurveDegree S.k _ C' (T.specialFiberComponentToSpec W) _ _ E hE
  rw [invertibleCurveDegree_eq_of_iso S.k _ _ e, invertibleCurveDegree_eq_curveDegree,
    invertibleCurveDegree_eq_curveDegree]
  exact curveDegree_pullback_eq_of_bijOn_genericPointsOne_of_isProper S.k _ _ _ _ q
    (S.contractedComponentMap_specialFiberComponentToSpec hf Z) hbij E 1 hstalk

/-! ### The intersection numbers of the contracted model -/

/-- **The two relations of the proof of [Stacks, Tag 0C6C] (1).** Writing
`f^{-1}C'_j = C_j + e_j C_n`, the degree of `f^*𝒪_{X'}(C'_j)` on `C_i`, `i < n`, gives
`(C'_i · C'_j) = (C_i · C_j) + e_j (C_i · C_n)`, and on `C_n` it gives
`0 = (C_n · C_j) + e_j (C_n · C_n)`. -/
public theorem exists_contractedSpecialFiberIntersectionMatrix_relations
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    [DecidableEq (irreducibleComponents S.specialFiber)]
    [DecidableEq (irreducibleComponents (S.contractedSituation hf).specialFiber)]
    (W : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    ∃ e : ℕ,
      (∀ Z : {Z : irreducibleComponents S.specialFiber // Z ≠ N},
        (S.contractedSituation hf).specialFiberIntersectionMatrix (S.contractedComponentEquiv hf Z)
            (S.contractedComponentEquiv hf W) =
          S.specialFiberIntersectionMatrix Z.1 W.1 + e * S.specialFiberIntersectionMatrix Z.1 N) ∧
        S.specialFiberIntersectionMatrix N W.1 + e * S.specialFiberIntersectionMatrix N N = 0 := by
  let T := S.contractedSituation hf
  let D' := T.specialFiberComponentIdeal (S.contractedComponentEquiv hf W)
  have hD' : IsEffectiveCartierDivisor D' := T.isEffectiveCartierDivisor_specialFiberComponent _
  obtain ⟨hpb, e, he⟩ := S.exists_comap_contractedComponent_eq hf W
  have : Stacks.Divisors.IsPullbackDefined f D' := hpb
  let L := Stacks.Divisors.invertibleSheaf' D'
  have hL : Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property L :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf D'
  have := hL
  have hL' : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
    Stacks.Modules.isInvertible_pullback f L
  have : IsEffectiveCartierDivisor (S.specialFiberComponentIdeal W.1) :=
    S.isEffectiveCartierDivisor_specialFiberComponent W.1
  have : IsEffectiveCartierDivisor (S.specialFiberComponentIdeal N) :=
    S.isEffectiveCartierDivisor_specialFiberComponent N
  have : IsEffectiveCartierDivisor (S.specialFiberComponentIdeal N ^ e) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow
      (S.isEffectiveCartierDivisor_specialFiberComponent N) e
  -- the degree of the pullback on every component of `X_k`
  have hdeg : ∀ Y : irreducibleComponents S.specialFiber,
      componentDegree S.k (S.specialFiberComponentIdeal Y) (S.specialFiberComponentToSpec Y)
          (S.isProper_specialFiberComponentToSpec Y)
          (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y)
          ((Scheme.Modules.pullback f).obj L) hL' =
        S.specialFiberIntersectionMatrix Y W.1 + e * S.specialFiberIntersectionMatrix Y N := by
    intro Y
    have hC := fun Y => S.isEffectiveCartierDivisor_specialFiberComponent Y
    let C := fun Y => S.specialFiberComponentIdeal Y
    let g := fun Y => S.specialFiberComponentToSpec Y
    let hg := fun Y => S.isProper_specialFiberComponentToSpec Y
    let hdim := fun Y => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Y
    rw [componentDegree_eq_of_iso S.k _ _ _ _ _ _ hL'
      (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _ hpb)
      (Stacks.Divisors.invertibleSheafPullbackIso f D'),
      componentDegree_invertibleSheaf_congr S C g hg hdim Y he _
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _ (hC W.1)
            (Stacks.Divisors.isEffectiveCartierDivisor_pow (hC N) e))),
      componentDegree_invertibleSheaf_mul S C g hg hdim Y _ _ _
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _ (hC W.1))
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf _),
      componentDegree_invertibleSheaf_pow S C g hg hdim Y _ e _
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _ (hC N)),
      S.specialFiberIntersectionMatrix_eq_componentDegree Y W.1,
      S.specialFiberIntersectionMatrix_eq_componentDegree Y N]
  refine ⟨e, fun Z => ?_, ?_⟩
  · rw [← hdeg Z.1, S.componentDegree_pullback_contraction hf Z L hL hL',
      T.specialFiberIntersectionMatrix_eq_componentDegree]
  · rw [← hdeg N]
    exact S.componentDegree_pullback_contraction_exceptional hf L hL hL'

/-- Elimination of the coefficient `e_j` from the two relations. -/
private theorem eq_sub_mul_div_of_relations {a b c d t m n : ℚ} (ht : t = a + m * b)
    (h1 : c + m * d = 0) (h2 : b + n * d = 0) : t = a - b * c / d := by
  by_cases hd : d = 0
  · subst hd
    simp only [mul_zero, add_zero] at h1 h2
    subst h1 h2
    simpa using ht
  · have hm : m = -c / d := by field_simp; linarith
    rw [ht, hm]
    field_simp
    ring

/-- **Stacks Project, Tag 0C6C, part (1).** Let `f : X ⟶ X'` contract the component `C_n` of the
special fibre of a regular proper model, and let `C'_i = f(C_i)`, `i < n`, be the components of
the special fibre of the contracted model. Then for `i, j < n`

`(C'_i · C'_j) = (C_i · C_j) - (C_i · C_n)(C_j · C_n) / (C_n · C_n)`. -/
@[stacks 0C6C "part (1): (C'_i · C'_j) = (C_i · C_j) - (C_i · C_n)(C_j · C_n)/(C_n · C_n)"]
public theorem contractedSpecialFiberIntersectionMatrix
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f)
    [DecidableEq (irreducibleComponents S.specialFiber)]
    [DecidableEq (irreducibleComponents (S.contractedSituation hf).specialFiber)]
    (Z W : {Z : irreducibleComponents S.specialFiber // Z ≠ N}) :
    ((S.contractedSituation hf).specialFiberIntersectionMatrix (S.contractedComponentEquiv hf Z)
        (S.contractedComponentEquiv hf W) : ℚ) =
      S.specialFiberIntersectionMatrix Z.1 W.1 -
        S.specialFiberIntersectionMatrix Z.1 N * S.specialFiberIntersectionMatrix W.1 N /
          S.specialFiberIntersectionMatrix N N := by
  obtain ⟨m, hT, hW⟩ := S.exists_contractedSpecialFiberIntersectionMatrix_relations hf W
  obtain ⟨n, -, hZ⟩ := S.exists_contractedSpecialFiberIntersectionMatrix_relations hf Z
  rw [S.specialFiberIntersectionMatrix_comm N W.1] at hW
  rw [S.specialFiberIntersectionMatrix_comm N Z.1] at hZ
  refine eq_sub_mul_div_of_relations (m := (m : ℚ)) (n := (n : ℚ)) ?_ ?_ ?_
  · exact_mod_cast hT Z
  · exact_mod_cast hW
  · exact_mod_cast hZ

end RegularProperModelSituation

end Stacks.Models

end
