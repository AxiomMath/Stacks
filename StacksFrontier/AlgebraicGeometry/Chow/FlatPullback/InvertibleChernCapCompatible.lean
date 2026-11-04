module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.IsoComponentEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapComponent

/-!
# The component case of Stacks 02SS for an invertible module

Let `X` and `X'` be schemes locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, let `f : X' ⟶ X` be flat of relative dimension `r` and let `L` be an invertible
module on `X`. Over every integral component `W = closure {x}` of `X` of delta-dimension `k + 1`
the two cycles of [Stacks, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS) attached to the
component rules of `L` and of `f^*L` differ by a cycle rationally equivalent to zero on the
inverse image `f^{-1}(W)`; this is
`Stacks.Chow.FirstChernCapRationallyCompatibleWithFlatPullback` for those rules.

## Main results

* `Stacks.Chow.firstChernCapRationallyCompatibleWithFlatPullback_invertible` — the component case
  of Stacks 02SS for the component rules of `L` and of `f^*L`.
* `Stacks.Chow.finsum_fibre_flatPullbackWeight_eq_components` — **Stacks 02R8**, a sum over a
  fibre weighted by the flat pullback multiplicity read as a sum over the components of the
  inverse image of the closure of the point.

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Comparing two differently graded cycles on coefficients -/

private theorem properPushforward_coeff_eq (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : A ⟶ B)
    [IsClosedImmersion j] (hj : j ≫ sB = sA) (m n : ℤ) (c : CycleGroup C sA m)
    (d : CycleGroup C sA n) (hcd : ∀ w, c.1 w = d.1 w) (z : B) :
    (properPushforward C sA sB j hj m c).1 z = (properPushforward C sA sB j hj n d).1 z := by
  rw [properPushforward_apply_of_isClosedImmersion, properPushforward_apply_of_isClosedImmersion]
  exact finsum_mem_congr rfl fun w _ ↦ hcd w

private theorem flatPullback_coeff_eq (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (h : A ⟶ B)
    [LocallyOfFiniteType h] [Flat h] (hb : h ≫ sB = sA) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) {m n : ℤ} (hmn : m = n)
    (c : CycleGroup C sB m) (d : CycleGroup C sB n) (hcd : ∀ w, c.1 w = d.1 w) (z : A) :
    (flatPullback C sA sB h hb r hr m c).1 z = (flatPullback C sA sB h hb r hr n d).1 z := by
  rw [flatPullback_apply, flatPullback_apply, hcd, hmn]

private theorem properPushforward_zsmul_sub_apply (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (j : A ⟶ B)
    [IsProper j] (hj : j ≫ sB = sA) (m : ℤ) (n : ℤ) (c d : CycleGroup C sA m) (z : B) :
    (properPushforward C sA sB j hj m (n • (c - d))).1 z =
      n * (properPushforward C sA sB j hj m c).1 z -
        n * (properPushforward C sA sB j hj m d).1 z := by
  rw [← properPushforwardHom_apply, map_zsmul, properPushforwardHom_apply,
    properPushforward_sub, ← mul_sub]
  rfl

/-! ### The irreducible components of a locally Noetherian scheme as an index set -/

private def integralComponentOf {Z : Scheme.{u}} (V : irreducibleComponents Z) :
    Z.IdealSheafData := integralComponentAt V.2.1.genericPoint

/-- The supports of the integral closed subschemes on the irreducible components of a locally
Noetherian scheme form a locally finite family. -/
public theorem locallyFinite_support_integralComponentAt_genericPoint {Z : Scheme.{u}}
    [IsLocallyNoetherian Z] :
    LocallyFinite fun V : irreducibleComponents Z ↦
      ((integralComponentAt V.2.1.genericPoint).support : Set Z) := by
  have hcomp : LocallyFinite fun V : irreducibleComponents Z ↦ (V : Set Z) := by
    simpa using AlgebraicGeometry.locallyFinite_irreducibleComponents_image (𝟙 Z)
  exact hcomp.subset fun V ↦ by rw [coe_support_integralComponentAt_genericPoint]

/-- Distinct irreducible components of a scheme have distinct generic points. -/
public theorem injective_genericPoint_irreducibleComponents {Z : Scheme.{u}} :
    Function.Injective fun V : irreducibleComponents Z ↦ V.2.1.genericPoint := by
  intro V V' h
  have h' : V.2.1.genericPoint = V'.2.1.genericPoint := h
  refine Subtype.ext ?_
  rw [← coe_support_integralComponentAt_genericPoint V,
    ← coe_support_integralComponentAt_genericPoint V']
  exact congrArg (fun z : Z ↦ (((integralComponentAt z).support : Closeds Z) : Set Z)) h'

private theorem rationallyEquivalentToZero_of_componentSum (C : ChowSituation.{u})
    {Z : Scheme.{u}} (q : Z ⟶ C.S) [LocallyOfFiniteType q] [IsLocallyNoetherian Z] (j : ℤ)
    (a : ∀ V : irreducibleComponents Z,
      CycleGroup C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ q) j)
    (ha : ∀ V : irreducibleComponents Z, IsRationallyEquivalentToZero C
      ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ q) j (a V))
    {α : CycleGroup C q j}
    (hα : ∀ z : Z, α.1 z = ∑ᶠ V : irreducibleComponents Z,
      (properPushforward C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ q) q
        (integralComponentAt V.2.1.genericPoint).subschemeι rfl j (a V)).1 z) :
    IsRationallyEquivalentToZero C q j α :=
  rationallyEquivalentToZero_finsum_of_closedSupports C q j integralComponentOf
    locallyFinite_support_integralComponentAt_genericPoint a ha hα

private theorem hasFiniteSupport_componentCoeff (C : ChowSituation.{u}) {Z : Scheme.{u}}
    (q : Z ⟶ C.S) [LocallyOfFiniteType q] [IsLocallyNoetherian Z] (j : ℤ)
    (m : irreducibleComponents Z → ℤ)
    (c : ∀ V : irreducibleComponents Z,
      CycleGroup C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ q) j) (z : Z) :
    Function.HasFiniteSupport fun V ↦ m V *
      (properPushforward C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ q) q
        (integralComponentAt V.2.1.genericPoint).subschemeι rfl j (c V)).1 z := by
  refine (finite_irreducibleComponents_mem z).subset fun V hV ↦ ?_
  show z ∈ (V : Set Z)
  by_contra hcon
  refine hV ?_
  have h0 : z ∉ Set.range (integralComponentAt V.2.1.genericPoint).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt_genericPoint]
    exact hcon
  show m V * _ = 0
  rw [properPushforward_apply_of_notMem_range C _ q _ rfl _ (c V) h0, mul_zero]

/-! ### The generic points of the components of an inverse image -/

private theorem base_genericPoint_comap_integralComponentAt {X' X : Scheme.{u}} (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (x : X)
    (V : irreducibleComponents ((integralComponentAt x).comap f).subscheme) :
    f.base (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) = x := by
  have := isIntegral_integralComponentAt x
  rw [base_genericPoint_irreducibleComponents_comap f (integralComponentAt x) V]
  exact subschemeι_genericPoint_integralComponentAt x

/-- **Stacks 02R8.** A sum over the fibre `f^{-1}(x)` weighted by the flat pullback multiplicity
is the sum over the irreducible components of `f^{-1}(closure {x})`, evaluated at their generic
points. -/
theorem finsum_fibre_flatPullbackWeight_eq_components (C : ChowSituation.{u})
    {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (x : X) (j : ℤ) (F : X' → ℤ) :
    ∑ᶠ x' ∈ f.base ⁻¹' {x}, flatPullbackWeight C sX' f j x' * F x' =
      ∑ᶠ V : irreducibleComponents ((integralComponentAt x).comap f).subscheme,
        flatPullbackWeight C sX' f j
            (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) *
          F (((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) := by
  have hinj : Function.Injective
      fun V : irreducibleComponents ((integralComponentAt x).comap f).subscheme ↦
        ((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint := fun V V' h ↦
    injective_genericPoint_irreducibleComponents
      (((integralComponentAt x).comap f).subschemeι.isClosedEmbedding.injective h)
  rw [finsum_mem_inter_support_eq' _ (f.base ⁻¹' {x})
      (Set.range fun V : irreducibleComponents ((integralComponentAt x).comap f).subscheme ↦
        ((integralComponentAt x).comap f).subschemeι.base V.2.1.genericPoint) ?_,
    finsum_mem_range hinj]
  intro x' hx'
  refine ⟨fun hmem ↦ ?_, fun hmem ↦ ?_⟩
  · exact exists_irreducibleComponents_of_flatPullbackWeight_ne_zero C sX' f x j (by exact hmem)
      (left_ne_zero_of_mul hx')
  · obtain ⟨V, hV⟩ := hmem
    exact hV ▸ base_genericPoint_comap_integralComponentAt f x V

/-! ### Stacks 0EPJ with the summands regraded -/

private theorem flatPullback_chernComponentCycle_coeff (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] [IsIntegral B] [IsLocallyNoetherian B] (h : A ⟶ B)
    [LocallyOfFiniteType h] [Flat h] (hb : h ≫ sB = sA) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (k : ℤ) (N : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 N]
    (hB : schemeDeltaDimension C sB = ((k + 1 : ℤ) : EInt))
    (s : N.presheaf.stalk (genericPoint B)) (hs : s ≠ 0)
    (c : ∀ V : irreducibleComponents A,
      CycleGroup C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ sA) (k + (r : ℤ)))
    (hc : ∀ (V : irreducibleComponents A)
      (w : (integralComponentAt V.2.1.genericPoint).subscheme), (c V).1 w =
        letI := isIntegral_integralComponentAt V.2.1.genericPoint
        letI : IsLocallyNoetherian (integralComponentAt V.2.1.genericPoint).subscheme :=
          LocallyOfFiniteType.isLocallyNoetherian
            ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ sA)
        letI := isDominant_subschemeι_integralComponentAt_comp h V
        letI := isInvertible_presheaf_pullback N
          ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ h)
        ((meromorphicDivisorCycleOfInvertible C
          ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ sA)
          (schemeDeltaDimension_integralComponentAt_comp C sA sB h hb r hr hB V)
          ((Scheme.Modules.pullback
            ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ h)).obj N)
          (genericStalkPullback ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ h) N
            s)).val).1 w) (z : A) :
    (flatPullback C sA sB h hb r hr k
        (chernComponentCycle C sB hB (isTrivializedNear_of_isInvertible N) s)).1 z =
      ∑ᶠ V : irreducibleComponents A,
        (cycleAssociatedToClosedSubscheme C sA (𝟙 A) (k + 1 + (r : ℤ))).1 V.2.1.genericPoint *
          (properPushforward C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ sA) sA
            (integralComponentAt V.2.1.genericPoint).subschemeι rfl (k + (r : ℤ)) (c V)).1 z := by
  rw [flatPullback_coeff_eq C sA sB h hb r hr (show k = k + 1 - 1 by ring) _
      (meromorphicDivisorCycleOfInvertible C sB hB N s).val (fun w ↦ rfl) z,
    flatPullback_meromorphicDivisor_eq_sum_components C sA sB h hb r hr hB N s hs z]
  refine finsum_congr fun V ↦ ?_
  have := isIntegral_integralComponentAt V.2.1.genericPoint
  have : IsLocallyNoetherian (integralComponentAt V.2.1.genericPoint).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ sA)
  have := isDominant_subschemeι_integralComponentAt_comp h V
  have := isInvertible_presheaf_pullback N
    ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ h)
  exact congrArg _ (properPushforward_coeff_eq C _ sA _ rfl _ _ _ _ (hc V) z).symm

/-! ### The two cycles on one component of the inverse image -/

private theorem exists_componentCycles (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (r : ℕ) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (W : X.IdealSheafData) [IsIntegral W.subscheme] [IsLocallyNoetherian W.subscheme]
    (W' : X'.IdealSheafData) (g : W'.subscheme ⟶ W.subscheme) [Flat g]
    (hsq : g ≫ W.subschemeι = W'.subschemeι ≫ f)
    (hDimRaw : ∀ V : irreducibleComponents W'.subscheme,
      schemeDeltaDimension C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
        (W'.subschemeι ≫ (f ≫ p))) = ((k + 1 + (r : ℤ) : ℤ) : EInt))
    (s : ((Scheme.Modules.pullback W.subschemeι).obj L).presheaf.stalk (genericPoint W.subscheme))
    (hs : s ≠ 0) (V : irreducibleComponents W'.subscheme) :
    ∃ cc dd : CycleGroup C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
        (W'.subschemeι ≫ (f ≫ p))) (k + (r : ℤ)),
      IsRationallyEquivalentToZero C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
          (W'.subschemeι ≫ (f ≫ p))) (k + (r : ℤ)) (dd - cc) ∧
      (∀ w : (integralComponentAt V.2.1.genericPoint).subscheme, cc.1 w =
        letI := isIntegral_integralComponentAt V.2.1.genericPoint
        letI : IsLocallyNoetherian (integralComponentAt V.2.1.genericPoint).subscheme :=
          LocallyOfFiniteType.isLocallyNoetherian
            ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ (W'.subschemeι ≫ (f ≫ p)))
        letI := isDominant_subschemeι_integralComponentAt_comp g V
        letI := isInvertible_presheaf_modulePullback L W.subschemeι
        letI := isInvertible_presheaf_pullback ((Scheme.Modules.pullback W.subschemeι).obj L)
          ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ g)
        ((meromorphicDivisorCycleOfInvertible C
          ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
            (W'.subschemeι ≫ (f ≫ p))) (hDimRaw V)
          ((Scheme.Modules.pullback
            ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ g)).obj
            ((Scheme.Modules.pullback W.subschemeι).obj L))
          (genericStalkPullback ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ g)
            ((Scheme.Modules.pullback W.subschemeι).obj L) s)).val).1 w) ∧
      ∀ z : W'.subscheme,
        (properPushforward C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
            (W'.subschemeι ≫ (f ≫ p))) (W'.subschemeι ≫ (f ≫ p))
            (integralComponentAt V.2.1.genericPoint).subschemeι rfl (k + (r : ℤ)) dd).1 z =
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
            (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L))
            (W'.subschemeι.base V.2.1.genericPoint)).1 (W'.subschemeι.base z) := by
  obtain ⟨eV, heV⟩ :=
    exists_iso_integralComponentAt_comp W'.subschemeι V.2.1.genericPoint
  have hTVint := isIntegral_integralComponentAt V.2.1.genericPoint
  have hVVint := isIntegral_integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)
  have hTVnoeth : IsLocallyNoetherian (integralComponentAt V.2.1.genericPoint).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ (W'.subschemeι ≫ (f ≫ p)))
  have hVVnoeth : IsLocallyNoetherian
      (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
  have hdom := isDominant_subschemeι_integralComponentAt_comp g V
  have hMinv := isInvertible_presheaf_modulePullback L W.subschemeι
  have hMVinv := isInvertible_presheaf_pullback ((Scheme.Modules.pullback W.subschemeι).obj L)
    ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ g)
  have hM1inv := isInvertible_presheaf_modulePullback ((Scheme.Modules.pullback f).obj L)
    (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι
  have hcompV : eV.hom ≫
      ((integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι ≫ (f ≫ p)) =
      (integralComponentAt V.2.1.genericPoint).subschemeι ≫ (W'.subschemeι ≫ (f ≫ p)) := by
    simp only [← Category.assoc, heV]
  have hDimTV : schemeDeltaDimension C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
      (W'.subschemeι ≫ (f ≫ p))) = ((k + (r : ℤ) + 1 : ℤ) : EInt) :=
    (hDimRaw V).trans (congrArg (fun n : ℤ ↦ (n : EInt)) (by ring))
  have hDimVV : schemeDeltaDimension C
      ((integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
      = ((k + (r : ℤ) + 1 : ℤ) : EInt) :=
    (schemeDeltaDimension_of_iso C _ _ eV hcompV).trans hDimTV
  have hinvV : eV.inv ≫ ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
      (W'.subschemeι ≫ (f ≫ p))) =
      (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι ≫ (f ≫ p) := by
    rw [← hcompV, Iso.inv_hom_id_assoc]
  have hiotaV : eV.inv ≫ ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ W'.subschemeι) =
      (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι := by
    rw [← heV, Iso.inv_hom_id_assoc]
  refine ⟨chernComponentCycle C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
      (W'.subschemeι ≫ (f ≫ p))) hDimTV (isTrivializedNear_of_isInvertible _)
      (genericStalkPullback ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ g)
        ((Scheme.Modules.pullback W.subschemeι).obj L) s),
    properPushforward C
      ((integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
      ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ (W'.subschemeι ≫ (f ≫ p)))
      eV.inv hinvV (k + (r : ℤ))
      (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L)
        (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)) hVVint hDimVV),
    ?_, fun w ↦ rfl, ?_⟩
  · refine rationallyEquivalentToZero_properPushforward_sub_chernComponentCycle C
      ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ (W'.subschemeι ≫ (f ≫ p)))
      ((integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
      eV hcompV (k + (r : ℤ)) hDimTV hDimVV _ _
      (pullbackCompIso eV.hom
          (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι
          (integralComponentAt V.2.1.genericPoint).subschemeι W'.subschemeι heV
          ((Scheme.Modules.pullback f).obj L) ≪≫
        (Scheme.Modules.pullback (integralComponentAt V.2.1.genericPoint).subschemeι).mapIso
          (pullbackCompIso W'.subschemeι f g W.subschemeι hsq.symm L) ≪≫
        (Scheme.Modules.pullbackComp
          (integralComponentAt V.2.1.genericPoint).subschemeι g).app
          ((Scheme.Modules.pullback W.subschemeι).obj L))
      (genericStalkPullback_ne_zero
        ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ g)
        (isTrivializedNear_of_isInvertible ((Scheme.Modules.pullback W.subschemeι).obj L)) hs) _
      (fun t ht ↦ mk_chernComponentCycleRule_eq C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L)
        (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint))
        (fun W'' _ y ↦
          have := isInvertible_presheaf_modulePullback
            ((Scheme.Modules.pullback f).obj L) W''.subschemeι
          isTrivializedNear_of_isInvertible _ y)
        hDimVV ht)
  · intro z
    rw [show firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
          (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L))
          (W'.subschemeι.base V.2.1.genericPoint) =
        firstChernComponentCycle C (f ≫ p) (k + (r : ℤ))
          (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L))
          (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)) hVVint hDimVV from by
      rw [← firstChernComponentCycleAt_genericPointOf C (f ≫ p) (k + (r : ℤ))
        (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
          ((Scheme.Modules.pullback f).obj L))
        (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)) hVVint hDimVV,
        genericPointOf_integralComponentAt]]
    rw [show firstChernComponentCycle C (f ≫ p) (k + (r : ℤ))
          (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L))
          (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)) hVVint hDimVV =
        properPushforward C (W'.subschemeι ≫ (f ≫ p)) (f ≫ p) W'.subschemeι rfl (k + (r : ℤ))
          (properPushforward C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
              (W'.subschemeι ≫ (f ≫ p))) (W'.subschemeι ≫ (f ≫ p))
            (integralComponentAt V.2.1.genericPoint).subschemeι rfl (k + (r : ℤ))
            (properPushforward C
              ((integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι ≫
                (f ≫ p))
              ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
                (W'.subschemeι ≫ (f ≫ p))) eV.inv hinvV (k + (r : ℤ))
              (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
                ((Scheme.Modules.pullback f).obj L)
                (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)) hVVint
                hDimVV))) from by
      rw [properPushforward_properPushforward, properPushforward_properPushforward]
      exact congrFun (properPushforward_congr C
        ((integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι ≫ (f ≫ p))
        (f ≫ p) (integralComponentAt (W'.subschemeι.base V.2.1.genericPoint)).subschemeι
        (eV.inv ≫ ((integralComponentAt V.2.1.genericPoint).subschemeι ≫ W'.subschemeι))
        hiotaV.symm rfl (by rw [hiotaV]) (k + (r : ℤ))) _]
    rw [properPushforward_apply_image_of_isClosedImmersion]

/-! ### Summing the component equivalences -/

private theorem rationallyEquivalentToZero_sub_of_components (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (r : ℕ) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (W : X.IdealSheafData) [IsIntegral W.subscheme] [IsLocallyNoetherian W.subscheme]
    (W' : X'.IdealSheafData) [IsLocallyNoetherian W'.subscheme]
    (g : W'.subscheme ⟶ W.subscheme) [LocallyOfFiniteType g] [Flat g]
    (hsq : g ≫ W.subschemeι = W'.subschemeι ≫ f)
    (hgb : g ≫ (W.subschemeι ≫ p) = W'.subschemeι ≫ (f ≫ p))
    (hr : AlgebraicGeometry.RelativeDimension g r)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (s : ((Scheme.Modules.pullback W.subschemeι).obj L).presheaf.stalk (genericPoint W.subscheme))
    (hs : s ≠ 0) (x : X) (D : CycleGroup C (f ≫ p) (k + (r : ℤ)))
    (hD : ∀ y' : X', D.1 y' = ∑ᶠ x' ∈ f.base ⁻¹' {x},
      flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
        (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
          (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L)) x').1 y')
    (hreindex : ∀ F : X' → ℤ,
      ∑ᶠ x' ∈ f.base ⁻¹' {x}, flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' * F x' =
        ∑ᶠ V : irreducibleComponents W'.subscheme,
          flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ))
              (W'.subschemeι.base V.2.1.genericPoint) *
            F (W'.subschemeι.base V.2.1.genericPoint))
    (hwt : ∀ V : irreducibleComponents W'.subscheme,
      flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ))
          (W'.subschemeι.base V.2.1.genericPoint) =
        (cycleAssociatedToClosedSubscheme C (W'.subschemeι ≫ (f ≫ p)) (𝟙 W'.subscheme)
          (k + 1 + (r : ℤ))).1 V.2.1.genericPoint)
    (B : CycleGroup C (W'.subschemeι ≫ (f ≫ p)) (k + (r : ℤ)))
    (hB : ∀ z : W'.subscheme, B.1 z =
      letI := isInvertible_presheaf_modulePullback L W.subschemeι
      (flatPullback C (W'.subschemeι ≫ (f ≫ p)) (W.subschemeι ≫ p) g hgb r hr k
        (chernComponentCycle C (W.subschemeι ≫ p) hDim
          (isTrivializedNear_of_isInvertible
            ((Scheme.Modules.pullback W.subschemeι).obj L)) s)).1 z) :
    IsRationallyEquivalentToZero C (W'.subschemeι ≫ (f ≫ p)) (k + (r : ℤ))
      (cyclePullbackAlongClosedImmersion C (W'.subschemeι ≫ (f ≫ p)) (f ≫ p) W'.subschemeι rfl
        (k + (r : ℤ)) D - B) := by
  classical
  have hMinv := isInvertible_presheaf_modulePullback L W.subschemeι
  have hDimRaw : ∀ V : irreducibleComponents W'.subscheme,
      schemeDeltaDimension C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
        (W'.subschemeι ≫ (f ≫ p))) = ((k + 1 + (r : ℤ) : ℤ) : EInt) := fun V ↦
    schemeDeltaDimension_integralComponentAt_comp C (W'.subschemeι ≫ (f ≫ p))
      (W.subschemeι ≫ p) g hgb r hr hDim V
  choose cc dd hre hcc hdd using
    exists_componentCycles C p f r k L W W' g hsq hDimRaw s hs
  obtain ⟨mult, hmult⟩ : ∃ m : irreducibleComponents W'.subscheme → ℤ, ∀ V, m V =
      (cycleAssociatedToClosedSubscheme C (W'.subschemeι ≫ (f ≫ p)) (𝟙 W'.subscheme)
        (k + 1 + (r : ℤ))).1 V.2.1.genericPoint := ⟨_, fun _ ↦ rfl⟩
  have halpha : ∀ z : W'.subscheme, B.1 z =
      ∑ᶠ V : irreducibleComponents W'.subscheme, mult V *
        (properPushforward C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
            (W'.subschemeι ≫ (f ≫ p))) (W'.subschemeι ≫ (f ≫ p))
            (integralComponentAt V.2.1.genericPoint).subschemeι rfl (k + (r : ℤ))
            (cc V)).1 z := by
    intro z
    rw [hB z, flatPullback_chernComponentCycle_coeff C (W'.subschemeι ≫ (f ≫ p))
      (W.subschemeι ≫ p) g hgb r hr k _ hDim s hs cc hcc z]
    exact finsum_congr fun V ↦ by rw [hmult V]
  have hbeta : ∀ z : W'.subscheme, D.1 (W'.subschemeι.base z) =
      ∑ᶠ V : irreducibleComponents W'.subscheme, mult V *
        (properPushforward C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
            (W'.subschemeι ≫ (f ≫ p))) (W'.subschemeι ≫ (f ≫ p))
            (integralComponentAt V.2.1.genericPoint).subschemeι rfl (k + (r : ℤ))
            (dd V)).1 z := by
    intro z
    rw [hD (W'.subschemeι.base z), hreindex]
    exact finsum_congr fun V ↦ by rw [hmult V, hdd V z, hwt V]
  have haV : ∀ V : irreducibleComponents W'.subscheme,
      IsRationallyEquivalentToZero C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
        (W'.subschemeι ≫ (f ≫ p))) (k + (r : ℤ)) (mult V • (dd V - cc V)) := fun V ↦
    (rationalEquivalences C ((integralComponentAt V.2.1.genericPoint).subschemeι ≫
      (W'.subschemeι ≫ (f ≫ p))) (k + (r : ℤ))).zsmul_mem (hre V) (mult V)
  refine rationallyEquivalentToZero_of_componentSum C (W'.subschemeι ≫ (f ≫ p)) (k + (r : ℤ))
    (fun V ↦ mult V • (dd V - cc V)) haV fun z ↦ ?_
  have hlhs : (cyclePullbackAlongClosedImmersion C (W'.subschemeι ≫ (f ≫ p)) (f ≫ p)
        W'.subschemeι rfl (k + (r : ℤ)) D - B).1 z =
      D.1 (W'.subschemeι.base z) - B.1 z := rfl
  rw [hlhs, hbeta z, halpha z,
    ← finsum_sub_distrib
      (hasFiniteSupport_componentCoeff C (W'.subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) mult dd z)
      (hasFiniteSupport_componentCoeff C (W'.subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) mult cc z)]
  exact (finsum_congr fun V ↦ properPushforward_zsmul_sub_apply C _
    (W'.subschemeι ≫ (f ≫ p)) _ rfl (k + (r : ℤ)) (mult V) (dd V) (cc V) z).symm

/-! ### The two cycles on the inverse image of an integral component -/

section Setup

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

private def capCycle (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (x : X) :
    CycleGroup C (f ≫ p) (k + (r : ℤ)) :=
  (firstChernCapRule C (f ≫ p) (k + (r : ℤ))
      (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
    (hcast ▸ flatPullback C (f ≫ p) p f rfl r hf (k + 1)
      (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι (k + 1)))

private def compCycle {x : X} (hx : relativeDimension C.dimensionFunction p x = k + 1) :
    CycleGroup C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (k + (r : ℤ)) :=
  haveI := locallyOfFiniteType_comapRestrict (integralComponentAt x) f
  haveI := flat_comapRestrict (integralComponentAt x) f
  flatPullback C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
    ((integralComponentAt x).subschemeι ≫ p) (comapRestrict (integralComponentAt x) f)
    (comapRestrict_comp_base C (f ≫ p) p f rfl (integralComponentAt x)) r
    (relativeDimension_comapRestrict (integralComponentAt x) f hf) k
    (firstChernComponentCycleRule C p k L (integralComponentAt x)
      (isIntegral_integralComponentAt x) (schemeDeltaDimension_integralComponentAt_of_eq C p hx))

private theorem properPushforward_compCycle
    {x : X} (hx : relativeDimension C.dimensionFunction p x = k + 1) :
    properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ))
        (compCycle C p f r hf k L hx) =
      flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k (firstChernComponentCycleRule C p k L) x) := by
  have := locallyOfFiniteType_comapRestrict (integralComponentAt x) f
  have := flat_comapRestrict (integralComponentAt x) f
  rw [firstChernComponentCycleAt_eq C p k (firstChernComponentCycleRule C p k L) hx]
  exact (flatPullback_properPushforward_comap C (f ≫ p) p f rfl r hf k (integralComponentAt x)
    (firstChernComponentCycleRule C p k L (integralComponentAt x)
      (isIntegral_integralComponentAt x)
      (schemeDeltaDimension_integralComponentAt_of_eq C p hx))).symm

/-! ### The coefficient identity -/

private theorem coeff_identity (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) {x : X}
    (hx : relativeDimension C.dimensionFunction p x = k + 1) (y' : X') :
    (∑ᶠ x' ∈ f.base ⁻¹' {x},
        flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
            (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L)) x').1 y') -
      (flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k (firstChernComponentCycleRule C p k L) x)).1 y' =
      (properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ))
        (cyclePullbackAlongClosedImmersion C
            (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
            ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ))
            (capCycle C p f r hf k L hcast x) -
          compCycle C p f r hf k L hx)).1 y' := by
  have hD : (capCycle C p f r hf k L hcast x).1 y' =
      ∑ᶠ x' ∈ f.base ⁻¹' {x},
        flatPullbackWeight C (f ≫ p) f (k + 1 + (r : ℤ)) x' *
          (firstChernComponentCycleAt C (f ≫ p) (k + (r : ℤ))
            (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L)) x').1 y' :=
    extendCycleGroup_flatPullback_cycleAssociatedToClosedSubscheme_apply C p f r hf k _ hcast x
      hx y'
  have hind : (properPushforward C (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
        (f ≫ p) ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ))
        (cyclePullbackAlongClosedImmersion C
          (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
          ((integralComponentAt x).comap f).subschemeι rfl (k + (r : ℤ))
          (capCycle C p f r hf k L hcast x))).1 y' = (capCycle C p f r hf k L hcast x).1 y' := by
    rw [properPushforward_cyclePullbackAlongClosedImmersion_apply]
    by_cases hy : y' ∈ Set.range ((integralComponentAt x).comap f).subschemeι.base
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      exact (extendCycleGroup_eq_zero_of_notMem_range C p f r hf k _ hcast x hx hy).symm
  rw [properPushforward_sub, ← properPushforward_compCycle C p f r hf k L hx]
  change _ = (_ : ℤ) - _
  rw [hind, hD]

/-! ### The component case of Stacks 02SS for an invertible module -/

/-- **The component case of Stacks 02SS for an invertible module.** For an invertible module `L`
on `X` and `f : X' ⟶ X` flat of relative dimension `r`, the two cycles of Stacks 02SS differ,
over every integral component `W = closure {x}` of `X` of delta-dimension `k + 1`, by a cycle
rationally equivalent to zero on the inverse image `f^{-1}(W)`. -/
theorem firstChernCapRationallyCompatibleWithFlatPullback_invertible :
    FirstChernCapRationallyCompatibleWithFlatPullback C p f r hf k
      (firstChernComponentCycleRule C p k L)
      (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
        ((Scheme.Modules.pullback f).obj L)) := by
  classical
  intro x hx
  have hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1 := by ring
  have hWint := isIntegral_integralComponentAt x
  have hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p)
      = ((k + 1 : ℤ) : EInt) := schemeDeltaDimension_integralComponentAt_of_eq C p hx
  have hgt := locallyOfFiniteType_comapRestrict (integralComponentAt x) f
  have hgf := flat_comapRestrict (integralComponentAt x) f
  have hgd := relativeDimension_comapRestrict (integralComponentAt x) f hf
  have hgb := comapRestrict_comp_base C (f ≫ p) p f rfl (integralComponentAt x)
  have hMinv := isInvertible_presheaf_modulePullback L (integralComponentAt x).subschemeι
  have hNoeth : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ p)
  have hW'Noeth : IsLocallyNoetherian ((integralComponentAt x).comap f).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      (((integralComponentAt x).comap f).subschemeι ≫ (f ≫ p))
  have hs₀ := exists_ne_zero_genericStalk (isTrivializedNear_of_isInvertible
    ((Scheme.Modules.pullback (integralComponentAt x).subschemeι).obj L)
    (genericPoint (integralComponentAt x).subscheme))
  exact ⟨_,
    rationallyEquivalentToZero_sub_of_components C p f r k L (integralComponentAt x)
      ((integralComponentAt x).comap f) (comapRestrict (integralComponentAt x) f)
      (comapRestrict_subschemeι (integralComponentAt x) f) hgb hgd hDim _ hs₀.choose_spec x
      (capCycle C p f r hf k L hcast x)
      (extendCycleGroup_flatPullback_cycleAssociatedToClosedSubscheme_apply C p f r hf k _ hcast
        x hx)
      (finsum_fibre_flatPullbackWeight_eq_components C (f ≫ p) f x (k + 1 + (r : ℤ)))
      (fun V ↦ flatPullbackWeight_eq_cycleAssociatedToClosedSubscheme_id C (f ≫ p) f x
        (k + 1 + (r : ℤ)) V.2.1.genericPoint
        (base_genericPoint_comap_integralComponentAt f x V))
      (compCycle C p f r hf k L hx) fun _ ↦ rfl,
    coeff_identity C p f r hf k L hcast hx⟩

end Setup

end Stacks.Chow

end
