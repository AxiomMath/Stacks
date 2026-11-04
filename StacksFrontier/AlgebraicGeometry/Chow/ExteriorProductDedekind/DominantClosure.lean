module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SpecializationTrdeg
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormulaGeneral
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closures of points dominating a component of a Dedekind base

Let `S` be a scheme with an open covering by spectra of Dedekind domains, as in Stacks section
42.63, and let `X` be an irreducible scheme locally of finite type over `S` whose generic point
`ξ` maps to a generic point of `S`. Then:

* if `X` is integral, `X ⟶ S` is flat;
* `X ⟶ S` has relative dimension `trdeg_{κ(f ξ)} κ(ξ)`: every nonempty fibre is equidimensional
  of that dimension, the special fibres included. For this it suffices that `S` is locally
  Noetherian with local rings of dimension at most one.

Applied to the reduced closure `V` of a point `x` of a scheme over the base of section 42.63
which dominates an irreducible component of the base, this says that `V` is flat over the base
of relative dimension `δ(x) - δ(f x)`, which is `δ(x) - 1` when `f x` is not a closed point.

## Main results

* `AlgebraicGeometry.flat_of_mem_genericPoints_of_isDedekindDomain` — an integral scheme over a
  locally Dedekind base whose generic point lies over a generic point of the base is flat over
  it.
* `AlgebraicGeometry.ringKrullDim_stalk_le_one_of_isDedekindDomain` — the local rings of a
  locally Dedekind scheme have dimension at most one.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_ringKrullDim_stalk_le_one` — over a
  locally Noetherian base with local rings of dimension at most one, the fibres of an
  irreducible scheme dominating a component have local dimension `trdeg_{κ(f ξ)} κ(ξ)`
  everywhere.
* `AlgebraicGeometry.relativeDimension_of_ringKrullDim_stalk_le_one` — the same as a relative
  dimension statement.
* `Stacks.Chow.flat_pointClosure_of_dominatesBaseComponent` — the reduced closure of a point
  dominating a component of the base of section 42.63 is flat over the base.
* `Stacks.Chow.pointClosure_relativeDimension_of_dominatesBaseComponent` and
  `Stacks.Chow.pointClosure_relativeDimension_of_dominatesBaseComponent_of_not_isClosed` — it
  has relative dimension `δ(x) - δ(f x)`, respectively `δ(x) - 1`.

## Implementation notes

The relative dimension is stated with `δ(x) - δ(f x)` rather than `δ(x) - 1`, because a Dedekind
domain in the sense of `IsDedekindDomain` may be a field: a component of the base may be a
single closed point, whose generic point has `δ = 0`. When the image of `x` is not closed it has
`δ = 1`, and the second form is the corollary.

## References

* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0FC8](https://stacks.math.columbia.edu/tag/0FC8)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-! ### Flatness over a locally Dedekind base -/

/-- An integral scheme over a base covered by spectra of Dedekind domains, whose generic point
maps to a generic point of the base, is flat over the base. -/
theorem flat_of_mem_genericPoints_of_isDedekindDomain {X S : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ S)
    (hS : ∀ s : S, ∃ U : S.Opens,
      s ∈ (U : Set S) ∧ IsAffineOpen U ∧ IsDedekindDomain (S.presheaf.obj (op U)))
    (hf : f (genericPoint X) ∈ genericPoints S) : Flat f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hxU, hU, hD⟩ := hS (f x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).2
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hxV, hVU, ?_⟩
  have hξV : genericPoint X ∈ V := (genericPoint_specializes x).mem_open V.isOpen hxV
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hbot : (hU.primeIdealOf ⟨f (genericPoint X), hVU hξV⟩).asIdeal = ⊥ := by
    rw [← Ideal.height_eq_zero_iff_eq_bot]
    have h := ringKrullDim_stalk_eq_zero_of_mem_genericPoints S _ hf
    rw [hU.ringKrullDim_stalk_eq_height _ (hVU hξV)] at h
    exact_mod_cast h
  have hinj : Function.Injective (f.appLE U V hVU).hom := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hcomap := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hξV)
    rw [PrimeSpectrum.comap_asIdeal, hbot] at hcomap
    have hmem : a ∈ Ideal.comap (f.appLE U V hVU).hom
        (hV.primeIdealOf ⟨genericPoint X, hξV⟩).asIdeal := by
      rw [Ideal.mem_comap, ha]
      exact Ideal.zero_mem _
    rwa [hcomap] at hmem
  let := (f.appLE U V hVU).hom.toAlgebra
  have : Module.IsTorsionFree Γ(S, U) Γ(X, V) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  exact (inferInstance : Module.Flat Γ(S, U) Γ(X, V))

/-! ### Fibre dimension over a base of dimension at most one -/

/-- The local rings of a scheme covered by spectra of Dedekind domains have dimension at most
one. -/
theorem ringKrullDim_stalk_le_one_of_isDedekindDomain {S : Scheme.{u}}
    (hS : ∀ s : S, ∃ U : S.Opens,
      s ∈ (U : Set S) ∧ IsAffineOpen U ∧ IsDedekindDomain (S.presheaf.obj (op U)))
    (s : S) : ringKrullDim (S.presheaf.stalk s) ≤ 1 := by
  obtain ⟨U, hsU, hU, hD⟩ := hS s
  rw [hU.ringKrullDim_stalk_eq_height s hsU]
  calc ((hU.primeIdealOf ⟨s, hsU⟩).asIdeal.height : WithBot ℕ∞)
      ≤ ringKrullDim Γ(S, U) :=
        Ideal.height_le_ringKrullDim_of_ne_top (hU.primeIdealOf ⟨s, hsU⟩).isPrime.ne_top
    _ ≤ 1 := Ring.krullDimLE_iff.mp inferInstance

/-- Let `f : X ⟶ S` be locally of finite type, with `X` irreducible, `S` locally Noetherian with
local rings of dimension at most one, and the generic point `ξ` of `X` lying over a generic
point of `S`. Then the fibre through any point of `X` has local dimension
`trdeg_{κ(f ξ)} κ(ξ)` there. -/
@[ega "IV 12.2.1.1" "partial",
  ega "IV 13.1.1" "special case",
  ega "IV 9.5.6" "special case",
  sga "6 X 7.4" "partial"]
theorem topologicalKrullDimAt_fiber_eq_of_ringKrullDim_stalk_le_one {X S : Scheme.{u}}
    [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [IrreducibleSpace X]
    (hS : ∀ s : S, ringKrullDim (S.presheaf.stalk s) ≤ 1)
    (hf : f (genericPoint X) ∈ genericPoints S) (x : X) :
    letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (Cardinal.toENat (Algebra.trdeg (S.residueField (f (genericPoint X)))
        (X.residueField (genericPoint X))) : WithBot ℕ∞) := by
  let := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  set T₀ : ℕ∞ := Cardinal.toENat (Algebra.trdeg (S.residueField (f (genericPoint X)))
    (X.residueField (genericPoint X))) with hT₀
  have key : ∀ v : X,
      Cardinal.toENat (@Algebra.trdeg (S.residueField (f v)) (X.residueField v) _ _
        (f.residueFieldMap v).hom.toAlgebra) ≤ T₀ := by
    intro v
    let := (f.residueFieldMap v).hom.toAlgebra
    have H := ringKrullDim_stalk_add_trdeg_le_of_forall_genericPoints f v T₀
      (fun η hη _ ↦ by
        have hηu : closure ({η} : Set X) = Set.univ := by
          have h : closure ({η} : Set X) ∈ irreducibleComponents X := hη
          rwa [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
        have hηξ : η = genericPoint X :=
          (show IsGenericPoint η Set.univ from hηu).eq (genericPoint_spec X)
        subst hηξ
        exact le_rfl)
    by_cases hv : f v = f (genericPoint X)
    · have h0 : ringKrullDim (S.presheaf.stalk (f v)) = 0 := by
        rw [hv]
        exact ringKrullDim_stalk_eq_zero_of_mem_genericPoints S _ hf
      have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk v) :=
        ringKrullDim_nonneg_of_nontrivial
      rw [h0, zero_add] at H
      exact_mod_cast le_trans (le_add_of_nonneg_left hnn) H
    · have hvξ : v ≠ genericPoint X := fun h ↦ hv (h ▸ rfl)
      have h1 : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk v) :=
        one_le_ringKrullDim_stalk hvξ
      have H' : ((1 + Cardinal.toENat (Algebra.trdeg (S.residueField (f v))
          (X.residueField v)) : ℕ∞) : WithBot ℕ∞) ≤ ((1 + T₀ : ℕ∞) : WithBot ℕ∞) := by
        push_cast
        exact (add_le_add_left h1 _).trans (H.trans (add_le_add_left (hS _) _))
      exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp (WithBot.coe_le_coe.mp H')
  have hclosure : ∀ (s : S) (v : X) (hv : f v = s),
      topologicalKrullDim (closure ({(f.fiberHomeo s).symm ⟨v, hv⟩} : Set (f.fiber s))) ≤
        (T₀ : WithBot ℕ∞) := by
    intro s v hv
    subst hv
    show topologicalKrullDim (closure ({f.asFiber v} : Set (f.fiber (f v)))) ≤ _
    rw [topologicalKrullDim_closure_singleton_eq_trdeg (S.residueField (f v)) (f.fiber (f v))
      (f.fiberToSpecResidueField (f v)) (f.asFiber v), trdeg_residueField_asFiber f v]
    exact_mod_cast key v
  apply le_antisymm
  · obtain ⟨Z, hZ, -, hZd⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
        (S.residueField (f x)) (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) (f.asFiber x)
    rw [← hZd]
    have hw : closure ({hZ.1.genericPoint} : Set (f.fiber (f x))) = Z :=
      hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
    have hv : f (f.fiberι (f x) hZ.1.genericPoint) = f x :=
      (f.fiberHomeo (f x) hZ.1.genericPoint).2
    have hwv : hZ.1.genericPoint =
        (f.fiberHomeo (f x)).symm ⟨f.fiberι (f x) hZ.1.genericPoint, hv⟩ :=
      ((f.fiberHomeo (f x)).symm_apply_apply _).symm
    rw [← hw, hwv]
    exact hclosure _ _ hv
  · refine le_trans ?_ (fiberDimensionAt_le_of_specializes f (genericPoint_specializes x))
    rw [topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f (genericPoint X)]
    exact le_add_of_nonneg_left ringKrullDim_nonneg_of_nontrivial

/-- Let `f : X ⟶ S` be locally of finite type, with `X` irreducible, `S` locally Noetherian with
local rings of dimension at most one, and the generic point `ξ` of `X` lying over a generic
point of `S`. Then `f` has relative dimension `trdeg_{κ(f ξ)} κ(ξ)`: every nonempty fibre is
equidimensional of that dimension. -/
theorem relativeDimension_of_ringKrullDim_stalk_le_one {X S : Scheme.{u}}
    [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [IrreducibleSpace X]
    (hS : ∀ s : S, ringKrullDim (S.presheaf.stalk s) ≤ 1)
    (hf : f (genericPoint X) ∈ genericPoints S) :
    letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
    RelativeDimension f (Cardinal.toNat (Algebra.trdeg (S.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X)))) := by
  let := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  let _ : Algebra.EssFiniteType (S.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X)) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f (genericPoint X))
  have ht : Algebra.trdeg (S.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X)) < Cardinal.aleph0 := trdeg_lt_aleph0 _ _
  set d := Cardinal.toNat (Algebra.trdeg (S.residueField (f (genericPoint X)))
    (X.residueField (genericPoint X))) with hd
  have hdcast : ((d : ℕ∞) : WithBot ℕ∞) = (Cardinal.toENat (Algebra.trdeg
      (S.residueField (f (genericPoint X))) (X.residueField (genericPoint X))) :
        WithBot ℕ∞) :=
    congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
      (by rw [hd, ← Cardinal.toNat_toENat, ENat.natCast_toNat (Cardinal.toENat_lt_top.mpr ht).ne])
  intro s hs
  have hlocal : ∀ w : f.fiber s, topologicalKrullDimAt (f.fiber s) w = (d : WithBot ℕ∞) := by
    intro w
    rw [← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f s w,
      topologicalKrullDimAt_fiber_eq_of_ringKrullDim_stalk_le_one f hS hf]
    exact hdcast.symm
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (S.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) hlocal, ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hloc : ∀ w : f.fiber s, localKrullDim (f.fiber s) w = (d : WithBot ℕ∞) := fun w ↦ by
    rw [← topologicalKrullDimAt_eq_localKrullDim]; exact hlocal w
  simp_rw [hloc]
  have : Nonempty (f.fiber s) := hs
  exact iSup_const

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The reduced closure of a point dominating a component of the base -/

/-- The generic point of the reduced closure of `x` maps to `x`. -/
private theorem subschemeι_genericPoint_closure {X : Scheme.{u}} (x : X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme] :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι.base
      (genericPoint (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme) = x :=
  genericPointOf_integralComponentAt x

/-- Over the base of Stacks section 42.63, the reduced closure of a point dominating an
irreducible component of the base is flat over the base. -/
@[ega "IV 14.5.6" "(d) ⇒ (a), special case"]
theorem flat_pointClosure_of_dominatesBaseComponent (C : ChowSituation.{u})
    (hC : IsDedekindChowBase C) {X : Scheme.{u}} (p : X ⟶ C.S) (x : X)
    (hx : DominatesBaseComponent C p x) :
    Flat ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι ≫ p) := by
  have _ : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme := isIntegral_integralComponentAt x
  refine AlgebraicGeometry.flat_of_mem_genericPoints_of_isDedekindDomain _ hC.1 ?_
  rwa [Scheme.Hom.comp_apply, subschemeι_genericPoint_closure]

/-- Over the base of Stacks section 42.63, the reduced closure of a point `x` of relative
dimension `d` which dominates an irreducible component of the base has constant fibre dimension
`d - δ(f x)` over the base, and that number is non-negative. This is the analogue over a
Dedekind base of `Stacks.Chow.pointClosure_relativeDimension`. -/
theorem pointClosure_relativeDimension_of_dominatesBaseComponent (C : ChowSituation.{u})
    (hC : IsDedekindChowBase C) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (x : X)
    (hx : DominatesBaseComponent C p x) (d : ℤ)
    (hd : relativeDimension C.dimensionFunction p x = d) :
    ((d - C.dimensionFunction (p.base x)).toNat : ℤ) = d - C.dimensionFunction (p.base x) ∧
      AlgebraicGeometry.RelativeDimension
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ p)
        (d - C.dimensionFunction (p.base x)).toNat := by
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have _ : IsIntegral I.subscheme := isIntegral_integralComponentAt x
  have hbase : (I.subschemeι ≫ p) (genericPoint I.subscheme) = p x := by
    rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_closure]
  have hrel : relativeDimension C.dimensionFunction (I.subschemeι ≫ p)
      (genericPoint I.subscheme) = d := by
    rw [relativeDimension_comp_closedImmersion, subschemeι_genericPoint_closure, hd]
  have H := AlgebraicGeometry.relativeDimension_of_ringKrullDim_stalk_le_one (I.subschemeι ≫ p)
    (AlgebraicGeometry.ringKrullDim_stalk_le_one_of_isDedekindDomain hC.1) (by rwa [hbase])
  obtain ⟨n, hn, hH⟩ : ∃ n : ℕ, d - C.dimensionFunction (p.base x) = n ∧
      AlgebraicGeometry.RelativeDimension (I.subschemeι ≫ p) n := by
    refine ⟨_, ?_, H⟩
    simp only [relativeDimension, hbase] at hrel
    omega
  rw [hn, Int.toNat_natCast]
  exact ⟨rfl, hH⟩

/-- Over the base of Stacks section 42.63, the reduced closure of a point `x` of relative
dimension `d` which dominates an irreducible component of the base, and whose image is not a
closed point, has constant fibre dimension `d - 1` over the base, and `d ≥ 1`. -/
theorem pointClosure_relativeDimension_of_dominatesBaseComponent_of_not_isClosed
    (C : ChowSituation.{u}) (hC : IsDedekindChowBase C) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (x : X) (hx : DominatesBaseComponent C p x)
    (hclosed : ¬ IsClosed ({p.base x} : Set C.S)) (d : ℤ)
    (hd : relativeDimension C.dimensionFunction p x = d) :
    ((d - 1).toNat : ℤ) = d - 1 ∧
      AlgebraicGeometry.RelativeDimension
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ p) (d - 1).toNat := by
  have h := pointClosure_relativeDimension_of_dominatesBaseComponent C hC p x hx d hd
  rwa [hC.2.2 _ hclosed] at h

end Stacks.Chow

end
