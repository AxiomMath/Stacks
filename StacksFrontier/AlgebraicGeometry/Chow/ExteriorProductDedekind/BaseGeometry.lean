module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Cycles
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GraphLineProjectionFlat
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Triviality
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.HigherCodimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base of the exterior product over a Dedekind base

Let `(S, δ)` be as in Stacks section 42.63: `S` is locally the spectrum of a Dedekind domain,
`δ(s) = 0` at closed points and `δ(s) = 1` elsewhere. This file records the local structure of such
a base.

* Every local ring `𝒪_{S,s}` is a localization of a Dedekind domain, hence a Dedekind domain,
  hence a principal ideal domain of dimension at most one.
* A point `s` which is not the generic point of an irreducible component of `S` is closed and
  `𝒪_{S,s}` is a discrete valuation ring: a chain `η ⤳ s ⤳ t` of distinct points would give
  `𝒪_{S,t}` dimension at least two.
* For such a point the reduced closed point `s` is an effective Cartier divisor of `S`.

## References

* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite IsLocalRing

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}}

/-- On a base as in Stacks section 42.63 every local ring is a Dedekind domain. -/
theorem IsDedekindChowBase.isDedekindDomain_stalk (hC : IsDedekindChowBase C) (s : C.S) :
    IsDedekindDomain (C.S.presheaf.stalk s) := by
  obtain ⟨U, hsU, hU, hD⟩ := hC.1 s
  let _ := C.S.presheaf.algebra_section_stalk (⟨s, hsU⟩ : U)
  have := hU.isLocalization_stalk ⟨s, hsU⟩
  have : IsDomain (C.S.presheaf.stalk s) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (C.S.presheaf.stalk s)
      (hU.primeIdealOf ⟨s, hsU⟩).asIdeal.primeCompl_le_nonZeroDivisors
  exact IsLocalization.isDedekindDomain Γ(C.S, U)
    (hU.primeIdealOf ⟨s, hsU⟩).asIdeal.primeCompl_le_nonZeroDivisors _

/-- The local rings of a base as in Stacks section 42.63 are domains. -/
theorem IsDedekindChowBase.isDomain_stalk (hC : IsDedekindChowBase C) (s : C.S) :
    IsDomain (C.S.presheaf.stalk s) :=
  (hC.isDedekindDomain_stalk s).toIsDomain

/-- The local rings of a base as in Stacks section 42.63 have dimension at most one. -/
theorem IsDedekindChowBase.ringKrullDim_stalk_le_one (hC : IsDedekindChowBase C) (s : C.S) :
    ringKrullDim (C.S.presheaf.stalk s) ≤ 1 := by
  have := hC.isDedekindDomain_stalk s
  exact Ring.krullDimLE_iff.mp inferInstance

/-- A point of a base as in Stacks section 42.63 which is not the generic point of an
irreducible component has a proper generization. -/
theorem exists_specializes_ne_of_not_mem_irreducibleComponents {s : C.S}
    (hs : closure ({s} : Set C.S) ∉ irreducibleComponents C.S) :
    ∃ η : C.S, η ⤳ s ∧ η ≠ s := by
  by_contra h
  push Not at h
  exact hs (closure_singleton_mem_irreducibleComponents_of_forall_specializes h)

/-- In the specialization order of a scheme a proper generization is strictly larger. -/
theorem lt_of_specializes_of_ne {X : Scheme.{u}} {a b : X} (h : a ⤳ b) (hne : a ≠ b) :
    b < a :=
  lt_of_le_not_ge h fun h' ↦ hne (h.antisymm h').eq

/-- A point of coheight at least `m + 1` has a local ring of dimension more than `m`. -/
private theorem false_of_add_one_le_coheight {X : Scheme.{u}} {x : X} {m : ℕ}
    (hco : (m + 1 : ℕ∞) ≤ Order.coheight x) (hdim : ringKrullDim (X.presheaf.stalk x) ≤ m) :
    False := by
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  have := (WithBot.coe_le_coe.mpr hco).trans hdim
  norm_cast at this
  omega

/-- **Closed points of a Dedekind base.** On a base as in Stacks section 42.63 a point which is
not the generic point of an irreducible component is closed. -/
theorem IsDedekindChowBase.isClosed_singleton (hC : IsDedekindChowBase C) {s : C.S}
    (hs : closure ({s} : Set C.S) ∉ irreducibleComponents C.S) :
    IsClosed ({s} : Set C.S) := by
  obtain ⟨η, hηs, hne⟩ := exists_specializes_ne_of_not_mem_irreducibleComponents hs
  refine isClosed_of_closure_subset fun t ht ↦ ?_
  by_contra htne
  have hco : (2 : ℕ∞) ≤ Order.coheight t :=
    calc (2 : ℕ∞) ≤ Order.coheight η + 1 + 1 := by
          rw [add_assoc, one_add_one_eq_two]; exact le_add_self
      _ ≤ Order.coheight s + 1 := by
          gcongr; exact Order.coheight_add_one_le (lt_of_specializes_of_ne hηs hne)
      _ ≤ Order.coheight t := Order.coheight_add_one_le
        (lt_of_specializes_of_ne (specializes_iff_mem_closure.mpr ht) (Ne.symm htne))
  exact false_of_add_one_le_coheight (m := 1) hco (hC.ringKrullDim_stalk_le_one t)

/-- **Local rings at closed points of a Dedekind base.** On a base as in Stacks section 42.63 the
local ring at a point which is not the generic point of an irreducible component is a discrete
valuation ring. -/
theorem IsDedekindChowBase.isDiscreteValuationRing_stalk (hC : IsDedekindChowBase C) {s : C.S}
    (hs : closure ({s} : Set C.S) ∉ irreducibleComponents C.S) :
    haveI := hC.isDomain_stalk s
    IsDiscreteValuationRing (C.S.presheaf.stalk s) := by
  have := hC.isDedekindDomain_stalk s
  obtain ⟨η, hηs, hne⟩ := exists_specializes_ne_of_not_mem_irreducibleComponents hs
  have hnf : ¬ IsField (C.S.presheaf.stalk s) := by
    intro hF
    let _ := hF.toField
    have h0 : ringKrullDim (C.S.presheaf.stalk s) = 0 := ringKrullDim_eq_zero_of_field _
    exact false_of_add_one_le_coheight (m := 0)
      (le_add_self.trans (Order.coheight_add_one_le (lt_of_specializes_of_ne hηs hne))) h0.le
  exact ((IsDiscreteValuationRing.TFAE (C.S.presheaf.stalk s) hnf).out 3 1).mp ‹_›

/-- **A closed point of a Dedekind base is an effective Cartier divisor.** On a base as in Stacks
section 42.63 the reduced closed subscheme on a point which is not the generic point of an
irreducible component is an effective Cartier divisor. -/
theorem IsDedekindChowBase.isEffectiveCartierDivisor_vanishingIdeal (hC : IsDedekindChowBase C)
    {s : C.S} (hs : closure ({s} : Set C.S) ∉ irreducibleComponents C.S) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{s}, hC.isClosed_singleton hs⟩ : Closeds C.S)) := by
  have := hC.isDedekindDomain_stalk s
  have := hC.isDiscreteValuationRing_stalk hs
  have hx := hC.isClosed_singleton hs
  have key : ∃ (U : C.S.affineOpens) (hxU : s ∈ (U : Set C.S)),
      ∃ ξ ∈ nonZeroDivisors (C.S.presheaf.stalk s),
        Ideal.map (C.S.presheaf.germ U.1 s hxU).hom
            ((Scheme.IdealSheafData.vanishingIdeal (⟨{s}, hx⟩ : Closeds C.S)).ideal U)
          = Ideal.span {ξ} := by
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      C.S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    obtain ⟨π, hπ⟩ := IsPrincipalIdealRing.principal (maximalIdeal (C.S.presheaf.stalk s))
    refine ⟨⟨V, hV⟩, hxV, π, ?_, ?_⟩
    · refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
      refine IsDiscreteValuationRing.not_a_field (C.S.presheaf.stalk s) ?_
      rw [hπ, h0]
      simp
    · rw [map_germ_ideal_vanishingIdeal_singleton hx ⟨V, hV⟩ hxV, hπ]
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_stalk _ fun z hz => ?_
  rw [supportSet_vanishingIdeal_singleton hx] at hz
  replace hz : z = s := hz
  subst hz
  exact key

/-! ### The section cutting out a closed point -/

/-- **The closed point as the zero scheme of a section.** On a base as in Stacks section 42.63 a
point `s` which is not the generic point of an irreducible component is the zero scheme of a
global section of an invertible module (the canonical section of `𝒪_S(s)`), and that invertible
module restricts trivially to the point. -/
theorem IsDedekindChowBase.exists_section_zeroScheme_eq (hC : IsDedekindChowBase C) {s : C.S}
    (hs : closure ({s} : Set C.S) ∉ irreducibleComponents C.S) :
    ∃ (L : C.S.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible C.S.sheaf.obj
        C.S.ringCatSheaf.property L) (σ : Γ(L, ⊤)),
      Stacks.Divisors.zeroScheme C.S L σ =
          Scheme.IdealSheafData.vanishingIdeal
            (⟨{s}, hC.isClosed_singleton hs⟩ : Closeds C.S) ∧
        AlgebraicGeometry.SheafOfModules.IsTrivial
          (Stacks.Divisors.zeroScheme C.S L σ).subscheme.sheaf.obj
          (Stacks.Divisors.zeroScheme C.S L σ).subscheme.ringCatSheaf.property
          ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme C.S L σ).subschemeι).obj L) := by
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{s}, hC.isClosed_singleton hs⟩ : Closeds C.S)
  have := hC.isEffectiveCartierDivisor_vanishingIdeal hs
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible C.S.sheaf.obj
      C.S.ringCatSheaf.property (Stacks.Divisors.invertibleSheaf' D) :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  obtain ⟨σ, -, hσ⟩ := exists_isRegularSection_zeroScheme_eq D
    (Stacks.Divisors.invertibleSheaf' D) (Iso.refl _)
  have hσ' : Stacks.Divisors.zeroScheme C.S (Stacks.Divisors.invertibleSheaf' D)
      (σ.eval (op ⊤)) = D := hσ
  refine ⟨Stacks.Divisors.invertibleSheaf' D, hinv, σ.eval (op ⊤), hσ', ?_⟩
  rw [hσ']
  have : Subsingleton D.subscheme :=
    subsingleton_subscheme_vanishingIdeal (hC.isClosed_singleton hs)
  have : DiscreteTopology D.subscheme := inferInstance
  have hpinv : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf
      (structureSheafRing D.subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' D)) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (Stacks.Divisors.pullback_isInvertible D.subschemeι _)
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology D.subscheme
    ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' D))
  exact ⟨e⟩

/-! ### Flatness and relative dimension of integral schemes over the base -/

/-- The local ring at the generic point of an irreducible component of a base as in Stacks
section 42.63 is a field. -/
theorem IsDedekindChowBase.isField_stalk_of_mem (hC : IsDedekindChowBase C) {η : C.S}
    (hη : closure ({η} : Set C.S) ∈ irreducibleComponents C.S) :
    IsField (C.S.presheaf.stalk η) := by
  have := hC.isDomain_stalk η
  have hmax : IsMax η := by
    intro a ha
    have hsub : closure ({η} : Set C.S) ⊆ closure ({a} : Set C.S) :=
      closure_minimal (Set.singleton_subset_iff.mpr ha.mem_closure) isClosed_closure
    have heq := hη.2 isIrreducible_singleton.closure hsub
    exact (specializes_iff_mem_closure.mpr (heq (subset_closure rfl)) : η ⤳ a)
  have h0 : ringKrullDim (C.S.presheaf.stalk η) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast Order.coheight_eq_zero.mpr hmax
  have : Ring.KrullDimLE 0 (C.S.presheaf.stalk η) := Ring.krullDimLE_iff.mpr h0.le
  exact Ring.KrullDimLE.isField_of_isDomain

/-- The generization maps between the local rings of a base as in Stacks section 42.63 are
injective. -/
theorem IsDedekindChowBase.stalkSpecializes_injective (hC : IsDedekindChowBase C) {a b : C.S}
    (h : a ⤳ b) : Function.Injective (C.S.presheaf.stalkSpecializes h) := by
  obtain ⟨U, hbU, hU, hD⟩ := hC.1 b
  have haU : a ∈ U := (h.mem_open U.isOpen hbU)
  let _ := C.S.presheaf.algebra_section_stalk (⟨a, haU⟩ : U)
  let _ := C.S.presheaf.algebra_section_stalk (⟨b, hbU⟩ : U)
  have hla := hU.isLocalization_stalk ⟨a, haU⟩
  have hlb := hU.isLocalization_stalk ⟨b, hbU⟩
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  rw [← map_sub] at hxy
  set z := x - y
  obtain ⟨⟨r, m⟩, hz⟩ := IsLocalization.mk'_surjective
    (hU.primeIdealOf ⟨b, hbU⟩).asIdeal.primeCompl z
  dsimp only at hz
  have hcomm : ∀ t : Γ(C.S, U), C.S.presheaf.stalkSpecializes h
      (algebraMap Γ(C.S, U) (C.S.presheaf.stalk b) t) =
      algebraMap Γ(C.S, U) (C.S.presheaf.stalk a) t := fun t ↦
    congrArg (fun φ ↦ φ.hom t) (C.S.presheaf.germ_stalkSpecializes (U := U) hbU h)
  have hr : algebraMap Γ(C.S, U) (C.S.presheaf.stalk a) r = 0 := by
    have hmk : z * algebraMap _ (C.S.presheaf.stalk b) (m : Γ(C.S, U)) =
        algebraMap _ (C.S.presheaf.stalk b) r := by
      rw [← hz]; exact IsLocalization.mk'_spec _ _ _
    have := congrArg (C.S.presheaf.stalkSpecializes h).hom hmk
    rw [map_mul, hcomm, hcomm, hxy, zero_mul] at this
    exact this.symm
  have hr0 : r = 0 := by
    obtain ⟨⟨c, hc⟩, hcr⟩ := (IsLocalization.map_eq_zero_iff
      (hU.primeIdealOf ⟨a, haU⟩).asIdeal.primeCompl (C.S.presheaf.stalk a) r).mp hr
    have hc0 : c ≠ 0 := fun h0 ↦ hc (h0 ▸ Ideal.zero_mem _)
    exact (mul_eq_zero.mp hcr).resolve_left hc0
  rw [← hz, hr0]
  exact IsLocalization.mk'_zero _

/-- **Integral schemes dominating a component of a Dedekind base are flat over it.** If `P` is
integral and `q : P ⟶ S` carries the generic point of `P` to the generic point of an irreducible
component of a base as in Stacks section 42.63, then `q` is flat. -/
theorem IsDedekindChowBase.flat_of_mem_irreducibleComponents (hC : IsDedekindChowBase C)
    {P : Scheme.{u}} [IsIntegral P] (q : P ⟶ C.S)
    (hq : closure ({q.base (genericPoint P)} : Set C.S) ∈ irreducibleComponents C.S) :
    Flat q := by
  refine Flat.of_stalkMap q fun x ↦ ?_
  have := hC.isDedekindDomain_stalk (q.base x)
  have hgen : genericPoint P ⤳ x := genericPoint_specializes x
  have hinj : Function.Injective (q.stalkMap x) := by
    intro a b hab
    have h1 := congrArg (P.presheaf.stalkSpecializes hgen).hom hab
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply,
      ← Scheme.Hom.stalkSpecializes_stalkMap_apply] at h1
    let _ := (hC.isField_stalk_of_mem hq).toField
    have h2 := (q.stalkMap (genericPoint P)).hom.injective h1
    exact hC.stalkSpecializes_injective _ h2
  exact flat_of_injective_of_isBezout (f := (q.stalkMap x).hom) hinj

/-- A morphism to a scheme all of whose local rings are fields is flat. -/
theorem flat_of_isField_stalk {P T : Scheme.{u}} (q : P ⟶ T)
    (hT : ∀ t : T, IsField (T.presheaf.stalk t)) : Flat q := by
  refine Flat.of_stalkMap q fun x ↦ ?_
  let _ := (hT (q.base x)).toField
  rw [RingHom.Flat]
  infer_instance

/-- **Relative dimension of an irreducible scheme over a base of dimension at most one.** Let
`q : P ⟶ T` be locally of finite type with `P` irreducible, and assume the local rings of `T` at
the points of the image are Noetherian of dimension at most one. Then every nonempty fibre of `q`
is equidimensional of dimension the transcendence degree of the residue field extension at the
generic point of `P` (Stacks 0B2I). -/
@[ega "IV 5.6.5" "special case"]
theorem relativeDimension_of_irreducibleSpace {P T : Scheme.{u}} (q : P ⟶ T)
    [LocallyOfFiniteType q] [IrreducibleSpace P]
    (hT : ∀ x : P, IsNoetherianRing (T.presheaf.stalk (q.base x)) ∧
      ringKrullDim (T.presheaf.stalk (q.base x)) ≤ 1) :
    AlgebraicGeometry.RelativeDimension q (Cardinal.toNat (residueTrdeg q (genericPoint P))) := by
  rw [relativeDimension_iff_forall_topologicalKrullDimAt]
  intro x
  refine topologicalKrullDimAt_fiber_eq_of_target_dim_le_one q x (hT x).1 (hT x).2 _ ?_
  intro η hη _
  have hηgen : η = genericPoint P := by
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hη
    exact ((genericPoint_spec P).eq (by rw [IsGenericPoint, hη])).symm
  subst hηgen
  set W : irreducibleComponents P := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; rfl⟩
  have hWgen : W.2.1.genericPoint = genericPoint P :=
    (W.2.1.isGenericPoint_genericPoint isClosed_univ).eq (by
      change closure _ = _
      exact genericPoint_spec P)
  have hzero := ringKrullDim_stalk_fiber_genericPoint q W
  rw [hWgen] at hzero
  have hfx := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg q (genericPoint P)
  rw [hzero, zero_add] at hfx
  rw [hfx]
  have hlt := residueTrdeg_lt_aleph0 q (genericPoint P)
  change ((Cardinal.toENat (residueTrdeg q (genericPoint P)) : ℕ∞) : WithBot ℕ∞) = _
  rw [Cardinal.toENat_eq_natCast.mpr (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm]
  norm_cast

end Stacks.Chow
