module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.FactorizationCriterion
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.MultiplePointCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistSectionExistence
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic

/-!
# The minimal twist of [Stacks, Tag 0A27]

For an ideal sheaf `D` on a scheme `X`, the inclusion `D ^ (p + 1) ≤ D ^ p` induces a morphism
`ℐ_{D^{p+1}} ⟶ ℐ_{D^p}` of ideal sheaves over the two inclusions into `𝒪_X`, and it is the only
such morphism. For an effective Cartier divisor with empty support, the map `𝒪_X ⟶ 𝒪_X(D)` is
an isomorphism. Together these give the inner claim of [Stacks, Tag 0A27] for a closed point `x`
of a proper curve: given the local statement at every `p` and the dimension count at one `N`,
the complement `X ∖ {x}` is affine.

## Main results

* `Stacks.Divisors.negativeTwistMap`: the morphism `ℐ_I ⟶ ℐ_J` of ideal sheaves induced by
  `I ≤ J`, with `negativeTwistMap_idealInclusion` its compatibility with the two inclusions into
  `𝒪_X` and `eq_negativeTwistMap` saying it is the only such morphism.
* `Stacks.Divisors.isIso_unitToInvertibleSheaf_of_supportSet_eq_empty`: for an effective Cartier
  divisor with empty support, `𝒪_X ⟶ 𝒪_X(D)` is an isomorphism; hence
  `mem_range_unitToInvertibleSheaf_of_supportSet_eq_empty`, every global section of `𝒪_X(D)` is
  then a section of `𝒪_X`.
* `Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_minimal_of_finrank`: the inner
  claim of [Stacks, Tag 0A27] at a given minimal `p`.
* `Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_finrank`: the inner claim of
  [Stacks, Tag 0A27] with the local statement at every `p` and the dimension count at a single
  `N`.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (structureSheafHom)
open Stacks.ProjectiveSpaceSections

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} {I J : X.IdealSheafData}

section IdealSheafMap

/-- For `I ≤ J`, the composite `ℐ_I ⟶ 𝒪_X ⟶ i_{J*} 𝒪_{V(J)}` is zero. -/
theorem idealInclusion_comp_unitToPushforwardObjUnit_eq_zero (h : I ≤ J) :
    idealInclusion I ≫ SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (J.subschemeι.toLRSHom.toShHom)) = 0 := by
  have hcomp : (Scheme.IdealSheafData.inclusion h).toLRSHom ≫ I.subschemeι.toLRSHom
      = J.subschemeι.toLRSHom := by
    rw [← Scheme.Hom.comp_toLRSHom, Scheme.IdealSheafData.inclusion_subschemeι]
  rw [← hcomp]
  exact Stacks.ClosedImmersion.comp_unitToPushforwardObjUnit_comp_eq_zero
    (Scheme.IdealSheafData.inclusion h).toLRSHom I.subschemeι.toLRSHom
    (idealInclusion I) (kernel.condition _)

/-- **The morphism `ℐ_I ⟶ ℐ_J` of ideal sheaves induced by `I ≤ J`**, the lift of
`ℐ_I ⟶ 𝒪_X` through the kernel `ℐ_J` of `𝒪_X ⟶ i_* 𝒪_{V(J)}` ([Stacks, Tag 01WX] (3)). -/
noncomputable def negativeTwistMap (h : I ≤ J) : negativeTwist I ⟶ negativeTwist J :=
  kernel.lift _ (idealInclusion I) (idealInclusion_comp_unitToPushforwardObjUnit_eq_zero h)

/-- **The induced morphism lies over the two inclusions into `𝒪_X`.** -/
@[reassoc]
theorem negativeTwistMap_idealInclusion (h : I ≤ J) :
    negativeTwistMap h ≫ idealInclusion J = idealInclusion I :=
  kernel.lift_ι _ _ _

/-- **There is only one morphism of ideal sheaves over the two inclusions into `𝒪_X`.** -/
theorem eq_negativeTwistMap (h : I ≤ J) (φ : negativeTwist I ⟶ negativeTwist J)
    (hφ : φ ≫ idealInclusion J = idealInclusion I) : φ = negativeTwistMap h := by
  refine (cancel_mono (idealInclusion J)).mp ?_
  rw [hφ, negativeTwistMap_idealInclusion]

/-- **`ℐ_{D^{p+1}} ≤ ℐ_{D^p}`.** -/
theorem pow_succ_le_pow (D : X.IdealSheafData) (p : ℕ) : D ^ (p + 1) ≤ D ^ p :=
  Scheme.IdealSheafData.pow_le_pow_right_of_le D (Nat.le_succ p)

end IdealSheafMap

section EmptySupport

/-- **The support of the zeroth power of an ideal sheaf is empty.** -/
theorem supportSet_pow_zero (D : X.IdealSheafData) : (D ^ 0).supportSet = ∅ := by
  rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
  rfl

/-- **`𝒪_X ⟶ 𝒪_X(D)` is an isomorphism when `D` has empty support.** -/
theorem isIso_unitToInvertibleSheaf_of_supportSet_eq_empty (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (h : D.supportSet = ∅) :
    IsIso (unitToInvertibleSheaf D) := by
  have huniv : (nonvanishingChart (invertibleSheaf D) (canonicalSections D) : Set X)
      = Set.univ := by
    rw [nonvanishingChart_canonicalSections, h, Set.compl_empty]
  refine Stacks.SheafOfModules.isIso_of_isIso_val_app _ fun A => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  refine Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen
    (X := X.toRingedSpace) (invertibleSheaf D) (canonicalSections D) A.unop
    fun y _ => Set.eq_univ_iff_forall.mp huniv y

/-- **Every global section of `𝒪_X(D)` is a section of `𝒪_X` when `D` has empty support.** -/
theorem mem_range_unitToInvertibleSheaf_of_supportSet_eq_empty (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (h : D.supportSet = ∅)
    (t : (invertibleSheaf D).sections) :
    t ∈ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf D)) := by
  have hiso := isIso_unitToInvertibleSheaf_of_supportSet_eq_empty D h
  refine ⟨_root_.SheafOfModules.sectionsMap (inv (unitToInvertibleSheaf D)) t, ?_⟩
  rw [← _root_.SheafOfModules.sectionsMap_comp, IsIso.inv_hom_id,
    _root_.SheafOfModules.sectionsMap_id]

end EmptySupport

section Engine

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

/-- **The inner claim of [Stacks, Tag 0A27] at a minimal `p`.** Let `X` be a proper curve over
`k`, locally Noetherian and integral, and let `x` be a closed point at which `𝒪_{X,x}` is a
discrete valuation ring. Suppose that a global section of `𝒪_X((p+1)x)` whose germ at `x` does
not generate the stalk comes from `𝒪_X(p·x)` (`hlocal`), that every global section of
`𝒪_X(p·x)` is a section of `𝒪_X` (`hmin`), and that
`dim_k H¹(X, 𝒪_X) < d ≤ dim_k H⁰(X, i_* i^* 𝒪_X((p+1)x))`. Then `X ∖ {x}` is affine. -/
theorem isAffineOpen_compl_singleton_of_mem_range_of_minimal_of_finrank
    [IsLocallyNoetherian X] [IsIntegral X]
    (hf : IsProper f) (hc : IsCurve k f) {x : X} (hx : IsClosed ({x} : Set X))
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {p : ℕ}
    (hlocal : ∀ t : (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))).sections,
      x ∉ nonvanishingChart (invertibleSheaf
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))) t →
        t ∈ Set.range (_root_.SheafOfModules.sectionsMap (invertibleSheafMap
          (negativeTwistMap (pow_succ_le_pow
            (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) p)))))
    (hmin : ∀ t : (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p)).sections,
      t ∈ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ p))))
    [FiniteDimensional k
      (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 1)]
    {d : ℕ}
    (hd : Module.finrank k
      (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 1) < d)
    (hd' : d ≤ Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)).subschemeι).obj
        ((Scheme.Modules.pullback
            (Scheme.IdealSheafData.vanishingIdeal
              (⟨{x}, hx⟩ : Closeds X) ^ (p + 1)).subschemeι).obj
          (modulesInvertibleSheaf
            (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))))) 0)) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) :=
  isAffineOpen_compl_singleton_of_minimal_of_finrank f hf hc hx
    (negativeTwistMap (pow_succ_le_pow _ p)) (negativeTwistMap_idealInclusion _) hlocal hmin
    hd hd'

/-- **The inner claim of [Stacks, Tag 0A27].** Let `X` be a proper curve over `k`, locally
Noetherian and integral, and let `x` be a closed point at which `𝒪_{X,x}` is a discrete valuation
ring. Given

* `hlocal`, at **every** `p`: a global section of `𝒪_X((p+1)x)` whose germ at `x` does not
  generate the stalk comes from `𝒪_X(p·x)`;
* `hd`, `hd'`, at a **single** `N`: `dim_k H¹(X, 𝒪_X) < d ≤ dim_k H⁰(X, i_* i^* 𝒪_X((N+1)x))`;

then `X ∖ {x}` is affine. -/
theorem isAffineOpen_compl_singleton_of_mem_range_of_finrank
    [IsLocallyNoetherian X] [IsIntegral X]
    (hf : IsProper f) (hc : IsCurve k f) {x : X} (hx : IsClosed ({x} : Set X))
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hlocal : ∀ p : ℕ, ∀ t : (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))).sections,
      x ∉ nonvanishingChart (invertibleSheaf
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (p + 1))) t →
        t ∈ Set.range (_root_.SheafOfModules.sectionsMap (invertibleSheafMap
          (negativeTwistMap (pow_succ_le_pow
            (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) p)))))
    [FiniteDimensional k
      (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 1)]
    {d N : ℕ}
    (hd : Module.finrank k
      (cohomologyOverField k f (_root_.SheafOfModules.unit X.ringCatSheaf) 1) < d)
    (hd' : d ≤ Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (N + 1)).subschemeι).obj
        ((Scheme.Modules.pullback
            (Scheme.IdealSheafData.vanishingIdeal
              (⟨{x}, hx⟩ : Closeds X) ^ (N + 1)).subschemeι).obj
          (modulesInvertibleSheaf
            (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (N + 1))))) 0)) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_notMem_range_unitToInvertibleSheaf f
    (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ (N + 1)) hd hd'
  have hQ : ∃ n : ℕ, ∃ t : (invertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)).sections,
      t ∉ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))) :=
    ⟨N + 1, s₀, hs₀⟩
  have hbase : ¬ ∃ t : (invertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ 0)).sections,
      t ∉ Set.range (_root_.SheafOfModules.sectionsMap (unitToInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ 0))) := by
    rintro ⟨t, ht⟩
    exact ht (mem_range_unitToInvertibleSheaf_of_supportSet_eq_empty _
      (supportSet_pow_zero _) t)
  have hne : Nat.find hQ ≠ 0 := fun h0 => hbase (h0 ▸ Nat.find_spec hQ)
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin := Nat.find_min hQ (m := p) (by omega)
  obtain ⟨s, hs⟩ := hp ▸ Nat.find_spec hQ
  exact isAffineOpen_compl_singleton_of_minimal hf hc hx
    (negativeTwistMap (pow_succ_le_pow _ p)) (negativeTwistMap_idealInclusion _)
    (hlocal p) (fun t => not_not.mp fun hnt => hmin ⟨t, hnt⟩) s hs

end Engine

end Stacks.Divisors

end
