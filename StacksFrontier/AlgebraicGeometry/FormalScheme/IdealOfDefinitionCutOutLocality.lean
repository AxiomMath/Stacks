/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinitionColimit
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinitionLocality
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionCutOutLocality

/-!
# Locality of ideals of definition cut out by their sections

**Stacks 0AIW** says that on a formal scheme `𝔛` à la EGA the condition of being an ideal of
definition, and that of being a fundamental system of ideals of definition, may be checked on the
members of an affine open covering. For an arbitrary ideal sheaf both claims are false
(`not_forall_isIdealOfDefinitionOn_of_cover`,
`not_forall_isFundamentalSystemOfIdealsOfDefinitionOn_of_hasBasis_cover`). This file proves them
for the ideal sheaves cut out by their sections over the affine formal opens
(`IdealSheaf.IsCutOutOn`), the class of the colimit criterion
`FormalScheme.isFppfColimitOfThickenings_iff`.

## The argument

Let `𝔚 ⊆ 𝔙` be affine formal opens, `𝔚 ≅ Spf B`, with `ℐ(𝔙)` an ideal of definition. By
`IdealSheaf.isWeakIdealOfDefinition_of_le_of_isCutOutOn` the ideal `ℐ(𝔚)` is open. Given an open
ideal `O` of `B`, let `L ⊆ O` be a weak ideal of definition and `K = L + ℐ(𝔙)B`, a weak ideal of
definition. The quotient point `Spec (B/K) → 𝔚` kills `ℐ(𝔙)`, hence, `ℐ` being cut out over `𝔙`,
kills `ℐ(𝔚)`: so `ℐ(𝔚) ⊆ K`. As `ℐ(𝔙)ᵐ` maps into `L` for `m` large, `K^{1+m} ⊆ L + (ℐ(𝔙)B)ᵐ ⊆ L`,
so `ℐ(𝔚)^{1+m} ⊆ O`: this is the uniform power bound the weak version lacks.

## Main results

In namespace `AlgebraicGeometry.LocallyTopologicallyRingedSpace`:

* `IdealSheaf.isIdealOfDefinition_of_le_of_isCutOutOn`: for a cut-out ideal sheaf, being an ideal
  of definition over an affine formal open passes to every smaller affine formal open.
* `IdealSheaf.isIdealOfDefinitionOn_of_cover_of_isCutOutOn`: **Stacks 0AIW**, the
  ideal-of-definition condition on an affine open covering.
* `isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_isCutOutOn`: **Stacks 0AIW**, the
  fundamental-system condition on an affine open covering.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

namespace LocallyTopologicallyRingedSpace.IdealSheaf

variable {X : LTRS.{u}} {I : IdealSheaf X}

/-- **A cut-out ideal sheaf which is an ideal of definition over an affine formal open is one over
every smaller affine formal open.** If `ℐ` is cut out by its sections over the weak affine formal
opens and `ℐ(𝔙)` is an ideal of definition, then so is `ℐ(𝔚)` for every weak affine formal open
`𝔚 ⊆ 𝔙`. -/
theorem isIdealOfDefinition_of_le_of_isCutOutOn
    (hC : I.IsCutOutOn (IsWeakAffineFormalOpen X)) {V W : Opens X}
    (hV : IsWeakAffineFormalOpen X V) (hW : IsWeakAffineFormalOpen X W) (hWV : W ≤ V)
    (hJ : IsIdealOfDefinition (I.ideal V)) :
    IsIdealOfDefinition (I.ideal W) := by
  have hJw := isWeakIdealOfDefinition_of_isIdealOfDefinition hJ
  refine ⟨(isWeakIdealOfDefinition_of_le_of_isCutOutOn hC hV hW hWV hJw).1, fun U hU => ?_⟩
  let B := hW.chart.ring.α
  let hB := hW.chart.admissible
  let ψ := hW.chart.iso
  let e := weakChartSectionsRingEquiv B hB ψ
  let h := weakChartSectionsHomeomorph B hB ψ
  have hsec : ∀ x : (X.presheaf.obj (op W)).α, (weakChartSections B hB ψ).1 (e.symm x) = x :=
    e.apply_symm_apply
  have hU' : h ⁻¹' U ∈ nhds (0 : B) := by
    refine h.continuous.continuousAt.preimage_mem_nhds ?_
    rwa [weakChartSectionsHomeomorph_apply, map_zero]
  obtain ⟨O, hO, hOU⟩ := (IsLinearTopology.hasBasis_ideal (R := B)).mem_iff.mp hU'
  let L₀ := weaklyPreAdmissibleSpfIndex B hB.1
  have hLopen : IsOpen ((O ⊓ L₀.1 : Ideal B) : Set B) :=
    (O.toAddSubgroup.isOpen_of_mem_nhds hO).inter L₀.2.1
  let res := X.presheaf.map (homOfLE hWV).op
  let φ : (X.presheaf.obj (op V)).α →+* B := (e.symm : _ →+* B).comp res.1
  have hφ : Continuous φ := h.symm.continuous.comp res.2
  let K : Ideal B := (O ⊓ L₀.1) ⊔ Ideal.map φ (I.ideal V)
  have hKnil : K ≤ topologicalNilradical B := by
    refine sup_le (fun x hx => L₀.2.2 x hx.2) (Ideal.map_le_iff_le_comap.2 fun t ht => ?_)
    exact IsTopologicallyNilpotent.map (φ := φ) hφ (hJw.2 t ht)
  let N : WeakIdealsOfDefinition B :=
    ⟨K, Submodule.isOpen_mono le_sup_left hLopen, fun x hx => hKnil hx⟩
  let f := weakChartPoint B hB ψ N
  have hfW : Set.range f.toHom.base ⊆ (W : Set X) := range_weakChartPoint_subset B hB ψ N
  have hkill : ∀ t ∈ I.ideal V, (f.toHom.c.app (op V)).1 t = 0 := by
    intro t ht
    refine c_app_eq_zero_of_range_subset_of_le f hWV hfW ?_
    rw [← hsec (res.1 t)]
    exact (weakChartPoint_c_app_weakChartSections_eq_zero_iff B hB ψ N _).2
      (le_sup_right (a := O ⊓ L₀.1) (Ideal.mem_map_of_mem φ ht))
  have hWK : Ideal.map (e.symm : _ →+* B) (I.ideal W) ≤ K := by
    refine Ideal.map_le_iff_le_comap.2 fun s hs => ?_
    have hs0 := (hC V hV W hWV s).1 hs _ f (hfW.trans hWV) hkill
    rw [← hsec s] at hs0
    exact (weakChartPoint_c_app_weakChartSections_eq_zero_iff B hB ψ N _).1 hs0
  obtain ⟨m, hm⟩ := hJ.exists_pow_le (J := Ideal.comap φ (O ⊓ L₀.1)) (hLopen.preimage hφ)
  have hJm : Ideal.map φ (I.ideal V) ^ m ≤ O ⊓ L₀.1 := by
    rw [← Ideal.map_pow]
    exact (Ideal.map_mono hm).trans Ideal.map_comap_le
  have hKpow : K ^ (1 + m) ≤ O := Ideal.sup_pow_add_le_pow_sup_pow.trans
    (sup_le ((pow_one _).trans_le inf_le_left) (hJm.trans inf_le_left))
  refine ⟨1 + m, fun x hx => ?_⟩
  have hx' : e.symm x ∈ Ideal.map (e.symm : _ →+* B) (I.ideal W ^ (1 + m)) :=
    Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at hx'
  have := hOU (hKpow (Ideal.pow_right_mono hWK _ hx'))
  rwa [Set.mem_preimage, weakChartSectionsHomeomorph_apply, hsec] at this

end LocallyTopologicallyRingedSpace.IdealSheaf

namespace LocallyTopologicallyRingedSpace

open IdealSheaf

variable {X : LTRS.{u}}

/-- Cutting out by sections over affine formal opens gives the same over weak affine ones. -/
private theorem isCutOutOn_weak_of_isCutOutOn_affine (hX : IsFormalScheme X) {I : IdealSheaf X}
    (hC : I.IsCutOutOn (IsAffineFormalOpen X)) : I.IsCutOutOn (IsWeakAffineFormalOpen X) := by
  rwa [hX.isWeakAffineFormalOpen_eq]

/-- A cut-out ideal sheaf which is an ideal of definition over an affine formal open is one over
every smaller affine formal open. -/
private theorem isIdealOfDefinition_of_le_of_isCutOutOn_affine (hX : IsFormalScheme X)
    {I : IdealSheaf X} (hC : I.IsCutOutOn (IsAffineFormalOpen X)) {V W : Opens X}
    (hV : IsAffineFormalOpen X V) (hW : IsAffineFormalOpen X W) (hWV : W ≤ V)
    (hJ : IsIdealOfDefinition (I.ideal V)) : IsIdealOfDefinition (I.ideal W) :=
  isIdealOfDefinition_of_le_of_isCutOutOn (isCutOutOn_weak_of_isCutOutOn_affine hX hC)
    hV.isWeakAffineFormalOpen hW.isWeakAffineFormalOpen hWV hJ

/-- **Stacks 0AIW, the ideal-of-definition condition may be checked on the members of an affine
open covering, for ideal sheaves cut out by their sections.** Let `𝔛` be a formal scheme à la EGA
and `ℐ` an ideal sheaf cut out by its sections over the affine formal opens
(`IdealSheaf.IsCutOutOn`). If `ℐ(𝔙)` is an ideal of definition for the members `𝔙` of a covering
of `𝔛` by affine formal opens, then `ℐ` is an ideal of definition.

These are the ideal sheaves of the colimit criterion of Stacks 0AIW,
`FormalScheme.isFppfColimitOfThickenings_iff`. For an arbitrary ideal sheaf checking the covering
members is not enough (`not_forall_isIdealOfDefinitionOn_of_cover`), and the condition must then be
checked on the affine formal opens inside the covering members
(`IdealSheaf.isIdealOfDefinitionOn_of_cover_of_isFormalScheme`). Over an affine formal open inside
a covering member the condition is `IdealSheaf.isIdealOfDefinition_of_le_of_isCutOutOn`. -/
@[stacks 0AIW "it suffices to check the ideal-of-definition condition on the members of an affine \
open covering: for ideal sheaves cut out by their sections over the affine formal opens \
(IdealSheaf.IsCutOutOn), the class of the colimit criterion \
FormalScheme.isFppfColimitOfThickenings_iff; for an arbitrary ideal sheaf it is false \
(not_forall_isIdealOfDefinitionOn_of_cover)"]
theorem IdealSheaf.isIdealOfDefinitionOn_of_cover_of_isCutOutOn
    (hX : IsFormalScheme X) (I : IdealSheaf X)
    (hC : I.IsCutOutOn (IsAffineFormalOpen X)) (𝒰 : Set (Opens X))
    (h𝒰 : ∀ V ∈ 𝒰, IsAffineFormalOpen X V) (hcover : sSup 𝒰 = ⊤)
    (hI : ∀ V ∈ 𝒰, IsIdealOfDefinition (I.ideal V)) :
    I.IsIdealOfDefinitionOn (IsAffineFormalOpen X) := by
  exact I.isIdealOfDefinitionOn_of_cover_of_isFormalScheme hX 𝒰 hcover
    fun V hV _ hUV hU => isIdealOfDefinition_of_le_of_isCutOutOn_affine hX hC (h𝒰 V hV) hU hUV
      (hI V hV)

/-- **Stacks 0AIW, the fundamental-system condition may be checked on the members of an affine
open covering, for ideal sheaves cut out by their sections.** Let `𝔛` be a formal scheme à la EGA
and `{ℐ_λ}` a nonempty family of ideal sheaves, directed by inclusion, each cut out by its sections
over the affine formal opens. If over the members `𝔙` of a covering of `𝔛` by affine formal opens
the `ℐ_λ(𝔙)` are ideals of definition forming a neighbourhood basis of zero, then `{ℐ_λ}` is a
fundamental system of ideals of definition.

The family is indexed, as in the source, by a directed set (nonempty, by Stacks' definition of a
directed set), with `ℐ_μ ⊆ ℐ_λ` for `μ ≥ λ`; over an affine formal open inside a single covering
member no directedness is used (`hasBasis_of_le_of_isCutOutOn`). These are the families of the
colimit criterion `FormalScheme.isFppfColimitOfThickenings_iff`. For arbitrary ideal sheaves
checking the covering members is not enough
(`not_forall_isFundamentalSystemOfIdealsOfDefinitionOn_of_hasBasis_cover`). -/
@[stacks 0AIW "it suffices to check the fundamental-system condition on the members of an affine \
open covering: for a family indexed by a directed set, as in the source, of ideal sheaves cut out \
by their sections over the affine formal opens (IdealSheaf.IsCutOutOn), the class of the colimit \
criterion FormalScheme.isFppfColimitOfThickenings_iff; for arbitrary ideal sheaves it is false \
(not_forall_isFundamentalSystemOfIdealsOfDefinitionOn_of_hasBasis_cover)",
  ega "I 10.3.7" "more general"]
theorem isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_isCutOutOn
    (hX : IsFormalScheme X) (𝒮 : Set (IdealSheaf X))
    (hC : ∀ I ∈ 𝒮, I.IsCutOutOn (IsAffineFormalOpen X)) (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (𝒰 : Set (Opens X)) (h𝒰 : ∀ V ∈ 𝒰, IsAffineFormalOpen X V) (hcover : sSup 𝒰 = ⊤)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, IsIdealOfDefinition (I.ideal V))
    (hbasis : ∀ V ∈ 𝒰, (nhds (0 : (X.presheaf.obj (op V)).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal V : Set (X.presheaf.obj (op V)).α)) :
    IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X) := by
  have hdef : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → IsAffineFormalOpen X U →
      IsIdealOfDefinition (I.ideal U) := fun I hI V hV _ hUV hU =>
    isIdealOfDefinition_of_le_of_isCutOutOn_affine hX (hC I hI) (h𝒰 V hV) hU hUV (h𝒮 I hI V hV)
  exact isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_isFormalScheme hX 𝒮 hne hdir 𝒰
    hcover hdef fun V hV U hUV hU => hasBasis_of_le_of_isCutOutOn 𝒮
      (fun I hI => isCutOutOn_weak_of_isCutOutOn_affine hX (hC I hI))
      (h𝒰 V hV).isWeakAffineFormalOpen hU.isWeakAffineFormalOpen hUV
      (fun I hI => isWeakIdealOfDefinition_of_isIdealOfDefinition (hdef I hI V hV U hUV hU))
      (hbasis V hV)

end LocallyTopologicallyRingedSpace

end AlgebraicGeometry

end
