module

public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Local
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective

/-!
# Global sections of an invertible module as rational functions

Let `X` be a normal locally Noetherian integral scheme, `L` an invertible `𝒪_X`-module and `s` a
regular meromorphic section of `L`, with generic value `v ∈ L_η`, a basis of the one-dimensional
`K`-vector space `L_η` (`K` the function field). Every global section `t` of `L` has a coordinate
`ρ(t) ∈ K`, `t_η = ρ(t) v`. This file shows that `ρ` identifies `Γ(X, L)` with the space of
`a ∈ K` such that `a v` lies in `L_ξ` at every point `ξ` of codimension one, i.e. such that
`ord_ξ(a) + ord_ξ(s) ≥ 0` along every prime divisor:

* `ρ` is additive, `Γ(X, 𝒪_X)`-linear and injective (an invertible module is torsion free);
* `ρ(t)` satisfies the condition, the germs of `t` lying in the stalks of `L`;
* conversely every such `a` is `ρ(t)` for a global section `t`: multiplication by `a v` is a
  map of generic stalks `𝒪_η → L_η` carrying `𝒪_ξ` into `L_ξ` in codimension one, so it extends
  to a morphism `𝒪_X → L` by [Stacks, Tag 0AY7]
  (`AlgebraicGeometry.exists_hom_of_mapsTo_stalkSpecializes`), whose value on `1` is `t`.

On a curve this is the classical description `Γ(C, 𝒪(D)) = L(D) = {f : div f + D ≥ 0}`.

## Main definitions

* `Stacks.Zeta.genericCoord`: the coordinate `ρ`.

## Main results

* `Stacks.Zeta.mem_range_stalkSpecializes_iff`: the stalk condition is the order condition.
* `Stacks.Zeta.genericCoord_injective`, `Stacks.Zeta.genericCoord_add`,
  `Stacks.Zeta.genericCoord_smul`, `Stacks.Zeta.genericCoord_mem`,
  `Stacks.Zeta.exists_genericCoord_eq`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Zeta

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)

attribute [local instance] isQuasicoherent_of_isInvertible

/-- The generic value of the meromorphic section `s`, a basis of `L_η`. -/
abbrev genericValue : L.presheaf.stalk (genericPoint X) := meromorphicGenericValue X L s

include hs

omit [IsLocallyNoetherian X] in
/-- The generic value of a regular meromorphic section is nonzero. -/
theorem genericValue_ne_zero : genericValue X L s ≠ 0 :=
  meromorphicGenericValue_ne_zero X L s hs

/-- The `K`-linear isomorphism `K ≃ L_η`, `z ↦ z v`, given by the basis `v` of `L_η`. -/
def genericBasisEquiv : X.functionField ≃ₗ[X.functionField] L.presheaf.stalk (genericPoint X) :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton X.functionField (L.presheaf.stalk (genericPoint X))
      (genericValue X L s))
    (isStalkBasis_genericPoint_of_ne_zero X L (genericValue_ne_zero X L s hs))

omit [IsLocallyNoetherian X] in
/-- The isomorphism `K ≃ L_η` sends `z` to `z v`. -/
theorem genericBasisEquiv_apply (z : X.functionField) :
    genericBasisEquiv X L s hs z = z • genericValue X L s := rfl

/-- **The stalk condition is the order condition.** For `a ≠ 0` and a prime divisor `Z` with
generic point `ξ`, the vector `a v` comes from `L_ξ` exactly when
`ord_ξ(a) + ord_Z(s) ≥ 0`. -/
theorem mem_range_stalkSpecializes_iff (Z : PrimeDivisor X)
    [IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)] {a : X.functionField}
    (ha : a ≠ 0) :
    a • genericValue X L s ∈ Set.range (L.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ Z.genericPoint))) ↔
      0 ≤ X.ord a Z.genericPoint + orderOfVanishingMeromorphic X L s hs Z := by
  have hZ1 := PrimeDivisor.coheight_genericPoint Z
  obtain ⟨m, hm, b, hb⟩ := (orderOfVanishingMeromorphicData X L s hs Z).2.1
  have hval : genericValue X L s = b • L.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ Z.genericPoint)) m :=
    meromorphicGenericValue_eq X L s _ hb
  have hord : orderOfVanishingMeromorphic X L s hs Z = X.ord b Z.genericPoint :=
    (orderOfVanishingMeromorphicData X L s hs Z).2.2 m hm b hb
  obtain ⟨hb0, hm0⟩ : b ≠ 0 ∧ L.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ Z.genericPoint)) m ≠ 0 := by
    have := genericValue_ne_zero X L s hs
    rw [hval] at this
    exact smul_ne_zero_iff.mp this
  rw [hord, ← Scheme.ord_mul ha hb0, hval, smul_smul]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp (hm ▸ Submodule.mem_top (x := n))
    rw [Stacks.ModuleStalkSpecialization.stalkSpecializes_smul L _ r m] at hn
    have hr : X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes (Set.mem_univ Z.genericPoint)) r = a * b :=
      smul_left_injective _ hm0 hn
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [map_zero] at hr
      exact mul_ne_zero ha hb0 hr.symm
    rw [← hr, ← algebraMap_functionField_eq_stalkSpecializes]
    exact Stacks.BombieriStepanov.ord_algebraMap_nonneg hZ1 hr0
  · intro h
    obtain ⟨r, hr⟩ := Stacks.BombieriStepanov.exists_algebraMap_eq_of_ord_nonneg hZ1 h
    refine ⟨r • m, ?_⟩
    rw [Stacks.ModuleStalkSpecialization.stalkSpecializes_smul L _ r m,
      ← algebraMap_functionField_eq_stalkSpecializes, hr]

/-- The coordinate `ρ(t) ∈ K` of a global section `t` of `L` against the generic value of `s`:
`t_η = ρ(t) v`. -/
def genericCoord (t : Γ(L, ⊤)) : X.functionField :=
  (genericBasisEquiv X L s hs).symm (L.presheaf.germ ⊤ (genericPoint X) trivial t)

omit [IsLocallyNoetherian X] in
/-- The generic germ of a global section `t` is `ρ(t) v`. -/
theorem genericCoord_spec (t : Γ(L, ⊤)) :
    L.presheaf.germ ⊤ (genericPoint X) trivial t =
      genericCoord X L s hs t • genericValue X L s :=
  ((genericBasisEquiv X L s hs).apply_symm_apply _).symm

omit [IsLocallyNoetherian X] in
/-- The coordinate `ρ` is additive. -/
theorem genericCoord_add (t t' : Γ(L, ⊤)) :
    genericCoord X L s hs (t + t') = genericCoord X L s hs t + genericCoord X L s hs t' := by
  rw [genericCoord, map_add, map_add]
  rfl

omit [IsLocallyNoetherian X] in
/-- The coordinate `ρ` is `Γ(X, 𝒪_X)`-linear: `ρ(r t)` is the generic germ of `r` times `ρ(t)`. -/
theorem genericCoord_smul (r : Γ(X, ⊤)) (t : Γ(L, ⊤)) :
    genericCoord X L s hs (r • t) =
      X.presheaf.germ ⊤ (genericPoint X) trivial r * genericCoord X L s hs t := by
  rw [genericCoord, Stacks.ModuleStalk.germ_smul L (genericPoint X) ⊤ trivial r t, map_smul]
  rfl

/-- **The coordinate is injective**: a global section `t` of `L` is determined by `ρ(t)`. -/
theorem genericCoord_injective : Function.Injective (genericCoord X L s hs) := by
  intro t t' h
  have hG : IsTorsionFree L := isTorsionFree_of_isReflexive L (isReflexive_of_isInvertible X L)
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have hgen : L.presheaf.germ ⊤ (genericPoint X) trivial (t - t') = 0 := by
    rw [map_sub, genericCoord_spec X L s hs t, genericCoord_spec X L s hs t', h, sub_self]
  exact sub_eq_zero.mp (hG ⊤ (t - t') (((torsion_section_tfae X L ⊤ (t - t')).out 3 2).mp hgen))

/-- **The coordinate of a global section satisfies the order condition** along every prime
divisor. -/
theorem genericCoord_mem (t : Γ(L, ⊤)) (Z : PrimeDivisor X)
    [IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint)] :
    genericCoord X L s hs t = 0 ∨
      0 ≤ X.ord (genericCoord X L s hs t) Z.genericPoint +
        orderOfVanishingMeromorphic X L s hs Z := by
  by_cases h0 : genericCoord X L s hs t = 0
  · exact Or.inl h0
  refine Or.inr ((mem_range_stalkSpecializes_iff X L s hs Z h0).1 ⟨L.presheaf.germ ⊤
    Z.genericPoint trivial t, ?_⟩)
  rw [← genericCoord_spec X L s hs t]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

/-- **Every function satisfying the order condition is the coordinate of a global section**: on
a normal `X`, if `a = 0` or `ord_Z(a) + ord_Z(s) ≥ 0` for every prime divisor `Z`, then
`a = ρ(t)` for some global section `t` of `L`. -/
theorem exists_genericCoord_eq [IsNormal X]
    (hdvr : ∀ Z : PrimeDivisor X, IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint))
    (a : X.functionField)
    (ha : ∀ Z : PrimeDivisor X, a = 0 ∨
      0 ≤ X.ord a Z.genericPoint + orderOfVanishingMeromorphic X L s hs Z) :
    ∃ t : Γ(L, ⊤), genericCoord X L s hs t = a := by
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹_›
  have hLcoh : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  have hOcoh : (Stacks.Divisors.structureModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
  set T : (Stacks.Divisors.structureModule X).presheaf.stalk (genericPoint X) →ₗ[X.functionField]
      L.presheaf.stalk (genericPoint X) :=
    (LinearMap.toSpanSingleton X.functionField _ (a • genericValue X L s)).comp
      (genericStructStalkEquiv X).toLinearMap with hTdef
  obtain ⟨p, hp⟩ := exists_hom_of_mapsTo_stalkSpecializes X L
    (Stacks.Divisors.structureModule X) (isReflexive_of_isInvertible X L) T (by
      rintro x hdim - ⟨n, rfl⟩
      have hx : coheight x = 1 := by
        rw [ringKrullDim_stalk_eq_coheight] at hdim
        exact WithBot.coe_injective hdim
      obtain ⟨Z, rfl⟩ : ∃ Z : PrimeDivisor X, Z.genericPoint = x :=
        ⟨PrimeDivisor.ofCoheightOne x hx, PrimeDivisor.genericPoint_ofCoheightOne x hx⟩
      have := hdvr Z
      have hcompat : T ((Stacks.Divisors.structureModule X).presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes (Set.mem_univ Z.genericPoint)) n) =
          X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
            (Set.mem_univ Z.genericPoint)) (structStalkLinearEquiv X _ n) •
            (a • genericValue X L s) := by
        rw [hTdef, LinearMap.comp_apply, LinearEquiv.coe_coe,
          genericStructStalkEquiv_stalkSpecializes]
        rfl
      rw [hcompat]
      by_cases ha0 : a = 0
      · rw [ha0, zero_smul, smul_zero]
        exact ⟨0, map_zero _⟩
      obtain ⟨m, hm⟩ := (mem_range_stalkSpecializes_iff X L s hs Z ha0).2
        ((ha Z).resolve_left ha0)
      refine ⟨structStalkLinearEquiv X _ n • m, ?_⟩
      rw [Stacks.ModuleStalkSpecialization.stalkSpecializes_smul L _ _ m, hm])
  refine ⟨Scheme.Modules.Hom.app p ⊤ (1 : Γ(X, ⊤)), ?_⟩
  have hgerm := (hp _).symm.trans (stalkMapOfHom_germ p (genericPoint X) ⊤ trivial (1 : Γ(X, ⊤)))
  set g := TopCat.Presheaf.germ (C := Ab.{u})
    (Stacks.Divisors.structureModule X).val.presheaf ⊤ (genericPoint X) trivial (1 : Γ(X, ⊤))
  have h1 : genericStructStalkEquiv X g = 1 := by
    have := structStalkLinearEquiv_germ X (genericPoint X) ⊤ trivial (1 : Γ(X, ⊤))
    rw [map_one] at this
    exact this
  have hT1 : T g = a • genericValue X L s := by
    show genericStructStalkEquiv X _ • (a • genericValue X L s) = _
    rw [h1, one_smul]
  rw [hT1] at hgerm
  have hfinal : (genericBasisEquiv X L s hs).symm (a • genericValue X L s) = a :=
    (genericBasisEquiv X L s hs).symm_apply_apply a
  rw [hgerm] at hfinal
  exact hfinal

end Stacks.Zeta

end
