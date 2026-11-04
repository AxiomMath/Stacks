module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentDiscreteValuation

/-!
# The components of the special fibre of a modification are curves

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` and a modification `f : X ⟶ S = Spec(A)` with special fibre `X_s` — the discussion
following the situation records two facts about the irreducible components `C_1, …, C_r` of
`X_s`: each has dimension at most one, and, unless `f` is an isomorphism, each has dimension
exactly one. This file proves both.

## Main results

* `AlgebraicGeometry.IsModification.geometricallyConnected`: a modification of the spectrum of a
  normal domain has geometrically connected fibres ([Stacks, Tag 0AY8]).
* `AlgebraicGeometry.VanishingSituation.isIso_f_of_topologicalKrullDim_component_eq_zero`: if
  some `C_i` is a point then `f` is an isomorphism.
* `AlgebraicGeometry.VanishingSituation.topologicalKrullDim_component_eq_one_of_not_isIso`: if
  `f` is not an isomorphism then every `C_i` has dimension one.

## Implementation notes

The upper bound is the dimension formula [Stacks, Tag 0BAE] at the generic point `ξ_i` of
`C_i`: its correction term vanishes because `f` is birational, `dim 𝒪_{S, s} ≤ 2`, and
`dim 𝒪_{X, ξ_i} ≥ 1` because `ξ_i` is not the generic point of `X`; the transcendence degree of
`κ(ξ_i)` over `κ` is `dim C_i` by the chain lemma [Stacks, Tag 053V].

For the lower bound, the source argues through Stein factorization: `X_s` is connected
([Stacks, Tag 0AY8]), so if one of its components is a point then `X_s` is that point, `f` is
finite over a neighbourhood of `s` ([Stacks, Tag 02UP]) and hence everywhere since `S` is local,
and a finite birational morphism onto a normal integral scheme is an isomorphism
([Stacks, Tag 0AB1]). A component which is a point is a whole connected component because it
meets no other component: a point of `C_j` lying on the point `C_i` would make `C_i ⊆ C_j`.

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 02UP](https://stacks.math.columbia.edu/tag/02UP)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A modification of the spectrum of a normal domain has geometrically connected fibres.**
This is the second conclusion of [Stacks, Tag 0AY8]: the generic fibre of a birational morphism
is the spectrum of the function field of the base, so `H⁰` of the generic fibre is that field. -/
theorem IsModification.geometricallyConnected {A : Type u} [CommRing A] [IsNormalDomain A]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} (hf : IsModification f) :
    GeometricallyConnected f := by
  have hX : IsIntegral X := hf.source_isIntegral
  have hP : IsProper f := hf.isProper
  have hN : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hfib : IsIso (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational f hf.isBirational
  have hfibΓ : IsIso (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))).appTop := by
    have hc0 : IsIso (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))).c :=
      PresheafedSpace.c_isIso_of_iso
        (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))).toPshHom
    exact NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
  have hΓ : IsIso ((Scheme.ΓSpecIso
      ((Spec (.of A)).residueField (genericPoint (Spec (.of A))))).inv ≫
      (f.fiberToSpecResidueField (genericPoint (Spec (.of A)))).appTop) :=
    inferInstance
  have hgen : ∀ x : X, x ∈ genericPoints X → f x = genericPoint (Spec (.of A)) := by
    intro x hx
    have hmem := hf.isBirational.bijOn.mapsTo hx
    rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hmem
  exact Stacks.SteinFactorization.geometricallyConnected_of_isNormal f hgen hΓ

/-- An irreducible subset of a `T₀` space whose subspace topology has Krull dimension zero is a
single point. -/
theorem IsIrreducible.subsingleton_of_topologicalKrullDim_eq_zero {T : Type*} [TopologicalSpace T]
    [T0Space T] {s : Set T} (hs : IsIrreducible s) (h0 : topologicalKrullDim s = 0) :
    s.Subsingleton := by
  have : IrreducibleSpace s := Subtype.irreducibleSpace hs
  let top : IrreducibleCloseds s := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ s,
    isClosed_univ⟩
  have hmax : ∀ Z : IrreducibleCloseds s, Z = top := fun Z =>
    le_antisymm (fun _ _ => Set.mem_univ _)
      ((Order.krullDim_nonpos_iff_forall_isMax.mp h0.le Z) (fun _ _ => Set.mem_univ _))
  intro x hx y hy
  have hcl : ∀ z : s, closure ({z} : Set s) = Set.univ := fun z =>
    congrArg (fun Z : IrreducibleCloseds s => (Z : Set s))
      (hmax ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩)
  exact congrArg Subtype.val (Specializes.antisymm (x := (⟨x, hx⟩ : s)) (y := ⟨y, hy⟩)
    (specializes_iff_mem_closure.mpr (by simp [hcl]))
    (specializes_iff_mem_closure.mpr (by simp [hcl]))).eq

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-! ### The lower bound -/

/-- The special fibre of the modification is connected ([Stacks, Tag 0AY8]). -/
instance connectedSpace_specialFiber : ConnectedSpace V.specialFiber :=
  have := V.modification.geometricallyConnected
  inferInstance

/-- **A component of the special fibre which is a point is the whole special fibre.** The point
lies on no other component, since otherwise the component it forms would be contained in that
other one; so it is open in the special fibre as the complement of the finitely many other
components, and the special fibre is connected. -/
theorem eq_univ_of_topologicalKrullDim_component_eq_zero (i : Fin V.numberOfComponents)
    (h0 : topologicalKrullDim (V.component i) = 0) :
    V.component i = Set.univ := by
  have hirr := (V.component_mem_irreducibleComponents i).1
  have hsub : (V.component i).Subsingleton :=
    IsIrreducible.subsingleton_of_topologicalKrullDim_eq_zero hirr h0
  obtain ⟨x, hx⟩ := hirr.nonempty
  have hCi : V.component i = {x} := hsub.eq_singleton_of_mem hx
  have hnot : ∀ j, j ≠ i → x ∉ V.component j := by
    intro j hji hxj
    have hle : V.component i ≤ V.component j := by
      rw [hCi]
      exact Set.singleton_subset_iff.mpr hxj
    exact hji (V.component_injective (le_antisymm
      ((V.component_mem_irreducibleComponents i).2
        (V.component_mem_irreducibleComponents j).1 hle) hle))
  have hcover : ∀ y : V.specialFiber, ∃ j, y ∈ V.component j := by
    intro y
    obtain ⟨Z, hZ, hyZ⟩ := Set.mem_sUnion.mp
      ((sUnion_irreducibleComponents (X := V.specialFiber)).symm ▸ Set.mem_univ y)
    obtain ⟨j, rfl⟩ := V.exists_component_eq Z hZ
    exact ⟨j, hyZ⟩
  have hcompl : (V.component i)ᶜ = ⋃ j ∈ ({i}ᶜ : Set (Fin V.numberOfComponents)),
      V.component j := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    constructor
    · intro hy
      obtain ⟨j, hj⟩ := hcover y
      refine ⟨j, fun hji => hy (hji ▸ hj), hj⟩
    · rintro ⟨j, hji, hyj⟩ hyi
      rw [hCi, Set.mem_singleton_iff] at hyi
      exact hnot j hji (hyi ▸ hyj)
  have hclosed : IsClosed (V.component i)ᶜ := by
    rw [hcompl]
    exact (Set.toFinite _).isClosed_biUnion fun j _ =>
      isClosed_of_mem_irreducibleComponents _ (V.component_mem_irreducibleComponents j)
  have hclopen : IsClopen (V.component i) :=
    ⟨isClosed_of_mem_irreducibleComponents _ (V.component_mem_irreducibleComponents i),
      isClosed_compl_iff.mp hclosed⟩
  exact hclopen.eq_univ ⟨x, hx⟩

/-- **If a component of the special fibre is a point, the modification is an isomorphism.** The
special fibre is then a single point, so `f` is finite over a neighbourhood of the closed point
([Stacks, Tag 02UP]), which is all of the local base; a finite birational morphism onto a normal
integral scheme is an isomorphism ([Stacks, Tag 0AB1]). -/
theorem isIso_f_of_topologicalKrullDim_component_eq_zero (i : Fin V.numberOfComponents)
    (h0 : topologicalKrullDim (V.component i) = 0) : IsIso V.f := by
  have huniv := V.eq_univ_of_topologicalKrullDim_component_eq_zero i h0
  have hsub : (V.component i).Subsingleton :=
    IsIrreducible.subsingleton_of_topologicalKrullDim_eq_zero
      (V.component_mem_irreducibleComponents i).1 h0
  have hfib : (V.f ⁻¹' {V.closedPoint}).Finite := by
    have : Subsingleton V.specialFiber :=
      ⟨fun y z => hsub (huniv ▸ Set.mem_univ y) (huniv ▸ Set.mem_univ z)⟩
    exact Set.finite_coe_iff.mp ((V.f.fiberHomeo V.closedPoint).finite_iff.mp inferInstance)
  obtain ⟨W, hsW, hW⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton V.f
    V.closedPoint hfib
  have hWtop : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hsW
  have : IsFinite V.f := by
    subst hWtop
    have : IsIso (Scheme.Opens.ι (⊤ : V.base.Opens)) := V.base.topIso.isIso_hom
    have h1 : IsFinite ((⊤ : V.X.Opens).ι ≫ V.f) := by
      rw [show (⊤ : V.X.Opens) = V.f ⁻¹ᵁ ⊤ from rfl, ← morphismRestrict_ι]
      infer_instance
    have h2 : V.f = V.X.topIso.inv ≫ ((⊤ : V.X.Opens).ι ≫ V.f) := by
      rw [← Category.assoc, show (⊤ : V.X.Opens).ι = V.X.topIso.hom from rfl,
        Iso.inv_hom_id, Category.id_comp]
    rw [h2]
    infer_instance
  have hN : IsNormal V.base :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed V.A)
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal V.f V.modification.isBirational

/-- **Unless the modification is an isomorphism, every component of the special fibre has
dimension one.** This is the observation following Situation [Stacks, Tag 0AX8]. -/
theorem topologicalKrullDim_component_eq_one_of_not_isIso (hf : ¬ IsIso V.f)
    (i : Fin V.numberOfComponents) :
    topologicalKrullDim (V.component i) = 1 := by
  have : Nonempty (V.component i) :=
    (V.component_mem_irreducibleComponents i).1.nonempty.to_subtype
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (V.component i) := by
    obtain ⟨x⟩ := ‹Nonempty (V.component i)›
    have : Nonempty (IrreducibleCloseds (V.component i)) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  have h1 : topologicalKrullDim (V.component i) ≤ 1 := V.topologicalKrullDim_component_le_one i
  have hne : topologicalKrullDim (V.component i) ≠ 0 := fun h =>
    hf (V.isIso_f_of_topologicalKrullDim_component_eq_zero i h)
  obtain ⟨e, he⟩ : ∃ e : ℕ∞, (e : WithBot ℕ∞) = topologicalKrullDim (V.component i) :=
    WithBot.ne_bot_iff_exists.mp (fun hbot => by simp [hbot] at h0)
  rw [← he] at hne h1 ⊢
  have hele : e ≤ 1 := by exact_mod_cast h1
  have hene : e ≠ 0 := by exact_mod_cast hne
  exact_mod_cast le_antisymm hele (Order.one_le_iff_ne_zero.mpr hene)

end VanishingSituation

end AlgebraicGeometry

end
