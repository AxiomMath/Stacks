module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionComponentStalks
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Curves.NodalCurveComponents
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGenusNormalization
public import StacksFrontier.AlgebraicGeometry.Curves.NodalVectorFieldsEquivalence
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothVectorFields
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.TricanonicalEmbedding
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.GlobalSections

/-!
# Vector fields on a nodal curve without rational tails or bridges

Let `k` be an algebraically closed field and `X` a proper connected at-worst-nodal curve over `k`
of genus at least two, with no rational tails and no rational bridges. For an irreducible
component `Z` of `X`, with reduced structure `C` and normalization `C̃`, let `T_Z` be the set of
points of `C̃` lying over nodes of `X`. This file proves the combinatorial heart of
[Stacks, Tag 0E69]:

  `3 ≤ 2 g(C̃) + #T_Z`.

So a vector field on `C̃` fixing the points of `T_Z` vanishes, by
`Stacks.Curves.SheafDerivationOf.encard_setOf_fixes_le` once `deg Ω_{C̃} = 2 g(C̃) - 2`.

## The argument

Every node of `X` on `Z` has a point of `C̃` above it, and a node lying on no other component has
two (`AlgebraicGeometry.encard_normalizationFiber_eq_two_of_isNode`). If the inequality fails then
`g(C̃) ≤ 1` and `#T_Z ≤ 2 - 2 g(C̃)`:

* if `Z` meets no other component, then `Z = X` (connectedness) and `X` has at most
  `#T_Z / 2 ≤ 1 - g(C̃)` nodes, so `g(X) ≤ g(C̃) + 1 - g(C̃) = 1` by
  `AlgebraicGeometry.genus_le_genus_normalization_add_ncard_singularLocus`;
* otherwise `g(C̃) = 0`, every node on `Z` lies on another component, so `C` is smooth and of
  genus zero, and `C` meets the closure `X'` of its complement in one or two reduced `k`-points:
  `C` is a rational tail or a rational bridge.

## Main results

* `Stacks.Curves.three_le_two_mul_genus_add_encard_nodePoints`: `3 ≤ 2 g(C̃) + #T_Z`.
* `Stacks.Curves.exists_restrictOpens_fixes_and_eq_zero`: a vector field on `X` gives, on each
  `C̃_Z`, a vector field fixing `T_Z`, and `D = 0` once all of these vanish.
* `Stacks.Curves.isRationalTail_or_isRationalBridge_of_ncard`,
  `Stacks.Curves.finrank_globalSections_intersection_eq_ncard`,
  `Stacks.Curves.genus_le_of_reducedComponent_eq_univ`: the three geometric inputs of the case
  analysis.

## References

* [Stacks Project, Tag 0E69](https://stacks.math.columbia.edu/tag/0E69)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The structure morphism of the reduced irreducible component `Z` of a `k`-scheme. -/
abbrev componentStructure (Z : irreducibleComponents X) :
    X.reducedComponent Z ⟶ Spec (.of k) :=
  X.reducedComponentι Z ≫ (X ↘ Spec (.of k))

/-- The points of the normalization of the reduced component `Z` lying over nodes of `X`. -/
abbrev nodePoints [LocallyOfFiniteType (X ↘ Spec (.of k))] (Z : irreducibleComponents X) :
    Set (normalizationSchemeOverField k (componentStructure (k := k) Z)) :=
  {z | IsNode k X (X.reducedComponentι Z
    (normalizationOverField k (componentStructure (k := k) Z) z))}

/-- Three distinct elements of a set make its cardinality at least three. -/
theorem three_le_encard_of_mem {α : Type*} {s : Set α} {a b c : α} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.encard := by
  have h3 : ({a, b, c} : Set α).encard = 3 := Set.encard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [← h3]
  exact Set.encard_le_encard (by
    rintro x (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hc)

section Component

variable [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- **Every point of a component lies under a point of its normalization.** -/
theorem exists_normalizationOverField_eq_of_mem (Z : irreducibleComponents X) {x : X}
    (hx : x ∈ (Z : Set X)) :
    ∃ z : normalizationSchemeOverField k (componentStructure (k := k) Z),
      X.reducedComponentι Z (normalizationOverField k (componentStructure (k := k) Z) z) = x := by
  rw [← X.range_reducedComponentι Z] at hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := (Scheme.surjective_normalization (X.reducedComponent Z)
    (finite_irreducibleComponents_of_locallyOfFiniteType k
      (componentStructure (k := k) Z))).surj y
  exact ⟨z, by rw [hz]⟩

variable (k) in
include k in
/-- A reduced irreducible component of an equidimensional one-dimensional scheme of finite type
over a field has dimension one. -/
theorem topologicalKrullDim_reducedComponent_eq_one (hequi : Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (Z : irreducibleComponents X) :
    topologicalKrullDim (X.reducedComponent Z) = 1 := by
  let h : X.reducedComponent Z ≃ₜ Set.range (X.reducedComponentι Z).base :=
    (IsPreimmersion.isEmbedding (X.reducedComponentι Z)).toHomeomorph
  calc
    topologicalKrullDim (X.reducedComponent Z) =
        topologicalKrullDim (Set.range (X.reducedComponentι Z).base) :=
      IsHomeomorph.topologicalKrullDim_eq _ h.isHomeomorph
    _ = topologicalKrullDim (Z : Set X) :=
      IsHomeomorph.topologicalKrullDim_eq _
        (Homeomorph.setCongr (X.range_reducedComponentι Z)).isHomeomorph
    _ = 1 := topologicalKrullDim_irreducibleComponent_eq_one (X ↘ Spec (.of k)) hequi hdim _ Z.2

/-- A node of `X` lying on a component and off the closure of its complement is a node of the
reduced component. -/
private theorem isNode_reducedComponent_of_notMem [IsAlgClosed k] [IsReduced X]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1) (Z : irreducibleComponents X)
    (y : X.reducedComponent Z)
    (hx' : X.reducedComponentι Z y ∉ ((complementaryCurveIdeal
      (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).support : Set X))
    (hnode : IsNode k X (X.reducedComponentι Z y)) :
    @IsNode k _ (X.reducedComponent Z) ⟨componentStructure (k := k) Z⟩ y := by
  set C := Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z)
  let V : X.Opens := ⟨((complementaryCurveIdeal C).support : Set X)ᶜ,
    (complementaryCurveIdeal C).support.isClosed.isOpen_compl⟩
  have hV : (V : Set X) ⊆ Set.range C.subschemeι.base := by
    intro w hw
    rw [C.range_subschemeι]
    by_contra hwC
    exact hw (compl_support_subset_support_complementaryCurveIdeal C hwC)
  exact isNode_comp_of_isClosedImmersion_of_mem_opens (X ↘ Spec (.of k)) hdim C.subschemeι
    (topologicalKrullDim_reducedComponent_eq_one k hequi hdim Z) V hV y hx' hnode

/-- **A node lying on a single component has two points of the normalization of that component
above it.** Off the closure `X'` of the complement of `Z` the component agrees with `X`, so the
node is a node of the component, over which its normalization has two points. -/
theorem exists_ne_mem_nodePoints_of_notMem [IsAlgClosed k] [IsReduced X]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1) (Z : irreducibleComponents X)
    {x : X} (hxZ : x ∈ (Z : Set X)) (hnode : IsNode k X x)
    (hx' : x ∉ ((complementaryCurveIdeal
      (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).support : Set X)) :
    ∃ z₁ ∈ nodePoints (k := k) Z, ∃ z₂ ∈ nodePoints (k := k) Z, z₁ ≠ z₂ ∧
      X.reducedComponentι Z (normalizationOverField k (componentStructure (k := k) Z) z₁) = x ∧
      X.reducedComponentι Z (normalizationOverField k (componentStructure (k := k) Z) z₂) = x := by
  have hCdim := topologicalKrullDim_reducedComponent_eq_one k hequi hdim Z
  have hxr := hxZ
  rw [← X.range_reducedComponentι Z] at hxr
  obtain ⟨y, rfl⟩ := hxr
  have hnodeC := isNode_reducedComponent_of_notMem hequi hdim Z y hx' hnode
  let : (X.reducedComponent Z).Over (Spec (.of k)) := ⟨componentStructure (k := k) Z⟩
  have : LocallyOfFiniteType (X.reducedComponent Z ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (componentStructure (k := k) Z))
  have h2 := encard_normalizationFiber_eq_two_of_isNode hCdim
    (finite_irreducibleComponents_of_locallyOfFiniteType k (componentStructure (k := k) Z))
    y hnodeC
  obtain ⟨z₁, z₂, hne, heq⟩ := Set.encard_eq_two.mp h2
  have hz₁ : z₁ ∈ ({z₁, z₂} : Set _) := Set.mem_insert _ _
  have hz₂ : z₂ ∈ ({z₁, z₂} : Set _) := Set.mem_insert_of_mem _ rfl
  rw [← heq] at hz₁ hz₂
  have hz₁' : normalizationOverField k (componentStructure (k := k) Z) z₁ = y := hz₁
  have hz₂' : normalizationOverField k (componentStructure (k := k) Z) z₂ = y := hz₂
  refine ⟨z₁, ?_, z₂, ?_, hne, by rw [hz₁'], by rw [hz₂']⟩
  · show IsNode k X _
    rwa [hz₁']
  · show IsNode k X _
    rwa [hz₂']

/-- **A singular point of a component is a node of `X` lying on no other component.** -/
theorem isNode_and_notMem_of_mem_singularLocus_reducedComponent [IsAlgClosed k] [IsReduced X]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (Z : irreducibleComponents X)
    (y : X.reducedComponent Z) (hy : y ∈ singularLocus (X.reducedComponent Z)) :
    IsNode k X (X.reducedComponentι Z y) ∧ X.reducedComponentι Z y ∉ ((complementaryCurveIdeal
      (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).support : Set X) :=
  isNode_and_notMem_of_mem_singularLocus_subscheme hequi hdim hnodal _
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace _)
    (topologicalKrullDim_reducedComponent_eq_one k hequi hdim Z) y hy

omit [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- **The reduced component of a proper `k`-curve is a proper curve.** -/
theorem isCurve_componentStructure [IsProper (X ↘ Spec (.of k))] (hequi : Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (Z : irreducibleComponents X) :
    IsCurve k (componentStructure (k := k) Z) :=
  { toIsVariety := {}
    topologicalKrullDim_eq_one := topologicalKrullDim_reducedComponent_eq_one k hequi hdim Z }

/-- **If a component is the whole curve, the genus of the curve is at most the genus of the
normalization of the component plus the number of singular points of the component.** -/
theorem genus_le_of_reducedComponent_eq_univ [IsAlgClosed k] [IsProper (X ↘ Spec (.of k))]
    [IsReduced X] (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (Z : irreducibleComponents X)
    (hZ : (Z : Set X) = Set.univ) :
    (genus (X ↘ Spec (.of k)) : ℤ) ≤
      genus (normalizationOverField k (componentStructure (k := k) Z) ≫
        componentStructure (k := k) Z) + (singularLocus (X.reducedComponent Z)).ncard := by
  have : Surjective (X.reducedComponentι Z) := ⟨fun x => by
    have hx : x ∈ Set.range (X.reducedComponentι Z) := by
      rw [X.range_reducedComponentι Z, hZ]; trivial
    exact hx⟩
  have : IsIso (X.reducedComponentι Z) :=
    isIso_of_isClosedImmersion_of_surjective (X.reducedComponentι Z)
  have hgen : genus (componentStructure (k := k) Z) = genus (X ↘ Spec (.of k)) :=
    genus_comp_iso_eq k (X ↘ Spec (.of k)) (asIso (X.reducedComponentι Z))
  let : (X.reducedComponent Z).Over (Spec (.of k)) := ⟨componentStructure (k := k) Z⟩
  have : IsCurve k (X.reducedComponent Z ↘ Spec (.of k)) :=
    isCurve_componentStructure hequi hdim Z
  have : IsProper (X.reducedComponent Z ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (componentStructure (k := k) Z))
  have h := genus_le_genus_normalization_add_ncard_singularLocus k (X.reducedComponent Z)
    fun y hy => by
      obtain ⟨hnode, hnot⟩ :=
        isNode_and_notMem_of_mem_singularLocus_reducedComponent hequi hdim hnodal Z y hy
      exact isNode_reducedComponent_of_notMem hequi hdim Z y hnot hnode
  rw [← hgen]
  exact h

/-- The support of the ideal of the reduced component `Z` is `Z`. -/
private theorem support_vanishingIdeal_componentCloseds (Z : irreducibleComponents X) :
    ((Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z)).support : Set X) = Z := by
  rw [← Scheme.IdealSheafData.range_subschemeι]; exact X.range_reducedComponentι Z

omit [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- **The scheme-theoretic intersection of a component with the closure of its complement is a
finite set of reduced `k`-points**: its ring of global sections has dimension the number of
points of `Z ∩ X'`. It is reduced by [Stacks, Tag 0E38], finite over `k` being proper of
dimension zero, and a reduced scheme finite over an algebraically closed field has `dim_k Γ`
points. -/
theorem finrank_globalSections_intersection_eq_ncard [IsAlgClosed k]
    [IsProper (X ↘ Spec (.of k))] [IsReduced X] (hequi : Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    (Z : irreducibleComponents X) :
    letI : Algebra k Γ((intersectionWithComplementaryCurveIdeal
        (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ((intersectionWithComplementaryCurveIdeal
        (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).subschemeι ≫
          (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    Module.finrank k Γ((intersectionWithComplementaryCurveIdeal
        (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).subscheme, ⊤) =
      ((Z : Set X) ∩ ((complementaryCurveIdeal
        (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).support : Set X)).ncard := by
  set C := Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z)
  set I := intersectionWithComplementaryCurveIdeal C
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  obtain ⟨ι, K, hK, _, -, e, -⟩ := exists_iso_sigma_spec_intersectionWithComplementaryCurve
    hequi hdim hnodal C (TopologicalSpace.Equidimensional.of_preirreducibleSpace _)
    (topologicalKrullDim_reducedComponent_eq_one k hequi hdim Z)
  have : IsReduced I.subscheme := by
    have hsum : IsReduced (∐ fun i : ι => Spec (.of (K i))) := by
      let 𝒰 := sigmaOpenCover (fun i : ι => Spec (.of (K i)))
      have hcomp : ∀ i : 𝒰.I₀, IsReduced (𝒰.X i) := by
        intro i
        let : Field (K i) := hK i
        show IsReduced (Spec (.of (K i)))
        infer_instance
      exact IsReduced.of_openCover _ 𝒰
    exact isReduced_of_isOpenImmersion e.inv
  have : IsFinite (I.subschemeι ≫ (X ↘ Spec (.of k))) :=
    isFinite_of_isProper_of_topologicalKrullDim_le_zero _
      (topologicalKrullDim_intersectionWithComplementaryCurve_le_zero hdim.le C)
  rw [finrank_globalSections_eq_natCard_of_isReduced k (I.subschemeι ≫ (X ↘ Spec (.of k))),
    ← Set.ncard_range_of_injective I.subschemeι.isClosedEmbedding.injective, I.range_subschemeι]
  show ((C ⊔ complementaryCurveIdeal C).support : Set X).ncard = _
  rw [Scheme.IdealSheafData.support_sup]
  show ((C.support : Set X) ∩ _).ncard = _
  rw [support_vanishingIdeal_componentCloseds]

/-- **A smooth component of genus zero meeting the rest of the curve in one or two points is a
rational tail or a rational bridge.** Let `Z` be a proper component of `X` whose reduced
structure `C` is smooth (has no singular points) and whose normalization has genus zero. Then
`C` has genus zero, `C ∩ X'` is reduced with `#(Z ∩ X')` points, and the recognition lemmas of
[Stacks, Tag 0E3J] and [Stacks, Tag 0E3P] apply. -/
theorem isRationalTail_or_isRationalBridge_of_ncard [IsAlgClosed k]
    [IsProper (X ↘ Spec (.of k))] [IsReduced X] (hequi : Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    (Z : irreducibleComponents X) (hZ : (Z : Set X) ≠ Set.univ)
    (hsing : singularLocus (X.reducedComponent Z) = ∅)
    (hg0 : genus (normalizationOverField k (componentStructure (k := k) Z) ≫
      componentStructure (k := k) Z) = 0) :
    (((Z : Set X) ∩ ((complementaryCurveIdeal
        (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).support : Set X)).ncard = 1 →
      IsRationalTail k X (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))) ∧
    (((Z : Set X) ∩ ((complementaryCurveIdeal
        (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))).support : Set X)).ncard = 2 →
      IsRationalBridge k X (Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z))) := by
  set C := Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z)
  set I := intersectionWithComplementaryCurveIdeal C
  set fC := componentStructure (k := k) Z
  have hCdim := topologicalKrullDim_reducedComponent_eq_one k hequi hdim Z
  have : IsCurve k fC := isCurve_componentStructure hequi hdim Z
  have : IsProperVariety k fC := ⟨⟩
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fC.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Stacks.AlgebraicGeometry.UnitsNormalProper.bijective_structMap k fC)
  -- the genus of `C` is zero
  have hgC : genus fC = 0 := by
    let : (X.reducedComponent Z).Over (Spec (.of k)) := ⟨fC⟩
    have : IsCurve k (X.reducedComponent Z ↘ Spec (.of k)) := inferInstanceAs (IsCurve k fC)
    have : IsProper (X.reducedComponent Z ↘ Spec (.of k)) := inferInstanceAs (IsProper fC)
    have h := genus_le_genus_normalization_add_ncard_singularLocus k (X.reducedComponent Z)
      fun y hy => by rw [hsing] at hy; exact hy.elim
    change (genus fC : ℤ) ≤ genus (normalizationOverField k fC ≫ fC) + _ at h
    rw [hg0, hsing, Set.ncard_empty] at h
    omega
  have hne : Nonempty (complementaryCurve C) := by
    refine nonempty_complementaryCurve_of_support_ne_univ C ?_
    rw [support_vanishingIdeal_componentCloseds]; exact hZ
  have hs : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by simp
  have hf : fC ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) =
      C.subschemeι ≫ (X ↘ Spec (.of k)) := by rw [hs, Category.comp_id]
  have heq : Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I) ≫ fC =
      I.subschemeι ≫ (X ↘ Spec (.of k)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have key := finrank_globalSections_intersection_eq_ncard hequi hdim hnodal Z
  rw [← heq] at key
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · exact isRationalTail_of_finrank_globalSections_intersection_eq_one hdim.le C hCdim hne k fC hf
      (key.trans h1) hgC
  · exact isRationalBridge_of_finrank_globalSections_intersection_eq_two hdim.le C hCdim hne k fC
      hf (key.trans h2) hgC

/-- **The combinatorial heart of [Stacks, Tag 0E69].** Let `X` be a proper connected nodal curve
over an algebraically closed field, of genus at least two, without rational tails or bridges.
For every irreducible component `Z`, with normalization `C̃` of genus `gN` and with `T_Z` the
points of `C̃` over nodes of `X`, one has `3 ≤ 2 gN + #T_Z`. -/
theorem three_le_two_mul_genus_add_encard_nodePoints [IsAlgClosed k]
    [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C) (Z : irreducibleComponents X) :
    3 ≤ 2 * (genus (normalizationOverField k (componentStructure (k := k) Z) ≫
      componentStructure (k := k) Z) : ℕ∞) + (nodePoints (k := k) Z).encard := by
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hequi : Equidimensional X :=
    equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one hdim
  set C := Scheme.IdealSheafData.vanishingIdeal (X.componentCloseds Z)
  set gN := genus (normalizationOverField k (componentStructure (k := k) Z) ≫
    componentStructure (k := k) Z)
  set T := nodePoints (k := k) Z
  set ι := X.reducedComponentι Z
  set n := normalizationOverField k (componentStructure (k := k) Z)
  have hCsupp : (C.support : Set X) = (Z : Set X) := support_vanishingIdeal_componentCloseds Z
  have hCdim := topologicalKrullDim_reducedComponent_eq_one k hequi hdim Z
  have hCeq : Equidimensional C.subscheme :=
    TopologicalSpace.Equidimensional.of_preirreducibleSpace _
  by_contra hlt
  push Not at hlt
  -- points of `T` over nodes
  have hT1 : ∀ x, x ∈ (Z : Set X) → IsNode k X x → ∃ z ∈ T, ι (n z) = x := fun x hxZ hx => by
    obtain ⟨z, hz⟩ := exists_normalizationOverField_eq_of_mem (k := k) Z hxZ
    exact ⟨z, by change IsNode k X _; rw [hz]; exact hx, hz⟩
  have hdist : ∀ z z' : _, ι (n z) ≠ ι (n z') → z ≠ z' := fun z z' h hzz => h (by rw [hzz])
  have hT3 : ¬ 3 ≤ T.encard := fun h3 => by
    have : T.encard ≤ 2 * (gN : ℕ∞) + T.encard := le_add_self
    exact absurd (h3.trans this) (not_le.mpr hlt)
  -- a node off `X'` and another node give three points of `T`
  have hthree : ∀ x y, x ∈ (Z : Set X) → IsNode k X x →
      x ∉ ((complementaryCurveIdeal C).support : Set X) →
      y ∈ (Z : Set X) → IsNode k X y → y ≠ x → False := fun x y hxZ hx hx' hyZ hy hyx => by
    obtain ⟨z₁, hz₁, z₂, hz₂, hne, he₁, he₂⟩ :=
      exists_ne_mem_nodePoints_of_notMem hequi hdim Z hxZ hx hx'
    obtain ⟨z₃, hz₃, he₃⟩ := hT1 y hyZ hy
    exact hT3 (three_le_encard_of_mem hz₁ hz₂ hz₃ hne
      (hdist _ _ (by rw [he₁, he₃]; exact hyx.symm))
      (hdist _ _ (by rw [he₂, he₃]; exact hyx.symm)))
  by_cases hA : ((Z : Set X) ∩ ((complementaryCurveIdeal C).support : Set X)) = ∅
  · -- `Z` is the whole curve
    have hZu : (Z : Set X) = Set.univ := by
      by_contra hZ
      obtain ⟨w⟩ := nonempty_intersectionWithComplementaryCurve_of_connectedSpace C
        (by rw [hCsupp]; exact Z.2.1.nonempty) (by rw [hCsupp]; exact hZ)
      have hw : (intersectionWithComplementaryCurveIdeal C).subschemeι w ∈
          ((intersectionWithComplementaryCurveIdeal C).support : Set X) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w, rfl⟩
      change _ ∈ ((C ⊔ complementaryCurveIdeal C).support : Set X) at hw
      rw [Scheme.IdealSheafData.support_sup] at hw
      change _ ∈ (C.support : Set X) ∩ _ at hw
      rw [hCsupp, hA] at hw
      exact hw
    have hgen := genus_le_of_reducedComponent_eq_univ hequi hdim hnodal Z hZu
    -- `#Sing(C) + gN ≤ 1`
    have hsing : ((singularLocus (X.reducedComponent Z)).ncard : ℤ) + gN ≤ 1 := by
      by_cases hne : (singularLocus (X.reducedComponent Z)).Nonempty
      · obtain ⟨y, hy⟩ := hne
        obtain ⟨hx, hx'⟩ :=
          isNode_and_notMem_of_mem_singularLocus_reducedComponent hequi hdim hnodal Z y hy
        have hyZ : ι y ∈ (Z : Set X) := X.reducedComponentι_mem Z y
        obtain ⟨z₁, hz₁, z₂, hz₂, hne, -, -⟩ :=
          exists_ne_mem_nodePoints_of_notMem hequi hdim Z hyZ hx hx'
        have h2 : 2 ≤ T.encard := by
          rw [← Set.encard_pair hne]
          exact Set.encard_le_encard (by
            rintro w (rfl | rfl)
            · exact hz₁
            · exact hz₂)
        have hg0 : gN = 0 := by
          by_contra h0
          have : (2 : ℕ∞) ≤ 2 * (gN : ℕ∞) := by
            have : (1 : ℕ∞) ≤ gN := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
            calc (2 : ℕ∞) = 2 * 1 := by norm_num
              _ ≤ 2 * (gN : ℕ∞) := by gcongr
          have := add_le_add this h2
          exact absurd hlt (not_lt.mpr (le_trans (by norm_num) this))
        have hle : (singularLocus (X.reducedComponent Z)).encard ≤ 1 := by
          refine Set.encard_le_one_iff.mpr fun a b ha hb => ?_
          by_contra hab
          obtain ⟨hxa, hxa'⟩ :=
            isNode_and_notMem_of_mem_singularLocus_reducedComponent hequi hdim hnodal Z a ha
          obtain ⟨hxb, -⟩ :=
            isNode_and_notMem_of_mem_singularLocus_reducedComponent hequi hdim hnodal Z b hb
          exact hthree (ι a) (ι b) (X.reducedComponentι_mem Z a) hxa hxa'
            (X.reducedComponentι_mem Z b) hxb
            (fun h => hab (ι.isClosedEmbedding.injective h).symm)
        have hn1 := (Set.encard_le_coe_iff_finite_ncard_le.mp hle).2
        rw [hg0]
        push_cast
        exact_mod_cast hn1
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
        have : gN ≤ 1 := by
          by_contra h1
          push Not at h1
          have : (4 : ℕ∞) ≤ 2 * (gN : ℕ∞) := by
            have : (2 : ℕ∞) ≤ gN := by exact_mod_cast h1
            calc (4 : ℕ∞) = 2 * 2 := by norm_num
              _ ≤ 2 * (gN : ℕ∞) := by gcongr
          exact absurd hlt (not_lt.mpr (le_trans (by norm_num) (this.trans le_self_add)))
        push_cast
        simpa using this
    have : (2 : ℤ) ≤ genus (X ↘ Spec (.of k)) := by exact_mod_cast hg
    omega
  · -- `Z` meets the rest of the curve
    obtain ⟨a, haZ, ha'⟩ := Set.nonempty_iff_ne_empty.mpr hA
    have haC : a ∈ (C.support : Set X) := hCsupp ▸ haZ
    have ha : IsNode k X a :=
      isNode_of_mem_support_of_mem_support_complementaryCurveIdeal hequi hdim hnodal C hCeq
        hCdim haC ha'
    obtain ⟨-, -, D, -, -, hD, hDC, -, -⟩ :=
      exists_irreducibleComponents_of_mem_support_of_mem_support_complementaryCurveIdeal hequi
        hdim hnodal C hCeq hCdim haC ha'
    have hZne : (Z : Set X) ≠ Set.univ := fun h => hDC (by rw [hCsupp, h]; exact Set.subset_univ _)
    obtain ⟨za, hza, -⟩ := hT1 a haZ ha
    have hg0 : gN = 0 := by
      by_contra h0
      have h1 : 1 ≤ T.encard := Set.one_le_encard_iff_nonempty.mpr ⟨za, hza⟩
      have : (2 : ℕ∞) ≤ 2 * (gN : ℕ∞) := by
        have : (1 : ℕ∞) ≤ gN := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        calc (2 : ℕ∞) = 2 * 1 := by norm_num
          _ ≤ 2 * (gN : ℕ∞) := by gcongr
      have := add_le_add this h1
      exact absurd hlt (not_lt.mpr (le_trans (by norm_num) this))
    have hsing : singularLocus (X.reducedComponent Z) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      obtain ⟨hx, hx'⟩ :=
        isNode_and_notMem_of_mem_singularLocus_reducedComponent hequi hdim hnodal Z y hy
      exact hthree (ι y) a (X.reducedComponentι_mem Z y) hx hx' haZ ha
        (fun h => hx' (h ▸ ha'))
    have hA3 : ((Z : Set X) ∩ ((complementaryCurveIdeal C).support : Set X)).encard ≤ 2 := by
      by_contra h3
      push Not at h3
      obtain ⟨t, hts, ht⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt h3)
      obtain ⟨b₁, b₂, b₃, h12, h13, h23, rfl⟩ := Set.encard_eq_three.mp (by rw [ht]; norm_num)
      have hb : ∀ b ∈ ({b₁, b₂, b₃} : Set X), ∃ z ∈ T, ι (n z) = b := fun b hb' => by
        obtain ⟨hbZ, hb'⟩ := hts hb'
        exact hT1 b hbZ (isNode_of_mem_support_of_mem_support_complementaryCurveIdeal hequi hdim
          hnodal C hCeq hCdim (hCsupp ▸ hbZ) hb')
      obtain ⟨z₁, hz₁, e₁⟩ := hb b₁ (Set.mem_insert _ _)
      obtain ⟨z₂, hz₂, e₂⟩ := hb b₂ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      obtain ⟨z₃, hz₃, e₃⟩ := hb b₃ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
      exact hT3 (three_le_encard_of_mem hz₁ hz₂ hz₃ (hdist _ _ (by rw [e₁, e₂]; exact h12))
        (hdist _ _ (by rw [e₁, e₃]; exact h13)) (hdist _ _ (by rw [e₂, e₃]; exact h23)))
    have hfin := Set.finite_of_encard_le_coe hA3
    have hpos : 0 < ((Z : Set X) ∩ ((complementaryCurveIdeal C).support : Set X)).ncard :=
      (Set.ncard_pos hfin).mpr ⟨a, haZ, ha'⟩
    have hle2 : ((Z : Set X) ∩ ((complementaryCurveIdeal C).support : Set X)).ncard ≤ 2 := by
      exact_mod_cast (Set.encard_le_coe_iff_finite_ncard_le.mp hA3).2
    obtain ⟨htl, hbr⟩ :=
      isRationalTail_or_isRationalBridge_of_ncard hequi hdim hnodal Z hZne hsing hg0
    rcases (show ((Z : Set X) ∩ ((complementaryCurveIdeal C).support : Set X)).ncard = 1 ∨
        ((Z : Set X) ∩ ((complementaryCurveIdeal C).support : Set X)).ncard = 2 by omega)
      with h1 | h2
    · exact htail _ (htl h1)
    · exact hbridge _ (hbr h2)

/-! ### From `X` to the components of its normalization -/

/-- **Reduction of [Stacks, Tag 0E69] to the components of the normalization.** Let `X` be a
proper one-dimensional at-worst-nodal curve over an algebraically closed field, and write its
normalization as the disjoint union of the normalizations `C̃_Z` of its reduced components
([Stacks, Tag 0CDV]). A vector field `D` on `X` extends to a vector field `D'` on the
normalization fixing every point over a node ([Stacks, Tag 0E68]); its restriction to `C̃_Z`
fixes every point of `T_Z`, and if all of these restrictions vanish then `D = 0`. -/
theorem exists_restrictOpens_fixes_and_eq_zero [IsAlgClosed k]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    ∃ (e : (∐ fun Z : irreducibleComponents X =>
          normalizationSchemeOverField k (componentStructure (k := k) Z)) ≅
        normalizationSchemeOverField k (X ↘ Spec (.of k)))
      (_ : e.hom ≫ normalizationOverField k (X ↘ Spec (.of k)) =
        Limits.Sigma.desc fun Z : irreducibleComponents X =>
          normalizationOverField k (componentStructure (k := k) Z) ≫ X.reducedComponentι Z),
      ∀ D : SheafDerivation k X, ∃ D' : SheafDerivationOf
          (normalizationOverField k (X ↘ Spec (.of k)) ≫ (X ↘ Spec (.of k))),
        (∀ (Z : irreducibleComponents X) (z) (_ : z ∈ nodePoints (k := k) Z),
          ∃ hz : IsClosed ({z} : Set _),
            (D'.restrictOpens (Limits.Sigma.ι _ Z ≫ e.hom)).Fixes z hz) ∧
        ((∀ Z : irreducibleComponents X, D'.restrictOpens (Limits.Sigma.ι _ Z ≫ e.hom) = 0) →
          D = 0) := by
  set p := X ↘ Spec (.of k)
  set hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  obtain ⟨e, he⟩ := X.exists_iso_normalizationScheme_sigma_reducedComponent hX
  refine ⟨e, he, fun D => ?_⟩
  obtain ⟨D', ⟨hc, hfix⟩, -⟩ := (NodalVectorFields.range_branchPair k X hdim hnodal).1 D
  have hS := not_exists_isIso_normalization_restrict_iff k X hX hdim hnodal
  -- the images of the points of the components
  have hpt : ∀ (Z : irreducibleComponents X) (z : normalizationSchemeOverField k
      (componentStructure (k := k) Z)),
      Scheme.normalization X hX ((Limits.Sigma.ι _ Z ≫ e.hom) z) =
        X.reducedComponentι Z (normalizationOverField k (componentStructure (k := k) Z) z) :=
    fun Z z => by
      rw [← Scheme.Hom.comp_apply, Category.assoc]
      show (Limits.Sigma.ι _ Z ≫ e.hom ≫ normalizationOverField k p) z = _
      rw [he, Limits.Sigma.ι_desc, Scheme.Hom.comp_apply]
  refine ⟨D', fun Z z hz => ?_, fun h0 => ?_⟩
  · set j := Limits.Sigma.ι _ Z ≫ e.hom
    have hnode : IsNode k X (Scheme.normalization X hX (j z)) := by rw [hpt]; exact hz
    obtain ⟨hy, hfy⟩ := hfix (j z) ((hS (j z)).mpr hnode)
    have hzcl : IsClosed ({z} : Set _) := by
      have : (j.base ⁻¹' {j z} : Set _) = {z} := by
        ext w
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => j.isOpenEmbedding.injective h, fun h => h ▸ rfl⟩
      rw [← this]
      exact hy.preimage j.continuous
    exact ⟨hzcl, D'.fixes_restrictOpens j z hzcl hy hfy⟩
  · have hD' : D' = 0 := by
      refine D'.eq_zero_of_restrictOpens_eq_zero (fun Z => Limits.Sigma.ι _ Z ≫ e.hom)
        (fun y => ?_) h0
      obtain ⟨⟨Z, z⟩, hz⟩ := (sigmaMk _).surjective (e.inv y)
      refine ⟨Z, z, ?_⟩
      rw [sigmaMk_mk] at hz
      show (Limits.Sigma.ι _ Z ≫ e.hom) z = y
      rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl
    refine SheafDerivationOf.ext' fun U s => ?_
    have h1 := hc U s
    rw [hD', SheafDerivationOf.zero_onSections] at h1
    exact app_normalization_injective X hX U (h1.symm.trans (map_zero _).symm)

end Component

end Stacks.Curves

end
