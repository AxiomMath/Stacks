module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationIsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentDiscreteValuation
public import StacksFrontier.Topology.Dimension.KrullSeparation

/-!
# The dimension of a component of the special fibre

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` and a modification `f : X ⟶ S = Spec(A)` with the irreducible components
`C_1, …, C_r` of the special fibre `X_s` enumerated — Section 54.7 of the source records, in the
discussion following Situation 54.7.1, that `dim C_i = 1` for `i = 1, …, r`. That record has two
halves, and only one of them is a consequence of the Situation.

The upper bound `dim C_i ≤ 1` is: the dimension formula [Stacks, Tag 0BAE] at the generic point
`ξ_i` of `C_i` bounds `dim 𝒪_{X, ξ_i} + trdeg_κ κ(ξ_i)` by `dim 𝒪_{S, s} = 2`, its correction
term vanishing because `f` is birational; `dim 𝒪_{X, ξ_i} ≥ 1` because `ξ_i` is not the generic
point of `X`; and `trdeg_κ κ(ξ_i)` is `dim C_i` by [Stacks, Tag 053V]. No hypothesis beyond
Situation 0AX8 enters, and `topologicalKrullDim_component_le_one` is unconditional.

The lower bound is not a consequence of the Situation, and this is where the source's own
exclusion enters: for `f` the identity of `Spec(A)` — a legal modification — the special fibre is
the closed point, `r = 1`, and `dim C_1 = 0`. Section 54.7 sets that case aside, having observed
that a zero-dimensional special fibre makes the modification finite and hence an isomorphism:
"We will discard this uninteresting case and we conclude that $\dim (C_i) = 1$". That exclusion
is a standing assumption of the section, and `one_le_topologicalKrullDim_component` carries it as
`hfib : 1 ≤ dim X_s`, which transcribes that sentence rather than assuming anything the source
does not.

`hfib` is the only hypothesis. The source carries the bound from the fibre to each of its
components through the geometric connectedness of `X_s`, which it derives from the Stein
factorization ([Stacks, Tag 0AY8], second conclusion) and which this library has only over
[Stacks, Tag 0G7X]; that step is replaced here by one which needs no connectedness. A
zero-dimensional component is a point open in `X_s`, hence a quasi-finite point of `f`, and a
modification of the spectrum of a normal local domain with such a point in its closed fibre is an
isomorphism — `AlgebraicGeometry.IsModification.isIso_of_isOpen_singleton_fiber`, which is
Zariski's main theorem read over a local base. The special fibre is then that single point, of
dimension zero, which `hfib` forbids.

## Main results

The elided prefix is `AlgebraicGeometry.VanishingSituation`.

* `topologicalKrullDim_component_le_one`: `dim C_i ≤ 1`, with no hypothesis beyond Situation
  0AX8.
* `one_le_topologicalKrullDim_component`: `1 ≤ dim C_i`, for a special fibre of dimension at
  least one.
* `topologicalKrullDim_component_eq_one`: the observation following Situation 54.7.1,
  `dim C_i = 1`, from that one hypothesis on the special fibre.

## Implementation notes

The lower bound is proved by contraposition. A component of dimension zero is the closure of its
generic point and a single point, because a second point of it would be a nontrivial
specialization inside it and the space of a scheme is Kolmogorov; a single point which is an
irreducible component lies on no other component, by maximality, so it is the complement of the
union of the others and therefore open as well as closed. Open in `X_s`, it makes the
modification an isomorphism and the whole special fibre that one point
(`AlgebraicGeometry.IsModification.subsingleton_fiber_of_isOpen_singleton_fiber`), whose
topological Krull dimension is zero. This covers `r = 1` and `r ≥ 2` alike, which is why no
connectedness of the fibre is needed.

## References

* [Stacks Project, Tag 0AX7](https://stacks.math.columbia.edu/tag/0AX7)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
* [Stacks Project, Tag 053V](https://stacks.math.columbia.edu/tag/053V)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
-/

@[expose] public section

open Set TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The natural number a cardinal is sent to by `Cardinal.toNat` is at most the extended natural
number it is sent to by `Cardinal.toENat`: the two agree below `ℵ₀`, and above it the second is
`⊤`. -/
private theorem toNat_le_toENat (c : Cardinal) : (Cardinal.toNat c : ℕ∞) ≤ Cardinal.toENat c := by
  rcases lt_or_ge c Cardinal.aleph0 with h | h
  · obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.mp h
    simp
  · simp [Cardinal.toENat_eq_top.mpr h]

namespace VanishingSituation

/-- **A component of the special fibre has dimension at most one.** This is the half of the
observation following Situation 0AX8 that the Situation itself gives: by [Stacks, Tag 053V] the
dimension of the component is the transcendence degree of the residue field at its generic point
`ξ_i` over `κ`, the dimension formula [Stacks, Tag 0BAE] bounds that transcendence degree plus
`dim 𝒪_{X, ξ_i}` by `dim 𝒪_{S, s} = 2` — the correction term of the formula vanishing because
`f` is birational and `X` integral — and `dim 𝒪_{X, ξ_i} ≥ 1` because `ξ_i` is not the generic
point of `X`. -/
theorem topologicalKrullDim_component_le_one (V : VanishingSituation.{u})
    (i : Fin V.numberOfComponents) :
    topologicalKrullDim (V.component i) ≤ 1 := by
  set ξ := componentGenericPoint V i with hξ
  let _ : Algebra (V.base.residueField (V.f ξ)) (V.X.residueField ξ) :=
    (V.f.residueFieldMap ξ).hom.toAlgebra
  have h053 := natTrdegFiber_eq_topologicalKrullDim_closure V.f ξ
  rw [hξ, topologicalKrullDim_closure_asFiber_componentGenericPoint V i] at h053
  have hbridge : ((natTrdegFiber V.f ξ : ℕ) : ℕ∞) ≤ residueFieldTranscendenceDegree V.f ξ := by
    rw [show residueFieldTranscendenceDegree V.f ξ = Cardinal.toENat (Algebra.trdeg
      (V.base.residueField (V.f ξ)) (V.X.residueField ξ)) from rfl,
      natTrdegFiber_eq_toNat_trdeg_residueField]
    exact toNat_le_toENat _
  have hformula := ringKrullDim_stalk_add_residueFieldTranscendenceDegree_le V.f ξ
  rw [genericResidueFieldTranscendenceDegreeAt_eq_zero V.f V.modification.isBirational ξ]
    at hformula
  have hnat : natTrdegFiber V.f ξ ≤ 1 := by
    by_contra hsmall
    have h2 : (2 : ℕ∞) ≤ residueFieldTranscendenceDegree V.f ξ :=
      le_trans (by exact_mod_cast Nat.succ_le_of_lt (not_le.mp hsmall)) hbridge
    have habsurd : (3 : WithBot ℕ∞) ≤ 2 :=
      calc (3 : WithBot ℕ∞) = 1 + 2 := by norm_num
        _ ≤ ringKrullDim (V.X.presheaf.stalk ξ) +
              ((residueFieldTranscendenceDegree V.f ξ : ℕ∞) : WithBot ℕ∞) :=
            add_le_add (Stacks.LocalCohomology.one_le_ringKrullDim_stalk_of_ne_genericPoint _
              (componentGenericPoint_ne_genericPoint V i))
              (by simpa using WithBot.coe_le_coe.mpr h2)
        _ ≤ ringKrullDim (V.base.presheaf.stalk (V.f ξ)) + ((0 : ℕ∞) : WithBot ℕ∞) := hformula
        _ ≤ 2 + ((0 : ℕ∞) : WithBot ℕ∞) := add_le_add (V.ringKrullDim_stalk_base_le_two _) le_rfl
        _ = 2 := by norm_num
    norm_num at habsurd
  rw [← h053]
  exact_mod_cast hnat

/-- **A component of the special fibre has dimension at least one**, provided the special fibre
is not the zero-dimensional one that Section 54.7 discards.

The hypothesis is needed and it is the source's own: for `f` an isomorphism — which Situation
0AX8 permits — the special fibre is a single point and the conclusion fails, and that is the case
the source sets aside, in the sentence `hfib` transcribes. Nothing else is assumed. A
zero-dimensional component of the fibre is a point lying on no other component, hence open in the
fibre, and a modification of the spectrum of a normal local domain with a point open in its
closed fibre is an isomorphism, so the whole fibre is that point and has dimension zero. The
source instead rules this out by the geometric connectedness of `X_s`, which it derives from the
Stein factorization ([Stacks, Tag 0AY8], second conclusion); that is not needed here. -/
theorem one_le_topologicalKrullDim_component (V : VanishingSituation.{u})
    (hfib : 1 ≤ topologicalKrullDim V.specialFiber)
    (i : Fin V.numberOfComponents) :
    1 ≤ topologicalKrullDim (V.component i) := by
  have hC : V.component i ∈ irreducibleComponents V.specialFiber :=
    V.component_mem_irreducibleComponents i
  have hclosed : ∀ j, IsClosed (V.component j) := fun j =>
    isClosed_of_mem_irreducibleComponents _ (V.component_mem_irreducibleComponents j)
  have hgen : IsGenericPoint hC.1.genericPoint (V.component i) :=
    hC.1.isGenericPoint_genericPoint (hclosed i)
  set η := hC.1.genericPoint
  by_cases hsingle : ∃ y ∈ V.component i, y ≠ η
  · -- A second point of the component is a nontrivial specialization of its generic point.
    obtain ⟨y, hy, hyne⟩ := hsingle
    have hsub : (⟨η, hgen.mem⟩ : V.component i) ⤳ ⟨y, hy⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp (hgen.specializes hy)
    exact one_le_topologicalKrullDim_of_specializes_of_ne hsub fun hEq =>
      hyne (congrArg Subtype.val hEq).symm
  · -- Otherwise the component is a point, which is then open as well as closed.
    exfalso
    push Not at hsingle
    have hηnot : ∀ j, j ≠ i → η ∉ V.component j := by
      intro j hji hηj
      have hsub : V.component i ⊆ V.component j :=
        (hgen.mem_closed_set_iff (hclosed j)).mp hηj
      have hrev : V.component j ⊆ V.component i :=
        hC.2 (V.component_mem_irreducibleComponents j).1 hsub
      exact hji (V.component_injective (Set.Subset.antisymm hsub hrev)).symm
    have hcover : ∀ x : V.specialFiber, ∃ j, x ∈ V.component j := by
      intro x
      have hx : x ∈ ⋃₀ irreducibleComponents (V.specialFiber : Type u) := by
        rw [sUnion_irreducibleComponents]
        exact Set.mem_univ x
      obtain ⟨Z, hZ, hxZ⟩ := hx
      obtain ⟨j, hj⟩ := V.exists_component_eq Z hZ
      exact ⟨j, hj ▸ hxZ⟩
    have hTclosed : IsClosed (⋃ j ∈ {j | j ≠ i}, V.component j) :=
      (Set.toFinite _).isClosed_biUnion fun j _ => hclosed j
    have hTcompl : (⋃ j ∈ {j | j ≠ i}, V.component j)ᶜ = {η} := by
      refine Set.Subset.antisymm (fun x hx => ?_) (Set.singleton_subset_iff.mpr ?_)
      · obtain ⟨j, hj⟩ := hcover x
        by_cases hji : j = i
        · exact hsingle x (hji ▸ hj)
        · exact absurd (Set.mem_iUnion₂.mpr ⟨j, hji, hj⟩) hx
      · intro ht
        obtain ⟨j, hji, hj⟩ := Set.mem_iUnion₂.mp ht
        exact hηnot j hji hj
    have hopen : IsOpen ({η} : Set V.specialFiber) := hTcompl ▸ hTclosed.isOpen_compl
    -- An isolated point of the special fibre makes the modification an isomorphism, so the
    -- fibre is that one point and has dimension zero.
    have : Subsingleton V.specialFiber :=
      V.modification.subsingleton_fiber_of_isOpen_singleton_fiber η hopen
    rw [topologicalKrullDim] at hfib
    obtain ⟨A, B, hAB⟩ := Order.one_le_krullDim_iff.mp hfib
    exact hAB.ne (IrreducibleCloseds.ext (A.2.nonempty.eq_univ.trans B.2.nonempty.eq_univ.symm))

/-- **The observation following Situation 54.7.1: every irreducible component of the special
fibre has dimension one** — in its corrected form, which excludes the zero-dimensional special
fibre that Section 54.7 discards. The upper bound needs no hypothesis at all. -/
theorem topologicalKrullDim_component_eq_one (V : VanishingSituation.{u})
    (hfib : 1 ≤ topologicalKrullDim V.specialFiber)
    (i : Fin V.numberOfComponents) :
    topologicalKrullDim (V.component i) = 1 :=
  le_antisymm (V.topologicalKrullDim_component_le_one i)
    (V.one_le_topologicalKrullDim_component hfib i)

end VanishingSituation

end AlgebraicGeometry

end
