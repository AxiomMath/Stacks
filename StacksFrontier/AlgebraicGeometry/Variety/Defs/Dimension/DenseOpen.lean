module

public import StacksFrontier.AlgebraicGeometry.NodalContraction.CentreFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A dense open subset of a scheme of finite type over a field has the full dimension

Let `T` be a scheme locally of finite type over a field whose underlying space is Noetherian,
and let `U ⊆ T` be a dense open subset. Then `dim T ≤ dim U` (and so `dim T = dim U`).

The local dimension of `T` at a point `x` is the dimension of an irreducible component `Z`
through `x`
(`AlgebraicGeometry.exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt`,
[Stacks, Tag 0A21]). The generic point `η` of `Z` lies in `U`: the complement of the other
(finitely many) components is a nonempty open subset of `Z`, which the dense `U` meets, and every
point of `Z` is a specialization of `η`. Applying the same fact at `η`, whose only component is
`Z`, the local dimension at `η` is `dim Z`, and the local dimension of `T` at a point of the open
`U` is the local dimension of `U` there, which is at most `dim U`.

## Main results

* `IsGenericPoint.mem_of_isOpen_of_dense_of_mem_irreducibleComponents`
* `AlgebraicGeometry.topologicalKrullDim_le_of_isOpen_of_dense`
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The generic point of an irreducible component of a Noetherian space lies in every dense open
subset. -/
theorem _root_.IsGenericPoint.mem_of_isOpen_of_dense_of_mem_irreducibleComponents {T : Type*}
    [TopologicalSpace T] [NoetherianSpace T]
    {Z : Set T} (hZ : Z ∈ irreducibleComponents T) {η : T} (hη : IsGenericPoint η Z)
    {U : Set T} (hU : IsOpen U) (hd : Dense U) : η ∈ U := by
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := T)
  let O : Set T := (⋃₀ (irreducibleComponents T \ {Z}))ᶜ
  have hO : IsOpen O := by
    show IsOpen (⋃₀ (irreducibleComponents T \ {Z}))ᶜ
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hcl : closure O = Z := closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z hZ
  have hOne : O.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h, closure_empty] at hcl
    exact hZ.1.nonempty.ne_empty hcl.symm
  obtain ⟨u, huO, huU⟩ := hd.inter_open_nonempty O hO hOne
  have huZ : u ∈ Z := hcl ▸ subset_closure huO
  exact (hη.specializes huZ).mem_open hU huU

/-- **A dense open subset of a Noetherian scheme locally of finite type over a field has the
full dimension**: `dim T ≤ dim U`. -/
@[ega "IV 10.6.2" "partial", ega "IV 5.2.5" "special case"]
theorem topologicalKrullDim_le_of_isOpen_of_dense (k : Type u) [Field k] (T : Scheme.{u})
    (f : T ⟶ Spec (.of k)) [LocallyOfFiniteType f] [NoetherianSpace T] (U : Set T)
    (hU : IsOpen U) (hd : Dense U) :
    topologicalKrullDim T ≤ topologicalKrullDim U := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x ↦ ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  obtain ⟨Z, hZ, -, hdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k T f x
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηU : η ∈ U := IsGenericPoint.mem_of_isOpen_of_dense_of_mem_irreducibleComponents hZ hη hU hd
  obtain ⟨Z', hZ', hηZ', hdim'⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k T f η
  have hsub : Z ⊆ Z' := by
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hηZ')
      (isClosed_of_mem_irreducibleComponents Z' hZ')
  have hZZ' : Z = Z' := le_antisymm hsub (hZ.2 hZ'.1 hsub)
  rw [← hdim, hZZ', hdim']
  have h := hU.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq (⟨η, hηU⟩ : U)
  exact h.le.trans (topologicalKrullDimAt_le_topologicalKrullDim _)

end AlgebraicGeometry

end
