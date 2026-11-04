module

public import StacksFrontier.AlgebraicGeometry.Chow.Codimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineComponents
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct

/-!
# Normal schemes are locally equidimensional

A locally Noetherian normal scheme satisfies the three equivalent conditions of Stacks 0FE3 for
*every* integer-valued function on its points. The reason is that such a scheme is a disjoint
union of integral schemes, so each of its irreducible components is one of the summands and is
open; grouping the summands by the value of the function at their generic points produces the
decomposition asked for by condition (1).

## Main results

* `Stacks.Chow.HasDimensionDecomposition.of_isNormal`,
  `Stacks.Chow.IsLocallyPureDimensional.of_isNormal`,
  `Stacks.Chow.IsLocallyEquidimensional.of_isNormal` — the three conditions of Stacks 0FE3 on a
  locally Noetherian normal scheme.

## Implementation notes

The source states the conclusion for the relative dimension function of a morphism to a base in
the Chow situation. Its proof uses nothing about that function, so the statements here are for an
arbitrary `δ : X → ℤ`; the Chow situation enters only through
`Stacks.Chow.relativeDimension` at the point of use.

The decomposition of Stacks 033N is an isomorphism with a categorical coproduct, which is
transported to a homeomorphism with the sigma type of the summands. The irreducible components
of a sigma type of irreducible spaces are the summands, and the generic point of a summand is
the generic point of that irreducible space; the same holds after restricting the index set,
which is the form needed for the pieces of the decomposition.

## References

* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- In a sigma type of irreducible sober spaces restricted to a set of indices, an irreducible
component is one of the summands, and its generic point is the generic point of that summand. -/
private theorem exists_eq_sigmaMk_genericPoint {ι : Type*} (Y : ι → Type*)
    [∀ i, TopologicalSpace (Y i)] [∀ i, IrreducibleSpace (Y i)] [∀ i, QuasiSober (Y i)]
    [∀ i, T0Space (Y i)] (I : Set ι) [T0Space {p : Σ i, Y i // p.1 ∈ I}]
    (Z : Set {p : Σ i, Y i // p.1 ∈ I})
    (hZ : Z ∈ irreducibleComponents {p : Σ i, Y i // p.1 ∈ I})
    (ξ : {p : Σ i, Y i // p.1 ∈ I}) (hξ : IsGenericPoint ξ Z) :
    ∃ i ∈ I, (ξ : Σ i, Y i) = ⟨i, genericPoint (Y i)⟩ := by
  classical
  let i := (ξ : Σ i, Y i).1
  have hi : i ∈ I := ξ.2
  let F : Set {p : Σ i, Y i // p.1 ∈ I} := {p | (p : Σ i, Y i).1 = i}
  have hFopen : IsOpen F :=
    (isOpen_sigma_fst_preimage ({i} : Set ι)).preimage continuous_subtype_val
  have hFclosed : IsClosed F := isOpen_compl_iff.mp
    ((isOpen_sigma_fst_preimage ({i}ᶜ : Set ι)).preimage continuous_subtype_val)
  have hZsub : Z ⊆ F := by
    intro z hz
    by_contra hzi
    obtain ⟨w, -, hwF, hwFc⟩ := hZ.1.2 F Fᶜ hFopen hFclosed.isOpen_compl
      ⟨ξ, hξ.mem, rfl⟩ ⟨z, hz, hzi⟩
    exact hwFc hwF
  let f : Y i → {p : Σ i, Y i // p.1 ∈ I} := fun y ↦ ⟨⟨i, y⟩, hi⟩
  have hf : Continuous f := continuous_sigmaMk.subtype_mk _
  have himage : f '' (Set.univ : Set (Y i)) = F := by
    ext p
    constructor
    · rintro ⟨y, -, rfl⟩
      exact rfl
    · intro hp
      obtain ⟨⟨j, y⟩, hI⟩ := p
      obtain rfl : j = i := hp
      exact ⟨y, Set.mem_univ _, rfl⟩
  have hFirr : IsIrreducible F := himage ▸
    (IrreducibleSpace.isIrreducible_univ (Y i)).image f hf.continuousOn
  have hZeq : Z = F := Set.Subset.antisymm hZsub (hZ.2 hFirr hZsub)
  have hη : IsGenericPoint (⟨⟨i, genericPoint (Y i)⟩, hi⟩ :
      {p : Σ i, Y i // p.1 ∈ I}) F := by
    have hpoint := (genericPoint_spec (Y i)).image hf
    rwa [himage, hFclosed.closure_eq] at hpoint
  exact ⟨i, hi, congrArg Subtype.val ((hZeq ▸ hξ : IsGenericPoint ξ F).eq hη)⟩

/-- **Stacks 0FE3.** A locally Noetherian normal scheme decomposes into open and closed
subschemes on whose irreducible components any given integer-valued function is constant at the
generic points, the constant being the index of the piece. -/
@[stacks 0FE3 "normal_case"]
theorem HasDimensionDecomposition.of_isNormal (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsNormal X] (δ : X → ℤ) : HasDimensionDecomposition δ := by
  classical
  obtain ⟨ι, Y, -, hInt, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct_integral_normal X).mp inferInstance
  let (i : ι) : IsIntegral (Y i) := hInt i
  let h : X ≃ₜ (Σ i, Y i) := e.hom.homeomorph.trans (AlgebraicGeometry.sigmaMk Y).symm
  let I : ℤ → Set ι := fun n ↦ {i | δ (h.symm ⟨i, genericPoint (Y i)⟩) = n}
  let U : ℤ → X.Opens := fun n ↦
    ⟨h ⁻¹' (Sigma.fst ⁻¹' I n), (isOpen_sigma_fst_preimage (I n)).preimage h.continuous⟩
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · intro m n hmn
    refine disjoint_iff_inf_le.2 fun x hx ↦ ?_
    exact absurd ((hx.1 : δ (h.symm ⟨(h x).1, genericPoint (Y (h x).1)⟩) = m).symm.trans hx.2) hmn
  · refine le_antisymm le_top fun x _ ↦ Opens.mem_iSup.2 ?_
    exact ⟨δ (h.symm ⟨(h x).1, genericPoint (Y (h x).1)⟩), rfl⟩
  · intro n Z hZ ξ hξ
    let eU : U n ≃ₜ {p : Σ i, Y i // p.1 ∈ I n} := h.subtype fun _ ↦ Iff.rfl
    let : T0Space {p : Σ i, Y i // p.1 ∈ I n} := eU.t0Space
    have hZ' : eU '' Z ∈ irreducibleComponents {p : Σ i, Y i // p.1 ∈ I n} :=
      Homeomorph.image_mem_irreducibleComponents eU hZ
    have hξ' : IsGenericPoint (eU ξ) (eU '' Z) := by
      rw [← (eU.isClosedMap _ (isClosed_of_mem_irreducibleComponents Z hZ)).closure_eq]
      exact hξ.image eU.continuous
    obtain ⟨i, hi, hpoint⟩ :=
      exists_eq_sigmaMk_genericPoint (fun i ↦ (Y i : Type u)) (I n) _ hZ' (eU ξ) hξ'
    have hpoint' : h (ξ : X) = ⟨i, genericPoint (Y i)⟩ := hpoint
    calc δ (ξ : X) = δ (h.symm (h (ξ : X))) := by simp
      _ = δ (h.symm ⟨i, genericPoint (Y i)⟩) := by rw [hpoint']
      _ = n := hi

/-- **Stacks 0FE3.** On a locally Noetherian normal scheme every integer-valued function is
locally pure dimensional. -/
@[stacks 0FE3 "normal_case"]
theorem IsLocallyPureDimensional.of_isNormal (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsNormal X] (δ : X → ℤ) : IsLocallyPureDimensional δ :=
  .of_hasDimensionDecomposition (.of_isNormal X δ)

/-- **Stacks 0FE3.** On a locally Noetherian normal scheme every integer-valued function is
locally equidimensional. -/
@[stacks 0FE3 "normal_case"]
theorem IsLocallyEquidimensional.of_isNormal (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsNormal X] (δ : X → ℤ) : IsLocallyEquidimensional δ :=
  .of_isLocallyPureDimensional (.of_isNormal X δ)

end Stacks.Chow

end
