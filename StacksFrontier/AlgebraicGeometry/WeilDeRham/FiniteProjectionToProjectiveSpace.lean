module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Curves.UniformizerDifferential
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusReducible
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.DualClosedPoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.IteratedProjection
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FactorSyntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Finite
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLinesOfClosedSubset
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.DimensionOfProjectiveSpace
public import StacksFrontier.LinearAlgebra.SubspaceUnionCodim
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# A finite syntomic morphism from a smooth projective variety onto projective space

In the proof of axiom (A6) for de Rham cohomology (Stacks, Proposition 0FWD, the paragraph
"Proof of Axiom (A6) for `X` irreducible") the source chooses, for `k` algebraically closed and
`X` an irreducible smooth projective scheme of dimension `d` over `k`, a finite morphism
`f : X ⟶ 𝐏^d_k` (Intersection Theory, Section 0B1N and Lemma 0B1P), and observes that `f` is
finite syntomic: a local complete intersection morphism by More on Morphisms, Lemma 069M, and
flat by Algebra, Lemma 00R4. This file proves exactly that.

The projective space is the polynomial model `Proj k[T₀, …, T_d]` with its structure morphism
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k d`, the model on which the de Rham
cohomology of projective space (Tag 0FMJ) is computed in every dimension
(`Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.projectiveDeRhamCohomology`); for `d = m + 1`
it is, by definition, `Stacks.AlgebraicGeometry.ProjectiveSpaceDeRham.structureMorphism k m`. The
case `d = 0` needs no separate treatment: the target is then `ℙ⁰_k = Proj k[T₀]`.

## Main results

* `Stacks.WeilDeRham.exists_finrank_eq_disjoint_linearSubspace`: a closed subset of dimension
  `< e` of `𝐏(V)` misses the linear subspace cut out by some `e`-dimensional space of linear
  forms, for `e ≤ dim V`.
* `Stacks.WeilDeRham.exists_isFinite_syntomic_toProjectiveSpace`: **the finite syntomic morphism
  of the source.** For `X` irreducible, smooth and projective over `k` of dimension `d`, there is
  a morphism `f : X ⟶ ℙ^d_k` over `k` which is finite, surjective, flat, syntomic and a local
  complete intersection morphism.
* `Stacks.WeilDeRham.exists_isFinite_syntomic_toProjectiveSpace_of_relativeDimension`: the same,
  with the dimension given as `AlgebraicGeometry.RelativeDimension sX d`, the form in which
  `Stacks.WeilCohomology.IsNonemptyEquidimensional` states it.

## Implementation notes

The existence of the morphism is the source's projection argument done in one step: the
inclusion of `X` into some `𝐏(V)` coming from projectivity of `X` is followed by the linear
projection `𝐏(V) ⇢ 𝐏(W)` away from a linear subspace disjoint from `X`, where `W ≤ V` has
dimension `d + 1`; this is the composite of the point projections of Section 0B1N and is finite
on `X` by `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isFinite_projection_of_disjoint`.
Such a `W` exists by dimension theory: a linear form not vanishing at a chosen point of each of
the finitely many irreducible components of a closed subset `Z` cuts it in a closed subset nowhere
dense in `Z`, hence of smaller dimension (`IsNowhereDense.topologicalKrullDim_add_one_le`), and
`d + 1` such forms cut `X` down to the empty set. A basis of `W` identifies `𝐏(W)` with
`Proj k[T₀, …, T_d]` over `k`.

Flatness is miracle flatness (Tag 00R4) in the form of
`Stacks.Discriminant.flat_of_locallyQuasiFinite` (Tag 0BWJ): a quasi-finite morphism between
schemes smooth of the same relative dimension over `k` is flat; the local rings are regular,
hence Cohen–Macaulay, and quasi-finiteness gives the dimension equality. Syntomicity then follows
from `AlgebraicGeometry.syntomic_of_syntomic_comp_of_flat`: `f` is flat and of finite
presentation and `f` followed by the smooth, hence syntomic, structure morphism of `ℙ^d_k` is
the smooth structure morphism of `X`. This is the content of the source's appeal to 069M plus
flatness; the local complete intersection property of `f` is recovered from finiteness and
syntomicity by Tag 0FKY. Surjectivity holds because the image of `f` is open (flat of finite
presentation) and closed (finite) in the irreducible `ℙ^d_k`.

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Section 0B1N](https://stacks.math.columbia.edu/tag/0B1N)
* [Stacks Project, Tag 0B1P](https://stacks.math.columbia.edu/tag/0B1P)
* [Stacks Project, Tag 069M](https://stacks.math.columbia.edu/tag/069M)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpaceOfModule
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace Stacks.WeilDeRham

section LinearSubspace

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- **A closed subset of `𝐏(V)` of dimension `< e` misses a linear subspace of codimension `e`.**
Let `k` be algebraically closed, `V` finite-dimensional and nonzero, and `Z ⊆ 𝐏(V)` closed with
`dim Z < e ≤ dim V`. Then there is a subspace `W ≤ V` of linear forms with `dim W = e` whose
common zero locus `linearSubspace k V W` is disjoint from `Z`.

By induction on `e`: a linear form `v` not vanishing at a chosen point of each of the finitely
many irreducible components of `Z` cuts `Z` in a closed subset nowhere dense in `Z`, which has
dimension `< e - 1` and so misses the zero locus of some `(e - 1)`-dimensional `W'`; then
`W' + k v`, or `W'` enlarged by any vector if `v ∈ W'`, works. -/
theorem exists_finrank_eq_disjoint_linearSubspace [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (e : ℕ) (he : e ≤ Module.finrank k V)
    (Z : Set (projectiveSpaceOfModule k V)) (hZ : IsClosed Z)
    (hdim : topologicalKrullDim Z < (e : WithBot ℕ∞)) :
    ∃ W : Submodule k V, Module.finrank k W = e ∧ Disjoint Z (linearSubspace k V W) := by
  induction e generalizing Z with
  | zero =>
    have hbot : topologicalKrullDim Z = ⊥ := (WithBot.lt_zero_iff_eq_bot _).mp (by simpa using hdim)
    have hempty : Z = ∅ := by
      have := (topologicalKrullDim_eq_bot_iff_isEmpty Z).mp hbot
      exact Set.isEmpty_coe_sort.mp this
    exact ⟨⊥, finrank_bot k V, by simp [hempty]⟩
  | succ e ih =>
    classical
    -- a linear form not vanishing at a point of any irreducible component of `Z`
    have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
    let Wc : Set Z → Submodule k V := fun C =>
      if h : C.Nonempty then pointSubmodule k V h.some.1 else ⊥
    have hWc : ∀ C ∈ hfin.toFinset, Wc C ≠ ⊤ := by
      intro C hC
      have hne : C.Nonempty :=
        (hfin.mem_toFinset.mp hC).1.nonempty
      simp only [Wc, hne, ↓reduceDIte]
      intro htop
      obtain ⟨x, hx⟩ := exists_ι_notMem k V hne.some.1
      exact hx ((mem_pointSubmodule_iff k V _ x).mp (htop ▸ Submodule.mem_top))
    obtain ⟨v, hv⟩ := Stacks.LinearAlgebra.exists_notMem_biUnion_of_infinite hfin.toFinset Wc hWc
    set H := linearSubspace k V (k ∙ v) with hH
    set A := Z ∩ H with hA
    have hAclosed : IsClosed A := hZ.inter (isClosed_linearSubspace k V _)
    have hnd : IsNowhereDense ((Subtype.val : Z → _) ⁻¹' A) := by
      rw [isNowhereDense_preimage_val_iff_forall_irreducibleComponents hAclosed]
      intro C hC hCA
      have hne : C.Nonempty := hC.1.nonempty
      have hmem : (hne.some : Z).1 ∈ H := (hCA ⟨hne.some, hne.some_mem, rfl⟩).2
      rw [hH, mem_linearSubspace_iff, Submodule.span_singleton_le_iff_mem] at hmem
      have := hv C (hfin.mem_toFinset.mpr hC)
      simp only [Wc, hne, ↓reduceDIte] at this
      exact this hmem
    have hAdim : topologicalKrullDim A < (e : WithBot ℕ∞) := by
      have h1 := hnd.topologicalKrullDim_add_one_le (hAclosed.preimage continuous_subtype_val)
      rw [topologicalKrullDim_preimage_val Z A Set.inter_subset_left] at h1
      have h2 : topologicalKrullDim A + 1 < (e : WithBot ℕ∞) + 1 := by
        refine lt_of_le_of_lt h1 ?_
        simpa using hdim
      exact ENat.WithBot.add_one_le_natCast_iff.mp (ENat.WithBot.lt_add_one_iff.mp h2)
    obtain ⟨W', hW'rank, hW'disj⟩ := ih (by omega) A hAclosed hAdim
    have hW'top : W' < ⊤ := lt_top_iff_ne_top.2 fun h => by
      rw [h, finrank_top] at hW'rank
      omega
    obtain ⟨u, hu, hsub⟩ : ∃ u, u ∉ W' ∧
        linearSubspace k V W' ∩ linearSubspace k V (k ∙ u) ⊆ H := by
      by_cases hvW' : v ∈ W'
      · obtain ⟨u, -, hu⟩ := IsConcreteLE.exists_of_lt hW'top
        exact ⟨u, hu, fun q hq => linearSubspace_antitone k V
          ((Submodule.span_singleton_le_iff_mem v W').mpr hvW') hq.1⟩
      · exact ⟨v, hvW', fun q hq => hq.2⟩
    refine ⟨W' ⊔ k ∙ u, by rw [Submodule.finrank_sup_span_singleton hu, hW'rank], ?_⟩
    rw [linearSubspace_sup, Set.disjoint_iff]
    rintro q ⟨hqZ, hqW', hqu⟩
    exact Set.disjoint_iff.mp hW'disj ⟨⟨hqZ, hsub ⟨hqW', hqu⟩⟩, hqW'⟩

end LinearSubspace

section Projection

variable {k : Type u} [Field k]

/-- A basis of `W` identifies the projective space `𝐏(W)` with `Proj k[T₀, …, Tₙ]` over `k`: the
coordinate isomorphism followed by `projToSpecCoeff` is the structure morphism of `𝐏(W)`. -/
theorem projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_projToSpecCoeff {W : Type u}
    [AddCommGroup W] [Module k W] {n : ℕ} (b : Module.Basis (Fin (n + 1)) k W) :
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom ≫ projToSpecCoeff k n =
      projectiveSpaceOfModuleToSpec k W := by
  rw [projToSpecCoeff, Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap]
  exact projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_toSpecZero b

/-- **A projective scheme over a field embeds in `𝐏(kᴺ⁺¹)` over `k`.** Over the affine base
`Spec k` projectivity is H-projectivity, a closed immersion into `ℙᴺ_k` over `k`, and the
standard basis of `kᴺ⁺¹` identifies `ℙᴺ_k` with `𝐏(kᴺ⁺¹)` over `k`. -/
theorem exists_isClosedImmersion_projectiveSpaceOfModule_of_isProjective {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hproj : IsProjective sX) :
    ∃ (N : ℕ) (i : X ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k)),
      IsClosedImmersion i ∧ i ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = sX := by
  obtain ⟨N, i, hi, hip⟩ := (isProjective_iff_isProjectiveMorphism_of_isAffine sX).mp hproj
  refine ⟨N, i ≫ (basisProjectiveSpaceIso (Pi.basisFun k (Fin (N + 1)))).hom, ?_, ?_⟩
  · have := hi
    infer_instance
  · rw [Category.assoc, basisProjectiveSpaceIso_hom_comp_toSpec, ← hip]
    rfl

/-- **The finite syntomic morphism of the proof of axiom (A6) for de Rham cohomology.** Let `k`
be algebraically closed and let `X` be an irreducible scheme, smooth and projective over `k` of
dimension `d`. Then there is a morphism `f : X ⟶ ℙ^d_k = Proj k[T₀, …, T_d]` over `k` which is
finite, surjective, flat, syntomic and a local complete intersection morphism.

The morphism is the projection of an embedding `X ⊆ 𝐏(V)` away from a linear subspace disjoint
from `X` (Section 0B1N, Lemma 0B1P); it is flat by miracle flatness (Tag 00R4) and hence
syntomic, `X` being smooth over `k` (Tag 069M). -/
theorem exists_isFinite_syntomic_toProjectiveSpace [IsAlgClosed k] {X : Scheme.{u}}
    [IrreducibleSpace X] (sX : X ⟶ Spec (.of k)) [Smooth sX] (hproj : IsProjective sX) (d : ℕ)
    (hdim : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    ∃ f : X ⟶ AlgebraicGeometry.Proj (polyGrading k d),
      f ≫ projToSpecCoeff k d = sX ∧ IsFinite f ∧ Surjective f ∧ Flat f ∧ Syntomic f ∧
        IsLocalCompleteIntersectionMorphism f := by
  obtain ⟨N, i, hi, hisX⟩ := exists_isClosedImmersion_projectiveSpaceOfModule_of_isProjective sX
    hproj
  have := hi
  set V := Fin (N + 1) → k
  have hV : Module.finrank k V = N + 1 := Module.finrank_fin_fun k
  -- the image of `X` has dimension `d`
  have hZdim : topologicalKrullDim (Set.range i.base) = (d : WithBot ℕ∞) := by
    rw [← hdim]
    exact (i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq).symm
  -- so `d + 1 ≤ dim V`
  have hdN : d + 1 ≤ Module.finrank k V := by
    have h := topologicalKrullDim_subspace_le (projectiveSpaceOfModule k V) (Set.range i.base)
    rw [hZdim, topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV] at h
    have : d ≤ N := by exact_mod_cast h
    omega
  obtain ⟨W, hWrank, hWdisj⟩ := exists_finrank_eq_disjoint_linearSubspace (d + 1) hdN
    (Set.range i.base) i.isClosedEmbedding.isClosed_range
    (by rw [hZdim]; exact_mod_cast Nat.lt_succ_self d)
  obtain ⟨j, hj, hjfin⟩ := exists_isFinite_projection_of_disjoint i W hWdisj
  let b : Module.Basis (Fin (d + 1)) k W := Module.finBasisOfFinrankEq k W hWrank
  let f : X ⟶ AlgebraicGeometry.Proj (polyGrading k d) :=
    j ≫ projection k V W ≫ (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom
  have hf : f ≫ projToSpecCoeff k d = sX := by
    simp only [f, Category.assoc,
      projectiveSpaceOfModuleIsoProjMvPolynomial_hom_comp_projToSpecCoeff, projection_comp_toSpec]
    rw [← Category.assoc, hj, hisX]
  have hfin : IsFinite f := by
    have : IsFinite (j ≫ projection k V W) := hjfin
    simp only [f, ← Category.assoc]
    infer_instance
  -- both `X` and `ℙ^d_k` are smooth of relative dimension `d` over `k`
  have : SmoothOfRelativeDimension d (projToSpecCoeff k d) :=
    smoothOfRelativeDimension_projToSpecCoeff k d
  have : Smooth (projToSpecCoeff k d) := SmoothOfRelativeDimension.smooth d _
  have hsX : SmoothOfRelativeDimension d sX := by
    refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq sX d fun x => ?_
    rw [topologicalKrullDimAt_fiber_eq,
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x, hdim]
  have : SmoothOfRelativeDimension d (f ≫ projToSpecCoeff k d) := by rw [hf]; exact hsX
  have hflat : Flat f := Stacks.Discriminant.flat_of_locallyQuasiFinite (projToSpecCoeff k d) f d
  have : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading k d)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff k d)
  have : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hsyn : Syntomic f :=
    syntomic_of_syntomic_comp_of_flat f (projToSpecCoeff k d) (hf ▸ syntomic_of_smooth sX)
  have hsurj : Surjective f := by
    refine ⟨Set.range_eq_univ.mp ?_⟩
    have hclopen : IsClopen (Set.range f.base) :=
      ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
    exact hclopen.eq_univ (Set.range_nonempty _)
  exact ⟨f, hf, hfin, hsurj, hflat, hsyn,
    (flat_and_isLocalCompleteIntersectionMorphism_of_finite_syntomic ⟨hfin, hsyn⟩).2⟩

/-- **The finite syntomic morphism of the proof of axiom (A6) for de Rham cohomology**, with the
dimension of `X` stated as `AlgebraicGeometry.RelativeDimension sX d`, as in
`Stacks.WeilCohomology.IsNonemptyEquidimensional`. Let `k` be algebraically closed and let
`X` be an irreducible scheme, smooth and projective over `k`, of relative dimension `d` over `k`.
Then there is a morphism `f : X ⟶ ℙ^d_k = Proj k[T₀, …, T_d]` over `k` which is finite,
surjective, flat, syntomic and a local complete intersection morphism. -/
theorem exists_isFinite_syntomic_toProjectiveSpace_of_relativeDimension [IsAlgClosed k]
    {X : Scheme.{u}} [IrreducibleSpace X] (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hproj : IsProjective sX) (d : ℕ) (hd : RelativeDimension sX d) :
    ∃ f : X ⟶ AlgebraicGeometry.Proj (polyGrading k d),
      f ≫ projToSpecCoeff k d = sX ∧ IsFinite f ∧ Surjective f ∧ Flat f ∧ Syntomic f ∧
        IsLocalCompleteIntersectionMorphism f :=
  exists_isFinite_syntomic_toProjectiveSpace sX hproj d
    (topologicalKrullDim_eq_of_relativeDimension sX hd)

end Projection

end Stacks.WeilDeRham

end
