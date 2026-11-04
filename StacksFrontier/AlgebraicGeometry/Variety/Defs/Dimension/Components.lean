module

public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Local dimension and irreducible components

Let `X` be a scheme locally of finite type over a field and let `x` be a point of `X`. The local
dimension of `X` at `x` is the largest dimension of an irreducible component of `X` containing
`x`.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_eq_iSup_irreducibleComponents` identifies the local
  dimension at a point with the supremum of the dimensions of the irreducible components through
  that point.
* `AlgebraicGeometry.exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt`
  says that this supremum is attained by an irreducible component through the point.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional`: on an
  equidimensional such scheme the local dimension at every point is the dimension of the whole
  scheme, and `AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional` is the same
  statement with that dimension named by a natural number.

## Implementation notes

The locally algebraic structure is represented by an explicit morphism to the spectrum of the
field and a `LocallyOfFiniteType` instance. Following the existing dimension API, both local and
global dimensions take values in `WithBot ℕ∞`. The indexed-supremum formula and its companion
attainment statement together express the source's maximum. Irreducible components are subsets
of the underlying topological space of the scheme; a component is given the reduced induced
subscheme structure, which is what makes the dimension of a component computable from an affine
chart.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An irreducible component of an open subspace is the restriction of an irreducible component
of the ambient space. -/
private lemma exists_component_extension
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] (j : Y → X)
    (hj : Topology.IsOpenEmbedding j) (y : Y) (W : Set Y)
    (hW : W ∈ irreducibleComponents Y) (hyW : y ∈ W) :
    ∃ Z ∈ irreducibleComponents X, j y ∈ Z ∧ j ⁻¹' Z = W := by
  obtain ⟨Z, hZ, hWZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (hW.1.image j hj.continuous.continuousOn)
  have hyZ : j y ∈ Z := hWZ ⟨y, hyW, rfl⟩
  exact ⟨Z, hZ, hyZ, Set.Subset.antisymm
    (hW.2 (preimage_mem_irreducibleComponents hZ hj ⟨j y, hyZ, y, rfl⟩).1
      (Set.image_subset_iff.1 hWZ)) (Set.image_subset_iff.1 hWZ)⟩

/-- If restriction to an open subspace preserves the dimension of every irreducible component
through a point, then the suprema of component dimensions at that point agree. -/
private lemma iSup_components_eq_of_isOpenEmbedding
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] (j : Y → X)
    (hj : Topology.IsOpenEmbedding j) (y : Y)
    (hdim : ∀ Z ∈ irreducibleComponents X, j y ∈ Z →
      topologicalKrullDim Z = topologicalKrullDim (j ⁻¹' Z)) :
    (⨆ W ∈ {W ∈ irreducibleComponents Y | y ∈ W}, topologicalKrullDim W) =
      ⨆ Z ∈ {Z ∈ irreducibleComponents X | j y ∈ Z}, topologicalKrullDim Z := by
  apply le_antisymm
  · refine iSup₂_le fun W hW ↦ ?_
    obtain ⟨Z, hZ, hyZ, hpre⟩ := exists_component_extension j hj y W hW.1 hW.2
    rw [← hpre, ← hdim Z hZ hyZ]
    exact le_iSup₂_of_le Z ⟨hZ, hyZ⟩ le_rfl
  · refine iSup₂_le fun Z ⟨hZc, hyZ⟩ ↦ ?_
    rw [hdim Z hZc hyZ]
    exact le_iSup₂_of_le (j ⁻¹' Z)
      ⟨preimage_mem_irreducibleComponents hZc hj ⟨j y, hyZ, y, rfl⟩, hyZ⟩ le_rfl

/-- A subset of the domain of a topological embedding has the same dimension as its image. -/
private lemma topologicalKrullDim_eq_image
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] {j : Y → X}
    (hj : Topology.IsEmbedding j) (S : Set Y) :
    topologicalKrullDim S = topologicalKrullDim (j '' S) :=
  IsHomeomorph.topologicalKrullDim_eq _ (hj.homeomorphImage S).isHomeomorph

/-- An irreducible component of a locally algebraic scheme has the same dimension as its
restriction to an open subscheme meeting it. -/
private lemma component_dim_preimage
    (k : Type u) [Field k] (X Y : Scheme.{u}) (g : X ⟶ Spec (.of k))
    [LocallyOfFiniteType g] (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hyZ : j y ∈ Z) :
    topologicalKrullDim Z = topologicalKrullDim (j ⁻¹' Z) := by
  let Zc : Closeds X := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Zc
  let e : I.subscheme ≃ₜ Z :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso I.subschemeIso)).trans I.gluedHomeo |>.trans
      (Homeomorph.setCongr (Scheme.IdealSheafData.coe_support_vanishingIdeal Zc))
  have : IrreducibleSpace I.subscheme :=
    e.irreducibleSpace_iff.2 (Subtype.irreducibleSpace hZ.1)
  let V : Set I.subscheme := I.subschemeι ⁻¹' Set.range j
  have hV : IsOpen V := j.isOpenEmbedding.isOpen_range.preimage I.subschemeι.continuous
  have hVne : V.Nonempty := by
    obtain ⟨z, hz⟩ : j y ∈ Set.range I.subschemeι := by
      rwa [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal Zc]
    exact ⟨z, y, hz.symm⟩
  have himg : I.subschemeι '' V = j '' (j ⁻¹' Z) := by
    change I.subschemeι '' (I.subschemeι ⁻¹' Set.range j) = j '' (j ⁻¹' Z)
    rw [Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range,
      I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal Zc, Set.inter_comm]
    rfl
  calc
    topologicalKrullDim Z = topologicalKrullDim I.subscheme :=
      e.isHomeomorph.topologicalKrullDim_eq.symm
    _ = topologicalKrullDim V :=
      topologicalKrullDim_eq_of_isOpen k I.subscheme (I.subschemeι ≫ g) V hV hVne
    _ = topologicalKrullDim (I.subschemeι '' V) :=
      topologicalKrullDim_eq_image I.subschemeι.isClosedEmbedding.isEmbedding V
    _ = topologicalKrullDim (j '' (j ⁻¹' Z)) := by rw [himg]
    _ = topologicalKrullDim (j ⁻¹' Z) :=
      (topologicalKrullDim_eq_image j.isOpenEmbedding.isEmbedding _).symm

/-- In a Noetherian space, the supremum of the dimensions of the irreducible components through
a point is attained by one of them. -/
private lemma exists_mem_irreducibleComponents_topologicalKrullDim_eq_iSup
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (y : X) :
    ∃ W ∈ irreducibleComponents X, y ∈ W ∧ topologicalKrullDim W =
      ⨆ W ∈ {W ∈ irreducibleComponents X | y ∈ W}, topologicalKrullDim W := by
  obtain ⟨W₀, hW₀, hyW₀⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
  obtain ⟨W, hW, hmax⟩ := Set.exists_max_image {W | W ∈ irreducibleComponents X ∧ y ∈ W}
    (fun W : Set X ↦ topologicalKrullDim W)
    (NoetherianSpace.finite_irreducibleComponents.subset fun W hW ↦ hW.1)
    ⟨W₀, hW₀, hyW₀ (Set.mem_singleton y)⟩
  exact ⟨W, hW.1, hW.2, le_antisymm (le_iSup₂_of_le W hW le_rfl) (iSup₂_le hmax)⟩

/-- The supremum formula for the local dimension together with its attainment, proved in one
reduction to an affine chart. -/
private lemma local_dimension_components_core (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDimAt X x =
      ⨆ Z ∈ {Z ∈ irreducibleComponents X | x ∈ Z}, topologicalKrullDim Z ∧
    ∃ Z ∈ irreducibleComponents X, x ∈ Z ∧
      topologicalKrullDim Z = topologicalKrullDimAt X x := by
  obtain ⟨R, i, _, y, hxy⟩ := X.exists_Spec_apply_eq x
  let g : Spec R ⟶ Spec (.of k) := i ≫ f
  let : Algebra k R :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp) ≫
      (Scheme.ΓSpecIso R).hom).hom.toAlgebra
  have : Algebra.FiniteType k R := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp) ≫
      (Scheme.ΓSpecIso R).hom).hom).FiniteType
    exact (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective).comp
      ((g.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)).comp
        (RingHom.FiniteType.of_surjective _
          (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective))
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hOT := PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k y
  have hlocalEq : topologicalKrullDimAt X x = localKrullDim (PrimeSpectrum R) y := by
    rw [← hxy, i.isOpenEmbedding.topologicalKrullDimAt_eq y]
    exact topologicalKrullDimAt_eq_localKrullDim _ _
  have hcompEq :
      (⨆ W ∈ {W ∈ irreducibleComponents (Spec R) | y ∈ W}, topologicalKrullDim W) =
        ⨆ Z ∈ {Z ∈ irreducibleComponents X | x ∈ Z}, topologicalKrullDim Z := by
    simpa [hxy] using iSup_components_eq_of_isOpenEmbedding i i.isOpenEmbedding y
      fun Z hZ hyZ ↦ component_dim_preimage k X (Spec R) f i y hZ hyZ
  obtain ⟨W, hW, hyW, hSup⟩ := exists_mem_irreducibleComponents_topologicalKrullDim_eq_iSup y
  obtain ⟨Z, hZ, hxZ, hpre⟩ := exists_component_extension i i.isOpenEmbedding y W hW hyW
  have hdimZ := component_dim_preimage k X (Spec R) f i y hZ hxZ
  rw [hpre] at hdimZ
  exact ⟨hlocalEq.trans (hOT.1.trans hcompEq), Z, hZ, hxy ▸ hxZ,
    hdimZ.trans (hlocalEq.trans (hOT.1.trans hSup.symm)).symm⟩

/-- For a scheme locally of finite type over a field, the local dimension at a point is the
largest dimension of an irreducible component containing that point. -/
@[stacks 0A21 "local_dimension_components"]
theorem topologicalKrullDimAt_eq_iSup_irreducibleComponents
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDimAt X x =
      ⨆ Z ∈ {Z ∈ irreducibleComponents X | x ∈ Z}, topologicalKrullDim Z :=
  (local_dimension_components_core k X f x).1

/-- The maximum dimension among the irreducible components through a point is attained. -/
@[stacks 0A21 "local_dimension_components", ega "IV 10.6.3" "sup_i dim(Y_i)"]
theorem exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    ∃ Z ∈ irreducibleComponents X,
      x ∈ Z ∧ topologicalKrullDim Z = topologicalKrullDimAt X x :=
  (local_dimension_components_core k X f x).2

/-- On an equidimensional scheme locally of finite type over a field the local dimension at
every point is the dimension of the whole scheme. The local dimension at a point is the
dimension of some irreducible component through it, all components have the same dimension,
and the dimension of the scheme is the supremum of its local dimensions. -/
@[ega "IV 10.6.3" "special case"]
theorem topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional (k : Type u) [Field k]
    (X : Scheme.{u}) (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] (he : Equidimensional X)
    (x : X) : topologicalKrullDimAt X x = topologicalKrullDim X := by
  obtain ⟨Z, hZ, -, hZdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X q x
  have hconstant (y : X) : topologicalKrullDimAt X y = topologicalKrullDim Z := by
    obtain ⟨W, hW, -, hWdim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X q y
    exact hWdim.symm.trans (he W hW Z hZ)
  have hglobal : topologicalKrullDim X = topologicalKrullDim Z := by
    rw [topologicalKrullDim_eq_iSup_localKrullDim]
    simp_rw [← topologicalKrullDimAt_eq_localKrullDim, hconstant]
    exact le_antisymm (iSup_le fun _ ↦ le_rfl) (le_iSup_of_le x le_rfl)
  exact hZdim.symm.trans hglobal.symm

/-- An equidimensional scheme locally of finite type over a field and of dimension `d` has local
dimension `d` at each of its points. -/
theorem topologicalKrullDimAt_eq_of_equidimensional (k : Type u) [Field k] (Z : Scheme.{u})
    (q : Z ⟶ Spec (.of k)) [LocallyOfFiniteType q] {d : ℕ} (he : Equidimensional Z)
    (hd : topologicalKrullDim Z = (d : WithBot ℕ∞)) (z : Z) :
    topologicalKrullDimAt Z z = (d : WithBot ℕ∞) :=
  (topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k Z q he z).trans hd

end AlgebraicGeometry

end
