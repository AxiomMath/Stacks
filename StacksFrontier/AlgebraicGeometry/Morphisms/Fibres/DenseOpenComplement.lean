module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseFibreAux
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.GaloisCoverDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.SigmaMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The complement of a fibrewise dense open in a family of curves

Two facts about the fibres of a morphism used in the proof of Stacks 0GKX.

* `topologicalKrullDim_nonpos_of_isInducing_of_range_subset`: in a quasi-sober space of dimension
  at most `1`, a subspace avoiding an open containing all generic points has dimension at most `0`.
* `AlgebraicGeometry.locallyQuasiFinite_comp_of_dense_fiber`: if `g : X ⟶ S` is locally of finite
  type with fibres of dimension at most `1`, and `O ⊆ X` is open and dense in every fibre, then a
  closed subscheme of `X` disjoint from `O` is locally quasi-finite over `S`. Its fibres meet no
  generic point of a fibre of `g`, hence have dimension `0`.
* `AlgebraicGeometry.dense_fiber_image_of_isOpenImmersion`: if `q̄ : Ȳ ⟶ T` is smooth with
  geometrically connected fibres and `j : Y ⟶ Ȳ` is an open immersion with `j ≫ q̄` surjective,
  then a subset of `Y` dense in every fibre of `j ≫ q̄` has image dense in every fibre of `q̄`:
  the fibres of `q̄` are irreducible (smooth and connected) and meet `Y` in a nonempty open.
* `AlgebraicGeometry.sigmaMap_curveFamily`: a finite coproduct of proper smooth morphisms with
  geometrically connected fibres of dimension at most `1` is again such a morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

/-- **A subspace avoiding the generic points of a curve-like space is zero-dimensional.** Let `X`
be quasi-sober of dimension at most `1` and `D ⊆ X` an open containing every generic point of
`X`. Then every subspace `Z` embedded in `X` away from `D` has dimension at most `0`: an
irreducible closed subset of `X` inside `Dᶜ` is not an irreducible component (its generic point
would lie in `D`), so it is minimal. -/
@[sga "4 XVIII 1.1.3" "more general"]
theorem topologicalKrullDim_nonpos_of_isInducing_of_range_subset {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] [QuasiSober X] (hX : topologicalKrullDim X ≤ 1) {D : Set X}
    (hD : IsOpen D) (hgen : genericPoints X ⊆ D) {f : Z → X} (hf : IsInducing f)
    (hfD : Set.range f ⊆ Dᶜ) : topologicalKrullDim Z ≤ 0 := by
  have hmax : ∀ A : IrreducibleCloseds Z,
      ¬ IsMax (IrreducibleCloseds.map f hf.continuous A) := by
    intro A hA
    set A' := IrreducibleCloseds.map f hf.continuous A
    have hcomp : (A' : Set X) ∈ irreducibleComponents X := by
      rw [irreducibleComponents_eq_maximals_closed]
      exact ⟨⟨A'.isClosed, A'.isIrreducible⟩, fun s hs hAs =>
        hA (b := ⟨s, hs.2, hs.1⟩) hAs⟩
    have hξ := A'.isIrreducible.isGenericPoint_genericPoint A'.isClosed
    have hξgen : A'.isIrreducible.genericPoint ∈ genericPoints X := by
      change closure {_} ∈ irreducibleComponents X
      rw [hξ.def]
      exact hcomp
    have hsub : (A' : Set X) ⊆ Dᶜ :=
      closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact hfD ⟨z, rfl⟩) hD.isClosed_compl
    exact hsub hξ.mem (hgen hξgen)
  rw [topologicalKrullDim, Order.krullDim_nonpos_iff_forall_isMin]
  intro A B hBA
  by_contra hAB
  have hlt : B < A := lt_of_le_not_ge hBA hAB
  have hmap := IrreducibleCloseds.map_strictMono_of_isInducing hf hlt
  rcases Order.krullDim_le_one_iff.mp hX (IrreducibleCloseds.map f hf.continuous A) with h | h
  · exact hmap.not_ge (h hmap.le)
  · exact hmax A h

namespace AlgebraicGeometry

/-- **The complement of a fibrewise dense open is quasi-finite.** Let `g : X ⟶ S` be locally of
finite type with all fibres of dimension at most `1`, let `O ⊆ X` be open and dense in every
fibre of `g`, and let `i : Z ⟶ X` be a closed immersion whose image misses `O`. Then `i ≫ g` is
locally quasi-finite: each fibre of `i ≫ g` sits in the fibre of `g` away from an open containing
all its generic points, so it has dimension `0`. -/
theorem locallyQuasiFinite_comp_of_dense_fiber_of_isClosedImmersion {X S Z : Scheme.{u}} (g : X ⟶ S)
    [LocallyOfFiniteType g] (hdim : ∀ s, topologicalKrullDim (g.fiber s) ≤ 1) {O : Set X}
    (hO : IsOpen O) (hd : ∀ s, Dense ((g.fiberι s) ⁻¹' O)) (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : Set.range i ⊆ Oᶜ) : LocallyQuasiFinite (i ≫ g) := by
  refine locallyQuasiFinite_of_forall_topologicalKrullDim_fiber_le_zero (i ≫ g) fun s => ?_
  have := isLocallyNoetherian_fiber_of_locallyOfFiniteType g s
  have hO' : IsOpen ((g.fiberι s) ⁻¹' O) := hO.preimage (g.fiberι s).continuous
  have hgen : genericPoints (g.fiber s) ⊆ (g.fiberι s) ⁻¹' O := fun x hx =>
    Scheme.mem_of_mem_genericPoints_of_dense (g.fiber s) hO' (hd s) hx
  have h := topologicalKrullDim_nonpos_of_isInducing_of_range_subset (hdim s) hO' hgen
    (g.fiberMap i s).isEmbedding.isInducing (by
      rintro _ ⟨z, rfl⟩ hz
      exact hi ⟨_, rfl⟩ (by simpa only [Set.mem_preimage, Scheme.Hom.fiberι_fiberMap] using hz))
  simpa using h

/-- **A fibrewise dense subset of an open stays fibrewise dense in a smooth connected
compactification.** Let `q̄ : Ȳ ⟶ T` be smooth with geometrically connected fibres and
`j : Y ⟶ Ȳ` an open immersion with `j ≫ q̄` surjective. If `D ⊆ Y` is dense in every fibre of
`j ≫ q̄`, then `j(D)` is dense in every fibre of `q̄`: a fibre of `q̄` is smooth and connected over
a field, hence irreducible, and it meets `Y` in a nonempty open, which is therefore dense. -/
theorem dense_fiber_image_of_isOpenImmersion {Y Ybar T : Scheme.{u}} (j : Y ⟶ Ybar)
    [IsOpenImmersion j] (qbar : Ybar ⟶ T) [Smooth qbar] [Surjective (j ≫ qbar)]
    (hc : ∀ s, GeometricallyConnected (qbar.fiberToSpecResidueField s)) {D : Set Y}
    (hD : ∀ s, Dense (((j ≫ qbar).fiberι s) ⁻¹' D)) (s : T) :
    Dense ((qbar.fiberι s) ⁻¹' (j '' D)) := by
  have : ConnectedSpace (qbar.fiber s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := qbar.fiberToSpecResidueField s)
  have : Smooth (qbar.fiberToSpecResidueField s) :=
    inferInstanceAs (Smooth (pullback.snd qbar (T.fromSpecResidueField s)))
  have : IrreducibleSpace (qbar.fiber s) :=
    Abhyankar.irreducibleSpace_of_smooth_of_connectedSpace (k := T.residueField s)
      (qbar.fiberToSpecResidueField s)
  obtain ⟨y, hy⟩ := (j ≫ qbar).surjective s
  have hy' : y ∈ Set.range ((j ≫ qbar).fiberι s) := by
    rw [Scheme.Hom.range_fiberι]
    exact hy
  obtain ⟨z, -⟩ := hy'
  have hdense : DenseRange (qbar.fiberMap j s) :=
    (qbar.fiberMap j s).isOpenEmbedding.isOpenMap.isOpen_range.dense ⟨_, z, rfl⟩
  refine ((hdense.dense_image (qbar.fiberMap j s).continuous (hD s))).mono ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨_, hw, (Scheme.Hom.fiberι_fiberMap qbar j s w).symm⟩

/-- **A finite coproduct of families of curves is a family of curves.** If every `q̄ᵢ : Ȳᵢ ⟶ Tᵢ`
is proper and smooth with geometrically connected fibres of dimension at most `1`, so is
`∐ q̄ᵢ : ∐ Ȳᵢ ⟶ ∐ Tᵢ`: the first three properties are local on the target, and the fibre of
`∐ q̄ᵢ` over a point of `Tₖ` is the fibre of `q̄ₖ`, as `q̄ₖ` is the base change of `∐ q̄ᵢ` along
`Tₖ ⟶ ∐ Tᵢ`. -/
theorem sigmaMap_curveFamily {ι : Type} [Finite ι] {T Ybar : ι → Scheme.{u}}
    (qbar : ∀ i, Ybar i ⟶ T i)
    (h : ∀ i, IsProper (qbar i) ∧ Smooth (qbar i) ∧
      (∀ s, GeometricallyConnected ((qbar i).fiberToSpecResidueField s)) ∧
      ∀ s, topologicalKrullDim ((qbar i).fiber s) ≤ 1) :
    IsProper (Limits.Sigma.map qbar) ∧ Smooth (Limits.Sigma.map qbar) ∧
      GeometricallyConnected (Limits.Sigma.map qbar) ∧
      ∀ s, topologicalKrullDim ((Limits.Sigma.map qbar).fiber s) ≤ 1 := by
  have hp : IsProper (Limits.Sigma.map qbar) :=
    IsZariskiLocalAtTarget.sigmaMap (P := @IsProper) qbar fun i => (h i).1
  have hgc : ∀ i, GeometricallyConnected (qbar i) := fun i =>
    (GeometricallyConnected.iff_geometricallyConnected_fiber (f := qbar i)).mpr (h i).2.2.1
  have : IsZariskiLocalAtTarget @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  refine ⟨hp, IsZariskiLocalAtTarget.sigmaMap (P := @Smooth) qbar fun i => (h i).2.1, ?_, ?_⟩
  · have := IsZariskiLocalAtTarget.sigmaMap (P := geometrically (ConnectedSpace ·)) qbar
      fun i => by rw [← GeometricallyConnected.eq_geometrically]; exact hgc i
    rwa [← GeometricallyConnected.eq_geometrically] at this
  · intro s
    obtain ⟨k, t, rfl⟩ := (sigmaOpenCover T).exists_eq s
    have e := congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback (isPullback_sigmaMap qbar k)) t
    change (Limits.Sigma.map qbar).fiberDimension (Sigma.ι T k t) ≤ 1
    exact (e.symm.trans_le ((h k).2.2.2 t) : _)

end AlgebraicGeometry

end
