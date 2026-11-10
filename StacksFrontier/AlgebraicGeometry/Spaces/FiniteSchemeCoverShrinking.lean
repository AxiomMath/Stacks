module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverEtaleOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoverSchematicNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.WeilDivisor
public import StacksFrontier.Topology.Sober.Generization

/-!
# Shrinking the dense open of a finite scheme cover

Let `X` be a quasi-separated algebraic space over a scheme `S` whose space of points `|X|` has
finitely many irreducible components, and let `f : Y ⟶ X` be a finite morphism of finite
presentation from a scheme `Y`, finite étale over a quasi-compact dense open subspace `U ⊆ X`
(the conclusion of clause (1) of Stacks 0GUN). The finitely many generic points `ξ₁, …, ξₖ` of
the irreducible components of `|X|` lie in `|U|`, so `f` is étale at every point over them, and
these points are therefore the generic points `η₁, …, ηₙ` of finitely many distinct irreducible
components of `Y`; there are finitely many of them because the fibres of a finite morphism are
finite. If `V ⊆ Y` is an open containing every `ηᵢ`, the image under `f` of `Y ∖ V` is closed and
misses every `ξⱼ`, so a quasi-compact open neighbourhood `U' ⊆ U` of `{ξ₁, …, ξₖ}` avoiding it
exists, because quasi-compact opens form a basis of `|X|`. Then `U'` is dense, and
`f⁻¹(U') ⊆ V`. This is the step "after shrinking `U` we may assume `f⁻¹(U) ⊂ V`" of the proof
of Stacks 0GV5.

## Main results

* `PrespectralSpace.exists_isOpen_isCompact_subset_of_finite`: in a prespectral space a finite
  subset of an open set lies in a compact open subset of it.
* `AlgebraicGeometry.Space.IsFiniteSchemeCoverFiniteEtaleOverDenseOpen.exists_shrink`: the
  shrinking step.

## References

* [Stacks Project, Tag 0GUN](https://stacks.math.columbia.edu/tag/0GUN)
* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

/-- In a prespectral space, a finite subset `s` of an open set `O` is contained in a compact open
subset of `O`. -/
theorem PrespectralSpace.exists_isOpen_isCompact_subset_of_finite {α : Type*}
    [TopologicalSpace α] [PrespectralSpace α] {s O : Set α} (hs : s.Finite) (hO : IsOpen O)
    (hsO : s ⊆ O) : ∃ K : Set α, IsOpen K ∧ IsCompact K ∧ s ⊆ K ∧ K ⊆ O := by
  have h (x : s) : ∃ K : Set α, K ∈ {U : Set α | IsOpen U ∧ IsCompact U} ∧ x.1 ∈ K ∧ K ⊆ O :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (hsO x.2) hO
  choose K hK hxK hKO using h
  have : Finite s := hs.to_subtype
  exact ⟨⋃ x, K x, isOpen_iUnion fun x => (hK x).1, isCompact_iUnion fun x => (hK x).2,
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxK ⟨x, hx⟩⟩, Set.iUnion_subset hKO⟩

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Shrinking the dense open of a finite scheme cover.** Let `X` be a quasi-separated algebraic
space whose space of points has finitely many irreducible components, and let `f : h_Y ⟶ X` be a
finite and finitely presented morphism from a scheme `T`, finite étale over the quasi-compact
dense open subspace `U`, as in clause (1) of Stacks 0GUN. Then there are finitely many distinct
irreducible components `Zᵢ` of `T`, with generic points `ηᵢ`, such that for every open `V ⊆ T`
containing all the `ηᵢ` there is a quasi-compact dense open subspace `U' ≤ U` of `X` with
`f⁻¹(|U'|) ⊆ V`.

The `ηᵢ` are the points of `T` lying over the generic points of `|X|`. -/
theorem IsFiniteSchemeCoverFiniteEtaleOverDenseOpen.exists_shrink
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hXfin : (irreducibleComponents (points B S hS X)).Finite)
    {Y : BigFppfOver B S hS} {f : yoneda.obj Y ⟶ X} {U : Subfunctor X}
    (hf : IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U) :
    ∃ (n : ℕ) (Z : Fin n → Set ((BigFppfOver.toScheme B S hS).obj Y))
      (η : Fin n → (BigFppfOver.toScheme B S hS).obj Y),
      (∀ i, Z i ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj Y)) ∧
      Function.Injective Z ∧ (∀ i, IsGenericPoint (η i) (Z i)) ∧
      ∀ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, (∀ i, η i ∈ V) →
        ∃ U' : Subfunctor X, IsOpenSubspace B S hS U' ∧
          IsQuasiCompactSpace B S hS U'.toFunctor ∧ Dense (subspacePointSet B S hS X U') ∧
          U' ≤ U ∧ ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
            pointsMap B S hS _ f ((schemePointsHomeomorph B S hS Y).symm y) ∈
              subspacePointSet B S hS X U' → y ∈ V := by
  classical
  obtain ⟨-, hfin, hfp, hU, -, hUdense, -, hUet⟩ := hf
  set T := (BigFppfOver.toScheme B S hS).obj Y
  set e : points B S hS (yoneda.obj Y) ≃ₜ T := schemePointsHomeomorph B S hS Y
  set φ := pointsMap B S hS (yoneda.obj Y) f
  have hYalg : IsAlgebraicSpace B S hS (yoneda.obj Y) := isAlgebraicSpace_yoneda B S hS Y
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj Y) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hYalg hXqs hfp.2.2
  have hXdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hXqs
  have _ := t0Space_points_of_isDecentSpace B S hS hX hXdec
  have _ := quasiSober_points_of_isDecentSpace B S hS hX hXdec
  have _ := prespectralSpace_points B S hS X hX
  have _ : T0Space (points B S hS (yoneda.obj Y)) := e.isEmbedding.t0Space
  -- The generic points of `|X|` lie in `|U|`.
  set G := genericPoints (points B S hS X)
  have hGfin : G.Finite := genericPoints.finite hXfin
  have hUopen : IsOpen (subspacePointSet B S hS X U) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2
  have hGU : G ⊆ subspacePointSet B S hS X U := fun ξ hξ =>
    mem_of_mem_genericPoints_of_dense hUopen hUdense hXfin hξ
  -- The points over them are finitely many generic points of `T`.
  set E := φ ⁻¹' G
  have hEfin : E.Finite := hGfin.preimage' fun ξ _ =>
    finite_preimage_singleton_of_isFinite B S hS hYalg hX f hfin ξ
  have hEgen : ∀ y ∈ E, e y ∈ genericPoints T := by
    intro y hy
    have hyet : IsEtaleAt B S hS f y :=
      isEtaleAt_of_isEtale_pullback_fst B S hS hX hYalg U hU f hUet y (hGU hy)
    have hygen : y ∈ genericPoints (points B S hS (yoneda.obj Y)) :=
      (hyet.mem_genericPoints_iff B S hS hZ hYalg hX hYqs hXqs).1 hy
    refine mem_genericPoints_of_forall_specializes_eq fun t ht => ?_
    have h := forall_specializes_eq_of_mem_genericPoints hygen (e.symm t)
      (by simpa using ht.map e.symm.continuous)
    rw [← h, Homeomorph.apply_symm_apply]
  -- Enumerate them.
  set E' : Finset T := (hEfin.image e).toFinset
  set η : Fin E'.card → T := fun i => (E'.equivFin.symm i).1
  have hηgen : ∀ i, η i ∈ genericPoints T := by
    intro i
    obtain ⟨y, hy, hyη⟩ := (hEfin.image e).mem_toFinset.1 (E'.equivFin.symm i).2
    rw [show η i = e y from hyη.symm]
    exact hEgen y hy
  have hEη : ∀ y ∈ E, ∃ i, η i = e y := fun y hy =>
    ⟨E'.equivFin ⟨e y, (hEfin.image e).mem_toFinset.2 ⟨y, hy, rfl⟩⟩, by simp [η]⟩
  refine ⟨E'.card, fun i => closure {η i}, η, hηgen, fun i j hij => ?_, fun i => rfl, ?_⟩
  · have hij' : η i = η j := IsGenericPoint.eq (x := η i) (y := η j) rfl hij.symm
    exact E'.equivFin.symm.injective (Subtype.ext hij')
  intro V hV
  -- The image of the complement of `V` is closed and misses every generic point of `|X|`.
  set W : Set (points B S hS (yoneda.obj Y)) := e ⁻¹' V
  have hEW : E ⊆ W := fun y hy => by
    obtain ⟨i, hi⟩ := hEη y hy
    change e y ∈ V
    rw [← hi]
    exact hV i
  have hCcl : IsClosed (φ '' Wᶜ) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS f
      (universallyClosed_of_isFinite B S hS hYalg hX hfin X hX (𝟙 X)) _
      (V.2.preimage e.continuous).isClosed_compl
  have hGC : G ⊆ subspacePointSet B S hS X U ∩ (φ '' Wᶜ)ᶜ := by
    refine fun ξ hξ => ⟨hGU hξ, ?_⟩
    rintro ⟨y, hyW, rfl⟩
    exact hyW (hEW hξ)
  obtain ⟨K, hKopen, hKcpt, hGK, hKsub⟩ :=
    PrespectralSpace.exists_isOpen_isCompact_subset_of_finite hGfin
      (hUopen.inter hCcl.isOpen_compl) hGC
  obtain ⟨U', hU', hU'K⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX K hKopen
  refine ⟨U', hU', isQuasiCompactSpace_of_isCompact_range B S hS hX hU' (hU'K ▸ hKcpt), ?_,
    le_of_range_pointsMap_ι_subset B S hS hU (hU'K ▸ fun x hx => (hKsub hx).1), ?_⟩
  · change Dense (Set.range (pointsMap B S hS U'.toFunctor U'.ι))
    rw [hU'K]
    exact (dense_iff_closure_eq.2 genericPoints.closure).mono hGK
  · intro y hy
    change φ (e.symm y) ∈ Set.range (pointsMap B S hS U'.toFunctor U'.ι) at hy
    rw [hU'K] at hy
    by_contra hyV
    exact (hKsub hy).2 ⟨e.symm y, by simpa [W] using hyV, rfl⟩

end AlgebraicGeometry.Space

end
