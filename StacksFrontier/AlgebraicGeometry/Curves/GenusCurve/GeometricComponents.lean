module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Geometric
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusIrreducible

/-!
# Additivity of the geometric genus over irreducible components

Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`.  The
geometric genus of `X` over `k` is the sum of the geometric genera of the irreducible components
of `X` of dimension one, each taken with its reduced closed subscheme structure.

## Main results

* `AlgebraicGeometry.geometricGenus_eq_sum_all_components`: the geometric genus of a proper
  scheme over a field is the sum, over *all* its irreducible components, of their geometric
  genera.
* `AlgebraicGeometry.geometricGenus_eq_sum_components`: for a proper scheme of dimension at most
  one, the geometric genus is the sum of the geometric genera of the components of dimension
  one.

## References

* [Stacks Project, Tag 0CE1](https://stacks.math.columbia.edu/tag/0CE1)
* [Stacks Project, Tag 0CE0](https://stacks.math.columbia.edu/tag/0CE0)
* [Stacks Project, Tag 04KX](https://stacks.math.columbia.edu/tag/04KX)
* [Stacks Project, Tag 04KW](https://stacks.math.columbia.edu/tag/04KW)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-! ### Irreducible components and embeddings -/

/-- The preimage of an irreducible closed subset contained in the range of an embedding is
irreducible. -/
theorem isIrreducible_preimage_of_isEmbedding {A : Type u} {Y : Type v}
    [TopologicalSpace A] [TopologicalSpace Y] [QuasiSober Y]
    {f : A → Y} (hf : Topology.IsEmbedding f)
    {Z : Set Y} (hZ : IsIrreducible Z) (hZc : IsClosed Z)
    (hZf : Z ⊆ Set.range f) : IsIrreducible (f ⁻¹' Z) := by
  obtain ⟨x, hx⟩ := hZf (hZ.isGenericPoint_genericPoint hZc).mem
  have he : closure ({x} : Set A) = f ⁻¹' Z := by
    rw [hf.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hx,
      (hZ.isGenericPoint_genericPoint hZc).def]
  exact he ▸ isIrreducible_singleton.closure

/-- The preimage under an embedding of an irreducible component contained in its range is an
irreducible component. -/
private theorem preimage_mem_irreducibleComponents_of_isEmbedding {A : Type u} {Y : Type v}
    [TopologicalSpace A] [TopologicalSpace Y] [QuasiSober Y]
    {f : A → Y} (hf : Topology.IsEmbedding f)
    {Z : Set Y} (hZ : Z ∈ irreducibleComponents Y)
    (hZf : Z ⊆ Set.range f) : f ⁻¹' Z ∈ irreducibleComponents A := by
  refine ⟨isIrreducible_preimage_of_isEmbedding hf hZ.1
    (isClosed_of_mem_irreducibleComponents _ hZ) hZf, ?_⟩
  intro T hT hZT
  have hsub : Z ⊆ f '' T := by
    rw [← Set.image_preimage_eq_of_subset hZf]
    exact Set.image_mono hZT
  exact Set.image_subset_iff.mp (hZ.2 (hT.image f hf.continuous.continuousOn) hsub)

/-- If the range of an embedding is a finite union of irreducible components of the target, then
the image of an irreducible component of the source is an irreducible component of the target. -/
private theorem image_mem_irreducibleComponents_of_isEmbedding {A : Type u} {Y : Type v}
    [TopologicalSpace A] [TopologicalSpace Y] [QuasiSober Y]
    {f : A → Y} (hf : Topology.IsEmbedding f)
    (S : Set (Set Y)) (hS : S.Finite) (hSc : S ⊆ irreducibleComponents Y)
    (hr : Set.range f = ⋃₀ S) {Z : Set A} (hZ : Z ∈ irreducibleComponents A) :
    f '' Z ∈ irreducibleComponents Y := by
  have hirr := hZ.1.image f hf.continuous.continuousOn
  obtain ⟨T, hT, hZT⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr hS.toFinset
    (fun T hT ↦ isClosed_of_mem_irreducibleComponents _ (hSc (hS.mem_toFinset.mp hT)))
    (by rw [hS.coe_toFinset, ← hr]; exact Set.image_subset_range _ _)
  have hTc := hSc (hS.mem_toFinset.mp hT)
  have hTr : T ⊆ Set.range f := hr ▸ Set.subset_sUnion_of_mem (hS.mem_toFinset.mp hT)
  have he : Z = f ⁻¹' T :=
    Set.Subset.antisymm (Set.image_subset_iff.mp hZT)
      (hZ.2 (isIrreducible_preimage_of_isEmbedding hf hTc.1
        (isClosed_of_mem_irreducibleComponents _ hTc) hTr) (Set.image_subset_iff.mp hZT))
  rwa [he, Set.image_preimage_eq_of_subset hTr]

/-! ### Transporting a reduced closed subscheme along a closed immersion -/

/-- Let `f : A ⟶ Y` be a closed immersion and let `Z ⊆ A` be closed with image `W ⊆ Y`.  The
reduced closed subschemes of `A` and of `Y` cut out by `Z` and by `W` are isomorphic over `Y`. -/
theorem exists_subschemeIso_of_image_eq
    {A Y : Scheme.{u}} (f : A ⟶ Y) [IsClosedImmersion f]
    (Z : Closeds A) (W : Closeds Y) (hW : f.base '' (Z : Set A) = W) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅
      (Scheme.IdealSheafData.vanishingIdeal W).subscheme,
      e.hom ≫ (Scheme.IdealSheafData.vanishingIdeal W).subschemeι =
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let J := Scheme.IdealSheafData.vanishingIdeal W
  let i := I.subschemeι ≫ f
  let j := J.subschemeι
  have himage : Scheme.IdealSheafData.map I f = J := by
    rw [Scheme.IdealSheafData.map_vanishingIdeal]
    congr 1
    refine Closeds.ext ?_
    change closure (f.base '' (Z : Set A)) = (W : Set Y)
    rw [hW, W.isClosed.closure_eq]
  have hker : i.ker = j.ker := by
    simpa [i, j, Scheme.IdealSheafData.map] using himage
  let e : I.subscheme ⟶ J.subscheme :=
    IsClosedImmersion.lift j i hker.symm.le
  have he : e ≫ j = i := IsClosedImmersion.lift_fac j i hker.symm.le
  have : IsIso e := IsClosedImmersion.isIso_of_ker_eq i j e he hker
  exact ⟨asIso e, he⟩

/-! ### The contribution of an irreducible component -/

/-- The contribution of an irreducible component `C` of `X` to the genus formula: the genus of
the normalization of `C` with its reduced structure when `C` has dimension one, and zero
otherwise. -/
private abbrev componentContribution (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (C : irreducibleComponents X) : ℕ :=
  if topologicalKrullDim (irreducibleComponentIdeal C).subscheme = 1 then
    genus (normalizationOverField k ((irreducibleComponentIdeal C).subschemeι ≫ p) ≫
      ((irreducibleComponentIdeal C).subschemeι ≫ p))
  else 0

/-- A closed immersion matches the contribution of an irreducible component of its source with
the contribution of the corresponding irreducible component of its target. -/
private theorem componentContribution_image {k : Type u} [Field k] {A Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [IsProper p] (f : A ⟶ Y) [IsClosedImmersion f]
    (D : irreducibleComponents A) (E : irreducibleComponents Y)
    (hE : f.base '' (D : Set A) = E) :
    componentContribution k (f ≫ p) D = componentContribution k p E := by
  obtain ⟨e, he⟩ := exists_subschemeIso_of_image_eq f
    ⟨D.1, isClosed_of_mem_irreducibleComponents _ D.2⟩
    ⟨E.1, isClosed_of_mem_irreducibleComponents _ E.2⟩ hE
  have hd := IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph
  dsimp [componentContribution]
  rw [hd]
  split_ifs with h
  · exact genus_normalizationOverField_eq_of_isIso _ _ e.hom (by simp [← Category.assoc, he])
  · rfl

/-! ### Base change of a closed subscheme -/

/-- The base change of a closed subscheme `C ⊆ X` along a morphism `T ⟶ S`, as a morphism into
the base change of `X`. -/
private abbrev baseChangeInclusion {C X S T : Scheme.{u}}
    (i : C ⟶ X) (g : X ⟶ S) (s : T ⟶ S) :
    pullback (C := Scheme.{u}) (i ≫ g) s ⟶ pullback (C := Scheme.{u}) g s :=
  pullback.map (i ≫ g) s g s i (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The base change of a closed subscheme is compatible with the first projections. -/
private theorem baseChangeInclusion_fst {C X S T : Scheme.{u}}
    (i : C ⟶ X) (g : X ⟶ S) (s : T ⟶ S) :
    baseChangeInclusion i g s ≫ pullback.fst g s = pullback.fst (i ≫ g) s ≫ i := by
  simp [baseChangeInclusion, pullback.map]

/-- The base change of a closed subscheme is compatible with the second projections. -/
private theorem baseChangeInclusion_snd {C X S T : Scheme.{u}}
    (i : C ⟶ X) (g : X ⟶ S) (s : T ⟶ S) :
    baseChangeInclusion i g s ≫ pullback.snd g s = pullback.snd (i ≫ g) s := by
  simp [baseChangeInclusion, pullback.map]

/-- The base change of a closed immersion is a closed immersion. -/
private theorem isClosedImmersion_baseChangeInclusion {C X S T : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (g : X ⟶ S) (s : T ⟶ S) :
    IsClosedImmersion (baseChangeInclusion i g s) := by
  have h : IsPullback (baseChangeInclusion i g s) (pullback.fst (i ≫ g) s)
      (pullback.fst g s) i :=
    .of_right (t := .flip <| .of_hasPullback ..)
      (by simpa [baseChangeInclusion_snd] using (IsPullback.of_hasPullback (i ≫ g) s).flip)
      (by simp)
  exact (IsClosedImmersion.isStableUnderBaseChange).of_isPullback h.flip inferInstance

/-- The base change of a closed subscheme has for underlying set the preimage of that
subscheme. -/
private theorem range_baseChangeInclusion {C X S T : Scheme.{u}}
    (i : C ⟶ X) (g : X ⟶ S) (s : T ⟶ S) :
    Set.range (baseChangeInclusion i g s).base =
      (pullback.fst g s).base ⁻¹' Set.range i.base := by
  simp [baseChangeInclusion, Scheme.Pullback.range_map]

/-- An irreducible component, with its reduced structure, is an irreducible scheme. -/
private theorem irreducibleSpace_irreducibleComponentIdeal {X : Scheme.{u}}
    (C : irreducibleComponents X) : IrreducibleSpace (irreducibleComponentIdeal C).subscheme := by
  apply Subtype.irreducibleSpace
  simpa [irreducibleComponentIdeal] using C.2.1

/-- An irreducible component of the base change of an irreducible component `C` of `X` is an
irreducible component of the base change of `X`. -/
private theorem image_baseChangeInclusion_mem_irreducibleComponents
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (C : irreducibleComponents X)
    (D : irreducibleComponents (pullback (C := Scheme.{u})
      ((irreducibleComponentIdeal C).subschemeι ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    (baseChangeInclusion (irreducibleComponentIdeal C).subschemeι g
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' (D : Set _) ∈
      irreducibleComponents
        (pullback (C := Scheme.{u}) g (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := pullback (C := Scheme.{u}) g s
  let π := pullback.fst g s
  let j := baseChangeInclusion (irreducibleComponentIdeal C).subschemeι g s
  have : IsNoetherian Y := {}
  have : IsClosedImmersion j := isClosedImmersion_baseChangeInclusion _ _ _
  apply image_mem_irreducibleComponents_of_isEmbedding j.isClosedEmbedding.isEmbedding
    {Z : Set Y | Z ∈ irreducibleComponents Y ∧ Z ⊆ π.base ⁻¹' (C : Set X)}
    ((finite_irreducibleComponents_of_isNoetherian (X := Y)).subset (fun _ h ↦ h.1))
    (fun _ h ↦ h.1) _ D.2
  rw [range_baseChangeInclusion]
  simpa [irreducibleComponentIdeal] using
    preimage_irreducibleComponent_eq_sUnion k K X g C.1 C.2

/-- An irreducible component of the base change of an irreducible component `C` of `X` lies over
`C`: its image in `X` is all of `C`. -/
@[ega "IV 2.3.4" "(iii), special case"]
private theorem image_baseChangeInclusion_image_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    (C : irreducibleComponents X)
    (D : irreducibleComponents (pullback (C := Scheme.{u})
      ((irreducibleComponentIdeal C).subschemeι ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base ''
      ((baseChangeInclusion (irreducibleComponentIdeal C).subschemeι g
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' (D : Set _)) = C := by
  have := irreducibleSpace_irreducibleComponentIdeal C
  have hD := mapsTo_irreducibleComponents_baseChange k K _
    ((irreducibleComponentIdeal C).subschemeι ≫ g) D.2
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hD
  dsimp only at hD
  calc
    _ = (irreducibleComponentIdeal C).subschemeι.base ''
        ((pullback.fst ((irreducibleComponentIdeal C).subschemeι ≫ g)
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' (D : Set _)) := by
      rw [← Set.image_comp, ← Set.image_comp]
      congr 1
      funext x
      exact congrArg (fun q : _ ⟶ X ↦ q.base x) (baseChangeInclusion_fst _ _ _)
    _ = C := by
      rw [hD, Set.image_univ]
      simp [irreducibleComponentIdeal]

/-! ### Reindexing the sum -/

/-- The sum of the contributions of the irreducible components of a base change of `X` equals the
iterated sum, over the irreducible components `C` of `X`, of the contributions of the irreducible
components of the base change of `C`. -/
private theorem sum_componentContribution_baseChange (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    [Fintype (irreducibleComponents X)] :
    let s := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let Y := pullback (C := Scheme.{u}) g s
    let : IsNoetherian Y := {}
    let : Finite (irreducibleComponents Y) :=
      (finite_irreducibleComponents_of_isNoetherian (X := Y)).to_subtype
    let : Fintype (irreducibleComponents Y) := Fintype.ofFinite _
    ∑ E : irreducibleComponents Y, componentContribution K (pullback.snd g s) E =
      ∑ C : irreducibleComponents X,
        let A := pullback (C := Scheme.{u}) ((irreducibleComponentIdeal C).subschemeι ≫ g) s
        let : IsNoetherian A := {}
        let : Finite (irreducibleComponents A) :=
          (finite_irreducibleComponents_of_isNoetherian (X := A)).to_subtype
        let : Fintype (irreducibleComponents A) := Fintype.ofFinite _
        ∑ D : irreducibleComponents A,
          componentContribution K
            (pullback.snd ((irreducibleComponentIdeal C).subschemeι ≫ g) s) D := by
  classical
  intro s Y _ _ _
  let A (C : irreducibleComponents X) :=
    pullback (C := Scheme.{u}) ((irreducibleComponentIdeal C).subschemeι ≫ g) s
  let j (C : irreducibleComponents X) :=
    baseChangeInclusion (irreducibleComponentIdeal C).subschemeι g s
  have (C : irreducibleComponents X) : IsNoetherian (A C) := {}
  have (C : irreducibleComponents X) : IsClosedImmersion (j C) :=
    isClosedImmersion_baseChangeInclusion _ _ _
  let (C : irreducibleComponents X) : Finite (irreducibleComponents (A C)) :=
    (finite_irreducibleComponents_of_isNoetherian (X := A C)).to_subtype
  let (C : irreducibleComponents X) : Fintype (irreducibleComponents (A C)) :=
    Fintype.ofFinite _
  let f : (Σ C : irreducibleComponents X, irreducibleComponents (A C)) →
      irreducibleComponents Y := fun CD ↦
    ⟨(j CD.1).base '' (CD.2 : Set _),
      image_baseChangeInclusion_mem_irreducibleComponents k K g CD.1 CD.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun ⟨C, D⟩ ⟨C', D'⟩ h ↦ ?_, fun E ↦ ?_⟩
    · obtain rfl : C = C' := Subtype.ext (by
        rw [← image_baseChangeInclusion_image_eq k K g C D,
          ← image_baseChangeInclusion_image_eq k K g C' D']
        exact congrArg (fun E : irreducibleComponents Y ↦
          (pullback.fst g s).base '' (E : Set Y)) h)
      obtain rfl : D = D' := Subtype.ext
        ((Set.image_injective.mpr (j C).isClosedEmbedding.injective) (congrArg Subtype.val h))
      rfl
    · let C : irreducibleComponents X :=
        ⟨(pullback.fst g s).base '' (E : Set Y),
          mapsTo_irreducibleComponents_baseChange k K X g E.2⟩
      have hr : (E : Set Y) ⊆ Set.range (j C).base := by
        rw [range_baseChangeInclusion]
        simpa [irreducibleComponentIdeal, C] using
          (Set.subset_preimage_image (pullback.fst g s).base (E : Set Y))
      let D : irreducibleComponents (A C) :=
        ⟨(j C).base ⁻¹' (E : Set Y), preimage_mem_irreducibleComponents_of_isEmbedding
          (j C).isClosedEmbedding.isEmbedding E.2 hr⟩
      exact ⟨⟨C, D⟩, Subtype.ext (Set.image_preimage_eq_of_subset hr)⟩
  let e := Equiv.ofBijective f hf
  change ∑ E, componentContribution K (pullback.snd g s) E = ∑ C, ∑ D,
    componentContribution K
      (pullback.snd ((irreducibleComponentIdeal C).subschemeι ≫ g) s) D
  rw [← Fintype.sum_sigma (f := fun CD :
    (Σ C : irreducibleComponents X, irreducibleComponents (A C)) ↦
      componentContribution K
        (pullback.snd ((irreducibleComponentIdeal CD.1).subschemeι ≫ g) s) CD.2)]
  refine (Fintype.sum_equiv e _ _ fun CD ↦ ?_).symm
  simpa [e, Equiv.ofBijective_apply, j, baseChangeInclusion_snd] using
    componentContribution_image (pullback.snd g s) (j CD.1) CD.2 (f CD) rfl

/-! ### Additivity of the geometric genus -/

/-- The geometric genus of a proper scheme over a field is the sum of the geometric genera of all
its irreducible components, each with its reduced closed subscheme structure. -/
public theorem geometricGenus_eq_sum_all_components {k : Type u} [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    [Fintype (irreducibleComponents X)] :
    geometricGenus k g = ∑ C : irreducibleComponents X,
      geometricGenus k ((irreducibleComponentIdeal C).subschemeι ≫ g) :=
  sum_componentContribution_baseChange k (AlgebraicClosure k) g

/-- Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`. The
geometric genus of `X` over `k` is the sum of the geometric genera of
the irreducible components of `X` of dimension one, each taken with its reduced closed subscheme
structure; components of dimension zero contribute nothing. -/
@[stacks 0CE1]
public theorem geometricGenus_eq_sum_components {k : Type u} [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hX : topologicalKrullDim X ≤ 1) :
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
    letI : Finite (irreducibleComponents X) :=
      (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
    letI : Fintype (irreducibleComponents X) := Fintype.ofFinite _
    geometricGenus k g =
      ∑ C : irreducibleComponents X,
        if topologicalKrullDim (irreducibleComponentIdeal C).subscheme = 1 then
          geometricGenus k ((irreducibleComponentIdeal C).subschemeι ≫ g)
        else 0 := by
  classical
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  let : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  rw [geometricGenus_eq_sum_all_components]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  split_ifs with hC
  · rfl
  · exact geometricGenus_eq_zero_of_dim_lt_one _ (lt_of_le_of_ne
      ((Topology.IsInducing.topologicalKrullDim_le
        (irreducibleComponentIdeal C).subschemeι.isClosedEmbedding.isEmbedding.isInducing).trans hX)
      hC)

end AlgebraicGeometry

end
