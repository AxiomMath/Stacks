module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMap

/-!
# Reduction of the generic-point map to the irreducible components

For a scheme with finitely many irreducible components and chosen generic points, remove the
pairwise intersections of the components. The resulting dense open is the disjoint union of its
pieces lying in the components. Rational maps on the source, and their evaluation at the generic
points, therefore decompose over these pieces.

## Main definitions

* `AlgebraicGeometry.GenericPointMapContext.ComponentRationalMapsOver` is the type of rational
  maps over the base out of an open piece of a dense open of the source.
* `AlgebraicGeometry.GenericPointMapContext.IrreducibleComponentReduction` records the dense
  open, its componentwise decomposition, and the induced decompositions of rational maps and of
  the generic-point map.

## Main results

* `AlgebraicGeometry.GenericPointMapContext.nonempty_irreducibleComponentReduction` constructs
  the reduction.
* `AlgebraicGeometry.GenericPointMapContext.injective_genericPointMap_iff_components` and
  `AlgebraicGeometry.GenericPointMapContext.surjective_genericPointMap_iff_components` give
  componentwise criteria for injectivity and surjectivity, including the degenerate cases.

## Implementation notes

Well-definedness of the generic-point map is part of the representative-independence
specification in `AlgebraicGeometry.GenericPointMapContext.GenericPointMap`; this file uses the
canonical map constructed there. The component pieces are open subsets of the dense open, rather
than open subsets of the original scheme. The equivalence `restrictRationalMapsEquiv` expresses
both invariance under passage to the dense open and the product decomposition on that open.
Componentwise evaluation is characterized on every representative over the base, by its image
point and its stalk map transported through the three open immersions from the representative's
domain to the component piece, the dense open, and the original source. Heterogeneous equality
accounts for the equality identifying the point in that domain with the chosen generic point of
the source.

An empty domain makes the global map injective, and an empty codomain makes it surjective, even
when the corresponding componentwise property fails; the criteria account for these cases without
any inhabitation hypotheses.

## References

* [Stacks Project, Section 29.49, Lemma 0BX8](https://stacks.math.columbia.edu/tag/0BX8)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

namespace GenericPointMapContext

variable (C : GenericPointMapContext.{u})



/-- Rational maps over the base whose source is an open piece of a dense open
of `C.X`. -/
public abbrev ComponentRationalMapsOver (U : C.X.Opens) (V : U.toScheme.Opens) :=
  {f : V.toScheme.RationalMap C.Y //
    f.compHom C.toBaseTarget = (V.ι ≫ U.ι ≫ C.toBaseSource).toRationalMap}

/-- The componentwise description obtained after deleting all pairwise
intersections of the irreducible components of the source. -/
public structure IrreducibleComponentReduction where
  /-- The complement of the pairwise intersections of the components. -/
  denseOpen : C.X.Opens
  dense_denseOpen : Dense (denseOpen : Set C.X)
  denseOpen_carrier :
    (denseOpen : Set C.X) =
      {x | ∀ i j, i ≠ j → x ∉ (C.components i : Set C.X) ∩ (C.components j : Set C.X)}
  /-- The part of each irreducible component in the dense open. -/
  componentOpen : Fin C.numberOfComponents → denseOpen.toScheme.Opens
  componentOpen_carrier (i) :
    (componentOpen i : Set denseOpen.toScheme) =
      {x : denseOpen.toScheme | x.1 ∈ (C.components i : Set C.X)}
  pairwise_disjoint_componentOpen :
    ∀ i j, i ≠ j → Disjoint (componentOpen i) (componentOpen j)
  iSup_componentOpen : (⨆ i, componentOpen i) = ⊤
  /-- Restriction to the component pieces is the product decomposition of
  rational maps. -/
  restrictRationalMapsEquiv :
    C.RationalMapsOver ≃ ∀ i, ComponentRationalMapsOver C denseOpen (componentOpen i)
  /-- Evaluation at the generic point of one component. -/
  componentGenericPointMap (i) :
    ComponentRationalMapsOver C denseOpen (componentOpen i) → C.GenericPointLocalMap i
  /-- Componentwise evaluation sends a representative to its value at the
  chosen generic point. -/
  componentGenericPointMap_point (i)
      (f : ComponentRationalMapsOver C denseOpen (componentOpen i))
      (g : (componentOpen i).toScheme.PartialMap C.Y)
      (represents : g.toRationalMap = f.1)
      (over : g.hom ≫ C.toBaseTarget =
        g.domain.ι ≫ (componentOpen i).ι ≫ denseOpen.ι ≫ C.toBaseSource)
      (x : g.domain) (hx : x.1.1.1 = C.genericPoint i) :
      (componentGenericPointMap i f).point = g.hom x
  /-- The componentwise stalk map is the representative's stalk map, using
  the canonical stalk isomorphisms of the intervening open immersions. -/
  componentGenericPointMap_stalk (i)
      (f : ComponentRationalMapsOver C denseOpen (componentOpen i))
      (g : (componentOpen i).toScheme.PartialMap C.Y)
      (represents : g.toRationalMap = f.1)
      (over : g.hom ≫ C.toBaseTarget =
        g.domain.ι ≫ (componentOpen i).ι ≫ denseOpen.ι ≫ C.toBaseSource)
      (x : g.domain) (hx : x.1.1.1 = C.genericPoint i) :
      HEq (componentGenericPointMap i f).stalkMap
        (g.hom.stalkMap x ≫ (g.domain.stalkIso x).hom ≫
          ((componentOpen i).stalkIso x.1).hom ≫ (denseOpen.stalkIso x.1.1).hom)
  /-- Under the product decomposition, componentwise evaluation is the
  original generic-point map. -/
  componentGenericPointMap_restrict (f : C.RationalMapsOver) :
    (fun i ↦ componentGenericPointMap i (restrictRationalMapsEquiv f i)) =
      C.genericPointMapForRationalMaps f

/-- Every point of `C.X` lies in one of the enumerated irreducible components. -/
private lemma exists_mem_component (x : C.X) : ∃ i, x ∈ (C.components i : Set C.X) := by
  have hxall : x ∈ ⋃₀ irreducibleComponents C.X := by
    rw [sUnion_irreducibleComponents]
    simp
  obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hxall
  refine ⟨C.components.symm ⟨Z, hZ⟩, ?_⟩
  rw [C.components.apply_symm_apply]
  exact hxZ

/-- An open subset of `C.X` containing every chosen generic point is dense. -/
public lemma dense_of_generic_points_mem_open (U : C.X.Opens)
    (hU : ∀ i, C.genericPoint i ∈ U) : Dense (U : Set C.X) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨i, hx⟩ := exists_mem_component C x
  rw [← (C.isGenericPoint i).def] at hx
  exact closure_mono (Set.singleton_subset_iff.mpr (hU i)) hx

private lemma genericPoint_mem_component (i : Fin C.numberOfComponents) :
    C.genericPoint i ∈ (C.components i : Set C.X) :=
  (C.isGenericPoint i).mem

private lemma genericPoint_mem_component_iff (i j : Fin C.numberOfComponents)
    (h : C.genericPoint i ∈ (C.components j : Set C.X)) : i = j := by
  have hle : (C.components i : Set C.X) ⊆ (C.components j : Set C.X) := by
    rw [← (C.isGenericPoint i).def]
    exact closure_minimal (by simpa using h)
      (isClosed_of_mem_irreducibleComponents _ (C.components j).property)
  have hle' : (C.components j : Set C.X) ⊆ (C.components i : Set C.X) :=
    ((C.components i).property).2 (C.components j).property.1 hle
  exact C.components.injective (Subtype.ext (hle.antisymm hle'))

private lemma genericPoint_not_mem_inter_component (i j : Fin C.numberOfComponents)
    (hij : i ≠ j) :
    C.genericPoint i ∉ (C.components i : Set C.X) ∩ (C.components j : Set C.X) :=
  fun h ↦ hij (genericPoint_mem_component_iff C i j h.2)

private noncomputable def disjointComponentLocus : C.X.Opens :=
  ⟨⋂ i, ⋂ j, if h : i = j then Set.univ else
      ((C.components i : Set C.X) ∩ (C.components j : Set C.X))ᶜ,
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => by
      split_ifs with h
      · exact isOpen_univ
      · exact (isClosed_of_mem_irreducibleComponents _ (C.components i).property).inter
          (isClosed_of_mem_irreducibleComponents _ (C.components j).property) |>.isOpen_compl⟩

private lemma disjointComponentLocus_carrier :
    (disjointComponentLocus C : Set C.X) =
      {x | ∀ i j, i ≠ j → x ∉ (C.components i : Set C.X) ∩ (C.components j : Set C.X)} := by
  ext x
  classical
  simp [disjointComponentLocus]

private lemma dense_disjointComponentLocus :
    Dense (disjointComponentLocus C : Set C.X) := by
  apply dense_of_generic_points_mem_open C (disjointComponentLocus C)
  intro i
  show C.genericPoint i ∈ (disjointComponentLocus C : Set C.X)
  rw [disjointComponentLocus_carrier]
  simp only [Set.mem_ofPred_eq]
  intro j k hjk h
  have hij : i = j := genericPoint_mem_component_iff C i j h.1
  have hik : i = k := genericPoint_mem_component_iff C i k h.2
  exact hjk (hij.symm.trans hik)

private noncomputable def componentOpenAux (i : Fin C.numberOfComponents) :
    (disjointComponentLocus C).toScheme.Opens := by
  classical
  let excluded : Set C.X := ⋃ j, if j = i then ∅ else (C.components j : Set C.X)
  have hexcluded : IsClosed excluded := isClosed_iUnion_of_finite fun j => by
    split_ifs
    · exact isClosed_empty
    · exact isClosed_of_mem_irreducibleComponents _ (C.components j).property
  let W : C.X.Opens := ⟨excludedᶜ, hexcluded.isOpen_compl⟩
  refine ⟨{x : (disjointComponentLocus C).toScheme |
    x.1 ∈ (C.components i : Set C.X)}, ?_⟩
  have hcarrier :
      ({x : (disjointComponentLocus C).toScheme |
        x.1 ∈ (C.components i : Set C.X)} :
        Set (disjointComponentLocus C).toScheme) =
        Subtype.val ⁻¹' (W : Set C.X) := by
    ext x
    change x.1 ∈ (C.components i : Set C.X) ↔ x.1 ∉ excluded
    constructor
    · intro hxi hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      split_ifs at hj with hji
      · simp at hj
      · have hxprop : ∀ p q, p ≠ q → x.1 ∉
            (C.components p : Set C.X) ∩ (C.components q : Set C.X) :=
          (congrArg (fun s : Set C.X => x.1 ∈ s)
            (disjointComponentLocus_carrier C)).mp x.2
        have hdisj := hxprop i j (Ne.symm hji)
        exact hdisj ⟨hxi, hj⟩
    · intro hx
      by_contra hxi
      obtain ⟨j, hxj⟩ := exists_mem_component C x.1
      have hji : j ≠ i := by
        intro hji
        apply hxi
        simpa [hji] using hxj
      have : x.1 ∈ excluded := by
        rw [Set.mem_iUnion]
        refine ⟨j, ?_⟩
        simp [hji, hxj]
      exact (hx this).elim
  rw [hcarrier]
  exact (W.2.preimage continuous_subtype_val)

private lemma componentOpenAux_carrier (i : Fin C.numberOfComponents) :
    (componentOpenAux C i : Set (disjointComponentLocus C).toScheme) =
      {x : (disjointComponentLocus C).toScheme |
        x.1 ∈ (C.components i : Set C.X)} :=
  rfl

private lemma pairwise_disjoint_componentOpenAux (i j : Fin C.numberOfComponents)
    (hij : i ≠ j) : Disjoint (componentOpenAux C i) (componentOpenAux C j) := by
  apply (TopologicalSpace.Opens.coe_disjoint).mp
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hxprop : ∀ p q, p ≠ q → (x.1 : C.X) ∉
      (C.components p : Set C.X) ∩ (C.components q : Set C.X) :=
    (congrArg (fun s : Set C.X => (x.1 : C.X) ∈ s)
      (disjointComponentLocus_carrier C)).mp x.2
  exact hxprop i j hij ⟨hxi, hxj⟩

private lemma iSup_componentOpenAux_eq_top :
    (⨆ i : Fin C.numberOfComponents, componentOpenAux C i) = ⊤ := by
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_iSup]
  ext x
  constructor
  · intro _
    simp
  · intro _
    show x ∈ ⋃ i : Fin C.numberOfComponents, (componentOpenAux C i : Set _)
    obtain ⟨i, hxi⟩ := exists_mem_component C x.1
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩

private lemma componentGenericPoint_mem_componentOpenAux
    (i : Fin C.numberOfComponents) :
    (⟨C.genericPoint i,
      genericPoint_mem_dense_open C (disjointComponentLocus C)
        (dense_disjointComponentLocus C) i⟩ :
      (disjointComponentLocus C).toScheme) ∈
        (componentOpenAux C i : Set (disjointComponentLocus C).toScheme) :=
  genericPoint_mem_component C i

private lemma componentOpenAux_preimage_dense
    (i : Fin C.numberOfComponents) (W : C.X.Opens)
    (hη : C.genericPoint i ∈ W) :
    Dense (((componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι) ⁻¹ᵁ W :
      Set (componentOpenAux C i).toScheme) := by
  let e : (componentOpenAux C i).toScheme ⟶ C.X :=
    (componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι
  apply dense_iff_inter_open.mpr
  intro A hA hne
  obtain ⟨x, hx⟩ := hne
  let A' : (componentOpenAux C i).toScheme.Opens := ⟨A, hA⟩
  have hxcomp : e x ∈ (C.components i : Set C.X) := x.2
  have hηA : C.genericPoint i ∈ e ''ᵁ A' :=
    (C.isGenericPoint i).mem_open_set_iff (e ''ᵁ A').2 |>.2 ⟨e x, hxcomp, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, hyeq⟩ := hηA
  refine ⟨y, hy, ?_⟩
  show (e.base y) ∈ W
  exact hyeq ▸ hη

private noncomputable def pullbackComponentPartialMap
    (i : Fin C.numberOfComponents) (g : C.X.PartialMap C.Y)
    (hD : Dense (((componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι) ⁻¹ᵁ
      g.domain : Set (componentOpenAux C i).toScheme)) :
    (componentOpenAux C i).toScheme.PartialMap C.Y := by
  let e : (componentOpenAux C i).toScheme ⟶ C.X :=
    (componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι
  exact ⟨e ⁻¹ᵁ g.domain, hD,
    e.resLE g.domain (e ⁻¹ᵁ g.domain) le_rfl ≫ g.hom⟩

/-- Pulling a partial map over the base back to a component piece keeps it over the base. -/
private lemma pullbackComponentPartialMap_over
    (i : Fin C.numberOfComponents) (g : C.X.PartialMap C.Y)
    (hD : Dense (((componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι) ⁻¹ᵁ
      g.domain : Set (componentOpenAux C i).toScheme))
    (hg : g.hom ≫ C.toBaseTarget = g.domain.ι ≫ C.toBaseSource) :
    (pullbackComponentPartialMap C i g hD).hom ≫ C.toBaseTarget =
      (pullbackComponentPartialMap C i g hD).domain.ι ≫ (componentOpenAux C i).ι ≫
        (disjointComponentLocus C).ι ≫ C.toBaseSource := by
  dsimp only [pullbackComponentPartialMap]
  rw [Category.assoc, hg, ← Category.assoc, Scheme.Hom.resLE_comp_ι]
  rfl

private noncomputable def restrictRationalMapToComponent (i : Fin C.numberOfComponents)
    (f : C.RationalMapsOver) :
    ComponentRationalMapsOver C (disjointComponentLocus C) (componentOpenAux C i) := by
  classical
  let rep := representativeOver C f
  let p := pullbackComponentPartialMap C i rep (componentOpenAux_preimage_dense C i rep.domain
    (genericPoint_mem_dense_open C rep.domain rep.dense_domain i))
  let : (componentOpenAux C i).toScheme.Over C.S :=
    ⟨(componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι ≫ C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  have : p.IsOver C.S := (Scheme.PartialMap.isOver_iff).mpr
    (pullbackComponentPartialMap_over C i rep _ (representativeOver_base C f))
  exact ⟨p.toRationalMap, (Scheme.RationalMap.isOver_iff).mp inferInstance⟩

private lemma pullbackComponentPartialMap_equiv
    (i : Fin C.numberOfComponents) (g h : C.X.PartialMap C.Y)
    (hg : C.genericPoint i ∈ g.domain) (hh : C.genericPoint i ∈ h.domain)
    (he : g.equiv h) :
    (pullbackComponentPartialMap C i g
      (componentOpenAux_preimage_dense C i g.domain hg)).equiv
      (pullbackComponentPartialMap C i h
        (componentOpenAux_preimage_dense C i h.domain hh)) := by
  classical
  obtain ⟨W, hW, hWg, hWh, hmap⟩ := he
  have hηW : C.genericPoint i ∈ W := genericPoint_mem_dense_open C W hW i
  let e : (componentOpenAux C i).toScheme ⟶ C.X :=
    (componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι
  let W' := e ⁻¹ᵁ W
  have hW' : Dense (W' : Set (componentOpenAux C i).toScheme) :=
    componentOpenAux_preimage_dense C i W hηW
  have hW'g : W' ≤ e ⁻¹ᵁ g.domain := e.preimage_mono hWg
  have hW'h : W' ≤ e ⁻¹ᵁ h.domain := e.preimage_mono hWh
  let pg := pullbackComponentPartialMap C i g
    (componentOpenAux_preimage_dense C i g.domain hg)
  let ph := pullbackComponentPartialMap C i h
    (componentOpenAux_preimage_dense C i h.domain hh)
  refine ⟨W', hW', hW'g, hW'h, ?_⟩
  show (pg.restrict W' hW' hW'g).hom = (ph.restrict W' hW' hW'h).hom
  show ((componentOpenAux C i).toScheme.homOfLE hW'g ≫
      e.resLE g.domain (e ⁻¹ᵁ g.domain) le_rfl ≫ g.hom) =
    ((componentOpenAux C i).toScheme.homOfLE hW'h ≫
      e.resLE h.domain (e ⁻¹ᵁ h.domain) le_rfl ≫ h.hom)
  have hfactorG :
      (componentOpenAux C i).toScheme.homOfLE hW'g ≫
          e.resLE g.domain (e ⁻¹ᵁ g.domain) le_rfl =
        e.resLE W W' le_rfl ≫ C.X.homOfLE hWg := by
    apply (cancel_mono g.domain.ι).mp
    simp [Scheme.Hom.resLE, Category.assoc]
    rfl
  have hfactorH :
      (componentOpenAux C i).toScheme.homOfLE hW'h ≫
          e.resLE h.domain (e ⁻¹ᵁ h.domain) le_rfl =
        e.resLE W W' le_rfl ≫ C.X.homOfLE hWh := by
    apply (cancel_mono h.domain.ι).mp
    simp [Scheme.Hom.resLE, Category.assoc]
    rfl
  rw [← Category.assoc, hfactorG, ← Category.assoc, hfactorH]
  exact congrArg (fun k => e.resLE W W' le_rfl ≫ k) hmap

private lemma componentGenericPoint_mem_componentOpen (R : IrreducibleComponentReduction C)
    (i : Fin C.numberOfComponents) :
    (⟨C.genericPoint i, genericPoint_mem_dense_open C R.denseOpen R.dense_denseOpen i⟩ :
      R.denseOpen.toScheme) ∈ (R.componentOpen i : Set R.denseOpen.toScheme) := by
  rw [R.componentOpen_carrier]
  show C.genericPoint i ∈ (C.components i : Set C.X)
  exact genericPoint_mem_component C i

private lemma componentImage_pairwise_disjoint
    (U : C.X.Opens) (V : Fin C.numberOfComponents → U.toScheme.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (W : ∀ i, (V i).toScheme.Opens)
    (i j : Fin C.numberOfComponents) (hij : i ≠ j) :
    Disjoint
      (((V i).ι ≫ U.ι) ''ᵁ W i)
      (((V j).ι ≫ U.ι) ''ᵁ W j) := by
  have h : Disjoint (((V i).ι ≫ U.ι) ''ᵁ ⊤) (((V j).ι ≫ U.ι) ''ᵁ ⊤) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp,
      Scheme.Opens.opensRange_ι, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      ← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
    rintro x ⟨xi, hxi, rfl⟩ ⟨xj, hxj, hxj_eq⟩
    have hV : xi = xj := U.ι.isOpenEmbedding.injective hxj_eq.symm
    exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr (hdisj i j hij)) hxi
      (hV ▸ hxj)
  exact h.mono (((V i).ι ≫ U.ι).image_mono le_top) (((V j).ι ≫ U.ι).image_mono le_top)

private lemma componentRepresentative_generic_mem
    (U : C.X.Opens) (hU : Dense (U : Set C.X))
    (V : Fin C.numberOfComponents → U.toScheme.Opens)
    (hVcarrier : ∀ i, (V i : Set U.toScheme) =
      {x : U.toScheme | x.1 ∈ (C.components i : Set C.X)})
    (g : ∀ i, (V i).toScheme.PartialMap C.Y) (i : Fin C.numberOfComponents) :
    C.genericPoint i ∈ (⨆ j, ((V j).ι ≫ U.ι) ''ᵁ (g j).domain : C.X.Opens) := by
  refine (le_iSup (fun j ↦ ((V j).ι ≫ U.ι) ''ᵁ (g j).domain) i) ?_
  let e : (V i).toScheme ⟶ C.X :=
    (V i).ι ≫ U.ι
  let W : C.X.Opens := e ''ᵁ (g i).domain
  let ηU : U.toScheme := ⟨C.genericPoint i,
    genericPoint_mem_dense_open C U hU i⟩
  have hηV : ηU ∈ (V i : Set U.toScheme) := by
    rw [hVcarrier]
    exact genericPoint_mem_component C i
  let ηV : (V i).toScheme := ⟨ηU, hηV⟩
  let : Nonempty (V i).toScheme := ⟨ηV⟩
  obtain ⟨y, hy⟩ := (g i).dense_domain.nonempty
  let x : (g i).domain := ⟨y, hy⟩
  have hxcomponent (x : (g i).domain) : e x ∈ (C.components i : Set C.X) :=
    (congrArg (fun W : Set U.toScheme => x.1.1 ∈ W) (hVcarrier i)).mp x.1.2
  have hη : C.genericPoint i ∈ W :=
    (IsGenericPoint.mem_open_set_iff (C.isGenericPoint i) W.2).2
      ⟨e x, hxcomponent x, ⟨x, x.2, rfl⟩⟩
  simpa [W, e] using hη

private lemma componentOpenAux_genericPoint_isGeneric (i : Fin C.numberOfComponents) :
    IsGenericPoint
      (⟨⟨C.genericPoint i,
        genericPoint_mem_dense_open C (disjointComponentLocus C)
          (dense_disjointComponentLocus C) i⟩,
        componentGenericPoint_mem_componentOpenAux C i⟩ :
        (componentOpenAux C i).toScheme)
      Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro x
  simp only [Set.mem_univ, iff_true]
  let U := disjointComponentLocus C
  let V := componentOpenAux C i
  let ηU : U.toScheme := ⟨C.genericPoint i,
    genericPoint_mem_dense_open C U (dense_disjointComponentLocus C) i⟩
  let ηV : V.toScheme := ⟨⟨C.genericPoint i,
    genericPoint_mem_dense_open C U (dense_disjointComponentLocus C) i⟩,
    componentGenericPoint_mem_componentOpenAux C i⟩
  let e : V.toScheme ⟶ C.X := V.ι ≫ U.ι
  have hη : e ηV = C.genericPoint i := rfl
  have hx : e x ∈ (C.components i : Set C.X) := (componentOpenAux_carrier C i).le x.2
  refine (e.isOpenEmbedding.isInducing.specializes_iff).mp ?_
  rw [hη]
  exact (C.isGenericPoint i).specializes hx

private lemma componentOpenAux_genericPoint_mem (i : Fin C.numberOfComponents)
    (W : (componentOpenAux C i).toScheme.Opens)
    (hW : Dense (W : Set (componentOpenAux C i).toScheme)) :
    (⟨⟨C.genericPoint i,
      genericPoint_mem_dense_open C (disjointComponentLocus C)
        (dense_disjointComponentLocus C) i⟩,
      componentGenericPoint_mem_componentOpenAux C i⟩ :
        (componentOpenAux C i).toScheme) ∈ W := by
  let η : (componentOpenAux C i).toScheme := ⟨⟨C.genericPoint i,
    genericPoint_mem_dense_open C (disjointComponentLocus C)
      (dense_disjointComponentLocus C) i⟩,
    componentGenericPoint_mem_componentOpenAux C i⟩
  let : Nonempty (componentOpenAux C i).toScheme := ⟨η⟩
  apply (IsGenericPoint.mem_open_set_iff
    (componentOpenAux_genericPoint_isGeneric C i) W.2).2
  obtain ⟨x, hx⟩ := hW.nonempty
  exact ⟨x, Set.mem_univ _, hx⟩

private lemma componentOpenAux_irreducibleSpace (i : Fin C.numberOfComponents) :
    IrreducibleSpace (componentOpenAux C i).toScheme :=
  (irreducibleSpace_def _).2
    (componentOpenAux_genericPoint_isGeneric C i).isIrreducible

private lemma stalkMap_eqToHom_naturality {X Y : Scheme} (f : X ⟶ Y)
    {x x' : X} (h : x = x') :
    f.stalkMap x ≫ eqToHom (congrArg (fun z => X.presheaf.stalk z) h) =
      eqToHom (congrArg (fun z => Y.presheaf.stalk z) (congrArg f h)) ≫
        f.stalkMap x' := by
  cases h
  simp

@[reducible] private noncomputable def componentGenericPointContext (i : Fin C.numberOfComponents)
    (η : (componentOpenAux C i).toScheme)
    (hη : IsGenericPoint η Set.univ) :
    GenericPointMapContext.{u} := by
  let V := componentOpenAux C i
  let : IrreducibleSpace V.toScheme := componentOpenAux_irreducibleSpace C i
  refine {
    S := C.S
    X := V.toScheme
    Y := C.Y
    toBaseSource := V.ι ≫ (disjointComponentLocus C).ι ≫ C.toBaseSource
    toBaseTarget := C.toBaseTarget
    numberOfComponents := 1
    components := {
      toFun := fun _ ↦ ⟨Set.univ, by
        simp [irreducibleComponents_eq_singleton]⟩
      invFun := fun _ ↦ 0
      left_inv := by intro j; fin_cases j; rfl
      right_inv := by
        intro Z
        apply Subtype.ext
        have hZ' : Z.1 = Set.univ := by
          apply Set.mem_singleton_iff.mp
          simpa [irreducibleComponents_eq_singleton] using Z.2
        exact hZ'.symm }
    genericPoint := fun _ ↦ η
    isGenericPoint := by
      intro j
      fin_cases j
      change IsGenericPoint η Set.univ
      exact hη }

private noncomputable def componentGenericPointMapAux
    (i : Fin C.numberOfComponents) :
    ComponentRationalMapsOver C (disjointComponentLocus C) (componentOpenAux C i) →
      C.GenericPointLocalMap i := by
  let U := disjointComponentLocus C
  let V := componentOpenAux C i
  let ηU : U.toScheme := ⟨C.genericPoint i,
    genericPoint_mem_dense_open C U (dense_disjointComponentLocus C) i⟩
  let ηV : V.toScheme := ⟨ηU, componentGenericPoint_mem_componentOpenAux C i⟩
  have hηV : IsGenericPoint ηV Set.univ := componentOpenAux_genericPoint_isGeneric C i
  let : IrreducibleSpace V.toScheme := componentOpenAux_irreducibleSpace C i
  let e : V.toScheme ⟶ C.X := V.ι ≫ U.ι
  let Ci := componentGenericPointContext C i ηV hηV
  have hη : e ηV = C.genericPoint i := rfl
  intro f
  let : IrreducibleSpace Ci.X := componentOpenAux_irreducibleSpace C i
  let j : Fin 1 := 0
  let gi : Ci.RationalMapsOver := ⟨f.1, f.2⟩
  let gp := Ci.genericPointMapForRationalMaps
  let data := gp.toFun gi j
  let ζ : V.toScheme := Ci.genericPoint j
  have hζ : e ζ = C.genericPoint i := by
    dsimp [ζ, Ci]
    rfl
  have hmaps : C.toBaseTarget data.point = C.toBaseSource (C.genericPoint i) :=
    data.mapsTo.trans (congrArg C.toBaseSource hζ)
  let : IsOpenImmersion e := by
    dsimp [e]
    infer_instance
  let eStalkIso := asIso (e.stalkMap ζ)
  let stalkTransport := eqToHom
    (congrArg (fun x => C.X.presheaf.stalk x) hζ)
  have hcancel : e.stalkMap ζ ≫ eStalkIso.inv = 𝟙 _ := eStalkIso.hom_inv_id
  have hcancel2 :
      (C.toBaseSource.stalkMap (e ζ) ≫ e.stalkMap ζ) ≫
        eStalkIso.inv = C.toBaseSource.stalkMap (e ζ) := by
    simp only [Category.assoc, hcancel, Category.comp_id]
  have hcancel3 : e.stalkMap ζ ≫ (eStalkIso.inv ≫ stalkTransport) =
      stalkTransport := by
    rw [← Category.assoc, hcancel, Category.id_comp]
  have hbridge :
      Ci.toBaseSource.stalkMap ζ ≫ eStalkIso.inv ≫ stalkTransport =
        eqToHom (congrArg (fun x => C.S.presheaf.stalk x)
          (congrArg C.toBaseSource hζ)) ≫
          C.toBaseSource.stalkMap (C.genericPoint i) := by
    change (e ≫ C.toBaseSource).stalkMap ζ ≫
        eStalkIso.inv ≫ stalkTransport = _
    calc
      _ = (C.toBaseSource.stalkMap (e ζ) ≫ e.stalkMap ζ) ≫
          eStalkIso.inv ≫ stalkTransport := by
            rw [Scheme.Hom.stalkMap_comp (f := e) (g := C.toBaseSource)]
            rfl
      _ = C.toBaseSource.stalkMap (e ζ) ≫ stalkTransport := by
            simp only [Category.assoc, hcancel3]
      _ = _ := stalkMap_eqToHom_naturality C.toBaseSource hζ
  refine {
    point := data.point
    mapsTo := hmaps
    stalkMap := data.stalkMap ≫ eStalkIso.inv ≫ stalkTransport
    isLocalHom := by
      have hdata : IsLocalHom (CommRingCat.Hom.hom data.stalkMap) := data.isLocalHom
      have hIso : IsLocalHom eStalkIso.inv.hom := isLocalHom_of_isIso _
      have hTransport : IsLocalHom stalkTransport.hom := isLocalHom_of_isIso _
      have hinner : IsLocalHom (eStalkIso.inv.hom.comp data.stalkMap.hom) :=
        @RingHom.isLocalHom_comp _ _ _ _ _ _ eStalkIso.inv.hom
          data.stalkMap.hom hIso hdata
      exact @RingHom.isLocalHom_comp _ _ _ _ _ _ stalkTransport.hom
        (eStalkIso.inv.hom.comp data.stalkMap.hom) hTransport hinner
    commutes := by
      have h := congrArg (fun q => q ≫ eStalkIso.inv ≫ stalkTransport) data.commutes
      change
        (C.toBaseTarget.stalkMap data.point ≫ data.stalkMap) ≫
            eStalkIso.inv ≫ stalkTransport =
          eqToHom (congrArg (fun x => C.S.presheaf.stalk x) data.mapsTo) ≫
            (Ci.toBaseSource.stalkMap ζ ≫ eStalkIso.inv ≫ stalkTransport) at h
      rw [hbridge] at h
      have hcast :
          eqToHom (congrArg (fun x => C.S.presheaf.stalk x) data.mapsTo) ≫
              eqToHom (congrArg (fun x => C.S.presheaf.stalk x)
                (congrArg C.toBaseSource hζ)) =
            eqToHom (congrArg (fun x => C.S.presheaf.stalk x) hmaps) := by
        rw [eqToHom_trans]
      have htail :
          eqToHom (congrArg (fun x => C.S.presheaf.stalk x) data.mapsTo) ≫
              eqToHom (congrArg (fun x => C.S.presheaf.stalk x)
                (congrArg C.toBaseSource hζ)) ≫
              C.toBaseSource.stalkMap (C.genericPoint i) =
            eqToHom (congrArg (fun x => C.S.presheaf.stalk x) hmaps) ≫
              C.toBaseSource.stalkMap (C.genericPoint i) := by
        calc
          _ = (eqToHom (congrArg (fun x => C.S.presheaf.stalk x) data.mapsTo) ≫
              eqToHom (congrArg (fun x => C.S.presheaf.stalk x)
                (congrArg C.toBaseSource hζ))) ≫
              C.toBaseSource.stalkMap (C.genericPoint i) := by
                simp only [Category.assoc]
          _ = _ := congrArg (fun q => q ≫ C.toBaseSource.stalkMap
            (C.genericPoint i)) hcast
      exact h.trans htail }

private lemma componentGenericPointMapAux_point
    (i : Fin C.numberOfComponents)
    (f : ComponentRationalMapsOver C (disjointComponentLocus C)
      (componentOpenAux C i))
    (g : (componentOpenAux C i).toScheme.PartialMap C.Y)
    (represents : g.toRationalMap = f.1)
    (over : g.hom ≫ C.toBaseTarget =
      g.domain.ι ≫ (componentOpenAux C i).ι ≫
        (disjointComponentLocus C).ι ≫ C.toBaseSource)
    (x : g.domain) (hx : x.1.1.1 = C.genericPoint i) :
    (componentGenericPointMapAux C i f).point = g.hom x := by
  classical
  let U := disjointComponentLocus C
  let V := componentOpenAux C i
  let ηU : U.toScheme := ⟨C.genericPoint i,
    genericPoint_mem_dense_open C U (dense_disjointComponentLocus C) i⟩
  let ηV : V.toScheme := ⟨ηU, componentGenericPoint_mem_componentOpenAux C i⟩
  have hηV : IsGenericPoint ηV Set.univ := componentOpenAux_genericPoint_isGeneric C i
  let : IrreducibleSpace V.toScheme := componentOpenAux_irreducibleSpace C i
  let e : V.toScheme ⟶ C.X := V.ι ≫ U.ι
  let Ci := componentGenericPointContext C i ηV hηV
  let j : Fin 1 := 0
  let gi : Ci.RationalMapsOver := ⟨f.1, f.2⟩
  let gp := Ci.genericPointMapForRationalMaps
  let data := gp.toFun gi j
  have hmem : ηV ∈ g.domain :=
    componentOpenAux_genericPoint_mem C i g.domain g.dense_domain
  let xη : g.domain := ⟨ηV, hmem⟩
  have hover : g.hom ≫ Ci.toBaseTarget = g.domain.ι ≫ Ci.toBaseSource := by
    simpa [Ci, e, V, U] using over
  have hmap := gp.map_point gi g represents hover
    (fun k ↦ by fin_cases k; exact hmem) j
  have hxeq : x = xη := Subtype.ext (Subtype.ext (Subtype.ext hx))
  show data.point = g.hom x
  calc
    data.point = g.hom xη := by simpa [data, gp, gi, j] using hmap
    _ = g.hom x := congrArg g.hom hxeq.symm

private lemma componentGenericPointMapAux_stalk
    (i : Fin C.numberOfComponents)
    (f : ComponentRationalMapsOver C (disjointComponentLocus C)
      (componentOpenAux C i))
    (g : (componentOpenAux C i).toScheme.PartialMap C.Y)
    (represents : g.toRationalMap = f.1)
    (over : g.hom ≫ C.toBaseTarget =
      g.domain.ι ≫ (componentOpenAux C i).ι ≫
        (disjointComponentLocus C).ι ≫ C.toBaseSource)
    (x : g.domain) (hx : x.1.1.1 = C.genericPoint i) :
    HEq (componentGenericPointMapAux C i f).stalkMap
      (g.hom.stalkMap x ≫ (g.domain.stalkIso x).hom ≫
        ((componentOpenAux C i).stalkIso x.1).hom ≫
        ((disjointComponentLocus C).stalkIso x.1.1).hom) := by
  classical
  let U := disjointComponentLocus C
  let V := componentOpenAux C i
  let ηU : U.toScheme := ⟨C.genericPoint i,
    genericPoint_mem_dense_open C U (dense_disjointComponentLocus C) i⟩
  let ηV : V.toScheme := ⟨ηU, componentGenericPoint_mem_componentOpenAux C i⟩
  have hηV : IsGenericPoint ηV Set.univ := componentOpenAux_genericPoint_isGeneric C i
  let : IrreducibleSpace V.toScheme := componentOpenAux_irreducibleSpace C i
  let e : V.toScheme ⟶ C.X := V.ι ≫ U.ι
  let Ci := componentGenericPointContext C i ηV hηV
  let j : Fin 1 := 0
  let gi : Ci.RationalMapsOver := ⟨f.1, f.2⟩
  let gp := Ci.genericPointMapForRationalMaps
  let data := gp.toFun gi j
  let ζ : V.toScheme := Ci.genericPoint j
  have hζ : e ζ = C.genericPoint i := by
    dsimp [ζ, Ci]
    rfl
  let : IsOpenImmersion e := by
    dsimp [e]
    infer_instance
  let eStalkIso := asIso (e.stalkMap ζ)
  let stalkTransport := eqToHom
    (congrArg (fun z => C.X.presheaf.stalk z) hζ)
  have hover : g.hom ≫ Ci.toBaseTarget = g.domain.ι ≫ Ci.toBaseSource := by
    simpa [Ci, e, V, U] using over
  let : Nonempty V.toScheme := ⟨ζ⟩
  have hmem : ζ ∈ g.domain := componentOpenAux_genericPoint_mem C i g.domain g.dense_domain
  have hmap := gp.map_stalk gi g represents hover
    (fun k ↦ by fin_cases k; exact hmem) j
  let xη : g.domain := ⟨ζ, hmem⟩
  have hpoint := gp.map_point gi g represents hover
    (fun k ↦ by fin_cases k; exact hmem) j
  have hpoint' : data.point = g.hom xη := by
    simpa [data, gp, gi, j, xη] using hpoint
  have hxeq : x = xη := Subtype.ext (Subtype.ext (Subtype.ext hx))
  subst x
  have hstalk : HEq (eStalkIso.inv ≫ stalkTransport)
      ((V.stalkIso ζ).hom ≫ (U.stalkIso ζ.1).hom) := by
    apply heq_of_eq
    cases hζ
    dsimp [stalkTransport]
    apply (cancel_mono (e.stalkMap ζ)).mp
    calc
      eStalkIso.inv ≫ e.stalkMap ζ = 𝟙 _ := eStalkIso.inv_hom_id
      _ = (V.stalkIso ζ).hom ≫ (U.stalkIso ζ.1).hom ≫ e.stalkMap ζ := by
        rw [Scheme.Hom.stalkMap_comp]
        rw [← Scheme.Opens.stalkIso_inv U (V.ι ζ)]
        rw [← Scheme.Opens.stalkIso_inv V ζ]
        have hUpt : ζ.1 = V.ι ζ := rfl
        have hUhom : HEq (U.stalkIso ζ.1).hom
            (U.stalkIso (V.ι ζ)).hom :=
          heq_apply_of_eq (fun z ↦ (U.stalkIso z).hom) hUpt
        have hUcomp := CategoryTheory.heq_comp
          (f := (U.stalkIso ζ.1).hom)
          (g := (U.stalkIso (V.ι ζ)).inv)
          (f' := (U.stalkIso (V.ι ζ)).hom)
          (g' := (U.stalkIso (V.ι ζ)).inv)
          (congrArg U.toScheme.presheaf.stalk hUpt)
          (congrArg C.X.presheaf.stalk (congrArg U.ι hUpt)) rfl hUhom HEq.rfl
        have hUcomp' : HEq
            ((U.stalkIso ζ.1).hom ≫ (U.stalkIso (V.ι ζ)).inv)
            (𝟙 (U.toScheme.presheaf.stalk (V.ι ζ))) := by
          simpa only [Iso.hom_inv_id] using hUcomp
        have hVcomp := CategoryTheory.heq_comp
          (f := (V.stalkIso ζ).hom)
          (g := (U.stalkIso ζ.1).hom ≫ (U.stalkIso (V.ι ζ)).inv)
          (f' := (V.stalkIso ζ).hom)
          (g' := 𝟙 (U.toScheme.presheaf.stalk (V.ι ζ))) rfl
          (congrArg U.toScheme.presheaf.stalk hUpt) rfl HEq.rfl hUcomp'
        have hVcomp' := CategoryTheory.heq_comp
          (f := (V.stalkIso ζ).hom ≫
            ((U.stalkIso ζ.1).hom ≫ (U.stalkIso (V.ι ζ)).inv))
          (g := (V.stalkIso ζ).inv)
          (f' := (V.stalkIso ζ).hom)
          (g' := (V.stalkIso ζ).inv) rfl rfl rfl hVcomp HEq.rfl
        have hRHS :
            ((V.stalkIso ζ).hom ≫
              ((U.stalkIso ζ.1).hom ≫ (U.stalkIso (V.ι ζ)).inv)) ≫
                (V.stalkIso ζ).inv = 𝟙 _ :=
          eq_of_heq (by
            simpa only [Category.id_comp, Iso.hom_inv_id] using hVcomp')
        calc
          𝟙 _ = ((V.stalkIso ζ).hom ≫
              ((U.stalkIso ζ.1).hom ≫ (U.stalkIso (V.ι ζ)).inv)) ≫
                (V.stalkIso ζ).inv := hRHS.symm
          _ = (V.stalkIso ζ).hom ≫ (U.stalkIso ζ.1).hom ≫
              (U.stalkIso (V.ι ζ)).inv ≫ (V.stalkIso ζ).inv := by
            let a := (V.stalkIso ζ).hom
            let b := (U.stalkIso ζ.1).hom
            let c := (U.stalkIso (V.ι ζ)).inv
            let d := (V.stalkIso ζ).inv
            show ((a ≫ (b ≫ c)) ≫ d) = a ≫ (b ≫ (c ≫ d))
            exact (Category.assoc a (b ≫ c) d).trans
              (congrArg (fun q => a ≫ q) (Category.assoc b c d))
  have htotal := CategoryTheory.heq_comp
    (eq1 := congrArg C.Y.presheaf.stalk hpoint')
    (eq2 := rfl) (eq3 := rfl) hmap hstalk
  show HEq (data.stalkMap ≫ eStalkIso.inv ≫ stalkTransport)
    (g.hom.stalkMap xη ≫ (g.domain.stalkIso xη).hom ≫
      (V.stalkIso xη.1).hom ≫ (U.stalkIso xη.1.1).hom)
  exact htotal

/-- On the cover of `⨆ i, T i` by pairwise disjoint opens `T i`, any family of morphisms out of
the members agrees on the overlaps. -/
private lemma iSupOpenCover_compat_of_disjoint {X Y : Scheme.{u}} {ι : Type*}
    (T : ι → X.Opens) (hdisj : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (φ : ∀ i, (Scheme.Opens.iSupOpenCover T).X i ⟶ Y) (i j : ι) :
    Limits.pullback.fst ((Scheme.Opens.iSupOpenCover T).f i)
        ((Scheme.Opens.iSupOpenCover T).f j) ≫ φ i =
      Limits.pullback.snd ((Scheme.Opens.iSupOpenCover T).f i)
        ((Scheme.Opens.iSupOpenCover T).f j) ≫ φ j := by
  let cover : (⨆ i, T i).toScheme.OpenCover := Scheme.Opens.iSupOpenCover T
  by_cases hij : i = j
  · subst j
    have : Mono (cover.f i) := by
      show Mono (X.homOfLE (le_iSup T i))
      infer_instance
    have hfst : Limits.pullback.fst (cover.f i) (cover.f i) =
        Limits.pullback.snd (cover.f i) (cover.f i) :=
      (cancel_mono (cover.f i)).mp Limits.pullback.condition
    rw [hfst]
  · have hempty : IsEmpty ↑(Limits.pullback (cover.f i) (cover.f j)) := by
      apply Scheme.isEmpty_pullback
      rw [Set.disjoint_iff_forall_ne]
      intro x hx y hy hxy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, hb⟩ := hy
      have hab : a.1 = b.1 := by
        calc
          a.1 = (cover.f i a).1 := by
            show a.1 = (X.homOfLE (le_iSup T i) a).1
            exact (Scheme.homOfLE_apply _ _).symm
          _ = (cover.f j b).1 := congrArg Subtype.val (hxy.trans hb.symm)
          _ = b.1 := by
            show (X.homOfLE (le_iSup T j) b).1 = b.1
            exact Scheme.homOfLE_apply _ _
      exact (Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr
        (hdisj i j hij))) a.2 (hab ▸ b.2)
    exact IsInitial.hom_ext (isInitialOfIsEmpty (X := Limits.pullback _ _)) _ _

private noncomputable def assembleComponentPartialMaps
    (U : C.X.Opens) (hU : Dense (U : Set C.X))
    (V : Fin C.numberOfComponents → U.toScheme.Opens)
    (hVcarrier : ∀ i, (V i : Set U.toScheme) =
      {x : U.toScheme | x.1 ∈ (C.components i : Set C.X)})
    (hVdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (g : ∀ i, (V i).toScheme.PartialMap C.Y) :
    C.X.PartialMap C.Y := by
  classical
  let T (i : Fin C.numberOfComponents) : C.X.Opens := ((V i).ι ≫ U.ι) ''ᵁ (g i).domain
  exact ⟨⨆ i, T i,
    dense_of_generic_points_mem_open C _ (componentRepresentative_generic_mem C U hU V hVcarrier g),
    (Scheme.Opens.iSupOpenCover T).glueMorphisms
      (fun i ↦ (((V i).ι ≫ U.ι).isoImage (g i).domain).inv ≫ (g i).hom)
      (iSupOpenCover_compat_of_disjoint T
        (componentImage_pairwise_disjoint C U V hVdisj (fun i ↦ (g i).domain)) _)⟩

/-- Restricting the assembled partial map to the `i`-th piece recovers the `i`-th local map. -/
private lemma iSupOpenCover_f_assembleComponentPartialMaps
    (U : C.X.Opens) (hU : Dense (U : Set C.X))
    (V : Fin C.numberOfComponents → U.toScheme.Opens)
    (hVcarrier : ∀ i, (V i : Set U.toScheme) =
      {x : U.toScheme | x.1 ∈ (C.components i : Set C.X)})
    (hVdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (g : ∀ i, (V i).toScheme.PartialMap C.Y) (i : Fin C.numberOfComponents) :
    (Scheme.Opens.iSupOpenCover fun j ↦ ((V j).ι ≫ U.ι) ''ᵁ (g j).domain).f i ≫
        (assembleComponentPartialMaps C U hU V hVcarrier hVdisj g).hom =
      (((V i).ι ≫ U.ι).isoImage (g i).domain).inv ≫ (g i).hom := by
  unfold assembleComponentPartialMaps
  dsimp only
  exact (Scheme.Opens.iSupOpenCover fun j ↦ ((V j).ι ≫ U.ι) ''ᵁ (g j).domain).ι_glueMorphisms
    (fun i ↦ (((V i).ι ≫ U.ι).isoImage (g i).domain).inv ≫ (g i).hom)
    (iSupOpenCover_compat_of_disjoint _
      (componentImage_pairwise_disjoint C U V hVdisj fun j ↦ (g j).domain) _) i

private lemma assembleComponentPartialMaps_local_equiv
    (g : ∀ i : Fin C.numberOfComponents,
      (componentOpenAux C i).toScheme.PartialMap C.Y)
    (i : Fin C.numberOfComponents)
    (hη : C.genericPoint i ∈ (assembleComponentPartialMaps C (disjointComponentLocus C)
        (dense_disjointComponentLocus C) (componentOpenAux C)
        (fun j ↦ componentOpenAux_carrier C j)
        (fun j k hjk ↦ pairwise_disjoint_componentOpenAux C j k hjk) g).domain) :
    (pullbackComponentPartialMap C i
      (assembleComponentPartialMaps C (disjointComponentLocus C)
        (dense_disjointComponentLocus C) (componentOpenAux C)
        (fun j ↦ componentOpenAux_carrier C j)
        (fun j k hjk ↦ pairwise_disjoint_componentOpenAux C j k hjk) g)
      (componentOpenAux_preimage_dense C i _ hη)).equiv
      (g i) := by
  classical
  let U := disjointComponentLocus C
  let V := componentOpenAux C
  let e (j : Fin C.numberOfComponents) : (V j).toScheme ⟶ C.X :=
    (V j).ι ≫ U.ι
  let T (j : Fin C.numberOfComponents) : C.X.Opens := e j ''ᵁ (g j).domain
  let p := assembleComponentPartialMaps C U (dense_disjointComponentLocus C) V
    (fun j ↦ componentOpenAux_carrier C j)
    (fun j k hjk ↦ pairwise_disjoint_componentOpenAux C j k hjk) g
  let D : C.X.Opens := p.domain
  let cover : D.toScheme.OpenCover := Scheme.Opens.iSupOpenCover T
  let q := pullbackComponentPartialMap C i p (componentOpenAux_preimage_dense C i p.domain hη)
  have hle : (g i).domain ≤ q.domain := fun x hx ↦ (le_iSup T i : T i ≤ D) ⟨x, hx, rfl⟩
  refine ⟨(g i).domain, (g i).dense_domain, hle, le_rfl, ?_⟩
  have hglue : cover.f i ≫ p.hom = ((e i).isoImage (g i).domain).inv ≫ (g i).hom :=
    iSupOpenCover_f_assembleComponentPartialMaps C U (dense_disjointComponentLocus C) V
      (fun j ↦ componentOpenAux_carrier C j)
      (fun j k hjk ↦ pairwise_disjoint_componentOpenAux C j k hjk) g i
  have hdomain : (g i).domain ≤ (e i) ⁻¹ᵁ D := hle
  have hqD : q.domain ≤ (e i) ⁻¹ᵁ D := by
    show (e i) ⁻¹ᵁ D ≤ (e i) ⁻¹ᵁ D
    exact le_rfl
  let a : (g i).domain.toScheme ⟶ D.toScheme :=
    (e i).resLE D (g i).domain hdomain
  let b : (g i).domain.toScheme ⟶ D.toScheme :=
    ((e i).isoImage (g i).domain).hom ≫ cover.f i
  have hcover : cover.f i ≫ D.ι = (T i).ι := by
    show C.X.homOfLE (le_iSup T i) ≫ D.ι = (T i).ι
    exact C.X.homOfLE_ι (le_iSup T i)
  have hfactor : a = b := by
    apply (cancel_mono D.ι).mp
    calc
      _ = (g i).domain.ι ≫ e i := by
        dsimp [a]
        exact Scheme.Hom.resLE_comp_ι (e i) hdomain
      _ = ((e i).isoImage (g i).domain).hom ≫ (T i).ι := by
        symm
        exact Scheme.Hom.isoImage_hom_ι (e i) (g i).domain
      _ = ((e i).isoImage (g i).domain).hom ≫ cover.f i ≫ D.ι := by
        rw [← hcover]
        rfl
  have hrestrict :
      (V i).toScheme.homOfLE hle ≫
          (e i).resLE D q.domain hqD = a := by
    apply (cancel_mono D.ι).mp
    dsimp [a]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    show ((V i).toScheme.homOfLE hle ≫ q.domain.ι) ≫ e i =
      (g i).domain.ι ≫ e i
    exact congrArg (fun f ↦ f ≫ e i) ((V i).toScheme.homOfLE_ι hle)
  show ((V i).toScheme.homOfLE hle ≫ q.hom) =
    ((V i).toScheme.homOfLE le_rfl ≫ (g i).hom)
  have hqhom : q.hom = (e i).resLE D q.domain hqD ≫ p.hom := rfl
  rw [hqhom, ← Category.assoc, hrestrict, hfactor]
  calc
    b ≫ p.hom = ((e i).isoImage (g i).domain).hom ≫
        (cover.f i ≫ p.hom) := by
      dsimp [b]
      exact Category.assoc _ _ _
    _ = ((e i).isoImage (g i).domain).hom ≫
        (((e i).isoImage (g i).domain).inv ≫ (g i).hom) :=
      congrArg _ hglue
    _ = (V i).toScheme.homOfLE le_rfl ≫ (g i).hom := by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      simp only [Scheme.homOfLE_rfl, Category.id_comp]

private noncomputable def chooseComponentRepresentative
    (U : C.X.Opens) (V : Fin C.numberOfComponents → U.toScheme.Opens)
    (i : Fin C.numberOfComponents)
    (f : ComponentRationalMapsOver C U (V i)) :
    {g : (V i).toScheme.PartialMap C.Y //
      g.hom ≫ C.toBaseTarget =
        g.domain.ι ≫ (V i).ι ≫ U.ι ≫ C.toBaseSource ∧
      g.toRationalMap = f.1} := by
  let : (V i).toScheme.Over C.S :=
    ⟨(V i).ι ≫ U.ι ≫ C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  have : f.1.IsOver C.S := (Scheme.RationalMap.isOver_iff).mpr f.2
  let hrep : ∃ g : (V i).toScheme.PartialMap C.Y,
      g.IsOver C.S ∧ g.toRationalMap = f.1 :=
    f.1.exists_partialMap_over C.S
  let g := Classical.choose hrep
  have hspec := Classical.choose_spec hrep
  exact ⟨g, ⟨(Scheme.PartialMap.isOver_iff).mp hspec.1, hspec.2⟩⟩

private noncomputable def assembleComponentRationalMaps
    (U : C.X.Opens) (hU : Dense (U : Set C.X))
    (V : Fin C.numberOfComponents → U.toScheme.Opens)
    (hVcarrier : ∀ i, (V i : Set U.toScheme) =
      {x : U.toScheme | x.1 ∈ (C.components i : Set C.X)})
    (hVdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (f : ∀ i, ComponentRationalMapsOver C U (V i)) :
    C.RationalMapsOver := by
  classical
  let rep (i : Fin C.numberOfComponents) := chooseComponentRepresentative C U V i (f i)
  let g (i : Fin C.numberOfComponents) := (rep i).1
  let p := assembleComponentPartialMaps C U hU V hVcarrier hVdisj g
  let e (i : Fin C.numberOfComponents) : (V i).toScheme ⟶ C.X :=
    (V i).ι ≫ U.ι
  let T (i : Fin C.numberOfComponents) : C.X.Opens := e i ''ᵁ (g i).domain
  let D : C.X.Opens := p.domain
  let cover : D.toScheme.OpenCover := Scheme.Opens.iSupOpenCover T
  have hp : p.hom ≫ C.toBaseTarget = p.domain.ι ≫ C.toBaseSource := by
    apply cover.hom_ext
    intro i₀
    let i : Fin C.numberOfComponents := i₀
    have hrestriction : cover.f i₀ ≫ p.hom = ((e i).isoImage (g i).domain).inv ≫ (g i).hom :=
      iSupOpenCover_f_assembleComponentPartialMaps C U hU V hVcarrier hVdisj g i
    change cover.f i₀ ≫ p.hom ≫ C.toBaseTarget = cover.f i₀ ≫ D.ι ≫ C.toBaseSource
    rw [reassoc_of% hrestriction]
    change (((e i).isoImage (g i).domain).inv ≫ (g i).hom) ≫ C.toBaseTarget =
      cover.f i ≫ D.ι ≫ C.toBaseSource
    have h₁ : ((e i).isoImage (g i).domain).inv ≫ (g i).hom ≫ C.toBaseTarget =
        (T i).ι ≫ C.toBaseSource := by
      calc
      _ = ((e i).isoImage (g i).domain).inv ≫
          ((g i).hom ≫ C.toBaseTarget) := rfl
      _ = ((e i).isoImage (g i).domain).inv ≫
          ((g i).domain.ι ≫ e i ≫ C.toBaseSource) :=
            congrArg (fun q => ((e i).isoImage (g i).domain).inv ≫ q) (rep i).2.1
      _ = ((e i).isoImage (g i).domain).inv ≫
          (g i).domain.ι ≫ e i ≫ C.toBaseSource := by simp only
      _ = (T i).ι ≫ C.toBaseSource := by
          have himage :
              ((e i).isoImage (g i).domain).inv ≫ (g i).domain.ι ≫ e i = (T i).ι := by
            simp [T]
          exact congrArg (fun q => q ≫ C.toBaseSource) himage
    have h₂ : (T i).ι ≫ C.toBaseSource =
        cover.f i₀ ≫ D.ι ≫ C.toBaseSource := by
      have hcover : (T i).ι = cover.f i₀ ≫ D.ι := by
        change (T i).ι = C.X.homOfLE (le_iSup T i) ≫ D.ι
        exact (C.X.homOfLE_ι (le_iSup T i)).symm
      rw [hcover]
      exact Category.assoc _ _ _
    exact h₁.trans h₂
  let : C.X.Over C.S := ⟨C.toBaseSource⟩
  let : C.Y.Over C.S := ⟨C.toBaseTarget⟩
  have : p.IsOver C.S := (Scheme.PartialMap.isOver_iff).mpr hp
  exact ⟨p.toRationalMap, (Scheme.RationalMap.isOver_iff).mp inferInstance⟩

private lemma assembleComponentPullbacks_equiv
    (g : C.X.PartialMap C.Y)
    (hη : ∀ i, C.genericPoint i ∈ g.domain) :
    (assembleComponentPartialMaps C (disjointComponentLocus C)
      (dense_disjointComponentLocus C) (componentOpenAux C)
      (fun i ↦ componentOpenAux_carrier C i)
      (fun i j hij ↦ pairwise_disjoint_componentOpenAux C i j hij)
      (fun i ↦ pullbackComponentPartialMap C i g
        (componentOpenAux_preimage_dense C i g.domain (hη i)))).equiv g := by
  classical
  let V := componentOpenAux C
  let e (i : Fin C.numberOfComponents) : (V i).toScheme ⟶ C.X :=
    (V i).ι ≫ (disjointComponentLocus C).ι
  let q (i : Fin C.numberOfComponents) :=
    pullbackComponentPartialMap C i g (componentOpenAux_preimage_dense C i g.domain (hη i))
  let T (i : Fin C.numberOfComponents) : C.X.Opens := e i ''ᵁ (q i).domain
  let p := assembleComponentPartialMaps C (disjointComponentLocus C)
    (dense_disjointComponentLocus C) V (fun j ↦ componentOpenAux_carrier C j)
    (fun i j hij ↦ pairwise_disjoint_componentOpenAux C i j hij) q
  let D : C.X.Opens := p.domain
  let cover : D.toScheme.OpenCover := Scheme.Opens.iSupOpenCover T
  show p.equiv g
  have hTg (i : Fin C.numberOfComponents) : T i ≤ g.domain := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    show ((componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι) y ∈ g.domain
    change y ∈ ((componentOpenAux C i).ι ≫ (disjointComponentLocus C).ι) ⁻¹ᵁ
      g.domain at hy
    exact hy
  have hTD (i : Fin C.numberOfComponents) : T i ≤ D := le_iSup T i
  have hDg : D ≤ g.domain := by
    apply iSup_le
    exact hTg
  refine ⟨D, p.dense_domain, le_rfl, hDg, ?_⟩
  have hDmap (i : Fin C.numberOfComponents) :
      C.X.homOfLE (hTD i) ≫ p.hom = ((e i).isoImage (q i).domain).inv ≫ (q i).hom :=
    iSupOpenCover_f_assembleComponentPartialMaps C (disjointComponentLocus C)
      (dense_disjointComponentLocus C) V (fun j ↦ componentOpenAux_carrier C j)
      (fun i j hij ↦ pairwise_disjoint_componentOpenAux C i j hij) q i
  have hqdom (i : Fin C.numberOfComponents) :
      (q i).domain ≤ (e i) ⁻¹ᵁ g.domain := by
    show (pullbackComponentPartialMap C i g
      (componentOpenAux_preimage_dense C i g.domain (hη i))).domain ≤ _
    rfl
  have hTfactor (i : Fin C.numberOfComponents) :
      C.X.homOfLE (hTD i) ≫ C.X.homOfLE hDg =
        ((e i).isoImage (q i).domain).inv ≫
          (e i).resLE g.domain (q i).domain (hqdom i) := by
    apply (cancel_mono g.domain.ι).mp
    calc
      _ = (T i).ι := by
        simp [Scheme.homOfLE_ι]
      _ = ((e i).isoImage (q i).domain).inv ≫ (q i).domain.ι ≫ e i := by
        rw [← Scheme.Hom.isoImage_inv_ι]
      _ = ((e i).isoImage (q i).domain).inv ≫
          (e i).resLE g.domain (q i).domain (hqdom i) ≫
            g.domain.ι := by
        rw [← Scheme.Hom.resLE_comp_ι (e i) (hqdom i)]
  have hqhom (i : Fin C.numberOfComponents) :
      (q i).hom = (e i).resLE g.domain (q i).domain (hqdom i) ≫ g.hom := by
    rfl
  have hloc (i : Fin C.numberOfComponents) :
      C.X.homOfLE (hTD i) ≫ p.hom =
        C.X.homOfLE (hTD i) ≫ C.X.homOfLE hDg ≫ g.hom := by
    rw [hDmap i, hqhom i]
    rw [← Category.assoc, ← hTfactor i]
    exact Category.assoc _ _ _
  show C.X.homOfLE le_rfl ≫ p.hom = C.X.homOfLE hDg ≫ g.hom
  simp only [Scheme.homOfLE_rfl, Category.id_comp]
  apply cover.hom_ext
  intro i
  exact hloc i

private lemma partialMaps_equiv_of_component_pullbacks_equiv
    (f g : C.X.PartialMap C.Y)
    (hfη : ∀ i, C.genericPoint i ∈ f.domain)
    (hgη : ∀ i, C.genericPoint i ∈ g.domain)
    (hfg : ∀ i,
      (pullbackComponentPartialMap C i f
        (componentOpenAux_preimage_dense C i f.domain (hfη i))).equiv
      (pullbackComponentPartialMap C i g
        (componentOpenAux_preimage_dense C i g.domain (hgη i)))) :
    f.equiv g := by
  classical
  let U := disjointComponentLocus C
  let V := componentOpenAux C
  let e (i : Fin C.numberOfComponents) : (V i).toScheme ⟶ C.X :=
    (V i).ι ≫ U.ι
  let Wi (i : Fin C.numberOfComponents) : (V i).toScheme.Opens :=
    Classical.choose (hfg i)
  have hspec (i : Fin C.numberOfComponents) := Classical.choose_spec (hfg i)
  have hWi (i : Fin C.numberOfComponents) : Dense (Wi i : Set (V i).toScheme) :=
    (hspec i).1
  have hWif (i : Fin C.numberOfComponents) :
      Wi i ≤ (pullbackComponentPartialMap C i f
        (componentOpenAux_preimage_dense C i f.domain (hfη i))).domain :=
    (hspec i).2.1
  have hWig (i : Fin C.numberOfComponents) :
      Wi i ≤ (pullbackComponentPartialMap C i g
        (componentOpenAux_preimage_dense C i g.domain (hgη i))).domain :=
    (hspec i).2.2.1
  have hmap (i : Fin C.numberOfComponents) :
      ((pullbackComponentPartialMap C i f
        (componentOpenAux_preimage_dense C i f.domain (hfη i))).restrict
          (Wi i) (hWi i) (hWif i)).hom =
      ((pullbackComponentPartialMap C i g
        (componentOpenAux_preimage_dense C i g.domain (hgη i))).restrict
          (Wi i) (hWi i) (hWig i)).hom :=
    (hspec i).2.2.2
  let T (i : Fin C.numberOfComponents) : C.X.Opens := e i ''ᵁ Wi i
  have hTf (i : Fin C.numberOfComponents) : T i ≤ f.domain := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    show y ∈ (e i) ⁻¹ᵁ f.domain
    exact hWif i hy
  have hTg (i : Fin C.numberOfComponents) : T i ≤ g.domain := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    show y ∈ (e i) ⁻¹ᵁ g.domain
    exact hWig i hy
  have hTη (i : Fin C.numberOfComponents) : C.genericPoint i ∈ T i := by
    let ηU : U.toScheme := ⟨C.genericPoint i,
      genericPoint_mem_dense_open C U (dense_disjointComponentLocus C) i⟩
    have hηV : ηU ∈ (V i : Set U.toScheme) := by
      rw [componentOpenAux_carrier C i]
      exact genericPoint_mem_component C i
    let : Nonempty (V i).toScheme := ⟨⟨ηU, hηV⟩⟩
    obtain ⟨x, hx⟩ := (hWi i).nonempty
    have hxcomp : e i x ∈ (C.components i : Set C.X) :=
      (congrArg (fun s : Set U.toScheme => x.1 ∈ s) (componentOpenAux_carrier C i)).mp x.2
    exact (C.isGenericPoint i).mem_open_set_iff (T i).2 |>.2 ⟨e i x, hxcomp, x, hx, rfl⟩
  let D : C.X.Opens := ⨆ i, T i
  have hD : Dense (D : Set C.X) :=
    dense_of_generic_points_mem_open C D (fun i ↦ le_iSup T i (hTη i))
  have hDf : D ≤ f.domain := iSup_le hTf
  have hDg : D ≤ g.domain := iSup_le hTg
  have hlocal (i : Fin C.numberOfComponents) :
      C.X.homOfLE (hTf i) ≫ f.hom =
        C.X.homOfLE (hTg i) ≫ g.hom := by
    let qf := pullbackComponentPartialMap C i f
      (componentOpenAux_preimage_dense C i f.domain (hfη i))
    let qg := pullbackComponentPartialMap C i g
      (componentOpenAux_preimage_dense C i g.domain (hgη i))
    let α := (e i).isoImage (Wi i)
    have hqfPre : qf.domain ≤ (e i) ⁻¹ᵁ f.domain := by
      rfl
    have hqgPre : qg.domain ≤ (e i) ⁻¹ᵁ g.domain := by
      rfl
    have hqfHom : qf.hom = (e i).resLE f.domain qf.domain hqfPre ≫ f.hom := rfl
    have hqgHom : qg.hom = (e i).resLE g.domain qg.domain hqgPre ≫ g.hom := rfl
    have hfactor (P : C.X.PartialMap C.Y) (Q : (V i).toScheme.Opens)
        (hQ : Q ≤ (e i) ⁻¹ᵁ P.domain) (hW : Wi i ≤ Q) (hT : T i ≤ P.domain) :
        C.X.homOfLE hT =
          α.inv ≫ (V i).toScheme.homOfLE hW ≫ (e i).resLE P.domain Q hQ := by
      apply (cancel_mono P.domain.ι).mp
      calc
        _ = (T i).ι := Scheme.homOfLE_ι _ _
        _ = α.inv ≫ (Wi i).ι ≫ e i := (Scheme.Hom.isoImage_inv_ι (e i) (Wi i)).symm
        _ = α.inv ≫ (V i).toScheme.homOfLE hW ≫ Q.ι ≫ e i :=
          (congrArg (fun k ↦ α.inv ≫ k ≫ e i) ((V i).toScheme.homOfLE_ι hW)).symm
        _ = α.inv ≫ (V i).toScheme.homOfLE hW ≫ (e i).resLE P.domain Q hQ ≫ P.domain.ι :=
          congrArg (fun k ↦ α.inv ≫ (V i).toScheme.homOfLE hW ≫ k)
            (Scheme.Hom.resLE_comp_ι (e i) hQ).symm
    have hfactorF := hfactor f qf.domain hqfPre (hWif i) (hTf i)
    have hfactorG := hfactor g qg.domain hqgPre (hWig i) (hTg i)
    calc
      _ = α.inv ≫ ((V i).toScheme.homOfLE (hWif i) ≫ qf.hom) := by
        rw [hqfHom]
        simpa only [Category.assoc] using
          congrArg (fun k ↦ k ≫ f.hom) (hfactorF)
      _ = α.inv ≫ ((V i).toScheme.homOfLE (hWig i) ≫ qg.hom) :=
        congrArg (fun k ↦ α.inv ≫ k) (hmap i)
      _ = _ := by
        rw [hqgHom]
        simpa only [Category.assoc] using
          (congrArg (fun k ↦ k ≫ g.hom) (hfactorG)).symm
  let cover : D.toScheme.OpenCover := Scheme.Opens.iSupOpenCover T
  have hrestrict :
      (f.restrict D hD hDf).hom = (g.restrict D hD hDg).hom := by
    apply cover.hom_ext
    intro i
    show cover.f i ≫ C.X.homOfLE hDf ≫ f.hom =
      cover.f i ≫ C.X.homOfLE hDg ≫ g.hom
    simpa [cover, Scheme.Opens.iSupOpenCover] using hlocal i
  exact ⟨D, hD, hDf, hDg, hrestrict⟩

private theorem genericPointLocalMap_ext
    (i : Fin C.numberOfComponents)
    {a b : C.GenericPointLocalMap i}
    (hp : a.point = b.point) (hs : HEq a.stalkMap b.stalkMap) : a = b := by
  cases a with
  | mk ap am ast alocal acomm =>
    cases b with
    | mk bp bm bst blocal bcomm =>
      cases hp
      have hst : ast = bst := eq_of_heq hs
      subst bst
      rfl

/-- The construction of the reduction to the irreducible components. -/
private theorem irreducibleComponentReduction_package :
    Nonempty (IrreducibleComponentReduction C) := by
  classical
  let U := disjointComponentLocus C
  let V := componentOpenAux C
  let hU := dense_disjointComponentLocus C
  let hcarrier : ∀ i, (V i : Set U.toScheme) =
      {x : U.toScheme | x.1 ∈ (C.components i : Set C.X)} :=
    fun i ↦ componentOpenAux_carrier C i
  let hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j) :=
    fun i j hij ↦ pairwise_disjoint_componentOpenAux C i j hij
  refine ⟨{
    denseOpen := U
    dense_denseOpen := hU
    denseOpen_carrier := disjointComponentLocus_carrier C
    componentOpen := V
    componentOpen_carrier := hcarrier
    pairwise_disjoint_componentOpen := hdisj
    iSup_componentOpen := iSup_componentOpenAux_eq_top C
    restrictRationalMapsEquiv := ?_
    componentGenericPointMap := fun i ↦ componentGenericPointMapAux C i
    componentGenericPointMap_point := ?_
    componentGenericPointMap_stalk := ?_
    componentGenericPointMap_restrict := ?_ }⟩
  · refine {
      toFun := fun f i ↦ restrictRationalMapToComponent C i f
      invFun := assembleComponentRationalMaps C U hU V hcarrier hdisj
      left_inv := ?_
      right_inv := ?_ }
    · intro f
      apply Subtype.ext
      let fc : ∀ i : Fin C.numberOfComponents,
          ComponentRationalMapsOver C U (V i) :=
        fun i ↦ restrictRationalMapToComponent C i f
      let reps : ∀ i : Fin C.numberOfComponents,
          (V i).toScheme.PartialMap C.Y :=
        fun i ↦ (chooseComponentRepresentative C U V i (fc i)).1
      let p := assembleComponentPartialMaps C U hU V hcarrier hdisj reps
      let assembled := assembleComponentRationalMaps C U hU V hcarrier hdisj fc
      have hassembled : assembled.1 = p.toRationalMap := rfl
      let r := representativeOver C f
      have hrη : ∀ i, C.genericPoint i ∈ r.domain :=
        fun i ↦ genericPoint_mem_dense_open C r.domain r.dense_domain i
      have hpη : ∀ i, C.genericPoint i ∈ p.domain :=
        componentRepresentative_generic_mem C U hU V hcarrier reps
      have hcomponent : ∀ i,
          (pullbackComponentPartialMap C i p
            (componentOpenAux_preimage_dense C i p.domain (hpη i))).equiv
          (pullbackComponentPartialMap C i r
            (componentOpenAux_preimage_dense C i r.domain (hrη i))) := by
        intro i
        have hlocal := assembleComponentPartialMaps_local_equiv C reps i (hpη i)
        let q := pullbackComponentPartialMap C i r
          (componentOpenAux_preimage_dense C i r.domain (hrη i))
        have hrestrict : (fc i).1 = q.toRationalMap := rfl
        have hrep : (reps i).toRationalMap = q.toRationalMap :=
          ((chooseComponentRepresentative C U V i (fc i)).2.2).trans hrestrict
        exact hlocal.trans
          ((Scheme.PartialMap.toRationalMap_eq_iff).mp hrep)
      have hpeq : p.equiv r :=
        partialMaps_equiv_of_component_pullbacks_equiv C p r hpη hrη hcomponent
      show assembled.1 = f.1
      rw [hassembled]
      exact (Scheme.PartialMap.toRationalMap_eq_iff).mpr hpeq |>.trans
        (representativeOver_toRationalMap C f)
    · intro f
      funext i
      apply Subtype.ext
      let reps : ∀ j : Fin C.numberOfComponents,
          (componentOpenAux C j).toScheme.PartialMap C.Y :=
        fun j ↦ (chooseComponentRepresentative C U V j (f j)).1
      let p := assembleComponentPartialMaps C U hU V hcarrier hdisj reps
      let global := assembleComponentRationalMaps C U hU V hcarrier hdisj f
      have hglobal : global.1 = p.toRationalMap := rfl
      let r := representativeOver C global
      have hr : r.equiv p := by
        apply (Scheme.PartialMap.toRationalMap_eq_iff).mp
        rw [representativeOver_toRationalMap, hglobal]
      have hrη : C.genericPoint i ∈ r.domain :=
        genericPoint_mem_dense_open C r.domain r.dense_domain i
      have hpη : C.genericPoint i ∈ p.domain :=
        componentRepresentative_generic_mem C U hU V hcarrier reps i
      let q := pullbackComponentPartialMap C i r
        (componentOpenAux_preimage_dense C i r.domain hrη)
      have hq : q.equiv
          (pullbackComponentPartialMap C i p
            (componentOpenAux_preimage_dense C i p.domain hpη)) :=
        pullbackComponentPartialMap_equiv C i r p hrη hpη hr
      have hlocal := assembleComponentPartialMaps_local_equiv C reps i hpη
      have hcomp : q.equiv (reps i) := hq.trans hlocal
      have hrestrict :
          (restrictRationalMapToComponent C i global).1 = q.toRationalMap := rfl
      show (restrictRationalMapToComponent C i global).1 = (f i).1
      rw [hrestrict]
      exact (Scheme.PartialMap.toRationalMap_eq_iff).mpr hcomp |>.trans
        (chooseComponentRepresentative C U V i (f i)).2.2
  · exact componentGenericPointMapAux_point C
  · exact componentGenericPointMapAux_stalk C
  · intro f
    funext i
    let U := disjointComponentLocus C
    let V := componentOpenAux C i
    let e : V.toScheme ⟶ C.X := V.ι ≫ U.ι
    let ηU : U.toScheme := ⟨C.genericPoint i,
      genericPoint_mem_dense_open C U (dense_disjointComponentLocus C) i⟩
    let ηV : V.toScheme := ⟨ηU, componentGenericPoint_mem_componentOpenAux C i⟩
    let r := representativeOver C f
    have hηr : C.genericPoint i ∈ r.domain :=
      genericPoint_mem_dense_open C r.domain r.dense_domain i
    let q := pullbackComponentPartialMap C i r
      (componentOpenAux_preimage_dense C i r.domain hηr)
    have hqη : ηV ∈ q.domain := hηr
    have hqdomain : q.domain = e ⁻¹ᵁ r.domain := by
      dsimp [q, pullbackComponentPartialMap, e, U, V]
    have hpre : q.domain ≤ e ⁻¹ᵁ r.domain := by
      rw [hqdomain]
    let xq : q.domain.toScheme := ⟨ηV, hqη⟩
    let res : q.domain.toScheme ⟶ r.domain.toScheme :=
      e.resLE r.domain q.domain hpre
    let x0 : r.domain.toScheme := res xq
    let x0' : r.domain.toScheme := ⟨C.genericPoint i, hηr⟩
    let fi := restrictRationalMapToComponent C i f
    have hqrep : q.toRationalMap = fi.1 := rfl
    have hqover := pullbackComponentPartialMap_over C i r
      (componentOpenAux_preimage_dense C i r.domain hηr) (representativeOver_base C f)
    let A := componentGenericPointMapAux C i fi
    let B := C.genericPointMapForRationalMaps f i
    have hApoint : A.point = q.hom xq :=
      componentGenericPointMapAux_point C i fi q hqrep hqover xq (by rfl)
    have hAStalk₀ : HEq A.stalkMap
        (q.hom.stalkMap xq ≫ (q.domain.stalkIso xq).hom ≫
          (V.stalkIso xq.1).hom ≫ (U.stalkIso xq.1.1).hom) :=
      componentGenericPointMapAux_stalk C i fi q hqrep hqover xq (by rfl)
    have hUpt : xq.1.1 = V.ι xq.1 := rfl
    have hUhom : HEq (U.stalkIso xq.1.1).hom
        (U.stalkIso (V.ι xq.1)).hom :=
      heq_apply_of_eq (fun z ↦ (U.stalkIso z).hom) hUpt
    have hAStalk : HEq A.stalkMap
        (q.hom.stalkMap xq ≫ (q.domain.stalkIso xq).hom ≫
          (V.stalkIso xq.1).hom ≫ (U.stalkIso (V.ι xq.1)).hom) :=
      hAStalk₀.trans (CategoryTheory.heq_comp
        (f := q.hom.stalkMap xq ≫ (q.domain.stalkIso xq).hom ≫
          (V.stalkIso xq.1).hom)
        (g := (U.stalkIso xq.1.1).hom)
        (f' := q.hom.stalkMap xq ≫ (q.domain.stalkIso xq).hom ≫
          (V.stalkIso xq.1).hom)
        (g' := (U.stalkIso (V.ι xq.1)).hom)
        rfl (congrArg U.toScheme.presheaf.stalk hUpt)
        (congrArg C.X.presheaf.stalk (congrArg U.ι hUpt)) HEq.rfl hUhom)
    have hresPoint : x0.1 = e xq.1 := by
      show (res xq).1 = e xq.1
      rw [Scheme.Hom.coe_resLE_apply]
    let κ := C.X.presheaf.stalkCongr (.of_eq hresPoint)
    have hBpoint : B.point = r.hom x0' :=
      (C.genericPointMapForRationalMaps).map_point f r
        (representativeOver_toRationalMap C f)
        (representativeOver_base C f)
        (fun j ↦ genericPoint_mem_dense_open C r.domain r.dense_domain j) i
    have hqpoint : q.hom xq = r.hom x0 := rfl
    have hidx : x0 = x0' := by
      apply Subtype.ext
      show (res xq).1 = C.genericPoint i
      rw [Scheme.Hom.coe_resLE_apply]
      show (U.ι (V.ι ηV)) = _
      rfl
    have hpoint : A.point = B.point :=
      hApoint.trans
        (hqpoint.trans ((congrArg r.hom hidx).trans hBpoint.symm))
    have htarget : HEq
        (r.hom.stalkMap x0 ≫ (r.domain.stalkIso x0).hom ≫ κ.hom)
        (r.hom.stalkMap x0' ≫ (r.domain.stalkIso x0').hom) := by
      let m (z : r.domain.toScheme) :=
        r.hom.stalkMap z ≫ (r.domain.stalkIso z).hom
      have hκ : HEq (m x0 ≫ κ.hom) (m x0) := by
        dsimp [κ]
        rw [stalkCongr_hom_eqToHom] <;> try assumption
        exact (heq_of_eqToHom_right
          (X := C.X) (x := x0.1) (y := e xq.1)
          (f := m x0)
          (g := m x0 ≫ eqToHom (congrArg C.X.presheaf.stalk hresPoint))
          hresPoint (by simp)).symm
      have hm : HEq (m x0) (m x0') := heq_apply_of_eq m hidx
      exact hκ.trans hm
    have hBStalk : HEq B.stalkMap
        (r.hom.stalkMap x0' ≫ (r.domain.stalkIso x0').hom) :=
      (C.genericPointMapForRationalMaps).map_stalk f r
        (representativeOver_toRationalMap C f)
        (representativeOver_base C f)
        (fun j ↦ genericPoint_mem_dense_open C r.domain r.dense_domain j) i
    have hresSquare :
      (r.domain.stalkIso x0).hom ≫ κ.hom ≫ e.stalkMap xq.1 =
          res.stalkMap xq ≫ (q.domain.stalkIso xq).hom := by
      simpa [κ, Scheme.Hom.resLEStalkMap,
        TopCat.Presheaf.stalkCongr_hom] using
          (Scheme.Hom.resLEStalkMap e hpre xq).hom.w
    have heCancel :
        e.stalkMap xq.1 ≫ (V.stalkIso xq.1).hom ≫
          (U.stalkIso (V.ι xq.1)).hom = 𝟙 _ := by
      dsimp [e]
      rw [Scheme.Hom.stalkMap_comp]
      rw [← Scheme.Opens.stalkIso_inv U (V.ι xq.1)]
      rw [← Scheme.Opens.stalkIso_inv V xq.1]
      let I := V.stalkIso xq.1 ≪≫ U.stalkIso (V.ι xq.1)
      calc
        _ = ((U.stalkIso (V.ι xq.1)).inv ≫ (V.stalkIso xq.1).inv) ≫
              ((V.stalkIso xq.1).hom ≫ (U.stalkIso (V.ι xq.1)).hom) :=
          Category.assoc _ _ _
        _ = 𝟙 _ := I.inv_hom_id
    have heCancel' : e.stalkMap xq.1 ≫
        ((V.stalkIso xq.1).hom ≫ (U.stalkIso (V.ι xq.1)).hom) = 𝟙 _ := by
      simpa [Category.assoc] using heCancel
    have htransport :
        res.stalkMap xq ≫ (q.domain.stalkIso xq).hom ≫
          (V.stalkIso xq.1).hom ≫ (U.stalkIso (V.ι xq.1)).hom =
        (r.domain.stalkIso x0).hom ≫ κ.hom := by
      calc
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun k ↦ k ≫ (V.stalkIso xq.1).hom ≫
              (U.stalkIso (V.ι xq.1)).hom) hresSquare.symm
        _ = _ := by
          rw [heCancel']
          exact congrArg (fun k ↦ (r.domain.stalkIso x0).hom ≫ k)
            (Category.comp_id κ.hom)
    have hqStalk : q.hom.stalkMap xq =
        r.hom.stalkMap x0 ≫ res.stalkMap xq := by
      show (res ≫ r.hom).stalkMap xq = _
      simpa only [hqpoint] using Scheme.Hom.stalkMap_comp res r.hom xq
    cases hqpoint
    have hbridge0 : HEq
        (q.hom.stalkMap xq ≫ (q.domain.stalkIso xq).hom ≫
          (V.stalkIso xq.1).hom ≫ (U.stalkIso (V.ι xq.1)).hom)
        (r.hom.stalkMap x0 ≫ (r.domain.stalkIso x0).hom ≫ κ.hom) := by
      have h := congrArg (fun k ↦ r.hom.stalkMap x0 ≫ k) htransport
      rw [← Category.assoc, ← hqStalk] at h
      exact heq_of_eq h
    have hbridge : HEq
        (q.hom.stalkMap xq ≫ (q.domain.stalkIso xq).hom ≫
          (V.stalkIso xq.1).hom ≫ (U.stalkIso (V.ι xq.1)).hom)
        (r.hom.stalkMap x0' ≫ (r.domain.stalkIso x0').hom) :=
      hbridge0.trans htarget
    have hstalk : HEq A.stalkMap B.stalkMap :=
      hAStalk.trans (hbridge.trans hBStalk.symm)
    exact genericPointLocalMap_ext C i hpoint hstalk

/-- Deleting the pairwise intersections gives a dense open on which rational
maps and their generic-point data decompose over the irreducible components. -/
public alias nonempty_irreducibleComponentReduction := irreducibleComponentReduction_package

/-- The generic-point map is injective exactly when its domain is empty or all
of its component maps on the dense disjoint-component locus are injective. -/
public theorem injective_genericPointMap_iff_components
    (R : IrreducibleComponentReduction C) :
    Function.Injective C.genericPointMapForRationalMaps ↔
      IsEmpty C.RationalMapsOver ∨
        ∀ i, Function.Injective (R.componentGenericPointMap i) := by
  classical
  constructor
  · intro h
    rcases isEmpty_or_nonempty C.RationalMapsOver with hempty | hnonempty
    · exact Or.inl hempty
    · right
      let f := Classical.choice hnonempty
      have (i : Fin C.numberOfComponents) :
          Nonempty (ComponentRationalMapsOver C R.denseOpen (R.componentOpen i)) :=
        ⟨R.restrictRationalMapsEquiv f i⟩
      apply Pi.map_injective.mp
      intro a b hab
      apply R.restrictRationalMapsEquiv.symm.injective
      apply h
      rw [← R.componentGenericPointMap_restrict, ← R.componentGenericPointMap_restrict]
      funext i
      simpa only [Equiv.apply_symm_apply, Pi.map_apply] using congrFun hab i
  · rintro (hempty | h)
    · exact fun f ↦ (hempty.false f).elim
    · intro f g hfg
      apply R.restrictRationalMapsEquiv.injective
      funext i
      apply h i
      exact congrFun ((R.componentGenericPointMap_restrict f).trans
        (hfg.trans (R.componentGenericPointMap_restrict g).symm)) i

/-- The generic-point map is surjective exactly when its product of generic-point
data is empty or all component maps on the dense disjoint-component locus are
surjective. -/
public theorem surjective_genericPointMap_iff_components
    (R : IrreducibleComponentReduction C) :
    Function.Surjective C.genericPointMapForRationalMaps ↔
      IsEmpty (∀ i, C.GenericPointLocalMap i) ∨
        ∀ i, Function.Surjective (R.componentGenericPointMap i) := by
  classical
  constructor
  · intro h
    rcases isEmpty_or_nonempty (∀ i, C.GenericPointLocalMap i) with hempty | hnonempty
    · exact Or.inl hempty
    · right
      let y₀ := Classical.choice hnonempty
      intro i y
      obtain ⟨f, hf⟩ := h (Function.update y₀ i y)
      refine ⟨R.restrictRationalMapsEquiv f i, ?_⟩
      simpa using congrFun ((R.componentGenericPointMap_restrict f).trans hf) i
  · rintro (hempty | h)
    · exact fun y ↦ (hempty.false y).elim
    · intro y
      choose f hf using fun i ↦ h i (y i)
      refine ⟨R.restrictRationalMapsEquiv.symm f, ?_⟩
      rw [← R.componentGenericPointMap_restrict, Equiv.apply_symm_apply]
      exact funext hf

end GenericPointMapContext

end AlgebraicGeometry

end
