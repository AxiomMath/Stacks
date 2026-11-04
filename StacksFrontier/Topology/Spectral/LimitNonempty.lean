module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Cofiltered limits of nonempty spectral spaces are nonempty

Let `I` be a cofiltered category and `F : I ⥤ TopCat` a diagram of spectral spaces all of whose
transition maps are spectral. A compatible system of nonempty subsets `Z i ⊆ F.obj i`, each closed
in the constructible topology of `F.obj i`, has a point in its limit; in particular the limit of
`F` is nonempty when every `F.obj i` is.

## Main definitions

* `SpectralLimits.limitSet`: the set of compatible families in `∀ i, F.obj i`, the underlying set
  of the limit of `F`.
* `SpectralLimits.IsSpectralDiagram`: every object of the diagram is a spectral space and every
  transition map is a spectral map.
* `SpectralLimits.ConstructibleFamily`: the product of the constructible topologies of the
  `F.obj i`.

## Main results

* `SpectralLimits.nonempty_limitSet_inter_of_isClosed_constructible`: a compatible cofiltered
  system of nonempty constructibly closed subsets of a spectral diagram has nonempty limit.
* `SpectralLimits.nonempty_limitSet`: the cofiltered limit of a diagram of nonempty spectral
  spaces is nonempty.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace SpectralLimits

variable {I : Type u} [Category.{v} I]

/-- The set of compatible families in `∏ i, F.obj i`, i.e. the underlying set of `lim F`. -/
def limitSet (F : I ⥤ TopCat) : Set (∀ i, F.obj i) :=
  { x | ∀ ⦃j i : I⦄ (a : j ⟶ i), F.map a (x j) = x i }

/-- A *spectral diagram*: every object is a spectral space and every transition map is a spectral
map. -/
structure IsSpectralDiagram (F : I ⥤ TopCat) : Prop where
  /-- Every space in the diagram is spectral. -/
  spectral_obj : ∀ i, SpectralSpace (F.obj i)
  /-- Every transition map of the diagram is a spectral map. -/
  spectral_map : ∀ ⦃j i : I⦄ (a : j ⟶ i), IsSpectralMap (F.map a)

/-- The product of the constructible topologies of a diagram of spaces: a family of points of the
constructible-topology copies of the `F.obj i`, carrying the product topology as its instance. -/
abbrev ConstructibleFamily (F : I ⥤ TopCat) : Type _ := ∀ i, WithConstructibleTopology (F.obj i)

/-- A family of points of the `F.obj i`, read as a point of `ConstructibleFamily F`. -/
def toConstructibleFamily (F : I ⥤ TopCat) (x : ∀ i, F.obj i) : ConstructibleFamily F :=
  fun i => WithConstructibleTopology.toConstructible (x i)

/-- A point of `ConstructibleFamily F`, read as a family of points of the `F.obj i`. -/
def ofConstructibleFamily (F : I ⥤ TopCat) (x : ConstructibleFamily F) : ∀ i, F.obj i :=
  fun i => WithConstructibleTopology.ofConstructible (x i)

variable {F : I ⥤ TopCat} (hF : IsSpectralDiagram F)

omit hF in
/-- Evaluation at `i` is continuous on `ConstructibleFamily F`. -/
theorem continuous_apply_constructibleFamily (i : I) :
    Continuous fun x : ConstructibleFamily F => x i :=
  @continuous_apply I (fun k ↦ WithConstructibleTopology (F.obj k)) _ i

include hF

/-- For a spectral diagram `F`, the product `ConstructibleFamily F` of the constructible topologies
of the `F.obj i` is compact. -/
theorem compactSpace_constructibleFamily : CompactSpace (ConstructibleFamily F) :=
  @Pi.compactSpace I (fun i ↦ WithConstructibleTopology (F.obj i)) _
    fun i ↦ have := hF.spectral_obj i; inferInstance

/-- The compatibility condition `F.map a (x j) = x i` cuts out a closed subset of
`ConstructibleFamily F`. -/
theorem isClosed_setOf_map_eq {j i : I} (a : j ⟶ i) :
    IsClosed { x : ConstructibleFamily F |
      WithConstructibleTopology.map (F.map a) (x j) = x i } := by
  have := hF.spectral_obj i
  exact isClosed_eq ((hF.spectral_map a).continuous_withConstructibleTopology.comp
    (continuous_apply_constructibleFamily (F := F) j)) (continuous_apply_constructibleFamily i)

omit hF in
/-- The condition `x i ∈ Z i` cuts out a closed subset of `ConstructibleFamily F` as soon as
`Z i` is closed in the constructible topology of `F.obj i`. -/
theorem isClosed_setOf_apply_mem {Z : ∀ i, Set (F.obj i)}
    (hZ : ∀ i, @IsClosed (F.obj i) (constructibleTopology (F.obj i)) (Z i)) (i : I) :
    IsClosed { x : ConstructibleFamily F |
      WithConstructibleTopology.ofConstructible (x i) ∈ Z i } :=
  (WithConstructibleTopology.isClosed_preimage_ofConstructible.mpr (hZ i)).preimage
    (continuous_apply_constructibleFamily i)

omit hF in
/-- For a compatible system of nonempty subsets `Z i ⊆ F.obj i` over a cofiltered `I`, any finite
set `S` of objects and finite set `M` of morphisms of `I`, there is a family that lies in `Z i` for
every `i ∈ S` and is compatible along every morphism in `M`. -/
theorem exists_mem_of_finite (Z : ∀ i, Set (F.obj i)) (hZ_ne : ∀ i, (Z i).Nonempty)
    [IsCofiltered I] (hZ_comp : ∀ ⦃j i : I⦄ (a : j ⟶ i), F.map a '' Z j ⊆ Z i)
    (S : Finset I) (M : Finset (Σ (j : I), Σ (i : I), (j ⟶ i))) :
    ∃ x : ∀ i, F.obj i, (∀ i ∈ S, x i ∈ Z i) ∧ (∀ m ∈ M, F.map m.2.2 (x m.1) = x m.2.1) := by
  classical
  let O : Finset I := S ∪ Finset.image (·.1) M ∪ Finset.image (·.2.1) M
  have hS_sub : ∀ i ∈ S, i ∈ O := fun i hi ↦ Finset.mem_union_left _ (Finset.mem_union_left _ hi)
  have hM_src : ∀ m ∈ M, m.1 ∈ O := fun m hm ↦
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm))
  have hM_tgt : ∀ m ∈ M, m.2.1 ∈ O := fun m hm ↦
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)
  let H : Finset ((X : I) ×' (Y : I) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) :=
    Finset.univ.image (fun (⟨m, hm⟩ : M) ↦ ⟨m.1, m.2.1, hM_src m hm, hM_tgt m hm, m.2.2⟩)
  obtain ⟨z, hz⟩ := hZ_ne (IsCofiltered.inf O H)
  refine ⟨fun i ↦ if h : i ∈ O then F.map (IsCofiltered.infTo O H h) z else (hZ_ne i).some, ?_, ?_⟩
  · intro i hi
    simp only [dite_eq_left (hS_sub i hi)]
    exact hZ_comp _ (Set.mem_image_of_mem _ hz)
  · intro m hm
    simp only [dite_eq_left (hM_src m hm), dite_eq_left (hM_tgt m hm)]
    have hmem : (⟨m.1, m.2.1, hM_src m hm, hM_tgt m hm, m.2.2⟩ :
        (X : I) ×' (Y : I) ×' (_ : X ∈ O) ×' (_ : Y ∈ O) ×' (X ⟶ Y)) ∈ H :=
      Finset.mem_image.mpr ⟨⟨m, hm⟩, Finset.mem_univ _, rfl⟩
    have h := congr_arg (fun f ↦ F.map f z)
      (IsCofiltered.infTo_commutes O H (hM_src m hm) (hM_tgt m hm) hmem)
    rwa [F.map_comp] at h

/-- A compatible cofiltered system of nonempty constructibly closed subsets of a spectral diagram
has nonempty limit. -/
@[stacks 0A2W "part (1)"]
theorem nonempty_limitSet_inter_of_isClosed_constructible [IsCofiltered I]
    (Z : ∀ i, Set (F.obj i)) (hZ_ne : ∀ i, (Z i).Nonempty)
    (hZ_cl : ∀ i, @IsClosed (F.obj i) (constructibleTopology (F.obj i)) (Z i))
    (hZ_comp : ∀ ⦃j i : I⦄ (a : j ⟶ i), F.map a '' Z j ⊆ Z i) :
    { x : ∀ i, F.obj i | x ∈ limitSet F ∧ ∀ i, x i ∈ Z i }.Nonempty := by
  classical
  let t : (Σ (j : I), Σ (i : I), (j ⟶ i)) ⊕ I → Set (ConstructibleFamily F)
    | Sum.inl m => { x | WithConstructibleTopology.map (F.map m.2.2) (x m.1) = x m.2.1 }
    | Sum.inr i => { x | WithConstructibleTopology.ofConstructible (x i) ∈ Z i }
  have ht_cl : ∀ idx, IsClosed (t idx)
    | Sum.inl m => isClosed_setOf_map_eq hF m.2.2
    | Sum.inr i => isClosed_setOf_apply_mem hZ_cl i
  have hfip : ∀ u : Finset ((Σ (j : I), Σ (i : I), (j ⟶ i)) ⊕ I),
      (Set.univ ∩ ⋂ idx ∈ u, t idx).Nonempty := by
    intro u
    obtain ⟨x, hx_mem, hx_comp⟩ := exists_mem_of_finite Z hZ_ne hZ_comp
      (u.preimage Sum.inr fun _ _ _ _ h ↦ Sum.inr.inj h)
      (u.preimage Sum.inl fun _ _ _ _ h ↦ Sum.inl.inj h)
    refine ⟨toConstructibleFamily F x, Set.mem_univ _, ?_⟩
    simp only [Set.mem_iInter]
    rintro (m | i) hidx
    · exact congrArg WithConstructibleTopology.toConstructible
        (hx_comp m (Finset.mem_preimage.mpr hidx))
    · exact hx_mem i (Finset.mem_preimage.mpr hidx)
  obtain ⟨x, -, hx_all⟩ :=
    (@isCompact_univ _ _ (compactSpace_constructibleFamily hF)).inter_iInter_nonempty t ht_cl hfip
  exact ⟨ofConstructibleFamily F x,
    fun {j} {i} a ↦ congrArg WithConstructibleTopology.ofConstructible
      (Set.mem_iInter.mp hx_all (Sum.inl ⟨j, i, a⟩)),
    fun i ↦ Set.mem_iInter.mp hx_all (Sum.inr i)⟩

/-- The cofiltered limit of a diagram of nonempty spectral spaces is nonempty. -/
@[stacks 0A2W "part (2)"]
theorem nonempty_limitSet [IsCofiltered I] (hX_ne : ∀ i, Nonempty (F.obj i)) :
    (limitSet F).Nonempty :=
  (nonempty_limitSet_inter_of_isClosed_constructible hF (fun _ ↦ Set.univ)
    (fun i ↦ ⟨(hX_ne i).some, Set.mem_univ _⟩)
    (fun i ↦ @isClosed_univ (F.obj i) (constructibleTopology (F.obj i)))
    fun {_ _} _ ↦ Set.subset_univ _).mono fun _ hx ↦ hx.1

end SpectralLimits
