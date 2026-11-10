module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Topology.Sheaves.Functors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.PushforwardAlgStruct
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SheafStalk
public import StacksFrontier.Topology.Sheaves.Limits.DescendOpens
public import StacksFrontier.Topology.Sheaves.Limits.GermPullback
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackComparison
public import StacksFrontier.Topology.Spectral.InverseLimits
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter

/-!
# Sections on an intersection of quasi-compact opens

Let `E` be the intersection of a nonempty family of quasi-compact open subsets `U i` of a
quasi-separated scheme, directed under reverse inclusion. For every sheaf of sets on the
scheme, the sections on `E` -- meaning the global sections of the inverse image of the sheaf
along the inclusion of `E` with its subspace topology -- are the filtered colimit of the
sections on the `U i`.

## Main definitions

* `AlgebraicGeometry.intersectionIndex` is a family of opens regarded as an index type
  ordered by reverse inclusion.
* `AlgebraicGeometry.sectionsDiagram` is the diagram of sections of a sheaf on such a family.
* `AlgebraicGeometry.sectionsOnSubset` is the space of global sections of the inverse image of
  a sheaf to a subset.
* `AlgebraicGeometry.stageToSubset` is the canonical restriction from one stage of the family
  to the intersection.
* `AlgebraicGeometry.pullbackGermIso` is the isomorphism
  `Stacks.GermPullbackComparison.pullbackToGerm` from the inverse image of a sheaf of sets to the
  germ model `GermPullback.sheaf` of that inverse image.

## Main results

* `AlgebraicGeometry.colimit_sections_equiv_sections_iInter` identifies the colimit of the
  stage sections with the sections on the intersection, compatibly with every canonical map
  from a stage.
* `AlgebraicGeometry.spectralSpace_of_isCompact`: a quasi-compact open of a quasi-separated
  scheme is a spectral space.
* `AlgebraicGeometry.exists_opens_le_of_iInter_subset`: an open subset containing the
  intersection already contains one of its stages.

## Implementation notes

The index category `intersectionIndex U` is a wrapper rather than a type synonym, so that the
family `U` is determined by the type of an index.

The equivalence is characterized on every colimit injection by the canonical map obtained from
the pullback-pushforward unit, so it is the canonical map and not merely some bijection. The
proof compares the inverse-image sheaf with the sheaf of compatible germs, for which the
statement is a compactness argument on the inverse limit of the stages.

## References

* [Stacks Project, Tag 0APH](https://stacks.math.columbia.edu/tag/0APH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open Stacks.GermPullbackComparison

/-- A family of open subsets, regarded as an indexing type ordered by reverse
inclusion.  This is a wrapper rather than a type synonym so that the family
`U` is determined by the type of an index. -/
structure intersectionIndex {X I : Type u} [TopologicalSpace X] (U : I → Opens X) where
  /-- The index of the corresponding member of the family. -/
  val : I

/-- A family of opens is ordered by reverse inclusion: one index lies below another exactly when
the second open is contained in the first. -/
instance {X I : Type u} [TopologicalSpace X] (U : I → Opens X) :
    Preorder (intersectionIndex U) where
  le i j := U j.val ≤ U i.val
  le_refl _ := le_rfl
  le_trans _ _ _ hij hjk := hjk.trans hij

/-- A nonempty family of opens has a nonempty reverse-inclusion index. -/
instance {X I : Type u} [TopologicalSpace X] (U : I → Opens X) [Nonempty I] :
    Nonempty (intersectionIndex U) :=
  Nonempty.map (intersectionIndex.mk (U := U)) inferInstance

/-- The diagram sending a member of a decreasing family of opens to the
sections of a sheaf on that open. -/
def sectionsDiagram {X I : Type u} [TopologicalSpace X]
    (F : (TopCat.of X).Sheaf (Type u)) (U : I → Opens X) :
    Functor (intersectionIndex U) (Type u) where
  obj i := F.obj.obj (op (U i.val))
  map {i j} f := F.obj.map (homOfLE f.le).op
  map_id i := by
    rw [← F.obj.map_id]
    rfl
  map_comp f g := by
    rw [← F.obj.map_comp]
    rfl

/-- Sections on a subset are global sections of the inverse-image sheaf on
the subset with its subspace topology. -/
noncomputable def sectionsOnSubset {X : Type u} [TopologicalSpace X] (E : Set X)
    (F : (TopCat.of X).Sheaf (Type u)) :=
  ((TopCat.Sheaf.pullback (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).obj F).obj.obj (op ⊤)

/-- The canonical map from sections on an open containing `E` to sections of
the inverse-image sheaf on `E`. -/
noncomputable def stageToSubset {X I : Type u} [TopologicalSpace X]
    (F : (TopCat.of X).Sheaf (Type u)) (U : I → Opens X)
    (E : Set X) (hE : ∀ i, E ⊆ U i) (i : intersectionIndex U) :
    (sectionsDiagram F U).obj i → sectionsOnSubset E F := fun s ↦
  TopCat.Presheaf.restrict
      (F := ((TopCat.Sheaf.pullback (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).obj F).obj)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (Stacks.subsetInclusion (TopCat.of X) E)).unit.app F).hom.app
      (op (U i.val)) s) (homOfLE fun x _ ↦ hE i.val x.2)

/-- A family of opens in which any two members contain a common member is filtered for reverse
inclusion. -/
lemma filtered_intersectionIndex {X I : Type u} [TopologicalSpace X]
    [Nonempty I] (U : I → Opens X)
    (hdir : ∀ i j, (∃ k, (U k : Set X) ⊆ U i ∩ U j)) :
    IsFiltered (intersectionIndex U) := by
  let : IsDirectedOrder (intersectionIndex U) := ⟨fun i j ↦ by
    obtain ⟨k, hk⟩ := hdir i.val j.val
    exact ⟨⟨k⟩, hk.trans Set.inter_subset_left, hk.trans Set.inter_subset_right⟩⟩
  infer_instance

/-- The canonical maps from the stages to the intersection are compatible with the restriction
maps between stages. -/
private lemma stageToSubset_naturality {X I : Type u} [TopologicalSpace X]
    (F : (TopCat.of X).Sheaf (Type u)) (U : I → Opens X)
    (E : Set X) (hE : ∀ i, E ⊆ U i)
    {i j : intersectionIndex U} (f : i ⟶ j)
    (s : (sectionsDiagram F U).obj i) :
    stageToSubset F U E hE j ((sectionsDiagram F U).map f s) =
      stageToSubset F U E hE i s := by
  let G := ((TopCat.Sheaf.pullback (Type u) (Stacks.subsetInclusion (TopCat.of X) E)).obj F).obj
  let η := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
    (Stacks.subsetInclusion (TopCat.of X) E)).unit.app F).hom
  let a : (op (U i.val) : (Opens X)ᵒᵖ) ⟶ op (U j.val) := (homOfLE f.le).op
  let Vi : Opens E := (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj (U i.val)
  let Vj : Opens E := (Opens.map (Stacks.subsetInclusion (TopCat.of X) E)).obj (U j.val)
  let aE : (op Vi : (Opens E)ᵒᵖ) ⟶ op Vj :=
    (homOfLE (by intro x hx; exact f.le hx)).op
  let bj : (op Vj : (Opens E)ᵒᵖ) ⟶ op ⊤ :=
    (homOfLE (by intro x hx; exact hE j.val x.2)).op
  let bi : (op Vi : (Opens E)ᵒᵖ) ⟶ op ⊤ :=
    (homOfLE (by intro x hx; exact hE i.val x.2)).op
  have hn := η.naturality a
  change G.map bj (η.app (op (U j.val)) (F.obj.map a s)) =
    G.map bi (η.app (op (U i.val)) s)
  have hn' : η.app (op (U j.val)) (F.obj.map a s) =
      G.map aE (η.app (op (U i.val)) s) :=
    congrArg (fun h ↦ h s) hn
  rw [hn', show bi = aE ≫ bj from Subsingleton.elim _ _, G.map_comp]
  rfl

/-- The map out of the colimit of the stage sections determined by the canonical maps to the
sections on the intersection. -/
private noncomputable def canonicalMap {X I : Type u} [TopologicalSpace X]
    (F : (TopCat.of X).Sheaf (Type u)) (U : I → Opens X)
    (E : Set X) (hE : ∀ i, E ⊆ U i) :
    colimit (sectionsDiagram F U) ⟶ sectionsOnSubset E F :=
  colimit.desc _
    { pt := sectionsOnSubset E F
      ι :=
        { app := fun i ↦ ↾stageToSubset F U E hE i
          naturality := by
            intro i j f
            ext s
            change stageToSubset F U E hE j ((sectionsDiagram F U).map f s) =
              stageToSubset F U E hE i s
            exact stageToSubset_naturality F U E hE f s } }

/-- Restricting `canonicalMap` along a colimit injection gives the canonical map from that
stage. -/
private lemma canonicalMap_ι {X I : Type u} [TopologicalSpace X]
    (F : (TopCat.of X).Sheaf (Type u)) (U : I → Opens X)
    (E : Set X) (hE : ∀ i, E ⊆ U i)
    (i : intersectionIndex U) (s : (sectionsDiagram F U).obj i) :
    canonicalMap F U E hE (colimit.ι (sectionsDiagram F U) i s) =
      stageToSubset F U E hE i s := by
  rw [canonicalMap, ← ConcreteCategory.comp_apply, colimit.ι_desc]
  rfl

/-- The intersection of a family of opens is contained in each member. -/
private lemma subset_of_eq_iInter {X I : Type u} [TopologicalSpace X] {U : I → Opens X}
    {E : Set X} (hE : E = ⋂ i, (U i : Set X)) (i : I) : E ⊆ U i :=
  hE ▸ Set.iInter_subset (fun i ↦ (U i : Set X)) i

/-- On a spectral space, an open subset containing the intersection of a directed family of
quasi-compact opens already contains one member of the family. -/
private lemma exists_opens_le_of_iInter_subset_of_spectralSpace {X I : Type u}
    [TopologicalSpace X] [SpectralSpace X] [Nonempty I]
    (U : I → Opens X) (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X))
    (V : Opens X) (hEV : E ⊆ V) : ∃ i, U i ≤ V :=
  SpectralSubset.exists_subset_of_subset_isOpen (fun i ↦ (U i : Set X))
    (fun i ↦ ⟨(U i).isOpen, hqc i⟩) hdir E hE V V.isOpen hEV

/-- On a spectral space, the intersection of a directed family of quasi-compact opens is
quasi-compact. -/
private lemma isCompact_iInter_opens_of_spectralSpace {X I : Type u}
    [TopologicalSpace X] [SpectralSpace X] [Nonempty I]
    (U : I → Opens X) (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) : IsCompact E :=
  (SpectralSubset.isStableCompact_of_isDirectedInterCompactOpen E
    ⟨I, inferInstance, (fun i ↦ (U i : Set X)),
      (fun i ↦ ⟨(U i).isOpen, hqc i⟩), hE, hdir⟩).1

/-- A quasi-compact open subspace of a quasi-separated scheme is a spectral space. -/
lemma spectralSpace_of_isCompact {X : AlgebraicGeometry.Scheme.{u}}
    [QuasiSeparatedSpace X] (U : Opens X) (hU : IsCompact (U : Set X)) :
    SpectralSpace U := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let : QuasiSeparatedSpace U := U.isOpenEmbedding'.quasiSeparatedSpace
  exact SpectralSpace.mk

/-- In a quasi-separated space, the preimage of a quasi-compact open subset in a quasi-compact
open subspace `U` is quasi-compact. -/
private lemma isCompact_preimage_val {X : Type u} [TopologicalSpace X]
    [QuasiSeparatedSpace X] (U : Opens X) (hU : IsCompact (U : Set X)) (A : Set X)
    (hAo : IsOpen A) (hA : IsCompact A) : IsCompact (Subtype.val ⁻¹' A : Set U) := by
  apply U.isOpenEmbedding'.isEmbedding.isCompact_iff.mpr
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]
  exact QuasiSeparatedSpace.inter_isCompact _ _ hAo hA U.isOpen hU

/-- On a quasi-separated space, the inclusion of a quasi-compact open subset into a larger open
subset is a spectral map. -/
private lemma isSpectralMap_opens_inclusion {X : Type u} [TopologicalSpace X]
    [QuasiSeparatedSpace X] (U V : Opens X) (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) :
    IsSpectralMap (fun x : U ↦ (⟨x.1, hUV x.2⟩ : V)) := by
  constructor
  · exact Continuous.subtype_mk continuous_subtype_val (fun x ↦ hUV x.2)
  · intro W hWo hWc
    convert isCompact_preimage_val U hU _ (V.isOpenEmbedding'.isOpenMap W hWo)
      (hWc.image continuous_subtype_val) using 1
    ext x
    exact (Subtype.val_injective.mem_set_image (s := W) (a := ⟨x.1, hUV x.2⟩)).symm

/-- The preimage of an open subset of `X` in an open subspace `U₀`. -/
private def opensPreimageVal {X : Type u} [TopologicalSpace X] (U₀ V : Opens X) : Opens U₀ :=
  (Opens.map (TopCat.ofHom ⟨(Subtype.val : U₀ → X), continuous_subtype_val⟩)).obj V

/-- Restricting a directed family of quasi-compact opens of a quasi-separated space to a member
`U i₀` gives a directed family of quasi-compact opens with the restricted intersection. -/
private lemma restrict_family_to_stage {X I : Type u} [TopologicalSpace X]
    [QuasiSeparatedSpace X] (U : I → Opens X) (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j) (E : Set X)
    (hE : E = ⋂ i, (U i : Set X)) (i₀ : I) :
    (∀ i, IsCompact (opensPreimageVal (U i₀) (U i) : Set (U i₀))) ∧
      (∀ i j, ∃ k, (opensPreimageVal (U i₀) (U k) : Set (U i₀)) ⊆
        opensPreimageVal (U i₀) (U i) ∩ opensPreimageVal (U i₀) (U j)) ∧
      (Subtype.val ⁻¹' E : Set (U i₀)) = ⋂ i, (opensPreimageVal (U i₀) (U i) : Set (U i₀)) := by
  refine ⟨fun i ↦ isCompact_preimage_val (U i₀) (hqc i₀) (U i) (U i).isOpen (hqc i),
    fun i j ↦ ?_, by rw [hE, Set.preimage_iInter]; rfl⟩
  obtain ⟨k, hk⟩ := hdir i j
  exact ⟨k, fun x hx ↦ hk hx⟩

/-- An open subset of a quasi-separated scheme containing the intersection of a directed family of
quasi-compact opens already contains one member of the family. -/
lemma exists_opens_le_of_iInter_subset {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] [Nonempty I]
    (U : I → Opens X) (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X))
    (V : Opens X) (hEV : E ⊆ V) : ∃ i, U i ≤ V := by
  classical
  let i₀ : I := Classical.choice inferInstance
  let U₀ : Opens X := U i₀
  let : SpectralSpace U₀ := spectralSpace_of_isCompact U₀ (hqc i₀)
  obtain ⟨hqc', hdir', hE'⟩ := restrict_family_to_stage U hqc hdir E hE i₀
  let U' : I → Opens U₀ := fun i ↦ opensPreimageVal U₀ (U i)
  let E' : Set U₀ := Subtype.val ⁻¹' E
  let V' : Opens U₀ := opensPreimageVal U₀ V
  have hEV' : E' ⊆ V' := fun x hx ↦ hEV hx
  obtain ⟨i, hi⟩ := exists_opens_le_of_iInter_subset_of_spectralSpace U' hqc' hdir' E' hE' V' hEV'
  obtain ⟨k, hk⟩ := hdir i i₀
  exact ⟨k, fun x hx ↦ hi (show (⟨x, (hk hx).2⟩ : U₀) ∈ U' i from (hk hx).1)⟩

/-- The intersection of a directed family of quasi-compact opens of a quasi-separated scheme is
quasi-compact. -/
private lemma isCompact_iInter_opens {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] [Nonempty I]
    (U : I → Opens X) (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) : IsCompact E := by
  classical
  let i₀ : I := Classical.choice inferInstance
  let U₀ : Opens X := U i₀
  let : SpectralSpace U₀ := spectralSpace_of_isCompact U₀ (hqc i₀)
  obtain ⟨hqc', hdir', hE'⟩ := restrict_family_to_stage U hqc hdir E hE i₀
  let U' : I → Opens U₀ := fun i ↦ opensPreimageVal U₀ (U i)
  let E' : Set U₀ := Subtype.val ⁻¹' E
  have hcompact : IsCompact E' := isCompact_iInter_opens_of_spectralSpace U' hqc' hdir' E' hE'
  have hEsub : E ⊆ U₀ := subset_of_eq_iInter hE i₀
  have himage : Subtype.val '' E' = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hEsub hx⟩, hx, rfl⟩
  rw [← himage]
  exact hcompact.image continuous_subtype_val

/-- A family of opens of a quasi-separated scheme, viewed as a cofiltered diagram of spectral
spaces and spectral maps. -/
private def openDiagram {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] (U : I → Opens X)
    [IsFiltered (intersectionIndex U)] (hqc : ∀ i, IsCompact (U i : Set X)) :
    SpectralDiagram ((intersectionIndex U)ᵒᵖ) where
  F :=
    { obj := fun i ↦ TopCat.of (U i.unop.val)
      map := fun {j i} f ↦ TopCat.ofHom
        ⟨fun x ↦ (⟨x.1, f.unop.le x.2⟩ : U i.unop.val),
          Continuous.subtype_mk continuous_subtype_val (fun x ↦ f.unop.le x.2)⟩
      map_id := by
        intro i
        apply TopCat.hom_ext
        ext x
        rfl
      map_comp := by
        intro i j k f g
        apply TopCat.hom_ext
        ext x
        rfl }
  isSpectralSpace := fun i ↦ spectralSpace_of_isCompact (U i.unop.val) (hqc _)
  isSpectralMap := fun {j i} f ↦
    isSpectralMap_opens_inclusion (U j.unop.val) (U i.unop.val)
      f.unop.le (hqc _)

/-- A point of the inverse limit of the stages has the same underlying point at every stage. -/
private lemma openDiagram_proj_val_eq {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] (U : I → Opens X)
    [IsFiltered (intersectionIndex U)] (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (x : (openDiagram U hqc).invLimit) (i j : I) :
    ((openDiagram U hqc).projFun (op (⟨i⟩ : intersectionIndex U)) x : U i).1 =
      ((openDiagram U hqc).projFun (op (⟨j⟩ : intersectionIndex U)) x : U j).1 := by
  obtain ⟨k, hk⟩ := hdir i j
  let D := openDiagram U hqc
  let a : (op (⟨k⟩ : intersectionIndex U)) ⟶ op (⟨i⟩ : intersectionIndex U) :=
    (homOfLE (show (⟨i⟩ : intersectionIndex U) ≤ ⟨k⟩ from hk.trans Set.inter_subset_left)).op
  let b : (op (⟨k⟩ : intersectionIndex U)) ⟶ op (⟨j⟩ : intersectionIndex U) :=
    (homOfLE (show (⟨j⟩ : intersectionIndex U) ≤ ⟨k⟩ from hk.trans Set.inter_subset_right)).op
  have ha := D.projFun_comp a x
  have hb := D.projFun_comp b x
  exact congrArg Subtype.val ha |>.trans (congrArg Subtype.val hb).symm

/-- The intersection of the family, with its subspace topology, is a cone over the stages. -/
private def openDiagram_cone {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] (U : I → Opens X)
    [IsFiltered (intersectionIndex U)] (hqc : ∀ i, IsCompact (U i : Set X))
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) : Cone (openDiagram U hqc).F where
  pt := TopCat.of E
  π :=
    { app := fun j ↦ TopCat.ofHom
        ⟨fun x ↦ (⟨x.1, subset_of_eq_iInter hE j.unop.val x.2⟩ : U j.unop.val),
          Continuous.subtype_mk continuous_subtype_val
            (fun x ↦ subset_of_eq_iInter hE j.unop.val x.2)⟩
      naturality := by
        intro j i f
        apply TopCat.hom_ext
        ext x
        rfl }

/-- The canonical map from the intersection to the inverse limit of the stages preserves
underlying points. -/
private lemma openDiagram_cone_lift_proj {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] (U : I → Opens X)
    [IsFiltered (intersectionIndex U)] (hqc : ∀ i, IsCompact (U i : Set X))
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) (i : I) (x : E) :
    ((openDiagram U hqc).projFun (op (⟨i⟩ : intersectionIndex U))
      (limit.lift (openDiagram U hqc).F (openDiagram_cone U hqc E hE) x) : U i).1 = x.1 :=
  congrArg Subtype.val (congrArg (fun f : TopCat.of E ⟶ TopCat.of (U i) ↦ f x)
    (limit.lift_π (openDiagram_cone U hqc E hE) (op (⟨i⟩ : intersectionIndex U))))

/-- The intersection of the family, with its subspace topology, is the inverse limit of the
stages. -/
private noncomputable def openDiagram_limitHomeomorph
    {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] [Nonempty I]
    (U : I → Opens X) [IsFiltered (intersectionIndex U)]
    (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) :
    E ≃ₜ (openDiagram U hqc).invLimit := by
  classical
  let D := openDiagram U hqc
  have hEi := subset_of_eq_iInter hE
  let C := openDiagram_cone U hqc E hE
  let φ : E → D.invLimit := limit.lift D.F C
  have hφ (y : E) (i : I) :
      (D.projFun (op (⟨i⟩ : intersectionIndex U)) (φ y) : U i).1 = y.1 :=
    openDiagram_cone_lift_proj U hqc E hE i y
  let i₀ : I := Classical.choice inferInstance
  let ψ : D.invLimit → E := fun x ↦
    ⟨((D.projFun (op (⟨i₀⟩ : intersectionIndex U)) x : U i₀).1), by
      rw [hE]
      simp only [Set.mem_iInter]
      intro i
      change ((openDiagram U hqc).projFun
        (op (⟨i₀⟩ : intersectionIndex U)) x : U i₀).1 ∈ U i
      rw [openDiagram_proj_val_eq U hqc hdir x i₀ i]
      exact (D.projFun (op (⟨i⟩ : intersectionIndex U)) x : U i).2⟩
  have hψφ (y : E) : ψ (φ y) = y := Subtype.ext (hφ y i₀)
  have hφψ (x : D.invLimit) : φ (ψ x) = x := by
    apply D.projFun_injective_pi
    intro j
    apply Subtype.ext
    rw [hφ, show (ψ x).1 = (D.projFun (op (⟨i₀⟩ : intersectionIndex U)) x : U i₀).1 from rfl]
    exact openDiagram_proj_val_eq U hqc hdir x i₀ j.unop.val
  exact
    { toEquiv := ⟨φ, ψ, hψφ, hφψ⟩
      continuous_toFun := (limit.lift D.F C).hom.continuous
      continuous_invFun := Continuous.subtype_mk
        ((D.projFun_continuous (op (⟨i₀⟩ : intersectionIndex U))).subtype_val)
        (fun x ↦ (ψ x).2) }

/-- The homeomorphism of the intersection with the inverse limit of the stages preserves
underlying points. -/
private lemma openDiagram_limitHomeomorph_proj
    {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] [Nonempty I]
    (U : I → Opens X) [IsFiltered (intersectionIndex U)]
    (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X)) (i : I) (x : E) :
    ((openDiagram U hqc).projFun (op (⟨i⟩ : intersectionIndex U))
      (openDiagram_limitHomeomorph U hqc hdir E hE x) : U i).1 = x.1 :=
  openDiagram_cone_lift_proj U hqc E hE i x


/-- **The inverse image of a sheaf of sets, as the sheaf of compatible germs.** The germ model
`GermPullback.sheaf` of the inverse image `g^{-1}F` is the inverse image, canonically. -/
noncomputable def pullbackGermIso {Y Z : TopCat.{u}} (g : Z ⟶ Y) (F : Y.Sheaf (Type u)) :
    (TopCat.Sheaf.pullback (Type u) g).obj F ≅
      GermPullback.sheaf (ConcreteCategory.hom g) F.presheaf :=
  haveI := Stacks.GermPullbackComparison.pullbackToGerm_isIso g F
  asIso (pullbackToGerm g F)

/-- `pullbackToGerm` carries the canonical map from a stage to the family of germs of the given
section. -/
private lemma pullbackToGerm_stageToSubset {X I : Type u} [TopologicalSpace X]
    (F : (TopCat.of X).Sheaf (Type u)) (U : I → Opens X)
    (E : Set X) (hE : ∀ i, E ⊆ U i) (i : intersectionIndex U)
    (s : (sectionsDiagram F U).obj i) :
    (pullbackToGerm (Stacks.subsetInclusion (TopCat.of X) E) F).hom.app (op ⊤)
      (stageToSubset F U E hE i s) =
      GermPullback.ofSection (g := ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) E))
        (W := ⊤) (V := U i.val) (fun z ↦ hE i.val z.1.2) s := by
  let g := Stacks.subsetInclusion (TopCat.of X) E
  let W := (Opens.map g).obj (U i.val)
  let a : (⊤ : Opens E) ⟶ W := homOfLE fun z _ ↦ hE i.val z.2
  let H := (TopCat.Sheaf.pullback (Type u) g).obj F
  let G := GermPullback.sheaf (ConcreteCategory.hom g) F.presheaf
  let m := (pullbackToGerm g F).hom
  let t := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
    (op (U i.val)) s
  have hn := m.naturality a.op
  have hp : m.app (op ⊤) (H.presheaf.map a.op t) =
      G.presheaf.map a.op (m.app (op W) t) :=
    congrArg (fun f ↦ f t) hn
  have hm : m.app (op W) t = GermPullback.ofSection (g := ConcreteCategory.hom g)
      (W := W) (V := U i.val) (fun z ↦ z.2) s :=
    pullbackToGerm_unit g F (U i.val) s
  change m.app (op ⊤) (H.presheaf.map a.op t) = _
  rw [hp, hm]
  apply GermPullback.ext
  intro z
  rfl

/-- The locus where two sections of a presheaf, each defined on an open subset, have the same germ
is open. -/
private lemma isOpen_germ_agree_two {X : Type u} [TopologicalSpace X]
    (F : (TopCat.of X).Presheaf (Type u)) (U V : Opens X)
    (s : F.obj (op U)) (t : F.obj (op V)) :
    IsOpen {x : X | ∃ (hxU : x ∈ U) (hxV : x ∈ V),
      F.germ U x hxU s = F.germ V x hxV t} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨hxU, hxV, he⟩ := hx
  obtain ⟨W, hxW, iU, iV, hw⟩ := F.germ_eq x hxU hxV s t he
  refine ⟨W, ?_, W.isOpen, hxW⟩
  intro y hy
  refine ⟨iU.le hy, iV.le hy, ?_⟩
  rw [← F.germ_res_apply iU y hy s, ← F.germ_res_apply iV y hy t, hw]

/-- A section of the sheaf of compatible germs on the whole subset is, near each point, the family
of germs of an ambient section. -/
private lemma germPullback_local_section {X : Type u} [TopologicalSpace X]
    (F : (TopCat.of X).Presheaf (Type u)) (E : Set X)
    (σ : (GermPullback.sheaf
      (ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) E)) F).presheaf.obj
      (op ⊤)) (x : E) :
    ∃ (V : Opens X) (_ : x.1 ∈ V) (s : F.obj (op V)),
      ∀ (y : E) (hy : y.1 ∈ V),
        σ.1 (⟨y, trivial⟩ : (⊤ : Opens E)) =
          (⟨y.1, F.germ V y.1 hy s⟩ : GermPullback.Germs F) := by
  obtain ⟨W, hxW, i, V, hV, s, hs⟩ :=
    GermPullback.exists_repr σ (show x ∈ (⊤ : Opens E) from trivial)
  obtain ⟨B, hBo, hB⟩ := isOpen_induced_iff.mp W.isOpen
  let A : Opens X := ⟨B ∩ V, hBo.inter V.isOpen⟩
  have hAV : A ≤ V := Set.inter_subset_right
  have hxB : x.1 ∈ B := show x ∈ (Subtype.val ⁻¹' B : Set E) from hB.symm ▸ hxW
  have hxA : x.1 ∈ A := ⟨hxB, hV ⟨x, hxW⟩⟩
  refine ⟨A, hxA, F.map (homOfLE hAV).op s, ?_⟩
  intro y hyA
  have hyW : y ∈ W := by
    change y ∈ (W : Set E)
    rw [← hB]
    exact hyA.1
  have hyV : y.1 ∈ V := hV ⟨y, hyW⟩
  have hσ := hs (⟨y, hyW⟩ : W)
  have hg := F.germ_res_apply (homOfLE hAV) y.1 hyA s
  change σ.1 (⟨y, trivial⟩ : (⊤ : Opens E)) =
    (⟨y.1, F.germ V y.1 hyV s⟩ : GermPullback.Germs F) at hσ
  exact hσ.trans (congrArg (fun ξ ↦ (⟨y.1, ξ⟩ : GermPullback.Germs F)) hg.symm)

/-- On a scheme, the ambient section representing a section of the sheaf of compatible germs near
a point may be taken on a quasi-compact open. -/
private lemma germPullback_local_compact_section
    {X : AlgebraicGeometry.Scheme.{u}} (F : X.toTopCat.Sheaf (Type u))
    (E : Set X)
    (σ : (GermPullback.sheaf (ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) E))
      F.presheaf).presheaf.obj (op ⊤)) (x : E) :
    ∃ (V : Opens X), IsCompact (V : Set X) ∧
      ∃ (_ : x.1 ∈ V) (s : F.presheaf.obj (op V)),
      ∀ (y : E) (hy : y.1 ∈ V),
        σ.1 (⟨y, trivial⟩ : (⊤ : Opens E)) =
          (⟨y.1, F.presheaf.germ V y.1 hy s⟩ : GermPullback.Germs F.presheaf) := by
  obtain ⟨W, hxW, s, hs⟩ := germPullback_local_section F.presheaf E σ x
  obtain ⟨A, hAc, hAo, hAx, hAW⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (K := {x.1}) (U := (W : Set X)) isCompact_singleton W.isOpen (by rintro _ rfl; exact hxW)
  let V : Opens X := ⟨A, hAo⟩
  have hVW : V ≤ W := hAW
  have hxV : x.1 ∈ V := hAx (Set.mem_singleton x.1)
  refine ⟨V, hAc, hxV, F.presheaf.map (homOfLE hVW).op s, ?_⟩
  intro y hyV
  exact (hs y (hVW hyV)).trans (congrArg (fun ξ ↦ (⟨y.1, ξ⟩ : GermPullback.Germs F.presheaf))
    (F.presheaf.germ_res_apply (homOfLE hVW) y.1 hyV s).symm)

/-- If every point of the inverse limit lying in a quasi-compact open lies in a given open, then
the same already holds at some stage of the diagram. -/
private lemma spectralDiagram_exists_stage_subset_open
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : SpectralDiagram.{u, u} J) (j : J)
    (W : Opens (D.F.obj j)) (hW : IsCompact (W : Set (D.F.obj j)))
    (S : Opens (D.F.obj j))
    (h : ∀ (x : D.invLimit), D.projFun j x ∈ W → D.projFun j x ∈ S) :
    ∃ (m : J) (c : m ⟶ j), ∀ (z : D.F.obj m),
      D.mapFun c z ∈ W → D.mapFun c z ∈ S := by
  classical
  by_contra hc
  push Not at hc
  have hne (m : J) (c : m ⟶ j) :
      (D.mapFun c ⁻¹' ((W : Set (D.F.obj j)) \ (S : Set (D.F.obj j)))).Nonempty :=
    hc m c
  obtain ⟨x, hxW, hxS⟩ := D.exists_projFun_mem_diff_of_forall_nonempty
    W.isOpen hW S.isOpen hne
  exact hxS (h x hxW)

/-- Two sections whose germs agree at every point of the intersection already have agreeing germs
on the overlap at some stage. -/
private lemma exists_stage_germ_agree_on_compact_overlap
    {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] [Nonempty I]
    (F : X.toTopCat.Sheaf (Type u)) (U : I → Opens X)
    [IsFiltered (intersectionIndex U)]
    (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X))
    (i₀ : I) (V W : Opens X) (hV : IsCompact (V : Set X))
    (hW : IsCompact (W : Set X))
    (s : F.presheaf.obj (op V)) (t : F.presheaf.obj (op W))
    (h : ∀ (x : E) (hxV : x.1 ∈ V) (hxW : x.1 ∈ W),
      F.presheaf.germ V x.1 hxV s = F.presheaf.germ W x.1 hxW t) :
    ∃ k : I, U k ≤ U i₀ ∧
      ∀ (p : X) (_ : p ∈ U k) (hpV : p ∈ V) (hpW : p ∈ W),
        F.presheaf.germ V p hpV s = F.presheaf.germ W p hpW t := by
  let D := openDiagram U hqc
  let j : (intersectionIndex U)ᵒᵖ := op ⟨i₀⟩
  let f : TopCat.of (U i₀) ⟶ X.toTopCat :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let B : Opens (U i₀) := (Opens.map f).obj (V ⊓ W)
  have hBc : IsCompact (B : Set (U i₀)) :=
    isCompact_preimage_val (U i₀) (hqc i₀) _ (V ⊓ W).isOpen
      (QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hV W.isOpen hW)
  let S : Opens X := ⟨{p | ∃ (hpV : p ∈ V) (hpW : p ∈ W),
      F.presheaf.germ V p hpV s = F.presheaf.germ W p hpW t},
    isOpen_germ_agree_two F.presheaf V W s t⟩
  let S₀ : Opens (U i₀) := (Opens.map f).obj S
  have hlim (p : D.invLimit) : D.projFun j p ∈ B → D.projFun j p ∈ S₀ := by
    intro hpB
    let H := openDiagram_limitHomeomorph U hqc hdir E hE
    let x : E := H.symm p
    have hpx : (D.projFun j p : U i₀).1 = x.1 := by
      rw [← H.apply_symm_apply p]
      exact openDiagram_limitHomeomorph_proj U hqc hdir E hE i₀ x
    have hxV : x.1 ∈ V := by rw [← hpx]; exact hpB.1
    have hxW : x.1 ∈ W := by rw [← hpx]; exact hpB.2
    change (D.projFun j p : U i₀).1 ∈ S
    rw [hpx]
    exact ⟨hxV, hxW, h x hxV hxW⟩
  obtain ⟨m, c, hc⟩ := spectralDiagram_exists_stage_subset_open D j B hBc S₀ hlim
  refine ⟨m.unop.val, c.unop.le, ?_⟩
  intro p hp hpV hpW
  exact (hc ⟨p, hp⟩ ⟨hpV, hpW⟩).2.2

/-- Every section of the sheaf of compatible germs on the intersection comes from a section on
some stage. -/
private lemma germPullback_stage_surjective
    {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] [Nonempty I]
    (F : X.toTopCat.Sheaf (Type u)) (U : I → Opens X)
    (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X))
    (σ : (GermPullback.sheaf (ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) E))
      F.presheaf).presheaf.obj (op ⊤)) :
    ∃ (i : I) (s : F.presheaf.obj (op (U i))),
      GermPullback.ofSection (g := ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) E))
        (W := ⊤) (V := U i)
        (fun z ↦ subset_of_eq_iInter hE i z.1.2) s = σ := by
  classical
  let : IsFiltered (intersectionIndex U) := filtered_intersectionIndex U hdir
  let i₀ : I := Classical.choice inferInstance
  choose V hVc hx s hs using fun x : E ↦
    germPullback_local_compact_section F E σ x
  have hcov : E ⊆ ⋃ x : E, (V x : Set X) := fun p hp ↦
    Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hx ⟨p, hp⟩⟩
  obtain ⟨T, hT⟩ := (isCompact_iInter_opens U hqc hdir E hE).elim_finite_subcover
    (fun x : E ↦ (V x : Set X)) (fun x ↦ (V x).isOpen) hcov
  let C : Opens X := ⟨⋃ x ∈ T, (V x : Set X),
    isOpen_biUnion fun x hxT ↦ (V x).isOpen⟩
  obtain ⟨iC, hiC⟩ := exists_opens_le_of_iInter_subset U hqc hdir E hE C hT
  choose k hkU hkAgree using fun x y : T ↦
    exists_stage_germ_agree_on_compact_overlap F U hqc hdir E hE i₀
      (V x.1) (V y.1) (hVc x.1) (hVc y.1)
      (s x.1) (s y.1) (fun p hpX hpY ↦
        SpectralSheafSystem.germs_snd_eq
          ((hs x.1 p hpX).symm.trans (hs y.1 p hpY)))
  let J := (intersectionIndex U)ᵒᵖ
  let L : Finset J :=
    insert (op (⟨iC⟩ : intersectionIndex U))
      (insert (op (⟨i₀⟩ : intersectionIndex U))
        (Finset.image (fun xy : T × T ↦ op (⟨k xy.1 xy.2⟩ : intersectionIndex U))
          Finset.univ))
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists L
  have hmC : U m.unop.val ≤ U iC :=
    (Classical.choice (hm (Finset.mem_insert_self _ _))).unop.le
  have hmPair (x y : T) : U m.unop.val ≤ U (k x y) :=
    (Classical.choice (hm (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Finset.mem_univ (x, y))))))).unop.le
  let A (x : T) : Opens X := U m.unop.val ⊓ V x.1
  let r (x : T) : F.presheaf.obj (op (A x)) :=
    F.presheaf.map (homOfLE inf_le_right).op (s x.1)
  have hA (x : T) : A x ≤ U m.unop.val := inf_le_left
  have hAcov (p : X) (hp : p ∈ U m.unop.val) : ∃ x : T, p ∈ A x := by
    have hpC : p ∈ C := hiC (hmC hp)
    obtain ⟨x, hxT, hpV⟩ := Set.mem_iUnion₂.mp hpC
    exact ⟨⟨x, hxT⟩, ⟨hp, hpV⟩⟩
  have hAgree (x y : T) (p : X) (hpX : p ∈ A x) (hpY : p ∈ A y) :
      F.presheaf.germ (A x) p hpX (r x) =
        F.presheaf.germ (A y) p hpY (r y) := by
    rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
    exact hkAgree x y p (hmPair x y hpX.1) hpX.2 hpY.2
  obtain ⟨t, ht⟩ := SpectralSheafSystem.exists_section_of_germ_agree
    F (U m.unop.val) A hA hAcov r hAgree
  have hEm : E ⊆ U m.unop.val := subset_of_eq_iInter hE _
  refine ⟨m.unop.val, t, ?_⟩
  apply GermPullback.ext
  intro z
  obtain ⟨x, hxT, hzV⟩ := Set.mem_iUnion₂.mp (hT z.1.2)
  let xT : T := ⟨x, hxT⟩
  have hzA : z.1.1 ∈ A xT := ⟨hEm z.1.2, hzV⟩
  have hst := ht xT z.1.1 hzA hzA.1
  have hr : F.presheaf.germ (A xT) z.1.1 hzA (r xT) =
      F.presheaf.germ (V x) z.1.1 hzV (s x) :=
    F.presheaf.germ_res_apply (homOfLE inf_le_right) z.1.1 hzA (s x)
  have hsigma := hs x z.1 hzV
  change (⟨z.1.1, F.presheaf.germ (U m.unop.val) z.1.1 hzA.1 t⟩ :
      GermPullback.Germs F.presheaf) = σ.1 z
  rw [hst, hr]
  exact hsigma.symm

/-- Two stage sections with the same family of germs on the intersection have the same image in
the colimit. -/
private lemma colimit_sections_eq_of_germ_eq
    {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] [Nonempty I]
    (F : X.toTopCat.Sheaf (Type u)) (U : I → Opens X)
    (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j)
    (E : Set X) (hE : E = ⋂ i, (U i : Set X))
    (i j : intersectionIndex U)
    (s : (sectionsDiagram F U).obj i) (t : (sectionsDiagram F U).obj j)
    (he : GermPullback.ofSection
        (g := ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) E))
        (W := ⊤) (V := U i.val)
        (fun z ↦ subset_of_eq_iInter hE i.val z.1.2) s =
      GermPullback.ofSection (g := ConcreteCategory.hom (Stacks.subsetInclusion (TopCat.of X) E))
        (W := ⊤) (V := U j.val)
        (fun z ↦ subset_of_eq_iInter hE j.val z.1.2) t) :
    colimit.ι (sectionsDiagram F U) i s =
      colimit.ι (sectionsDiagram F U) j t := by
  let S : Opens X := ⟨{p | ∃ (hpI : p ∈ U i.val) (hpJ : p ∈ U j.val),
      F.presheaf.germ (U i.val) p hpI s = F.presheaf.germ (U j.val) p hpJ t},
    isOpen_germ_agree_two F.presheaf (U i.val) (U j.val) s t⟩
  have hES : E ⊆ S := by
    intro p hp
    have hpI : p ∈ U i.val := subset_of_eq_iInter hE i.val hp
    have hpJ : p ∈ U j.val := subset_of_eq_iInter hE j.val hp
    have hval := congrArg (fun σ ↦ σ.1 (⟨⟨p, hp⟩, trivial⟩ : (⊤ : Opens E))) he
    change (⟨p, F.presheaf.germ (U i.val) p hpI s⟩ : GermPullback.Germs F.presheaf) =
      ⟨p, F.presheaf.germ (U j.val) p hpJ t⟩ at hval
    exact ⟨hpI, hpJ, SpectralSheafSystem.germs_snd_eq hval⟩
  obtain ⟨k, hk⟩ := exists_opens_le_of_iInter_subset U hqc hdir E hE S hES
  have hkI : U k ≤ U i.val := fun p hp ↦ (hk hp).1
  have hkJ : U k ≤ U j.val := fun p hp ↦ (hk hp).2.1
  let ik : intersectionIndex U := ⟨k⟩
  let fi : i ⟶ ik := homOfLE hkI
  let fj : j ⟶ ik := homOfLE hkJ
  apply Types.colimit_sound' fi fj
  apply TopCat.Presheaf.section_ext F (U k)
  intro p hp
  have hg := (hk hp).2.2
  change F.presheaf.germ (U i.val) p (hkI hp) s =
    F.presheaf.germ (U j.val) p (hkJ hp) t at hg
  change F.presheaf.germ (U k) p hp
      (F.presheaf.map (homOfLE hkI).op s) =
    F.presheaf.germ (U k) p hp
      (F.presheaf.map (homOfLE hkJ).op t)
  exact (F.presheaf.germ_res_apply (homOfLE hkI) p hp s).trans
    (hg.trans (F.presheaf.germ_res_apply (homOfLE hkJ) p hp t).symm)

/-- Sections on the intersection of a nonempty directed family of
quasi-compact opens of a quasi-separated scheme are the filtered colimit of
the sections on those opens.  The equivalence commutes with every canonical
map from a stage. -/
@[stacks 0APH]
theorem colimit_sections_equiv_sections_iInter
    {X : AlgebraicGeometry.Scheme.{u}} {I : Type u}
    [QuasiSeparatedSpace X] [Nonempty I]
    (F : X.toTopCat.Sheaf (Type u)) (U : I → Opens X)
    (hqc : ∀ i, IsCompact (U i : Set X))
    (hdir : ∀ i j, ∃ k, (U k : Set X) ⊆ U i ∩ U j) (E : Set X)
    (hE : E = ⋂ i, (U i : Set X)) :
    ∃ e : colimit (sectionsDiagram F U) ≃ sectionsOnSubset E F,
      ∀ (i : intersectionIndex U) (s : (sectionsDiagram F U).obj i),
        e (colimit.ι (sectionsDiagram F U) i s) =
          stageToSubset F U E
            (fun j ↦ by rw [hE]; exact Set.iInter_subset _ j) i s := by
  classical
  let hEi := subset_of_eq_iInter hE
  let g := Stacks.subsetInclusion (TopCat.of X) E
  let m := (pullbackToGerm g F).hom.app (op ⊤)
  have hm : Function.Injective m := by
    have : IsIso (pullbackToGerm g F) := Stacks.GermPullbackComparison.pullbackToGerm_isIso g F
    have : IsIso (pullbackToGerm g F).hom := by
      change IsIso ((TopCat.Sheaf.forget (Type u) (TopCat.of E)).map
        (pullbackToGerm g F))
      infer_instance
    have : IsIso m := NatIso.isIso_app_of_isIso _ _
    exact ((isIso_iff_bijective m).mp inferInstance).injective
  let φ := canonicalMap F U E hEi
  have hφinj : Function.Injective φ := by
    intro a b hab
    obtain ⟨i, s, ha⟩ := Types.jointly_surjective' a
    obtain ⟨j, t, hb⟩ := Types.jointly_surjective' b
    rw [← ha, ← hb] at hab ⊢
    have h := congrArg m hab
    rw [canonicalMap_ι, canonicalMap_ι,
      pullbackToGerm_stageToSubset, pullbackToGerm_stageToSubset] at h
    exact colimit_sections_eq_of_germ_eq F U hqc hdir E hE i j s t h
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨i, s, hs⟩ := germPullback_stage_surjective F U hqc hdir E hE (m y)
    refine ⟨colimit.ι (sectionsDiagram F U) (⟨i⟩ : intersectionIndex U) s, ?_⟩
    exact hm ((congrArg m (canonicalMap_ι F U E hEi ⟨i⟩ s)).trans
      ((pullbackToGerm_stageToSubset F U E hEi ⟨i⟩ s).trans hs))
  exact ⟨Equiv.ofBijective φ ⟨hφinj, hφsurj⟩, canonicalMap_ι F U E hEi⟩

end AlgebraicGeometry
