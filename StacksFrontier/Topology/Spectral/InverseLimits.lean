module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Spectral.ConstructibleProfinite
public import StacksFrontier.Topology.Limits.Defs
public import StacksCore.Topology.Category.TopCat.Limits.Cofiltered
public import Mathlib.Topology.Category.TopCat.Limits.Cofiltered

/-!
# Inverse limits of spectral spaces

Let `J` be a cofiltered category and `F : J ⥤ TopCat` a diagram in which every `F.obj j`
is a spectral space and every transition map `F.map a` is a spectral map. Then the inverse
limit `lim F` is a spectral space and every projection `lim F ⟶ F.obj j` is a spectral map.

The objects of `J` live in `Type v` and its morphisms in their own universe `Type v'`, with the
spaces in `TopCat.{max v u}`. The index hom universe does not enter the carrier of
`TopCat.limitCone`, which Mathlib states at `[Category.{w} J]` rather than at `SmallCategory J`,
so no universe of the spaces has to grow to accommodate a large index hom universe.

## Main definitions

* `SpectralDiagram`: a diagram of spectral spaces over a cofiltered index category whose
  transition maps are spectral.
* `SpectralDiagram.invLimit`: the inverse limit of such a diagram, as a topological space.
* `SpectralDiagram.proj`, `SpectralDiagram.projFun`: the projection to the `j`-th component,
  as a morphism of topological spaces and as a bare function.

## Main results

* `spectralDiagram_invLimit_spectralSpace`: the inverse limit is a spectral space.
* `spectralDiagram_proj_isSpectralMap`: every projection is a spectral map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe v u
universe v'

namespace TopCat

section CofilteredBasis

universe w

variable {J : Type v} [Category.{w} J] [IsCofiltered J] (F : J ⥤ TopCat.{max v u})
  (C : Cone F)

/-- The preimages of open sets in the factors form a topological basis of the limit of a cofiltered
system of topological spaces. This specialises `TopCat.isTopologicalBasis_cofiltered_limit` to the
case where the chosen basis of each factor is the collection of *all* open sets. -/
lemma isTopologicalBasis_preimage_open (hC : IsLimit C) :
    IsTopologicalBasis
      {U : Set C.pt | ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ U = C.π.app j ⁻¹' V} := by
  refine isTopologicalBasis_cofiltered_limit F C hC (fun _ => {U | IsOpen U})
    (fun _ => isTopologicalBasis_opens) (fun _ => isOpen_univ)
    (fun _ U1 U2 hU1 hU2 => hU1.inter hU2) ?_
  exact fun _ _ f _ hV => hV.preimage (F.map f).hom.continuous

end CofilteredBasis

end TopCat

/-- A copy of the topological space `X` carrying the constructible topology, with `Set X`
directly usable as a set of `WCT X`. -/
@[implicit_reducible]
private def WCT (X : Type*) [TopologicalSpace X] : Type _ := X

private instance instTopologicalSpaceWCT (X : Type*) [TopologicalSpace X] :
    TopologicalSpace (WCT X) :=
  constructibleTopology X

private instance compactSpaceWCT (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    CompactSpace (WCT X) :=
  have h : @CompactSpace X (constructibleTopology X) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology X) X _ (constructibleTopology X)
      _ (WithTopology.continuous_ofTopology (constructibleTopology X))
      compactSpace_withConstructibleTopology (WithTopology.ofTopology_surjective _)
  h

private instance t2SpaceWCT (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    T2Space (WCT X) :=
  have h : @T2Space X (constructibleTopology X) :=
    @T2Space.of_injective_continuous X (WithConstructibleTopology X) (constructibleTopology X) _ _
      (WithTopology.toTopology (constructibleTopology X)) (WithTopology.toTopology_injective _)
      (WithTopology.continuous_toTopology _)
  h

/-- A diagram of spectral spaces with spectral transition maps:
a functor `F : J ⥤ TopCat` from a cofiltered category `J` with objects in `Type v` and
morphisms in `Type v'` such that each `F.obj j` is a spectral space and each transition map
`F.map a` is spectral. -/
structure SpectralDiagram (J : Type v) [Category.{v'} J] [IsCofiltered J] where
  /-- The underlying diagram of topological spaces. -/
  F : J ⥤ TopCat.{max v u}
  /-- Each fibre of the diagram is a spectral topological space. -/
  isSpectralSpace : ∀ j : J, SpectralSpace (F.obj j)
  /-- Each transition map is a spectral map of topological spaces. -/
  isSpectralMap : ∀ {j i : J} (a : j ⟶ i), IsSpectralMap (F.map a)

namespace SpectralDiagram

variable {J : Type v} [Category.{v'} J] [IsCofiltered J] (D : SpectralDiagram.{v, u} J)

attribute [local instance] SpectralDiagram.isSpectralSpace

/-- The inverse limit of the diagram of topological spaces, as a topological space. -/
@[implicit_reducible]
noncomputable def invLimit : TopCat := Limits.limit D.F

/-- The projection from the inverse limit to the `j`-th component, as a continuous map. -/
noncomputable def proj (j : J) : D.invLimit ⟶ D.F.obj j := Limits.limit.π D.F j

/-- The projection from the inverse limit to the `j`-th component, as a bare function
on underlying spaces. -/
noncomputable def projFun (j : J) : D.invLimit → D.F.obj j :=
  ConcreteCategory.hom (D.proj j)

/-- `D.proj j` is the limit projection. -/
lemma proj_eq (j : J) : D.proj j = Limits.limit.π D.F j := rfl

/-- `D.projFun j` is the function underlying `D.proj j`. -/
lemma projFun_apply (j : J) (x : D.invLimit) : D.projFun j x = D.proj j x := rfl

/-! ### Basic facts about projections -/

/-- The projection from the inverse limit to the `j`-th component is continuous. -/
lemma projFun_continuous (j : J) : Continuous (D.projFun j) :=
  (D.proj j).hom.continuous

/-- The projections are compatible with the transition maps: for `a : j ⟶ i`, the `i`-th
coordinate of a point of the inverse limit is the image of its `j`-th coordinate under
`D.F.map a`. -/
lemma projFun_comp {j i : J} (a : j ⟶ i) (x : D.invLimit) :
    D.projFun i x = (ConcreteCategory.hom (D.F.map a)) (D.projFun j x) := by
  rw [projFun_apply, projFun_apply, proj_eq, proj_eq]
  exact (Limits.limit.w_apply D.F a x).symm

/-- A point of the inverse limit is determined by its coordinates. -/
lemma projFun_injective_pi (x y : D.invLimit)
    (h : ∀ j : J, D.projFun j x = D.projFun j y) : x = y :=
  Limits.Concrete.limit_ext D.F x y h

/-- The closure of the image of an irreducible subset of the inverse limit under the `j`-th
projection is irreducible. -/
lemma closure_image_isIrreducible (j : J) {C : Set D.invLimit}
    (hC : IsIrreducible C) : IsIrreducible (closure (D.projFun j '' C)) :=
  (hC.image (D.projFun j) (D.projFun_continuous j).continuousOn).closure

/-! ### Patch product setup -/

/-- The carrier of the inverse limit as a subset of the product. -/
@[implicit_reducible]
private def compatible : Set (∀ j : J, D.F.obj j) :=
  { u | ∀ {i j : J} (a : i ⟶ j), D.F.map a (u i) = u j }

/-- A point of `D.invLimit` packaged as a compatible family in the product. -/
private noncomputable def toPi : D.invLimit → ∀ j : J, D.F.obj j := fun x j => D.projFun j x

private lemma toPi_apply (x : D.invLimit) (j : J) : D.toPi x j = D.projFun j x := rfl

private lemma toPi_mem_compatible (x : D.invLimit) : D.toPi x ∈ D.compatible := by
  intro i j a
  exact (D.projFun_comp a x).symm

private lemma toPi_injective : Function.Injective D.toPi := fun x y h =>
  D.projFun_injective_pi x y (fun j => congrFun h j)

/-! ### A spectral map is continuous between constructible topologies -/

/-- A spectral map `f : X → Y` yields a continuous map of constructible topologies. -/
@[ega "IV 1.9.14" "(iii)"]
private lemma continuous_patchHom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) :
    Continuous (X := WCT X) (Y := WCT Y) f := by
  rw [show instTopologicalSpaceWCT Y =
      TopologicalSpace.generateFrom (constructibleTopologySubbasis Y) from rfl,
    continuous_generateFrom_iff]
  intro s hs
  rcases hs with ⟨hsOpen, hsCp⟩ | ⟨hsCl, hsCp⟩
  · -- s open + compact in Y. Preimage open + compact in X (via spectral `f`).
    exact (hf.isCompact_preimage_of_isOpen hsOpen hsCp).isOpen_constructibleTopology_of_isOpen
      (hsOpen.preimage hf.continuous)
  · -- s closed in Y with sᶜ compact. Preimage closed; preimage of sᶜ is compact.
    have hsCo : IsOpen (X := Y) sᶜ := hsCl.isOpen_compl
    have hpre_cp_co : IsCompact (f ⁻¹' sᶜ) := hf.isCompact_preimage_of_isOpen hsCo hsCp
    have hpre_cl : IsClosed (f ⁻¹' s) := hsCl.preimage hf.continuous
    have hpre_compl_cp : IsCompact (f ⁻¹' s)ᶜ := by
      rwa [Set.preimage_compl] at hpre_cp_co
    exact hpre_compl_cp.isOpen_constructibleTopology_of_isClosed hpre_cl

/-! ### Patch product is compact T2 and the compatibility set is closed -/

private instance compactSpace_pi_patch :
    CompactSpace (∀ j : J, WCT (D.F.obj j)) := by
  have : ∀ j, CompactSpace (WCT (D.F.obj j)) := fun j => inferInstance
  infer_instance

private instance t2Space_pi_patch :
    T2Space (∀ j : J, WCT (D.F.obj j)) := by
  have : ∀ j, T2Space (WCT (D.F.obj j)) := fun j => inferInstance
  infer_instance

private lemma compatible_isClosed_patch :
    IsClosed (X := ∀ j : J, WCT (D.F.obj j))
      (D.compatible : Set (∀ j : J, D.F.obj j)) := by
  -- compatible = ⋂ (i, j, a : i ⟶ j) { u | F.map a (u i) = u j }.
  have hrew : (D.compatible : Set (∀ j : J, D.F.obj j)) =
      ⋂ (p : Σ (ij : J × J), ij.1 ⟶ ij.2),
        { u : ∀ j : J, D.F.obj j | D.F.map p.snd (u p.fst.fst) = u p.fst.snd } := by
    ext u
    refine ⟨fun hu => ?_, fun hu i j a => ?_⟩
    · rintro _ ⟨p, rfl⟩
      exact hu p.2
    · exact Set.mem_iInter.mp hu ⟨(i, j), a⟩
  rw [hrew]
  refine isClosed_iInter (X := ∀ j : J, WCT (D.F.obj j)) ?_
  rintro ⟨⟨i, j⟩, a⟩
  have : T2Space (WCT (D.F.obj j)) := inferInstance
  -- f := fun u ↦ F.map a (u i) and g := fun u ↦ u j, both PatchProduct → patch(F.obj j).
  set f : (∀ j : J, WCT (D.F.obj j)) → WCT (D.F.obj j)
    := fun u => (D.F.map a) ((u i : WCT (D.F.obj i)) : D.F.obj i)
  set g : (∀ j : J, WCT (D.F.obj j)) → WCT (D.F.obj j)
    := fun u => u j
  have hfst : Continuous f := by
    have h1 : Continuous (X := ∀ j : J, WCT (D.F.obj j))
        (Y := WCT (D.F.obj i))
        (fun u : (∀ j : J, WCT (D.F.obj j)) => u i) :=
      continuous_apply i
    exact (continuous_patchHom (D.isSpectralMap a)).comp h1
  have hsnd : Continuous g := continuous_apply j
  have hclosed : IsClosed { u | f u = g u } := isClosed_eq hfst hsnd
  exact hclosed

private lemma compatible_isCompact_patch :
    IsCompact (X := ∀ j : J, WCT (D.F.obj j))
      (D.compatible : Set (∀ j : J, D.F.obj j)) :=
  D.compatible_isClosed_patch.isCompact

/-! ### Surjectivity of `toPi` onto the compatibility set -/

private lemma toPi_surjOn_compatible :
    ∀ u ∈ D.compatible, ∃ x : D.invLimit, D.toPi x = u := by
  intro u hu
  let e : D.invLimit ≅ (TopCat.limitCone D.F).pt :=
    (limit.isLimit D.F).conePointUniqueUpToIso (TopCat.limitConeIsLimit D.F)
  let v : (TopCat.limitCone D.F).pt := ⟨u, fun {i j} a => hu a⟩
  refine ⟨e.inv v, ?_⟩
  funext j
  have hcommute : D.proj j = e.hom ≫ (TopCat.limitCone D.F).π.app j :=
    ((limit.isLimit D.F).conePointUniqueUpToIso_hom_comp (TopCat.limitConeIsLimit D.F) j).symm
  have heinv : e.hom (e.inv v) = v := by simp
  simp only [toPi]
  rw [projFun_apply, hcommute, ConcreteCategory.comp_apply, heinv]
  exact TopCat.limitCone_π_app_apply D.F j v

/-! ### Compactness of `D.invLimit` via the patch-limit → invLimit map -/

/-- The patch limit subspace, equipped with the patch product subspace topology. -/
@[implicit_reducible]
private noncomputable def PatchLimit : Type _ :=
  { u : ∀ j : J, WCT (D.F.obj j) // u ∈ D.compatible }

private noncomputable instance : TopologicalSpace D.PatchLimit := by
  unfold PatchLimit
  infer_instance

private instance instCompactSpacePatchLimit : CompactSpace D.PatchLimit := by
  unfold PatchLimit
  exact isCompact_iff_compactSpace.mp D.compatible_isCompact_patch

/-- The set-theoretic map from the patch limit to `D.invLimit`. -/
private noncomputable def patchToInvLimit : D.PatchLimit → D.invLimit := fun v =>
  Classical.choose (D.toPi_surjOn_compatible v.val v.property)

private lemma toPi_patchToInvLimit (v : D.PatchLimit) :
    D.toPi (D.patchToInvLimit v) = v.val :=
  Classical.choose_spec (D.toPi_surjOn_compatible v.val v.property)

private lemma projFun_patchToInvLimit (v : D.PatchLimit) (j : J) :
    D.projFun j (D.patchToInvLimit v) = v.val j :=
  congrFun (D.toPi_patchToInvLimit v) j

private lemma patchToInvLimit_surjective : Function.Surjective D.patchToInvLimit := fun x =>
  ⟨⟨D.toPi x, D.toPi_mem_compatible x⟩,
    D.toPi_injective (D.toPi_patchToInvLimit ⟨D.toPi x, D.toPi_mem_compatible x⟩)⟩

/-- For prespectral `Y`, the identity from patch to original is continuous because
every original-open is constructible-open (every open is a union of qc-opens). -/
@[ega "IV 1.9.14" "(i)"]
private lemma continuous_id_of_patchTopology {Y : Type*} [TopologicalSpace Y]
    [PrespectralSpace Y] :
    Continuous (X := WCT Y) (Y := Y) id := by
  refine continuous_def.2 fun U hU => ?_
  -- U is open in Y. We want: id ⁻¹' U = U is open in `constructibleTopology Y`.
  rw [Set.preimage_id]
  -- Every open in `Y` is a union of qc-opens (prespectral basis), each in the subbasis.
  obtain ⟨B, hBsub, hBeq⟩ := PrespectralSpace.isTopologicalBasis.open_eq_sUnion hU
  rw [hBeq]
  refine @isOpen_sUnion Y (constructibleTopology Y) B fun V hV => ?_
  obtain ⟨hVopen, hVcomp⟩ := hBsub hV
  exact hVcomp.isOpen_constructibleTopology_of_isOpen hVopen

/-- `patchToInvLimit` is continuous, by checking that each `projFun j ∘ patchToInvLimit`
is continuous (the topology on `invLimit` is the infimum of induced topologies). -/
private lemma continuous_patchToInvLimit : Continuous D.patchToInvLimit := by
  have h_top : (D.invLimit : TopCat).str =
      ⨅ j : J, (D.F.obj j).str.induced (D.projFun j) :=
    TopCat.limit_topology D.F
  rw [continuous_iff_le_induced, h_top]
  -- Reduce to checking each `induced (projFun j) ...` is ≥ induced patchToInvLimit ....
  simp only [induced_iInf]
  refine le_iInf fun j => ?_
  -- Goal: induced patchToInvLimit (induced (projFun j) (F.obj j).str) ≤ PatchLimit topology
  -- LHS = induced (projFun j ∘ patchToInvLimit) (F.obj j).str.
  rw [induced_compose, ← continuous_iff_le_induced]
  -- Goal: Continuous (D.projFun j ∘ D.patchToInvLimit) : PatchLimit → F.obj j.
  have heq : (D.projFun j ∘ D.patchToInvLimit) = fun v : D.PatchLimit => (v.val j : D.F.obj j) := by
    funext v
    exact D.projFun_patchToInvLimit v j
  rw [heq]
  -- factor: PatchLimit → ∏ patch → patch (F.obj j) → F.obj j
  exact continuous_id_of_patchTopology.comp ((continuous_apply j).comp continuous_subtype_val)

/-- The inverse limit of a cofiltered diagram of spectral spaces is compact. -/
instance invLimit_compactSpace : CompactSpace D.invLimit := by
  rw [← isCompact_univ_iff, ← Set.image_univ_of_surjective D.patchToInvLimit_surjective]
  exact CompactSpace.isCompact_univ.image D.continuous_patchToInvLimit

/-! ### T0Space -/

/-- The inverse limit of a cofiltered diagram of spectral spaces is a T0 space. -/
instance invLimit_t0Space : T0Space D.invLimit :=
  ⟨fun x y h => D.projFun_injective_pi x y fun j => (h.map (D.projFun_continuous j)).eq⟩

/-! ### Sobriety -/

/-- For each `j`, the generic point of `closure (projFun j '' C)`. -/
private noncomputable def genericPointFamily {C : Set D.invLimit}
    (hC : IsIrreducible C) (j : J) : D.F.obj j :=
  have : QuasiSober (D.F.obj j) := inferInstance
  (D.closure_image_isIrreducible j hC).genericPoint

private lemma genericPointFamily_isGenericPoint {C : Set D.invLimit}
    (hC : IsIrreducible C) (j : J) :
    IsGenericPoint (D.genericPointFamily hC j) (closure (D.projFun j '' C)) := by
  have : QuasiSober (D.F.obj j) := inferInstance
  have := (D.closure_image_isIrreducible j hC).isGenericPoint_genericPoint_closure
  unfold genericPointFamily
  simpa [closure_closure] using this

private lemma genericPointFamily_compatible {C : Set D.invLimit}
    (hC : IsIrreducible C) : D.genericPointFamily hC ∈ D.compatible := by
  intro i j a
  have hi := D.genericPointFamily_isGenericPoint hC i
  have hj := D.genericPointFamily_isGenericPoint hC j
  have hclos_eq : closure ((D.F.map a) '' (closure (D.projFun i '' C))) =
      closure (D.projFun j '' C) := by
    rw [closure_image_closure (D.F.map a).hom.continuous]
    congr 1
    rw [Set.image_image]
    congr 1
    funext x
    exact (D.projFun_comp a x).symm
  have hi_image : IsGenericPoint ((D.F.map a) (D.genericPointFamily hC i))
      (closure ((D.F.map a) '' (closure (D.projFun i '' C)))) :=
    hi.image (D.F.map a).hom.continuous
  rw [hclos_eq] at hi_image
  exact hi_image.eq hj

private noncomputable def genericPoint {C : Set D.invLimit} (hC : IsIrreducible C) :
    D.invLimit :=
  Classical.choose
    (D.toPi_surjOn_compatible (D.genericPointFamily hC) (D.genericPointFamily_compatible hC))

private lemma projFun_genericPoint {C : Set D.invLimit} (hC : IsIrreducible C) (j : J) :
    D.projFun j (D.genericPoint hC) = D.genericPointFamily hC j :=
  congrFun (Classical.choose_spec
    (D.toPi_surjOn_compatible (D.genericPointFamily hC) (D.genericPointFamily_compatible hC))) j

/-- The basis of opens for the inverse limit: this is
`TopCat.isTopologicalBasis_preimage_open` for the limit cone of `D.F`, whose point is
`D.invLimit` and whose projections are the `D.proj j`. -/
private lemma isTopologicalBasis_preimage_open :
    IsTopologicalBasis
      { U : Set D.invLimit |
        ∃ (j : J) (V : Set (D.F.obj j)), IsOpen V ∧ U = D.proj j ⁻¹' V } :=
  TopCat.isTopologicalBasis_preimage_open D.F (Limits.limit.cone D.F)
    (Limits.limit.isLimit D.F)

/-- The constructed generic point of an irreducible closed set `C` lies in `C`: a basic open
neighbourhood of it is `proj j ⁻¹' V`, and `genericPointFamily hC j` being generic for
`closure (projFun j '' C)` forces `V` to meet `projFun j '' C`. -/
private lemma genericPoint_mem {C : Set D.invLimit}
    (hC : IsIrreducible C) (hCcl : IsClosed C) : D.genericPoint hC ∈ C := by
  suffices h_mem_cl : D.genericPoint hC ∈ closure C by
    rwa [hCcl.closure_eq] at h_mem_cl
  rw [mem_closure_iff]
  intro U hUopen hxU
  obtain ⟨_, ⟨j, V, hVopen, rfl⟩, hxb, hbU⟩ :=
    D.isTopologicalBasis_preimage_open.exists_subset_of_mem_open hxU hUopen
  have hxV : D.projFun j (D.genericPoint hC) ∈ V := hxb
  rw [D.projFun_genericPoint hC j] at hxV
  have hpf_meets : ((D.projFun j '' C) ∩ V).Nonempty := by
    rw [← closure_inter_open_nonempty_iff hVopen]
    exact ((D.genericPointFamily_isGenericPoint hC j).mem_open_set_iff hVopen).mp hxV
  obtain ⟨_, ⟨c, hcC, rfl⟩, hyV⟩ := hpf_meets
  exact ⟨c, hbU hyV, hcC⟩

/-- An irreducible closed set is contained in the closure of its constructed generic point:
a basic open neighbourhood `proj j ⁻¹' W` of a point of `C` meets `projFun j '' C`, hence
contains the generic point of `closure (projFun j '' C)`. Closedness of `C` is not needed. -/
private lemma subset_closure_genericPoint {C : Set D.invLimit} (hC : IsIrreducible C) :
    C ⊆ closure {D.genericPoint hC} := by
  intro y hyC
  rw [mem_closure_iff]
  intro V hVopen hyV
  obtain ⟨_, ⟨j, W, hWopen, rfl⟩, hyb, hbV⟩ :=
    D.isTopologicalBasis_preimage_open.exists_subset_of_mem_open hyV hVopen
  have hyW : D.projFun j y ∈ W := hyb
  refine ⟨D.genericPoint hC, hbV ?_, rfl⟩
  rw [Set.mem_preimage, ← projFun_apply, D.projFun_genericPoint hC j]
  exact ((D.genericPointFamily_isGenericPoint hC j).mem_open_set_iff hWopen).mpr
    ⟨D.projFun j y, subset_closure ⟨y, hyC, rfl⟩, hyW⟩

/-- Every irreducible closed subset has the constructed generic point. -/
private lemma isGenericPoint_genericPoint {C : Set D.invLimit}
    (hC : IsIrreducible C) (hCcl : IsClosed C) :
    IsGenericPoint (D.genericPoint hC) C :=
  Set.eq_of_subset_of_subset
    (hCcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (D.genericPoint_mem hC hCcl)))
    (D.subset_closure_genericPoint hC)

/-- The inverse limit of a cofiltered diagram of spectral spaces is quasi-sober: every
irreducible closed subset has a generic point. -/
instance invLimit_quasiSober : QuasiSober D.invLimit where
  sober hC hCcl := ⟨D.genericPoint hC, D.isGenericPoint_genericPoint hC hCcl⟩

/-! ### Quasi-compact opens in the inverse limit -/

/-- `U` qc-open in `F.obj j` ⇒ `projFun j ⁻¹' U` qc in `D.invLimit`. -/
private lemma isCompact_projFun_preimage (j : J) {U : Set (D.F.obj j)}
    (hUopen : IsOpen U) (hUcomp : IsCompact U) :
    IsCompact (D.projFun j ⁻¹' U) := by
  -- Patch view: `U` is patch-closed, since `Uᶜ` is closed in the original topology and
  -- `(Uᶜ)ᶜ = U` is qc, so `Uᶜ` is patch-open.
  have hUclosed_patch : IsClosed (X := WCT (D.F.obj j)) U :=
    isOpen_compl_iff.mp <|
      (show IsCompact Uᶜᶜ by simpa using hUcomp).isOpen_constructibleTopology_of_isClosed
        hUopen.isClosed_compl
  -- S := { v : PatchLimit | v.val j ∈ U } is closed in the patch limit.
  let S : Set D.PatchLimit := { v | (v.val j : D.F.obj j) ∈ U }
  have hSclosed : IsClosed S :=
    hUclosed_patch.preimage ((continuous_apply j).comp continuous_subtype_val)
  -- patchToInvLimit '' S = projFun j ⁻¹' U.
  have himg : D.patchToInvLimit '' S = D.projFun j ⁻¹' U := by
    refine Set.eq_of_subset_of_subset ?_ fun x hxU => ?_
    · rintro _ ⟨v, hvS, rfl⟩
      rw [Set.mem_preimage, D.projFun_patchToInvLimit v j]
      exact hvS
    · obtain ⟨v, rfl⟩ := D.patchToInvLimit_surjective x
      exact ⟨v, by rwa [Set.mem_preimage, D.projFun_patchToInvLimit v j] at hxU, rfl⟩
  rw [← himg]
  exact hSclosed.isCompact.image D.continuous_patchToInvLimit

/-! ### Basis of qc-opens and prespectral / quasi-separated -/

/-- The qc-open preimages from factors form a topological basis. -/
private lemma isTopologicalBasis_qc_opens :
    IsTopologicalBasis
      { S : Set D.invLimit | ∃ (j : J) (U : Set (D.F.obj j)),
          IsOpen U ∧ IsCompact U ∧ S = D.projFun j ⁻¹' U } := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro S ⟨j, U, hUo, _, rfl⟩
    exact hUo.preimage (D.projFun_continuous j)
  · intro x V hxV hVopen
    obtain ⟨_, ⟨j, W, hWopen, rfl⟩, hxb, hbV⟩ :=
      D.isTopologicalBasis_preimage_open.exists_subset_of_mem_open hxV hVopen
    have hxjW : D.projFun j x ∈ W := hxb
    obtain ⟨K, ⟨hKopen, hKcomp⟩, hxK, hKW⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxjW hWopen
    exact ⟨D.projFun j ⁻¹' K, ⟨j, K, hKopen, hKcomp, rfl⟩, hxK, fun y hyK => hbV (hKW hyK)⟩

/-- The inverse limit of a cofiltered diagram of spectral spaces is prespectral: its
quasi-compact opens form a basis of the topology. -/
instance invLimit_prespectralSpace : PrespectralSpace D.invLimit := by
  refine PrespectralSpace.of_isTopologicalBasis D.isTopologicalBasis_qc_opens ?_
  rintro _ ⟨j, U, hUo, hUc, rfl⟩
  exact D.isCompact_projFun_preimage j hUo hUc

/-- The inverse limit of a cofiltered diagram of spectral spaces is quasi-separated: the
intersection of two quasi-compact opens is quasi-compact. -/
instance invLimit_quasiSeparatedSpace : QuasiSeparatedSpace D.invLimit := by
  -- Use that the qc-open basis is closed under intersection.
  let b : (Σ j : J, { U : Set (D.F.obj j) // IsOpen U ∧ IsCompact U }) → Set D.invLimit :=
    fun p => D.projFun p.1 ⁻¹' p.2.val
  have hb_basis : IsTopologicalBasis (Set.range b) := by
    convert D.isTopologicalBasis_qc_opens using 1
    exact Set.ext fun S =>
      ⟨fun ⟨⟨j, U, hUo, hUc⟩, hU⟩ => ⟨j, U, hUo, hUc, hU.symm⟩,
        fun ⟨j, U, hUo, hUc, hU⟩ => ⟨⟨j, U, hUo, hUc⟩, hU.symm⟩⟩
  refine QuasiSeparatedSpace.of_isTopologicalBasis hb_basis ?_
  intro p q
  classical
  obtain ⟨hpopen, hpcomp⟩ := p.2.property
  obtain ⟨hqopen, hqcomp⟩ := q.2.property
  -- Cofiltered: choose k with maps a : k → p.1 and c : k → q.1.
  obtain ⟨k, hk⟩ : ∃ k : J, ∀ {X : J}, X ∈ ({p.1, q.1} : Finset J) → Nonempty (k ⟶ X) :=
    IsCofiltered.inf_objs_exists ({p.1, q.1} : Finset J)
  obtain ⟨a⟩ : Nonempty (k ⟶ p.1) := hk (by simp)
  obtain ⟨c⟩ : Nonempty (k ⟶ q.1) := hk (by simp)
  have hrew : b p ∩ b q =
      D.projFun k ⁻¹' ((D.F.map a) ⁻¹' p.2.val ∩ (D.F.map c) ⁻¹' q.2.val) := by
    simp only [b]
    rw [Set.preimage_inter]
    congr 1
    · ext x
      rw [Set.mem_preimage, Set.mem_preimage, Set.mem_preimage, D.projFun_comp a x]
    · ext x
      rw [Set.mem_preimage, Set.mem_preimage, Set.mem_preimage, D.projFun_comp c x]
  rw [hrew]
  have h1o : IsOpen ((D.F.map a) ⁻¹' p.2.val) := hpopen.preimage (D.F.map a).hom.continuous
  have h2o : IsOpen ((D.F.map c) ⁻¹' q.2.val) := hqopen.preimage (D.F.map c).hom.continuous
  exact D.isCompact_projFun_preimage k (h1o.inter h2o)
    (((D.isSpectralMap a).isCompact_preimage_of_isOpen hpopen hpcomp).inter_of_isOpen
      ((D.isSpectralMap c).isCompact_preimage_of_isOpen hqopen hqcomp) h1o h2o)

/-! ### Main: `invLimit` is spectral, and each projection is spectral -/

/-- The inverse limit of a cofiltered diagram of spectral spaces with spectral transition maps
is a spectral space. -/
instance invLimit_spectralSpace_aux : SpectralSpace D.invLimit where

end SpectralDiagram

/-- **Stacks 0A2Z** (inverse limit is spectral).
The inverse limit of a cofiltered diagram of spectral spaces with spectral transition maps is
a spectral topological space. -/
@[stacks 0A2Z "inverse limit is spectral"]
theorem spectralDiagram_invLimit_spectralSpace
    {J : Type v} [Category.{v'} J] [IsCofiltered J] (D : SpectralDiagram.{v, u} J) :
    SpectralSpace D.invLimit :=
  D.invLimit_spectralSpace_aux

/-- **Stacks 0A2Z** (projections are spectral).
Each projection from the inverse limit of a cofiltered diagram of spectral spaces to a
component of the diagram is a spectral map. -/
@[stacks 0A2Z "projections are spectral"]
theorem spectralDiagram_proj_isSpectralMap
    {J : Type v} [Category.{v'} J] [IsCofiltered J] (D : SpectralDiagram.{v, u} J) (j : J) :
    IsSpectralMap (D.projFun j) where
  toContinuous := D.projFun_continuous j
  isCompact_preimage_of_isOpen _ hUopen hUcomp :=
    D.isCompact_projFun_preimage j hUopen hUcomp

