module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Prespectrality and spectrality along a continuous open surjection

Prespectrality — the condition that the quasi-compact open subsets form a topological basis —
descends along a continuous open surjection. If `f : X → Y` is continuous, open and surjective
and `X` is prespectral, then the images of the quasi-compact opens of `X` are quasi-compact
opens of `Y` which form a basis of `Y`.

## Main results

* `prespectralSpace_of_isOpenMap_surjective`: the target of a continuous open surjection from
  a prespectral space is prespectral.
* `spectralSpace_of_isOpenMap_surjective`: the Kolmogorov target of a continuous open
  surjection from a spectral space is spectral, provided the saturation of every quasi-compact
  open of the source is quasi-compact.

## Implementation notes

Only the images of the quasi-compact opens of the source are used as a basis; they are open
because `f` is open and quasi-compact because `f` is continuous, and they are a basis because
a point of the target lifts and its lift has a quasi-compact open neighbourhood inside the
preimage of any given open set.

The companion statements for the remaining conditions in the definition of a spectral space do
*not* descend along an arbitrary continuous open surjection. They do descend once the
saturation `f ⁻¹' (f '' V)` of every quasi-compact open `V` of the source is quasi-compact,
that is once `f` is quasi-compact; together with the Kolmogorov property of the target, which
has to be supplied, this gives `spectralSpace_of_isOpenMap_surjective`. Quasi-separatedness is
then the image of an intersection of two quasi-compact opens of the source, and quasi-sobriety
is the compactness of the source in its constructible topology (Stacks 0901): the preimages of
an irreducible closed set and of the quasi-compact opens meeting it are closed in that topology
and have the finite intersection property, and the image of a point of their intersection is a
generic point.
-/

@[expose] public section

open TopologicalSpace Topology

/-- The target of a continuous open surjection from a prespectral space is prespectral: the
images of the quasi-compact opens of the source are quasi-compact opens forming a basis. -/
theorem prespectralSpace_of_isOpenMap_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PrespectralSpace X] {f : X → Y}
    (hf : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) :
    PrespectralSpace Y := by
  refine PrespectralSpace.of_isTopologicalBasis
    (B := (fun V : Set X ↦ f '' V) '' {V : Set X | IsOpen V ∧ IsCompact V}) ?_ ?_
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨V, ⟨hVopen, -⟩, rfl⟩
      exact hopen V hVopen
    · intro y W hy hW
      obtain ⟨x, rfl⟩ := hsurj y
      obtain ⟨V, ⟨hVopen, hVcompact⟩, hxV, hVW⟩ :=
        PrespectralSpace.isTopologicalBasis (X := X) |>.exists_subset_of_mem_open hy
          (hW.preimage hf)
      exact ⟨f '' V, ⟨V, ⟨hVopen, hVcompact⟩, rfl⟩, ⟨x, hxV, rfl⟩,
        Set.image_subset_iff.mpr hVW⟩
  · rintro _ ⟨V, ⟨-, hVcompact⟩, rfl⟩
    exact hVcompact.image hf

/-- **Spectrality along a quasi-compact continuous open surjection.** Let `f : X → Y` be a
continuous open surjection from a spectral space onto a Kolmogorov space such that the saturation
`f ⁻¹' (f '' V)` of every quasi-compact open `V` of `X` is quasi-compact. Then `Y` is spectral. -/
theorem spectralSpace_of_isOpenMap_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [SpectralSpace X] [T0Space Y] {f : X → Y}
    (hf : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f)
    (hsat : ∀ V : Set X, IsOpen V → IsCompact V → IsCompact (f ⁻¹' (f '' V))) :
    SpectralSpace Y := by
  have : CompactSpace Y := hsurj.compactSpace hf
  have : PrespectralSpace Y := prespectralSpace_of_isOpenMap_surjective hf hopen hsurj
  have hpre : ∀ W : Set Y, IsOpen W → IsCompact W → IsCompact (f ⁻¹' W) := by
    intro W hWo hWc
    obtain ⟨V, hVc, hVW⟩ := hopen.exists_opens_image_eq_of_prespectralSpace hf
      (hsurj.range_eq ▸ Set.subset_univ W) hWo hWc
    exact hVW ▸ hsat V V.2 hVc
  have : QuasiSeparatedSpace Y := by
    refine ⟨fun U V hUo hUc hVo hVc => ?_⟩
    rw [← Set.image_preimage_eq (U ∩ V) hsurj, Set.preimage_inter]
    exact (QuasiSeparatedSpace.inter_isCompact _ _ (hUo.preimage hf) (hpre U hUo hUc)
      (hVo.preimage hf) (hpre V hVo hVc)).image hf
  have : QuasiSober Y := by
    refine ⟨fun {T} hT hTc => ?_⟩
    let I := {W : Set Y // IsOpen W ∧ IsCompact W ∧ (T ∩ W).Nonempty}
    let t : I → Set (WithConstructibleTopology X) :=
      fun W => WithTopology.ofTopology ⁻¹' (f ⁻¹' T ∩ f ⁻¹' W.1)
    have hopenC : ∀ O : Set X, IsOpen O → IsOpen[constructibleTopology X] O := by
      intro O hO
      obtain ⟨B, hB, rfl⟩ := (PrespectralSpace.isTopologicalBasis (X := X)).open_eq_sUnion hO
      exact @isOpen_sUnion _ (constructibleTopology X) _
        fun s hs => (hB hs).2.isOpen_constructibleTopology_of_isOpen (hB hs).1
    have htc : ∀ W : I, IsClosed (t W) := by
      intro W
      rw [WithConstructibleTopology.isClosed_iff]
      have hA : IsOpen[constructibleTopology X] (f ⁻¹' T)ᶜ :=
        hopenC _ (hTc.preimage hf).isOpen_compl
      have hB : IsOpen[constructibleTopology X] (f ⁻¹' W.1)ᶜ :=
        IsCompact.isOpen_constructibleTopology_of_isClosed
          (by simpa only [compl_compl] using hpre W.1 W.2.1 W.2.2.1)
          (W.2.1.preimage hf).isClosed_compl
      let := constructibleTopology X
      exact (isOpen_compl_iff.mp hA).inter (isOpen_compl_iff.mp hB)
    have hfin : ∀ u : Finset I, (Set.univ ∩ ⋂ W ∈ u, t W).Nonempty := by
      intro u
      obtain ⟨y, hyT, hyW⟩ := (isIrreducible_iff_sInter.mp hT) (u.image Subtype.val)
        (Finset.forall_mem_image.2 fun W _ => W.2.1)
        (Finset.forall_mem_image.2 fun W _ => W.2.2.2)
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨WithTopology.toTopology _ x, Set.mem_univ _, Set.mem_iInter₂.mpr fun W hW =>
        ⟨hyT, Set.mem_sInter.mp hyW W.1 (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hW))⟩⟩
    obtain ⟨x, -, hx⟩ := isCompact_univ.inter_iInter_nonempty t htc hfin
    have hxW : ∀ W : I, f x.ofTopology ∈ W.1 := fun W => (Set.mem_iInter.mp hx W).2
    have hTne : (T ∩ Set.univ).Nonempty := by simpa using hT.nonempty
    have hxT : f x.ofTopology ∈ T :=
      (Set.mem_iInter.mp hx ⟨Set.univ, isOpen_univ, isCompact_univ, hTne⟩).1
    refine ⟨f x.ofTopology, subset_antisymm (closure_minimal (Set.singleton_subset_iff.mpr hxT) hTc)
      fun y hy => mem_closure_iff.mpr fun O hO hyO => ?_⟩
    obtain ⟨W, ⟨hWo, hWc⟩, hyW, hWO⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open hyO hO
    exact ⟨f x.ofTopology, hWO (hxW ⟨W, hWo, hWc, y, hy, hyW⟩), rfl⟩
  exact SpectralSpace.mk

end
