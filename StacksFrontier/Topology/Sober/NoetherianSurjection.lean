module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Sober
public import StacksFrontier.Topology.Noetherian.Defs

/-!
# Quasi-sobriety of the image of a (locally) Noetherian quasi-sober space

A continuous surjection out of a Noetherian quasi-sober space has quasi-sober target: the
preimage of an irreducible closed subset `T` is a finite union of irreducible closed subsets,
one of whose images is dense in `T`, and the image of a generic point of that subset is a
generic point of `T`. Weakening "Noetherian" to "locally Noetherian" costs the hypothesis that
the map be open, since the conclusion is then obtained on an open cover of the target by images
of Noetherian open subsets of the source.

## Main results

* `quasiSober_of_noetherianSpace_surjective`: a continuous surjection out of a Noetherian
  quasi-sober space has quasi-sober target.
* `quasiSober_of_isLocallyNoetherianSpace_isOpenMap_surjective`: a continuous open surjection
  out of a locally Noetherian quasi-sober space has quasi-sober target.
-/

@[expose] public section

open TopologicalSpace

/-- A continuous surjection out of a Noetherian quasi-sober space has quasi-sober target.

An irreducible closed `T` in the target has closed preimage, which is a finite union of
irreducible closed subsets `Z`; irreducibility of `T` puts it inside `closure (f '' Z)` for one
of them, and that closure is contained in `T`, so a generic point of `Z` maps to a generic point
of `T`. -/
theorem quasiSober_of_noetherianSpace_surjective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [NoetherianSpace X] [QuasiSober X] {f : X → Y} (hf : Continuous f)
    (hsurj : Function.Surjective f) : QuasiSober Y where
  sober {T} hT hTcl := by
    classical
    obtain ⟨S, hSfin, hScl, hSirr, hSeq⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible (hTcl.preimage hf)
    have hmemS {x : X} {Z : Set X} (hZ : Z ∈ S) (hxZ : x ∈ Z) : f x ∈ T :=
      show x ∈ f ⁻¹' T from hSeq ▸ Set.mem_sUnion.2 ⟨Z, hZ, hxZ⟩
    have himg : ((fun Z : Set X => closure (f '' Z)) '' S).Finite := hSfin.image _
    have hcov : T ⊆ ⋃₀ (himg.toFinset : Set (Set Y)) := by
      intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.1 (hSeq ▸ hy : x ∈ ⋃₀ S)
      refine ⟨closure (f '' Z), ?_, subset_closure ⟨x, hxZ, rfl⟩⟩
      rw [Finset.mem_coe, himg.mem_toFinset]
      exact ⟨Z, hZ, rfl⟩
    obtain ⟨W, hW, hTW⟩ := isIrreducible_iff_sUnion_isClosed.1 hT himg.toFinset
      (fun W hW => by
        rw [himg.mem_toFinset] at hW
        obtain ⟨Z, -, rfl⟩ := hW
        exact isClosed_closure) hcov
    rw [himg.mem_toFinset] at hW
    obtain ⟨Z, hZ, rfl⟩ := hW
    have hTeq : closure (f '' Z) = T :=
      le_antisymm (closure_minimal (by rintro _ ⟨x, hxZ, rfl⟩; exact hmemS hZ hxZ) hTcl) hTW
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober (hSirr Z hZ) (hScl Z hZ)
    exact ⟨f ξ, hTeq ▸ hξ.image hf⟩

/-- A continuous open surjection out of a locally Noetherian quasi-sober space has quasi-sober
target.

Each point of the source has a Noetherian open neighbourhood `U`; it is quasi-sober as an open
subspace, so its image is quasi-sober by `quasiSober_of_noetherianSpace_surjective`. These
images are open by hypothesis and cover the target by surjectivity, and quasi-sobriety is local
on an open cover. -/
theorem quasiSober_of_isLocallyNoetherianSpace_isOpenMap_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober X]
    (hX : IsLocallyNoetherianSpace X) {f : X → Y} (hf : Continuous f) (hopen : IsOpenMap f)
    (hsurj : Function.Surjective f) : QuasiSober Y := by
  classical
  choose U hUopen hUmem hUnoeth using hX
  have hcov : ⋃ x : X, f '' U x = Set.univ :=
    Set.eq_univ_of_forall fun y => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact Set.mem_iUnion.2 ⟨x, x, hUmem x, rfl⟩
  refine (IsOpenCover.of_sets (fun x : X => hopen _ (hUopen x)) hcov).quasiSober_iff_forall.2
    fun x => ?_
  have : NoetherianSpace (U x) := hUnoeth x
  have : QuasiSober (U x) := (hUopen x).isOpenEmbedding_subtypeVal.quasiSober
  change QuasiSober (f '' U x)
  refine quasiSober_of_noetherianSpace_surjective
    (f := fun z : U x => (⟨f z.1, z.1, z.2, rfl⟩ : (f '' U x : Set Y)))
    ((hf.comp continuous_subtype_val).subtype_mk _) ?_
  rintro ⟨y, z, hz, rfl⟩
  exact ⟨⟨z, hz⟩, rfl⟩

end
