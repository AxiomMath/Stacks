module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.RingTheory.Depth.Defs.Defs

/-!
# Depth along an ideal and along its image under a surjection

Let `A → B` be a surjective map of commutative rings, `I ⊆ A` an ideal and `M` a `B`-module,
read as an `A`-module through the map. Then the `I`-depth of `M` over `A` and the `I·B`-depth of
`M` over `B` agree.

## Main results

* `Module.depth_eq_depth_map_algebraMap`: `depth_I(M) = depth_{I·B}(M)` for a surjective
  `algebraMap A B` and a `B`-module `M`.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

open RingTheory.Sequence

/-- For a surjective algebra map `A → B`, the depth of a `B`-module along an ideal `I` of `A`
agrees with its depth along the image ideal. -/
public theorem Module.depth_eq_depth_map_algebraMap {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hsurj : Function.Surjective (algebraMap A B)) (I : Ideal A)
    (M : Type*) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] :
    Module.depth A I M = Module.depth B (I.map (algebraMap A B)) M := by
  have hreg : ∀ rs : List A, IsRegular M rs ↔ IsRegular M (rs.map (algebraMap A B)) := fun rs =>
    (AddEquiv.refl M).isRegular_congr <| List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ x => (algebraMap_smul B r x).symm
  have htop : I • (⊤ : Submodule A M) = ⊤ ↔
      (I.map (algebraMap A B)) • (⊤ : Submodule B M) = ⊤ := by
    rw [← Submodule.restrictScalars_eq_top_iff (S := A)
      (p := (I.map (algebraMap A B)) • (⊤ : Submodule B M)), Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top]
  have hlift : ∀ ss : List B, (∀ s ∈ ss, s ∈ I.map (algebraMap A B)) →
      ∃ rs : List A, (∀ r ∈ rs, r ∈ I) ∧ rs.map (algebraMap A B) = ss := by
    intro ss
    induction ss with
    | nil => exact fun _ => ⟨[], by simp, rfl⟩
    | cons s ss ih =>
      intro h
      obtain ⟨rs, hrs, hmap⟩ := ih fun t ht => h t (List.mem_cons_of_mem _ ht)
      obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ hsurj).mp (h s List.mem_cons_self)
      exact ⟨a :: rs, by simpa using ⟨ha, hrs⟩, by simp [hmap]⟩
  simp only [Module.depth, htop]
  refine if_congr Iff.rfl rfl (le_antisymm ?_ ?_)
  · refine iSup₂_le fun rs hrs => le_iSup₂_of_le (rs.map (algebraMap A B)) ?_ ?_
    · exact ⟨fun s hs => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
        exact Ideal.mem_map_of_mem _ (hrs.1 r hr), (hreg rs).mp hrs.2⟩
    · simp
  · refine iSup₂_le fun ss hss => ?_
    obtain ⟨rs, hrs, rfl⟩ := hlift ss hss.1
    refine le_iSup₂_of_le rs ⟨hrs, (hreg rs).mpr hss.2⟩ ?_
    simp

end
