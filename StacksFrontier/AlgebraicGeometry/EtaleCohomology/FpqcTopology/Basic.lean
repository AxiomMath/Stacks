module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute

/-!
# The fpqc topology

A family of morphisms to a scheme is an fpqc covering when its members are flat, jointly
surjective, and the family admits a quasi-compactness refinement. Zariski open coverings are
fpqc coverings, a flat surjective quasi-compact morphism is a singleton fpqc covering, and for
affine schemes a singleton family is an fpqc covering exactly when the corresponding ring map is
faithfully flat.

## Main results

* `AlgebraicGeometry.Scheme.zariskiPrecoverage_le_fpqcPrecoverage` says every Zariski covering
  family is an fpqc covering family.
* `AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage` says the singleton family of a
  flat, surjective, quasi-compact morphism is an fpqc covering.
* `AlgebraicGeometry.singleton_specMap_mem_fpqcPrecoverage_iff_faithfullyFlat` characterizes
  singleton fpqc coverings of affine schemes.

## Implementation notes

Mathlib states the Zariski comparison simultaneously for every scheme, as an inclusion of
precoverages. Flatness, surjectivity and quasi-compactness of a morphism are expressed by the
corresponding morphism-property typeclasses, and faithful flatness of a ring map by
`RingHom.FaithfullyFlat`.

## References

* [Stacks Project, Tag 03NY](https://stacks.math.columbia.edu/tag/03NY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

add_to_stacks 03NY "zariski_coverings"
  AlgebraicGeometry.Scheme.zariskiPrecoverage_le_fpqcPrecoverage
add_to_sga "4 VII 4.2" "partial" AlgebraicGeometry.Scheme.zariskiPrecoverage_le_fpqcPrecoverage

add_to_stacks 03NY "qc_flat_surjective" AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage
add_to_sga "3 III 3.3" "quasi-compact branch"
  AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage
add_to_sga "3 IV 6.3.2" "partial" AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage
add_to_sga "3 VIIA 8.1.4" "Converse clause"
  AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage
add_to_sga "3 XI 6.8" "Fpqc covering step"
  AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage
add_to_sga "4 VII 4.2" "partial" AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage
add_to_sga "4½ Arcata 1.6.4" "special case"
  AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 03NY.** The singleton family of affine schemes induced by a
ring homomorphism is an fpqc covering if and only if the homomorphism is faithfully flat. -/
@[stacks 03NY "affine_singleton"]
public theorem singleton_specMap_mem_fpqcPrecoverage_iff_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Presieve.singleton (Spec.map (CommRingCat.ofHom f)) ∈
      Scheme.fpqcPrecoverage (Spec (.of A)) ↔ f.FaithfullyFlat := by
  constructor <;> intro h
  · have hpre := (Scheme.singleton_mem_precoverage_iff (P := @Flat) _).mp h.2
    exact (flat_and_surjective_SpecMap_iff _).1 ⟨hpre.2, (surjective_iff _).2 hpre.1⟩
  · obtain ⟨hf, hs⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).2 h
    let _ := hf; let _ := hs; exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

end AlgebraicGeometry
