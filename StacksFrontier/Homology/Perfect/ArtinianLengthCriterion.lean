module

public import StacksFrontier.Homology.Perfect.FreeComplexLength

/-!
# The length criterion for free cohomology over an Artinian local ring

Let `A` be an Artinian local ring with residue field `κ`, and let `K` be a pseudo-coherent object
of `D(A)`, with fibre Betti numbers `β_i = dim_κ H^i(K ⊗ᴸ_A κ)`. Then

`ℓ(H^i(K)) ≤ β_i · ℓ(A)` for every `i`,

and equality holds in every degree if and only if every `H^i(K)` is free of rank `β_i`.

The proof represents `K` by its rank-minimal free model of [Stacks, Tag 0BCC], whose term in
degree `i` is `A^{β_i}`, and applies the complex-level criterion
`CochainComplex.moduleCat_d_eq_zero_of_length_homology_eq_of_free`.

This is the Artinian step of Deligne's proof that the de Rham cohomology sheaves of a proper
smooth morphism over `ℚ` are finite locally free, the assertion of [Stacks, Tag 0FMN] that the
source defers to a future reference.

## Main results

* `StacksDraft.Perfect.length_homology_le_of_isArtinianRing`: `ℓ(H^i(K)) ≤ β_i · ℓ(A)`.
* `StacksDraft.Perfect.length_homology_eq_iff_free_of_isArtinianRing`: equality in every degree
  iff every `H^i(K)` is free of rank `β_i`.

## Implementation notes

[Stacks, Tag 0BCC] (`StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing`)
is stated in the standard model `HasDerivedCategory.standard` of `D(A)`, and its minimal model is
only available there, so the two results of this file are stated in that model too, in a section
of their own. Everything they rest on is model-free.

No `@[stacks]` attribute is carried: these are tools.

## References

* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u v

namespace StacksDraft.Perfect

section StandardModel

attribute [local instance] HasDerivedCategory.standard

/-- A model `P` of `K` has the same homology as `K`. -/
private noncomputable def homologyIsoOfModel {A : Type u} [CommRing A]
    {K : DerivedCategory (ModuleCat.{max v u} A)} {P : CochainComplex (ModuleCat.{max v u} A) ℤ}
    (e : DerivedCategory.Q.obj P ≅ K) (j : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj K ≅ P.homology j :=
  (DerivedCategory.homologyFunctor _ j).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app P

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
  (K : DerivedCategory (ModuleCat.{max v u} A))
  (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
include hK

omit [IsArtinianRing A] in
/-- **`ℓ(H^i(K)) ≤ β_i · ℓ(A)`** for a pseudo-coherent object `K` of `D(A)` over an Artinian
local ring, where `β_i = dim_κ H^i(K ⊗ᴸ_A κ)`. -/
theorem length_homology_le_of_isArtinianRing (i : ℤ) :
    Module.length A ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) ≤
      Module.finrank (IsLocalRing.ResidueField A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} (IsLocalRing.ResidueField A)) i).obj
          ((totalDerivedExtensionScalars.{u, u, v} (IsLocalRing.residue A)).functor.obj K)) *
        Module.length A A := by
  obtain ⟨-, -, -, P, -, ⟨hPX, ⟨e⟩⟩, -⟩ :=
    exists_unique_boundedAbove_free_complex_representing.{u, v} K hK
  rw [(homologyIsoOfModel e i).moduleCat_length_eq]
  exact CochainComplex.moduleCat_length_homology_le_of_free.{v} P _ hPX i

/-- **The length criterion for free cohomology over an Artinian local ring.** For a
pseudo-coherent object `K` of `D(A)`, `ℓ(H^i(K)) = β_i · ℓ(A)` holds in every degree `i` if and
only if every `H^i(K)` is free of rank `β_i = dim_κ H^i(K ⊗ᴸ_A κ)`. -/
theorem length_homology_eq_iff_free_of_isArtinianRing :
    (∀ i : ℤ,
      Module.length A ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K) =
        Module.finrank (IsLocalRing.ResidueField A)
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} (IsLocalRing.ResidueField A))
            i).obj ((totalDerivedExtensionScalars.{u, u, v} (IsLocalRing.residue A)).functor.obj
              K)) * Module.length A A) ↔
      ∀ i : ℤ, Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj K ≅
        ModuleCat.of A (ULift.{v} (Fin (Module.finrank (IsLocalRing.ResidueField A)
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} (IsLocalRing.ResidueField A))
            i).obj ((totalDerivedExtensionScalars.{u, u, v} (IsLocalRing.residue A)).functor.obj
              K))) → A))) := by
  constructor
  · intro h i
    obtain ⟨-, -, -, P, -, ⟨hPX, ⟨e⟩⟩, -⟩ :=
      exists_unique_boundedAbove_free_complex_representing.{u, v} K hK
    have hd := CochainComplex.moduleCat_d_eq_zero_of_length_homology_eq_of_free.{v} P _ hPX
      Module.length_ne_top (fun j => by
        rw [← (homologyIsoOfModel e j).moduleCat_length_eq]; exact h j)
    exact ⟨homologyIsoOfModel e i ≪≫ P.moduleCatHomologyIsoXOfDEqZero hd i ≪≫ (hPX i).some⟩
  · intro h i
    rw [(h i).some.moduleCat_length_eq]
    exact Module.length_ulift_fin_pi A _

end StandardModel

end StacksDraft.Perfect
