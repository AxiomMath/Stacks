module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.LocalUnitBasis
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.OfBasis

/-!
# A degree-`d` cover of the spectrum of a field comes from structure constants

Let `K` be a field and let `p : Z ⟶ Spec K` be finite locally free of degree `d > 0`. Then `Z`
is the spectrum of the algebra of a free `d`-dimensional structure over `K`, as a scheme over
`Spec K`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.overIsoSpecOverSections`: a scheme affine over the
  spectrum of a ring is the spectrum of its own global sections, as a scheme over that spectrum.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.exists_structure_overIsoSpecCover_of_field`: a degree-`d`
  finite locally free cover of the spectrum of a field is the spectrum of the algebra of a free
  `d`-dimensional structure, over that spectrum.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

/-- A scheme affine over the spectrum of a ring is the spectrum of its own global sections, as a
scheme over that spectrum, for the algebra structure the morphism induces. -/
noncomputable def overIsoSpecOverSections {R : Type u} [CommRing R] {Z : Scheme.{u}}
    [IsAffine Z] (p : Z ⟶ Spec (.of R)) :
    letI : Algebra R Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom.toAlgebra
    Over.mk p ≅ specOver R Γ(Z, ⊤) :=
  letI : Algebra R Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom.toAlgebra
  Over.isoMk Z.isoSpec (by
    change Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop) = p
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id])

/-- A degree-`d` finite locally free cover of the spectrum of a field `K` is the spectrum of the
algebra of a free `d`-dimensional structure over `K`, as a scheme over `Spec K`. -/
theorem exists_structure_overIsoSpecCover_of_field {K : Type u} [Field K] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of K)) (d : ℕ) [NeZero d]
    (hp : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p d) :
    ∃ m : FiniteFreeAlgebra K d, Nonempty (Over.mk p ≅ specCover m) := by
  have : IsAffineHom p := hp.toIsAffineHom
  have : IsAffine Z := isAffine_of_isAffineHom p
  let : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  obtain ⟨_, hrank⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget p d rfl).mp hp
  obtain ⟨b, hb⟩ :=
    exists_basis_one_of_isLocalRing (Module.finBasisOfFinrankEq K Γ(Z, ⊤) hrank)
  exact ⟨ofBasis b hb,
    ⟨overIsoSpecOverSections p ≪≫ specOverIsoSpecCoverOfBasis b hb⟩⟩

end AlgebraicGeometry.FiniteFreeAlgebra

end
