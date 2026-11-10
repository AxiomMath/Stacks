module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceMorphism

/-!
# A section of a projective bundle over an open trivialising the module

Let `ℰ` be a quasi-coherent module on a scheme `X` and `π : 𝐏(ℰ) ⟶ X` its projective bundle.
Over an open `U ⊆ X` on which `ℰ` is free of rank `n + 1`, the bundle restricts to `ℙⁿ_U`, and
`ℙⁿ_U ⟶ U` has an obvious section — the zero vector of a standard affine chart. Transporting
that section back gives

  `σ : U ⟶ 𝐏(ℰ)` with `σ ≫ π = U.ι`,

which is the pair of fields `sect` and `sect_comp_proj` of
`Stacks.Divisors.BundleSplittingDatum`. This is Tag 01OE.

## Main results

* `Stacks.ProjectiveBundleSplitting.exists_section_projectiveSpaceOver`: the projection of
  `ℙⁿ_S` to `S` has a section, for every scheme `S` and every `n`.
* `Stacks.ProjectiveBundleSplitting.exists_section_freeProjectiveBundle`: the projection of
  `𝐏(𝒪_S^{n+1})` to `S` has a section.
* `Stacks.ProjectiveBundleSplitting.exists_section_of_restrict_free`: the projection of `𝐏(ℰ)`
  has a section over an open on which `ℰ` is free of rank `n + 1`.
* `Stacks.ProjectiveBundleSplitting.exists_nonempty_open_section`: on an irreducible base, a
  module finite locally free of rank `n + 1` admits such an open, nonempty.

## Implementation notes

**Where the section comes from.** `ℙⁿ_S = S ×_{Spec ℤ} ℙⁿ_ℤ` carries the standard affine charts
`𝔸ⁿ_S ⟶ ℙⁿ_S` over `S` of
`AlgebraicGeometry.projectiveSpaceOver.affineChart`, and `𝔸ⁿ_S ⟶ S` has the zero section
`AlgebraicGeometry.AffineSpace.homOfVector (𝟙 S) 0`. The composite is a section of `ℙⁿ_S ⟶ S`;
no hypothesis on `S` is needed, and `n = 0` is allowed. Which chart is used is immaterial — the
first coordinate is taken.

**Why the trivialising open need not be affine.** The comparison of `𝐏(ℰ)` with `ℙⁿ` is made
over the whole of `U` at once, by Tag 01O3's base-change square
`AlgebraicGeometry.projectiveBundleBaseChangeComparison` at the open immersion `U.ι` followed by
Tag 01OE's `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace`. The chart-wise mapping-in
statement `Stacks.RelativeProj.Situation.exists_hom_relativeProjToBase`, which would need an
affine open and an explicit homomorphism out of the ring of homogeneous sections, is not used.

**The free module in the shape the trivialisation produces.** The pointwise form of Tag 01C6's
rank predicate, `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank`, gives an
isomorphism of `ℰ.restrict U.ι` with `SheafOfModules.free (ULift (Fin r))`, which is
`Stacks.SymGraded.freeModule (Stacks.SymGraded.coordIndex n)` for `r = n + 1`; the restriction
is crossed to the pullback by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`,
which is the shape the base-change comparison reads.

## References

* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleSplitting

/-- **The projection of `ℙⁿ_S` to `S` has a section.** The `0`-th standard affine chart
`𝔸ⁿ_S ⟶ ℙⁿ_S` lies over `S`, and the zero vector gives a section of `𝔸ⁿ_S ⟶ S`; the composite
is a section of `ℙⁿ_S ⟶ S`. -/
theorem exists_section_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    ∃ s : S ⟶ AlgebraicGeometry.projectiveSpaceOver.{u} n S,
      s ≫ (AlgebraicGeometry.projectiveSpaceOver.{u} n S ↘ S) = 𝟙 S := by
  refine ⟨AffineSpace.homOfVector
      (n := ULift.{u} {j : Fin (n + 1) // j ≠ 0}) (𝟙 S) 0 ≫
    AlgebraicGeometry.projectiveSpaceOver.affineChart n 0 Equiv.ulift S, ?_⟩
  rw [Category.assoc, AlgebraicGeometry.projectiveSpaceOver.affineChart_over,
    AffineSpace.homOfVector_over]

/-- **The bundle of the free module of rank `n + 1` is the one Tag 01OE compares with `ℙⁿ`.**
`Stacks.SymGraded.freeProjectiveBundle` is the relative `Proj` of
`Stacks.SymGraded.freeSymGradedAlgebra`, which is the symmetric algebra of the free module; both
sides are the same term with the definitions unfolded. -/
theorem schemeProjectiveBundle_freeModule (S : Scheme.{u}) (n : ℕ) :
    schemeProjectiveBundle (X := S) (freeModule (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := S) (coordIndex.{u} n)) =
      freeProjectiveBundle (X := S) n :=
  rfl

/-- **The projection of `𝐏(𝒪_S^{n+1})` to `S` has a section.** Tag 01OE identifies the bundle of
a free module with `ℙⁿ_S` over `S`, and `ℙⁿ_S ⟶ S` has a section. -/
theorem exists_section_freeProjectiveBundle (S : Scheme.{u}) (n : ℕ) :
    ∃ s : S ⟶ (schemeProjectiveBundle (X := S) (freeModule (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := S) (coordIndex.{u} n))).scheme,
      s ≫ (schemeProjectiveBundle (X := S) (freeModule (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := S) (coordIndex.{u} n))).toBase = 𝟙 S := by
  rw [schemeProjectiveBundle_freeModule]
  obtain ⟨t, ht⟩ := exists_section_projectiveSpaceOver n S
  refine ⟨t ≫ (projectiveBundleIsoProjectiveSpace (X := S) n).inv, ?_⟩
  rw [Category.assoc, ← projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := S) n,
    Iso.inv_hom_id_assoc]
  exact ht

/-- **A section of `𝐏(ℰ) ⟶ X` over an open on which `ℰ` is free of rank `n + 1`.** Tag 01O3's
base-change square identifies the part of `𝐏(ℰ)` lying over `U` with `𝐏(ℰ|_U) = 𝐏(𝒪_U^{n+1})`,
whose projection to `U` has a section; the second projection of the fibre product carries that
section into `𝐏(ℰ)`. -/
theorem exists_section_of_restrict_free {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    (hqc : IsQuasicoherentPieces E) (n : ℕ) (U : X.Opens)
    (hfree : Nonempty (E.restrict U.ι ≅
      SheafOfModules.free.{u} (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    ∃ σ : U.toScheme ⟶ (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme,
      σ ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase = U.ι := by
  have hE : freeModule (X := U.toScheme) (coordIndex.{u} n) ≅
      (Scheme.Modules.pullback U.ι).obj E :=
    hfree.some.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E
  obtain ⟨e, he⟩ := AlgebraicGeometry.projectiveBundleBaseChangeComparison U.ι E hqc
    (freeModule (X := U.toScheme) (coordIndex.{u} n)) (isQuasicoherentPieces_free _) hE
  obtain ⟨t, ht⟩ := exists_section_freeProjectiveBundle U.toScheme n
  refine ⟨t ≫ e.hom ≫ pullback.snd U.ι (schemeProjectiveBundle E hqc).toBase, ?_⟩
  change t ≫ e.hom ≫ pullback.snd _ _ ≫ (schemeProjectiveBundle E hqc).toBase = _
  rw [← pullback.condition, reassoc_of% he, reassoc_of% ht]

/-- **A nonempty open with a section, on an irreducible base.** A module finite locally free of
rank `n + 1` on an irreducible — in particular an integral — scheme is free of that rank on an
open neighbourhood of any point, and over such an open the projection of the bundle has a
section. This is the pair of fields `sect` and `sect_comp_proj` of
`Stacks.Divisors.BundleSplittingDatum`, together with `trivialOpen` and
`nonempty_trivialOpen`. -/
theorem exists_nonempty_open_section {X : Scheme.{u}} [IrreducibleSpace X] (E : X.Modules)
    [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E) (n : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)) :
    ∃ (U : X.Opens) (_ : Nonempty U)
      (σ : U.toScheme ⟶ (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme),
        σ ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase = U.ι := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hxU, hiso⟩ :=
    (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (n + 1)).mpr hE x
  exact ⟨U, ⟨⟨x, hxU⟩⟩, exists_section_of_restrict_free E hqc n U hiso⟩

end Stacks.ProjectiveBundleSplitting

end
