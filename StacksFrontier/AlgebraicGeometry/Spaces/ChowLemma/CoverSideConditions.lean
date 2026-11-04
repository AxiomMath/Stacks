module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoverSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase

/-!
# The side conditions of the cover of Stacks 089J

Side conditions on the construction datum of the cover of [Stacks, Tag 089J]: quasi-separatedness
of a scheme separated over an affine base, reasonableness of an algebraic space separated over an
affine base, quasi-compactness of a chart with compact source, and the emptiness of a scheme
finite locally free of rank zero over a field.

## Main results

* `Stacks.Morphisms.isEmpty_of_isFiniteLocallyFreeOfRank_zero_of_specTarget`: a morphism to the
  spectrum of a field which is finite locally free of rank zero has empty source.
* `AlgebraicGeometry.quasiSeparatedSpace_of_isSeparated_toSpec`: a scheme separated over the
  spectrum of a ring is a quasi-separated space.
* `AlgebraicGeometry.Space.isReasonableSpace_of_isSeparated_toBase`: an algebraic space separated
  over an affine base is reasonable.
* `AlgebraicGeometry.Space.isQuasiCompact_of_compactSpace_source`: a morphism into an algebraic
  space separated over the base, out of a representable presheaf with compact underlying scheme,
  is quasi-compact.

## References

* [Stacks Project, Tag 03DY](https://stacks.math.columbia.edu/tag/03DY)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- A morphism to the spectrum of a field which is finite locally free of rank zero has empty
source. -/
theorem isEmpty_of_isFiniteLocallyFreeOfRank_zero_of_specTarget {K : Type u} [Field K]
    {Z : AlgebraicGeometry.Scheme.{u}} (f : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (h : IsFiniteLocallyFreeOfRank f 0) : IsEmpty Z := by
  let _ : Algebra K ↑Γ(Z, ⊤) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  obtain ⟨_, _, hrank⟩ := (isFiniteLocallyFreeOfRank_iff_finrank_sections_eq f 0).1 h
  have hzero : ∀ x : ↑Γ(Z, ⊤), x = 0 := (finrank_zero_iff_forall_zero (K := K)).1 hrank
  have hsub : Subsingleton ↑Γ(Z, ⊤) := ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
  have := AlgebraicGeometry.isAffine_of_isAffineHom f
  exact ⟨fun z ↦ (PrimeSpectrum.isEmpty_iff_subsingleton.mpr hsub).elim (Z.isoSpec.hom.base z)⟩

end Stacks.Morphisms

namespace AlgebraicGeometry

/-- A scheme separated over the spectrum of a ring is a quasi-separated space. -/
theorem quasiSeparatedSpace_of_isSeparated_toSpec {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) (hf : IsSeparated f) : QuasiSeparatedSpace Y := by
  have hterm : f ≫ terminal.from (Spec R) = terminal.from Y := terminalIsTerminal.hom_ext _ _
  have : Scheme.IsSeparated Y := ⟨by rw [← hterm]; infer_instance⟩
  infer_instance

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space separated over an affine base is reasonable. -/
theorem isReasonableSpace_of_isSeparated_toBase (hSaff : IsAffine S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from X)) :
    IsReasonableSpace B S hS X := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have habs : IsAbsolutelySeparated B S hS hZ X :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ (Over.mk (𝟙 (B.obj hS))) hSaff
      ((isTerminal_yoneda_obj_base B S hS).from X) hXsep
  exact isReasonableSpace_of_isVeryReasonableSpace B S hS X hX
    (isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ X hX
      (isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS X hZ hX
        (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ X habs)))

/-- A morphism into an algebraic space separated over the base, out of a representable presheaf
whose underlying scheme is compact, is quasi-compact. -/
theorem isQuasiCompact_of_compactSpace_source [QuasiSeparatedSpace S]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X)
    (hWc : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (hXsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from X)) :
    IsQuasiCompact B S hS c := by
  have hbase : QuasiSeparatedSpace
      ((BigFppfOver.toScheme B S hS).obj (Over.mk (𝟙 (B.obj hS)))) :=
    inferInstanceAs (QuasiSeparatedSpace S)
  refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS c
    ((isTerminal_yoneda_obj_base B S hS).from X) (isAlgebraicSpace_yoneda B S hS W)
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))) ?_
    (isQuasiSeparated_of_isSeparated B S hS hXsep)
  rw [show c ≫ (isTerminal_yoneda_obj_base B S hS).from X =
      yoneda.map (Over.mkIdTerminal.from W) from
    (isTerminal_yoneda_obj_base B S hS).hom_ext _ _]
  exact isQuasiCompact_yoneda_map_of_compactSpace B S hS _ hWc hbase

end AlgebraicGeometry.Space

end
