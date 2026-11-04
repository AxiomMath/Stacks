module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexProperFlat
public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.RelativelyPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartExistence

/-!
# The relative dualizing complex of a proper flat morphism is a relative dualizing complex

Let `S` be a quasi-compact and quasi-separated scheme and `f : X ⟶ S` a proper, flat morphism of
finite presentation. The relative dualizing complex `ω_{X/S}^• = a(𝒪_S)` of
[Stacks, Remark 0B6S], together with the map `ξ : Δ_*𝒪_X ⟶ L pr₁^*ω_{X/S}^•` adjoint to the
isomorphism `𝒪_X ≅ c(L pr₁^*ω_{X/S}^•)` of [Stacks, Tag 0E2Q], is a relative dualizing complex in
the sense of [Stacks, Definition 0E2T] ([Stacks, Tag 0E2Z]).

## Main results

* `Stacks.Duality.isRelativeDualizingComplex_relativeDualizingComplex` — [Stacks, Tag 0E2Z].

## Implementation notes

The proof is the source's. Condition (1), that `ω_{X/S}^•` is `S`-perfect, is
[Stacks, Tag 0E4L] part (1),
`Stacks.Duality.StandardModel.isPerfectRelativeTo_relativeDualizingComplex`. Condition (2): `ξ`
is the transpose under `Δ_* ⊣ R ℰom(𝒪_X, -)` of an isomorphism
`𝒪_X ≅ R ℰom(𝒪_X, L pr₁^*ω_{X/S}^•)` (the isomorphism of [Stacks, Tag 0E2Q] read through
[Stacks, Tag 0A9X]), and by [Stacks, Tag 0A77] such a transpose defines an isomorphism
`Δ_*𝒪_X ≅ R SheafHom(Δ_*𝒪_X, L pr₁^*ω_{X/S}^•)`
(`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isIso_diagonalAction_diagonalGenerator`).

All derived categories are at `CategoryTheory.HasDerivedCategory.standard`, the model at which
relative dualizing complexes are defined; the instances are named in the statement.

## References

* [Stacks Project, Tag 0E2Z](https://stacks.math.columbia.edu/tag/0E2Z)
* [Stacks Project, Tag 0E2T](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Tag 0E4L](https://stacks.math.columbia.edu/tag/0E4L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-- **Stacks Project, Tag 0E2Z.** Let `S` be a quasi-compact and quasi-separated scheme and let
`f : X ⟶ S` be a proper, flat morphism of finite presentation. The relative dualizing complex
`ω_{X/S}^• = a(𝒪_S)` of [Stacks, Remark 0B6S]
(`Stacks.Duality.StandardModel.relativeDualizingComplex`) together with the map
`ξ : Δ_*𝒪_X ⟶ L pr₁^*ω_{X/S}^•` coming from the isomorphism `𝒪_X ≅ c(L pr₁^*ω_{X/S}^•)` of
[Stacks, Tag 0E2Q] (`Stacks.Duality.relativeDualizingComplexDiagonalMap`) is a relative
dualizing complex in the sense of [Stacks, Definition 0E2T], for the open `W = X ×_S X` (the
morphism being separated) and the derived tensor product of sheaves of modules.

Of finite presentation is `LocallyOfFinitePresentation f` together with the quasi-compactness and
quasi-separatedness that properness includes. -/
@[stacks 0E2Z]
theorem isRelativeDualizingComplex_relativeDualizingComplex {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    haveI : CompactSpace (pullback f f : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
    haveI : QuasiSeparatedSpace (pullback f f : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst f f)
    @Scheme.Hom.IsRelativeDualizingComplex X S f (HasDerivedCategory.standard _)
      (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base) (fun _ => HasDerivedCategory.standard _))
      (Scheme.Hom.DiagonalOpen.ofIsSeparated f) (StandardModel.relativeDualizingComplex f).obj
      (relativeDualizingComplexDiagonalMap f) :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  have : QuasiSeparatedSpace (pullback f f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f f)
  (@Scheme.Hom.isRelativeDualizingComplex_iff X S f (HasDerivedCategory.standard _)
      (fun _ => HasDerivedCategory.standard _) _ _
      (@RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base) (fun _ => HasDerivedCategory.standard _))
      (Scheme.Hom.DiagonalOpen.ofIsSeparated f) (StandardModel.relativeDualizingComplex f).obj
      (relativeDualizingComplexDiagonalMap f)).2
    ⟨StandardModel.isPerfectRelativeTo_relativeDualizingComplex f,
      (Scheme.Hom.DiagonalOpen.ofIsSeparated f).isIso_diagonalAction_diagonalGenerator _
        (diagonalExactSupportRelativeDualizingComplexIso f)⟩

end Stacks.Duality

end
