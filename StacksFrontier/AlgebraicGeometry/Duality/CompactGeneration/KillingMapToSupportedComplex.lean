module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.SupportedPerfectLift
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.TensorHomSourceNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafHomSupported
public import StacksFrontier.AlgebraicGeometry.Duality.InternalHom.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingTransposeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit

/-!
# Tag 0A9C: killing a map to a complex with support

Let `X` be a quasi-compact quasi-separated scheme and let `T ⊆ X` be closed with quasi-compact
complement; write `U = X ∖ T`. Let `α : P ⟶ E` be a morphism of `D(𝒪_X)` with either

1. `P` perfect and `E` with quasi-coherent cohomology supported on `T`, or
2. `P` pseudo-coherent and `E` with quasi-coherent cohomology supported on `T` and bounded below.

Then there are a perfect complex `I` of `𝒪_X`-modules and a map `I ⟶ 𝒪_X[0]` such that the
composite `I ⊗^L_{𝒪_X} P ⟶ P ⟶ E` is zero and `I|_U ⟶ 𝒪_U[0]` is an isomorphism.

## Main results

* `AlgebraicGeometry.exists_isPerfect_derivedTensor_comp_eq_zero`: **[Stacks, Tag 0A9C]**.

## The proof

It is the source's. The complex `K = R𝓗om_{𝒪_X}(P, E)` has quasi-coherent cohomology by
[Stacks, Tag 0A6H] — in case (1) by
`Stacks.Duality.InternalHom.derivedCategoryB_derivedSheafHom_of_isPerfect`, which needs no
boundedness, and in case (2) by
`AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent` — and that cohomology is
supported on `T` by `AlgebraicGeometry.cohomologySupportedOn_derivedSheafHom`, formation of `R𝓗om`
commuting with restriction to opens. The tensor–internal-Hom bijection of [Stacks, Tag 08J8] turns
`α` into a morphism `α' : 𝒪_X[0] ⟶ K`, and
`Stacks.Duality.Supported.exists_isPerfect_isIso_derivedRestrict_comp_eq_zero` — the
cell-filtration argument of [Stacks, Tags 0A9A, 09SN, 094A and 09SP] — produces the perfect complex
`I` and the map `f : I ⟶ 𝒪_X[0]` with `f ≫ α' = 0` and `I|_U ⟶ 𝒪_U[0]` invertible. Naturality of
that bijection in its source variable,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, reads `f ≫ α' = 0` as the
vanishing of `I ⊗^L_{𝒪_X} P ⟶ P ⟶ E`, the bijection being additive and `α'` being by construction
the transpose of the composite `𝒪_X[0] ⊗^L_{𝒪_X} P ⟶ P ⟶ E`.

## Implementation notes

*The model of the derived category.* `CategoryTheory.HasDerivedCategory.standard`, which the
whole derived-internal-Hom cluster pins and which is therefore the only model at which
[Stacks, Tag 08J8] and its naturality can be stated. The cell-filtration argument lives at the
locally small model, and
`StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedPerfectFactorizationStandard`
is where it is carried across.

*The map `I ⊗^L P ⟶ P`.* It is `f ⊗ 1_P` followed by the left unit constraint
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso` of [Stacks, Tag 0FPT], at the
canonical derived tensor product of [Stacks, Tag 06YU] — the same bifunctor the bijection of
[Stacks, Tag 08J8] is stated against, so the two meet with no comparison isomorphism.

*What the statement does not assume.* The source has `α` a morphism of `D_QCoh(𝒪_X)`, so that
`P` too has quasi-coherent cohomology. That is not used: the quasi-coherence of
`R𝓗om_{𝒪_X}(P, E)` needs only perfectness or pseudo-coherence of `P` together with
quasi-coherence of `E`. The hypothesis is therefore omitted, which only strengthens the
statement.

*Nothing is carried.* Every result the source cites is in the library: [Stacks, Tag 0A9A] is
`Stacks.Rouquier.exists_isPerfect_isWeakTriangulatedGenerator_supported`, [Stacks, Tag 09M1] is
`AlgebraicGeometry.isCompactObject_of_isPerfect`, [Stacks, Tag 0A6H] is the two statements named
above, and [Stacks, Tags 09SN], [Stacks, Tag 094A] and [Stacks, Tag 09SP] are combined in
`CategoryTheory.Pretriangulated.exists_fac_of_isWeakTriangulatedGenerator`.

## References

* [Stacks Project, Tag 0A9C](https://stacks.math.columbia.edu/tag/0A9C)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules (ringedSite)
open Stacks.Cohomology.PerfectComplexes
open Stacks.Duality.Supported (complementOpenOfIsClosed)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The canonical derived tensor product of [Stacks, Tag 06YU] on `D(𝒪_X)`, read as a datum over
the sheaf of rings rather than over the ringed site, which is the form the unit constraints of
[Stacks, Tag 0FPT] are stated for. Its bifunctor is
`Stacks.SheafOfModules.derivedTensorProductFunctor` unchanged. -/
abbrev schemeDerivedTensorProduct :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (ringedSite X.sheaf).O :=
  Stacks.DerivedQCoh.OpenLift.ringedSiteDerivedTensorProduct X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (ringedSite X.sheaf))

variable {X}

/-- **[Stacks, Tag 0A9C] for a map out of the structure sheaf, at the ringed-site spelling of
`D(𝒪_X)`.** This is `Stacks.Duality.Supported.exists_isPerfect_isIso_derivedRestrict_comp_eq_zero`
with the objects and morphisms read in `(ringedSite X.sheaf).DerivedModules`, the spelling over
which the derived tensor product and the bijection of [Stacks, Tag 08J8] are stated. Reading the
data across once, here, keeps the comparison of the two spellings out of the proof of
[Stacks, Tag 0A9C] below. -/
theorem exists_isPerfect_isIso_comp_eq_zero_ringedSite [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ) (K : (ringedSite X.sheaf).DerivedModules)
    (hKqc : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) K)
    (hKT : CohomologySupportedOn X.ringCatSheaf T K)
    (ζ : Stacks.DerivedTensor.RingedSite.unitObject (ringedSite X.sheaf) ⟶ K) :
    ∃ (I : (ringedSite X.sheaf).DerivedModules)
      (f : I ⟶ Stacks.DerivedTensor.RingedSite.unitObject (ringedSite X.sheaf)),
      IsPerfect (X := X.toRingedSpace) I ∧
        IsIso ((Scheme.Modules.restrictFunctor
          (complementOpenOfIsClosed hT).ι).mapDerivedCategory.map f) ∧ f ≫ ζ = 0 := by
  obtain ⟨I, f, hIp, hIiso, hf⟩ :=
    Stacks.Duality.Supported.exists_isPerfect_isIso_derivedRestrict_comp_eq_zero hT hTc K hKqc hKT ζ
  exact ⟨I, f, hIp, hIiso, hf⟩

/-- **[Stacks, Tag 0A9C].** Let `X` be a quasi-compact quasi-separated scheme, let `T ⊆ X` be
closed with quasi-compact complement and write `U = X ∖ T`. Let `α : P ⟶ E` be a morphism of
`D(𝒪_X)` with `E` having quasi-coherent cohomology supported on `T`, and with either `P` perfect
or `P` pseudo-coherent and `E` bounded below. Then there are a perfect complex `I` and a map
`f : I ⟶ 𝒪_X[0]` such that `I ⊗^L_{𝒪_X} P ⟶ P ⟶ E` is zero and `I|_U ⟶ 𝒪_U[0]` is an
isomorphism.

See the module documentation for the proof and for what is carried. -/
theorem exists_isPerfect_derivedTensor_comp_eq_zero [CompactSpace X] [QuasiSeparatedSpace X]
    {T : Set X} (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (P E : (ringedSite X.sheaf).DerivedModules) (α : P ⟶ E)
    (hEqc : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E)
    (hET : CohomologySupportedOn X.ringCatSheaf T E)
    (hP : IsPerfect (X := X.toRingedSpace) P ∨
      (RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) P ∧
        DerivedCategoryB.IsBoundedBelow E)) :
    ∃ (I : (ringedSite X.sheaf).DerivedModules)
      (f : I ⟶ Stacks.DerivedTensor.RingedSite.unitObject (ringedSite X.sheaf)),
      IsPerfect (X := X.toRingedSpace) I ∧
        IsIso ((Scheme.Modules.restrictFunctor
          (complementOpenOfIsClosed hT).ι).mapDerivedCategory.map f) ∧
        ((Stacks.SheafOfModules.derivedTensorProductFunctor (ringedSite X.sheaf)).map f).app P ≫
          (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso (ringedSite X.sheaf)
            (schemeDerivedTensorProduct X) P).hom ≫ α = 0 := by
  -- `K = R𝓗om(P, E)` has quasi-coherent cohomology supported on `T`.
  have hKqc : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (((ringedSite X.sheaf).derivedSheafHomBifunctor.obj (op P)).obj E) := by
    rcases hP with h | ⟨h, hb⟩
    · exact Stacks.Duality.InternalHom.derivedCategoryB_derivedSheafHom_of_isPerfect X P E h hEqc
    · exact derivedCategoryB_derivedSheafHom_of_isPseudoCoherent X P E h ⟨hb, hEqc⟩
  have hKT := cohomologySupportedOn_derivedSheafHom X hT P E hET
  -- The transpose of `𝒪_X[0] ⊗^L P ⟶ P ⟶ E` under the bijection of [Stacks, Tag 08J8].
  let e := RingedSite.derivedCurryHomEquiv (ringedSite X.sheaf)
    (Stacks.DerivedTensor.RingedSite.unitObject (ringedSite X.sheaf)) P E
  let u : ((Stacks.SheafOfModules.derivedTensorProductFunctor (ringedSite X.sheaf)).obj
      (Stacks.DerivedTensor.RingedSite.unitObject (ringedSite X.sheaf))).obj P ⟶ E :=
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso (ringedSite X.sheaf)
      (schemeDerivedTensorProduct X) P).hom ≫ α
  obtain ⟨I, f, hIp, hIiso, hf⟩ :=
    exists_isPerfect_isIso_comp_eq_zero_ringedSite hT hTc _ hKqc hKT (e.symm u)
  exact ⟨I, f, hIp, hIiso,
    RingedSite.derivedTensorProductFunctor_map_app_comp_eq_zero_of_comp_derivedCurryHomEquiv_symm
      (ringedSite X.sheaf) _ _ _ _ f u hf⟩

end AlgebraicGeometry

end
