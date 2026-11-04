module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMapQuasiIso
public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.VanishingCohomology

/-!
# The Hom complex out of a resolution, into a K-injective complex

Let `A` be an abelian category, let `T` be an object of `A` and let `ε : P ⟶ T[0]` be a
resolution of `T` by a chain complex `P` indexed by `ℕ`, that is a quasi-isomorphism onto the
complex concentrated in degree zero. For a K-injective cochain complex `I` the Hom complex out of
`P`, placed in non-positive degrees, then computes the Hom complex out of `T`; and that Hom
complex is the product total complex of the double complex `Hom(P_p, I^q)`. So

`Hom(T, I^•) ⟶ Tot_π(Hom(P_p, I^q))`

is a quasi-isomorphism, with no boundedness hypothesis on `I`.

This is the step shared by the two resolutions the cohomological descent of a hypercovering
needs — the free abelian complex of Stacks 01GE on the base site and the complex of Stacks 0D78
on the total site — and by the integral resolution of Stacks 09WI, for which
`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequenceUnbounded.lean` spells it
out at the complex of sections.

## Main definitions

* `CochainComplex.resolutionCochainAugmentation`: the resolution read as a cochain complex
  supported in non-positive degrees, together with its augmentation.
* `CochainComplex.resolutionToProductTotal`: the comparison `Hom(T, I^•) ⟶ Tot_π(Hom(P_p, I^q))`.

## Main results

* `CochainComplex.quasiIso_resolutionCochainAugmentation`: the cochain form of a resolution is
  again a quasi-isomorphism.
* `CochainComplex.quasiIso_resolutionToProductTotal`: **the comparison is a quasi-isomorphism at a
  K-injective complex.**

## Implementation notes

The two inputs are `CochainComplex.HomComplex.homComplexMap_quasiIso`, which inverts the Hom
complex of a quasi-isomorphism between complexes with K-injective targets, and
`CochainComplex.homProductTotalIso`, which identifies the Hom complex out of a chain complex
placed in non-positive degrees with the product total complex of `Hom(P_p, I^q)`. The source of
the comparison is written as `CochainComplex.coyonedaComplex` rather than as the Hom complex out
of `T[0]`, the two being identified by
`Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (P : ChainComplex A ℕ) (T : A) (ε : P ⟶ (ChainComplex.single₀ A).obj T)

/-- A resolution `ε : P ⟶ T[0]` read as a morphism of cochain complexes, with `P` placed in
non-positive degrees. -/
def resolutionCochainAugmentation :
    P.extend ComplexShape.embeddingDownNat ⟶ (CochainComplex.singleFunctor A 0).obj T :=
  HomologicalComplex.extendMap ε ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat T 0 0 rfl).hom

/-- The cochain form of a resolution is a quasi-isomorphism. -/
instance quasiIso_resolutionCochainAugmentation [QuasiIso ε] :
    QuasiIso (resolutionCochainAugmentation P T ε) := by
  dsimp only [resolutionCochainAugmentation]
  infer_instance

omit [HasDerivedCategory A] in
/-- **An additive functor carries the cochain form of a resolution to a quasi-isomorphism as soon
as it carries the resolution itself to one.** The cochain form places the `ℕ`-indexed chain
complex `P` in the non-positive degrees of a `ℤ`-indexed cochain complex, and the functor is
applied *after* that extension; this transfers the hypothesis back to the `ℕ`-indexed complex,
where the resolution lives.

The two steps are `HomologicalComplex.quasiIso_mapHomologicalComplex_map_extendMap_iff`, which
moves the functor past the extension, and the fact that the remaining factor
`HomologicalComplex.extendSingleIso` is an isomorphism. -/
theorem quasiIso_map_resolutionCochainAugmentation {B : Type*} [Category* B] [Abelian B]
    (F : A ⥤ B) [F.Additive]
    (h : QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ε)) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (resolutionCochainAugmentation P T ε)) := by
  have hext : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap ε ComplexShape.embeddingDownNat)) :=
    (HomologicalComplex.quasiIso_mapHomologicalComplex_map_extendMap_iff F
      ComplexShape.embeddingDownNat ε).2 h
  dsimp only [resolutionCochainAugmentation]
  rw [Functor.map_comp]
  infer_instance

/-- **The comparison `Hom(T, I^•) ⟶ Tot_π(Hom(P_p, I^q))`**: the Hom complex out of `T`, mapped by
precomposition with the augmentation of the resolution, read through the identification of the Hom
complex out of the resolution with the product total complex of the double complex
`Hom(P_p, I^q)`. -/
def resolutionToProductTotal (I : CochainComplex A ℤ) :
    coyonedaComplex T I ⟶ (homProductDoubleComplex P I).productTotal :=
  (Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda T I).inv ≫
    CochainComplex.HomComplex.homComplexMap (resolutionCochainAugmentation P T ε) (𝟙 I) ≫
      (homProductTotalIso P I).hom

/-- **The Hom complex out of a resolution computes the Hom complex out of the object resolved, at
a K-injective complex.** For a resolution `ε : P ⟶ T[0]` and a K-injective complex `I`, with no
boundedness hypothesis, the comparison from `Hom(T, I^•)` to the product total complex of
`Hom(P_p, I^q)` is a quasi-isomorphism. -/
instance quasiIso_resolutionToProductTotal [QuasiIso ε] (I : CochainComplex A ℤ)
    [I.IsKInjective] : QuasiIso (resolutionToProductTotal P T ε I) := by
  have := CochainComplex.HomComplex.homComplexMap_quasiIso
    (resolutionCochainAugmentation P T ε) (𝟙 I)
  dsimp only [resolutionToProductTotal]
  infer_instance

end CochainComplex

end
