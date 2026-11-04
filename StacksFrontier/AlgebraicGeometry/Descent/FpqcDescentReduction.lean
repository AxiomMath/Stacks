module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumAlongRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumRealizations
public import StacksFrontier.AlgebraicGeometry.Descent.DescendingTypesOfMorphisms
public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongFpqcCovering
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.FamilyCoproduct

/-!
# Fpqc descent of morphisms over an affine base

Let `P` be a property of morphisms of schemes which is stable under base change and closed under
finite disjoint unions, and for which every descent datum relative to a surjective flat morphism
of affine schemes whose component has `P` is effective.  Then over an affine base every descent
datum relative to an fpqc covering whose components have `P` is effective.

## Main results

* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffine`: over an affine base, every
  descent datum relative to an fpqc covering whose components have `P` is effective.
* `AlgebraicGeometry.DescentData.isFamilyEffective_pullback_of_isAffine`: the same conclusion for
  the base change of a descent datum relative to an fpqc covering of an arbitrary base along a
  morphism from an affine scheme.

## Implementation notes

The index type of the covering family lies in the universe of the schemes, which is what the
refinement step of Stacks 022E and the pullback functor of Stacks 02VS are stated for.

## References

* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 023X](https://stacks.math.columbia.edu/tag/023X)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {I : Type u} {X : I → Scheme.{u}}

/-- The base change of a family of morphisms with fixed target along a morphism of base schemes,
read as a morphism of families of morphisms of schemes lying over that morphism. -/
def MorphismOfSchemeFamilies.ofBaseChange {S S' : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (h : S' ⟶ S) : MorphismOfSchemeFamilies.{u} where
  sourceBase := S'
  targetBase := S
  sourceFamily := 𝒰.pullback₁ h
  targetFamily := 𝒰
  baseHom := h
  familyHom :=
    { s₀ i := i
      h₀ i := pullback.snd h (𝒰.f i)
      w₀ _ := pullback.condition.symm }

namespace DescentData

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

/-- Let `P` be stable under base change and closed under finite disjoint unions, and let every
descent datum relative to a surjective flat morphism of affine schemes whose component has `P` be
effective.  Then over an affine base every descent datum relative to an fpqc covering whose
components have `P` is effective. -/
@[stacks 02W3 "the fpqc case over an affine base"]
theorem isFamilyEffective_of_isAffine
    [P.IsStableUnderBaseChange]
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (a : ∀ j, Y j ⟶ Z j), (∀ j, P (a j)) → P (Limits.Sigma.map a))
    (haffine : ∀ {T Z : Scheme.{u}} [IsAffine T] [IsAffine Z] (a : Z ⟶ T),
      Surjective a → Flat a → ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    [IsAffine S] (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective := by
  refine isFamilyEffective_of_finiteAffineFlat (V := ⟨I, X, f⟩) hf ?_ D hP
  intro 𝒱 hfin haff _ hmem E hPE
  have : Finite 𝒱.I₀ := hfin
  have hgmem : Presieve.singleton (Sigma.desc 𝒱.f) ∈ Scheme.propQCPrecoverage (@Flat.{u}) S :=
    (ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem 𝒱.X 𝒱.f).mp hmem
  obtain ⟨hgsurj, hgflat⟩ :=
    (Scheme.singleton_mem_precoverage_iff (@Flat.{u}) (Sigma.desc 𝒱.f)).mp
      (Scheme.propQCPrecoverage_le_precoverage S hgmem)
  exact isFamilyEffective_of_finiteAffine (Q := @Flat.{u}) (𝒱 := 𝒱) hcoprod haffine haff ⟨hgsurj⟩
    hgflat E hPE

/-- The base change of a descent datum relative to an fpqc covering of an arbitrary base along a
morphism from an affine scheme is effective, under the hypotheses of
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffine`. -/
theorem isFamilyEffective_pullback_of_isAffine
    [P.IsStableUnderBaseChange]
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (a : ∀ j, Y j ⟶ Z j), (∀ j, P (a j)) → P (Limits.Sigma.map a))
    (haffine : ∀ {T Z : Scheme.{u}} [IsAffine T] [IsAffine Z] (a : Z ⟶ T),
      Surjective a → Flat a → ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    (𝒰 : PreZeroHypercover.{u} S)
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData 𝒰.f) (hP : ∀ i, P (D.obj i).hom)
    {S' : Scheme.{u}} [IsAffine S'] (h : S' ⟶ S) :
    ((MorphismOfSchemeFamilies.pullbackFunctor
      (MorphismOfSchemeFamilies.ofBaseChange 𝒰 h)).functor.obj D).IsFamilyEffective := by
  set F := MorphismOfSchemeFamilies.ofBaseChange 𝒰 h
  have hmem : Presieve.ofArrows (𝒰.pullback₁ h).X (𝒰.pullback₁ h).f ∈
      Scheme.fpqcPrecoverage S' :=
    ((⟨𝒰, h𝒰⟩ : Scheme.fpqcPrecoverage.ZeroHypercover S).pullback₁ h).mem₀
  refine isFamilyEffective_of_isAffine hcoprod haffine (𝒰.pullback₁ h).f hmem _ fun i ↦ ?_
  rw [(MorphismOfSchemeFamilies.pullbackFunctor F).obj_eq D]
  exact MorphismProperty.baseChange_obj (F.familyHom.h₀ i) (D.obj (F.familyHom.s₀ i)) (hP _)

end DescentData

end AlgebraicGeometry
