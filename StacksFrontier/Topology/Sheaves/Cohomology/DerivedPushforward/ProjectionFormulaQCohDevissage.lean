module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceModulesAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaTriangles

/-!
# The dévissage of [Stacks, Tag 08EU], assembled

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes, `E ∈ D_QCoh(𝒪_X)`
and `K ∈ D_QCoh(𝒪_Y)`.  [Stacks, Tag 08EU] asserts that the projection-formula morphism of
[Stacks, Tag 0B53],

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`,

is an isomorphism.  The source's proof has five steps: reduce to `Y` affine; direct sums;
distinguished triangles; the equivalence `D(A) ≌ D_QCoh(𝒪_Y)` over an affine base, which reduces
a general `K` to the shifts of the structure sheaf; and the case of those shifts, which the
source calls clear.

Three of the five are theorems of this development:

* the reduction to an affine base is
  `ProjectionFormulaQCohLocalization.isIso_projectionFormulaMap_of_isDQCoh_of_affineBase`;
* the triangle step is
  `Stacks.Cohomology.ProjectionFormulaTriangles.isIso_projectionFormulaMap_triangle`;
* the base case at every shift of the structure sheaf is
  `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitShift_unconditional`,
  unconditional and for an arbitrary morphism of ringed spaces.

This file puts those three together and states the whole tag, with the remaining two steps — the
dévissage principle for `D_QCoh` over an affine base, and the direct-sum step — as the named
hypotheses `hdev` and `hsig`.  Nothing else is assumed.

## Main results

* `isDQCoh_shift` and `sigmaShiftIso`: the two pieces of shift bookkeeping the assembly needs,
  both unconditional.
* `isIso_projectionFormulaMap_of_isDQCoh_of_isAffine_of_devissage`: the tag over an **affine**
  base, from `hdev` and `hsig`.
* `isIso_projectionFormulaMap_of_isDQCoh_of_devissage`: **the whole of [Stacks, Tag 08EU], from
  `hdev` and `hsig` and nothing else.**

## No tag is attached here

`hdev` and `hsig` are hypotheses that nothing in this development yet concludes, so none of the
declarations below states [Stacks, Tag 08EU] and none carries its attribute.  The two existing
registrations of that tag are untouched.

## Implementation notes

*Why the dévissage is run on all shifts at once.*  The dévissage theorem of [Stacks, Tag 09PB],
`CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts`, asks for the
**plain** two-out-of-three property — `T` at two vertices of a distinguished triangle gives `T` at
the third — and supplies the shifts separately, through its hypothesis at every shift of the
generator.  The plain property is *not* available for `T K = IsIso (projectionFormulaMap f E K)`:
the five-lemma argument that proves it needs invertibility at `T.obj₁⟦1⟧` and `T.obj₂⟦1⟧` as
well, which is exactly why
`Stacks.Cohomology.ProjectionFormulaTriangles.isIso_projectionFormulaMap_triangle` is stated over
all shifts.  So the property the dévissage is run on is `AllShifts f E K = ∀ n, IsIso
(projectionFormulaMap f E (K⟦n⟧))`, whose plain two-out-of-three *is* the all-shifts statement,
and the conclusion is read back at `n = 0` through `shiftFunctorZero`.  The cost is the two
bookkeeping lemmas at the head of the file: the coproduct step has to be transported across
`(∐ Z)⟦n⟧ ≅ ∐ (Z ·⟦n⟧)`, and that needs the shifted family to be quasi-coherent again.

*`hsig` is stated with a `[HasCoproduct Z]` binder.*  That is an instance binder for a limit that
the library supplies, not an added hypothesis on the mathematics: `D_QCoh` of a scheme has all
coproducts indexed by the scheme universe, by [Stacks, Tag 08DT].

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite

universe u

noncomputable section

namespace Stacks.Cohomology.ProjectionFormulaQCohDevissage

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

/-- **A shift of a complex with quasi-coherent cohomology has quasi-coherent cohomology.**

`Stacks.DerivedQCoh.IsDQCoh` is, by definition, membership of the object property
`DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent _)`, which is stable under the
shift because quasi-coherent modules on a scheme form a weak Serre subcategory
(`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre`). -/
theorem isDQCoh_shift {Y : Scheme.{u}}
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) (n : ℤ) :
    Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) (K⟦n⟧) :=
  DerivedCategoryB.derivedCategoryB_shift_mem
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre Y) n hK


/-- **The shift of a coproduct is the coproduct of the shifts.**  The shift by `n` is an
equivalence of the derived category, hence preserves every coproduct that exists. -/
def sigmaShiftIso {Y : Scheme.{u}} {I : Type u}
    (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    [HasCoproduct Z] (n : ℤ) [HasCoproduct (fun i => (Z i)⟦n⟧)] :
    (∐ Z)⟦n⟧ ≅ ∐ (fun i => (Z i)⟦n⟧) :=
  Limits.PreservesCoproduct.iso (shiftFunctor
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) n) Z


section Assembly

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- The property the dévissage is run on: invertibility of the projection-formula morphism at
`K` **and at every shift of `K`**.  Taking all shifts is what makes the plain two-out-of-three
hypothesis of [Stacks, Tag 09PB] provable; see the implementation notes. -/
private abbrev AllShifts
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) : Prop :=
  ∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (K⟦n⟧))

/-- **[Stacks, Tag 08EU] over an affine base, from the dévissage principle and the coproduct
step.**  The triangle step is supplied here from
`Stacks.Cohomology.ProjectionFormulaTriangles.isIso_projectionFormulaMap_triangle` through `htr`,
and the base case from
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitShift_unconditional`,
which is already a theorem.  What is still assumed is `hdev`, the dévissage principle for
`D_QCoh` over an affine base, and `hsig`, the coproduct step for the projection-formula
morphism. -/
theorem isIso_projectionFormulaMap_of_isDQCoh_of_isAffine_of_devissage
    [QuasiCompact f] [QuasiSeparated f] [IsAffine Y]
    (hdev :
      ∀ (T : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) → Prop),
      (∀ {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))},
        (A ≅ B) → T A → T B) →
      (∀ {I : Type u}
        (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
        [HasCoproduct Z],
        (∀ i, Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) (Z i)) →
        (∀ i, T (Z i)) → T (∐ Z)) →
      (∀ Δ : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))),
        Δ ∈ distinguishedTriangles →
          (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ m : ℤ, T ((singleUnit Y.toRingedSpace)⟦m⟧)) →
      ∀ K', Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K' → T K')
    (hsig : ∀ {I : Type u}
      (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
      [HasCoproduct Z],
      (∀ i, Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) (Z i)) →
      (∀ i, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (Z i))) →
      IsIso (projectionFormulaMap f.toLRSHom.toShHom E (∐ Z)))
    (htr : ∀ (T : Triangle
        (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))),
      T ∈ distinguishedTriangles →
      ((∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₁⟦n⟧))) →
        (∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₂⟦n⟧))) →
        ∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₃⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₁⟦n⟧))) →
        (∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₂⟦n⟧))) ∧
      ((∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₂⟦n⟧))) →
        (∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₃⟦n⟧))) →
        ∀ n : ℤ, IsIso (projectionFormulaMap f.toLRSHom.toShHom E (T.obj₁⟦n⟧))))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) := by
  have key : AllShifts f E K := by
    refine hdev (AllShifts f E) (fun {A B} e hA n =>
        isIso_projectionFormulaMap_of_iso_right _ _ ((shiftFunctor _ n).mapIso e) (hA n))
      (fun {I} Z _ hZ hT n => ?_) (fun Δ hΔ => htr Δ hΔ) (fun m n => ?_) K hK
    · refine isIso_projectionFormulaMap_of_iso_right _ _ (sigmaShiftIso Z n).symm ?_
      exact hsig _ (fun i => isDQCoh_shift (Z i) (hZ i) n) (fun i => hT i n)
    · refine isIso_projectionFormulaMap_of_iso_right _ _
        ((shiftFunctorAdd' (DerivedCategory
          (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) m n (m + n) rfl).app
            (singleUnit Y.toRingedSpace)) ?_
      exact isIso_projectionFormulaMap_unitShift_unconditional _ _ (m + n)
  refine isIso_projectionFormulaMap_of_iso_right _ _
    ((shiftFunctorZero (DerivedCategory
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) ℤ).app K) (key 0)

end Assembly


section Chain

/-- **The whole of [Stacks, Tag 08EU], conditional on exactly two named inputs.**

For a quasi-compact and quasi-separated morphism of schemes `f : X ⟶ Y`, `E ∈ D_QCoh(𝒪_X)` and
`K ∈ D_QCoh(𝒪_Y)`, the projection-formula morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism — granted `hdev` and `hsig`.  The statement is the source's, with no added
hypothesis on `f`, `E` or `K` and no stand-in: the two assumptions are the two steps of the
source's own dévissage that this development does not yet have, each stated uniformly in the
geometric data so that the localization of
`ProjectionFormulaQCohLocalization.isIso_projectionFormulaMap_of_isDQCoh_of_affineBase`
can apply them to the base change it produces.

Because `hdev` and `hsig` are hypotheses, this declaration does **not** state [Stacks, Tag 08EU]
and does not carry its attribute. -/
theorem isIso_projectionFormulaMap_of_isDQCoh_of_devissage
    (hdev : ∀ (Y' : Scheme.{u}), IsAffine Y' →
      ∀ (T : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) → Prop),
      (∀ {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace))},
        (A ≅ B) → T A → T B) →
      (∀ {I : Type u}
        (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)))
        [HasCoproduct Z],
        (∀ i, Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y'.toRingedSpace) (Z i)) →
        (∀ i, T (Z i)) → T (∐ Z)) →
      (∀ Δ : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace))),
        Δ ∈ distinguishedTriangles →
          (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ m : ℤ, T ((singleUnit Y'.toRingedSpace)⟦m⟧)) →
      ∀ K', Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y'.toRingedSpace) K' → T K')
    (hsig : ∀ (X' Y' : Scheme.{u}) (f' : X' ⟶ Y'), QuasiCompact f' → QuasiSeparated f' →
      ∀ (E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))),
      Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X'.toRingedSpace) E' →
      ∀ {I : Type u}
        (Z : I → DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)))
        [HasCoproduct Z],
        (∀ i, Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y'.toRingedSpace) (Z i)) →
        (∀ i, IsIso (projectionFormulaMap f'.toLRSHom.toShHom E' (Z i))) →
        IsIso (projectionFormulaMap f'.toLRSHom.toShHom E' (∐ Z)))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace) E)
    (hK : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing Y.toRingedSpace) K) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom E K) :=
  ProjectionFormulaQCohLocalization.isIso_projectionFormulaMap_of_isDQCoh_of_affineBase
    (fun X' Y' f' hqc hqs haf E' K' hE' hK' =>
      @isIso_projectionFormulaMap_of_isDQCoh_of_isAffine_of_devissage _ _ f' E' hqc hqs haf
        (hdev Y' haf) (hsig X' Y' f' hqc hqs E' hE')
        (fun T hT =>
          Stacks.Cohomology.ProjectionFormulaTriangles.isIso_projectionFormulaMap_triangle
            f'.toLRSHom.toShHom E' T hT) K' hK')
    f E K hE hK

end Chain

end Stacks.Cohomology.ProjectionFormulaQCohDevissage

end

end
