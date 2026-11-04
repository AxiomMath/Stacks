module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic

/-!
# The inclusion of `D(QCoh(𝒪_X))` into `D(𝒪_X)` lands in `D_QCoh(𝒪_X)`

Stacks 06Z0 asserts, for `X = Spec A`, that the functor `(06VT)` of that lemma — the functor
`D(QCoh(𝒪_X)) ⥤ D(𝒪_X)` induced by the inclusion of the quasi-coherent modules, which is
`Stacks.DerivedQCoh.derivedQCohι` — is an equivalence onto the objects satisfying
`Stacks.DerivedQCoh.IsDQCoh`. `StacksFrontier/AlgebraicGeometry/DerivedQCoh/Basic.lean` records that
assertion as the remaining content of the tag beyond the `~` edge
`Stacks.DerivedQCoh.derivedTildeEquiv`.

This file does two things. It proves the half of that assertion which needs no cohomology — that
the essential image of `derivedQCohι` is *contained* in the objects satisfying `IsDQCoh`, so that
"equivalence onto the `IsDQCoh` objects" is a statement about a functor already known to land
there. And it isolates the remaining half as a single named condition,
`Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`, from which the identification that the proof of
Stacks 09VF consumes — every object of `D_QCoh(𝒪_{Spec A})` is the complex of quasi-coherent
sheaves associated to an object of `D(A)` — is derived here.

## Main definitions

* `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh A` is the remaining content of Stacks 06Z0 for the
  functor `(06VT)`: `Stacks.DerivedQCoh.derivedQCohι` is full, is faithful, and has essential
  image exactly the objects satisfying `Stacks.DerivedQCoh.IsDQCoh`.

## Main results

* `Stacks.DerivedQCoh.isDQCoh_derivedQCohι_obj`: every object in the image of
  `Stacks.DerivedQCoh.derivedQCohι` satisfies `Stacks.DerivedQCoh.IsDQCoh`. This is the
  containment half of `IsEquivalenceOntoDQCoh`, and it is unconditional.
* `Stacks.DerivedQCoh.isDQCoh_of_essImage_derivedQCohι`: the same statement for an object merely
  isomorphic to one in the image, which is the `essImage` half of `IsEquivalenceOntoDQCoh`.
* `Stacks.DerivedQCoh.exists_iso_derivedTilde_of_isDQCoh`: granted the essential-surjectivity
  half, every object of `D_QCoh(𝒪_{Spec A})` is isomorphic to the image under `derivedQCohι` of
  the object of `D(QCoh(𝒪_{Spec A}))` attached by `derivedTildeEquiv` to an object of `D(A)`.
* `Stacks.DerivedQCoh.isDQCoh_iff_exists_iso_derivedTilde`: the same as a characterisation of
  `IsDQCoh`, whose reverse implication needs none of Stacks 06Z0.

## Implementation notes

**What is proved and what is not.** `IsEquivalenceOntoDQCoh` carries no `stacks` attribute and is
not proved. The source proves it from Serre vanishing on an affine scheme (Stacks 01XB) through
the finite-cohomological-dimension criterion of Stacks 08D4; Stacks 01XB is not formalized in this
library in any cohomology model, and the Čech input to it that *is* formalized —
`AlgebraicGeometry.isZero_cechCohomology_of_isStandardOpenCover` (Stacks 01X9) together with the
cofinality results of
`StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverCofinality` — is separated from it by
Stacks 01EW, which is not formalized either. So the condition is stated, the half of it that is
formal is discharged, and the consumer step is proved from the rest.

It is worth recording why the general theorem
`CategoryTheory.ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory` (Stacks 0FCL) does
not discharge this condition, since its conclusion is of exactly this shape. Besides asking for a
Serre class — closure of the quasi-coherent modules under extensions, which is not available here
— it asks that every epimorphism with quasi-coherent target be hit by a quasi-coherent object.
On `Spec A` every quasi-coherent module is `M^~` for an `A`-module `M`, and `(-)^~` is left
adjoint to global sections, so a morphism `N^~ ⟶ ℱ` is an `A`-linear map `N ⟶ Γ(X, ℱ)` and the
composite `N^~ ⟶ ℱ ⟶ M^~` is epi exactly when `N ⟶ Γ(X, ℱ) ⟶ M` is surjective. The hypothesis is
therefore *equivalent* to surjectivity of global sections on epimorphisms onto quasi-coherent
modules, which is Serre vanishing in degree one. The general theorem is not a cheaper route; it
needs the same input.

**The comparison of homology.** The containment is proved by comparing the cohomology objects of
`derivedQCohι` with those of its argument. The isomorphism `Hⁿ ∘ D(F) ≅ F ∘ Hⁿ` for an exact
functor `F` is derived inline rather than cited: the repository has it in a dozen places, each
either specialised to module categories or `private` to its file —
`StacksFrontier/Homology/PseudoCoherent/Basic.lean`'s `mapDerivedCategoryHomologyIso` and
`StacksFrontier/Algebra/Homology/DerivedCategory/SerreSubcategory.lean`'s
`mapDerivedCategoryCompHomologyFunctorIso` among them — and no public general form exists. Making
one of those public would be the right fix; importing either file here is not, since both carry
import closures far larger than this module's. A repository-tier deduplication pass should lift
one general copy out and delete the rest.

**Universes.** The derived categories are hypotheses, with `D(A)` and `D(𝒪_{Spec A})` sharing one
universe parameter and `D(QCoh(𝒪_{Spec A}))` carrying its own, exactly as in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/Basic.lean`, so that the statements here compose with
the ones there without transport.

## References

* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Section 36.3 (06VT)](https://stacks.math.columbia.edu/tag/06VT)
* [The Stacks Project, Lemma 30.2.2 (01XB)](https://stacks.math.columbia.edu/tag/01XB)
* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry

universe w w' u₁ v₁ u₂ v₂ u

namespace Stacks.DerivedQCoh

section Exact

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₁] [Abelian C₂] [HasDerivedCategory.{w} C₁] [HasDerivedCategory.{w'} C₂]

/-- For an exact functor `F : C₁ ⥤ C₂`, the cohomology objects of `D(F) X` are the images under
`F` of those of `X`: `Hⁿ ∘ D(F) ≅ F ∘ Hⁿ`.

Both sides invert quasi-isomorphisms, so the isomorphism is obtained from the complex-level one —
`CategoryTheory.ShortComplex.mapHomologyIso`, the statement that an exact functor commutes with
the homology of a short complex — by descending along the localisation
`CategoryTheory.DerivedCategory.Q`. It is the general form of a result the repository currently
holds only in specialised or `private` copies; see the implementation notes of this file. -/
private def derivedHomologyCommIso (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n ≅
      DerivedCategory.homologyFunctor C₁ n ⋙ F :=
  letI e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) n ⋙ F :=
    NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun φ ↦
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor C₁ (ComplexShape.up ℤ) n).map φ) F)
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C₁ n ⋙ F)) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor C₂ n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors C₂ n) ≪≫ e ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C₁ n).symm F)

end Exact

section Affine

variable (A : CommRingCat.{u})
  [HasDerivedCategory.{w'}
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (Spec A).ringCatSheaf)]

/-- **The functor (06VT) of Stacks 06Z0 lands in `D_QCoh(𝒪_X)`.** Every object of
`D(QCoh(𝒪_{Spec A}))` is carried by `Stacks.DerivedQCoh.derivedQCohι` to an object of
`D(𝒪_{Spec A})` all of whose cohomology sheaves are quasi-coherent.

This is the half of "`derivedQCohι` is an equivalence onto the objects satisfying
`Stacks.DerivedQCoh.IsDQCoh`" that needs no cohomology: the inclusion of the quasi-coherent
modules is exact, so it commutes with cohomology, and the cohomology objects of
`D(QCoh(𝒪_{Spec A}))` are quasi-coherent by construction. -/
theorem isDQCoh_derivedQCohι_obj (F : DerivedCategory
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory) :
    IsDQCoh (R := (Spec A).ringCatSheaf) ((derivedQCohι A).obj F) := fun i ↦
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    ((derivedHomologyCommIso
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)) i).app F).symm
    ((DerivedCategory.homologyFunctor _ i).obj F).2

/-- **The essential image of the functor (06VT) of Stacks 06Z0 is contained in `D_QCoh(𝒪_X)`.**
An object of `D(𝒪_{Spec A})` isomorphic to one in the image of
`Stacks.DerivedQCoh.derivedQCohι` has all its cohomology sheaves quasi-coherent.

This is `Stacks.DerivedQCoh.isDQCoh_derivedQCohι_obj` together with
`Stacks.DerivedQCoh.isDQCoh_of_iso`, and it is the forward implication of the essential-image
clause of `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`. -/
theorem isDQCoh_of_essImage_derivedQCohι
    {E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf)}
    (hE : (derivedQCohι A).essImage E) : IsDQCoh (R := (Spec A).ringCatSheaf) E := by
  obtain ⟨F, ⟨e⟩⟩ := hE
  exact isDQCoh_of_iso (R := (Spec A).ringCatSheaf) e (isDQCoh_derivedQCohι_obj A F)

/-- **The remaining content of Stacks 06Z0 for the functor (06VT).** The functor
`Stacks.DerivedQCoh.derivedQCohι : D(QCoh(𝒪_{Spec A})) ⥤ D(𝒪_{Spec A})` is full, is faithful, and
has essential image exactly the objects satisfying `Stacks.DerivedQCoh.IsDQCoh`; that is, it is an
equivalence onto `D_QCoh(𝒪_{Spec A})`.

This is stated as an abbreviation, not proved, and carries no `stacks` attribute. The forward
implication of the essential-image clause is
`Stacks.DerivedQCoh.isDQCoh_of_essImage_derivedQCohι` and holds unconditionally; what is missing
is fullness, faithfulness and essential surjectivity, for which the source uses Serre vanishing
on an affine scheme. See the module documentation for why the general theorem
`CategoryTheory.ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory` does not supply
it. -/
abbrev IsEquivalenceOntoDQCoh : Prop :=
  (derivedQCohι A).Full ∧ (derivedQCohι A).Faithful ∧
    ∀ E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf),
      (derivedQCohι A).essImage E ↔ IsDQCoh (R := (Spec A).ringCatSheaf) E

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **An object of `D(A)` gives an object of `D_QCoh(𝒪_{Spec A})`.** The complex of quasi-coherent
sheaves attached to an object of `D(A)` by the `~` edge
`Stacks.DerivedQCoh.derivedTildeEquiv` of Stacks 06Z0, read in `D(𝒪_{Spec A})` through
`Stacks.DerivedQCoh.derivedQCohι`, has all its cohomology sheaves quasi-coherent.

This is `Stacks.DerivedQCoh.isDQCoh_derivedQCohι_obj` at the object `M^~`, and it is the
direction of `Stacks.DerivedQCoh.isDQCoh_iff_exists_iso_derivedTilde` that needs none of the
unproved content of Stacks 06Z0. -/
theorem isDQCoh_derivedTilde_obj (M : DerivedCategory (ModuleCat.{u} A)) :
    IsDQCoh (R := (Spec A).ringCatSheaf)
      ((derivedQCohι A).obj ((derivedTildeEquiv A).functor.obj M)) :=
  isDQCoh_derivedQCohι_obj A _

/-- **The affine identification of Stacks 06Z0, granted its essential-surjectivity half.** Let
`E` be an object of `D(𝒪_{Spec A})` all of whose cohomology sheaves are quasi-coherent. If the
functor `Stacks.DerivedQCoh.derivedQCohι` hits every such object, then `E` is isomorphic to the
complex of quasi-coherent sheaves attached to an object `M` of `D(A)`.

This is the identification the proof of Stacks 09VF uses on an affine open: there `M` is
`RΓ(U, E)`, and identifying it as such is a further part of Stacks 06Z0 — the one that needs the
derived sections functor — which is not supplied here. The hypothesis is the essential
surjectivity clause of `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`, taken alone: neither fullness
nor faithfulness is used. -/
theorem exists_iso_derivedTilde_of_isDQCoh
    (hess : ∀ E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf),
      IsDQCoh (R := (Spec A).ringCatSheaf) E → (derivedQCohι A).essImage E)
    {E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf)}
    (hE : IsDQCoh (R := (Spec A).ringCatSheaf) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} A),
      Nonempty ((derivedQCohι A).obj ((derivedTildeEquiv A).functor.obj M) ≅ E) := by
  obtain ⟨F, ⟨e⟩⟩ := hess E hE
  exact ⟨(derivedTildeEquiv A).inverse.obj F,
    ⟨(derivedQCohι A).mapIso ((derivedTildeEquiv A).counitIso.app F) ≪≫ e⟩⟩

/-- **`D_QCoh(𝒪_{Spec A})` consists of the complexes attached to objects of `D(A)`, granted the
essential-surjectivity half of Stacks 06Z0.** An object of `D(𝒪_{Spec A})` has all its cohomology
sheaves quasi-coherent exactly when it is isomorphic to the complex of quasi-coherent sheaves
attached to an object of `D(A)` by the `~` edge of Stacks 06Z0.

The reverse implication is `Stacks.DerivedQCoh.isDQCoh_derivedTilde_obj` and is unconditional;
only the forward one uses the hypothesis. -/
theorem isDQCoh_iff_exists_iso_derivedTilde
    (hess : ∀ E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf),
      IsDQCoh (R := (Spec A).ringCatSheaf) E → (derivedQCohι A).essImage E)
    (E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf)) :
    IsDQCoh (R := (Spec A).ringCatSheaf) E ↔
      ∃ M : DerivedCategory (ModuleCat.{u} A),
        Nonempty ((derivedQCohι A).obj ((derivedTildeEquiv A).functor.obj M) ≅ E) := by
  refine ⟨exists_iso_derivedTilde_of_isDQCoh A hess, ?_⟩
  rintro ⟨M, ⟨e⟩⟩
  exact isDQCoh_of_essImage_derivedQCohι A ⟨_, ⟨e⟩⟩

end Affine

end Stacks.DerivedQCoh

end
