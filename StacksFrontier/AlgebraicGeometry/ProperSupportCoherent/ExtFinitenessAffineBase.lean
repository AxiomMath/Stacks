module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DegreeZeroCohomology
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero

/-!
# Finiteness of degree-zero derived global sections over an affine Noetherian base

Let `A` be a Noetherian ring and let `N` be an object of `D(𝒪_{Spec A})` whose cohomology sheaves
are all quasi-coherent and whose degree-zero cohomology sheaf is coherent. This file proves that
`H⁰(RΓ(Spec A, N))` is a **finite** `A`-module. It is the affine input of [Stacks, Tag 0D0D]: the
step that turns coherence of a cohomology sheaf on the base into finiteness of a module of
cohomology over the base ring.

The argument has two halves. The first is condition (4) of [Stacks, Tag 01XZ] on the base itself:
a coherent module on `Spec A` is the associated sheaf of its global sections and is of finite
type, so those global sections are a finite `A`-module. The second is the degree-zero clause of
[Stacks, Tag 06Z0]: on an affine scheme the degree-zero cohomology of derived global sections is
the global sections of the degree-zero cohomology sheaf.

## Main results

* `Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_moduleSpecΓ_of_isCoherent`:
  a coherent module on the spectrum of a Noetherian ring has finite global sections.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_homologyZero_derivedGlobalSections`:
  the finiteness of `H⁰(RΓ(Spec A, N))`.

## Implementation notes

**The degree-zero clause of [Stacks, Tag 06Z0] is rebuilt here at the standard model, and that is
the only reason this file contains any derived-category construction.**
`AlgebraicGeometry.derivedGlobalSectionsHomologyZeroIso` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/DegreeZeroCohomology.lean` states exactly the
comparison used below, but that file carries no `HasDerivedCategory` binder, so the declaration is
baked at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose
morphisms live in `Type u`. The derived category of [Stacks, Tag 0D0B] — and so of every consumer
in this directory — is `CategoryTheory.HasDerivedCategory.standard`, whose morphisms live in
`Type (u + 1)`. The two categories are equivalent and not equal, so no statement about one is a
statement about the other: citing
`AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso` where
`homologyDerivedGlobalSectionsIsoStandard` is used below fails with

```
Application type mismatch: the argument E has type
  ObjectProperty.FullSubcategory.{u + 1, u + 1} (DerivedCategoryB.derivedCategoryB …)
but is expected to have type
  ObjectProperty.FullSubcategory.{u, u + 1} (DerivedCategoryB.derivedCategoryB …)
```

and no import or `attribute [local instance] HasDerivedCategory.standard` at the use site can
bridge that, the instance being fixed inside the cited declaration rather than taken as a binder;
the same obstruction is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/FiniteCohomology.lean`, which works around it by passing
through a representing cochain complex.

Here it is removed instead of worked around: every input of that comparison is already stated at
free `[HasDerivedCategory.{w} _]` binders — `AlgebraicGeometry.derivedTildeFactors`,
`CategoryTheory.DerivedCategory.homologyFunctorFactors`,
`AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` — or mentions no derived category at all,
`AlgebraicGeometry.tildeHomologyGlobalSectionsIso` being an isomorphism of functors on cochain
complexes. So the two-step descent of that file (`CategoryTheory.Localization.liftNatIso` of the
complex-level isomorphism, then transport along the counit of the derived Spec–Γ adjunction) is
repeated below with the standard model pinned, the counit being invertible by
`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence`. The three private declarations
`derivedTildeHomologyGlobalSectionsIsoStandardAux`,
`derivedTildeHomologyGlobalSectionsIsoStandard` and `homologyDerivedGlobalSectionsIsoStandard`
carry no tag: they are the locally small file's mathematics at another model, not new content, and
[Stacks, Tag 06Z0] is tagged there.

**`attribute [local instance 10000]`, not the plain attribute.** The import closure reaches
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, whose `HasDerivedCategory` declarations are
*global* instances; a default-priority local attribute loses to them, and the file would then
silently be about the locally small model again.

**`moduleFinite_moduleSpecΓ_of_isCoherent` restates
`AlgebraicGeometry.moduleFinite_moduleSpecΓ_of_isCoherent` of
`StacksFrontier/AlgebraicGeometry/DeRham/FiniteCohomology.lean`** for a bare commutative ring rather
than a bundled one, with a shorter proof and without that file's import cone. Whoever merges the
two should keep the `{A : Type u} [CommRing A]` spelling, which is the one the consumers of
[Stacks, Tag 0D0D] use.

## References

* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0D0B](https://stacks.math.columbia.edu/tag/0D0B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The degree-zero clause of Stacks 06Z0 at the standard model -/

section Affine

variable (R : CommRingCat.{u})

/-- `E ↦ Γ(Spec R, Hⁿ(E))` on the complexes with quasi-coherent cohomology sheaves: the
right-hand side of the degree-`n` clause of [Stacks, Tag 06Z0]. Naming it keeps the three
comparisons below readable, their statements otherwise repeating it three times. -/
private abbrev qcohHomologySections (n : ℤ) :
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory ⥤
      ModuleCat.{u} R :=
  (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ⋙
      DerivedCategory.homologyFunctor (Spec R).Modules n ⋙ globalSectionsOver (𝟙 (Spec R))

/-- `derivedTildeHomologyGlobalSectionsIsoStandard` precomposed with the localization functor,
which is the shape `CategoryTheory.Localization.liftNatIso` consumes. This is
`AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIsoAux` at the standard model. -/
private def derivedTildeHomologyGlobalSectionsIsoStandardAux (n : ℤ) :
    DerivedCategory.Q ⋙ (derivedTilde R ⋙ qcohHomologySections R n) ≅
      DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n :=
  Functor.isoWhiskerLeft DerivedCategory.Q (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedTildeFactors R)
      (DerivedCategory.homologyFunctor (Spec R).Modules n ⋙ globalSectionsOver (𝟙 (Spec R))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ))
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors (Spec R).Modules n)
          (globalSectionsOver (𝟙 (Spec R)))) ≪≫
    tildeHomologyGlobalSectionsIso R n ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).symm

/-- **The cohomology of derived global sections at an object of the form `M^~`, at the standard
model.** For an object `M` of `D(R)` the global sections of the degree-`n` cohomology sheaf of
`M^~` is `Hⁿ(M)`. This is `AlgebraicGeometry.derivedTildeCompHomologyGlobalSectionsIso` at the
standard model. -/
private def derivedTildeHomologyGlobalSectionsIsoStandard (n : ℤ) :
    derivedTilde R ⋙ qcohHomologySections R n ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) n :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (derivedTilde R ⋙ qcohHomologySections R n))
    (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) n) _ _
    (h₁ := Localization.Lifting.compLeft _ _ _) (h₂ := Localization.Lifting.compLeft _ _ _)
    (derivedTildeHomologyGlobalSectionsIsoStandardAux R n)

/-- **[Stacks, Tag 06Z0], the cohomology of derived global sections on an affine scheme, at the
standard model.** For an object `E` of `D_QCoh(𝒪_{Spec R})` the degree-`n` cohomology of
`RΓ(Spec R, E)` is the module of global sections of the degree-`n` cohomology sheaf of `E`,
naturally in `E`. This is
`AlgebraicGeometry.derivedGlobalSectionsQuasicoherentCompHomologyIso` at the standard model; see
the implementation notes for why it is rebuilt rather than cited. -/
private def homologyDerivedGlobalSectionsIsoStandard (n : ℤ) :
    derivedGlobalSectionsQuasicoherent R ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ≅
      qcohHomologySections R n :=
  Functor.isoWhiskerLeft (derivedGlobalSectionsQuasicoherent R)
      (derivedTildeHomologyGlobalSectionsIsoStandard R n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (StandardModel.derivedTildeQuasicoherentAdjunction R).counit) _ ≪≫
    Functor.leftUnitor _

end Affine

/-! ### Finiteness over the base ring -/

/-- A coherent module on the spectrum of a Noetherian ring has finite global sections. -/
theorem moduleFinite_moduleSpecΓ_of_isCoherent {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : (Spec (CommRingCat.of A)).Modules) (hM : M.IsCoherent) :
    Module.Finite A (AlgebraicGeometry.moduleSpecΓFunctor.obj M) := by
  obtain ⟨hqc, hft⟩ := CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M
  exact (AlgebraicGeometry.tilde_isFiniteType_iff
      (AlgebraicGeometry.moduleSpecΓFunctor.obj M)).mp
    (hft.of_iso (asIso M.fromTildeΓ).symm)

/-- On an affine Noetherian base, the degree-zero cohomology of derived global sections of a
complex with quasi-coherent cohomology sheaves whose degree-zero cohomology sheaf is coherent is
a finite module over the base ring. -/
theorem moduleFinite_homologyZero_derivedGlobalSections
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (N : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules i).obj
      N).IsQuasicoherent)
    (hcoh : ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules 0).obj
      N).IsCoherent) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((derivedGlobalSectionsOver (𝟙 (Spec (CommRingCat.of A)))).obj N)) := by
  let E : (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).FullSubcategory :=
    ⟨N, fun i => hqc i⟩
  have hfin : Module.Finite A (AlgebraicGeometry.moduleSpecΓFunctor.obj
      ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules 0).obj
        ((DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
          (SheafOfModules.isQuasicoherent
            (Spec (CommRingCat.of A)).ringCatSheaf)).ι.obj E))) :=
    moduleFinite_moduleSpecΓ_of_isCoherent _ hcoh
  exact Module.Finite.equiv
    (((moduleSpecΓIsoGlobalSectionsOver (CommRingCat.of A)).app _ ≪≫
      ((homologyDerivedGlobalSectionsIsoStandard (CommRingCat.of A) 0).app E).symm).toLinearEquiv)

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
