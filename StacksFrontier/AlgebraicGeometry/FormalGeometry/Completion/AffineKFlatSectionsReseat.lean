module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineKFlatSectionsBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineSectionsSiteComparison
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse

/-!
# The sections spelling of the two K-flatness inputs of the affine projection formula

`Completion/AffineKFlatSectionsBridge.lean` proves both K-flatness inputs of the affine
projection formula

`RΓ(V, K ⊗^𝐋_{𝒪_X} M) ≅ RΓ(V, K) ⊗^𝐋_{Γ(X, V)} Γ(M, V)`

at one representative, but in the *wrong ring*: its K-flatness statement
`Stacks.Algebraization.kFlat_tildeΓComplex` is about
`AlgebraicGeometry.moduleSpecΓFunctor`, which lands in `ModuleCat R` because it has absorbed
the isomorphism `Γ(Spec R, ⊤) ≅ R`, whereas the affine section formula
`Stacks.SectionTensorFormula.sectionsTensorComplexIso` is written over `Γ(X, V)` on the nose.
That file records the reseating as the first of the two things it does not do. This file does it.

## The reseat is definitional, and that is the whole point

`AlgebraicGeometry.moduleSpecΓFunctor` is *by definition* evaluation at `⊤` followed by
restriction of scalars along `(AlgebraicGeometry.Scheme.ΓSpecIso R).inv`:

`moduleSpecΓFunctor = schemeSectionsOver ⊤ ⋙ ModuleCat.restrictScalars (ΓSpecIso R).inv.hom`

holds by `rfl`, and cheaply — the `whnf` blow-up that
`Completion/AffineKFlatSectionsBridge.lean` documents happens when the *degreewise* application
of `Functor.mapHomologicalComplex` is unfolded through
`AlgebraicGeometry.SpecModulesToSheafFullyFaithful`, not when the two functors are compared.
So the reseat needs no geometry at all: restricting back along `(ΓSpecIso R).hom` cancels the
absorbed isomorphism (`Stacks.Algebraization.specTopRestrictCancel`), and K-flatness survives a
restriction of scalars along a ring isomorphism by
`CochainComplex.DerivedTensor.isKFlat_restrictScalars_of_ringEquiv`.

Both statements below are therefore about one complex rather than about all of them, exactly as
the assembly route recorded in `Completion/CohomologyAffineAdicComparison.lean` predicted: no
K-flatness theorem about arbitrary sections functors is proved or needed.

## Main results

* `Stacks.Algebraization.specTopSectionsReseatIso` — `Γ(Spec R, -)` as a functor to `ModuleCat R`,
  restricted back along `Γ(Spec R, ⊤) ≅ R`, is the sections functor at `⊤` over `Γ(Spec R, ⊤)`.
* `Stacks.Algebraization.tildeSectionsComplexIso` — `Γ(Spec R, P̃) ≅ P` as complexes of
  `Γ(Spec R, ⊤)`-modules, `P` reseated along the same isomorphism.
* `Stacks.Algebraization.kFlat_sections_tildeComplex` — hence `Γ(Spec R, P̃)` is K-flat **over
  `Γ(Spec R, ⊤)`**.
* `Stacks.Algebraization.exists_kFlat_tilde_sections_kFlat_isQuasicoherent_iso` — the three
  inputs of the affine projection formula at one representative, in the rings and spellings the
  formula is written in.

## What is still owed

The transport to an affine **open** `V` of a general scheme, along
`AlgebraicGeometry.IsAffineOpen.isoSpec`, which is where part (2) of [Stacks, Tag 0A0K] needs
this. `AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec` is the identification
`RΓ(Spec Γ(X, V), E|_V) ≅ RΓ(V, E)` it would go through, and that statement is `Nonempty` and
explicitly *not* claimed natural in `E` — so it cannot by itself carry an isomorphism of the
adic tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ`, which is the only form part (2) consumes. A naturality upgrade
is available in principle, both sides being total right derived functors of isomorphic functors
with a restriction that preserves K-injectives
(`AlgebraicGeometry.Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_ι`), so
`CategoryTheory.Functor.rightDerivedNatIso` applies; it is not carried out here.

Nothing here is registered against any tag: these are restatements of results already in the
library, not statements of the source.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard

variable (R : CommRingCat.{u})

/-- **The two restrictions of scalars along the two directions of `Γ(Spec R, ⊤) ≅ R` cancel.**
Restriction of scalars along a composite is the composite of the restrictions
(`ModuleCat.restrictScalarsComp'`), and the composite here is the identity ring map. -/
public def specTopRestrictCancel :
    ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).inv.hom ⋙
        ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).hom.hom ≅
      𝟭 (ModuleCat.{u} Γ(Spec R, ⊤)) :=
  (ModuleCat.restrictScalarsComp'.{u} (Scheme.ΓSpecIso R).hom.hom
      (Scheme.ΓSpecIso R).inv.hom (RingHom.id Γ(Spec R, ⊤))
      (by
        ext x
        simp)).symm ≪≫
    ModuleCat.restrictScalarsId.{u} Γ(Spec R, ⊤)

/-- **`AlgebraicGeometry.moduleSpecΓFunctor`, reseated over `Γ(Spec R, ⊤)`, is the sections
functor at `⊤`.** The global sections functor of Mathlib's tilde–Gamma adjunction lands in
`ModuleCat R`, having absorbed `Γ(Spec R, ⊤) ≅ R`; restricting scalars back along that
isomorphism recovers `Stacks.Algebraization.schemeSectionsOver ⊤`, the spelling
`Stacks.SectionTensorFormula.sectionsTensorComplexIso` is written in.

The identity
`moduleSpecΓFunctor = schemeSectionsOver ⊤ ⋙ ModuleCat.restrictScalars (ΓSpecIso R).inv.hom`
holds by `rfl`, so the content is only the cancellation
`Stacks.Algebraization.specTopRestrictCancel`. -/
public def specTopSectionsReseatIso :
    moduleSpecΓFunctor (R := R) ⋙
        ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).hom.hom ≅
      schemeSectionsOver (X := Spec R) ⊤ :=
  Functor.isoWhiskerLeft (schemeSectionsOver (X := Spec R) ⊤) (specTopRestrictCancel R) ≪≫
    Functor.rightUnitor _

variable (P : CochainComplex (ModuleCat.{u} R) ℤ)

/-- **`Γ(Spec R, P̃) ≅ P` as complexes of `Γ(Spec R, ⊤)`-modules.** This is
`Stacks.Algebraization.tildeΓComplexIso`, which is an isomorphism of complexes of `R`-modules,
carried over `Γ(Spec R, ⊤)` by `Stacks.Algebraization.specTopSectionsReseatIso`.

Every spelling below is a *composite* functor applied degreewise, never
`moduleSpecΓFunctor.mapHomologicalComplex` applied to `AlgebraicGeometry.tildeComplexMod P`, for
the reason `Completion/AffineKFlatSectionsBridge.lean` records: the latter exhausts the heartbeat
budget at `whnf`. -/
public def tildeSectionsComplexIso :
    ((schemeSectionsOver (X := Spec R) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (AlgebraicGeometry.tildeComplexMod P) ≅
      ((ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).hom.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor R ⋙ schemeSectionsOver (X := Spec R) ⊤))
      (ComplexShape.up ℤ)).app P ≪≫
    ((NatIso.mapHomologicalComplex
      (Functor.isoWhiskerLeft (tilde.functor R) (specTopSectionsReseatIso R))
      (ComplexShape.up ℤ)).app P).symm ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl ((tilde.functor R ⋙ moduleSpecΓFunctor) ⋙
        ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).hom.hom))
      (ComplexShape.up ℤ)).app P).symm ≪≫
    ((ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).hom.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (tildeΓComplexIso R P)

/-- **`Γ(Spec R, P̃)` is K-flat over `Γ(Spec R, ⊤)` when `P` is K-flat over `R`.** This is
`Stacks.Algebraization.kFlat_tildeΓComplex` over the ring the affine projection formula is
written over rather than over `R`: `P` reseated along `Γ(Spec R, ⊤) ≅ R` stays K-flat by
`CochainComplex.DerivedTensor.isKFlat_restrictScalars_of_ringEquiv`, and K-flatness transports
along `Stacks.Algebraization.tildeSectionsComplexIso` by `CochainComplex.kFlat_of_iso`. -/
public theorem kFlat_sections_tildeComplex (hP : CochainComplex.KFlat.{u, u} P) :
    CochainComplex.KFlat.{u, u}
      (((schemeSectionsOver (X := Spec R) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (AlgebraicGeometry.tildeComplexMod P)) :=
  CochainComplex.kFlat_of_iso (tildeSectionsComplexIso R P).symm
    (CochainComplex.DerivedTensor.isKFlat_restrictScalars_of_ringEquiv
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv P hP)

/-- **The three inputs of the affine projection formula at one representative, in the rings the
formula is written in.** Every object of `D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves
is the class of `P̃` for a complex `P` of `R`-modules with

* `P̃` K-flat as a complex of `𝒪_{Spec R}`-modules — what
  `Stacks.Algebraization.derivedTensorSingleIsoRowComplex` consumes;
* every term of `P̃` quasi-coherent — what `Stacks.SectionTensorFormula.sectionsTensorComplexIso`
  and `Stacks.Algebraization.homologySectionsIsoOfIsAffineOpen` consume;
* `Γ(Spec R, P̃)` K-flat **over `Γ(Spec R, ⊤)`** — what the recognition of the resulting
  degreewise tensor product of sections as a derived tensor product consumes.

This is `Stacks.Algebraization.exists_kFlat_tilde_isKFlat_isQuasicoherent_iso` with its
module-side K-flatness replaced by the sections-side K-flatness it implies, by
`Stacks.Algebraization.kFlat_sections_tildeComplex`.

No finiteness, pseudo-coherence or boundedness is assumed or asserted. -/
public theorem exists_kFlat_tilde_sections_kFlat_isQuasicoherent_iso
    (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      _root_.Stacks.SheafOfModules.IsKFlat (AlgebraicGeometry.specCommRingSheaf R)
        (AlgebraicGeometry.tildeComplexMod P) ∧
      (∀ i : ℤ, ((AlgebraicGeometry.tildeComplexMod P).X i).IsQuasicoherent) ∧
      CochainComplex.KFlat.{u, u}
        (((schemeSectionsOver (X := Spec R) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (AlgebraicGeometry.tildeComplexMod P)) ∧
      Nonempty ((DerivedCategory.Q.obj (AlgebraicGeometry.tildeComplexMod P) :
        DerivedCategory (Spec R).Modules) ≅ E) := by
  obtain ⟨P, hP, hKF, hqc, he⟩ := exists_kFlat_tilde_isKFlat_isQuasicoherent_iso R E hE
  exact ⟨P, hKF, hqc, kFlat_sections_tildeComplex R P hP, he⟩

end Stacks.Algebraization

end
