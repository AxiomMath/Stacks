module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineKFlatQuasicoherentResolution
public import StacksFrontier.Homology.KFlat.Closure

/-!
# Both K-flatness inputs of the affine projection formula, at one representative

`Completion/CohomologyAffineAdicComparison.lean` records two statements as missing from the
affine projection formula

`RΓ(V, K ⊗^𝐋_{𝒪_X} M) ≅ RΓ(V, K) ⊗^𝐋_{Γ(X, V)} Γ(M, V)`,

which is the whole of the affine-level gap in part (2) of [Stacks, Tag 0A0K]: a K-flat
representative of `K` with **quasi-coherent terms**, and **K-flatness of `Γ(V, E)`** over
`Γ(X, V)`. `Completion/AffineKFlatQuasicoherentResolution.lean` supplies the first on `Spec R`.
This file supplies the second **for the same representative**, and then packages the two together.

## Why the second one is not a theorem about arbitrary sections

The missing statement was recorded as "K-flatness of `Γ(V, E)` over `Γ(X, V)`, which is not
proved for any of the sections functors". Proved in that generality it would be a real theorem.
It does not have to be: the representative of
`Stacks.Algebraization.exists_isKFlat_isQuasicoherent_iso_of_isQuasicoherent_homology` is `P̃` for
a complex `P` of `R`-modules that is **already K-flat by construction**, and `Γ ∘ (-)^~` is
naturally the identity. So all that is owed is a `Γ ∘ tilde ≅ id` bridge at the level of
complexes, and Mathlib already has it in the only degree that matters:
`AlgebraicGeometry.tilde.toTildeΓNatIso`, the unit of the tilde–Gamma adjunction, is a **natural
isomorphism** `𝟭 (ModuleCat R) ≅ tilde.functor R ⋙ moduleSpecΓFunctor`. Applying it degreewise
is `Stacks.Algebraization.tildeΓComplexIso` below, and K-flatness then transports along it by
[Stacks, Tag 064K]'s closure lemma `CochainComplex.kFlat_of_iso`.

## Main results

* `Stacks.Algebraization.tildeΓComplexIso` — `Γ(Spec R, P̃) ≅ P` as complexes of `R`-modules.
* `Stacks.Algebraization.kFlat_tildeΓComplex` — hence `Γ(Spec R, P̃)` is K-flat when `P` is.
* `Stacks.Algebraization.exists_kFlat_tilde_isKFlat_isQuasicoherent_iso` — the two inputs at one
  representative: for every object of `D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves
  there is a complex `P` of `R`-modules which is K-flat, whose associated complex of sheaves `P̃`
  is K-flat with quasi-coherent terms, and whose class is the given object.

## What is still owed, and it is no longer a K-flatness statement

Two things, neither of them about K-flatness.

* The sections spelling. `AlgebraicGeometry.moduleSpecΓFunctor` lands in `ModuleCat R`, having
  absorbed `Γ(Spec R, ⊤) ≅ R`, whereas the affine section formula
  `Stacks.SectionTensorFormula.sectionsTensorComplexIso` is written with
  `Stacks.Cohomology.sectionsFunctor`, i.e. `SheafOfModules.evaluation` at the open, over the ring
  `Γ(X, V)` on the nose. Reseating along that ring isomorphism is
  `CochainComplex.isKFlat_restrictScalars_of_ringEquiv`; it is not done here.
* The transport to an affine **open** of a general scheme, along
  `AlgebraicGeometry.IsAffineOpen.isoSpec`, which is where part (2) needs all of this.
  `AlgebraicGeometry.affineDerivedSectionsPresentation` performs the analogous transport for
  pseudo-coherence and is the model.

Nothing here is registered against any tag.

## Implementation notes

**The spelling of the sections complex is forced by the heartbeat budget, not by taste.** The
statements below are written with the *composite* functor,
`(tilde.functor R ⋙ moduleSpecΓFunctor).mapHomologicalComplex`, and not with
`moduleSpecΓFunctor.mapHomologicalComplex` applied to `AlgebraicGeometry.tildeComplexMod P`. The
two are the same complex, but the second spelling does not elaborate: merely stating
`(moduleSpecΓFunctor.mapHomologicalComplex _).obj (tildeComplexMod P) ≅ P` exhausts the
200000-heartbeat budget at `whnf`, because `moduleSpecΓFunctor` is defined through
`AlgebraicGeometry.SpecModulesToSheafFullyFaithful` and unfolding the nested degreewise
application forces the unifier through it. In the composite spelling the same statement
elaborates in well under a second, and a single component
`moduleSpecΓFunctor.obj ((tilde.functor R).obj M) ≅ M` is cheap either way. A consumer that needs
the nested spelling should bridge the two functors once, by name, rather than let unification
attempt it.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard

variable (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ)

/-- **`Γ(Spec R, P̃) ≅ P`, as complexes of `R`-modules.** The global sections of the complex of
sheaves associated to a complex `P` of `R`-modules is `P` again.

In each degree this is `AlgebraicGeometry.tilde.isoTop`, and the differentials match because that
isomorphism is natural: `AlgebraicGeometry.tilde.toTildeΓNatIso` is the unit of the tilde–Gamma
adjunction of Mathlib and is a natural *isomorphism* `𝟭 ≅ tilde.functor R ⋙ moduleSpecΓFunctor`,
not merely a natural transformation.

The sections are spelled with the composite functor rather than as
`moduleSpecΓFunctor.mapHomologicalComplex` applied to `AlgebraicGeometry.tildeComplexMod P`; the
two are the same complex but the second spelling exhausts the heartbeat budget at `whnf`, as the
module documentation explains. -/
public def tildeΓComplexIso :
    ((tilde.functor R ⋙ moduleSpecΓFunctor).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅
      P :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (tilde.isoTop (P.X i)).symm)
    (fun i j _ => ((tilde.toTildeΓNatIso (R := R)).inv.naturality (P.d i j)).symm)

/-- **The global sections of `P̃` are K-flat over `R` when `P` is.** This is the second of the two
statements `Completion/CohomologyAffineAdicComparison.lean` records as missing from the affine
projection formula, and at a representative of the shape `P̃` it is not a theorem about sections
at all: `Γ(Spec R, P̃)` *is* `P`, by `Stacks.Algebraization.tildeΓComplexIso`, and K-flatness
transports along an isomorphism of complexes by `CochainComplex.kFlat_of_iso`. -/
public theorem kFlat_tildeΓComplex (hP : CochainComplex.KFlat.{u, u} P) :
    CochainComplex.KFlat.{u, u}
      (((tilde.functor R ⋙ moduleSpecΓFunctor).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  CochainComplex.kFlat_of_iso (tildeΓComplexIso R P).symm hP

/-- **Both K-flatness inputs of the affine projection formula, at one representative.** Every
object of `D(𝒪_{Spec R})` whose cohomology sheaves are quasi-coherent is the class of `P̃` for a
complex `P` of `R`-modules such that

* `P` is K-flat over `R` — so, by `Stacks.Algebraization.kFlat_tildeΓComplex`, so is
  `Γ(Spec R, P̃)`;
* `P̃` is K-flat as a complex of `𝒪_{Spec R}`-modules;
* every term of `P̃` is quasi-coherent.

The first and third are what the affine section formula
`Stacks.SectionTensorFormula.sectionsTensorComplexIso` and the recognition of the result as a
derived tensor product consume; the second is what
`Stacks.Algebraization.derivedTensorSingleIsoRowComplex` consumes. This is
`Stacks.Algebraization.exists_isKFlat_isQuasicoherent_iso_of_isQuasicoherent_homology` with the
module-side complex kept rather than discarded, which is the whole of the strengthening: the
representative there was already of this shape.

No finiteness, pseudo-coherence or boundedness is assumed or asserted. -/
public theorem exists_kFlat_tilde_isKFlat_isQuasicoherent_iso
    (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      CochainComplex.KFlat.{u, u} P ∧
      _root_.Stacks.SheafOfModules.IsKFlat (AlgebraicGeometry.specCommRingSheaf R)
        (AlgebraicGeometry.tildeComplexMod P) ∧
      (∀ i : ℤ, ((AlgebraicGeometry.tildeComplexMod P).X i).IsQuasicoherent) ∧
      Nonempty ((DerivedCategory.Q.obj (AlgebraicGeometry.tildeComplexMod P) :
        DerivedCategory (Spec R).Modules) ≅ E) := by
  obtain ⟨M, ⟨eM⟩⟩ :=
    _root_.Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard E hE
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := _root_.Stacks.Duality.exists_kFlat_module_complex_iso R M
  refine ⟨Q, hQ, AlgebraicGeometry.kFlat_tilde Q hQ,
    fun i => inferInstanceAs (((tilde.functor R).obj (Q.X i)).IsQuasicoherent), ?_⟩
  exact ⟨((tilde.functor R).mapDerivedCategoryFactors.app Q).symm ≪≫
    (tilde.functor R).mapDerivedCategory.mapIso eQ ≪≫ eM⟩

end Stacks.Algebraization

end
