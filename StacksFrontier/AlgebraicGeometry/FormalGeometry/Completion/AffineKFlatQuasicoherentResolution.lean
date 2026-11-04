module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Modules.TildeKFlat
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine

/-!
# A K-flat representative with quasi-coherent terms, on an affine scheme

Every object of `D(𝒪_{Spec R})` whose cohomology sheaves are quasi-coherent is the class of a
**K-flat complex of quasi-coherent `𝒪_{Spec R}`-modules**. No finiteness, no pseudo-coherence and
no boundedness is assumed.

## Why this is wanted

It is the first of the two statements that
`Completion/CohomologyAffineAdicComparison.lean` records as missing from the affine projection
formula

`RΓ(V, K ⊗^𝐋_{𝒪_X} M) ≅ RΓ(V, K) ⊗^𝐋_{Γ(X, V)} Γ(M, V)`,

which is in turn the whole of the affine-level gap in part (2) of [Stacks, Tag 0A0K]. The two
existing K-flat resolutions of sheaves are both unusable there:

* `Stacks.Duality.exists_kFlatComplex_iso` and
  `AlgebraicGeometry.TorFormula.exists_kFlatComplex_iso` — the same statement, formalized twice —
  assert **nothing at all** about the terms of the representative;
* `Stacks.SheafOfModules.exists_isKFlat_isFlat_quasiIso_epi` gives **flat** terms, but they are
  direct sums of extensions by zero of `𝒪`, which are not quasi-coherent.

Quasi-coherence of the terms is what the section formula
`Stacks.SectionTensorFormula.sectionsTensorComplexIso` needs, and it is exactly the hypothesis
neither of those supplies. That file's documentation recorded the one place quasi-coherent K-flat
terms are reachable — `AlgebraicGeometry.kFlat_tilde` on `Spec A`, [Stacks, Tag 08DV] — and that
it "is not packaged as an existence statement". This packages it.

## How it goes

Three library statements, and the only idea is to choose the resolution on the **module** side,
where K-flat resolutions exist and are carried to sheaves by a library theorem, rather than on the
sheaf side, where the resolutions that exist have the wrong terms.

1. `Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard` —
   essential surjectivity of derived sheafification, [Stacks, Tag 06Z0] — writes the given object
   as `M̃` for an `M` in `D(R)`.
2. `Stacks.Duality.exists_kFlat_module_complex_iso` replaces `M` by the class of a K-flat complex
   `P` of `R`-modules, which is [Stacks, Tag 06Y4] packaged through
   `CochainComplex.KFlat.chosenResolution`.
3. `AlgebraicGeometry.kFlat_tilde`, [Stacks, Tag 08DV], makes `P̃` K-flat as a complex of sheaves,
   and its terms are `tilde (Pⁱ)`, quasi-coherent by construction.

The comparison `(tilde.functor R).mapDerivedCategory.obj (Q P) ≅ Q P̃` is
`CategoryTheory.Functor.mapDerivedCategoryFactors`, the statement that an exact functor's induced
functor on derived categories agrees with its degreewise action — no exactness argument is
repeated here.

## What this does **not** give

The projection formula needs a **second** statement, and this is not it: K-flatness of `Γ(V, E)`
over `Γ(X, V)`, which is not proved for any of the sections functors. For the representative
produced here it should be immediate rather than general, since `Γ(Spec R, P̃) ≅ P` by the
affine equivalence `AlgebraicGeometry.tildeEquiv` and `P` is K-flat by construction — so the
owed statement is a `Γ ∘ tilde ≅ id` bridge at the level of complexes, in the sections spelling
the section formula is written in, and not a K-flatness theorem about arbitrary sections. That
bridge is not made here.

Nor is this transported to an affine **open** of a general scheme, which is where part (2) needs
it. The transport is along `AlgebraicGeometry.IsAffineOpen.isoSpec`, and
`AlgebraicGeometry.affineDerivedSectionsPresentation` already performs the analogous transport
for pseudo-coherence; it is not performed here.

Nothing in this file is registered against any tag: it is an existence statement assembled from
library ones, not a statement of the source.

## Implementation notes

The statement is pinned to `CategoryTheory.HasDerivedCategory.standard`, the instance
[Stacks, Tag 06Z0] is available at in the form used, and the K-flatness spelling is
`Stacks.SheafOfModules.IsKFlat (AlgebraicGeometry.specCommRingSheaf R)`, the one
`AlgebraicGeometry.kFlat_tilde` concludes and the one
`Stacks.Algebraization.derivedTensorSingleIsoRowComplex` consumes.
`AlgebraicGeometry.specCommRingSheaf R` is `(Spec R).sheaf` by `rfl`, and
`AlgebraicGeometry.SpecModules R` is `(Spec R).Modules` by `rfl`, so no reseating appears.

Quasi-coherence of the terms is stated rather than left to instance search, which does not see
through the degreewise application of `Functor.mapHomologicalComplex` — the same reason
`Stacks.Divisors.Eta.isQuasicoherent_tildeComplex` exists.

## References

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

/-- **Every object of `D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves is the class of a
K-flat complex of quasi-coherent `𝒪_{Spec R}`-modules.**

The two K-flat resolutions of complexes of sheaves already in the library are both unusable where
this is wanted: `Stacks.Duality.exists_kFlatComplex_iso` says nothing about the terms of its
representative, and `Stacks.SheafOfModules.exists_isKFlat_isFlat_quasiIso_epi` gives terms that
are flat but not quasi-coherent. Quasi-coherence of the terms is what the affine section formula
`Stacks.SectionTensorFormula.sectionsTensorComplexIso` consumes.

The resolution is chosen on the module side and carried over: [Stacks, Tag 06Z0] writes the
object as `M̃`, [Stacks, Tag 06Y4] replaces `M` by a K-flat complex `P` of `R`-modules, and
[Stacks, Tag 08DV] (`AlgebraicGeometry.kFlat_tilde`) makes `P̃` K-flat. Its terms are the sheaves
`tilde (Pⁱ)`.

No finiteness, pseudo-coherence or boundedness is assumed of the object, and none is asserted of
the representative. -/
public theorem exists_isKFlat_isQuasicoherent_iso_of_isQuasicoherent_homology
    (R : CommRingCat.{u}) (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj E).IsQuasicoherent) :
    ∃ P : CochainComplex (Spec R).Modules ℤ,
      _root_.Stacks.SheafOfModules.IsKFlat (AlgebraicGeometry.specCommRingSheaf R) P ∧
      (∀ i : ℤ, (P.X i).IsQuasicoherent) ∧
      Nonempty ((DerivedCategory.Q.obj P : DerivedCategory (Spec R).Modules) ≅ E) := by
  obtain ⟨M, ⟨eM⟩⟩ :=
    _root_.Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard E hE
  obtain ⟨P, hP, ⟨eP⟩⟩ := _root_.Stacks.Duality.exists_kFlat_module_complex_iso R M
  refine ⟨AlgebraicGeometry.tildeComplexMod P, AlgebraicGeometry.kFlat_tilde P hP,
    fun i => inferInstanceAs (((tilde.functor R).obj (P.X i)).IsQuasicoherent), ?_⟩
  exact ⟨((tilde.functor R).mapDerivedCategoryFactors.app P).symm ≪≫
    (tilde.functor R).mapDerivedCategory.mapIso eP ≪≫ eM⟩

end Stacks.Algebraization

end
