module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeTensorKFlat
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DgaResolutionTensorRepresents
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyPKFlat
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductTotalComplex
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.Tor.DerivedTensorKFlatResolution

/-!
# Stacks 0BZ8 over a K-flat middle algebra

Let `R` be a ring and let `(A, d)`, `(B, d)` and `(C, d)` be differential graded `R`-algebras
such that the ordinary tensor product `A ⊗_R C` represents `A ⊗^𝐋_R C` in `D(R)`. The proof of
Stacks Tag 0BZ8 has two halves. The second half assumes in addition that `B` is K-flat as a
complex of `R`-modules and *proves* the hypothesis of Tag 0BZ5, that the canonical map
`(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` of Tag 0BZ4 is an isomorphism; the first
half reduces a general `B` to that case, not by proving the map of Tag 0BZ4 to be an isomorphism
but by replacing `B` by a quasi-isomorphic K-flat differential graded algebra (Tag 0BZ7) and
transporting the *conclusion* along the equivalence of derived categories of Tag 09S6.

This file carries out the second half. It is the whole of the content of Tag 0BZ8 beyond Tag
0BZ5 that can be had in the form of the Tag 0BZ4 isomorphism: for a general `B` that isomorphism
does not follow from representability, so
`DifferentialGraded.Bimodule.DgaResolutionRepresentsInvertsBaseChange` — the hypothesis under
which `DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIso` assembles Tag 0BZ8 —
is discharged here exactly under K-flatness of `B` and not in general. The implementation notes
of `StacksFrontier/Algebra/DifferentialGraded/Module/DgaResolutionTensorRepresents.lean` record why.

The first half is
`StacksFrontier/Algebra/DifferentialGraded/Module/DgaResolutionGeneralBase.lean`, which proves Tag
0BZ8 for a general `B` by consuming the result of this file at the K-flat algebra `B'` of Tag
0BZ7; what it gives up in exchange for dropping K-flatness of `B` is the naming of the bimodule
`N''`, which the source does not name either.

## Main results

* `DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_of_dgaResolutionRepresents`:
  if `B` is K-flat as a complex of `R`-modules and `A ⊗_R C` represents `A ⊗^𝐋_R C`, then the
  canonical map of Tag 0BZ4 is an isomorphism. This is the second half of the proof of Tag 0BZ8.
* `DifferentialGraded.Bimodule.dgaResolutionRepresentsInvertsBaseChange_of_kFlat`: the same
  statement, packaged as the hypothesis of
  `DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIso`.
* `DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIsoOfKFlatBase`: **Tag 0BZ8
  for a K-flat middle algebra**, with representability of `A ⊗^𝐋_R C` by `A ⊗_R C` and
  K-flatness of `B` as its only hypotheses.

## Implementation notes

*The shape of the proof.* The source chooses a differential graded `R`-module `L` with property
(P) and a quasi-isomorphism `L ⟶ A`, observes that `P = L ⊗_R B` then has property (P) as a
differential graded `B`-module, and computes the comparison of Tag 09LS at `(A ⊗_R B)_B` on that
resolution. Here the resolution of `(A ⊗_R B)_B` is instead an arbitrary property-(P) resolution
`Q ⟶ (A ⊗_R B)_B`, which exists by Tag 09KP; what makes that legitimate is that the complex
underlying `Q` is K-flat over `R` — this is
`DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration`, where K-flatness of
`B` is used the first time — together with the fact that tensoring a K-flat resolution with a
fixed complex does not depend on the resolution,
`CochainComplex.DerivedTensor.quasiIso_trightCochain_map_of_kFlat_resolution`. The source's
resolution `L ⊗_R B` is thereby replaced by the resolution `P ⊗_R B` of
`DifferentialGraded.Bimodule` fame, where `P ⟶ A^•` is a K-flat resolution of complexes of
`R`-modules (Tag 06Y4) — a complex, not a differential graded `B`-module, which is why nothing
has to be said about property (P) of a tensor product.

*Where the hypotheses go.* K-flatness of `B` is used twice: to see that the complex underlying a
property-(P) differential graded `B`-module is K-flat over `R`, and to see that `P ⊗_R B ⟶
A ⊗_R B` is a quasi-isomorphism and that `P ⊗_R B ⊗_R C ⟶ A ⊗_R B ⊗_R C` is one as well — the
latter is the source's appeal to Tag 06Y0, and it is
`CochainComplex.DerivedTensor.quasiIso_trightCochain_map_whiskerRight`. Representability is used
once, at the K-flat resolution `P ⟶ A^•`.

*The identifications.* The complex underlying `(A ⊗_R B)_B` is the complex underlying the
differential graded algebra `A ⊗_R B`, because restriction of scalars changes no complex
(`DifferentialGradedModule.restrictScalars_toCochainComplex`), and that is the total complex
`Tot(A^• ⊗_R B^•)` by Tag 065X
(`DifferentialGradedAlgebra.tensorToCochainComplexIso`). The complex underlying
`Q ⊗_B {}_B(B ⊗_R C)_C` is `Tot(Q^• ⊗_R C^•)`, naturally in `Q`, by
`DifferentialGraded.absBalancedComplexIso_naturality`, which is the computation the proof of Tag
09S4 is built on.

*The lifted monoidal structure.* As elsewhere in this chapter, `CochainComplex.KFlat` and the
tensor–total functors are stated against the large-universe monoidal structure of
`StacksFrontier/Algebra/Category/ModuleCat/Monoidal/LargeUniverse.lean`, so those instances are
settled locally for this file.

## References

* [Stacks Project, Tag 0BZ8](https://stacks.math.columbia.edu/tag/0BZ8), whose proof this is the
  second half of; the lemma it strengthens is
  [Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5), the map in its hypothesis is
  [Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the first half uses
  [Tag 0BZ7](https://stacks.math.columbia.edu/tag/0BZ7) and
  [Tag 09S6](https://stacks.math.columbia.edu/tag/09S6), property-(P) resolutions exist by
  [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP), K-flat resolutions of complexes exist by
  [Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4), K-flatness is
  [Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ) and preserves quasi-isomorphisms by
  [Tag 06Y0](https://stacks.math.columbia.edu/tag/06Y0), and the tensor product of two
  differential graded algebras is a total complex by
  [Tag 065X](https://stacks.math.columbia.edu/tag/065X).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra CochainComplex.DerivedTensor
open MonoidalCategory

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

variable {R : Type u} [CommRing R]

/-- **The second half of the proof of Stacks Tag 0BZ8.** If the differential graded algebra
`(B, d)` is K-flat as a complex of `R`-modules and `A ⊗_R C` represents `A ⊗^𝐋_R C` in `D(R)`,
then the canonical map `(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` of Tag 0BZ4 is an
isomorphism — which by Tag 0BZ5 is all that the conclusion of Tag 0BZ8 needs.

The source resolves `(A ⊗_R B)_B` by `L ⊗_R B` for a property-(P) differential graded `R`-module
`L` quasi-isomorphic to `A`; the comparison of Tag 09LS at `(A ⊗_R B)_B` is then the map
`L ⊗_R B ⊗_R C ⟶ A ⊗_R B ⊗_R C`, which K-flatness of `B` reduces to `L ⊗_R C ⟶ A ⊗_R C`, and
that is the representability hypothesis. Here the resolution is an arbitrary property-(P)
resolution `Q ⟶ (A ⊗_R B)_B`, and what replaces the source's computation is that the complex
underlying `Q` is K-flat over `R` and that tensoring a K-flat resolution with `C` does not
depend on which resolution is taken; the resolution the hypothesis is evaluated at is then
`Tot(P^• ⊗_R B^•)` for a K-flat resolution `P^• ⟶ A^•` of complexes of `R`-modules. -/
@[stacks 0BZ8 "the second half of the proof: for B K-flat as a complex of R-modules, \
representability of A ⊗^L_R C by A ⊗_R C makes the map (0BZ4) an isomorphism"]
theorem isIso_derivedTensorBaseChangeComparison_of_dgaResolutionRepresents
    (A B C : DifferentialGradedAlgebra.{u, u} R)
    (hB : CochainComplex.KFlat.{u, u} (regularModule B).toCochainComplex)
    (hrep : DgaResolutionRepresentsDerivedTensor A C) :
    IsIso (derivedTensorBaseChangeComparison A B C) := by
  obtain ⟨Q, f, hf, hQ⟩ :=
    DifferentialGradedModule.exists_propertyP_resolution B (baseChangeModule A B)
  obtain ⟨P, p, hP, -, hp, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (regularModule A).toCochainComplex
  have := hf
  have := hp
  -- the second K-flat resolution of the complex underlying `A ⊗_R B`
  let q₀ : P ⊗ (regularModule B).toCochainComplex ⟶
      (forgetToCochainComplex B).obj (baseChangeModule A B) :=
    (p ▷ (regularModule B).toCochainComplex) ≫ (tensorToCochainComplexIso A B).inv
  have hwp : QuasiIso (p ▷ (regularModule B).toCochainComplex) := by
    rw [← trightCochain_map_eq_whiskerRight.{u, u} (regularModule B).toCochainComplex p]
    exact quasiIso_tright_map.{u, u} _ hB p
  have hq₀ : QuasiIso q₀ :=
    quasiIso_comp (hφ := hwp) (hφ' := quasiIso_of_isIso (tensorToCochainComplexIso A B).inv) _ _
  have hq₀rep : QuasiIso ((TrightCochain (regularModule C).toCochainComplex).map q₀) := by
    change QuasiIso ((TrightCochain (regularModule C).toCochainComplex).map
      ((p ▷ (regularModule B).toCochainComplex) ≫ (tensorToCochainComplexIso A B).inv))
    rw [Functor.map_comp]
    exact quasiIso_comp
      (hφ := quasiIso_trightCochain_map_whiskerRight.{u, u} _ _ hB p (hrep P hP p hp))
      (hφ' := quasiIso_of_isIso ((TrightCochain (regularModule C).toCochainComplex).map
        (tensorToCochainComplexIso A B).inv)) _ _
  -- the comparison of Tag 0BZ4, read at the property-(P) resolution
  rw [isIso_derivedTensorBaseChangeComparison_iff,
    isIso_derivedTensorFunctorCounit_app_iff_quasiIso_of_propertyP
      (baseChangeBimodule B C) f hf hQ]
  have hcore : QuasiIso (absRightTensorMap B C f) := by
    change QuasiIso ((TrightCochain (regularModule C).toCochainComplex).map
      ((forgetToCochainComplex B).map f))
    exact quasiIso_trightCochain_map_of_kFlat_resolution.{u} _ q₀
      (CochainComplex.KFlat.tensor R P (regularModule B).toCochainComplex hP hB) hq₀rep
      ((forgetToCochainComplex B).map f)
      (kFlat_toCochainComplex_of_propertyPFiltration hB hQ.some)
  have h1 : QuasiIso ((absBalancedComplexIso B C Q).hom ≫ (forgetToCochainComplex C).map
      ((tensorCompFunctor (baseChangeBimodule B C)).map f)) := by
    rw [← absBalancedComplexIso_naturality B C f]
    exact quasiIso_comp (hφ := hcore)
      (hφ' := quasiIso_of_isIso (absBalancedComplexIso B C (baseChangeModule A B)).hom) _ _
  exact (quasiIso_iff_comp_left
    (hφ := quasiIso_of_isIso (absBalancedComplexIso B C Q).hom) _ _).1 h1

/-- **The hypothesis `hbridge` of
`DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIso` holds when `B` is K-flat
as a complex of `R`-modules.** That hypothesis is the step of the proof of Tag 0BZ8 beyond Tag
0BZ5, namely that representability of `A ⊗^𝐋_R C` by `A ⊗_R C` makes the map of Tag 0BZ4 an
isomorphism, and this is exactly the second half of the source's proof:
`DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_of_dgaResolutionRepresents`.

For a general `B` the source does not prove the map of Tag 0BZ4 to be an isomorphism; it replaces
`B` by a quasi-isomorphic K-flat differential graded algebra (Tag 0BZ7) and transports the
conclusion of the lemma along the equivalence of derived categories of Tag 09S6. -/
theorem dgaResolutionRepresentsInvertsBaseChange_of_kFlat
    (A B C : DifferentialGradedAlgebra.{u, u} R)
    (hB : CochainComplex.KFlat.{u, u} (regularModule B).toCochainComplex) :
    DgaResolutionRepresentsInvertsBaseChange A B C :=
  isIso_derivedTensorBaseChangeComparison_of_dgaResolutionRepresents A B C hB

/-- **Stacks Tag 0BZ8 for a K-flat middle algebra.** Let `R` be a ring, let `(A, d)`, `(B, d)`
and `(C, d)` be differential graded `R`-algebras with `A ⊗_R C` representing `A ⊗^𝐋_R C` in
`D(R)` and with `B` K-flat as a complex of `R`-modules, let `N` be a differential graded
`(A, B)`-bimodule and `N'` a differential graded `(B, C)`-bimodule. Then the composition
`D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to `- ⊗_A^𝐋 N''` for
the differential graded `(A, C)`-bimodule `N'' = Ñ ⊗_B Ñ'` of
`DifferentialGraded.Bimodule.compTensorResolution`.

This is `DifferentialGraded.Bimodule.dgaResolutionDerivedTensorFunctorCompIso` with its carried
hypothesis `hbridge` discharged; the representability hypothesis `hrep` of the source is the only
hypothesis left besides K-flatness of `B`, which the source's reduction by Tag 0BZ7 and Tag 09S6
removes — that is
`DifferentialGraded.Bimodule.exists_derivedTensorFunctorCompIso` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DgaResolutionGeneralBase.lean`, at the cost of no
longer naming the bimodule `N''`. -/
@[stacks 0BZ8 "for B K-flat as a complex of R-modules, with representability of A ⊗^L_R C by \
A ⊗_R C as its only other hypothesis"]
def dgaResolutionDerivedTensorFunctorCompIsoOfKFlatBase
    {A B C : DifferentialGradedAlgebra.{u, u} R}
    (hB : CochainComplex.KFlat.{u, u} (regularModule B).toCochainComplex)
    (hrep : DgaResolutionRepresentsDerivedTensor A C)
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  dgaResolutionDerivedTensorFunctorCompIso
    (dgaResolutionRepresentsInvertsBaseChange_of_kFlat A B C hB) hrep N N'

end DifferentialGraded.Bimodule

end
