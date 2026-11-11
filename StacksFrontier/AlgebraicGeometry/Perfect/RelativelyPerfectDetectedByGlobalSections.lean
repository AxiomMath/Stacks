module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedBelowGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.Homology.Perfect.Defs

/-!
# Perfectness of the derived global sections of the perfect twists of an object

Let `A` be a ring, let `X` be a scheme separated, of finite presentation and flat over `A`, and
let `K` be an object of `D_QCoh(𝒪_X)`. Suppose that `RΓ(X, K ⊗^L_{𝒪_X} E)` is a perfect object
of `D(A)` for every perfect object `E` of `D(𝒪_X)`. Then, for a perfect generator `G` of
`D_QCoh(𝒪_X)`, the groups `Ext^i_X(G, K)` and `Hom_{D(𝒪_X)}(G⟦-i⟧, K)` vanish for `i ≪ 0`.

Perfectness of the dual `G^∨` is a hypothesis, so the hypothesis on perfect twists applies to
it; a perfect object of `D(A)` is a bounded complex of finite projective modules, hence has
vanishing cohomology in all sufficiently negative degrees, and forgetting the `A`-module
structure of the cohomology leaves that vanishing in place. Vanishing of
`H^i(X, G^∨ ⊗^L_{𝒪_X} K)` for `i ≪ 0` is one of the equivalent conditions of the
perfect-generator criterion, which converts it into the two asserted vanishings.

## Main results

* `AlgebraicGeometry.isZero_homology_of_isPerfect`: a perfect object of `D(R)` has vanishing
  cohomology in all sufficiently negative degrees.
* `AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect`: the two
  vanishings, from perfectness in `D(A)` of the derived global sections of the perfect twists.

## Implementation notes

Perfectness of `RΓ(X, K ⊗^L_{𝒪_X} E)` in `D(A)` is the existence of a perfect object `M` of
`D(A)` — `StacksDraft.Perfect.IsPerfect`, Stacks 0657 (1) — whose underlying object of
`D(Ab)`, along the forgetful functor from `A`-modules to abelian groups, is isomorphic to it.
Derived global sections of sheaves of modules in this development are valued in `D(Ab)`, by
`Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections`, so the `A`-module structure of
the source statement is carried by that datum and by nothing else.

The source writes the twist as `E ⊗^L_{𝒪_X} K`; the library's derived tensor product takes the
factor to be dualized second, and the twist is written `K ⊗^L_{𝒪_X} E` to match the shape in
which the perfect-generator criterion states it. The derived tensor product is symmetric, so
this is the hypothesis of the source.

Nothing below is pinned to a universe: `A : Type u` and `X : Scheme.{u}`. Perfectness of the
dual `G^∨` and invertibility of the Stacks 08I1 map are explicit arguments, exactly as the
perfect-generator criterion
`Stacks.SheafOfModules.eventually_subsingleton_ext_iff_isZero_homology_derivedTensorDual`
takes the latter. Both are assertions of Stacks 08DQ which the library proves at every universe
(`Stacks.SheafOfModules.isPerfect_derivedDual` and
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`); they are discharged in
`AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect'`. The perfect
generator `G` (Stacks 09IS, `Stacks.SheafOfModules.exists_isPerfect_generator`) and
quasi-compactness and quasi-separatedness of `X` are arguments as well, so that this lemma
applies to any chosen generator.

**Where the conclusion of Stacks 0GET is proved.** That `K` is `Spec(A)`-perfect,
`AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`, is
`AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isPerfect_derivedGlobalSectionsOver_tensor`
of `StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectFromGlobalSections.lean`, which
carries the tag. It uses the flat variant of the vanishing proved here, together with Stacks 0GES,
the implication (2) ⇒ (1) of Stacks 0GEH and condition (1) of Stacks 0GEQ, all of which the
library proves.

## References

* [Stacks Project, Lemma 37.69.6 (Tag 0GET)](https://stacks.math.columbia.edu/tag/0GET)
* [Stacks Project, Proposition 36.40.6 (Tag 0GEQ)](https://stacks.math.columbia.edu/tag/0GEQ)
* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.SheafOfModules

namespace AlgebraicGeometry

universe w v u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Perfect objects of the derived category of a ring are bounded below -/

/-- **A perfect object of `D(R)` has vanishing cohomology in all sufficiently negative
degrees.** A perfect object is isomorphic to a complex of finite projective modules vanishing
in degrees below some `a`, and such a complex has vanishing cohomology there. -/
public theorem isZero_homology_of_isPerfect {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {K : DerivedCategory (ModuleCat.{v} R)} (hK : StacksDraft.Perfect.IsPerfect K) :
    ∃ a : ℤ, ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
  obtain ⟨P, a, b, hGE, hLE, -, -, ⟨e⟩⟩ := hK
  have := hGE
  refine ⟨a, fun i hi => ?_⟩
  have h0 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
      (DerivedCategory.Q.obj P)) :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app P).isZero_iff.2
      (P.isZero_of_isGE a i hi)
  exact h0.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e)

/-! ### Vanishing of the Ext groups against a perfect generator -/

section Objective

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)]

/-- Forgetting the `A`-module structure keeps the cohomology of a perfect object of `D(A)`
vanishing in all sufficiently negative degrees. -/
private theorem isZero_homology_mapDerivedCategory_of_isPerfect
    {M : DerivedCategory (ModuleCat.{u} A)} (hM : StacksDraft.Perfect.IsPerfect M) :
    ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategory.obj M)) := by
  obtain ⟨a, ha⟩ := isZero_homology_of_isPerfect hM
  refine ⟨a, fun i hi => ?_⟩
  have hiso := ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso
    i).app M
  exact hiso.isZero_iff.2
    (Functor.map_isZero (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) (ha i hi))

/-- **The vanishing that the hypothesis of Stacks 0GET produces.** Let `A` be a ring, let `X` be a
scheme separated, of finite presentation and flat over `A`, let `G` be a perfect generator of
`D_QCoh(𝒪_X)` whose dual `G^∨` is perfect, and let `K` be an object of `D_QCoh(𝒪_X)`. If
`RΓ(X, K ⊗^L_{𝒪_X} E)` is a perfect object of `D(A)` for every perfect object `E` of `D(𝒪_X)`,
then `Ext^i_X(G, K)` and `Hom_{D(𝒪_X)}(G⟦-i⟧, K)` vanish for `i ≪ 0`.

Perfectness of `G^∨` is Stacks 08DQ, and is a hypothesis here rather than a consequence of
`hG`; see the implementation notes. It makes the hypothesis on perfect twists apply to `G^∨`,
so that `RΓ(X, K ⊗^L_{𝒪_X} G^∨)` is the underlying complex of abelian groups of a perfect
object of `D(A)`. A perfect object of `D(A)` has vanishing cohomology in all sufficiently
negative degrees and the forgetful functor to abelian groups is exact, so
`H^i(X, G^∨ ⊗^L_{𝒪_X} K)` vanishes for `i ≪ 0`; that is condition (5) of Stacks 0GEQ, whose
equivalence with conditions (3) and (2) gives the two assertions.

`Spec(A)`-perfectness of `K`, the conclusion of Stacks 0GET, is
`AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isPerfect_derivedGlobalSectionsOver_tensor`. -/
public theorem eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [QuasiCompact f] [Flat f]
    [LocallyOfFinitePresentation f]
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (G K : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hGdual : (ringedSite X.sheaf).IsPerfect (derivedDual X.sheaf G))
    (hgen : ∀ L : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj L).IsQuasicoherent) →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ L), g = 0) → IsZero L)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent)
    (h08I1 : ∀ i : ℤ, IsIso (derivedTensorDualToSheafHom X.sheaf G (K⟦i⟧)))
    (hperf : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      (ringedSite X.sheaf).IsPerfect E →
        ∃ M : DerivedCategory (ModuleCat.{u} A), StacksDraft.Perfect.IsPerfect M ∧
          Nonempty ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
              (((derivedTensor X.sheaf).obj K).obj E) ≅
            (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategory.obj M)) :
    (∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext G K i)) ∧
      ∃ N : ℤ, ∀ i ≤ N, Subsingleton (G⟦-i⟧ ⟶ K) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hperf (derivedDual X.sheaf G) hGdual
  obtain ⟨a, ha⟩ := isZero_homology_mapDerivedCategory_of_isPerfect hM
  have hext : ∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext G K i) :=
    (eventually_subsingleton_ext_iff_isZero_homology_derivedTensorDual
        hqc hqs G K hG hgen hK h08I1).2
      ⟨a - 1, fun n hn =>
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso e).isZero_iff.2
          (ha n (by omega))⟩
  exact ⟨hext, (eventually_subsingleton_shiftedHom_iff_ext hqc hqs G K hG hgen hK).2 hext⟩

end Objective

end AlgebraicGeometry

end
