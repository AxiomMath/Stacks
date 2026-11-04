module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedAboveGenerator
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute

/-!
# Pseudo-coherence of the derived global sections of the perfect twists of an object

Let `A` be a ring, let `X` be a quasi-compact, quasi-separated scheme over `A`, and let `K` be an
object of `D_QCoh(𝒪_X)`. Suppose that `RΓ(X, K ⊗^L_{𝒪_X} E)` is a pseudo-coherent object of
`D(A)` for every perfect object `E` of `D(𝒪_X)`. Then, for a perfect generator `G` of
`D_QCoh(𝒪_X)`, the groups `Ext^i_X(G, K)` and `Hom_{D(𝒪_X)}(G⟦-i⟧, K)` vanish for `i ≫ 0`.

That vanishing is the input the source proof of Stacks 0GES feeds to Stacks 0GEN. A
pseudo-coherent object of `D(A)` is represented by a complex of finite free modules vanishing in
all large degrees, so its cohomology vanishes there; forgetting the `A`-module structure leaves
that vanishing in place. Vanishing of `H^i(X, G^∨ ⊗^L_{𝒪_X} K)` for `i ≫ 0` is condition (5) of
Stacks 0GEN, whose equivalences with conditions (3) and (2) give the two asserted vanishings.

## Main results

* `StacksDraft.PseudoCoherence.isZero_homology_of_isPseudoCoherent`: a pseudo-coherent object
  of `D(R)` has vanishing cohomology in all sufficiently large degrees.
* `AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPseudoCoherent`:
  the two vanishings, from pseudo-coherence in `D(A)` of the derived global sections of the
  perfect twists.

Stacks 0GES itself is
`AlgebraicGeometry.isPseudoCoherent_of_derivedGlobalSectionsOver_tensor_isPerfect`.

## Implementation notes

Pseudo-coherence of `RΓ(X, K ⊗^L_{𝒪_X} E)` in `D(A)` is
`StacksDraft.PseudoCoherence.IsPseudoCoherent` — Stacks 064Q (2) — of the object
`(derivedGlobalSectionsOver f).obj (K ⊗^L_{𝒪_X} E)`, where
`AlgebraicGeometry.derivedGlobalSectionsOver` is the `A`-linear unbounded `RΓ(X, -)` of Stacks
0D5W. The comparison
`Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso` identifies
`RΓ(X, -)` followed by the forgetful functor with `derivedModuleGlobalSections` of the ringed
site, so the vanishing obtained in `D(A)` transports to condition (5) of Stacks 0GEN in the
spelling that criterion uses.

## References

* [Stacks Project, Lemma 37.69.5 (Tag 0GES)](https://stacks.math.columbia.edu/tag/0GES)
* [Stacks Project, Proposition 36.40.5 (Tag 0GEN)](https://stacks.math.columbia.edu/tag/0GEN)
* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.SheafOfModules

universe v u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Pseudo-coherent objects of the derived category of a ring are bounded above -/

namespace StacksDraft.PseudoCoherence

/-- **A pseudo-coherent object of `D(R)` has vanishing cohomology in all sufficiently large
degrees.** -/
public theorem isZero_homology_of_isPseudoCoherent {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat.{v} R)} (hK : IsPseudoCoherent K) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  have := hb
  refine ⟨b, fun i hi => ?_⟩
  have h0 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
      (DerivedCategory.Q.obj E)) :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app E).isZero_iff.2
      (E.isZero_of_isLE b i hi)
  exact h0.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e).symm

end StacksDraft.PseudoCoherence

namespace AlgebraicGeometry

/-! ### Vanishing of the Ext groups against a perfect generator -/

section Objective

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- Forgetting the `A`-module structure keeps the cohomology of a pseudo-coherent object of
`D(A)` vanishing in all sufficiently large degrees. -/
private theorem isZero_homology_mapDerivedCategory_of_isPseudoCoherent
    {M : DerivedCategory (ModuleCat.{u} A)}
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategory.obj M)) := by
  obtain ⟨b, hb⟩ := StacksDraft.PseudoCoherence.isZero_homology_of_isPseudoCoherent hM
  refine ⟨b, fun i hi => ?_⟩
  have hiso := ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso
    i).app M
  exact hiso.isZero_iff.2
    (Functor.map_isZero (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) (hb i hi))

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)]
  [∀ V : TopologicalSpace.Opens X.toPresheafedSpace.carrier,
    HasSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]
  [∀ V : TopologicalSpace.Opens X.toPresheafedSpace.carrier,
    ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ V : TopologicalSpace.Opens X.toPresheafedSpace.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]

/-- **The vanishing that the hypothesis of Stacks 0GES produces.** Let `A` be a ring, let `X` be
a quasi-compact, quasi-separated scheme, let `G` be a perfect generator of `D_QCoh(𝒪_X)`, and let
`K` be an object of `D_QCoh(𝒪_X)`. If `RΓ(X, K ⊗^L_{𝒪_X} E)` is a pseudo-coherent object of
`D(A)` for every perfect object `E` of `D(𝒪_X)`, then `Ext^i_X(G, K)` and
`Hom_{D(𝒪_X)}(G⟦-i⟧, K)` vanish for `i ≫ 0`.

The dual `G^∨` is perfect by Stacks 08DQ (`Stacks.SheafOfModules.isPerfect_derivedDual`), so the
hypothesis on perfect twists applies to it, and
`RΓ(X, K ⊗^L_{𝒪_X} G^∨)` is the underlying complex of abelian groups of a pseudo-coherent
object of `D(A)`. A pseudo-coherent object of `D(A)` has vanishing cohomology in all
sufficiently large degrees and the forgetful functor to abelian groups is exact, so
`H^i(X, G^∨ ⊗^L_{𝒪_X} K)` vanishes for `i ≫ 0`; that is condition (5) of Stacks 0GEN, whose
equivalence with conditions (3) and (2) gives the two assertions. -/
public theorem eventually_subsingleton_ext_of_derivedGlobalSections_isPseudoCoherent
    (f : X ⟶ Spec (CommRingCat.of A))
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (G K : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hgen : ∀ L : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj L).IsQuasicoherent) →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ L), g = 0) → IsZero L)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent)
    (hpc : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      (ringedSite X.sheaf).IsPerfect E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((derivedGlobalSectionsOver f).obj (((derivedTensor X.sheaf).obj K).obj E))) :
    (∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (DerivedCategory.Ext G K i)) ∧
      ∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (G⟦-i⟧ ⟶ K) := by
  obtain ⟨b, hb⟩ := isZero_homology_mapDerivedCategory_of_isPseudoCoherent (A := A)
    (hpc (derivedDual X.sheaf G) (isPerfect_derivedDual X.sheaf G hG))
  have hext : ∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (DerivedCategory.Ext G K i) :=
    (eventually_subsingleton_ext_iff_isZero_homology_atTop hqc hqs G K hG hgen hK).2
      ⟨b + 1, fun n hn => (hb n (by omega)).of_iso
        (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
          ((Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso
            f).app (((derivedTensor X.sheaf).obj K).obj (derivedDual X.sheaf G)))).symm)⟩
  exact ⟨hext,
    (eventually_subsingleton_shiftedHom_iff_ext_atTop hqc hqs G K hG hgen hK).2 hext⟩

end Objective

end AlgebraicGeometry

end
