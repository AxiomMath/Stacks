module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison `D(Coh(𝒪_F)) ⥤ D_Coh(𝒪_F)` on an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The coherent
`𝒪_F`-modules are closed under kernels, cokernels and finite products inside all `𝒪_F`-modules,
so `Coh(𝒪_F)` is abelian and the inclusion `Coh(𝒪_F) ⥤ Mod(𝒪_F)` is exact.  Its derived functor
has coherent cohomology in every degree, hence factors through the full subcategory
`D_Coh(𝒪_F) ⊆ D(𝒪_F)` of objects with coherent cohomology, and the factorisation is the
canonical functor

`D(Coh(𝒪_F)) ⟶ D_Coh(𝒪_F)`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentDerivedCategory` is `D_Coh(𝒪_F)`, the full subcategory of
  `D(𝒪_F)` of objects all of whose cohomology modules are coherent.
* `AlgebraicGeometry.Space.coherentDerivedComparison` is the canonical functor
  `D(Coh(𝒪_F)) ⥤ D_Coh(𝒪_F)`.
* `AlgebraicGeometry.Space.coherentDerivedComparisonCompιIso` identifies its composite with the
  inclusion of `D_Coh(𝒪_F)` as the derived functor of `Coh(𝒪_F) ⥤ Mod(𝒪_F)`.

## Main results

* `AlgebraicGeometry.Space.isCoherent_isClosedUnderKernels`,
  `AlgebraicGeometry.Space.isCoherent_isClosedUnderCokernels` and
  `AlgebraicGeometry.Space.isCoherent_isClosedUnderFiniteProducts`: coherence of `𝒪_F`-modules
  is closed under kernels, cokernels and finite products, so `Coh(𝒪_F)` is abelian and the
  inclusion `Coh(𝒪_F) ⥤ Mod(𝒪_F)` is exact.
* `AlgebraicGeometry.Space.coherentDerivedComparison_mem`: the derived functor of the inclusion
  of the coherent `𝒪_F`-modules has coherent cohomology in every degree.

## Implementation notes

`Mod(𝒪_F)` is `AlgebraicGeometry.Space.Modules`, the sheaves of modules on the small étale
ringed site of `F`, and `Coh(𝒪_F)` is `AlgebraicGeometry.Space.CoherentModules`, the full
subcategory cut out by `AlgebraicGeometry.Space.IsCoherent`; no category is restated.

The closure properties are the clauses of Stacks 07UC, and none of them is a hypothesis here.
The quasi-coherence clause of `AlgebraicGeometry.Space.IsCoherent` is redundant by
`AlgebraicGeometry.Space.isCoherent_iff_isCoherentOnSite`, so coherence of `𝒪_F`-modules is
coherence on the small étale ringed site, which Stacks 01BY shows closed under kernels
(`Stacks.SheafOfModules.isCoherentOnSite_kernel`), cokernels
(`Stacks.SheafOfModules.isCoherentOnSite_cokernel`) and finite direct sums
(`Stacks.SheafOfModules.isCoherentOnSite_biprod`) over an arbitrary site.  In particular the
closure clauses of Stacks 03M1 for quasi-coherence, which are not available in this library, are
not needed: on a ringed site coherence passes to kernels and cokernels on its own.

Local Noetherianity of `F` is not assumed.  Stacks 08GJ is stated for a locally Noetherian
algebraic space, where the coherent modules are also exactly the quasi-coherent modules of
finite type; the comparison functor itself needs only the closure properties above, which hold
over an arbitrary site, so the construction below is a generalisation and specialises to the
source's situation by instantiating `F` at a locally Noetherian algebraic space.

The module universe is the universe `u` of the schemes, the universe of the structure sheaf of
the small étale ringed site.  It cannot be left free:
`AlgebraicGeometry.Space.isCoherent_iff_isCoherentOnSite` builds the presentations witnessing
quasi-coherence out of sections of the structure sheaf, and `u` is also the universe in which
`Mod(𝒪_F)` is abelian by `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`.

That the derived inclusion has coherent cohomology is the comparison
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for an exact functor, `Hⁿ(I(K)) ≅
I(Hⁿ(K))`, together with the fact that `I` takes values in the coherent modules.  The comparison
is obtained by corestricting the derived inclusion along `CategoryTheory.ObjectProperty.lift`,
so its composite with the inclusion of `D_Coh(𝒪_F)` is the derived inclusion on the nose, by
`CategoryTheory.ObjectProperty.liftCompιIso`.

`D_Coh(𝒪_F)` is not shown here to be a triangulated subcategory of `D(𝒪_F)`, and the comparison
is not shown to be exact: `DerivedCategoryB.derivedCategoryB_isTriangulated` asks for coherence
to be a weak Serre class, whose remaining clause is closure under extensions, Stacks 01BY (4) on
a site, which this library does not have for `SheafOfModules.IsCoherentOnSite`.

## References

* [Stacks Project, Tag 08GJ](https://stacks.math.columbia.edu/tag/08GJ)
* [Stacks Project, Tag 06UR](https://stacks.math.columbia.edu/tag/06UR)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### `Coh(𝒪_F)` is abelian and its inclusion into `Mod(𝒪_F)` is exact -/

/-- Coherence of `𝒪_F`-modules is invariant under isomorphism. -/
instance isCoherent_isClosedUnderIsomorphisms :
    (isCoherent.{u, u} B S hS F hF).IsClosedUnderIsomorphisms where
  of_iso {_M N} e hM :=
    let : SheafOfModules.IsCoherentOnSite N :=
      Stacks.SheafOfModules.isCoherentOnSite_of_iso e hM.toIsCoherentOnSite
    isCoherent_of_isCoherentOnSite B S hS F hF N

/-- **Coherence of `𝒪_F`-modules is closed under kernels.**  The kernel of a map of modules
coherent on the small étale ringed site is coherent on that site, by Stacks 01BY (3). -/
instance isCoherent_isClosedUnderKernels :
    (isCoherent.{u, u} B S hS F hF).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine (isCoherent.{u, u} B S hS F hF).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk) ?_
    let : SheafOfModules.IsCoherentOnSite (kernel f) :=
      Stacks.SheafOfModules.isCoherentOnSite_kernel hM.toIsCoherentOnSite
        hN.toIsCoherentOnSite f
    exact isCoherent_of_isCoherentOnSite B S hS F hF (kernel f)

/-- **Coherence of `𝒪_F`-modules is closed under cokernels.**  The cokernel of a map of modules
coherent on the small étale ringed site is coherent on that site, by Stacks 01BY (3). -/
instance isCoherent_isClosedUnderCokernels :
    (isCoherent.{u, u} B S hS F hF).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine (isCoherent.{u, u} B S hS F hF).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk) ?_
    let : SheafOfModules.IsCoherentOnSite (cokernel f) :=
      Stacks.SheafOfModules.isCoherentOnSite_cokernel f hM.toIsCoherentOnSite
        hN.toIsCoherentOnSite
    exact isCoherent_of_isCoherentOnSite B S hS F hF (cokernel f)

/-- **Coherence of `𝒪_F`-modules is closed under binary products.**  A binary product of modules
is their biproduct, and a biproduct of modules coherent on the small étale ringed site is
coherent on that site, by Stacks 01BY (3). -/
instance isCoherent_isClosedUnderBinaryProducts :
    (isCoherent.{u, u} B S hS F hF).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    refine ObjectProperty.prop_of_iso _ (HasLimit.isoOfNatIso (diagramIsoPair G)).symm ?_
    have : HasBinaryBiproduct (G.obj ⟨WalkingPair.left⟩) (G.obj ⟨WalkingPair.right⟩) :=
      HasBinaryBiproduct.of_hasBinaryProduct _ _
    let : SheafOfModules.IsCoherentOnSite
        (G.obj ⟨WalkingPair.left⟩ ⨯ G.obj ⟨WalkingPair.right⟩) :=
      Stacks.SheafOfModules.isCoherentOnSite_prod
        (hG ⟨WalkingPair.left⟩).toIsCoherentOnSite (hG ⟨WalkingPair.right⟩).toIsCoherentOnSite
    exact isCoherent_of_isCoherentOnSite B S hS F hF _)

/-- **Coherence of `𝒪_F`-modules is closed under finite products.**  The empty product is a zero
module, which is coherent, and the binary case is
`AlgebraicGeometry.Space.isCoherent_isClosedUnderBinaryProducts`. -/
instance isCoherent_isClosedUnderFiniteProducts :
    (isCoherent.{u, u} B S hS F hF).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The inclusion `Coh(𝒪_F) ⥤ Mod(𝒪_F)` is left exact: coherence is closed under kernels, so the
inclusion creates them. -/
instance preservesFiniteLimits_ι_coherentModules :
    PreservesFiniteLimits (isCoherent.{u, u} B S hS F hF).ι :=
  have : ∀ ⦃X Y : CoherentModules.{u, u} B S hS F hF⦄ (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (isCoherent.{u, u} B S hS F hF).ι :=
    fun {_ _} f => ObjectProperty.preservesKernels_ι _ f
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The inclusion `Coh(𝒪_F) ⥤ Mod(𝒪_F)` is right exact: coherence is closed under cokernels, so
the inclusion creates them. -/
instance preservesFiniteColimits_ι_coherentModules :
    PreservesFiniteColimits (isCoherent.{u, u} B S hS F hF).ι :=
  have : ∀ ⦃X Y : CoherentModules.{u, u} B S hS F hF⦄ (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (isCoherent.{u, u} B S hS F hF).ι :=
    fun {_ _} f => ObjectProperty.preservesCokernels_ι _ f
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- The inclusion `Coh(𝒪_F) ⥤ Mod(𝒪_F)` is additive: it preserves binary products. -/
instance additive_ι_coherentModules :
    (isCoherent.{u, u} B S hS F hF).ι.Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The comparison functor -/

/-- The category `D_Coh(𝒪_F)`: the full subcategory of the unbounded derived category of
`𝒪_F`-modules whose objects have coherent cohomology modules in every degree. -/
noncomputable abbrev CoherentDerivedCategory :=
  (DerivedCategoryB.derivedCategoryB (isCoherent.{u, u} B S hS F hF)).FullSubcategory

/-- **Stacks 08GJ, well-definedness.**  The derived functor of the inclusion of the coherent
`𝒪_F`-modules has coherent cohomology in every degree: the inclusion is exact, so it commutes
with cohomology. -/
@[stacks 08GJ "well-definedness"]
theorem coherentDerivedComparison_mem (K : DerivedCategory (CoherentModules.{u, u} B S hS F hF)) :
    DerivedCategoryB.derivedCategoryB (isCoherent.{u, u} B S hS F hF)
      ((isCoherent.{u, u} B S hS F hF).ι.mapDerivedCategory.obj K) := by
  set P := isCoherent.{u, u} B S hS F hF
  intro n
  exact P.prop_of_iso ((P.ι.mapDerivedCategoryHomologyIso n).app K).symm
    (P.prop_ι_obj ((DerivedCategory.homologyFunctor _ n).obj K))

/-- **Stacks 08GJ.**  The canonical functor from the derived category of the coherent
`𝒪_F`-modules to the derived category of all `𝒪_F`-modules with coherent cohomology,

`D(Coh(𝒪_F)) ⟶ D_Coh(𝒪_F)`,

obtained by factoring the derived functor of the exact inclusion `Coh(𝒪_F) ⥤ Mod(𝒪_F)` through
`D_Coh(𝒪_F)`. -/
@[stacks 08GJ]
noncomputable def coherentDerivedComparison :
    DerivedCategory (CoherentModules.{u, u} B S hS F hF) ⥤
      CoherentDerivedCategory.{u} B S hS F hF :=
  (DerivedCategoryB.derivedCategoryB (isCoherent.{u, u} B S hS F hF)).lift
    (isCoherent.{u, u} B S hS F hF).ι.mapDerivedCategory
    (coherentDerivedComparison_mem B S hS F hF)

/-- **Stacks 08GJ, the canonical comparison.**  The functor `D(Coh(𝒪_F)) ⥤ D_Coh(𝒪_F)` followed
by the inclusion of `D_Coh(𝒪_F)` into `D(𝒪_F)` is the derived functor of the inclusion
`Coh(𝒪_F) ⥤ Mod(𝒪_F)`; that is, the comparison is a factorisation of the latter. -/
@[stacks 08GJ "canonical comparison"]
noncomputable def coherentDerivedComparisonCompιIso :
    coherentDerivedComparison B S hS F hF ⋙
        (DerivedCategoryB.derivedCategoryB (isCoherent.{u, u} B S hS F hF)).ι ≅
      (isCoherent.{u, u} B S hS F hF).ι.mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

end AlgebraicGeometry.Space

end
