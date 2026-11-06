module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedDirectSums
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilityShrinkHoms
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute

/-!
# The coherator revisited: a right adjoint to `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`

Let `X` be a quasi-compact and quasi-separated scheme. The inclusion
`J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` of the complexes of `𝒪_X`-modules with quasi-coherent cohomology into
the full unbounded derived category has a right adjoint, written `DQ_X` in the source. This is
[Stacks, Tag 0CR0].

The source gives two proofs. The first runs the induction principle [Stacks, Tag 08DR] on the
quasi-compact opens of `X`, using the affine coherator [Stacks, Tag 08D9] as the base case, the
Mayer–Vietoris triangle [Stacks, Tag 08BV] and the extension-product criterion
[Stacks, Tag 0CQS] together with [Stacks, Tag 0CQR] for the gluing step. The second proof is one
appeal to Brown representability [Stacks, Tag 0A8G]: the inclusion is exact and preserves direct
sums, and `D_QCoh(𝒪_X)` is compactly generated, so the inclusion has an exact right adjoint.

It is the second proof that is carried out here. Everything it needs about the inclusion is
available: `D_QCoh(𝒪_X)` is a strictly full triangulated subcategory of `D(𝒪_X)` closed under
direct sums ([Stacks, Tag 06VT] and [Stacks, Tag 08DT]), so the inclusion is exact and preserves
direct sums, and Brown representability is
`CategoryTheory.Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated`.

## The carried hypothesis

Compact generation of `D_QCoh(𝒪_X)` is **not** available in this repository and is therefore
carried as an explicit hypothesis, `CategoryTheory.Pretriangulated.IsCompactlyGenerated`
([Stacks, Tag 09SQ]). It is the conjunction of two results of the source which are both true for
a quasi-compact quasi-separated `X` and neither of which is formalized here:

* [Stacks, Tag 09IS], that `D_QCoh(𝒪_X)` has a single perfect generator, and
* [Stacks, Tag 09M1], that a perfect object of `D_QCoh(𝒪_X)` is compact.

The same gap is recorded at
`Stacks.Duality.Supported.exists_isTriangulated_rightAdjoint_of_compactlyGenerated`, in the
supported form ([Stacks, Tag 0A9A] and [Stacks, Tag 0A9B]). The hypothesis is not the conclusion
in disguise: the existence of a right adjoint of the inclusion of a triangulated subcategory says
nothing about compact objects — for `A = ⊤` the inclusion is the identity and has a right adjoint
whatever the ambient category, while `⊤` is compactly generated only for special ambients.

The quasi-compactness and quasi-separatedness of `X` are kept, because they are the hypotheses of
the tag, even though it is the carried hypothesis and not they that the Brown-representability
argument consumes.

## Main results

* `Stacks.Duality.Coherator.isLeftAdjoint_derivedQuasiCoherentι` — **[Stacks, Tag 0CR0]**: the
  inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint.
* `Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_derivedQuasiCoherentι` — the same
  conclusion with the adjoint exhibited as an exact functor and the adjunction as a triangulated
  one, which is what Brown representability produces.

## Implementation notes

The derived category is the locally small one,
`SheafOfModules.hasDerivedCategory` of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`,
supplied by instance search at the explicit universe arguments `.{u, u}`. This is forced rather
than chosen: Brown representability asks for direct sums indexed by the *morphism* universe of
the category, and only at the locally small model is that universe `u`, the universe indexing the
direct sums of `𝒪_X`-modules. With `CategoryTheory.HasDerivedCategory.standard` the morphisms live
in `Type (u + 1)` and the hypothesis is false rather than unavailable; see the implementation notes
of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`.

`Stacks.Duality.Coherator.derivedQuasiCoherent_isTriangulated` and its companion for closure under
isomorphisms are declared here as instances at a *free* model, because they are what gives
`D_QCoh(𝒪_X)` its shift, hence its pretriangulated structure, hence a statement at all. The
library has the same two facts in two shapes neither of which serves: for the meet
`Stacks.Duality.quasiCoherentSupported` of quasi-coherence with a support condition
(`Stacks.Duality.Supported.quasiCoherentSupported_isTriangulated`), which is a different object
property; and for `Stacks.Duality.derivedQuasiCoherent` itself as
`Stacks.Perfect.SupportedQuasicoherent.derivedQuasiCoherent_isTriangulated`, which is elaborated
under a file-level `attribute [local instance] CategoryTheory.HasDerivedCategory.standard` and so
is pinned to the model at which Brown representability does not apply.

## References

* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 09SQ](https://stacks.math.columbia.edu/tag/09SQ)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 0CQR](https://stacks.math.columbia.edu/tag/0CQR)
* [Stacks Project, Tag 0CQS](https://stacks.math.columbia.edu/tag/0CQS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated Opposite
open Stacks.AlgebraicGeometry.QuasicoherentWeakSerre

universe w u

namespace Stacks.Duality.Coherator

/-! ### The triangulated structure of `D_QCoh(𝒪_X)` -/

section Subcategory

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- `D_QCoh(𝒪_X)` is strictly full, for an arbitrary scheme: quasi-coherent modules form a weak
Serre subcategory ([Stacks, Tag 06VT]), and the subcategory of the derived category that a weak
Serre subcategory cuts out is closed under isomorphisms. -/
instance derivedQuasiCoherent_isClosedUnderIsomorphisms :
    (derivedQuasiCoherent X).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (A := SheafOfModules.{u} X.ringCatSheaf) _ (isQuasicoherent_isWeakSerre X)

/-- **`D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`** ([Stacks, Tag 06VT] through
[Stacks, Tag 06UP]): quasi-coherent `𝒪_X`-modules form a weak Serre subcategory, and the
complexes whose cohomology sheaves all lie in a weak Serre subcategory form a strictly full
saturated triangulated subcategory of the derived category. -/
instance derivedQuasiCoherent_isTriangulated : (derivedQuasiCoherent X).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated
    (A := SheafOfModules.{u} X.ringCatSheaf) _ (isQuasicoherent_isWeakSerre X)

end Subcategory

/-! ### The right adjoint `DQ_X` -/

/-- **[Stacks, Tag 0CR0], with compact generation of `D_QCoh(𝒪_X)` as a hypothesis.** Let `X` be a
quasi-compact quasi-separated scheme and suppose `D_QCoh(𝒪_X)` is compactly generated. Then the
inclusion `J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint `DQ_X`, which is moreover exact: the
adjunction `J ⊣ DQ_X` is a triangulated adjunction for a `Functor.CommShift ℤ` structure on
`DQ_X`.

This is the source's second proof. The inclusion is exact and preserves the direct sums indexed by
`Type u` — `D_QCoh(𝒪_X)` is a strictly full triangulated subcategory of `D(𝒪_X)` closed under
those direct sums, [Stacks, Tag 06VT] and [Stacks, Tag 08DT] — so Brown representability
[Stacks, Tag 0A8G] applies to it as soon as the compact generating family is given.

Compact generation is [Stacks, Tag 09IS] together with [Stacks, Tag 09M1] and is carried as a
hypothesis; neither is proved in this repository.

This declaration is not registered as [Stacks, Tag 0CR0]: the tag for every quasi-compact
quasi-separated scheme, with no compact-generation hypothesis, is
`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι` in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCoherator.lean`. -/
theorem exists_isTriangulated_rightAdjoint_derivedQuasiCoherentι (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : IsCompactlyGenerated.{u} (derivedQuasiCoherent.{u, u} X).FullSubcategory) :
    ∃ (DQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
        (derivedQuasiCoherent.{u, u} X).FullSubcategory)
      (adj : (derivedQuasiCoherent.{u, u} X).ι ⊣ DQ) (_ : DQ.CommShift ℤ), adj.IsTriangulated := by
  obtain ⟨I, E, hcompact, hgen⟩ := hX
  let : ∀ i : I, IsCompactObject.{u} (E i) := hcompact
  let (J : Type u) : (derivedQuasiCoherent.{u, u} X).IsClosedUnderColimitsOfShape (Discrete J) :=
    Supported.derivedQuasiCoherent_isClosedUnderCoproducts.{u, u} X J
  let (J : Type u) :
      HasColimitsOfShape (Discrete J) (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
    Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory _ J
  have : HasCoproducts.{u} (derivedQuasiCoherent.{u, u} X).FullSubcategory := fun J =>
    hasColimitsOfShape_of_closedUnderColimits (Discrete J) _
  have : ∀ J : Type u,
      PreservesColimitsOfShape (Discrete J) (derivedQuasiCoherent.{u, u} X).ι :=
    fun _ => inferInstance
  have : ∀ (i : I) (α : Type u),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i))) :=
    fun i α => preservesCoproducts_preadditiveCoyoneda_of_isCompactObject (E i) α
  exact exists_isTriangulated_rightAdjoint_of_compactlyGenerated
    (derivedQuasiCoherent.{u, u} X).ι E hgen

/-- **[Stacks, Tag 0CR0], with compact generation of `D_QCoh(𝒪_X)` as a hypothesis.** For a
quasi-compact quasi-separated scheme `X` whose `D_QCoh(𝒪_X)` is compactly generated, the inclusion
functor `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint `DQ_X`.

This is the tag's own conclusion, read off from
`Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_derivedQuasiCoherentι`, which also
records that the adjoint is exact. The tag asserts existence, so an existence statement —
`CategoryTheory.Functor.IsLeftAdjoint`, the class saying that a right adjoint exists — is the
faithful conclusion; no particular `DQ_X` is chosen.

This declaration is not registered as [Stacks, Tag 0CR0]: the tag for every quasi-compact
quasi-separated scheme, with no compact-generation hypothesis, is
`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι` in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCoherator.lean`. -/
theorem isLeftAdjoint_derivedQuasiCoherentι (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hX : IsCompactlyGenerated.{u} (derivedQuasiCoherent.{u, u} X).FullSubcategory) :
    (derivedQuasiCoherent.{u, u} X).ι.IsLeftAdjoint :=
  have ⟨_, adj, _, _⟩ := exists_isTriangulated_rightAdjoint_derivedQuasiCoherentι X hX
  adj.isLeftAdjoint

end Stacks.Duality.Coherator

end
