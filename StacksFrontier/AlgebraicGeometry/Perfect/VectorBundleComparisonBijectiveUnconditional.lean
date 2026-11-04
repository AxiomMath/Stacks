module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.AcyclicCycles
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.DerivedRoofUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentativeUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# `K₀(Vect(X)) ⟶ K₀(X)` is an isomorphism

`Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom` is the bijectivity half
of [Stacks, Tag 0FDJ], but it carries three hypotheses: `hrep`, which is [Stacks, Tag 0F8F];
`hroof`, which is [Stacks, Tag 0F8G]; and `hcyc`, step (2) of the proof of Tag 0FDJ itself.  This
file discharges all three.

`hcyc` is `Stacks.Perfect.BoundedLocallyFreeComplexes.forall_isFiniteLocallyFree_cycles`, which
assumes nothing at all.  `hrep` and `hroof` are available as soon as the diagonal of `X` is
affine, which is the conclusion of [Stacks, Tag 0F8C] on a quasi-compact and quasi-separated
scheme with the resolution property:
`AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal` of
`StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineDiagonal`.  So [Stacks, Tag 0FDJ]
holds on a quasi-compact and quasi-separated scheme with the resolution property, and the
remaining statements below are the special cases in which the affine diagonal has a reason of its
own: a scheme with affine diagonal, a separated scheme, a Noetherian scheme, a scheme with an ample
invertible module, and an affine scheme.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom_of_affineDiagonal`: the
  comparison homomorphism is bijective on a quasi-compact and quasi-separated scheme with the
  resolution property whose diagonal is affine.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom_of_hasResolutionProperty`:
  **[Stacks, Tag 0FDJ]** — the comparison homomorphism is
  bijective on a quasi-compact and quasi-separated scheme with the resolution property, the
  affine diagonal being deduced from [Stacks, Tag 0F8C].
* `..._of_isSeparated`, `..._of_isNoetherian`, `..._of_isAmple`, `..._of_isAffine`: the same with
  the affine diagonal had some other way.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.inverseAddHom_of_affineDiagonal` and
  `inverseAddHom_comp_comparisonAddHom_of_affineDiagonal`:
  the inverse homomorphism `K₀(X) ⟶ K₀(Vect(X))` of the source, as a homomorphism depending on
  nothing but the scheme, together with the identity that makes it one.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom_spec` and
  `..._projectiveSpace`: the conclusion on `Spec R` for an arbitrary ring `R`, and on `ℙⁿ_S`
  over an affine base, which is not affine for `n ≥ 1`.

## Implementation notes

The ample invertible module on `ℙⁿ_S` is
`Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf`, and its ampleness over an affine
base is `Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf`.

The two instance priorities set at the top of the namespace are the ones recorded in the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparisonBijective`, and both are
load-bearing here for the same reasons: without them the two spellings of the derived category of
the `𝒪_X`-modules are found with different instances and the statements mentioning
`AlgebraicGeometry.comparisonAddHom` do not elaborate.

## References

* [Stacks Project, Tag 0FDJ](https://stacks.math.columbia.edu/tag/0FDJ)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
* [Stacks Project, Tag 0F8G](https://stacks.math.columbia.edu/tag/0F8G)
* [Stacks Project, Tag 0F8C](https://stacks.math.columbia.edu/tag/0F8C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.AmpleProjectiveImmersion
open Stacks.Cohomology.PerfectComplexes
open Stacks.FiniteLocallyFree
open Stacks.ProjectiveSpace

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] hasDerivedCategoryStandardRingedSiteModules

section AffineDiagonal

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [HasResolutionProperty X]

/-- **The inverse of the comparison homomorphism on a scheme with affine diagonal.**  The Euler
characteristic of a bounded complex of finite locally free modules representing a perfect object
defines a homomorphism `K₀(X) ⟶ K₀(Vect(X))`; on a quasi-compact and quasi-separated scheme with
the resolution property and affine diagonal all three of its inputs are available, so it depends
on nothing but the scheme. -/
def inverseAddHom_of_affineDiagonal [IsAffineHom (pullback.diagonal (terminal.from X))] :
    K0 (PerfectDerivedCategory X) →+ VectorBundleKZero X :=
  inverseAddHom X (exists_boundedFiniteLocallyFree_iso_of_affineDiagonal X)
    (exists_boundedFiniteLocallyFree_roof_of_affineDiagonal X)
    (forall_isFiniteLocallyFree_cycles X)

/-- The homomorphism of
`Stacks.Perfect.BoundedLocallyFreeComplexes.inverseAddHom_of_affineDiagonal` is a left inverse of
the comparison homomorphism. -/
@[sga "6 0 3.1" "partial"]
theorem inverseAddHom_comp_comparisonAddHom_of_affineDiagonal
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    (inverseAddHom_of_affineDiagonal X).comp (comparisonAddHom X) = AddMonoidHom.id _ :=
  inverseAddHom_comp_comparisonAddHom X
    (exists_boundedFiniteLocallyFree_iso_of_affineDiagonal X)
    (exists_boundedFiniteLocallyFree_roof_of_affineDiagonal X)
    (forall_isFiniteLocallyFree_cycles X)

/-- **The comparison homomorphism `K₀(Vect(X)) ⟶ K₀(X)` is bijective on a quasi-compact and
quasi-separated scheme with the resolution property and affine diagonal.**

The three hypotheses of
`Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom` are discharged here:
`hrep` is `exists_boundedFiniteLocallyFree_iso_of_affineDiagonal` ([Stacks, Tag 0F8F]), `hroof`
is `exists_boundedFiniteLocallyFree_roof_of_affineDiagonal` ([Stacks, Tag 0F8G]) and `hcyc` is
`forall_isFiniteLocallyFree_cycles`, which assumes nothing. -/
theorem bijective_comparisonAddHom_of_affineDiagonal
    [IsAffineHom (pullback.diagonal (terminal.from X))] : Function.Bijective (comparisonAddHom X) :=
  bijective_comparisonAddHom X (exists_boundedFiniteLocallyFree_iso_of_affineDiagonal X)
    (exists_boundedFiniteLocallyFree_roof_of_affineDiagonal X)
    (forall_isFiniteLocallyFree_cycles X)

end AffineDiagonal

/-- **Stacks Project, Tag 0FDJ.**  On a quasi-compact and quasi-separated scheme with the
resolution property the canonical homomorphism `K₀(Vect(X)) ⟶ K₀(X) = K₀(D_perf(𝒪_X))`, which
sends the class of a finite locally free `𝒪_X`-module to the class of that module placed in
degree zero, is an isomorphism: it is bijective, and it is a homomorphism of abelian groups by
construction.

Surjectivity is
`Stacks.Perfect.BoundedLocallyFreeComplexes.surjective_comparisonAddHom`, which reads off the
class of a bounded complex of finite locally free modules as the alternating sum of the classes
of its terms.  Injectivity is the source's inverse map, the Euler characteristic
`Σᵢ (-1)ⁱ [ℰⁱ]`; it is well defined because two bounded complexes of finite locally free modules
isomorphic in `D(𝒪_X)` are connected by a roof of such complexes ([Stacks, Tag 0F8G]) and because
the Euler characteristic of a bounded acyclic such complex vanishes, the modules of cycles being
finite locally free.

The affine diagonal that both halves need is [Stacks, Tag 0F8C] at these same three conditions,
`AlgebraicGeometry.HasResolutionProperty.isAffineHom_diagonal`. -/
@[stacks 0FDJ, sga "6 0 3.1" "more general"]
theorem bijective_comparisonAddHom_of_hasResolutionProperty (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] [HasResolutionProperty X] :
    Function.Bijective (comparisonAddHom X) :=
  have _ := HasResolutionProperty.isAffineHom_diagonal X
  bijective_comparisonAddHom_of_affineDiagonal X

/-- **`K₀(Vect(X)) ⟶ K₀(X)` is bijective on a quasi-compact separated scheme with the resolution
property.**  A separated scheme has a closed, hence affine, diagonal, so no form of
[Stacks, Tag 0F8C] is needed. -/
theorem bijective_comparisonAddHom_of_isSeparated (X : Scheme.{u}) [CompactSpace X]
    [X.IsSeparated] [HasResolutionProperty X] :
    Function.Bijective (comparisonAddHom X) :=
  bijective_comparisonAddHom_of_affineDiagonal X

/-- **`K₀(Vect(X)) ⟶ K₀(X)` is bijective on a Noetherian scheme with the resolution property.**
This is the special case of
`Stacks.Perfect.BoundedLocallyFreeComplexes.bijective_comparisonAddHom_of_hasResolutionProperty`
in which the affine diagonal comes from the Noetherian case of [Stacks, Tag 0F8C],
`AlgebraicGeometry.isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian`. -/
theorem bijective_comparisonAddHom_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    [HasResolutionProperty X] :
    Function.Bijective (comparisonAddHom X) :=
  have _ : QuasiSeparatedSpace X := IsLocallyNoetherian.quasiSeparatedSpace
  have _ := isAffineHom_diagonal_of_hasResolutionProperty_of_isNoetherian X
  bijective_comparisonAddHom_of_affineDiagonal X

/-- **`K₀(Vect(X)) ⟶ K₀(X)` is bijective on a scheme carrying an ample invertible module.**
Ampleness supplies quasi-compactness, the resolution property ([Stacks, Tag 0F87]) and
separatedness ([Stacks, Tag 09MP]), hence the affine diagonal. -/
@[sga "6 VIII 3.1"]
theorem bijective_comparisonAddHom_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    Function.Bijective (comparisonAddHom X) :=
  have _ : CompactSpace X := hL.1
  have _ : HasResolutionProperty X := hasResolutionProperty_of_isAmple L hL
  have _ : X.IsSeparated :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple X L hL).isSeparated
  bijective_comparisonAddHom_of_isSeparated X

/-- **`K₀(Vect(X)) ⟶ K₀(X)` is bijective on an affine scheme.**  The structure sheaf is ample on
an affine scheme, so no hypothesis on the scheme is left. -/
theorem bijective_comparisonAddHom_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    Function.Bijective (comparisonAddHom X) :=
  bijective_comparisonAddHom_of_isAmple X (Stacks.Ample.unitModule X)
    (Stacks.Ample.isAmple_unitModule_of_isAffine X)

/-- **`K₀(Vect(Spec R)) ⟶ K₀(Spec R)` is bijective for every ring `R`.** -/
theorem bijective_comparisonAddHom_spec (R : CommRingCat.{u}) :
    Function.Bijective (comparisonAddHom (Spec R)) :=
  bijective_comparisonAddHom_of_isAffine (Spec R)

/-- **`K₀(Vect(ℙⁿ_S)) ⟶ K₀(ℙⁿ_S)` is bijective for `S` affine.**  The hyperplane sheaf `𝒪(1)`
is an ample invertible module on `ℙⁿ_S`, a scheme which for `n ≥ 1` is not affine. -/
theorem bijective_comparisonAddHom_projectiveSpace (n : ℕ) (S : Scheme.{u}) [IsAffine S] :
    Function.Bijective (comparisonAddHom (projectiveSpaceOver n S)) :=
  bijective_comparisonAddHom_of_isAmple (projectiveSpaceOver n S)
    (projectiveSpaceTwistingSheaf n S) (isAmple_projectiveSpaceTwistingSheaf n S)

/-! ### The comparison isomorphism -/

section ComparisonAddEquiv

variable (X : Scheme.{u})

/-- **The comparison isomorphism `K₀(Vect(X)) ≃+ K₀(X)`** of a quasi-compact and quasi-separated
scheme with the resolution property: the comparison homomorphism
`AlgebraicGeometry.comparisonAddHom`, which is bijective by [Stacks, Tag 0FDJ]
(`bijective_comparisonAddHom_of_hasResolutionProperty`). -/
def vectorBundleKZeroAddEquiv [CompactSpace X] [QuasiSeparatedSpace X]
    [HasResolutionProperty X] : VectorBundleKZero X ≃+ K0 (PerfectDerivedCategory X) :=
  AddEquiv.ofBijective (comparisonAddHom X)
    (bijective_comparisonAddHom_of_hasResolutionProperty X)

/-- The comparison isomorphism is the comparison homomorphism. -/
@[simp]
theorem vectorBundleKZeroAddEquiv_apply [CompactSpace X] [QuasiSeparatedSpace X]
    [HasResolutionProperty X] (c : VectorBundleKZero X) :
    vectorBundleKZeroAddEquiv X c = comparisonAddHom X c :=
  rfl

/-- The comparison isomorphism sends the class of a finite locally free module `ℰ` to the class
of the perfect object `ℰ[0]`. -/
theorem vectorBundleKZeroAddEquiv_classOf [CompactSpace X] [QuasiSeparatedSpace X]
    [HasResolutionProperty X] (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    vectorBundleKZeroAddEquiv X (VectorBundleKZero.classOf X M) =
      K0.cls (⟨(DerivedCategory.singleFunctor X.Modules 0).obj M,
        isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM⟩ : PerfectDerivedCategory X) :=
  comparisonAddHom_classOf' X M hM

end ComparisonAddEquiv

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
