module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.Acyclicity
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ExtendedAlternatingCechComparison
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedEquivalence
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# The extended alternating Čech complex computes the local cohomology sheaves

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions, let `Z` be their common
zero locus and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion.  The extended alternating
Čech complex `𝓕^•` of [Stacks, Tag 0G7I] of a quasi-coherent `𝒪_X`-module `F` is acyclic off
`Z` by [Stacks, Tag 0G7K], so its cohomology sheaves are supported on `Z`; therefore [Stacks,
Tag 0AEF] part (2) applies to it and the canonical map `i_* R𝓗_Z(𝓕^•) ⟶ 𝓕^•` is invertible.
Combined with [Stacks, Tag 0G7M], which says that `R𝓗_Z` inverts the augmentation
`𝓕^• ⟶ F[0]`, this identifies the direct image of each local cohomology sheaf of `F` with the
corresponding cohomology sheaf of the complex:

`i_* 𝓗 ⁿ_Z(F) ≅ Hⁿ(𝓕^•)`.

In the top degree `n = c` the right-hand side is the cokernel
`Coker(⨁ᵢ F_{1…î…c} ⟶ F_{1…c})` of the last Čech differential, which is the module the fraction
class of [Stacks, Tag 0G7Q] lands in; so this isomorphism is the step of that construction which
passes from the Čech cokernel to the local cohomology sheaf.

## Main definitions

* `Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso`: the isomorphism
  `i_* 𝓗 ⁿ_Z(F) ≅ Hⁿ(𝓕^•)`.

## Main results

* `Stacks.Perfect.CechLocalCohomology.cohomologySupportedOn_extendedAlternatingCech`: the
  cohomology sheaves of the extended alternating Čech complex are supported on the common zero
  locus of the equations.

## Implementation notes

Support is a condition on the stalks of the cohomology sheaves at the points off `Z`, whereas
[Stacks, Tag 0G7K] is the acyclicity of the restriction of the complex to the union of the
principal opens of the equations.  The passage between the two is stalkwise: the stalk complex
of the restriction at a point of the union is the stalk complex of the complex itself at that
point, by `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, so the acyclicity gives
exactness of the latter; and the stalk functor is exact, hence commutes with homology, so the
stalk of a cohomology sheaf vanishes exactly when the stalk complex is exact there.

The stalk functor is used in its `ModuleCat 𝒪ₓ`-valued form composed with the forgetful functor
to abelian groups, rather than in the `AddCommGrpCat`-valued form in which support is stated:
the two agree by `AlgebraicGeometry.SheafOfModules.stalkFunctor_comp_forget₂`, but only the
composite has its additivity and exactness available to instance synthesis.

The complex is `ℕ`-indexed and the derived category is `ℤ`-indexed, so the comparison runs
through `HomologicalComplex.extend` along `ComplexShape.embeddingUpNat`: in a negative degree
the extension vanishes, hence so does its homology, and in a degree `n : ℕ` the two homologies
agree by `HomologicalComplex.extendHomologyIso`.

The isomorphism of the main definition is the composite of four: the inverse of `Hⁿ` of the
isomorphism `R𝓗_Z(𝓕^•) ≅ R𝓗_Z(F[0])` of [Stacks, Tag 0G7M], pushed forward; the comparison
`i_*(Hⁿ(M)) ≅ Hⁿ(i_*^D M)` available because `i_*` is exact; `Hⁿ` of the invertible canonical
map `i_* R𝓗_Z(𝓕^•) ⟶ 𝓕^•` of [Stacks, Tag 0AEF] part (2); and the identification of the
derived-category cohomology of a complex with its own homology.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7K](https://stacks.math.columbia.edu/tag/0G7K)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.ExtendedAlternatingCech (data augmentation)
open AlgebraicGeometry.SheafOfModules (stalkFunctor stalkShortComplex)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechLocalCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Stalks of cohomology sheaves -/

/-- Taking the stalk at `x` of a sheaf of modules, through the stalk over the stalk ring
followed by the forgetful functor to abelian groups.  This is the stalk functor in which
support is stated, written so that its additivity and exactness are found by synthesis. -/
private abbrev stalkAb {T : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
    (x : T) : _root_.SheafOfModules.{u} O ⥤ AddCommGrpCat.{u} :=
  stalkFunctor O x ⋙
    forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := T) O.obj x))
      AddCommGrpCat.{u}

/-- A cohomology sheaf of a complex of sheaves of modules has vanishing stalk at a point where
the complex of stalks is exact: the stalk functor is exact, so it commutes with homology. -/
private theorem isZero_stalk_homology {T : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (x : T)
    {ι : Type} {cs : ComplexShape ι} (K : HomologicalComplex (_root_.SheafOfModules.{u} O) cs)
    (n : ι) [K.HasHomology n] (h : (stalkShortComplex O (K.sc n) x).Exact) :
    IsZero (TopCat.Presheaf.stalk (K.homology n).val.presheaf x) := by
  have hGA : ((K.sc n).map (stalkAb O x)).Exact := h
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).1 hGA)
    ((K.sc n).mapHomologyIso (stalkAb O x)).symm

/-- The stalk of a sheaf of modules vanishes at `x` if that of an isomorphic sheaf does. -/
private theorem isZero_stalk_of_iso {T : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (x : T)
    {A B : _root_.SheafOfModules.{u} O} (e : A ≅ B)
    (h : IsZero (TopCat.Presheaf.stalk B.val.presheaf x)) :
    IsZero (TopCat.Presheaf.stalk A.val.presheaf x) :=
  IsZero.of_iso h ((stalkAb O x).mapIso e)

variable {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)

/-- **Stacks Project, Tag 0G7K**, stalkwise.  At a point of the union of the principal opens of
the equations, the complex of stalks of the extended alternating Čech complex is exact in every
degree: the restriction of the complex to that union is acyclic, and the stalk complex of the
restriction at such a point is the stalk complex of the complex itself. -/
private theorem stalkShortComplex_exact_at (n : ℕ)
    (y : (⨆ i, X.basicOpen (f i) : X.Opens).toScheme) :
    (stalkShortComplex (structureSheafRing X.toRingedSpace) ((data f F).complex.sc n)
      ((⨆ i, X.basicOpen (f i) : X.Opens).ι.base y)).Exact := by
  have hex : ((((Scheme.Modules.pullback (⨆ i, X.basicOpen (f i) : X.Opens).ι
      ).mapHomologicalComplex (ComplexShape.up ℕ)).obj (data f F).complex).sc n).Exact :=
    AlgebraicGeometry.ExtendedAlternatingCech.acyclic_on_equationsComplement f F n
  have hstalk := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheafRing
      (⨆ i, X.basicOpen (f i) : X.Opens).toScheme.toRingedSpace) _).1 hex y
  let j := (⨆ i, X.basicOpen (f i) : X.Opens).ι
  let P := Scheme.Modules.toPresheaf (⨆ i, X.basicOpen (f i) : X.Opens).toScheme ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let e := Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback j).symm P ≪≫
    Scheme.Modules.restrictStalkNatIso j y
  let S := (data f F).complex.sc n
  let eS : S.map (Scheme.Modules.pullback j ⋙ P) ≅
      S.map (Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j.base y)) :=
    ShortComplex.isoMk (e.app S.X₁) (e.app S.X₂) (e.app S.X₃)
      (by simpa [Scheme.Modules.toPresheaf_map] using (e.hom.naturality S.f).symm)
      (by simpa [Scheme.Modules.toPresheaf_map] using (e.hom.naturality S.g).symm)
  exact (ShortComplex.exact_iff_of_iso eS).1 hstalk

/-- **Stacks Project, Tag 0G7K**, as a support statement.  The cohomology sheaves of the
extended alternating Čech complex of the equations `f₁, …, f_c` are supported on their common
zero locus: the complex is acyclic on the complement, which is the union of the principal opens
of the equations.

This is the hypothesis under which [Stacks, Tag 0AEF] part (2) applies to the complex. -/
@[stacks 0G7K "the cohomology sheaves are supported on the common zero locus"]
theorem cohomologySupportedOn_extendedAlternatingCech :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace)
      (equationsClosedSet f)
      (DerivedCategory.Q.obj ((data f F).complex.extend ComplexShape.embeddingUpNat)) := by
  intro i x hx
  have hxU : x ∈ (⨆ j, X.basicOpen (f j) : X.Opens) := by
    simpa [equationsClosedSet] using hx
  have key : IsZero (TopCat.Presheaf.stalk
      (((data f F).complex.extend ComplexShape.embeddingUpNat).homology i).val.presheaf x) := by
    match i with
    | Int.negSucc k =>
        refine Functor.map_isZero (stalkAb (structureSheafRing X.toRingedSpace) x) ?_
        have hX : IsZero ((((data f F).complex.extend ComplexShape.embeddingUpNat).sc
            (Int.negSucc k)).X₂) :=
          (data f F).complex.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc k)
            (by intro m; simp)
        exact ShortComplex.isZero_homology_of_isZero_X₂ _ hX
    | Int.ofNat n =>
        exact isZero_stalk_of_iso _ x ((data f F).complex.extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := Int.ofNat n) rfl)
          (isZero_stalk_homology _ x _ n (stalkShortComplex_exact_at f F n ⟨x, hxU⟩))
  exact isZero_stalk_of_iso _ x ((DerivedCategory.homologyFunctorFactors X.Modules i).app
    ((data f F).complex.extend ComplexShape.embeddingUpNat)) key

/-! ### The direct image of the local cohomology sheaves -/

/-- **The extended alternating Čech complex computes the local cohomology sheaves.**  For a
quasi-coherent `𝒪_X`-module `F` and the common zero locus `Z` of the equations, the direct image
of the local cohomology sheaf `𝓗 ⁿ_Z(F)` along the inclusion of `Z` is the degree-`n` cohomology
sheaf of the extended alternating Čech complex of `F`.

In the top degree the right-hand side is the cokernel of the last Čech differential, the module
in which the fraction class of [Stacks, Tag 0G7Q] takes its values. -/
@[stacks 0G7M "the complex computes the local cohomology sheaves"]
def pushforwardLocalCohomologyIso [F.IsQuasicoherent] (n : ℕ) :
    letI := pushforward_preservesFiniteLimits X.toRingedSpace (equationsClosedSet f)
    letI := pushforward_preservesFiniteColimits X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f)
    (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).obj
        (localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f) (n : ℤ)
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≅
      (data f F).complex.homology n :=
  letI := pushforward_preservesFiniteLimits X.toRingedSpace (equationsClosedSet f)
  letI := pushforward_preservesFiniteColimits X.toRingedSpace (equationsClosedSet f)
    (isClosed_equationsClosedSet f)
  letI : IsIso ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f)).map (augmentation f F)) :=
    Stacks.Perfect.CechComparison.isIso_derivedSupportedSectionsOnClosed_map_augmentation f F
  (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).mapIso
      ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
        (asIso ((derivedSupportedSectionsOnClosed X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f)).map (augmentation f F)))).symm ≪≫
    (((modulePushforward (closedSubsetInclusion X.toRingedSpace
        (equationsClosedSet f))).mapDerivedCategoryHomologyFunctorIso (n : ℤ)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules (n : ℤ)).mapIso
      (derivedPushforwardSupportedSectionsIso X.toRingedSpace (equationsClosedSet f)
        (isClosed_equationsClosedSet f) _ (cohomologySupportedOn_extendedAlternatingCech f F)) ≪≫
    (DerivedCategory.homologyFunctorFactors X.Modules (n : ℤ)).app _ ≪≫
    (data f F).complex.extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl

end Stacks.Perfect.CechLocalCohomology

end
