module

public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineQuasiIso
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentCohomologySheaves
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksFrontier.Homology.DoubleHomology
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology sheaves of the naive cotangent complex are quasi-coherent

For a morphism of schemes `f : X ⟶ Y` the cohomology sheaves `H^i(NL_{X/Y})` are quasi-coherent
sheaves of `𝒪_X`-modules, for every `i`. This is the quasi-coherence clause of
[Stacks Project, Tag 0D0J].

## Main results

* `AlgebraicGeometry.Scheme.isQuasicoherent_homology_naiveCotangentComplex_negOne`: the degree
  `-1` cohomology sheaf is quasi-coherent.
* `AlgebraicGeometry.Scheme.isQuasicoherent_homology_naiveCotangentComplex`: every cohomology
  sheaf is quasi-coherent.

## Implementation notes

Degrees other than `-1` and `0` are zero by
`AlgebraicGeometry.Scheme.isZero_homology_naiveCotangentComplex`, and degree `0` is `Ω_{X/Y}` by
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_naiveCotangentComplex_zero`. Only degree `-1`
needs the affine-local argument, which is the source's: quasi-coherence is local
(`Stacks.Modules.isQuasicoherent_of_restrict`), so it suffices to treat the restriction of
`H^{-1}(NL_{X/Y})` to an affine open `V ⊆ f^{-1}U` with `U ⊆ Y` affine, and every point of `X`
lies in such a `V`.

On such a `V` the chain is:

* restriction along an open immersion is exact, so it commutes with cohomology
  (`Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso`); the restriction of
  `NL_{X/Y}` is `Stacks.NaiveCotangentAffineIso.restrictedNaiveCotangentComplex`;
* that complex is quasi-isomorphic to `(NL_{A/R})~` by Stacks 0D0I
  (`Stacks.NaiveCotangentAffineQuasiIso.quasiIso_comparisonMap`), so the two have isomorphic
  degree `-1` cohomology sheaves;
* `(NL_{A/R})~` is a `HomologicalComplex.double`, so its degree `-1` cohomology sheaf is the
  kernel of its differential, and its two terms are quasi-coherent by
  `Stacks.AssociatedSheaf.isQuasicoherent_associatedSheafFunctor_obj`; a kernel of a morphism of
  quasi-coherent modules is quasi-coherent
  (`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`).

Note that *no* exactness of the associated-sheaf construction is needed: the complex has two
terms, so its degree `-1` cohomology sheaf is a kernel outright.

`Functor.PreservesHomology` of the restriction functor is not an instance in the library; it is
produced here from `AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor` through
`CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels`, and passed positionally,
since instance search does not find it on its own.

## References

* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J)
* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), the affine comparison.
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE), quasi-coherence.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.NaiveCotangentAffineIso

universe u

namespace AlgebraicGeometry.Scheme

/-- The degree `-1` cohomology sheaf of `(NL_{A/R})~` is quasi-coherent: the complex has two
terms, both quasi-coherent, so that sheaf is the kernel of a morphism of quasi-coherent
modules. -/
private theorem isQuasicoherent_homology_associatedNaiveCotangentComplex {X : Scheme.{u}}
    {V : X.Opens} {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U) :
    ((associatedNaiveCotangentComplex f hVU).homology (-1)).IsQuasicoherent := by
  have h1 := Stacks.AssociatedSheaf.isQuasicoherent_associatedSheafFunctor_obj
    V.toScheme.toRingedSpace (alpha (V := V)) (nlSelfModNegOne f hVU)
  have h2 := Stacks.AssociatedSheaf.isQuasicoherent_associatedSheafFunctor_obj
    V.toScheme.toRingedSpace (alpha (V := V)) (nlSelfModZero f hVU)
  have e : (associatedNaiveCotangentComplex f hVU).homology (-1) ≅
      kernel ((Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} (V.toScheme.toRingedSpace)
        (alpha (V := V))).map (nlSelfModD f hVU)) :=
    HomologicalComplex.doubleHomologyIsoKernel _
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
  have hk := @Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel.{u} V.toScheme
    ((Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} (V.toScheme.toRingedSpace)
      (alpha (V := V))).obj (nlSelfModNegOne f hVU))
    ((Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} (V.toScheme.toRingedSpace)
      (alpha (V := V))).obj (nlSelfModZero f hVU))
    ((Stacks.AssociatedSheaf.associatedSheafFunctor.{u, u} (V.toScheme.toRingedSpace)
      (alpha (V := V))).map (nlSelfModD f hVU)) h1 h2
  exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso e.symm hk

/-- **Stacks 0D0I in degree `-1`.** For `U ⊆ Y` and `V ⊆ f^{-1}U` affine opens, the degree `-1`
cohomology sheaf of `NL_{X/Y}|_V` is quasi-coherent: the canonical map from `(NL_{A/R})~` is a
quasi-isomorphism, so the two cohomology sheaves agree. -/
private theorem isQuasicoherent_homology_restrictedNaiveCotangentComplex {X : Scheme.{u}}
    {V : X.Opens} {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((restrictedNaiveCotangentComplex f (V := V)).homology (-1)).IsQuasicoherent := by
  have hq : QuasiIso (Stacks.NaiveCotangentAffineMap.comparisonMap f hVU) :=
    Stacks.NaiveCotangentAffineQuasiIso.quasiIso_comparisonMap V f hVU hU hV
  have hiso : IsIso (HomologicalComplex.homologyMap
      (Stacks.NaiveCotangentAffineMap.comparisonMap f hVU) (-1)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp (hq.quasiIsoAt (-1))
  exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ _ hiso)
    (isQuasicoherent_homology_associatedNaiveCotangentComplex f hVU)

/-- The restriction of `H^{-1}(NL_{X/Y})` to an affine open `V` lying over an affine open of `Y`
is quasi-coherent: restriction along an open immersion is exact, so it commutes with cohomology,
and the restricted complex is covered by the previous statement. -/
private theorem isQuasicoherent_restrict_homology_naiveCotangentComplex {X : Scheme.{u}}
    {V : X.Opens} {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).obj
      ((naiveCotangentComplex f).homology (-1))).IsQuasicoherent := by
  have hph : Functor.PreservesHomology (Scheme.Modules.restrictFunctor (V : X.Opens).ι) := by
    have h1 := AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor (V : X.Opens).ι
    exact Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
    (@Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso _ _ _ _ _ _ _ _
      (Scheme.Modules.restrictFunctor (V : X.Opens).ι) inferInstance hph
      (naiveCotangentComplex f) (-1) inferInstance inferInstance)
    (isQuasicoherent_homology_restrictedNaiveCotangentComplex f hVU hU hV)

/-- **Stacks 0D0J, quasi-coherence in degree `-1`.** The degree `-1` cohomology sheaf of the
naive cotangent complex of a morphism of schemes is quasi-coherent. Every point of `X` lies in
an affine open `V` contained in the preimage of an affine open of `Y`, and quasi-coherence is
local. -/
theorem isQuasicoherent_homology_naiveCotangentComplex_negOne {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((naiveCotangentComplex f).homology (-1)).IsQuasicoherent := by
  have key : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      ((Scheme.Modules.restrictFunctor (W : X.Opens).ι).obj
        ((naiveCotangentComplex f).homology (-1))).IsQuasicoherent := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (f.base x))
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ U) (x := x) hxU
    exact ⟨W, hxW,
      isQuasicoherent_restrict_homology_naiveCotangentComplex f hWU hU hW⟩
  choose W hxW hqc using key
  refine Stacks.Modules.isQuasicoherent_of_restrict _ W ?_ hqc
  exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩

/-- **Stacks 0D0J, quasi-coherence clause.** Every cohomology sheaf of the naive cotangent
complex `NL_{X/Y}` of a morphism of schemes is a quasi-coherent sheaf of `𝒪_X`-modules: in
degree `-1` by the affine-local argument, in degree `0` because it is `Ω_{X/Y}`, and in every
other degree because it is zero. -/
@[stacks 0D0J "quasi-coherence of the cohomology sheaves; not H^0 = Omega, not the vanishing"]
theorem isQuasicoherent_homology_naiveCotangentComplex {X Y : Scheme.{u}} (f : X ⟶ Y) (i : ℤ) :
    ((naiveCotangentComplex f).homology i).IsQuasicoherent := by
  by_cases hneg : i = -1
  · subst hneg
    exact isQuasicoherent_homology_naiveCotangentComplex_negOne f
  by_cases hzero : i = 0
  · subst hzero
    exact isQuasicoherent_homology_naiveCotangentComplex_zero f
  exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero.{u}
    (R := X.ringCatSheaf) (isZero_homology_naiveCotangentComplex f i hneg hzero)

end AlgebraicGeometry.Scheme

end
