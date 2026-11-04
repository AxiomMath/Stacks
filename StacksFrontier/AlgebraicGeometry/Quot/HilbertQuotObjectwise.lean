module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyQuotSituation

/-!
# The objectwise comparison of the Hilbert and Quot functors

Stacks 0D00 identifies the Hilbert functor of a morphism `f : X ⟶ Y` of finite presentation with
the Quot functor of its structure sheaf.  This file builds the comparison at a single test
scheme: a family classified by the Hilbert functor is turned into a quotient classified by the
Quot functor of `𝒪_X/X/B`, and back.

## Main definitions

* `AlgebraicGeometry.Space.hilbertFamilySubobject`: the kernel of the quotient a Hilbert family
  determines — the defining ideal sheaf `𝓘_Z ⊆ 𝒪_{X_T}`, read as a subobject of the module
  `F_T` of the Quot situation along `F_T ≅ 𝒪_{X_T}`.
* `AlgebraicGeometry.Space.hilbertFamilyQuotientIso`: **`F_T/𝓘_Z ≅ i_*𝒪_Z`**, the identification
  that makes the four conditions of the Quot functor the three of the Hilbert functor.

## Main results

* `AlgebraicGeometry.Space.hilbertFamilySubobject_mem`: **the forward direction of Stacks 0D00,
  objectwise** — the quotient a Hilbert family determines lies in `Quot_{𝒪_X/X/B}(T)`.

## Implementation notes

**The subobject is `𝓘_Z` transported, not `𝓘_Z`.**  The module the Quot functor takes quotients
of is `F_T`, the inverse image of `𝒪_X` of Stacks 03LU, which is only *isomorphic* to `𝒪_{X_T}`
(`AlgebraicGeometry.Space.baseChangeModuleIsoStructureSheaf`).  So the subobject is
`CategoryTheory.Subobject.mk` of `𝓘_Z.ι` followed by the inverse of that isomorphism, and the
quotient by it is computed in three steps: off `CategoryTheory.Subobject.mk` by
`CategoryTheory.Subobject.underlyingIso` and `CategoryTheory.Limits.cokernelEpiComp`, off the
transport by `CategoryTheory.Limits.cokernelCompIsIso`, and then onto `i_*𝒪_Z` by Stacks 09RP in
degree zero (`AlgebraicGeometry.Space.conormalAlgebraDegreeZeroIso`).

**The ambient-universe abelian structure is removed.**  The `𝒪_{X_T}`-modules here have their
sections in the universe `u` of the schemes.  Left in place,
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is selected ahead of
`SheafOfModules.instAbelian` and leaves the module universe of every subobject and cokernel
below unsolved.

**Naturality.**  Stacks 0D00 asserts an *equality of functors*: the Hilbert functor restricts a
family by taking the inverse image `Z ↦ Z ×_{X_T} X_{T'}` of its closed subspace
(`AlgebraicGeometry.Space.HilbertFamily.baseChange`), while the Quot functor restricts a quotient
by pulling it back (`AlgebraicGeometry.Space.QuotSituation.quotientPullback`).  So the subobject
is cut out here by an arbitrary closed subspace of `X_T`
(`AlgebraicGeometry.Space.definingIdealSubobject`), and the Hilbert family's is the special case.

**The base change `X_T` is spelled as the Quot side spells it**, namely
`AlgebraicGeometry.Space.baseChangeSpace` at
`AlgebraicGeometry.Space.structureSheafTestScheme` rather than
`AlgebraicGeometry.Space.schemeBaseChangeSpace`; the two are the same algebraic space by `rfl`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

add_to_stacks 0D00 "the flatness entry of the dictionary, both directions"
  AlgebraicGeometry.Space.isFlatOver_pushforwardStructureSheaf_iff

add_to_stacks 0D00 "the finite-presentation entry of the dictionary, for a Hilbert family"
  AlgebraicGeometry.Space.isFinitePresentationOnSite_pushforwardStructureSheaf_hilbertFamily_unconditional

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-! ### The subobject cut out by a Hilbert family -/

variable (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  (T : SchemesOverPresheaf B S hS Y)

/-- The inclusion of the defining ideal sheaf of a closed subspace of `X_T` into the module `F_T`
of the Quot situation of `𝒪_X/X/B`, along `F_T ≅ 𝒪_{X_T}`. -/
abbrev definingIdealArrow
    (Zd : ClosedSubspaces B S hS (baseChangeSpace f (structureSheafTestScheme T)).1) :
    (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T))
        Zd).toSheafOfModules ⟶
      (structureSheafQuotSituation f hf).baseChangeModule (structureSheafTestScheme T) :=
  (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T)) Zd).ι ≫
    (baseChangeModuleIsoStructureSheaf f hf T).inv

/-- The transported inclusion of a defining ideal sheaf is a monomorphism. -/
theorem mono_definingIdealArrow
    (Zd : ClosedSubspaces B S hS (baseChangeSpace f (structureSheafTestScheme T)).1) :
    Mono (definingIdealArrow f hf T Zd) :=
  mono_comp'
    (inferInstanceAs (Mono (definingIdealSheaf B S hS
      (baseChangeSpace f (structureSheafTestScheme T)) Zd).ι))
    (@IsIso.mono_of_iso _ _ _ _ (baseChangeModuleIsoStructureSheaf f hf T).inv
      (Iso.isIso_inv (baseChangeModuleIsoStructureSheaf f hf T)))

/-- **The kernel of the quotient a closed subspace of `X_T` determines.**  The defining ideal
sheaf `𝓘_Z` of Stacks 03MB, read as a subobject of the module `F_T` of the Quot situation of
`𝒪_X/X/B` along `F_T ≅ 𝒪_{X_T}`. -/
def definingIdealSubobject
    (Zd : ClosedSubspaces B S hS (baseChangeSpace f (structureSheafTestScheme T)).1) :
    Subobject ((structureSheafQuotSituation f hf).baseChangeModule
      (structureSheafTestScheme T)) :=
  @Subobject.mk _ _ _ _ (definingIdealArrow f hf T Zd) (mono_definingIdealArrow f hf T Zd)

/-- The arrow of that subobject is the transported inclusion of the ideal sheaf, up to the
canonical identification of the underlying object. -/
theorem underlyingIso_inv_comp_definingIdealSubobject_arrow
    (Zd : ClosedSubspaces B S hS (baseChangeSpace f (structureSheafTestScheme T)).1) :
    (@Subobject.underlyingIso _ _ _ _ (definingIdealArrow f hf T Zd)
          (mono_definingIdealArrow f hf T Zd)).inv ≫
        (definingIdealSubobject f hf T Zd).arrow =
      definingIdealArrow f hf T Zd :=
  @Subobject.underlyingIso_arrow _ _ _ _ (definingIdealArrow f hf T Zd)
    (mono_definingIdealArrow f hf T Zd)

/-- The inclusion of the defining ideal sheaf of a family classified by the Hilbert functor into
`F_T`: the case of `AlgebraicGeometry.Space.definingIdealArrow` at the family's closed
subspace. -/
abbrev hilbertFamilyIdealArrow (z : HilbertFamily f T) :
    (definingIdealSheaf B S hS (schemeBaseChangeSpace f T)
        ⟨z.Z, z.closed⟩).toSheafOfModules ⟶
      (structureSheafQuotSituation f hf).baseChangeModule (structureSheafTestScheme T) :=
  definingIdealArrow f hf T ⟨z.Z, z.closed⟩

/-- The transported inclusion of the ideal sheaf of a Hilbert family is a monomorphism. -/
theorem mono_hilbertFamilyIdealArrow (z : HilbertFamily f T) :
    Mono (hilbertFamilyIdealArrow f hf T z) :=
  mono_definingIdealArrow f hf T ⟨z.Z, z.closed⟩

/-- **The kernel of the quotient a Hilbert family determines.**  For a family `Z ⊆ X_T` classified
by the Hilbert functor of `f` over `T`, the defining ideal sheaf `𝓘_Z` of Stacks 03MB, read as a
subobject of the module `F_T` of the Quot situation of `𝒪_X/X/B`. -/
def hilbertFamilySubobject (z : HilbertFamily f T) :
    Subobject ((structureSheafQuotSituation f hf).baseChangeModule
      (structureSheafTestScheme T)) :=
  definingIdealSubobject f hf T ⟨z.Z, z.closed⟩

/-- The subobject a Hilbert family cuts out is the one cut out by its closed subspace. -/
theorem hilbertFamilySubobject_eq_definingIdealSubobject (z : HilbertFamily f T) :
    hilbertFamilySubobject f hf T z = definingIdealSubobject f hf T ⟨z.Z, z.closed⟩ :=
  rfl

/-- The arrow of that subobject is the transported inclusion of the ideal sheaf, up to the
canonical identification of the underlying object. -/
theorem underlyingIso_inv_comp_hilbertFamilySubobject_arrow (z : HilbertFamily f T) :
    (@Subobject.underlyingIso _ _ _ _ (hilbertFamilyIdealArrow f hf T z)
          (mono_hilbertFamilyIdealArrow f hf T z)).inv ≫
        (hilbertFamilySubobject f hf T z).arrow =
      hilbertFamilyIdealArrow f hf T z :=
  underlyingIso_inv_comp_definingIdealSubobject_arrow f hf T ⟨z.Z, z.closed⟩

/-- The identification of the underlying object of the subobject with the ideal sheaf, read
backwards, is an epimorphism. -/
theorem epi_underlyingIso_inv_hilbertFamilyIdealArrow (z : HilbertFamily f T) :
    Epi (@Subobject.underlyingIso _ _ _ _ (hilbertFamilyIdealArrow f hf T z)
      (mono_hilbertFamilyIdealArrow f hf T z)).inv :=
  @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)

/-- **`F_T/𝓘_Z ≅ i_*𝒪_Z`.**  The quotient of `F_T` by the subobject a Hilbert family cuts out is
the direct image of the structure sheaf of the family (Stacks 09RP in degree zero). -/
def hilbertFamilyQuotientIso (z : HilbertFamily f T) :
    (structureSheafQuotSituation f hf).quotientModule (structureSheafTestScheme T)
        (hilbertFamilySubobject f hf T z) ≅
      pushforwardStructureSheaf B S hS (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩ := by
  letI := mono_hilbertFamilyIdealArrow f hf T z
  letI := epi_underlyingIso_inv_hilbertFamilyIdealArrow f hf T z
  exact (cokernelEpiComp (Subobject.underlyingIso (hilbertFamilyIdealArrow f hf T z)).inv
      (hilbertFamilySubobject f hf T z).arrow).symm ≪≫
    cokernelIsoOfEq (underlyingIso_inv_comp_hilbertFamilySubobject_arrow f hf T z) ≪≫
    @cokernelCompIsIso _ _ _ _ _ _
      (definingIdealSheaf B S hS (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩).ι
      (baseChangeModuleIsoStructureSheaf f hf T).inv _
      (Iso.isIso_inv (baseChangeModuleIsoStructureSheaf f hf T)) ≪≫
    conormalAlgebraDegreeZeroIso B S hS (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩

/-! ### The forward direction of Stacks 0D00, objectwise -/

/-- The quotient `F_T/𝓘_Z` is quasi-coherent. -/
theorem isQuasicoherentOnSite_hilbertFamilyQuotient (z : HilbertFamily f T) :
    ((structureSheafQuotSituation f hf).quotientModule (structureSheafTestScheme T)
      (hilbertFamilySubobject f hf T z)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (hilbertFamilyQuotientIso f hf T z).symm
    (isQuasicoherentOnSite_pushforwardStructureSheaf B S hS
      (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩)

/-- The quotient `F_T/𝓘_Z` is flat over the test scheme, because `Z ⟶ T` is. -/
theorem isFlatOver_hilbertFamilyQuotient (z : HilbertFamily f T) :
    IsFlatOver B S hS ((structureSheafQuotSituation f hf).space
        (structureSheafTestScheme T)).2
      ((structureSheafQuotSituation f hf).projection (structureSheafTestScheme T)).hom
      ((structureSheafQuotSituation f hf).quotientModule (structureSheafTestScheme T)
        (hilbertFamilySubobject f hf T z)) :=
  IsFlatOver.of_iso B S hS _ (hilbertFamilyQuotientIso f hf T z).symm
    (isFlatOver_pushforwardStructureSheaf_of_isFlat B S hS
      (X := schemeBaseChangeSpace f T) (T := schemeOverSpace T) ⟨z.Z, z.closed⟩
      (schemeBaseChangeProjectionHom B S hS f T) z.flat)

/-- The quotient `F_T/𝓘_Z` is of finite presentation, because `Z ⟶ T` is and `i` is therefore of
finite presentation: Modules on Sites, Lemma 0610 through Stacks 05WT. -/
theorem isFinitePresentationOnSite_hilbertFamilyQuotient (z : HilbertFamily f T) :
    ((structureSheafQuotSituation f hf).quotientModule (structureSheafTestScheme T)
      (hilbertFamilySubobject f hf T z)).IsFinitePresentationOnSite :=
  SheafOfModules.IsFinitePresentationOnSite.of_iso (hilbertFamilyQuotientIso f hf T z).symm
    (isFinitePresentationOnSite_pushforwardStructureSheaf_hilbertFamily_unconditional f hf T z)

/-- The quotient `F_T/𝓘_Z` has support proper over the test scheme, because `Z ⟶ T` is
proper. -/
theorem isProperlySupportedOver_hilbertFamilyQuotient (z : HilbertFamily f T) :
    (structureSheafQuotSituation f hf).IsProperlySupportedOver (structureSheafTestScheme T)
      ((structureSheafQuotSituation f hf).quotientModule (structureSheafTestScheme T)
        (hilbertFamilySubobject f hf T z)) := by
  have hsupp := supportOfSheaf_eq_of_iso B S hS
    ((structureSheafQuotSituation f hf).space (structureSheafTestScheme T))
    (hilbertFamilyQuotientIso f hf T z)
  refine hasProperSupport_of_subset B S hS _ _ _ _ ?_ (le_of_eq hsupp)
    ((hasProperSupport_pushforwardStructureSheaf_iff B S hS
      (X := schemeBaseChangeSpace f T) (T := schemeOverSpace T) ⟨z.Z, z.closed⟩
      (schemeBaseChangeProjectionHom B S hS f T) _).2 z.proper)
  rw [hsupp]
  exact isClosed_supportOfSheaf_pushforwardStructureSheaf B S hS
    (schemeBaseChangeSpace f T) ⟨z.Z, z.closed⟩

/-- The quotient of `F_T` that a family classified by the Hilbert functor of `f` over `T`
determines lies in `Quot_{𝒪_X/X/B}(T)`: it is quasi-coherent, of finite presentation, flat over
`T` and has support proper over `T`. -/
@[stacks 0D00 "the forward construction: a Hilbert family is a quotient of the structure sheaf"]
theorem hilbertFamilySubobject_mem (z : HilbertFamily f T) :
    hilbertFamilySubobject f hf T z ∈
      (structureSheafQuotSituation f hf).properlySupportedQuotients
        (structureSheafTestScheme T) :=
  ⟨⟨⟨isQuasicoherentOnSite_hilbertFamilyQuotient f hf T z,
      isFlatOver_hilbertFamilyQuotient f hf T z⟩,
    isFinitePresentationOnSite_hilbertFamilyQuotient f hf T z⟩,
    isProperlySupportedOver_hilbertFamilyQuotient f hf T z⟩

/-! ### The forward map on the schemes of the site -/

/-- **The forward map of Stacks 0D00 at a scheme of the site.**  A family classified by the
Hilbert functor of `f` over a scheme `T` of the big fppf site determines a quotient classified by
the Quot functor of `𝒪_X/X/B` over `T`, lying over the same morphism to `Y`: the quotient of
`F_T` by the defining ideal sheaf of the family. -/
def quotFamilyOfHilbertFamilyOver {Tsch : BigFppfOver B S hS} (x : HilbertFamilyOver f Tsch) :
    QuotFamilyOver (structureSheafQuotSituation f hf) Tsch where
  toBase := ObjectProperty.homMk x.toBase
  subobject := hilbertFamilySubobject f hf (CostructuredArrow.mk x.toBase) x.family
  mem := hilbertFamilySubobject_mem f hf (CostructuredArrow.mk x.toBase) x.family

/-- The forward map does not change the morphism to the base `Y`. -/
@[simp]
theorem quotFamilyOfHilbertFamilyOver_toBase_hom {Tsch : BigFppfOver B S hS}
    (x : HilbertFamilyOver f Tsch) :
    (quotFamilyOfHilbertFamilyOver f hf x).toBase.hom = x.toBase :=
  rfl

end AlgebraicGeometry.Space

end
