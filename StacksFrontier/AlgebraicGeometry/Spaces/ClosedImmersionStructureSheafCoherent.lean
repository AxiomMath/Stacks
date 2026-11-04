module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactKernelQuasicoherent

/-!
# Coherence of the direct image of the structure sheaf along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  This file proves that the `𝒪_X`-module `i_*𝒪_Z` is quasi-coherent, and that it is
coherent as soon as `X` is locally Noetherian.

The route is the one of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceQuotientQuasicoherent.lean`, carried out for
an arbitrary closed immersion rather than for the inclusion of a closed subspace presented as a
subfunctor.  The canonical map `𝒪_X ⟶ i_*𝒪_Z` is the structure map of `i` read as
a map of `𝒪_X`-modules; it is an epimorphism by the surjectivity clause of Stacks 03MB, and its
kernel is the kernel ideal sheaf `𝓘 = ker(i♯)` of `AlgebraicGeometry.Space.kernelIdealSheaf` on
the nose.  So `i_*𝒪_Z = 𝒪_X/𝓘`, and:

* `𝓘` is cartesian on affine charts because `i` is quasi-compact, which is
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernelIdealSheaf`, and so is `𝒪_X`; the
  projection onto the quotient is surjective on the sections over an affine chart, again by the
  affine case of Stacks 03MB, and the pair `𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z` is exact on sections over every
  chart because the sections of `𝓘` *are* the kernel of `i♯` there; so the quotient is cartesian
  on affine charts by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel`, hence
  quasi-coherent.
* `𝒪_X` is coherent when `X` is locally Noetherian, which is Stacks 07UB for the structure sheaf,
  and a quasi-coherent quotient of a coherent module is coherent, which is the quotient clause of
  Stacks 07UD.

Neither step uses Descent, Proposition 03DX(2) beyond the direction
`quasi-coherent ⟹ cartesian`, which is proved, and neither uses the case of schemes; so no
chart case of Stacks 03DW is owed.  This is what makes the statement available where the
reduction of `StacksFrontier/AlgebraicGeometry/Spaces/CoherentPushforwardReduction.lean` is not: the
coherence assertion of Stacks 07UH for a general finite morphism and a general coherent module
really does need the case of a chart, but for the structure sheaf along a *closed* immersion the
module is a quotient of `𝒪_X` by an ideal that is already known to be quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Space.structureSheafPushforward`: the direct image `i_*𝒪_Z` of the structure
  sheaf along a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.pushforwardStructureProjection`: the canonical map `𝒪_X ⟶ i_*𝒪_Z`.

## Main results

* `AlgebraicGeometry.Space.epi_pushforwardStructureProjection`: `𝒪_X ⟶ i_*𝒪_Z` is an
  epimorphism for a closed immersion, by the surjectivity clause of Stacks 03MB.
* `AlgebraicGeometry.Space.exact_val_app_pushforwardStructureProjection`: the pair
  `𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z` is exact on the sections over every object of the small étale site, with no
  hypothesis at all.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_structureSheafPushforward`: `i_*𝒪_Z` is
  cartesian on affine charts.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_structureSheafPushforward`: **`i_*𝒪_Z` is
  quasi-coherent**, with no hypothesis beyond the closed immersion.  This is the
  closed-immersion case of Stacks 03M9 for the structure sheaf.
* `AlgebraicGeometry.Space.isCoherent_structureSheafPushforward`: **`i_*𝒪_Z` is coherent** when
  `X` is locally Noetherian.  This is the case of the structure sheaf along a closed immersion of
  the coherence assertion of Stacks 07UH.

## Implementation notes

`AlgebraicGeometry.Space.pushforwardStructureProjection` is the arbitrary-morphism form of
`AlgebraicGeometry.Space.structureProjection`, which
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraDegreeZero.lean` builds for the inclusion of
a closed subspace.  The two are the same construction; what the generalization costs is that the
defining ideal sheaf of a closed subspace, `AlgebraicGeometry.Space.definingIdealSheaf`, is
replaced by `AlgebraicGeometry.Space.kernelIdealSheaf` of the morphism, whose cartesianity on
affine charts is available for every quasi-compact morphism and in particular for a closed
immersion (`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion'`).  No comparison
between the two settings is needed, and nothing identifies a closed immersion with the inclusion
of its image subfunctor here.

The projection's map on sections is the structure map `i♯` itself, stated as an equality of
*functions* (`pushforwardStructureProjection_val_app_hom_eq`, proved by `rfl`) rather than used
through definitional unfolding, for the reason recorded in the sibling file: the unfolding of
`AlgebraicGeometry.Space.structureSharp` passes through declarations that the module system does
not expose.

No `@[stacks 03M9]` or `@[stacks 07UH]` attribute is claimed.  Quasi-coherence of a direct image
is Stacks 03M9 for a quasi-compact quasi-separated morphism and an arbitrary quasi-coherent
module, and coherence of a direct image is Stacks 07UH for a finite morphism and an arbitrary
coherent module; what is proved here is the single case of the structure sheaf along a closed
immersion, an input to other tags rather than a clause of either.

## References

* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS}

/-- **The direct image `i_*𝒪_Z`** of the structure sheaf of `Z` along a morphism `i : Z ⟶ X` of
algebraic spaces, as an `𝒪_X`-module on the small étale site of `X`.

The direct image is the pushforward half of Stacks 03LU,
`AlgebraicGeometry.Space.modulePushforward`, applied to the structure sheaf of `Z` read as a
module over itself. -/
def structureSheafPushforward (i : Z ⟶ X) : Modules.{u, u} B S hS X.1 X.2 :=
  (modulePushforward B S hS i).obj (SheafOfModules.unit (structureRingSheaf B S hS Z))

/-- The canonical map `𝒪_X ⟶ i_*𝒪_Z` of `𝒪_X`-modules along a morphism `i : Z ⟶ X` of algebraic
spaces, given on sections over an object of the small étale site of `X` by the structure map of
`i`.

The sections of `i_*𝒪_Z` over such an object are its sections as a sheaf of rings, so the
underlying additive map is the structure map itself; `𝒪_X`-linearity is multiplicativity of the
structure map, the action of `𝒪_X` on the target being restriction of scalars along it.  This is
`AlgebraicGeometry.Space.structureProjection` for an arbitrary morphism in place of the inclusion
of a closed subspace. -/
def pushforwardStructureProjection (i : Z ⟶ X) :
    SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ structureSheafPushforward B S hS i where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat AddCommGrpCat).map ((structureSharp B S hS i).hom.app U)) (fun r ↦ by
      ext m
      exact (((structureSharp B S hS i).hom.app U).hom.map_mul r m).symm)
  val.naturality g := by
    ext
    exact ConcreteCategory.congr_hom ((structureSharp B S hS i).hom.naturality g) _

/-- The canonical map `𝒪_X ⟶ i_*𝒪_Z` acts on sections as the structure map of `i`. -/
@[simp]
theorem pushforwardStructureProjection_val_app_apply (i : Z ⟶ X)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (structureRingSheaf B S hS X).obj.obj U) :
    (pushforwardStructureProjection B S hS i).val.app U a =
      (structureSharp B S hS i).hom.app U a :=
  rfl

/-- The canonical map `𝒪_X ⟶ i_*𝒪_Z` on sections, as a function, is the structure map of `i`. -/
theorem pushforwardStructureProjection_val_app_hom_eq (i : Z ⟶ X)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    ⇑(ConcreteCategory.hom ((pushforwardStructureProjection B S hS i).val.app U)) =
      ⇑(ConcreteCategory.hom ((structureSharp B S hS i).hom.app U)) :=
  rfl

/-- **The kernel of the canonical map `𝒪_X ⟶ i_*𝒪_Z` is the kernel ideal sheaf of `i`.**

The sections of the kernel ideal sheaf over an object of the small étale site are the
ring-homomorphism kernel of the structure map there, which is by the previous lemma the kernel of
the projection on sections.  So the two submodule subsheaves have the same sections, and no
comparison map between them is needed. -/
theorem ker_pushforwardStructureProjection (i : Z ⟶ X) :
    SheafOfModules.Submodule.ker (pushforwardStructureProjection B S hS i) =
      kernelIdealSheaf B S hS i := by
  apply SheafOfModules.Submodule.ext
  rfl

/-- **The canonical map `𝒪_X ⟶ i_*𝒪_Z` of a closed immersion is an epimorphism**, because the
structure map of a closed immersion of algebraic spaces is locally surjective on the small étale
site of the target.  That surjectivity is the corresponding clause of Stacks 03MB,
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`, and the projection has the
structure map as its map on sections, so the two have the same image sieves. -/
theorem epi_pushforwardStructureProjection (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    Epi (pushforwardStructureProjection B S hS i) := by
  have h : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharp B S hS i).hom :=
    isLocallySurjective_structureSharp B S hS i hi
  rw [Presheaf.isLocallySurjective_iff_whisker_forget] at h
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    ⟨fun {_} s ↦ h.imageSieve_mem s⟩

/-- **The sections of `𝓘` over an étale chart are exactly the kernel of the canonical map
`𝒪_X ⟶ i_*𝒪_Z` there.**  Over every object of the small étale site the pair
`𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z` is exact on sections, with no hypothesis and no covering: the projection acts
as the structure map `i♯`, and the sections of the kernel ideal sheaf are by definition the kernel
of `i♯` on that chart. -/
theorem exact_val_app_pushforwardStructureProjection (i : Z ⟶ X)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Exact ((kernelIdealSheaf B S hS i).ι.val.app U)
      ((pushforwardStructureProjection B S hS i).val.app U) := by
  intro y
  refine ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, ?_⟩
  rintro ⟨x, rfl⟩
  exact x.2

/-- **The canonical map `𝒪_X ⟶ i_*𝒪_Z` of a closed immersion is surjective on the sections over
an affine étale chart.**  This is the sections form, over the affine charts, of the surjectivity
clause of Stacks 03MB. -/
theorem surjective_pushforwardStructureProjection_val_app_of_isAffine (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)) :
    Function.Surjective ((pushforwardStructureProjection B S hS i).val.app (op U)) := by
  rw [pushforwardStructureProjection_val_app_hom_eq]
  exact surjective_structureSharp_app_of_isAffine B S hS i hi U hU

/-- **`i_*𝒪_Z` is cartesian on affine charts** for a closed immersion `i`.

The kernel ideal sheaf `𝓘 = ker(i♯)` is cartesian on affine charts because a closed immersion is
quasi-compact, and the structure sheaf is cartesian on affine charts unconditionally.  The two
sections-level hypotheses of `AlgebraicGeometry.Space.isCartesianOnAffineCharts_cokernel` — which
for a general cokernel package the vanishing of Stacks 03DW — are *discharged* here: the
projection `𝒪_X ⟶ i_*𝒪_Z` is surjective over an affine chart by the affine case of the
surjectivity clause of Stacks 03MB, and the pair `𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z` is exact on sections over
*every* chart, by `exact_val_app_pushforwardStructureProjection`. -/
theorem isCartesianOnAffineCharts_structureSheafPushforward (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    IsCartesianOnAffineCharts (structureSheafPushforward B S hS i) :=
  isCartesianOnAffineCharts_cokernel (kernelIdealSheaf B S hS i).ι
    (pushforwardStructureProjection B S hS i)
    (fun U hU => surjective_pushforwardStructureProjection_val_app_of_isAffine B S hS i hi U hU)
    (fun U _ => exact_val_app_pushforwardStructureProjection B S hS i (op U))
    (isCartesianOnAffineCharts_kernelIdealSheaf B S hS i
      (isQuasiCompact_of_isClosedImmersion' B S hS hi))
    isCartesianOnAffineCharts_unit

/-- **Quasi-coherence of the direct image of the structure sheaf along a closed immersion.**  For
a closed immersion `i : Z ⟶ X` of algebraic spaces the `𝒪_X`-module `i_*𝒪_Z` is quasi-coherent.
This is the closed-immersion case of Stacks 03M9 for the structure sheaf, with no hypothesis
beyond the closed immersion. -/
theorem isQuasicoherentOnSite_structureSheafPushforward (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (structureSheafPushforward B S hS i).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_structureSheafPushforward B S hS i hi)

/-- **The direct image of the structure sheaf along a closed immersion is coherent on a locally
Noetherian algebraic space.**

`i_*𝒪_Z` is a quotient of `𝒪_X`, the quotient map being
`AlgebraicGeometry.Space.pushforwardStructureProjection`, which is an epimorphism by the
surjectivity clause of Stacks 03MB; it is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_structureSheafPushforward`; and `𝒪_X` is coherent
by Stacks 07UB.  So the quotient clause of Stacks 07UD,
`AlgebraicGeometry.Space.isCoherent_of_epi_of_isQuasicoherentOnSite`, applies.

This is the case of the structure sheaf along a closed immersion of the coherence assertion of
Stacks 07UH, and unlike the general case it needs no chart case of Stacks 03DW: see the module
documentation. -/
theorem isCoherent_structureSheafPushforward
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) :
    IsCoherent B S hS X.1 X.2 (structureSheafPushforward B S hS i) := by
  have hfact : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hX⟩
  have hepi : Epi (pushforwardStructureProjection B S hS i) :=
    epi_pushforwardStructureProjection B S hS i hi
  exact @isCoherent_of_epi_of_isQuasicoherentOnSite B S hS X.1 X.2 hfact _ _
    (pushforwardStructureProjection B S hS i) hepi
    (isQuasicoherentOnSite_structureSheafPushforward B S hS i hi)
    (isCoherent_structureSheaf B S hS X.1 X.2)

end AlgebraicGeometry.Space

end
