module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.DeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionAnnihilatedModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionGeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections

/-!
# The cycle of a closed subspace is the cycle of its pushed-forward structure sheaf

In Situation 0EDT let `X/B` be good and let `Y ⊂ X` be a closed subspace with inclusion
`i : Y → X`. Stacks 0EED says that if `dim_δ(Y) ≤ k` then `[Y]_k = [i_*𝒪_Y]_k`. Coefficientwise
this is the assertion that, for an integral closed subspace `Z ⊂ X` of δ-dimension `k` with
generic point `ξ`, the multiplicity of `Z` in `Y` — the length of `𝒪_Y` at `ξ` viewed in `Y` —
agrees with the length of `i_*𝒪_Y` at `ξ`, which is the coefficient of `Z` in `[i_*𝒪_Y]_k` by
Stacks 0EEC. That is exactly Stacks 0EE3, and the remaining bookkeeping is the bijection, from
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward`, between the integral closed
subspaces of `Y` and those of `X` supported inside `|Y|`.

Length on an algebraic space is `AlgebraicGeometry.Space.geometricLength`, the length at a
*geometric* point: the independence of the choice of geometric point above a point of `|X|` is
Stacks 0EE1, proved in this library, for a quasi-coherent `F`, as
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`
(`StacksFrontier/AlgebraicGeometry/Spaces/GeometricLengthPointIndependence.lean`). The cycle
coefficients below still carry a chosen geometric representative over each point, as an explicit
argument `γ`, in the same spirit as the library's forms of Stacks 0EE2 and 0EE3, but the two main
theorems of this file ask only that each `γ` lie over the point it is assigned to — not that the
two choices agree *as geometric points* along the inclusion — and restore the comparison through
Stacks 0EE1 instead.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.ambientGenericPoint`: the generic point of an
  integral closed subspace, as a point of the ambient space.
* `AlgebraicGeometry.Space.closedSubspacePushforwardStructureSheaf`: the direct image `i_*𝒪_Y`
  of the structure sheaf of a closed subspace.
* `AlgebraicGeometry.Space.cycleCoeffOfModule`: the coefficient of an integral closed subspace
  in `[F]_k`, the `k`-cycle of an `𝒪_X`-module, computed at a chosen geometric point.
* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`: the coefficient of an integral closed
  subspace in `[Y]_k`, the `k`-cycle of a closed subspace, computed at a chosen geometric point.

## Main results

* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule`: **Stacks 0EED**
  at an integral closed subspace contained in `Y`.
* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule_of_eq_zero`:
  **Stacks 0EED** as the equality of the two coefficient families.
* `AlgebraicGeometry.Space.exists_compatible_geometricRepresentative`: a choice of geometric
  representatives lying over every point of `|Y|` and of `|X|` exists, so the hypotheses `hγY`
  and `hγX` of the two results above are satisfiable.
* `AlgebraicGeometry.Space.geometricLength_closedSubspacePushforwardStructureSheaf`:
  Stacks 0EE3 for the structure sheaf of a closed subspace, the mathematical content of the
  coefficient equality.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_closedSubspacePushforwardStructureSheaf` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_closedSubspacePushforwardStructureSheaf`:
  `i_*𝒪_Y` is annihilated by the ideal cutting out `Y` and is quasi-coherent; together these
  give the vanishing of its length off `|Y|` that discharges the support bound of Lemma 07U0.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.ambientGenericPoint_pushforward`: the generic
  point of the image of an integral closed subspace is the image of its generic point.

## Implementation notes

**What is covered and what is not.** The coefficient of `Z` in `[Y]_k` is formed here as a
supremum over the integral closed subspaces `W ⊂ Y` whose image is `Z`; since
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward` is injective there is at most one
such `W`, so the supremum is its multiplicity when `Z ⊂ Y` and — `sSup ∅ = 0` in `ℕ∞` — is zero
otherwise, which is the convention of Stacks 0EE9: only the components of `Y` contribute. The
coefficient of `Z` in `[i_*𝒪_Y]_k` is the length of `i_*𝒪_Y` at the generic point of `Z`, the
formula of Stacks 0EEC. The two agree at every `Z` contained in `|Y|`, which is
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule`. For `Z` *not*
contained in `|Y|` the source argues that `ξ ∉ Supp(i_*𝒪_Y)` by the minimality of
scheme-theoretic support, Lemma 07U0; here that vanishing is proved directly from annihilation
of `i_*𝒪_Y` by the ideal cutting out `Y`
(`AlgebraicGeometry.Space.annihilatedByKerIdeal_closedSubspacePushforwardStructureSheaf`)
and `AlgebraicGeometry.Space.subsingleton_geometricModuleStalk_of_annihilatedByKerIdeal_of_notMem`:
a module annihilated by that ideal has a trivial stalk at a geometric point outside the image of
`|Y|`, and `ξ` lies outside that image exactly when no `W ⊂ Y` has image `Z`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq`, using that `Y` is a
decent space, `AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable`).

**The δ-dimension side.** `AlgebraicGeometry.Space.deltaDimension_closedSubspaceComponentImage`
records that the image of an integral closed subspace of `Y` has the same δ-dimension, so the
two coefficient families single out corresponding sets of subspaces; both definitions below test
the δ-dimension of `Z` in `X`, so the statements need nothing further. The bound `dim_δ(Y) ≤ k`,
which is the standing hypothesis under which the source writes `[Y]_k` at all, is carried by the
two tagged statements. It is what makes the supremum below the sum of Stacks 0EE9: under it, an
integral closed subspace of `Y` of δ-dimension `k` is an irreducible component of `Y`, because
its generic point attains the bound and Stacks 0EE6 — proved as
`AlgebraicGeometry.Space.isGenericPoint_of_deltaDimensionClosed_le` — makes a point attaining
the bound the generic point of a component. The definitions themselves do not require the
bound, so they are defined, and agree, more generally.

**Choices of geometric points.** `AlgebraicGeometry.Space.cycleCoeffOfModule` and
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` take a function `γ` assigning a geometric
point to each point of the space; the hypotheses `hγY` and `hγX` of the two theorems below ask
only that each chosen point lies over the point it is assigned to, not that the two choices
agree with one another along `i` as geometric points. Such choices exist by
`AlgebraicGeometry.Space.exists_compatible_geometricRepresentative`. Since `γX` composed with the
inclusion on points and `geometricPointMap i` composed with `γY` both lie over the same point of
`|X|`, Stacks 0EE1 (`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`) identifies the two
lengths they compute, which is enough to run the comparison without pinning `γX` and `γY` down
any more tightly than that.

**Coefficients.** `ℕ∞`-valued lengths are coerced to `ℤ` through `ENat.toNat`, so `∞` becomes
`0`. Finiteness of the length at a generic point of the support is Stacks 0EE4
(`AlgebraicGeometry.Space.tfae_isGenericPoint_supportOfSheaf_of_isDecentSpace`), which is not
used here; the coercion is applied to equal `ℕ∞` values on the two sides, so it does not weaken
any statement here, and
`AlgebraicGeometry.Space.geometricLength_closedSubspacePushforwardStructureSheaf` records the
equality before the coercion.

## References

* [Stacks Project, Tag 0EED](https://stacks.math.columbia.edu/tag/0EED)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE3](https://stacks.math.columbia.edu/tag/0EE3)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EEB](https://stacks.math.columbia.edu/tag/0EEB)
* [Stacks Project, Tag 0EEC](https://stacks.math.columbia.edu/tag/0EEC)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The generic point of an integral closed subspace, as a point of the ambient space -/

section AmbientGenericPoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The generic point of an integral closed subspace `Z ⊂ X`, as a point of `|X|`: the image
under the inclusion of the generic point of `Z` itself. -/
def IntegralClosedSubspace.ambientGenericPoint (Z : IntegralClosedSubspace B S hS X) :
    points B S hS X :=
  pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS)

/-- The ambient generic point of an integral closed subspace is a generic point of its set of
points. -/
theorem IntegralClosedSubspace.isGenericPoint_ambientGenericPoint
    (hX : IsAlgebraicSpace B S hS X) (Z : IntegralClosedSubspace B S hS X) :
    IsGenericPoint (Z.ambientGenericPoint B S hS) (subspacePointSet B S hS X Z.subspace) :=
  isGenericPoint_pointsMap_genericPoint B S hS hX Z

/-- The ambient generic point of the image of an integral closed subspace along a closed
immersion is the image of its ambient generic point: the inclusion is a closed embedding on
points, so it carries the generic point to a generic point of the image, and generic points are
unique. -/
theorem IntegralClosedSubspace.ambientGenericPoint_pushforward
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i)
    (W : IntegralClosedSubspace B S hS Y) :
    (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi W).ambientGenericPoint B S hS =
      pointsMap B S hS Y i (W.ambientGenericPoint B S hS) := by
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hi
  have hgen := W.isGenericPoint_ambientGenericPoint B S hS hY
  have hstep : closure ({pointsMap B S hS Y i (W.ambientGenericPoint B S hS)} :
        Set (points B S hS X)) =
      pointsMap B S hS Y i '' subspacePointSet B S hS Y W.subspace := by
    rw [← hgen, ← hemb.closure_image_eq, Set.image_singleton]
  have hgenX : IsGenericPoint (pointsMap B S hS Y i (W.ambientGenericPoint B S hS))
      (subspacePointSet B S hS X
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi W).subspace) :=
    hstep.trans
      (IntegralClosedSubspace.subspacePointSet_pushforward B S hS hX hY hXdec hi W).symm
  exact (eq_pointsMap_genericPoint_of_isGenericPoint B S hS hX _ _ hgenX).symm

end AmbientGenericPoint

/-! ### The direct image of the structure sheaf of a closed subspace -/

section PushforwardStructureSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The inclusion of a closed subspace, as a morphism of algebraic spaces over `S`. -/
def closedSubspaceHom (hX : IsAlgebraicSpace B S hS X) (Y : Subfunctor X)
    (hY : IsClosedSubspace B S hS Y) :
    (⟨Y.toFunctor, hY.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩ :=
  ObjectProperty.homMk Y.ι

/-- The inclusion of a closed subspace is a closed immersion of algebraic spaces. -/
theorem isClosedImmersion_closedSubspaceHom (hX : IsAlgebraicSpace B S hS X) (Y : Subfunctor X)
    (hY : IsClosedSubspace B S hS Y) :
    IsClosedImmersion B S hS (closedSubspaceHom B S hS hX Y hY).hom :=
  hY.2

/-- The direct image `i_*𝒪_Y` of the structure sheaf of a closed subspace `i : Y → X`, as an
`𝒪_X`-module.

The direct image is `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, the one for which
Stacks 0EE3 is available. -/
def closedSubspacePushforwardStructureSheaf (hX : IsAlgebraicSpace B S hS X) (Y : Subfunctor X)
    (hY : IsClosedSubspace B S hS Y) : Modules.{u, u} B S hS X hX :=
  (smallBaseChangeModulePushforward B S hS (closedSubspaceHom B S hS hX Y hY)
    (isClosedImmersion_closedSubspaceHom B S hS hX Y hY).rep).obj (SheafOfModules.unit _)

/-- **Stacks 0EE3 for the structure sheaf of a closed subspace.** For a closed subspace
`i : Y → X` and a geometric point `ȳ` of `Y`, the module `i_*𝒪_Y` has the same length at `i(ȳ)`
as `𝒪_Y` has at `ȳ`. -/
theorem geometricLength_closedSubspacePushforwardStructureSheaf
    (hX : IsAlgebraicSpace B S hS X) (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y)
    (ybar : GeometricPoint B S hS Y.toFunctor) :
    geometricLength B S hS ⟨X, hX⟩ (geometricPointMap Y.ι ybar)
        (closedSubspacePushforwardStructureSheaf B S hS hX Y hY) =
      geometricLength B S hS ⟨Y.toFunctor, hY.1⟩ ybar (SheafOfModules.unit _) :=
  geometricLength_chartDirectImage B S hS (closedSubspaceHom B S hS hX Y hY)
    (isClosedImmersion_closedSubspaceHom B S hS hX Y hY) ybar (SheafOfModules.unit _)

/-- **Half of the support bound of Lemma 07U0.** The direct image `i_*𝒪_Y` of the structure
sheaf of a closed subspace `i : Y → X` is annihilated by the ideal cutting out `Y`: it lies in
the essential image of the direct image along `i`, by the comparison with base change of étale
scheme charts. -/
theorem annihilatedByKerIdeal_closedSubspacePushforwardStructureSheaf
    (hX : IsAlgebraicSpace B S hS X) (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y) :
    AnnihilatedByKerIdeal B S hS (closedSubspaceHom B S hS hX Y hY)
      (closedSubspacePushforwardStructureSheaf B S hS hX Y hY) :=
  annihilatedByKerIdeal_of_essImage_modulePushforward B S hS (closedSubspaceHom B S hS hX Y hY)
    ⟨SheafOfModules.unit _,
      ⟨modulePushforwardIsoChartDirectImage B S hS (closedSubspaceHom B S hS hX Y hY)
        (isClosedImmersion_closedSubspaceHom B S hS hX Y hY) (SheafOfModules.unit _)⟩⟩

/-- The direct image `i_*𝒪_Y` of the structure sheaf of a closed subspace is quasi-coherent:
transport quasi-coherence of the direct image of the structure sheaf through the conormal
algebra along the isomorphism with base change of étale scheme charts. -/
theorem isQuasicoherentOnSite_closedSubspacePushforwardStructureSheaf
    (hX : IsAlgebraicSpace B S hS X) (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y) :
    (closedSubspacePushforwardStructureSheaf B S hS hX Y hY).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (modulePushforwardIsoChartDirectImage B S hS (closedSubspaceHom B S hS hX Y hY)
      (isClosedImmersion_closedSubspaceHom B S hS hX Y hY) (SheafOfModules.unit _))
    (isQuasicoherentOnSite_pushforwardStructureSheaf B S hS ⟨X, hX⟩ ⟨Y, hY⟩)

end PushforwardStructureSheaf

/-! ### The two cycle coefficients -/

section CycleCoeff

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EEB and 0EEC, at a chosen geometric point.** The coefficient of an integral closed
subspace `Z` in the `k`-cycle `[F]_k` of an `𝒪_X`-module `F`: the length of `F` at the generic
point of `Z` if `Z` has δ-dimension `k`, and zero otherwise, the length being taken at the
geometric point that `γ` assigns to that generic point. -/
def cycleCoeffOfModule (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (k : ℤ)
    (γ : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  if deltaDimension D sX Z = k then
    ((geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩
      (γ (Z.ambientGenericPoint D.site D.base D.base_mem)) F).toNat : ℤ)
  else 0

/-- The integral closed subspace of `X` carried by an integral closed subspace of a closed
subspace `Y ⊂ X`. -/
abbrev closedSubspaceComponentImage (sX : X ⟶ D.space) (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    IntegralClosedSubspace D.site D.base D.base_mem X :=
  IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
    (D.isDecentSpace_of_isGood sX hX) hY.2 W

/-- An integral closed subspace of a closed subspace and its image in the ambient space have the
same δ-dimension, so the components of `Y` of δ-dimension `k` correspond to the integral closed
subspaces of `X` of δ-dimension `k` contained in `|Y|`. -/
theorem deltaDimension_closedSubspaceComponentImage (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    deltaDimension D sX (closedSubspaceComponentImage D sX hX Y hY W) =
      deltaDimension D (Y.ι ≫ sX) W :=
  IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1
    (D.isDecentSpace_of_isGood sX hX) hY.2 W

/-- **Stacks 0EE9, at a chosen geometric point.** The coefficient of an integral closed subspace
`Z` in the `k`-cycle `[Y]_k` of a closed subspace `Y ⊂ X`: the multiplicity of `Z` in `Y` — the
length of `𝒪_Y` at the generic point of `Z`, read inside `Y` — if `Z` has δ-dimension `k` and is
carried by an integral closed subspace of `Y`, and zero otherwise.

The supremum has at most one element to take, because
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward` is injective, and is empty exactly
when `|Z|` is not contained in `|Y|`; `sSup ∅ = 0`, which is the convention of Stacks 0EE9 that
only components of `Y` contribute. -/
def cycleCoeffOfClosedSubspace (sX : X ⟶ D.space) (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  if deltaDimension D sX Z = k then
    ((sSup {d : ℕ∞ | ∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      closedSubspaceComponentImage D sX hX Y hY W = Z ∧
        geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩
          (γ (W.ambientGenericPoint D.site D.base D.base_mem))
          (SheafOfModules.unit _) = d}).toNat : ℤ)
  else 0

/-- An integral closed subspace of `X` which is not carried by an integral closed subspace of `Y`
has coefficient zero in `[Y]_k`. -/
theorem cycleCoeffOfClosedSubspace_eq_zero (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      closedSubspaceComponentImage D sX hX Y hY W ≠ Z) :
    cycleCoeffOfClosedSubspace D sX hX Y hY k γ Z = 0 := by
  have hempty : {d : ℕ∞ | ∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      closedSubspaceComponentImage D sX hX Y hY W = Z ∧
        geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩
          (γ (W.ambientGenericPoint D.site D.base D.base_mem))
          (SheafOfModules.unit _) = d} = ∅ := by
    ext d
    refine ⟨?_, fun hd => hd.elim⟩
    rintro ⟨W, hW, -⟩
    exact absurd hW (hZ W)
  rw [cycleCoeffOfClosedSubspace, hempty]
  simp

/-- The coefficient of the image of an integral closed subspace `W ⊂ Y` in `[Y]_k` is the length
of `𝒪_Y` at the generic point of `W`, when the image has δ-dimension `k`. -/
theorem cycleCoeffOfClosedSubspace_closedSubspaceComponentImage (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    cycleCoeffOfClosedSubspace D sX hX Y hY k γ
        (closedSubspaceComponentImage D sX hX Y hY W) =
      if deltaDimension D sX (closedSubspaceComponentImage D sX hX Y hY W) = k then
        ((geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩
          (γ (W.ambientGenericPoint D.site D.base D.base_mem))
          (SheafOfModules.unit _)).toNat : ℤ)
      else 0 := by
  have hinj := IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 hY.1
    (D.isDecentSpace_of_isGood sX hX) hY.2
  have hsingle : {d : ℕ∞ | ∃ W' : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      closedSubspaceComponentImage D sX hX Y hY W' =
          closedSubspaceComponentImage D sX hX Y hY W ∧
        geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩
          (γ (W'.ambientGenericPoint D.site D.base D.base_mem))
          (SheafOfModules.unit _) = d} =
      {geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩
        (γ (W.ambientGenericPoint D.site D.base D.base_mem)) (SheafOfModules.unit _)} := by
    ext d
    refine ⟨?_, fun hd => ⟨W, rfl, hd.symm⟩⟩
    rintro ⟨W', hW', rfl⟩
    have hWW : W' = W := hinj hW'
    subst hWW
    rfl
  rw [cycleCoeffOfClosedSubspace, hsingle, csSup_singleton]

end CycleCoeff

/-! ### Stacks 0EED -/

section Main

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A choice of geometric point above each point of a closed subspace `Y ⊂ X` extends to one on
`X` compatibly with the inclusion: the map on points of a closed immersion is injective, so the
chosen representatives of `|Y|` may be transported to the image and the remaining points of `|X|`
given arbitrary representatives. -/
theorem exists_compatible_geometricRepresentative (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) :
    ∃ (γY : points D.site D.base D.base_mem Y.toFunctor →
        GeometricPoint D.site D.base D.base_mem Y.toFunctor)
      (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X),
      (∀ y, (γY y).LiesOver y) ∧ (∀ x, (γX x).LiesOver x) ∧
        ∀ y, γX (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι y) =
          geometricPointMap Y.ι (γY y) := by
  classical
  have hinj := (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX
    hY.2).injective
  choose γY hγY using exists_geometricRepresentative D.site D.base D.base_mem Y.toFunctor
  choose γ0 hγ0 using exists_geometricRepresentative D.site D.base D.base_mem X
  refine ⟨γY, Function.extend (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι)
    (fun y => geometricPointMap Y.ι (γY y)) γ0, hγY, ?_, ?_⟩
  · intro x
    by_cases h : ∃ y, pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι y = x
    · obtain ⟨y, rfl⟩ := h
      rw [hinj.extend_apply]
      show pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι (γY y).image = _
      rw [hγY y]
    · rw [Function.extend_apply' _ _ _ h]
      exact hγ0 x
  · exact fun y => hinj.extend_apply _ _ y

/-- **Stacks 0EED, at an integral closed subspace contained in `Y`.** In Situation 0EDT let
`X/B` be good, let `Y ⊂ X` be a closed subspace with inclusion `i : Y → X`, assume
`dim_δ(Y) ≤ k`, and let `W` be an integral closed subspace of `Y` with image `Z ⊂ X`. Then the
coefficient of `Z` in `[Y]_k` is the coefficient of `Z` in `[i_*𝒪_Y]_k`.

The chosen geometric representatives `γY` and `γX` are each assumed to lie over the point they
are assigned to, which `AlgebraicGeometry.Space.exists_compatible_geometricRepresentative` shows
is possible; the content is then Stacks 0EE3, by way of
`AlgebraicGeometry.Space.geometricLength_closedSubspacePushforwardStructureSheaf`, together with
Stacks 0EE1 to move from `γX` at the image of the generic point of `W` to the geometric point
`i(γY(ξ_W))` that the comparison with `𝒪_Y` is stated at. -/
@[stacks 0EED "the coefficient at an integral closed subspace contained in Y, for a choice of
  geometric representatives above the points they are assigned to, using Lemma 0EE1 to compare
  the two"]
theorem cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (_hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (γY : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγY : ∀ y, (γY y).LiesOver y) (hγX : ∀ x, (γX x).LiesOver x)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) :
    cycleCoeffOfClosedSubspace D sX hX Y hY k γY
        (closedSubspaceComponentImage D sX hX Y hY W) =
      cycleCoeffOfModule D sX hX
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Y hY) k γX
        (closedSubspaceComponentImage D sX hX Y hY W) := by
  have := isQuasicoherentOnSite_closedSubspacePushforwardStructureSheaf
    D.site D.base D.base_mem hX.1 Y hY
  have himg : (γX (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι
      (W.ambientGenericPoint D.site D.base D.base_mem))).image =
      (geometricPointMap Y.ι (γY (W.ambientGenericPoint D.site D.base D.base_mem))).image := by
    rw [geometricPointMap_image, hγX _, hγY _]
  rw [cycleCoeffOfClosedSubspace_closedSubspaceComponentImage, cycleCoeffOfModule,
    IntegralClosedSubspace.ambientGenericPoint_pushforward,
    geometricLength_eq_of_image_eq D.site D.base D.base_mem hX.1
      (γX (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι
        (W.ambientGenericPoint D.site D.base D.base_mem)))
      (geometricPointMap Y.ι (γY (W.ambientGenericPoint D.site D.base D.base_mem))) himg
      (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Y hY),
    geometricLength_closedSubspacePushforwardStructureSheaf]

/-- **Stacks 0EED.** In Situation 0EDT let `X/B` be good, let `Y ⊂ X` be a closed subspace with
inclusion `i : Y → X`, and assume `dim_δ(Y) ≤ k`. Then `[Y]_k = [i_*𝒪_Y]_k`, as an equality of
coefficient families on the integral closed subspaces of `X`.

For an integral closed subspace `Z` with image contained in `|Y|` this is
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule`. Otherwise both sides
vanish: the left by `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_eq_zero`, and the right
because `i_*𝒪_Y` is annihilated by the ideal cutting out `Y`
(`AlgebraicGeometry.Space.annihilatedByKerIdeal_closedSubspacePushforwardStructureSheaf`), so its
geometric stalk is trivial at any geometric point over a point of `|X|` outside the image of
`|Y|`
(`AlgebraicGeometry.Space.subsingleton_geometricModuleStalk_of_annihilatedByKerIdeal_of_notMem`);
and the generic point of `Z` is such a point exactly when no integral closed subspace of `Y` has
image `Z`, since `Y` is a decent space
(`AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable`) and every integral closed
subspace of `X` contained in the image of `|Y|` is itself such an image
(`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq`). This is the support
bound of Lemma 07U0, proved rather than taken as a hypothesis. -/
@[stacks 0EED "the equality of the two k-cycles, for a choice of geometric representatives above
  the points they are assigned to"]
theorem cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule_of_eq_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (γY : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγY : ∀ y, (γY y).LiesOver y) (hγX : ∀ x, (γX x).LiesOver x) :
    cycleCoeffOfClosedSubspace D sX hX Y hY k γY =
      cycleCoeffOfModule D sX hX
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Y hY) k γX := by
  funext Z
  by_cases h : ∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      closedSubspaceComponentImage D sX hX Y hY W = Z
  · obtain ⟨W, rfl⟩ := h
    exact cycleCoeffOfClosedSubspace_eq_cycleCoeffOfModule D sX hX Y hY k hdim γY γX hγY hγX W
  · have h' : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
        closedSubspaceComponentImage D sX hX Y hY W ≠ Z := fun W hW => h ⟨W, hW⟩
    have hYdec : IsDecentSpace D.site D.base D.base_mem Y.toFunctor :=
      isDecentSpace_of_relativelyRepresentable D.site D.base D.base_mem hY.1 Y.ι hY.2.rep
        (D.isDecentSpace_of_isGood sX hX)
    have hnotmem : Z.ambientGenericPoint D.site D.base D.base_mem ∉
        Set.range (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι) := by
      intro hmem
      have hsub : subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
          Set.range (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι) := by
        rw [← Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1]
        exact closure_minimal (Set.singleton_subset_iff.2 hmem)
          (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX.1
            hY.2).isClosed_range
      obtain ⟨W, hW⟩ := IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem
        hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hYdec hY.2 Z hsub
      exact h' W hW
    have hzero : geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩
        (γX (Z.ambientGenericPoint D.site D.base D.base_mem))
        (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Y hY) = 0 := by
      have himgZ : (γX (Z.ambientGenericPoint D.site D.base D.base_mem)).image =
          Z.ambientGenericPoint D.site D.base D.base_mem := hγX _
      have hsub2 : Subsingleton (geometricModuleStalk D.site D.base D.base_mem ⟨X, hX.1⟩
          (γX (Z.ambientGenericPoint D.site D.base D.base_mem))
          (closedSubspacePushforwardStructureSheaf D.site D.base D.base_mem hX.1 Y hY)) := by
        refine subsingleton_geometricModuleStalk_of_annihilatedByKerIdeal_of_notMem
          D.site D.base D.base_mem (closedSubspaceHom D.site D.base D.base_mem hX.1 Y hY)
          (isClosedImmersion_closedSubspaceHom D.site D.base D.base_mem hX.1 Y hY) _
          (annihilatedByKerIdeal_closedSubspacePushforwardStructureSheaf D.site D.base
            D.base_mem hX.1 Y hY) _ ?_
        rw [himgZ]
        exact hnotmem
      rw [geometricLength, Module.length_eq_zero_iff]
      exact hsub2
    rw [cycleCoeffOfClosedSubspace_eq_zero D sX hX Y hY k γY Z h', cycleCoeffOfModule, hzero]
    simp

end Main

end AlgebraicGeometry.Space

end
