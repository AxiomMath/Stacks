module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Purity over a proper morphism of algebraic spaces

In the standing situation of Stacks 0CV6 — a finite type decent morphism `f : X ⟶ Y` of
algebraic spaces over a base scheme `S`, a finite type quasi-coherent `𝒪_X`-module `ℱ` and a
point `y` of `Y` — Stacks 0CVI says that `ℱ` is universally pure above `y` as soon as the
support of `ℱ` is proper over `Y`, that it is so in particular when `f` itself is proper, and
that `X` is then universally pure over `Y` as well.

The content is the case of a proper `f`, and it is short. Let `(g : T ⟶ Y, t' ⤳ t, ξ)` be an
impurity diagram. A proper morphism is universally closed, so the projection `f_T : X_T ⟶ T`
is a closed map on points; hence the image under `f_T` of the closure of `{ξ}` is a closed
subset of `|T|`. That image contains `f_T(ξ) = t'`, so it contains the closure of `{t'}`, and
the specialization `t' ⤳ t` puts `t` in that closure. So `t` does lie in the image, and the
diagram is not an impurity.

The case of a module whose support is proper over `Y` reduces to that one: if `i : Z ⟶ X` is a
closed immersion with `ℱ = i_*𝒢` — for instance the scheme-theoretic support of Stacks 07U1,
by Stacks 07U0 — then `𝒢` is universally pure above `y` by the proper case applied to the
situation on `Z`, and Stacks 0CVH transfers that to `ℱ`.

## Main definitions

* `AlgebraicGeometry.Space.PrePureSituation.sourceSpace`: the source of a situation, as an
  object of the category of algebraic spaces.
* `AlgebraicGeometry.Space.ClosedSubspaceModule.ofSchemeTheoreticSupport`: the
  closed-immersion presentation of the module of a situation furnished by its
  scheme-theoretic support, Stacks 07U1, together with the module of Stacks 07U0 living on
  it.
* `AlgebraicGeometry.Space.structurePrePureSituation`: the situation whose module is the
  structure sheaf `𝒪_X`, which is the one that expresses purity of the algebraic space `X`
  itself.
* `AlgebraicGeometry.Space.IsSpacePureAbove` and
  `AlgebraicGeometry.Space.IsSpacePureRelative`: parts (3) and (6) of Stacks 0CVD, the purity
  of the algebraic space `X` above a point of `Y` and relative to `Y`.

## Main results

* `AlgebraicGeometry.Space.ImpurityDiagram.not_isImpurity_of_universallyClosed`: a
  universally closed morphism admits no impurity diagram at all.
* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isProper`: **Stacks 0CVI, part (2).**
* `AlgebraicGeometry.Space.ClosedSubspaceModule.isUniversallyPureAbove_of_isProper`:
  **Stacks 0CVI, part (1)** in its general form, taking the closed-immersion presentation of
  the module as data.
* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isProper_schemeTheoreticSupport`:
  **Stacks 0CVI, part (1)** in the source's form, at the scheme-theoretic support.
* `AlgebraicGeometry.Space.isSpacePureRelative_iff`: purity of `X` relative to `Y` is purity
  of `X` above every point of `Y`.
* `AlgebraicGeometry.Space.isUniversallyPureAbove_structure_of_isProper`:
  **Stacks 0CVI, part (3).**

## Implementation notes

"Universally pure relative to `Y`" is the form of "universally pure above `y`" quantified over
the points `y` of the target, part (4) of Stacks 0CVD. A situation carries the point `y` as a
field, so the statements below — which hold for an arbitrary situation, hence for an arbitrary
point of the target — are the relative statements.

Parts (3) and (6) of Stacks 0CVD, which read purity of the algebraic space `X` as purity of
its structure sheaf, are stated here rather than with parts (1), (2), (4) and (5) in
`StacksFrontier.AlgebraicGeometry.Spaces.Flat.RelativelyPureModules`: they need the situation
whose module is `𝒪_X`, and so the quasi-coherence and the finite type of `𝒪_X`, which live in
files importing that one.

Properness is `AlgebraicGeometry.Space.IsProper` of Stacks 03ZM and only its universally
closed conjunct is used; the closedness of `f_T` is the instance of that conjunct at the
structure morphism `g : T ⟶ Y` of the impurity diagram, whose source `T` is a scheme of the
site and so an algebraic space. The specialization of an impurity diagram is recorded in the
scheme representing `T`, so the closure argument is transported along the comparison
bijection `AlgebraicGeometry.Space.pointsToScheme` of Stacks 03BX, using
`AlgebraicGeometry.Space.isClosed_pointTopology_yoneda_iff_isClosed_image` in one direction
and injectivity of that bijection in the other.

The general form of part (1) uses Stacks 0CVH in the form
`AlgebraicGeometry.Space.ClosedSubspaceModule.isUniversallyPureAbove_situation_iff`, whose
input, affine base change on the base changes of the situation, is
`AlgebraicGeometry.Space.ClosedSubspaceModule.baseChangeInput`. The form at the
scheme-theoretic support takes the module on the support from
`AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion`, which holds
for every closed immersion, and its two further arguments `hZ` and `hid` are the closed-subspace
data of the support, produced by
`AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport`, and are taken as
arguments because the properness hypothesis is stated in terms of the closed subspace they
exhibit.

Part (3) needs no hypothesis beyond properness and decency: the structure sheaf is the unit
object `SheafOfModules.unit` of the category of modules on the small étale ringed site, which
is quasi-coherent by `SheafOfModules.isQuasicoherentOnSite_unit` and of finite type by
`PresheafOfModules.isFiniteType_unit` together with
`Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType`.

## References

* [Stacks Project, Tag 0CVI](https://stacks.math.columbia.edu/tag/0CVI)
* [Stacks Project, Tag 0CV6](https://stacks.math.columbia.edu/tag/0CV6)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 0CVH](https://stacks.math.columbia.edu/tag/0CVH)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07U1](https://stacks.math.columbia.edu/tag/07U1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The source of a pre-pure situation, as an object of the category of algebraic spaces. -/
abbrev PrePureSituation.sourceSpace (P : PrePureSituation.{u, m} B S hS) :
    AlgebraicSpaces B S hS :=
  ⟨P.X, P.hX⟩

section Proper

attribute [local instance] pointTopology

/-! ### No impurity above a universally closed morphism -/

/-- **A universally closed morphism admits no impurity diagram.** The projection
`f_T : X_T ⟶ T` is a closed map on points, so the image under it of the closure of the
distinguished point `ξ` is closed; that image contains `f_T(ξ) = t'`, hence the closure of
`{t'}`, hence the specialization `t` of `t'`. So the second condition defining an impurity
fails.

The closure of `{t'}` is taken in the scheme representing `T`, where the specialization of the
diagram lives, and transported along the comparison bijection of Stacks 03BX. -/
theorem ImpurityDiagram.not_isImpurity_of_universallyClosed
    {P : PrePureSituation.{u, u} B S hS} (D : ImpurityDiagram P)
    (huc : UniversallyClosed B S hS P.f) : ¬ D.IsImpurity := by
  rintro ⟨-, hnot⟩
  refine hnot ?_
  -- The image under `f_T` of the closure of `{ξ}` is closed, `f_T` being a closed map.
  have hclosed : IsClosed (pointsMap B S hS D.baseChange D.toT '' closure {D.xi}) :=
    huc (yoneda.obj D.T) (isAlgebraicSpace_yoneda B S hS D.T) D.g _ isClosed_closure
  -- Read that in the scheme representing `T`, where the specialization lives.
  have himg : IsClosed (pointsToScheme B S hS D.T ''
      (pointsMap B S hS D.baseChange D.toT '' closure {D.xi})) :=
    (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS D.T _).1 hclosed
  have hmem : pointsToScheme B S hS D.T D.t' ∈ pointsToScheme B S hS D.T ''
      (pointsMap B S hS D.baseChange D.toT '' closure {D.xi}) :=
    ⟨D.t', ⟨D.xi, subset_closure (Set.mem_singleton _), D.pointsMap_toT_xi⟩, rfl⟩
  obtain ⟨w, hw, hweq⟩ := himg.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
    (specializes_iff_mem_closure.1 D.specializes)
  exact injective_pointsToScheme B S hS D.T hweq ▸ hw

/-! ### Stacks 0CVI, part (2) -/

/-- **Stacks 0CVI, part (2).** In the situation of Stacks 0CV6, if `f : X ⟶ Y` is proper then
the module `ℱ` is universally pure above `y`.

A proper morphism is universally closed, and a universally closed morphism admits no impurity
diagram. Since the point `y` of the situation is arbitrary, this is purity of `ℱ` relative
to `Y`. -/
@[stacks 0CVI "part (2): a finite type quasi-coherent module on the source of a proper \
morphism is universally pure above every point of the target"]
theorem isUniversallyPureAbove_of_isProper (P : PrePureSituation.{u, u} B S hS)
    (hf : IsProper B S hS P.f) : IsUniversallyPureAbove P :=
  fun D => D.not_isImpurity_of_universallyClosed (IsProper.universallyClosed B S hS hf)

/-! ### Stacks 0CVI, part (1) -/

/-- **Stacks 0CVI, part (1), in general form.** In the situation of Stacks 0CV6, let
`i : Z ⟶ X` be a closed immersion and suppose `ℱ = i_*𝒢` for a finite type quasi-coherent
`𝒪_Z`-module `𝒢`. If the composite `Z ⟶ Y` is proper, then `ℱ` is universally pure above `y`.

This is part (2) applied to the situation on `Z`, transferred to `ℱ` by Stacks 0CVH. The
source states the hypothesis as properness of the support of `ℱ` over `Y` and then reduces to
part (2) exactly this way, at the scheme-theoretic support; see
`AlgebraicGeometry.Space.isUniversallyPureAbove_of_isProper_schemeTheoreticSupport`.

The input of Stacks 0CVH, affine base change on the base changes of the situation, is
`AlgebraicGeometry.Space.ClosedSubspaceModule.baseChangeInput`. -/
@[stacks 0CVI "part (1) in general form, taking the closed-immersion presentation of the \
module as data"]
theorem ClosedSubspaceModule.isUniversallyPureAbove_of_isProper
    {P : PrePureSituation.{u, u} B S hS} (c : ClosedSubspaceModule P)
    (hZY : IsProper B S hS (c.i.hom ≫ P.f)) :
    IsUniversallyPureAbove P :=
  (c.isUniversallyPureAbove_situation_iff c.baseChangeInput).1
    (_root_.AlgebraicGeometry.Space.isUniversallyPureAbove_of_isProper c.situation hZY)

/-- **The closed-immersion presentation of the module of a situation at its scheme-theoretic
support.** The closed subspace is the scheme-theoretic support of Stacks 07U1 and the module
on it is the one of Stacks 07U0; its finite type is part (3) of Stacks 07U0. -/
noncomputable def ClosedSubspaceModule.ofSchemeTheoreticSupport
    {P : PrePureSituation.{u, u} B S hS}
    (hZ : IsClosedSubspace B S hS
      (schemeTheoreticSupport B S hS P.sourceSpace P.F))
    (G : Modules.{u, u} B S hS
      (closedSubspaceToSpace B S hS P.sourceSpace
        ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩).1
      (closedSubspaceToSpace B S hS P.sourceSpace
        ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩).2)
    (hG : G.IsQuasicoherentOnSite)
    (e : (modulePushforward B S hS (closedSubspaceInclusion B S hS P.sourceSpace
      ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩)).obj G ≅ P.F) :
    ClosedSubspaceModule P where
  Z := closedSubspaceToSpace B S hS P.sourceSpace
    ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩
  i := closedSubspaceInclusion B S hS P.sourceSpace
    ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩
  isClosedImmersion := hZ.2
  G := G
  moduleFiniteType := isFiniteTypeOnSite_module_on_closedSubspace B S hS P.sourceSpace P.F
    P.moduleFiniteType _ G e
  moduleQuasicoherent := hG
  iso := e.symm

/-- **Stacks 0CVI, part (1).** In the situation of Stacks 0CV6, if the scheme-theoretic
support of `ℱ` is proper over `Y`, then `ℱ` is universally pure above `y`.

This is the general form above at the closed-immersion presentation of `ℱ` furnished by its
scheme-theoretic support, Stacks 07U1, and the module on it of Stacks 07U0.

The two arguments `hZ` and `hid` are not assumptions about the geometry but the closed-subspace
data of the scheme-theoretic support, which
`AlgebraicGeometry.Space.exists_isClosedSubspace_schemeTheoreticSupport` produces from
quasi-coherence of the module together with its finite type in the sectionwise sense of
Stacks 03DL(5); they are taken as arguments because every other hypothesis here, the
properness assumption included, is stated about the closed subspace they exhibit. -/
@[stacks 0CVI "part (1) at the scheme-theoretic support, naming the support's closed-subspace \
data"]
theorem isUniversallyPureAbove_of_isProper_schemeTheoreticSupport
    (P : PrePureSituation.{u, u} B S hS)
    (hZ : IsClosedSubspace B S hS (schemeTheoreticSupport B S hS P.sourceSpace P.F))
    (hid : definingIdealSheaf B S hS P.sourceSpace
        ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩ =
      annihilatorIdealSheaf B S hS P.sourceSpace P.F)
    (hZY : IsProper B S hS ((closedSubspaceInclusion B S hS P.sourceSpace
      ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩).hom ≫ P.f)) :
    IsUniversallyPureAbove P := by
  obtain ⟨G, hG, ⟨e⟩⟩ := isQuasicoherentEssImagePushforward_of_isClosedImmersion B S hS
    P.sourceSpace
    (closedSubspaceInclusion B S hS P.sourceSpace
      ⟨schemeTheoreticSupport B S hS P.sourceSpace P.F, hZ⟩) hZ.2 P.F P.moduleQuasicoherent
    (annihilatedByKerIdeal_schemeTheoreticSupport B S hS P.sourceSpace P.F hZ hid)
  exact (ClosedSubspaceModule.ofSchemeTheoreticSupport hZ G hG e).isUniversallyPureAbove_of_isProper
    hZY

/-! ### Purity of the algebraic space: Stacks 0CVD, parts (3) and (6) -/

/-- **The situation of Stacks 0CV6 whose module is the structure sheaf `𝒪_X`.** This is the
situation in which purity of the algebraic space `X` over `Y` is purity of a module: the
structure sheaf is the unit object of the category of modules on the small étale ringed site,
and is quasi-coherent and of finite type unconditionally. -/
noncomputable def structurePrePureSituation {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsFiniteType B S hS f) (hdec : IsDecent B S hS f) (y : points B S hS Y) :
    PrePureSituation.{u, u} B S hS where
  X := X
  Y := Y
  hX := hX
  hY := hY
  f := f
  finiteType := hft
  decent := hdec
  F := SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))
  moduleFiniteType := Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType _
    (PresheafOfModules.isFiniteType_unit _)
  moduleQuasicoherent := SheafOfModules.isQuasicoherentOnSite_unit _
  y := y

/-- The situation obtained from a situation of Stacks 0CV6 by replacing its module with the
structure sheaf `𝒪_X` of the source, keeping the morphism and the chosen point. -/
noncomputable abbrev PrePureSituation.structureSituation
    (P : PrePureSituation.{u, u} B S hS) : PrePureSituation.{u, u} B S hS :=
  structurePrePureSituation P.hX P.hY P.f P.finiteType P.decent P.y

/-- **Stacks 0CVD, part (3).** The algebraic space `X` is *pure above `y`* when its structure
sheaf `𝒪_X` is pure above `y`.

The module of the situation plays no role: the condition is part (1) for the situation with the
same morphism and the same chosen point whose module is `𝒪_X`. -/
@[stacks 0CVD "part (3)"]
def IsSpacePureAbove (P : PrePureSituation.{u, u} B S hS) : Prop :=
  IsPureAbove P.structureSituation

/-- **Stacks 0CVD, part (6).** The algebraic space `X` is *`Y`-pure*, or *pure relative to
`Y`*, when its structure sheaf `𝒪_X` is pure relative to `Y`.

This is part (5) for the situation whose module is `𝒪_X`; neither the module nor the chosen
point of the situation plays a role, the latter because purity relative to `Y` varies it over
all of `|Y|`. -/
@[stacks 0CVD "part (6)"]
def IsSpacePureRelative (P : PrePureSituation.{u, u} B S hS) : Prop :=
  IsPureRelative P.structureSituation

/-- Purity of `X` relative to `Y` is purity of `X` above every point of `Y`: replacing the
module of a situation by `𝒪_X` and varying its chosen point commute. -/
theorem isSpacePureRelative_iff (P : PrePureSituation.{u, u} B S hS) :
    IsSpacePureRelative P ↔ ∀ y : points B S hS P.Y, IsSpacePureAbove { P with y := y } :=
  Iff.rfl

/-! ### Stacks 0CVI, part (3) -/

/-- **Stacks 0CVI, part (3).** If `f : X ⟶ Y` is a proper decent morphism of algebraic spaces
over `S`, then `X` is universally pure above every point of `Y`, that is, universally pure
relative to `Y`.

This is part (2) for the situation whose module is the structure sheaf of `X`. -/
@[stacks 0CVI "part (3): the source of a proper decent morphism is universally pure above \
every point of the target"]
theorem isUniversallyPureAbove_structure_of_isProper
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hdec : IsDecent B S hS f) (hf : IsProper B S hS f) (y : points B S hS Y) :
    IsUniversallyPureAbove
      (structurePrePureSituation hX hY f (IsProper.isFiniteType B S hS hf) hdec y) :=
  isUniversallyPureAbove_of_isProper _ hf

end Proper

end AlgebraicGeometry.Space

end
