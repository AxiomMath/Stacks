module

public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.Restriction
public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Extension
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# Coherence and reflexivity are local on affine opens

Both properties of a module on a locally Noetherian scheme that the proof of
[Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) checks after reducing to an affine
scheme — coherence and reflexivity — may be checked on the restrictions to the members of a
covering by *nonempty* affine opens.  The restriction to the nonempty members is enough because
every point lies in one, and it matters: an integrality hypothesis is not available on an empty
open subscheme.

For coherence this is condition (5) of [Stacks, Tag 01XZ], that is
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_exists_affineOpenCover_isFiniteTildeOn`,
once coherence of a restriction is turned into the `IsFiniteTildeOn` predicate that condition is
phrased with.  For reflexivity it is the stalk criterion of [Stacks, Tag 0AY3]
(`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_tfae`) together with the comparison of
the stalk of a restriction with the stalk at the image point
(`module_isReflexive_modStalk_of_restrict`).

## Main results

* `isFiniteTildeOn_of_isCoherent_restrict`: coherence of `F|_U` for `U` an affine open gives
  condition (4) of Tag 01XZ at `U`.  The library's `isFiniteTildeOn_of_isCoherent` asks for
  coherence of `F` itself, which is what makes it useless for a locality argument.
* `isCoherent_of_forall_isAffineOpen_restrict`: **coherence is local on nonempty affine opens.**
* `isReflexive_of_forall_isAffineOpen_restrict`: **reflexivity is local on nonempty affine
  opens**, for a coherent module.
* `isCoherent_and_isReflexive_of_forall_isAffineOpen_restrict`: the two together, which is the
  form the reduction to the affine case consumes.

## Implementation notes

`isFiniteTildeOn_of_isCoherent_restrict` is the `restrictIsoSpecTilde` argument with its
hypothesis weakened from quasi-coherence of `F` to quasi-coherence of `F|_U`: the only use of the
hypothesis is to know that `F|_U` read on `Spec Γ(X, U)` is quasi-coherent, and that already
follows from quasi-coherence of `F|_U`.  Rather than restate `restrictIsoSpecTilde` the
isomorphism is rebuilt inline from `restrictIsoSelf` and `fromTildeΓ`.

The covering is indexed by the points of `X`, each point being assigned an affine open
neighbourhood by `AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`; such an open is
nonempty by construction, which is how the `Nonempty` hypothesis is discharged.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **Condition (4) of [Stacks, Tag 01XZ] at an affine open, from coherence of the restriction
alone.**  If `F|_U` is coherent for `U` an affine open, then `F|_U` is the `tilde` of a finite
`Γ(X, U)`-module read through `U ≅ Spec Γ(X, U)`.

The library's `isFiniteTildeOn_of_isCoherent` assumes `F` itself coherent, which a locality
argument cannot use. -/
public theorem isFiniteTildeOn_of_isCoherent_restrict {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) (h : (F.restrict U.ι).IsCoherent) :
    IsFiniteTildeOn F U hU := by
  have := h
  have hq : (F.restrict U.ι).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  have hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} (F.restrict U.ι) :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  have hsq : (specRestrict F hU).IsQuasicoherent := inferInstance
  have hsft : _root_.SheafOfModules.IsFiniteType.{u, u, u} (specRestrict F hU) :=
    isFiniteType_restrict hU.isoSpec.inv _
  have htft : _root_.SheafOfModules.IsFiniteType.{u, u, u} (tilde (specModule F hU)) :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (M := specRestrict F hU)
      (asIso (specRestrict F hU).fromTildeΓ).symm
  refine ⟨specModule F hU,
    (AlgebraicGeometry.tilde_isFiniteType_iff (specModule F hU)).mp htft, ⟨?_⟩⟩
  exact (restrictIsoSelf hU.isoSpec (F.restrict U.ι)).symm ≪≫
    (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso
      (asIso (specRestrict F hU).fromTildeΓ).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app _

/-- Every point of a scheme `X` has an affine open neighbourhood, chosen as a family. -/
private theorem exists_forall_isAffineOpen_mem (X : Scheme.{u}) :
    ∃ V : X → X.Opens, (∀ x, IsAffineOpen (V x)) ∧ ∀ x, x ∈ V x := by
  choose V hV hxV _ using fun x : X =>
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := x)
      (U := (⊤ : X.Opens)) trivial
  exact ⟨V, hV, hxV⟩

/-- **Coherence is local on nonempty affine opens.**  A module on a locally Noetherian scheme
whose restriction to every nonempty affine open is coherent is coherent.

This is condition (5) ⇒ (1) of [Stacks, Tag 01XZ] applied to the covering of `X` by a chosen
affine open neighbourhood of each of its points. -/
public theorem isCoherent_of_forall_isAffineOpen_restrict {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules)
    (h : ∀ V : X.Opens, IsAffineOpen V → Nonempty V → (F.restrict V.ι).IsCoherent) :
    F.IsCoherent := by
  classical
  obtain ⟨V, hV, hxV⟩ := exists_forall_isAffineOpen_mem X
  exact CoherenceCriteria.isCoherent_of_exists_affineOpenCover_isFiniteTildeOn
    F ⟨X, V, top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩, fun x =>
      ⟨hV x, isFiniteTildeOn_of_isCoherent_restrict F (V x) (hV x)
        (h (V x) (hV x) ⟨⟨x, hxV x⟩⟩)⟩⟩

/-- **Reflexivity is local on nonempty affine opens**, for a coherent module on a locally
Noetherian scheme.

Reflexivity of a coherent module is detected on stalks ([Stacks, Tag 0AY3]), and the stalk of
`F` at a point of an open `V` is the stalk of `F|_V` there — the comparison
`module_isReflexive_modStalk_of_restrict`. -/
public theorem isReflexive_of_forall_isAffineOpen_restrict {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) (hFcoh : F.IsCoherent)
    (h : ∀ V : X.Opens, IsAffineOpen V → Nonempty V → IsReflexive (F.restrict V.ι)) :
    IsReflexive F := by
  classical
  have := hFcoh
  obtain ⟨V, hV, hxV⟩ := exists_forall_isAffineOpen_mem X
  refine ((isReflexive_tfae X F).out 1 2).mpr fun x => ?_
  have hVN : IsLocallyNoetherian (V x).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (V x).ι
  have hVcoh : (F.restrict (V x).ι).IsCoherent :=
    isCoherent_restrict_of_isCoherent X (V x) F hFcoh
  have hstalk := ((isReflexive_tfae (V x).toScheme (F.restrict (V x).ι)).out 1 2).mp
    (h (V x) (hV x) ⟨⟨x, hxV x⟩⟩)
  exact module_isReflexive_modStalk_of_restrict (V x).ι F ⟨x, hxV x⟩ (hstalk ⟨x, hxV x⟩)

/-- **Coherence and reflexivity together are local on nonempty affine opens.**  This is the
reduction the proof of [Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) performs
when it says "to prove this we may assume `X` is affine". -/
public theorem isCoherent_and_isReflexive_of_forall_isAffineOpen_restrict {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules)
    (h : ∀ V : X.Opens, IsAffineOpen V → Nonempty V →
      (F.restrict V.ι).IsCoherent ∧ IsReflexive (F.restrict V.ι)) :
    F.IsCoherent ∧ IsReflexive F :=
  have hcoh : F.IsCoherent :=
    isCoherent_of_forall_isAffineOpen_restrict F fun V hVa hVn => (h V hVa hVn).1
  ⟨hcoh, isReflexive_of_forall_isAffineOpen_restrict F hcoh fun V hVa hVn => (h V hVa hVn).2⟩

end Stacks.AlgebraicGeometry.ReflexiveModules

end
