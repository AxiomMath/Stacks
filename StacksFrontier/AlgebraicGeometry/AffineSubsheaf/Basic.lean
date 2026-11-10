module

public import StacksFrontier.AlgebraicGeometry.CardinalGeneratedColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence

/-!
# The affine case of Tag 01PF, as a finite type quasi-coherent subsheaf

Let `X` be an affine scheme, `F` a quasi-coherent `𝒪_X`-module and `W` a quasi-compact open of
`X` over which `F` is of finite type. Then `F` has a **finite type** quasi-coherent subsheaf
which is all of `F` over `W`.

This is the affine case of [Stacks, Tag 01PF] — the last paragraph of the source's proof, after
its two reductions — turned from a statement about spanning sets of sections into a statement
about a subsheaf. `Stacks.AlgebraicGeometry.Tag01PFAffine.exists_finite_spanning_subset`
produces a finite set `A` of global sections of `F` whose restrictions generate the sections of
`F` over every affine open inside `W`; the subsheaf is the one cut out by the family of spans of
the restrictions of `A`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.spanRestrictFamily`: the family, indexed by
  the affine opens of `X`, of spans of the restrictions of a set of **global** sections of `F`.
* `Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.spanRestrictSubsheaf`: the subsheaf of `F`
  cut out by that family.

## Main results

* `isCompatible_spanRestrictFamily`: the family is compatible in the sense of
  `Stacks.AlgebraicGeometry.GabberColimit.IsCompatible`, with no hypothesis on the set of
  sections at all. Compatibility is immediate here precisely because the sections are *global*:
  the family is by construction the base change of its own value at `⊤`.
* `isQuasicoherent_spanRestrictSubsheaf` and `isFiniteType_spanRestrictSubsheaf`: the subsheaf
  is quasi-coherent, and is of finite type as soon as the set of global sections is finite.
* `obj_spanRestrictSubsheaf_eq_top`: the subsheaf is all of `F` over every open — not merely
  every affine open — on which the restrictions of the sections span.
* `exists_isFiniteType_submodule_eq_top_on`: **the affine case of [Stacks, Tag 01PF]**, from
  the hypothesis that the sections of `F` over the affine opens inside `W` are finite modules.
* `exists_isFiniteType_submodule_eq_top_on_of_generatingSections`: the same with that
  hypothesis replaced by finite type of `F` near the points of `W`, which is the form a caller
  holds.

## Implementation notes

No stacks attribute is attached. Tag 01PF is a single assertion about an arbitrary
quasi-compact and quasi-separated scheme, and what is proved here carries `IsAffine X`, which
the tag does not grant; the covering set of the tag is therefore not complete and the tag is
withheld. What the source does with this affine case is to extend a finite type quasi-coherent
subsheaf from a quasi-compact open `U'` of `X` to `U' ∪ V` for `V` affine, by applying it on `V`
to the quasi-coherent extension of the subsheaf across `U' ⊓ V ↪ V` given by
[Stacks, Tag 01PE] (formalized as `AlgebraicGeometry.exists_quasicoherentSubobject_restrict`), and
then gluing along `U' ⊓ V`; iterating over a finite affine covering of `X` gives the tag.
Neither the gluing step nor the iteration is in this file.

The hypothesis is confined to the affine opens inside `W` while the conclusion holds over every
open inside `W`, and the proof of that asymmetry is where `sheafSubmodule` earns its keep: its
sections over an open are by definition the sections of `F` lying in the family after
restriction to every affine open, so the conclusion over a general open follows from the affine
opens below it with no sheaf-condition argument.

The result is phrased with the sections of the subsheaf, as
`N.toSubmodule.obj (op Z) = ⊤` for `Z ≤ W`, rather than as an isomorphism of the restriction of
the subsheaf to `W` with the restriction of `F`. That is the currency the construction and its
consumers both use: `Stacks.AlgebraicGeometry.GabberColimit.IsCompatible` and
`Stacks.AlgebraicGeometry.GabberColimit.mem_of_cover` are stated over `X.affineOpens`, and so is
the hypothesis `hsec` that
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebraFiltered.nonempty_isColimit_of_affineSections`
still owes. Moving a
module sheaf across the open immersion `W.ι` is delicate: the sections agree by `rfl`
while the two scalar actions differ by `(W.ι.appIso _).inv`, whose body is not exposed.

Finite type is obtained from the sections and not from a generating-sections datum:
`Stacks.AlgebraicGeometry.IdealPowerSmul.isFiniteType_of_finite_sections` says a quasi-coherent
module whose sections over every affine open form a finite module is of finite type, and the
sections of the subsheaf over an affine open are by construction the span of a finite set. The
`instance_reducible` attribute on `AlgebraicGeometry.Scheme.Modules` and the `show` ascriptions
below are both needed for that step: the submodule produced by
`Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule` has its type inferred in the
`F.val.obj` spelling, for which `Module Γ(X, U) Γ(F, U)` is not an instance, and the ascription
is what pins the sections to the `Γ(F, U)` spelling that carries the module structure.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf

open Stacks.AlgebraicGeometry.GabberColimit

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The restrictions to an affine open of a set `A` of global sections of `F`. -/
def spanRestrict (A : Set Γ(F, ⊤)) (U : X.affineOpens) : Set Γ(F, U.1) :=
  F.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op '' A

/-- The family, indexed by the affine opens of `X`, of spans of the restrictions of a set `A` of
global sections of `F`. -/
def spanRestrictFamily (A : Set Γ(F, ⊤)) (U : X.affineOpens) :
    Submodule Γ(X, U.1) Γ(F, U.1) :=
  Submodule.span Γ(X, U.1) (spanRestrict F A U)

/-- **The family of spans of the restrictions of a set of global sections is compatible.** For
affine opens `V ≤ U` the restriction from `U` to `V` of the restriction from `⊤` to `U` is the
restriction from `⊤` to `V`, so both sides of the compatibility condition are the span of the
same set; no hypothesis on `A`, on `F` or on `X` is needed beyond quasi-coherence, which only
enters through the statement of `IsCompatible`. -/
theorem isCompatible_spanRestrictFamily [F.IsQuasicoherent] (A : Set Γ(F, ⊤)) :
    IsCompatible F (spanRestrictFamily F A) := by
  refine isCompatible_span F (spanRestrict F A) fun U V h ↦ ?_
  congr 1
  exact (Tag01PFAffine.image_res_res F (le_top : U.1 ≤ ⊤) h A).symm

/-- The quasi-coherent subsheaf of `F` cut out by the spans of the restrictions of a set `A` of
global sections of `F`. Its sections over an affine open `U` are the span over `Γ(X, U)` of the
restrictions of `A` to `U`, by `obj_spanRestrictSubsheaf`. -/
def spanRestrictSubsheaf [F.IsQuasicoherent] (A : Set Γ(F, ⊤)) : F.Submodule :=
  sheafSubmodule F (spanRestrictFamily F A) (isCompatible_spanRestrictFamily F A)

/-- The sections of `spanRestrictSubsheaf F A` over an affine open `U` are the span of the
restrictions of `A` to `U`. -/
theorem obj_spanRestrictSubsheaf [F.IsQuasicoherent] (A : Set Γ(F, ⊤)) (U : X.affineOpens) :
    (spanRestrictSubsheaf F A).toSubmodule.obj (op U.1) = spanRestrictFamily F A U :=
  obj_sheafSubmodule F (spanRestrictFamily F A) (isCompatible_spanRestrictFamily F A) U

/-- `spanRestrictSubsheaf F A` is quasi-coherent. -/
theorem isQuasicoherent_spanRestrictSubsheaf [F.IsQuasicoherent] (A : Set Γ(F, ⊤)) :
    (spanRestrictSubsheaf F A).toSheafOfModules.IsQuasicoherent :=
  isQuasicoherent_sheafSubmodule F (spanRestrictFamily F A) (isCompatible_spanRestrictFamily F A)

/-- **`spanRestrictSubsheaf F A` is of finite type when `A` is finite.** Its sections over an
affine open are the span of the finite set of restrictions of `A`, hence a finite module, and a
quasi-coherent module with finite sections over every affine open is of finite type. -/
theorem isFiniteType_spanRestrictSubsheaf [F.IsQuasicoherent] {A : Set Γ(F, ⊤)}
    (hA : A.Finite) : (spanRestrictSubsheaf F A).toSheafOfModules.IsFiniteType := by
  have hqc := isQuasicoherent_spanRestrictSubsheaf F A
  refine IdealPowerSmul.isFiniteType_of_finite_sections _ fun U ↦ ?_
  have hspan : Module.Finite Γ(X, U.1) ↥(spanRestrictFamily F A U) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span (hA.image _))
  have hobj : Module.Finite Γ(X, U.1) ↥(show Submodule Γ(X, U.1) Γ(F, U.1) from
      (spanRestrictSubsheaf F A).toSubmodule.obj (op U.1)) := by
    rw [obj_spanRestrictSubsheaf F A U]
    exact hspan
  exact hobj

/-- **`spanRestrictSubsheaf F A` is all of `F` over every open on which the restrictions of `A`
span.** The hypothesis is only about the *affine* opens inside `W`, and the conclusion is about
every open inside `W`: a section of `F` over such an open lies in the subsheaf exactly when its
restriction to every affine open below lies in the family, and each of those affine opens is
itself inside `W`. -/
theorem obj_spanRestrictSubsheaf_eq_top [F.IsQuasicoherent] (A : Set Γ(F, ⊤)) {W : X.Opens}
    (hA : ∀ V : X.affineOpens, V.1 ≤ W → spanRestrictFamily F A V = ⊤)
    {Z : X.Opens} (hZ : Z ≤ W) :
    (spanRestrictSubsheaf F A).toSubmodule.obj (op Z) = ⊤ := by
  rw [eq_top_iff]
  intro s _
  change IsLocallyIn F (spanRestrictFamily F A) s
  intro V h
  rw [hA V (h.trans hZ)]
  exact Submodule.mem_top

/-- **The affine case of [Stacks, Tag 01PF].** Let `F` be a quasi-coherent module on an affine
scheme `X` and let `W` be a quasi-compact open over which the sections of `F` are finite
modules. Then `F` has a finite type quasi-coherent subsheaf whose sections over every open
inside `W` are all of the sections of `F`.

The finiteness hypothesis is [Stacks, Tag 01PB] for a finite-type hypothesis holding only over
`W`; `exists_isFiniteType_submodule_eq_top_on_of_generatingSections` supplies it in that form.
The subsheaf is `spanRestrictSubsheaf F A` for the finite set `A` of global sections produced by
`Stacks.AlgebraicGeometry.Tag01PFAffine.exists_finite_spanning_subset`, which is the source's
`N' ⊆ N` generated by the numerators of generators of the localizations `N_{f_i}`. -/
theorem exists_isFiniteType_submodule_eq_top_on [IsAffine X] [F.IsQuasicoherent] {W : X.Opens}
    (hW : IsCompact (W : Set X))
    (hfin : ∀ Z : X.Opens, IsAffineOpen Z → Z ≤ W → Module.Finite Γ(X, Z) Γ(F, Z)) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧
      ∀ Z : X.Opens, Z ≤ W → N.toSubmodule.obj (op Z) = ⊤ := by
  obtain ⟨A, hAfin, hAspan⟩ := Tag01PFAffine.exists_finite_spanning_subset F
    (isAffineOpen_top X) (le_top : W ≤ ⊤) hW hfin
  refine ⟨spanRestrictSubsheaf F A, isQuasicoherent_spanRestrictSubsheaf F A,
    isFiniteType_spanRestrictSubsheaf F hAfin, fun Z hZ ↦ ?_⟩
  exact obj_spanRestrictSubsheaf_eq_top F A (fun V hV ↦ hAspan V.1 V.2 hV) hZ

/-- **The affine case of [Stacks, Tag 01PF], from finite type near the points of `W`.** This is
`exists_isFiniteType_submodule_eq_top_on` with its hypothesis in the shape a caller holds: `F`
has finitely many generating sections near every point of `W`. The passage to finiteness of the
sections over the affine opens inside `W` is
`Stacks.AlgebraicGeometry.Tag01PFAffine.finite_sections_le`, which is [Stacks, Tag 01PB]
relative to an open. -/
theorem exists_isFiniteType_submodule_eq_top_on_of_generatingSections [IsAffine X]
    [F.IsQuasicoherent] {W : X.Opens} (hW : IsCompact (W : Set X))
    (hloc : ∀ x ∈ W, ∃ (Z : X.Opens) (_ : x ∈ Z) (σ : (F.restrict Z.ι).GeneratingSections),
      Finite σ.I) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧
      ∀ Z : X.Opens, Z ≤ W → N.toSubmodule.obj (op Z) = ⊤ :=
  exists_isFiniteType_submodule_eq_top_on F hW
    fun _ hZ hZW ↦ Tag01PFAffine.finite_sections_le F hloc hZ hZW

end Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf

end
