module

public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# Modules with a two-term finite locally free resolution

A module `ℳ` on a scheme `Y` which sits at the right-hand end of a short exact sequence

`0 ⟶ 𝒜 ⟶ ℬ ⟶ ℳ ⟶ 0`

with `𝒜` and `ℬ` finite locally free is a perfect `𝒪_Y`-module of Tor dimension at most one; and,
in the other direction, the kernel of a surjection from a finite locally free module onto a module
of Tor dimension at most one is itself finite locally free as soon as it is finitely presented.
This file proves both implications.

Together they are the whole second paragraph of the proof of Stacks tag 0ESQ except for its first
sentence. That paragraph reads: the cokernel of each differential of a finite free model has Tor
dimension at most one by tag 0ESN (this is the first sentence, and it is not here); hence
`Im(d_i)` is finite locally free as the kernel of a map from a finite locally free module to a
finitely presented module of Tor dimension at most one; hence `Ker(d_i)` is finite locally free by
the same argument; hence the short exact sequence
`0 ⟶ Im(d_{i-1}) ⟶ Ker(d_i) ⟶ H^i(E) ⟶ 0` gives the conclusion of the tag. The second and third
steps are `AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude` and the fourth is
`AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_shortExact_isFiniteLocallyFree`.

Nothing below is about blowups or Fitting ideals: the statements are about an arbitrary short
exact sequence of modules on a scheme.

## Main definitions

* `AlgebraicGeometry.HasTwoTermFiniteLocallyFreeResolution`: the module is isomorphic to the
  cokernel of a monomorphism of finite locally free modules.

## Main results

* `Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₃`: Stacks tag 08CJ (1) at the
  ringed-space Tor-amplitude predicate, the companion of part (3)
  `Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₁`.
* `AlgebraicGeometry.hasTorAmplitude_singleFunctor_of_isFlat` and
  `AlgebraicGeometry.hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree`: a flat, in particular
  a finite locally free, module in degree zero has Tor amplitude in `[0, 0]`.
* `AlgebraicGeometry.isFlat_of_shortExact_hasTorAmplitude` and
  `AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_hasTorAmplitude`: the kernel of a surjection
  from a flat module onto a module of Tor dimension at most one is flat, and is finite locally
  free when the surjection's source is finite locally free and the kernel is finitely presented.
  This is the `Im`/`Ker` step of the source's second paragraph.
* `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_shortExact_isFiniteLocallyFree` and
  `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution`: a
  module with a two-term finite locally free resolution is perfect of Tor dimension at most one.
  This is the last step of the source's second paragraph.

## Implementation notes

Everything is read off the single distinguished triangle `𝒜[0] ⟶ ℬ[0] ⟶ ℳ[0] ⟶ 𝒜[1]` of the
short exact sequence (`CategoryTheory.ShortComplex.ShortExact.singleTriangle`), so no two-term
cochain complex has to be built by hand and no quasi-isomorphism onto `ℳ[0]` has to be produced.
For the `Im`/`Ker` step the triangle is used at its first vertex, tag 08CJ (3), which is the part
of 08CJ already available at the ringed-space spelling; the flatness so obtained is turned into
finite local freeness by the equivalence of entries (1) and (4) of Stacks tag 05P2,
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation`. For
the last step it is used at its third vertex:

* Perfectness is the third vertex of the triangle, Stacks tag 08CR
  (`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished`), the first two
  vertices being perfect because they are finite locally free
  (`AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree`).
* Tor amplitude is the third vertex in Stacks tag 08CJ (1), applied with `[a, b] = [-1, 0]`:
  `𝒜[0]` has Tor amplitude in `[0, 1]` and `ℬ[0]` in `[-1, 0]`, both by widening `[0, 0]`, so
  `ℳ[0]` has Tor amplitude in `[-1, 0]`. Part (1) of tag 08CJ was not available at the
  ringed-space spelling — only part (3) — so it is instantiated here from the abstract
  `TorAmplitude.hasTorAmplitude_obj₃` in exactly the way part (3) is, the only content being the
  translation between the two encodings of "outside `[a, b]`".

The Tor amplitude of a finite locally free module in degree zero goes through the easy half of
Stacks tag 08CI, `Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative`:
the complex with the module in degree zero represents it, is concentrated in `[0, 0]`, and has
flat terms, because a finite locally free module is flat
(`AlgebraicGeometry.Scheme.Modules.isFlat_of_isFiniteLocallyFree`) and a zero module is flat
(`Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_isZero`). The same statement exists in
the tree as the `private` lemma `hasTorAmplitude_single_isFiniteLocallyFree` of
`StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/`
`FiniteLocallyFreeReplacement.lean`, where it is stated for an arbitrary degree `b` and against
`DerivedCategory.Q` of the single complex; being `private` it cannot be used from here, and the
version below is stated at `DerivedCategory.singleFunctor`, which is the spelling the single
triangle of a short exact sequence is at.

Finite local freeness is taken in the `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` spelling,
which is the one `AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree` and
`AlgebraicGeometry.Scheme.Modules.isFlat_of_isFiniteLocallyFree` are both stated at. The class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` is the other spelling; the two carry the
same local trivialization data, and
`AlgebraicGeometry.isFiniteLocallyFree_of_isFiniteLocallyFreeClass` crosses from the second to the
first, replacing the `constructor`-plus-`exists_isFiniteLocallyFreeData` idiom that appears
inline in three places in the Fitting-blowup files.

The translating `HasDerivedCategory` instance of
`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/OnARingedSpace.lean` is re-seated with
`attribute [local instance]` rather than restated: the declaration name is exported even though
the instance attribute is not, which is the route
`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/DirectSummands.lean` takes.

## References

* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry TopologicalSpace StrictlyPerfect
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u d

namespace Stacks.Cohomology.TorAmplitude.FlatOpcycles

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]

attribute [local instance] Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Tag 08CJ (1) at the ringed-space Tor-amplitude predicate.** In a distinguished triangle
`K ⟶ L ⟶ M ⟶ K[1]` of `D(O_X)`, if `K` has Tor amplitude in `[a + 1, b + 1]` and `L` has Tor
amplitude in `[a, b]`, then `M` has Tor amplitude in `[a, b]`.

This is `TorAmplitude.hasTorAmplitude_obj₃` read through
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.tensorSingleFunctor`, exactly as
`Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₁` reads part (3) through it; the
only content is the translation between the two encodings of "outside `[a, b]`". -/
@[stacks 08CJ "(1), at the ringed-space Tor-amplitude predicate"]
theorem hasTorAmplitude_obj₃
    (T : Triangle (DerivedCategory (RingedSpace.KFlatDerivedPullback.Modules X)))
    (hT : T ∈ distinguishedTriangles) (a b : ℤ)
    (hK : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₁ (a + 1) (b + 1))
    (hL : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₂ a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₃ a b := by
  have h := @TorAmplitude.hasTorAmplitude_obj₃
    (RingedSpace.KFlatDerivedPullback.Modules X) _ _ _ (tensorSingleFunctor X)
    (fun F => (Stacks.Cohomology.TorAmplitude.derTensor X).commShift_left
      ((DerivedCategory.singleFunctor (RingedSpace.KFlatDerivedPullback.Modules X) 0).obj F))
    (fun F => (Stacks.Cohomology.TorAmplitude.derTensor X).exact_left
      ((DerivedCategory.singleFunctor (RingedSpace.KFlatDerivedPullback.Modules X) 0).obj F))
    T hT a b
    (fun F i hi => hK F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
    (fun F i hi => hL F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
  exact fun F i hi => h F i (by simp only [Set.mem_Icc, not_and_or, not_le] at hi; omega)

end Stacks.Cohomology.TorAmplitude.FlatOpcycles

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- The class spelling of finite local freeness gives the bundled one: both carry exactly the
existence of local trivialization data. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeClass {Y : Scheme.{u}} (M : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) M := by
  constructor
  exact SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData

/-- **A finite locally free module in degree zero has Tor amplitude in `[0, 0]`.**

The complex with the module in degree zero represents it, is concentrated in `[0, 0]`, and has
flat terms — the module itself by hypothesis, every other term because it is zero — so the easy
half of Stacks tag 08CI applies. -/
@[sga "6 I 5.4" "Case n = 0"]
theorem hasTorAmplitude_singleFunctor_of_isFlat (Y : Scheme.{u}) (M : Y.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) M) :
    HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj M) 0 0 := by
  classical
  set K := (HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) 0).obj M with hK
  have hflat (i : ℤ) : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.sheaf) (K.X i) := by
    by_cases hi : i = 0
    · subst hi
      rw [hK, show ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) 0).obj M).X 0 = M from
        HomologicalComplex.single_obj_X_self _ _ _]
      exact hM
    · exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)
  have hterms (i : ℤ) (hi : i ∉ Set.Icc (0 : ℤ) 0) : IsZero (K.X i) := by
    have hi0 : i ≠ 0 := by simp only [Set.mem_Icc] at hi; omega
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi0
  exact Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative.{u, u + 1}
    (X := Y.toRingedSpace) _ 0 0 K hflat hterms (Iso.refl _)

/-- **A finite locally free module in degree zero has Tor amplitude in `[0, 0]`.** A finite
locally free module is flat, by the flatness half of Stacks tag 05P2. -/
theorem hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree (Y : Scheme.{u}) (M : Y.Modules)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) M) :
    HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj M) 0 0 :=
  hasTorAmplitude_singleFunctor_of_isFlat Y M
    (@Scheme.Modules.isFlat_of_isFiniteLocallyFree Y M hM)

/-- Tor amplitude in `[0, 0]` widens to `[-1 + 1, 0 + 1]`. -/
private theorem hasTorAmplitude_shift_of_hasTorAmplitude_zero {Y : Scheme.{u}}
    {K : DerivedCategory Y.Modules} (h : HasTorAmplitude Y.toRingedSpace K 0 0) :
    HasTorAmplitude Y.toRingedSpace K (-1 + 1) (0 + 1) :=
  Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1} h
    (show (-1 : ℤ) + 1 ≤ 0 by omega) (show (0 : ℤ) ≤ 0 + 1 by omega)

/-- **The kernel of a surjection from a flat module onto a module of Tor dimension at most one is
flat.** For a short exact sequence `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` of `𝒪_Y`-modules with `ℬ` flat and `𝒞`,
placed in degree zero, of Tor amplitude in `[-1, 0]`, the module `𝒜` is flat.

This is the mechanism behind both finite-local-freeness steps of the second paragraph of the proof
of Stacks tag 0ESQ: `Im(d_i)` is the kernel of a surjection from the finite free module
`𝒪^{⊕n_{i+1}}` onto `Coker(d_i)`, which tag 0ESN makes of Tor dimension at most one, and
`Ker(d_i)` is then the kernel of a surjection from `𝒪^{⊕n_i}` onto `Im(d_i)`.

The short exact sequence gives the distinguished triangle `𝒜[0] ⟶ ℬ[0] ⟶ 𝒞[0] ⟶ 𝒜[1]`, and tag
08CJ (3) with `[a, b] = [-1, 0]` puts `𝒜[0]` in Tor amplitude `[0, 1]`, from `ℬ[0]` in `[0, 1]`
and `𝒞[0]` in `[-1, 0]`. A module whose Tor amplitude starts at the degree it sits in is flat
(`Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_hasTorAmplitude_single`). -/
theorem isFlat_of_shortExact_hasTorAmplitude {Y : Scheme.{u}} (S : ShortComplex Y.Modules)
    (hS : S.ShortExact)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) S.X₂)
    (h₃ : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₃) (-1) 0) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) S.X₁ := by
  have hB := hasTorAmplitude_shift_of_hasTorAmplitude_zero
    (hasTorAmplitude_singleFunctor_of_isFlat Y S.X₂ h₂)
  have hA : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₁) 0 1 :=
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₁.{u, u + 1}
        hS.singleTriangle hS.singleTriangle_distinguished (-1) 0 hB h₃)
      (show (0 : ℤ) ≤ -1 + 1 by omega) (show (0 : ℤ) + 1 ≤ 1 by omega)
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_hasTorAmplitude_single.{u, u + 1}
    S.X₁ 0 1 hA

/-- **The kernel of a surjection from a finite locally free module onto a module of Tor dimension
at most one is finite locally free, as soon as it is finitely presented.** For a short exact
sequence `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` of `𝒪_Y`-modules with `ℬ` finite locally free, `𝒞` of Tor amplitude
in `[-1, 0]` in degree zero, and `𝒜` finitely presented, the module `𝒜` is finite locally free.

This is the sentence "`Im(d_i)` is finite locally free as the kernel of a map from a finite
locally free module to a finitely presented module of tor dimension `≤ 1`; hence `Ker(d_i)` is
finite locally free as well (same argument)" of the proof of Stacks tag 0ESQ. `𝒜` is flat by
`AlgebraicGeometry.isFlat_of_shortExact_hasTorAmplitude`, and flat plus finitely presented is
finite locally free by the equivalence of entries (1) and (4) of Stacks tag 05P2,
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation`. -/
theorem isFiniteLocallyFree_of_shortExact_hasTorAmplitude {Y : Scheme.{u}}
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (h₂ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) S.X₂)
    (h₃ : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₃) (-1) 0)
    (hfp : SheafOfModules.IsFinitePresentation.{u, u, u} S.X₁) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) S.X₁ := by
  have hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) S.X₁ :=
    isFlat_of_shortExact_hasTorAmplitude S hS
      (@Scheme.Modules.isFlat_of_isFiniteLocallyFree Y S.X₂ h₂) h₃
  have hclass : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁ :=
    (SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation S.X₁).mpr
      ⟨hflat, hfp⟩
  exact isFiniteLocallyFree_of_isFiniteLocallyFreeClass S.X₁

/-- **A module at the right-hand end of a short exact sequence of finite locally free modules is
perfect of Tor dimension at most one.** For a short exact sequence `0 ⟶ 𝒜 ⟶ ℬ ⟶ ℳ ⟶ 0` of
`𝒪_Y`-modules with `𝒜` and `ℬ` finite locally free, the module `ℳ` placed in degree zero is a
perfect object of `D(𝒪_Y)` and has Tor amplitude in `[-1, 0]`.

This is the last step of the second paragraph of the proof of Stacks tag 0ESQ. The short exact
sequence gives the distinguished triangle `𝒜[0] ⟶ ℬ[0] ⟶ ℳ[0] ⟶ 𝒜[1]`. Perfectness of the third
vertex is tag 08CR, the first two vertices being perfect because they are finite locally free.
Tor amplitude of the third vertex is tag 08CJ (1) with `[a, b] = [-1, 0]`: the first vertex has
Tor amplitude in `[0, 1]` and the second in `[-1, 0]`, both by widening `[0, 0]`. -/
theorem isPerfect_and_hasTorAmplitude_of_shortExact_isFiniteLocallyFree {Y : Scheme.{u}}
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (h₁ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) S.X₁)
    (h₂ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) S.X₂) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₃) ∧
      HasTorAmplitude Y.toRingedSpace
        ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₃) (-1) 0 := by
  have hA := hasTorAmplitude_shift_of_hasTorAmplitude_zero
    (hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree Y S.X₁ h₁)
  have hB : HasTorAmplitude Y.toRingedSpace
      ((DerivedCategory.singleFunctor Y.Modules 0).obj S.X₂) (-1) 0 :=
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree Y S.X₂ h₂)
      (show (-1 : ℤ) ≤ 0 by omega) le_rfl
  exact ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished
      hS.singleTriangle hS.singleTriangle_distinguished
      (isPerfect_singleFunctor_of_isFiniteLocallyFree Y S.X₁ h₁)
      (isPerfect_singleFunctor_of_isFiniteLocallyFree Y S.X₂ h₂),
    Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₃.{u, u + 1}
      hS.singleTriangle hS.singleTriangle_distinguished (-1) 0 hA hB⟩

/-- **A global resolution of length one by finite locally free modules.** The module is
isomorphic to the cokernel of a monomorphism `𝒜 ⟶ ℬ` of finite locally free `𝒪_Y`-modules.

This is what the second paragraph of the proof of Stacks tag 0ESQ produces for `H^i(Lb^*E)`,
with `𝒜 = Im(d_{i-1})` and `ℬ = Ker(d_i)` for a finite free model of the pullback of the
complex. -/
def HasTwoTermFiniteLocallyFreeResolution {Y : Scheme.{u}} (M : Y.Modules) : Prop :=
  ∃ S : ShortComplex Y.Modules, S.ShortExact ∧
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) S.X₁ ∧
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) S.X₂ ∧
    Nonempty (S.X₃ ≅ M)

/-- **A module with a two-term finite locally free resolution is perfect of Tor dimension at most
one.** This is
`AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_shortExact_isFiniteLocallyFree` transported
along the isomorphism of the module with the cokernel of the resolution: perfectness is invariant
under isomorphism in `D(𝒪_Y)`, and so is Tor amplitude. -/
theorem isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution {Y : Scheme.{u}}
    (M : Y.Modules) (h : HasTwoTermFiniteLocallyFreeResolution M) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor Y.Modules 0).obj M) ∧
      HasTorAmplitude Y.toRingedSpace
        ((DerivedCategory.singleFunctor Y.Modules 0).obj M) (-1) 0 := by
  obtain ⟨S, hS, h₁, h₂, ⟨e⟩⟩ := h
  obtain ⟨hperf, htor⟩ :=
    isPerfect_and_hasTorAmplitude_of_shortExact_isFiniteLocallyFree S hS h₁ h₂
  refine ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((DerivedCategory.singleFunctor Y.Modules 0).mapIso e) hperf, ?_⟩
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} htor
    ((DerivedCategory.singleFunctor Y.Modules 0).mapIso e).symm

end AlgebraicGeometry

end
