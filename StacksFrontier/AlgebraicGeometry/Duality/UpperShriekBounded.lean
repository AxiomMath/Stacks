module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Bounded

/-!
# The relative dualizing complex has bounded coherent cohomology

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a flat morphism of finite presentation
in `AlgebraicGeometry.FTS S`, the category of [Stacks, Tag 0F42]. The relative dualizing
complex of `f` is `ω^•_{X/Y} = f^!𝒪_Y`, where `f^!` is `Stacks.Duality.upperShriek` and `𝒪_Y`
is `Stacks.Duality.DerivedPushforward.derivedStructureSheaf`. This file proves that it lies
in `D^b_Coh(𝒪_X)`, which is part (a) of [Stacks, Tag 0B6U] (Lemma 48.17.9).

## Main results

* `Stacks.Duality.derivedCategoryBBounded_upperShriek_derivedStructureSheaf` —
  **[Stacks, Tag 0B6U]**, part (a): `f^!𝒪_Y ∈ D^b_Coh(𝒪_X)`.
* `Stacks.Duality.isCoherent_homology_of_tildeModels` and
  `Stacks.Duality.isBounded_of_tildeModels` — the two halves of the globalisation: a complex
  which on the members of an affine covering is the associated sheaf of a complex with finite
  cohomology has coherent cohomology, and one which is so with a *bounded* complex is bounded.

## Implementation notes

*What is carried.* One hypothesis is carried, `h0BV2`. It is the affine-chart description of
`f^!`: over an affine `V ⊆ Y` and an affine `U ⊆ f⁻¹(V)`, the restriction of `f^!𝒪_Y` to `U` is
the associated sheaf of the *algebraic* upper shriek, along a polynomial presentation of the
chart ring map `f.appLE V U`, of the complex `Γ(Y, V)` placed in degree zero — the model of
`𝒪_Y` over the affine `V`. This is the content of [Stacks, Tag 0AA1] together with the affine
comparison of [Stacks, Tag 0BV2], neither of which is available in this repository. Writing the
chart ring map as `f.appLE V U` and the model as `Γ(Y, V)` itself is what ties the hypothesis to
`f` and to `𝒪_Y`.

The hypothesis says nothing about any complex being bounded or having coherent cohomology; it
only names an isomorphism. The boundedness and the coherence come from
[Stacks, Tag 0BZK] (2), `Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_isPerfectRingMap`,
which says that the algebraic upper shriek along a perfect homomorphism of Noetherian rings
carries `D^b_Coh(R)` into `D^b_Coh(A)`, together with the globalisation proved here.

*Perfectness is not carried.* The source's hypothesis is that `f` is perfect, flatness together
with finite presentation sufficing by [Stacks, Tag 068A]. That implication is
`AlgebraicGeometry.perfect_of_flat_of_locallyOfFinitePresentation`, and the class field
`AlgebraicGeometry.Perfect.perfect_appLE` then supplies, for each pair of affine charts, exactly
the `RingHom.IsPerfectRingMap` that Tag 0BZK (2) consumes — evaluated at the canonical derived
tensoring `StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring`, so nothing about the
derived tensor product is assumed either.

*The two derived categories.* `Stacks.Duality.upperShriek` lives on
`Stacks.Duality.quasiCoherentDerivedCategory`, read at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` (derived universe `u`), while the derived
category of a chart ring is read at `CategoryTheory.HasDerivedCategory.standard` (derived
universe `u + 1`). The two never need to be compared: the universes keep them apart, and the
globalisation statements below are stated for an arbitrary `HasDerivedCategory.{w} X.Modules`
so that they apply at the model `f^!` uses.

*Relation to the dualizing-complex files.*
`Stacks.Duality.isCoherent_homology_of_tildeModels` is the argument of
`Stacks.Duality.isCoherent_homology_of_isDualizingComplex` with "dualizing" weakened to "finite
cohomology in every degree" and with the all-affine-opens quantifier weakened to a covering; the
complexes produced by Tag 0BZK (2) are bounded with finite cohomology but are not dualizing, so
the weaker hypothesis is the one available here.

## References

* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
* [Stacks Project, Tag 068A](https://stacks.math.columbia.edu/tag/068A)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.CoherentOfFiniteType
open StacksDraft.TorAmplitude

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w

namespace Stacks.Duality

open DerivedPushforward

/-! ### The cohomology of a tilde model -/

section TildeModel

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- **The cohomology of a tilde model is a tilde model of the cohomology.** If `K|_U` is the
associated sheaf of the complex `ω` over `Γ(X, U)`, then `H^i(K)|_U` is the associated sheaf of
the `Γ(X, U)`-module `H^i(ω)`. -/
def homologyRestrictIsoTilde {K : DerivedCategory X.Modules} {U : X.Opens}
    (hU : IsAffineOpen U) {ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(X, U))}
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj K).restrict U.ι ≅
      (Scheme.Modules.pullback hU.isoSpec.hom).obj
        (tilde ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)) :=
  ((Dualizing.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U.ι) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (Dualizing.mapDerivedCategoryHomologyIso
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) i).app ω ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app _

/-- **A tilde model with finite cohomology in degree `i` exhibits `H^i(K)|_U` as a finite
tilde**, which is condition (4) of [Stacks, Tag 01XZ] for `H^i(K)` at `U`. -/
theorem isFiniteTildeOn_homology_of_tildeModel {K : DerivedCategory X.Modules} {U : X.Opens}
    {hU : IsAffineOpen U} {ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(X, U))} (i : ℤ)
    (hfin : Module.Finite Γ(X, U)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω))
    (he : Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)) :
    IsFiniteTildeOn ((DerivedCategory.homologyFunctor X.Modules i).obj K) U hU :=
  ⟨_, hfin, ⟨homologyRestrictIsoTilde hU he.some i⟩⟩

/-- **A tilde model vanishing in degree `i` makes `H^i(K)|_U` vanish.** The associated sheaf of
a zero module is zero, and pulling back preserves zero objects. -/
theorem isZero_restrict_homology_of_tildeModel {K : DerivedCategory X.Modules} {U : X.Opens}
    {hU : IsAffineOpen U} {ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(X, U))} (i : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω))
    (he : Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :=
  IsZero.of_iso
    ((Scheme.Modules.pullback hU.isoSpec.hom).map_isZero
      ((tilde.functor Γ(X, U)).map_isZero hz))
    (homologyRestrictIsoTilde hU he.some i)

end TildeModel

/-! ### Globalisation -/

section Globalise

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- The chart data a complex is required to have at a point: an affine open neighbourhood `U`
and a complex over `Γ(X, U)` whose associated sheaf is `K|_U`. -/
def HasTildeModelAt (K : DerivedCategory X.Modules) (x : X) : Prop :=
  ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
    ∃ ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(X, U)),
      (DerivedCategoryB.IsBounded ω ∧
        ∀ i : ℤ, Module.Finite Γ(X, U)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)) ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
        (tilde.functor Γ(X, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)

/-- **The cohomology sheaves of a complex with tilde models are coherent.** The chart
neighbourhoods cover `X`, and on each of them the cohomology sheaf is the associated sheaf of a
finite module, so it is quasi-coherent and of finite type; on a locally Noetherian scheme that
is coherence, by [Stacks, Tag 01XZ] (2) ⇒ (1). -/
theorem isCoherent_homology_of_tildeModels [IsLocallyNoetherian X]
    {K : DerivedCategory X.Modules} (h : ∀ x : X, HasTildeModelAt.{u, w} K x) (i : ℤ) :
    _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules i).obj K) := by
  choose U hU hxU ω hω he using h
  set F := (DerivedCategory.homologyFunctor X.Modules i).obj K with hF
  have hcov : IsOpenCover U := by
    refine SetLike.ext fun x => ⟨fun _ => trivial, fun _ => ?_⟩
    simpa only [Opens.mem_iSup] using ⟨x, hxU x⟩
  have hfin : ∀ x : X, IsFiniteTildeOn F (U x) (hU x) := fun x =>
    isFiniteTildeOn_homology_of_tildeModel i ((hω x).2 i) (he x)
  have _ : F.IsQuasicoherent :=
    isQuasicoherent_of_cover_isFiniteTildeOn F U hcov hU hfin
  have _ : F.IsFiniteType :=
    isFiniteType_of_cover_isFiniteTildeOn F U hcov hU hfin
  exact isCoherent_of_isQuasicoherent_of_isFiniteType F

/-- **A complex with bounded tilde models is bounded.** Each chart bounds the cohomology of `K`
on a neighbourhood; a quasi-compact scheme is covered by finitely many of the charts, the
finitely many bounds have a common bound, and vanishing of a sheaf of modules is local. -/
theorem isBounded_of_tildeModels [CompactSpace X] {K : DerivedCategory X.Modules}
    (h : ∀ x : X, HasTildeModelAt.{u, w} K x) :
    DerivedCategoryB.IsBounded K := by
  classical
  choose U hU hxU ω hω he using h
  choose a ha using fun x : X => (hω x).1.1
  choose b hb using fun x : X => (hω x).1.2
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (X : Type u))).elim_finite_subcover
      (ι := (X : Type u)) (fun x : (X : Type u) => (U x : Set (X : Type u)))
      (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  have hcov : ⨆ x : {x : (X : Type u) // x ∈ t}, U x.1 = ⊤ := by
    refine SetLike.ext fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact Opens.mem_iSup.2 ⟨⟨i, hit⟩, hyi⟩
  have key : ∀ (n : ℤ), (∀ x : (X : Type u), x ∈ t →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U x)) n).obj (ω x))) →
      IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj K) := by
    intro n hn
    refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover
      (fun x : {x : (X : Type u) // x ∈ t} => U x.1) hcov _ fun x => ?_
    exact isZero_restrict_homology_of_tildeModel n (hn x.1 x.2) (he x.1)
  constructor
  · obtain ⟨c, hc⟩ := (t.image fun x => -a x).exists_le
    refine ⟨-c, fun n hn => key n fun x hxt => ha x n ?_⟩
    have := hc (-a x) (Finset.mem_image_of_mem _ hxt)
    omega
  · obtain ⟨c, hc⟩ := (t.image b).exists_le
    refine ⟨c, fun n hn => key n fun x hxt => hb x n ?_⟩
    have := hc (b x) (Finset.mem_image_of_mem _ hxt)
    omega

end Globalise

/-! ### Tag 0B6U, part (a) -/

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- The model of `𝒪_Y` over an affine open `V ⊆ Y`: the ring `Γ(Y, V)` itself, placed in
degree zero. -/
abbrev structureModel (V : Y.left.Opens) :
    DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(Y.left, V)) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y.left, V)) 0).obj
    (ModuleCat.of Γ(Y.left, V) Γ(Y.left, V))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The model of `𝒪_Y` over an affine open is bounded with finite cohomology, that is, it lies
in `D^b_Coh(Γ(Y, V))`: it is a single finite module in degree zero. -/
theorem derivedCategoryBBounded_structureModel (V : Y.left.Opens) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : ModuleCat.{u} Γ(Y.left, V) ↦ Module.Finite Γ(Y.left, V) M)
      (structureModel (Y := Y) V) := by
  have hz : ∀ n : ℤ, n ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(Y.left, V)) n).obj
        (structureModel (Y := Y) V)) := by
    intro n hn
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} Γ(Y.left, V)) n).app _)
    exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ n hn
  refine ⟨⟨⟨0, fun n hn => hz n (by omega)⟩, ⟨0, fun n hn => hz n (by omega)⟩⟩, fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    have e := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} Γ(Y.left, V)) 0).app (ModuleCat.of Γ(Y.left, V) Γ(Y.left, V))
    have _ : Module.Finite Γ(Y.left, V)
        ((𝟭 (ModuleCat.{u} Γ(Y.left, V))).obj (ModuleCat.of Γ(Y.left, V) Γ(Y.left, V))) :=
      inferInstanceAs (Module.Finite Γ(Y.left, V) Γ(Y.left, V))
    exact Module.Finite.equiv e.symm.toLinearEquiv
  · have _ : Subsingleton
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(Y.left, V)) n).obj
          (structureModel (Y := Y) V)) :=
      ModuleCat.isZero_iff_subsingleton.1 (hz n hn)
    have _ : Finite
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(Y.left, V)) n).obj
          (structureModel (Y := Y) V)) := Finite.of_subsingleton
    exact Module.Finite.of_finite


/-- **Stacks Project, Tag 0B6U (Lemma 48.17.9), part (a).** In Situation 48.16.1, let
`f : X ⟶ Y` be a morphism of `FTS S` which is flat and of finite presentation, so perfect by
[Stacks, Tag 068A]. Then the relative dualizing complex `ω^•_{X/Y} = f^!𝒪_Y` lies in
`D^b_Coh(𝒪_X)`: it is cohomologically bounded and all its cohomology sheaves are coherent.

The affine-chart description of `f^!` is the carried hypothesis `h0BV2`; everything that is
asserted about boundedness and coherence is proved, from [Stacks, Tag 0BZK] (2) for
the algebraic upper shriek and the globalisation of this file. -/
theorem derivedCategoryBBounded_upperShriek_derivedStructureSheaf
    [Flat f.left] [LocallyOfFinitePresentation f.left]
    (h0BV2 : ∀ x : X.left, ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (_hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
            (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) ≅
          (tilde.functor Γ(X.left, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
              (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)))) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules ↦ _root_.SheafOfModules.IsCoherent M)
      (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) := by
  have hnoeth : ∀ Z : AlgebraicGeometry.FTS S, IsLocallyNoetherian Z.left := fun Z => by
    have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
      inferInstanceAs (IsLocallyNoetherian S)
    exact LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hYn := hnoeth Y
  have hXn := hnoeth X
  have hXc : CompactSpace X.left := by
    have : CompactSpace ((Functor.fromPUnit S).obj X.right) :=
      inferInstanceAs (CompactSpace S)
    exact QuasiCompact.compactSpace_of_compactSpace X.hom
  have hmodels : ∀ x : X.left,
      HasTildeModelAt.{u, u}
        (((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj) x := by
    intro x
    obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ := h0BV2 x
    have hVn : IsNoetherianRing Γ(Y.left, V) :=
      IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have hUn : IsNoetherianRing Γ(X.left, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let D : CertifiedDerivedTensoring.{u, u} Γ(Y.left, V) :=
      canonicalCertifiedDerivedTensoring Γ(Y.left, V)
    have hperf := AlgebraicGeometry.Perfect.perfect_appLE f.left U hU V hV hUV D
    exact ⟨U, hU, hxU, _,
      Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_isPerfectRingMap.{u, u} p
        D.tensor D.comparison D.isLeftDerived hperf
        (derivedCategoryBBounded_structureModel (Y := Y) V),
      he⟩
  exact ⟨isBounded_of_tildeModels hmodels, fun i => isCoherent_homology_of_tildeModels hmodels i⟩

end Shriek

end Stacks.Duality

end
