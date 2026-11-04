module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Smooth
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesMorphism
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Jacobson
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus
import StacksCore.Tactic.StacksAttribute

/-!
# Twisting down by a nonsingular closed point

Let `k` be an algebraically closed field, let `X` be a proper curve over `k` and let `ℒ` be an
invertible `𝒪_X`-module with a nonzero global section. This file performs the geometric step of
the induction of [Stacks, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z): it produces a
closed point `x` of `X` at which `𝒪_{X,x}` is regular and at which some global section of `ℒ`
does not vanish, and, writing `i : Z ⟶ X` for the reduced closed subscheme `{x}`, the short
exact sequence

`0 ⟶ ℐ ⊗ ℒ ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0`

together with the two facts about its right-hand term that the induction consumes:
`dim_k H⁰(Z, i^* ℒ) = 1`, and some class of `H⁰(X, ℒ)` has nonzero image in `H⁰(X, i_* i^* ℒ)`.

## Main results

* `AlgebraicGeometry.exists_pointTwistDown`: **the geometric step of [Stacks, Tag 0B8Z]**, with
  no hypothesis beyond the tag's own.

## The source's three sentences, and where each goes

> *Let `U ⊆ X` be the nonempty open subset of nonsingular points studied in Lemma 33.25.8. Let
> `s ∈ H⁰(X, ℒ)` be nonzero. There exists a closed point `x ∈ U` such that `s` does not vanish
> in `x`.*

`U` is `{x | InfinitesimalLifting.SmoothAt f x}`, which is open and dense by [Stacks, Tag 0B8X]
(`AlgebraicGeometry.isOpen_smoothAt_locus` and `AlgebraicGeometry.dense_smoothAt_locus`; `k` is
perfect, being algebraically closed, and `X` is reduced, being a variety). The nonvanishing locus
`X_s` of a nonzero global section of an invertible module on an integral scheme is a nonempty
open (`AlgebraicGeometry.nonempty_nonvanishingLocus_of_ne_zero` and
`Stacks.SheafOfModules.isOpen_nonvanishingLocus`, [Stacks, Tag 01CY]), so `U ∩ X_s` is nonempty,
and it contains a closed point because a scheme of finite type over a field is Jacobson
([Stacks, Tag 02J6], `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`).

> *Let `ℐ` be the ideal sheaf of `i : x → X` as in Lemma 33.43.8. Look at the short exact
> sequence `0 → ℐ ⊗ ℒ → ℒ → i_* i^* ℒ → 0`.*

`ℐ` is `Scheme.IdealSheafData.vanishingIdeal {x}` and its invertibility is items (4) and (5) of
[Stacks, Tag 0B8Y], which over a perfect field are equivalent to smoothness at `x`
(`AlgebraicGeometry.smoothAt_closedPoint_tfae_of_isCurve_of_perfectField`). The sequence is
`Stacks.Divisors.exists_shortExact_invertibleTwist`: the ideal sequence of the closed subscheme
tensored by `ℒ`, with its right-hand term identified by the projection formula of
[Stacks, Tag 0FZE] for a closed immersion.

> *Observe that `H⁰(X, i_*i^*ℒ) = H⁰(x, i^*ℒ)` has dimension `1` as `x` is a `k`-rational point
> (`k` is algebraically closed). Since `s` does not vanish at `x` we conclude that
> `H⁰(X, ℒ) → H⁰(X, i_*i^*ℒ)` is surjective.*

The dimension count is `AlgebraicGeometry.finrank_cohomologyOverField_pullback_eq_one` below. `Z`
is a one-point scheme, so the invertible module `i^* ℒ` on it is trivial
(`Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`) and the count reduces to
`dim_k Γ(Z, 𝒪_Z) = 1`. That is where algebraic closedness is consumed: `Z` is an integral scheme
proper over `k`, so `Γ(Z, 𝒪_Z)` is a domain, finite over `k` by [Stacks, Tag 0BUG] clause (1),
hence a finite integral extension of `k`, hence `k` itself.

The nonvanishing of the image of `s` is
`AlgebraicGeometry.app_top_unit_ne_zero_of_mem_nonvanishingLocus` below: the nonvanishing locus
of a global section pulls back to the nonvanishing locus of its pullback
([Stacks, Tag 0H78], `Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff`), the
pullback of `s` along `i` *is* the image of `s` under the unit `ℒ ⟶ i_* i^* ℒ` read on global
sections, and a section whose nonvanishing locus is nonempty has a nonzero germ. Surjectivity
itself is not asserted here: the induction derives it from a nonzero class and the dimension
count, in `AlgebraicGeometry.finrank_cohomologyOverField_zero_add_one_eq_of_shortExact`.

## Implementation notes

**The conclusion is stated as one existential**, in the shape the induction of
`StacksFrontier/AlgebraicGeometry/Curves/PrescribedLowCohomology.lean` consumes: a closed immersion
`i`, an invertible `ℒ'`, maps `α` and `β`, short exactness of `0 ⟶ ℒ' ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0`, the
dimension count on `Z`, and a class with nonzero image. Nothing is claimed about `ℒ'` beyond
invertibility; it is `ℐ ⊗ ℒ`.

**Four spellings of one category meet here and the crossings are definitional.** The exact sequence
is stated over `SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (X).sheaf))` and the
cohomology over `AlgebraicGeometry.Scheme.Modules`; the two are the same type, by
`Stacks.SchemeCohomology.ringSheaf_ringedSpace`, and the pushforward and pullback functors agree on
the nose (`Stacks.SchemeCohomology.modulePushforward_hom`, `AlgebraicGeometry.pullback_scheme_eq`).
Likewise the invertibility predicate is written at `X.sheaf.obj X.ringCatSheaf.property`, at
`X.presheaf (structureSheafRing X.toRingedSpace).property` and at `Z.presheaf …`, and these are the
same proposition. Instance search does not cross any of them, so every crossing below is an `exact`
or a `have` at the target shape.

**The nonvanishing locus is used in two spellings.** `Stacks.SheafOfModules.nonvanishingLocus`
takes an `L.sections` and `Stacks.Ample.nonvanishingLocus` a `Γ(L, ⊤)`; they are the same set by
`AlgebraicGeometry.nonvanishingLocus_sectionsOfTop_eq`, which is used once, to carry the openness
and nonemptiness of the first to the second, in which [Stacks, Tag 0H78] is stated.

## References

* [Stacks Project, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 02J6](https://stacks.math.columbia.edu/tag/02J6)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- An invertible module in the `SheafOfModules` sense is invertible in the `Stacks` sense. -/
private theorem isInvertible_presheaf_of_isInvertible {X : Scheme.{u}} {L : X.Modules}
    (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L := hL

/-! ### The nonsingular closed point at which a section does not vanish -/

/-- **The source's sentence "there exists a closed point `x ∈ U` such that `s` does not vanish in
`x`".** On a curve over a perfect field, a nonzero global section of an invertible module does not
vanish at some closed point at which the structure morphism is smooth: the smooth locus is open
and dense ([Stacks, Tag 0B8X]), the nonvanishing locus is a nonempty open
([Stacks, Tag 01CY]), their intersection is therefore a nonempty open, and a finite-type
`k`-scheme is Jacobson ([Stacks, Tag 02J6]), so that intersection contains a closed point. -/
public theorem exists_isClosed_smoothAt_mem_nonvanishingLocus [PerfectField k] [IsCurve k f]
    (L : X.Modules) (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    ∃ x : X, IsClosed ({x} : Set X) ∧ InfinitesimalLifting.SmoothAt f x ∧
      x ∈ Stacks.Ample.nonvanishingLocus L s := by
  have _ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have _ := isInvertible_presheaf_of_isInvertible hL
  have hbridge : Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L
      (Stacks.SheafOfModules.sectionsOfTop L s) = Stacks.Ample.nonvanishingLocus L s :=
    nonvanishingLocus_sectionsOfTop_eq L s
  have hVo : IsOpen (Stacks.Ample.nonvanishingLocus L s) := by
    rw [← hbridge]
    exact Stacks.SheafOfModules.isOpen_nonvanishingLocus (X := X.toRingedSpace) L _
  have hVne : (Stacks.Ample.nonvanishingLocus L s).Nonempty :=
    hbridge ▸ nonempty_nonvanishingLocus_of_ne_zero L s hs
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxW, hxc⟩ := nonempty_inter_closedPoints
    ((dense_smoothAt_locus k f).inter_open_nonempty _ hVo hVne)
    (hVo.inter (isOpen_smoothAt_locus f)).isLocallyClosed
  exact ⟨x, hxc, hxW.2, hxW.1⟩

/-! ### The dimension of `H⁰` on the point -/

/-- **The source's sentence "`H⁰(X, i_*i^*ℒ) = H⁰(x, i^*ℒ)` has dimension `1` as `x` is a
`k`-rational point".** For `x` a closed point of a scheme proper and integral over an
algebraically closed field `k`, and `ℒ` invertible, the pullback of `ℒ` to the reduced closed
subscheme `{x}` has a one-dimensional space of sections.

The subscheme `Z` has one point, so the invertible module `i^* ℒ` on it is trivial, and
`dim_k H⁰(Z, 𝒪_Z) = dim_k Γ(Z, 𝒪_Z)`. That ring is a domain, `Z` being integral, and finite over
`k`, `Z` being proper over `k`; a finite integral extension domain over an algebraically closed
field is that field. -/
public theorem finrank_cohomologyOverField_pullback_eq_one [IsAlgClosed k] [IsProper f]
    [IsIntegral X] {x : X} (hx : IsClosed ({x} : Set X)) (L : X.Modules)
    (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    Module.finrank k (cohomologyOverField k
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).subschemeι ≫ f)
      ((Scheme.Modules.pullback
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).subschemeι).obj L) 0)
      = 1 := by
  set C : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
    with hC
  have hrange : Set.range C.subschemeι.base = {x} :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  have hmem (z : C.subscheme) : C.subschemeι.base z = x := by
    rw [← Set.mem_singleton_iff, ← hrange]
    exact Set.mem_range_self z
  have _ : Subsingleton (C.subscheme : Type u) :=
    ⟨fun z z' => (IsClosedImmersion.isClosedEmbedding C.subschemeι).injective
      ((hmem z).trans (hmem z').symm)⟩
  have _ : Stacks.SheafOfModules.IsInvertible C.subscheme.presheaf
      (structureSheafRing C.subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback C.subschemeι).obj L) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι L
      (isInvertible_presheaf_of_isInvertible hL)
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology C.subscheme
    ((Scheme.Modules.pullback C.subschemeι).obj L)
  have e' : (Scheme.Modules.pullback C.subschemeι).obj L ≅
      SheafOfModules.unit C.subscheme.ringCatSheaf := e
  rw [finrank_cohomologyOverField_eq_of_iso k (C.subschemeι ≫ f) e' 0,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  have _ : IrreducibleSpace (C.subscheme : Type u) :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X C
      (by rw [hC, hrange]; exact isIrreducible_singleton)
  have _ : IsReduced C.subscheme :=
    hC ▸ Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  have _ : AlgebraicGeometry.IsIntegral C.subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced C.subscheme
  have _ : IsProper (C.subschemeι ≫ f) := inferInstance
  let : Algebra k Γ(C.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (C.subschemeι ≫ f).appTop).hom.toAlgebra
  have _ : Module.Finite k Γ(C.subscheme, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k
      (C.subschemeι ≫ f)
  have _ : Algebra.IsIntegral k Γ(C.subscheme, ⊤) := Algebra.IsIntegral.of_finite k _
  have hbij : Function.Bijective (algebraMap k Γ(C.subscheme, ⊤)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  rw [← (AlgEquiv.ofBijective (Algebra.ofId k Γ(C.subscheme, ⊤))
    hbij).toLinearEquiv.finrank_eq, Module.finrank_self]

/-! ### The section does not vanish on the point -/

/-- **The source's sentence "`s` does not vanish at `x`", read on `H⁰`.** For `i : Z ⟶ X` a
morphism of schemes and `s` a global section of a module `ℒ` on `X` whose nonvanishing locus
meets the image of `i`, the image of `s` under the unit `ℒ ⟶ i_* i^* ℒ` on global sections is
nonzero.

The image of `s` under the unit, over `⊤`, *is* the pullback of `s`, so the nonvanishing locus of
the one is the preimage of the nonvanishing locus of the other, [Stacks, Tag 0H78]; a section
whose nonvanishing locus is inhabited has a nonzero germ there. -/
public theorem app_top_unit_ne_zero_of_mem_nonvanishingLocus {Z : Scheme.{u}} (i : Z ⟶ X)
    (L : X.Modules) (s : Γ(L, ⊤)) (z : Z)
    (hz : i.base z ∈ Stacks.Ample.nonvanishingLocus L s) :
    (Scheme.Modules.Hom.app
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app L) ⊤) s ≠ 0 := by
  have hne := Stacks.Ample.Γgerm_ne_zero_of_mem_nonvanishingLocus
    ((Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff i L s z).mpr hz)
  intro hc
  exact hne (by
    rw [show Stacks.NonvanishingPullback.pullbackGlobalSection i L s = 0 from hc, map_zero])

/-! ### The geometric step of Tag 0B8Z -/

/-- **The geometric step of the induction of [Stacks, Tag 0B8Z]**, at the tag's own hypotheses:
twisting down by a nonsingular `k`-rational closed point at which a global section does not
vanish.

Let `k` be algebraically closed, let `X` be a proper curve over `k` and let `ℒ` be invertible
with `dim_k H⁰(X, ℒ) > 0`. Then there are a closed point `i : Z ⟶ X` of `X`, an invertible `ℒ'`
and a short exact sequence `0 ⟶ ℒ' ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0` with `dim_k H⁰(Z, i^* ℒ) = 1` and with
some class of `H⁰(X, ℒ)` of nonzero image in `H⁰(X, i_* i^* ℒ)`.

`ℒ'` is `ℐ ⊗ ℒ` for `ℐ` the ideal sheaf of a point of the smooth locus ([Stacks, Tag 0B8X]) at
which a chosen nonzero section does not vanish; invertibility of `ℐ` is items (4) and (5) of
[Stacks, Tag 0B8Y], and `dim_k H⁰(Z, i^* ℒ) = 1` is the `k`-rationality of that point, which is
where algebraic closedness of `k` is used. -/
public theorem exists_pointTwistDown [IsAlgClosed k] [IsProper f] [IsCurve k f] (L : X.Modules)
    (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hpos : 0 < Module.finrank k (cohomologyOverField k f L 0)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (L' : X.Modules) (α : L' ⟶ L)
      (β : L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L))
      (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact ∧
        SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L' ∧
        Module.finrank k
            (cohomologyOverField k (i ≫ f) ((Scheme.Modules.pullback i).obj L) 0) = 1 ∧
        ∃ a, cohomologyOverFieldMap k f β 0 a ≠ 0 := by
  have : Nontrivial (cohomologyOverField k f L 0 : Type u) := Module.nontrivial_of_finrank_pos hpos
  have _ : Nontrivial Γ(L, ⊤) :=
    (cohomologyOverFieldZeroEquivSections k f L).symm.nontrivial
  obtain ⟨s, hs⟩ := exists_ne (0 : Γ(L, ⊤))
  obtain ⟨x, hxc, hxsm, hxs⟩ :=
    exists_isClosed_smoothAt_mem_nonvanishingLocus k f L hL s hs
  have hCeff : Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hxc⟩ : Closeds X)) :=
    (smoothAt_closedPoint_tfae_of_isCurve_of_perfectField k f hxc
      (InfinitesimalLifting.SmoothAt f x) (by simp)
      (Stacks.Divisors.IsEffectiveCartierDivisor
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hxc⟩ : Closeds X))) (by simp)).mp hxsm
  set C : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hxc⟩ : Closeds X)
    with hC
  obtain ⟨w, hSE⟩ := Stacks.Divisors.exists_shortExact_invertibleTwist C L hL
  obtain ⟨z, hzx⟩ : x ∈ Set.range C.subschemeι.base := by
    rw [hC, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact Set.mem_singleton x
  refine ⟨C.subscheme, C.subschemeι, inferInstance,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj L).obj
      (Stacks.Divisors.idealSheafOfModules C),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj L).map
      (Stacks.Divisors.idealInclusion C) ≫
      (Stacks.Divisors.tensorUnitIso L).hom,
    (modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app L, w, hSE,
    ?_, finrank_cohomologyOverField_pullback_eq_one k f hxc L hL,
    (cohomologyOverFieldZeroEquivSections k f L).symm s, ?_⟩
  · have _ : Stacks.SheafOfModules.IsInvertible X.presheaf
        (structureSheafRing X.toRingedSpace).property
        (Stacks.Divisors.idealSheafOfModules C) := hCeff
    have _ := isInvertible_presheaf_of_isInvertible hL
    exact Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.Divisors.idealSheafOfModules C) L
  · intro hc
    refine app_top_unit_ne_zero_of_mem_nonvanishingLocus C.subschemeι L s z (hzx ▸ hxs) ?_
    have key := cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f
      ((modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app L)
      ((cohomologyOverFieldZeroEquivSections k f L).symm s)
    exact ((congrArg (fun t => (Scheme.Modules.Hom.app
            ((modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app L) ⊤) t)
          (Equiv.apply_symm_apply (cohomologyOverFieldZeroEquivSections k f L) s).symm).trans
        (key.symm.trans
          ((congrArg (cohomologyOverFieldZeroEquivSections k f
              ((Scheme.Modules.pushforward C.subschemeι).obj
                ((Scheme.Modules.pullback C.subschemeι).obj L))) hc).trans
            (cohomologyOverFieldZeroEquivSections_zero k f _))))

end AlgebraicGeometry

end
