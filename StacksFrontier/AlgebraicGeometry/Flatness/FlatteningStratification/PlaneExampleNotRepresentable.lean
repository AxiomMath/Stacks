module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecProduct
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.PlaneExamplePowerSeries
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.MvPowerSeries.Noetherian

/-!
# The flattening example of the affine plane has no universal flattening

Let `k` be a field, `R = k[x, y]` and let `𝓕` be the quasi-coherent module on `Spec R`
associated to `k[x, x⁻¹, y]/(y) = (R/(y))[1/x]`, viewed over `Spec R` through the identity
morphism, as in
`StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.PlaneExample`.  The two
computations of **Stacks 0FJ1** are already available: the flatness functor `F_flat` of `𝓕` is a
singleton on every infinitesimal quotient `R/(x, y)^n`
(`AlgebraicGeometry.PlaneFlatteningExample.flatValue_infinitesimalQuotient_unique`) and is empty
on the formal plane `k[[x, y]]`
(`AlgebraicGeometry.PlaneFlatteningExample.flatValue_formalPlane_isEmpty`).  This file draws the
conclusion the tag states: `F_flat` is not representable, not even by an algebraic space, and so
the universal flattening of `𝓕` does not exist.

## Main definitions

* `AlgebraicGeometry.PlaneFlatteningExample.formalPlaneOver` is the structure morphism
  `Spec k[[x, y]] ⟶ Spec k[x, y]` of the formal plane over the affine plane.

## Main results

* `AlgebraicGeometry.PlaneFlatteningExample.isNoetherianCompleteLocalRing_formalPlane`: the
  formal plane is a Noetherian complete local ring.
* `AlgebraicGeometry.PlaneFlatteningExample.nonempty_flatValue_formalPlane_quotient`: `F_flat`
  is nonempty on `k[[x, y]] ⧸ J` for every ideal `J` containing a power of the maximal ideal.
* `AlgebraicGeometry.PlaneFlatteningExample.not_isAlgebraicSpace_of_objEquiv_flatFunctor`: no
  algebraic space over `Spec k[x, y]` has the values of `F_flat`.
* `AlgebraicGeometry.PlaneFlatteningExample.not_exists_isAlgebraicSpace_iso_flatFunctor`:
  `F_flat` is not representable by an algebraic space.
* `AlgebraicGeometry.PlaneFlatteningExample.not_hasUniversalFlattening`: the universal
  flattening of `𝓕` does not exist.
* `AlgebraicGeometry.PlaneFlatteningExample.flatFunctor_unique_isEmpty_not_representable`:
  **Stacks 0FJ1** in full: `F_flat` is a singleton on every `k[x, y]/(x, y)^n`, empty on
  `k[[x, y]]`, not representable by an algebraic space, and not representable by a scheme.

## Implementation notes

*The obstruction.*  The input that is not formal is the limit property of **Stacks 0AQH**: for an
algebraic space `X` over `S` and a Noetherian complete local `S`-algebra `A` with maximal ideal
`𝔪`, the map `X(A) ⟶ lim_n X(A/𝔪ⁿ)` is bijective.  It is used through
`AlgebraicGeometry.FormalSpace.nonempty_obj_of_forall_nonempty_obj_quotient`, the surjectivity
half read on points.  That form carries the hypothesis that every value of `X` be a subsingleton,
which is what makes the stagewise points compatible; for a functor with the values of `F_flat`
this holds by `AlgebraicGeometry.FlatnessSituation.flatFunctor_obj_subsingleton`.

*Why `k[[x, y]] ⧸ J` and not `k[x, y]/(x, y)ⁿ`.*  The stages of 0AQH are the quotients of the
formal plane, not of the polynomial ring, so the computation has to be transported along
the `k[x, y]`-algebra map `k[x, y]/(x, y)^n ⟶ k[[x, y]] ⧸ J`, which exists because `(x, y)^n` maps
into `𝔪ⁿ ⊆ J`.  Transport is `AlgebraicGeometry.FlatnessSituation.isFlatAfterBaseChange_of_hom`
applied to `AlgebraicGeometry.specOverMap` of that algebra map; no second flatness computation is
performed.  An isomorphism `k[[x, y]]/𝔪ⁿ ≅ k[x, y]/(x, y)ⁿ` is therefore never needed — only the
one-way algebra map.

*The shape of the non-representability statement.*  `AlgebraicGeometry.IsAlgebraicSpace` is a
predicate on presheaves on the big fppf site of `S`, whereas `F_flat` is displayed on the schemes
over `S`; the two are matched by `CategoryTheory.Over.post B.inclusion`, the functor presenting an
object of the site as a scheme over `S`, so that the restriction of `F_flat` to the site is the
composite `(Over.post B.inclusion).op ⋙ F_flat`, universe-lifted.  The statement that no
algebraic space is isomorphic to that composite is `not_exists_isAlgebraicSpace_iso_flatFunctor`;
it is deduced from `not_isAlgebraicSpace_of_objEquiv_flatFunctor`, which asks only for a bijection
of values at each object and no naturality, and is therefore the stronger refutation.  Nothing is
lost by dropping naturality: `CategoryTheory.Functor.representableBy_of_subsingleton` of
`StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.Artinian` is the converse for a
functor with subsingleton values, so for `F_flat` the objectwise condition and representability
agree.

Both ask that the site contain `Spec k[[x, y]]`, which is where the counterexample lives and
without which the restriction of `F_flat` to the site says nothing about the formal plane.  The
statement about the universal flattening needs no such hypothesis: representability there is by a
scheme over `Spec k[x, y]`, and a site containing that scheme together with the two spectra is
produced inside the proof by `AlgebraicGeometry.BigFppfSite.exists_containing`.

*What is not stated.*  The example is a scheme-level
`AlgebraicGeometry.FlatnessSituation`, so the clause refuted is the scheme-level
`AlgebraicGeometry.FlatnessSituation.HasUniversalFlattening` of **Stacks 05P6**.  Its
algebraic-space counterpart `AlgebraicGeometry.Space.FlatnessSituation.HasUniversalFlattening`
of **Stacks 0CWR** is a condition on a flatness situation of algebraic spaces, which this example
is not presented as; `not_exists_isAlgebraicSpace_iso_flatFunctor` is the content of 0FJ1's
parenthesis "even by an algebraic space" stated directly on `F_flat`.

## References

* [Stacks Project, Tag 0FJ1](https://stacks.math.columbia.edu/tag/0FJ1)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
* [Stacks Project, Tag 05P6](https://stacks.math.columbia.edu/tag/05P6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- The functor presenting an object of the big fppf category over `S` as a scheme over `S`
takes a scheme of the site with a chosen morphism to `S` back to that same morphism. -/
private theorem overPost_siteObject (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : Scheme.{u}} (hT : B.Contains T) (b : T ⟶ S) :
    (Over.post B.inclusion).obj (siteObject B S hS hT b) = Over.mk b := rfl

namespace PlaneFlatteningExample

/-- The formal plane `k[[x, y]]` is a Noetherian complete local ring. -/
public theorem isNoetherianCompleteLocalRing_formalPlane (E : PlaneFlatteningExample.{u}) :
    IsNoetherianCompleteLocalRing E.formalPlane :=
  have hN : IsNoetherianRing E.formalPlane := mvPowerSeries_fin_isNoetherianRing E.k 2
  ⟨hN, inferInstance,
    Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_mvPowerSeries E.k 2⟩

/-- The two coordinates generate an ideal inside the maximal ideal of the formal plane: a power
series with zero constant coefficient is not a unit. -/
public theorem span_coords_le_maximalIdeal (E : PlaneFlatteningExample.{u}) :
    Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} : Set E.formalPlane) ≤
      IsLocalRing.maximalIdeal E.formalPlane := by
  rw [Ideal.span_le]
  rintro f (rfl | rfl) <;>
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (by simp [MvPowerSeries.isUnit_iff_constantCoeff])

/-- **The flatness functor is nonempty on every infinitesimal quotient of the formal plane.**
For an ideal `J` of `k[[x, y]]` containing a power `𝔪ⁿ` of the maximal ideal, the quotient
`k[[x, y]] ⧸ J` receives the `k[x, y]`-algebra `k[x, y]/(x, y)^n`, so the singleton value of
`AlgebraicGeometry.PlaneFlatteningExample.flatValue_infinitesimalQuotient_unique` restricts to
it. -/
public theorem nonempty_flatValue_formalPlane_quotient (E : PlaneFlatteningExample.{u})
    (n : ℕ) (J : Ideal E.formalPlane)
    (h : IsLocalRing.maximalIdeal E.formalPlane ^ n ≤ J) :
    Nonempty (E.flatValue (E.formalPlane ⧸ J)) := by
  have hmem : ∀ a ∈ (Ideal.span ({E.x, E.y} : Set E.R)) ^ n,
      algebraMap E.R E.formalPlane a ∈ J := by
    intro a ha
    refine h (Ideal.pow_right_mono E.span_coords_le_maximalIdeal n ?_)
    have hmap : Ideal.map (algebraMap E.R E.formalPlane)
        ((Ideal.span ({E.x, E.y} : Set E.R)) ^ n) =
        Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} : Set E.formalPlane) ^ n := by
      rw [Ideal.map_pow, Ideal.map_span]
      congr 1
      rw [Set.image_insert_eq, Set.image_singleton,
        MvPolynomial.algebraMap_mvPowerSeries_X 0, MvPolynomial.algebraMap_mvPowerSeries_X 1]
    exact hmap ▸ Ideal.mem_map_of_mem _ ha
  let f : E.R ⧸ (Ideal.span ({E.x, E.y} : Set E.R)) ^ n →+* E.formalPlane ⧸ J :=
    Ideal.Quotient.lift _ (algebraMap E.R (E.formalPlane ⧸ J))
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hmem a ha)
  let φ : (E.R ⧸ (Ideal.span ({E.x, E.y} : Set E.R)) ^ n) →ₐ[E.R] (E.formalPlane ⧸ J) :=
    { f with commutes' := fun _ => rfl }
  exact ⟨⟨E.flatnessSituation.isFlatAfterBaseChange_of_hom (specOverMap φ)
    (flatValue_infinitesimalQuotient_unique E n).default.down⟩⟩

/-- The formal plane as a scheme over the affine plane. -/
public abbrev formalPlaneOver (E : PlaneFlatteningExample.{u}) :
    Spec (.of E.formalPlane) ⟶ E.X :=
  Spec.map (CommRingCat.ofHom (algebraMap E.R E.formalPlane))

/-- The structure morphism of a quotient of the formal plane over the affine plane is the
spectrum of its own structure map. -/
public theorem quotientSpec_comp_formalPlaneOver (E : PlaneFlatteningExample.{u})
    (J : Ideal E.formalPlane) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ E.formalPlaneOver =
      Spec.map (CommRingCat.ofHom (algebraMap E.R (E.formalPlane ⧸ J))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- **No algebraic space over `Spec k[x, y]` has the values of `F_flat`.**  Only a bijection of
values at each object of the site is asked for, with no naturality, so this refutes more than
representability.

If `X` had those values it would be a singleton on every `Spec (k[[x, y]] ⧸ J)` and empty on
`Spec k[[x, y]]`, contradicting the limit property of **Stacks 0AQH** for the Noetherian complete
local ring `k[[x, y]]`. -/
public theorem not_isAlgebraicSpace_of_objEquiv_flatFunctor
    (E : PlaneFlatteningExample.{u}) {B : BigFppfSite.{u}} (hS : B.Contains E.X)
    (hformal : B.Contains (Spec (.of E.formalPlane)))
    (X : (BigFppfOver B E.X hS)ᵒᵖ ⥤ Type u)
    (hXval : ∀ T : BigFppfOver B E.X hS,
      X.obj (op T) ≃ E.flatnessSituation.flatFunctor.obj
        (op ((Over.post B.inclusion).obj T))) :
    ¬ IsAlgebraicSpace B E.X hS X := by
  intro hX
  have hsub : ∀ T, Subsingleton (X.obj T) := fun T => Equiv.subsingleton (hXval T.unop)
  have hstage : ∀ (n : ℕ) (J : Ideal E.formalPlane),
      IsLocalRing.maximalIdeal E.formalPlane ^ n ≤ J →
      ∀ hJ : B.Contains (Spec (.of (E.formalPlane ⧸ J))),
        Nonempty (X.obj (op (siteObject B E.X hS hJ
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ E.formalPlaneOver)))) := by
    intro n J hle hJ
    refine Nonempty.map (hXval _).symm ?_
    rw [overPost_siteObject, E.quotientSpec_comp_formalPlaneOver J]
    exact E.nonempty_flatValue_formalPlane_quotient n J hle
  have hpt := FormalSpace.nonempty_obj_of_forall_nonempty_obj_quotient
    E.isNoetherianCompleteLocalRing_formalPlane hformal E.formalPlaneOver X hX hsub hstage
  refine E.flatValue_formalPlane_isEmpty.false ?_
  have hval := hpt.map (hXval _)
  rw [overPost_siteObject] at hval
  exact hval.some

/-- The flatness functor of the example is not representable by an algebraic space (the third
claim of `flatFunctor_unique_isEmpty_not_representable`): no algebraic space over `Spec k[x, y]` is
isomorphic to the restriction of `F_flat` to the big fppf site, provided that site contains the
formal plane. -/
public theorem not_exists_isAlgebraicSpace_iso_flatFunctor (E : PlaneFlatteningExample.{u})
    {B : BigFppfSite.{u}} (hS : B.Contains E.X)
    (hformal : B.Contains (Spec (.of E.formalPlane))) :
    ¬ ∃ X : (BigFppfOver B E.X hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B E.X hS X ∧
        Nonempty (X ≅ (Over.post B.inclusion).op ⋙
          E.flatnessSituation.flatFunctor ⋙ uliftFunctor) := by
  rintro ⟨X, hX, ⟨e⟩⟩
  exact E.not_isAlgebraicSpace_of_objEquiv_flatFunctor hS hformal X
    (fun T => (e.app (op T)).toEquiv.trans Equiv.ulift) hX

/-- The universal flattening of the example module does not exist: its flatness
functor is not representable by a scheme over `Spec k[x, y]` (the last claim of
`flatFunctor_unique_isEmpty_not_representable`).

A representing scheme would, in a big fppf site containing it together with the affine and the
formal plane, present `F_flat` as an algebraic space, which
`AlgebraicGeometry.PlaneFlatteningExample.not_isAlgebraicSpace_of_objEquiv_flatFunctor`
refutes. -/
public theorem not_hasUniversalFlattening (E : PlaneFlatteningExample.{u}) :
    ¬ E.flatnessSituation.HasUniversalFlattening := by
  intro h
  obtain ⟨W, ⟨hW⟩⟩ := h.has_representation
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({E.X, Spec (.of E.formalPlane), W.left} : Set Scheme.{u})
  have hS : B.Contains E.X := hB _ (by simp)
  have hformal : B.Contains (Spec (.of E.formalPlane)) := hB _ (by simp)
  have hWc : B.Contains W.left := hB _ (by simp)
  refine E.not_isAlgebraicSpace_of_objEquiv_flatFunctor hS hformal
    (yoneda.obj (siteObject B E.X hS hWc W.hom)) (fun T => ?_)
    (isAlgebraicSpace_yoneda B E.X hS _)
  exact ((Functor.FullyFaithful.ofFullyFaithful
    (Over.post B.inclusion)).homEquiv).trans hW.homEquiv

/-- **Stacks 0FJ1.** Let `k` be a field, `X = S = Spec k[x, y]` and `𝓕` the quasi-coherent
module associated to `k[x, x⁻¹, y]/(y)`, with flatness functor `F_flat`, and write
`F_flat(A) = F_flat(Spec A)` for a `k[x, y]`-algebra `A`.  Then `F_flat(k[x, y]/(x, y)^n)` is a
singleton for every `n`, while `F_flat(k[[x, y]])` is empty.  Hence `F_flat` is not
representable even by an algebraic space (on any big fppf site containing `Spec k[[x, y]]`, the
restriction of `F_flat` is isomorphic to no algebraic space over `S`), and in particular it is
not representable by a scheme over `S`: the universal flattening of `𝓕` does not exist. -/
@[stacks 0FJ1]
public theorem flatFunctor_unique_isEmpty_not_representable (E : PlaneFlatteningExample.{u}) :
    (∀ n : ℕ, Nonempty (Unique (E.flatValue (E.R ⧸ Ideal.span ({E.x, E.y} : Set E.R) ^ n)))) ∧
    IsEmpty (E.flatValue E.formalPlane) ∧
    (∀ (B : BigFppfSite.{u}) (hS : B.Contains E.X), B.Contains (Spec (.of E.formalPlane)) →
      ¬ ∃ X : (BigFppfOver B E.X hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B E.X hS X ∧
        Nonempty (X ≅ (Over.post B.inclusion).op ⋙
          E.flatnessSituation.flatFunctor ⋙ uliftFunctor)) ∧
    ¬ E.flatnessSituation.flatFunctor.IsRepresentable :=
  ⟨fun n => ⟨flatValue_infinitesimalQuotient_unique E n⟩, E.flatValue_formalPlane_isEmpty,
    fun _ hS hformal => E.not_exists_isAlgebraicSpace_iso_flatFunctor hS hformal,
    E.not_hasUniversalFlattening⟩

end PlaneFlatteningExample

end AlgebraicGeometry

end
