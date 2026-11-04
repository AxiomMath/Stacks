module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions

/-!
# Evaluation of rational functions on a chart meeting every dense open subspace

Let `X` be an algebraic space over a scheme `S` and let `W` be an object of the big fppf site
with a morphism `m : W → X` which factors through *every* dense open subspace of `X`. Then a
rational function on `X` can be pulled back along `m`: a dense-open representative is a
morphism `V → 𝔸¹` on a dense open subspace `V`, the morphism `m` factors through `V`, and
pulling the coordinate back gives a global section of `W`. The factorization is unique, the
inclusion of an open subspace being a monomorphism, so this is well defined on representatives;
two equivalent representatives agree after restriction to a common dense open subspace, through
which `m` also factors, so the value only depends on the rational function. The resulting map
is a ring homomorphism, because the ring operations on rational functions are computed by the
pointwise operations on the coordinates of representatives defined on one dense open subspace.

## Main definitions

* `AlgebraicGeometry.Space.FactorsThroughDenseOpens` is the hypothesis on `m`: it factors
  through every dense open subspace.
* `AlgebraicGeometry.Space.denseOpenLift` is the chosen factorization through a given dense
  open subspace.
* `AlgebraicGeometry.Space.evalSitePartial` is the value of a dense-open representative, and
  `AlgebraicGeometry.Space.evalSiteRingHom` is the induced ring homomorphism from the rational
  functions of Tag 0EMP to the global sections of `W`.

## Main results

* `AlgebraicGeometry.Space.evalSitePartial_eq` pins the value down: it is computed by *any*
  factorization of `m` through the domain of the representative.
* `AlgebraicGeometry.Space.evalSiteRingHom_eq` is the same statement for the ring
  homomorphism.

## Implementation notes

The hypothesis is phrased as a factorization property rather than as a condition on points,
so that a user may supply it either from Tag 03IE — a morphism factors through an open
subspace exactly when its point set does, which is
`AlgebraicGeometry.factorsThrough_openSubspace_iff_points` — or by hand.

`AlgebraicGeometry.Space.evalRingHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/GenericRationalFunctions.lean` is the case of a
field-valued representative of the generic point of an integral algebraic space, where the
factorization property holds because the generic point lies in every dense open subspace.
That evaluation lands in a field; the point of the present generality is that `W` may be the
spectrum of a ring with zerodivisors, which is what the embedding of the function field into
a total ring of fractions needs.

## References

* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 0EMM](https://stacks.math.columbia.edu/tag/0EMM)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- A morphism from a representable presheaf into `X` *factors through the dense opens* when it
factors through the inclusion of every dense open subspace of `X`. -/
def FactorsThroughDenseOpens (W : BigFppfOver B S hS) (m : yoneda.obj W ⟶ X) : Prop :=
  ∀ (U : Subfunctor X), IsDenseOpenSubspace B S hS hX U →
    ∃ j : yoneda.obj W ⟶ U.toFunctor, j ≫ U.ι = m

variable {W : BigFppfOver B S hS} {m : yoneda.obj W ⟶ X}

/-- The chosen factorization through a dense open subspace, together with the factorization
identity. -/
noncomputable def denseOpenLift (hm : FactorsThroughDenseOpens B S hS hX W m)
    {U : Subfunctor X} (hU : IsDenseOpenSubspace B S hS hX U) :
    {j : yoneda.obj W ⟶ U.toFunctor // j ≫ U.ι = m} :=
  Classical.indefiniteDescription _ (hm U hU)

/-- The factorization through a dense open subspace is unique, the inclusion of an open
subspace being a monomorphism. -/
theorem denseOpenLift_unique (hm : FactorsThroughDenseOpens B S hS hX W m)
    {U : Subfunctor X} (hU : IsDenseOpenSubspace B S hS hX U)
    (j : yoneda.obj W ⟶ U.toFunctor) (hj : j ≫ U.ι = m) :
    j = (denseOpenLift B S hS hX hm hU).1 := by
  have : Mono U.ι := mono_of_isOpenImmersion B S hS U.ι hU.1.2
  exact (cancel_mono U.ι).1 (hj.trans (denseOpenLift B S hS hX hm hU).2.symm)

/-! ### The value of a representative -/

/-- The value on the chart of a dense-open representative of a rational function: the
coordinate of the representative pulled back along the factorization of `m` through its
domain. -/
noncomputable def evalSitePartial (hm : FactorsThroughDenseOpens B S hS hX W m)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS)) :
    Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
  affineLineCoordinate B S hS (Opposite.op W)
    (yonedaEquiv ((denseOpenLift B S hS hX hm f.dense_open_domain).1 ≫ f.hom))

/-- The value on the chart is computed by any factorization of `m` through the domain of the
representative. -/
theorem evalSitePartial_eq (hm : FactorsThroughDenseOpens B S hS hX W m)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS))
    (j : yoneda.obj W ⟶ f.domain.toFunctor) (hj : j ≫ f.domain.ι = m) :
    evalSitePartial B S hS hX hm f =
      affineLineCoordinate B S hS (Opposite.op W) (yonedaEquiv (j ≫ f.hom)) := by
  rw [denseOpenLift_unique B S hS hX hm f.dense_open_domain j hj]
  rfl

/-- Equivalent dense-open representatives have the same value on the chart. -/
theorem evalSitePartial_congr (hm : FactorsThroughDenseOpens B S hS hX W m)
    {f g : PartialMap B S hS hX (affineLineFunctor B S hS)}
    (h : PartialMap.Equivalent B S hS f g) :
    evalSitePartial B S hS hX hm f = evalSitePartial B S hS hX hm g := by
  obtain ⟨V, hV, hVf, hVg, hcomp⟩ := h
  have hjV := (denseOpenLift B S hS hX hm hV).2
  rw [evalSitePartial_eq B S hS hX hm f
      ((denseOpenLift B S hS hX hm hV).1 ≫ Subfunctor.homOfLe hVf)
      (by rw [Category.assoc, Subfunctor.homOfLe_ι]; exact hjV),
    evalSitePartial_eq B S hS hX hm g
      ((denseOpenLift B S hS hX hm hV).1 ≫ Subfunctor.homOfLe hVg)
      (by rw [Category.assoc, Subfunctor.homOfLe_ι]; exact hjV),
    Category.assoc, Category.assoc, hcomp]

/-- The value of a rational function on the chart. -/
noncomputable def evalSiteFun (hm : FactorsThroughDenseOpens B S hS hX W m) :
    rationalFunctions B S hS hX → Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
  Quotient.lift (evalSitePartial B S hS hX hm)
    (fun _ _ h => evalSitePartial_congr B S hS hX hm h)

/-- Evaluation on the chart of the rational function represented by `f` is the evaluation of
`f` itself. -/
@[simp]
theorem evalSiteFun_toRationalMap (hm : FactorsThroughDenseOpens B S hS hX W m)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS)) :
    evalSiteFun B S hS hX hm (f.toRationalMap B S hS) =
      evalSitePartial B S hS hX hm f := rfl

/-! ### Evaluation on the chart is a ring homomorphism -/

/-- Restricting a dense-open representative to a smaller dense open subspace does not change
the rational function it represents. -/
theorem toRationalMap_restrict {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : PartialMap B S hS hX Y) {V : Subfunctor X}
    (hV : IsDenseOpenSubspace B S hS hX V) (hVf : V ≤ f.domain) :
    PartialMap.toRationalMap B S hS
        (⟨V, hV, Subfunctor.homOfLe hVf ≫ f.hom⟩ : PartialMap B S hS hX Y) =
      f.toRationalMap B S hS :=
  (PartialMap.toRationalMap_eq_iff B S hS).2
    ⟨V, hV, le_rfl, hVf, by
      rw [show Subfunctor.homOfLe (le_refl V) = 𝟙 V.toFunctor from rfl, Category.id_comp]⟩

/-- Stacks 0EMP, the clause for addition: a representative of the sum on a dense open
subspace, with the pointwise coordinate identity. -/
theorem exists_add_rep (U : Subfunctor X) (hU : IsDenseOpenSubspace B S hS hX U)
    (f g : U.toFunctor ⟶ affineLineFunctor B S hS) :
    ∃ a : U.toFunctor ⟶ affineLineFunctor B S hS,
      (∀ T x, affineLineCoordinate B S hS T (a.app T x) =
        affineLineCoordinate B S hS T (f.app T x) +
          affineLineCoordinate B S hS T (g.app T x)) ∧
      PartialMap.toRationalMap B S hS
          (⟨U, hU, a⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) =
        PartialMap.toRationalMap B S hS
            (⟨U, hU, f⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) +
          PartialMap.toRationalMap B S hS
            (⟨U, hU, g⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) := by
  obtain ⟨a, m, ha, hm, haR, hmR⟩ := (rationalFunctionsRing B S hS hX).choose_spec.1 U hU f g
  exact ⟨a, ha, haR⟩

/-- Stacks 0EMP, the clause for multiplication. -/
theorem exists_mul_rep (U : Subfunctor X) (hU : IsDenseOpenSubspace B S hS hX U)
    (f g : U.toFunctor ⟶ affineLineFunctor B S hS) :
    ∃ n : U.toFunctor ⟶ affineLineFunctor B S hS,
      (∀ T x, affineLineCoordinate B S hS T (n.app T x) =
        affineLineCoordinate B S hS T (f.app T x) *
          affineLineCoordinate B S hS T (g.app T x)) ∧
      PartialMap.toRationalMap B S hS
          (⟨U, hU, n⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) =
        PartialMap.toRationalMap B S hS
            (⟨U, hU, f⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) *
          PartialMap.toRationalMap B S hS
            (⟨U, hU, g⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) := by
  obtain ⟨a, n, ha, hn, haR, hnR⟩ := (rationalFunctionsRing B S hS hX).choose_spec.1 U hU f g
  exact ⟨n, hn, hnR⟩

/-- Stacks 0EMP, the clauses for zero and one. -/
theorem exists_zero_one_rep (U : Subfunctor X)
    (hU : IsDenseOpenSubspace B S hS hX U) :
    ∃ z o : U.toFunctor ⟶ affineLineFunctor B S hS,
      (∀ T x, affineLineCoordinate B S hS T (z.app T x) = 0) ∧
      (∀ T x, affineLineCoordinate B S hS T (o.app T x) = 1) ∧
      PartialMap.toRationalMap B S hS
          (⟨U, hU, z⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) = 0 ∧
      PartialMap.toRationalMap B S hS
          (⟨U, hU, o⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) = 1 :=
  (rationalFunctionsRing B S hS hX).choose_spec.2.1 U hU

/-- Evaluation of a representative on a fixed dense open subspace is the coordinate of its
value at the chosen factorization. -/
private theorem evalSitePartial_app (hm : FactorsThroughDenseOpens B S hS hX W m)
    {V : Subfunctor X} (hV : IsDenseOpenSubspace B S hS hX V)
    (ν : V.toFunctor ⟶ affineLineFunctor B S hS) :
    evalSitePartial B S hS hX hm
        (⟨V, hV, ν⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) =
      affineLineCoordinate B S hS (Opposite.op W)
        (ν.app (Opposite.op W) (yonedaEquiv (denseOpenLift B S hS hX hm hV).1)) := by
  rw [evalSitePartial_eq B S hS hX hm (⟨V, hV, ν⟩ : PartialMap B S hS hX _)
      (denseOpenLift B S hS hX hm hV).1 (denseOpenLift B S hS hX hm hV).2, yonedaEquiv_comp]

/-- Two rational functions are represented by dense-open representatives with a common domain. -/
private theorem exists_common_rep (x y : rationalFunctions B S hS hX) :
    ∃ (V : Subfunctor X) (hV : IsDenseOpenSubspace B S hS hX V)
      (f g : V.toFunctor ⟶ affineLineFunctor B S hS),
      PartialMap.toRationalMap B S hS
          (⟨V, hV, f⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) = x ∧
        PartialMap.toRationalMap B S hS
          (⟨V, hV, g⟩ : PartialMap B S hS hX (affineLineFunctor B S hS)) = y := by
  obtain ⟨f, hf⟩ := RationalMap.exists_rep B S hS x
  obtain ⟨g, hg⟩ := RationalMap.exists_rep B S hS y
  obtain ⟨V, hV, hVf, hVg⟩ :=
    exists_isDenseOpenSubspace_le B S hS hX f.dense_open_domain g.dense_open_domain
  exact ⟨V, hV, Subfunctor.homOfLe hVf ≫ f.hom, Subfunctor.homOfLe hVg ≫ g.hom,
    (toRationalMap_restrict B S hS hX f hV hVf).trans hf,
    (toRationalMap_restrict B S hS hX g hV hVg).trans hg⟩

/-- Evaluation on the chart respects addition. -/
theorem evalSiteFun_add (hm : FactorsThroughDenseOpens B S hS hX W m)
    (x y : rationalFunctions B S hS hX) :
    evalSiteFun B S hS hX hm (x + y) =
      evalSiteFun B S hS hX hm x + evalSiteFun B S hS hX hm y := by
  obtain ⟨V, hV, f, g, hf, hg⟩ := exists_common_rep B S hS hX x y
  obtain ⟨a, ha, haR⟩ := exists_add_rep B S hS hX V hV f g
  rw [← hf, ← hg, ← haR, evalSiteFun_toRationalMap, evalSiteFun_toRationalMap,
    evalSiteFun_toRationalMap, evalSitePartial_app, evalSitePartial_app, evalSitePartial_app, ha]

/-- Evaluation on the chart respects multiplication. -/
theorem evalSiteFun_mul (hm : FactorsThroughDenseOpens B S hS hX W m)
    (x y : rationalFunctions B S hS hX) :
    evalSiteFun B S hS hX hm (x * y) =
      evalSiteFun B S hS hX hm x * evalSiteFun B S hS hX hm y := by
  obtain ⟨V, hV, f, g, hf, hg⟩ := exists_common_rep B S hS hX x y
  obtain ⟨n, hn, hnR⟩ := exists_mul_rep B S hS hX V hV f g
  rw [← hf, ← hg, ← hnR, evalSiteFun_toRationalMap, evalSiteFun_toRationalMap,
    evalSiteFun_toRationalMap, evalSitePartial_app, evalSitePartial_app, evalSitePartial_app, hn]

/-- Evaluation on the chart sends zero to zero. -/
theorem evalSiteFun_zero (hm : FactorsThroughDenseOpens B S hS hX W m) :
    evalSiteFun B S hS hX hm 0 = 0 := by
  obtain ⟨z, o, hz, ho, hzR, hoR⟩ :=
    exists_zero_one_rep B S hS hX ⊤ (isDenseOpenSubspace_top B S hS hX)
  rw [← hzR, evalSiteFun_toRationalMap, evalSitePartial_app, hz]

/-- Evaluation on the chart sends one to one. -/
theorem evalSiteFun_one (hm : FactorsThroughDenseOpens B S hS hX W m) :
    evalSiteFun B S hS hX hm 1 = 1 := by
  obtain ⟨z, o, hz, ho, hzR, hoR⟩ :=
    exists_zero_one_rep B S hS hX ⊤ (isDenseOpenSubspace_top B S hS hX)
  rw [← hoR, evalSiteFun_toRationalMap, evalSitePartial_app, ho]

/-- Evaluation on a chart meeting every dense open subspace, as a ring homomorphism from the
rational functions of `X` to the global sections of the chart. -/
noncomputable def evalSiteRingHom (hm : FactorsThroughDenseOpens B S hS hX W m) :
    rationalFunctions B S hS hX →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) where
  toFun := evalSiteFun B S hS hX hm
  map_one' := evalSiteFun_one B S hS hX hm
  map_mul' := evalSiteFun_mul B S hS hX hm
  map_zero' := evalSiteFun_zero B S hS hX hm
  map_add' := evalSiteFun_add B S hS hX hm

/-- The ring homomorphism `evalSiteRingHom` is the function `evalSiteFun`. -/
@[simp]
theorem evalSiteRingHom_apply (hm : FactorsThroughDenseOpens B S hS hX W m)
    (x : rationalFunctions B S hS hX) :
    evalSiteRingHom B S hS hX hm x = evalSiteFun B S hS hX hm x := rfl

/-- The ring homomorphism is computed on a representative by any factorization of `m` through
the domain of that representative. -/
theorem evalSiteRingHom_eq (hm : FactorsThroughDenseOpens B S hS hX W m)
    (f : PartialMap B S hS hX (affineLineFunctor B S hS))
    (j : yoneda.obj W ⟶ f.domain.toFunctor) (hj : j ≫ f.domain.ι = m) :
    evalSiteRingHom B S hS hX hm (f.toRationalMap B S hS) =
      affineLineCoordinate B S hS (Opposite.op W) (yonedaEquiv (j ≫ f.hom)) :=
  evalSitePartial_eq B S hS hX hm f j hj

end AlgebraicGeometry.Space

end
