module

public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SeparablyClosedExtension
public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeHolds
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale cohomology does not change under extension of separably closed base field

Let `K/k` be an extension of separably closed fields, let `X` be a quasi-compact and
quasi-separated scheme over `k`, with `X_K = X ×_k Spec K` and projection `p : X_K ⟶ X`, and let
`E ∈ D⁺(X_étale)` have cohomology sheaves whose stalks are torsion of orders invertible in `k`.
[Stacks, Tag 0F0B] asserts that

1. the maps `H^q_ét(X, E) ⟶ H^q_ét(X_K, E|_{X_K})` are isomorphisms, and
2. `E ⟶ Rp_*(E|_{X_K})` is an isomorphism.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomology_pullback_of_isSepClosed` — part (1).
  `H^q_ét(X, E)` is the group of morphisms in `D⁺(X_étale)` out of the constant sheaf `ℤ` placed
  in degree `-q`, and the map is pullback along `p` followed by the identification of the
  pullback of `ℤ_X` with `ℤ_{X_K}`.
* `Stacks.EtaleCohomology.isIso_derivedUnit_baseChange_of_isSepClosed` — part (2): the unit
  `E ⟶ Rp_*p⁻¹E` of the derived adjunction of `p` is an isomorphism. The proof uses part (1) only
  for affine schemes étale over `X`, so it holds for every scheme `X` over `k`.

## The proof

Both parts are `Stacks.EtaleCohomology.bijective_etaleCohomology_restriction_of_isSepClosed` and
`Stacks.EtaleCohomology.isIso_derivedUnit_app_of_isSepClosed`, which carry out the source's
argument from [Stacks, Tag 0F09] (`SmoothLimitBaseChange`), applied to
`Stacks.EtaleCohomology.smoothLimitBaseChange_holds`, which proves Tag 0F09 from the smooth base
change theorem [Stacks, Theorem 0EYU].

## References

* [Stacks Project, Tag 0F0B](https://stacks.math.columbia.edu/tag/0F0B)
* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- The proof runs through the base change map `smallEtaleDerivedBaseChangeAb`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/BaseChangeCondition.lean`,
-- line 220),
-- which the base constructs under the standard model; that fixes the model here.
attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 0F0B] (1).** Let `K/k` be an extension of separably closed fields, `X` a
quasi-compact and quasi-separated scheme over `k`, `p : X_K ⟶ X` its base change to `K` and `E` in
`D⁺(X_étale)` whose cohomology sheaves have stalks which are torsion of orders invertible in `k`.
Then for every `q` the restriction map `H^q_ét(X, E) ⟶ H^q_ét(X_K, E|_{X_K})` is bijective. Here
`H^q_ét(X, E)` is the group of morphisms in `D⁺(X_étale)` from the constant sheaf `ℤ` placed in
degree `-q` to `E`, and restriction is the derived pullback along `p` followed by the
identification of the pullback of `ℤ_X` with `ℤ_{X_K}`. -/
@[stacks 0F0B "(1): H^q(X, E) ⟶ H^q(X_K, E|_{X_K}) is an isomorphism for K/k separably closed",
  sga "4 XII 5.4" "special case",
  sga "4 XVI 1.6" "Abelian L-torsion clause",
  sga "4½ Arcata 5.3.3" "special case",
  sga "4½ Th_finitude 3.9" "more general"]
theorem bijective_etaleCohomology_pullback_of_isSepClosed
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k] [IsSepClosed K]
    {X XK : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (p : XK ⟶ X) (fK : XK ⟶ Spec (.of K))
    (sq : IsPullback p fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (hE : ∀ q : ℤ, HasTorsionOrdersInvertibleOn (Spec (.of k))
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) q).obj E))
    (q : ℤ) :
    Function.Bijective
      (fun φ : (DerivedCategory.Plus.singleFunctor _ (-q)).obj (constantZ X) ⟶ E ↦
        (singleConstantZPullbackIso p (-q)).hom ≫
          (smallEtalePullbackAb p).rightDerivedFunctorPlus.map φ) :=
  bijective_etaleCohomology_restriction_of_isSepClosed smoothLimitBaseChange_holds f p fK sq E hE q

/-- **[Stacks, Tag 0F0B] (2).** Let `K/k` be an extension of separably closed fields, `X` a scheme
over `k`, `p : X_K ⟶ X` its base change to `K` and `E` in `D⁺(X_étale)` whose cohomology sheaves
have stalks which are torsion of orders invertible in `k`. Then `E ⟶ Rp_*(E|_{X_K})`, the unit of
the derived adjunction `p⁻¹ ⊣ Rp_*` at `E`, is an isomorphism. The source assumes `X`
quasi-compact and quasi-separated; the statement holds without it. -/
@[stacks 0F0B "(2): E ⟶ R(X_K → X)_* E|_{X_K} is an isomorphism for K/k separably closed",
  sga "4 XVI 1.6" "partial"]
theorem isIso_derivedUnit_baseChange_of_isSepClosed
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosed k] [IsSepClosed K]
    {X XK : Scheme.{u}} (f : X ⟶ Spec (.of k)) (p : XK ⟶ X) (fK : XK ⟶ Spec (.of K))
    (sq : IsPullback p fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1}))
    (hE : ∀ q : ℤ, HasTorsionOrdersInvertibleOn (Spec (.of k))
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) q).obj E)) :
    IsIso ((smallEtaleAdjunctionAb p).rightDerivedFunctorPlus.unit.app E) :=
  isIso_derivedUnit_app_of_isSepClosed smoothLimitBaseChange_holds f p fK sq E hE

end Stacks.EtaleCohomology

end
