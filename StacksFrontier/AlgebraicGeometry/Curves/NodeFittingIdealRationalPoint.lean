module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodeResidueFieldSeparable
public import StacksFrontier.RingTheory.PresentationCentred

/-!
# The Fitting-ideal criterion for a node at a rational point

Let `k` be a field, let `f : X ⟶ Spec k` be locally of finite type and let `x` be a closed point
of `X` whose residue field is `k` itself. Then the stalk at `x` of the first Fitting ideal sheaf
of `Ω_{X/k}` is the maximal ideal of `𝒪_{X,x}` exactly when `𝒪_{X,x}` carries a nodal quadratic
relation on its cotangent space, and consequently conditions (2) and (4) of Stacks Tag 0C4D are
equivalent at `x`.

This removes the chart and the presentation from
`Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation`: the point being
rational is exactly what is needed to build an affine chart presented by generators vanishing at
the point.

## Main results

* `Stacks.Curves.exists_sub_algebraMap_mem_primeIdealOf` — at a point whose residue field is the
  base field, every section on an affine chart agrees, at the point, with a section pulled back
  from the base.
* `Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation_of_rational` —
  the Fitting-ideal condition of Tag 0C4D is the nodal quadratic relation on `𝒪_{X,x}`, with no
  hypothesis beyond closedness of `x` and rationality of its residue field.
* `Stacks.Curves.isNodalAlgebra_stalk_iff_of_rational` — conditions (2) and (4) of Tag 0C4D are
  equivalent at a rational closed point.
* `Stacks.Curves.isNode_tfae_of_rational` — all six conditions of Tag 0C4D are equivalent at a
  rational closed point, with no further hypothesis.

## Implementation notes

The chart is any affine open around `x`, taken over `V = ⊤` on `Spec k`; the sections there are
a finitely presented algebra over `Γ(Spec k, ⊤)` because that ring is a field, hence Noetherian,
and the morphism is locally of finite type. The presentation centred at the point is
`Algebra.Presentation.exists_centred`, whose hypothesis — every section is congruent, modulo the
prime of `x`, to one pulled back from the base — is rationality of `κ(x)` read through the
localization: the prime of `x` in the chart is the contraction of the maximal ideal of
`𝒪_{X,x}`, and the composite `Γ(Spec k, ⊤) → Γ(X, U) → 𝒪_{X,x}` is the germ of the structure
morphism because `f.appLE ⊤ U` is `f.appTop` followed by a restriction.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C4C](https://stacks.math.columbia.edu/tag/0C4C)
-/

@[expose] public section

open CategoryTheory Algebra MvPolynomial IsLocalRing AlgebraicGeometry

namespace Stacks.Curves

universe u

/-- **A rational point is cut out by sections pulled back from the base.** If every element of
`κ(x)` is the residue of an element of `k`, then every section on an affine open `U ∋ x` agrees
modulo the prime of `x` with a section pulled back from `Spec k`. -/
theorem exists_sub_algebraMap_mem_primeIdealOf
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (x : X)
    (hrat : Function.Surjective ((X.residue x).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom))
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U)
    (hUV : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens)) :
    letI := Stacks.Smooth.algebraAppLE f hUV
    ∀ a : Γ(X, U), ∃ r : Γ(Spec (CommRingCat.of k), ⊤),
      a - algebraMap Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) r ∈
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  let := Stacks.Smooth.algebraAppLE f hUV
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  -- the germ of a section pulled back from the base is the structure map of the stalk
  have hgermcat : f.appLE (⊤ : (Spec (CommRingCat.of k)).Opens) U hUV ≫
      X.presheaf.germ U x hxU = f.appTop ≫ X.presheaf.germ ⊤ x (by simp) := by
    rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res']
    rfl
  have hgerm : ∀ r : Γ(Spec (CommRingCat.of k), ⊤),
      (X.presheaf.germ U x hxU).hom (algebraMap Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) r) =
        (f.appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom r := fun r =>
    congrArg (fun φ : Γ(Spec (CommRingCat.of k), ⊤) ⟶ X.presheaf.stalk x => φ.hom r) hgermcat
  intro a
  obtain ⟨c, hc⟩ := hrat ((X.residue x).hom ((X.presheaf.germ U x hxU).hom a))
  have hc' : IsLocalRing.residue (X.presheaf.stalk x)
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom c) =
      IsLocalRing.residue (X.presheaf.stalk x) ((X.presheaf.germ U x hxU).hom a) := hc
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c, ?_⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal, ← IsLocalRing.residue_eq_zero_iff]
  have halg : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hxU).hom :=
    TopCat.Presheaf.stalk_open_algebraMap X.presheaf (⟨x, hxU⟩ : U)
  rw [halg, map_sub, hgerm, map_sub, sub_eq_zero]
  exact hc'.symm

/-- **The Fitting-ideal condition of Tag 0C4D at a rational closed point is the nodal quadratic
relation.** For `f : X ⟶ Spec k` locally of finite type and `x` a closed point whose residue
field is `k`, the stalk at `x` of the first Fitting ideal sheaf of `Ω_{X/k}` is the maximal ideal
of `𝒪_{X,x}` exactly when `𝒪_{X,x}` carries a nodal quadratic relation on its cotangent
space. -/
theorem stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation_of_rational
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X))
    (hrat : Function.Surjective ((X.residue x).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom)) :
    IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f) (1 : ℤ)) x =
        maximalIdeal (X.presheaf.stalk x) ↔
      HasNodalQuadraticRelation (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have hV : IsAffineOpen (⊤ : (Spec (CommRingCat.of k)).Opens) := isAffineOpen_top _
  have hUV : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := le_top
  let := Stacks.Smooth.algebraAppLE f hUV
  let e : Γ(Spec (CommRingCat.of k), ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
    isNoetherianRing_of_ringEquiv k e.symm
  have := finitePresentation_appLE f hU hV hUV
  obtain ⟨n, m, P, hvP⟩ := Algebra.Presentation.exists_centred
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
    (exists_sub_algebraMap_mem_primeIdealOf k f x hrat hU hxU hUV)
  exact stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation f x ⟨U, hU⟩ hxU hx
    hV hUV k e P hvP

/-- **Conditions (2) and (4) of Tag 0C4D are equivalent at a rational closed point.** The local
ring at a closed point whose residue field is the base field is a nodal `k`-algebra exactly when
its residue field is separable over `k`, it is reduced, and the stalk at `x` of the first Fitting
ideal sheaf of `Ω_{X/k}` is its maximal ideal. -/
theorem isNodalAlgebra_stalk_iff_of_rational
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X))
    (hrat : Function.Surjective ((X.residue x).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom))
    (k₀ : Type u) [Field k₀] [Algebra k₀ (X.presheaf.stalk x)] :
    IsNodalAlgebra k₀ (X.presheaf.stalk x) ↔
      Algebra.IsSeparableExtension k₀ (ResidueField (X.presheaf.stalk x)) ∧
        IsReduced (X.presheaf.stalk x) ∧
          IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f) (1 : ℤ)) x =
            maximalIdeal (X.presheaf.stalk x) := by
  have key := stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation_of_rational k f x
    hx hrat
  exact ⟨fun h => ⟨h.1, h.2.1, key.2 h.2.2⟩, fun h => ⟨h.1, h.2.1, key.1 h.2.2⟩⟩

/-- **All six conditions of Stacks Tag 0C4D are equivalent at a rational closed point.**

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`x` be a closed point of `X` whose residue field is `k` itself — the hypothesis `hrat` says that
the structure map `k → κ(x)` is surjective.  Then the six conditions of the tag are equivalent,
with no further hypothesis.

The two equivalences that `Stacks.Curves.isNode_tfae_of_fittingIdeal_equivalence` leaves open are
discharged by
`Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation_of_rational`,
which turns the Fitting-ideal condition into the nodal quadratic relation: condition (1) becomes
condition (4) through condition (2), and condition (5) becomes condition (4) because the exchange
of depth one for reducedness in the presence of the nodal relation is Stacks Tag 0C49.

What keeps this short of the tag is only the rationality of `κ(x)`: a presentation of an affine
chart whose generators vanish at `x` exists exactly then, since generators lying in the prime of
`x` generate `κ(x)` over `k` by zero.

A general closed point has `κ(x) / k` finite and, by
`Stacks.Curves.isSeparableExtension_residueField_of_isNode` and the separability clause of
conditions (2), (4), (5) and (6), separable in every case that matters.  Reducing it to the
rational case asks only for the Fitting-ideal condition to descend along the base change to the
algebraic closure: Tag 0C3I
(`AlgebraicGeometry.fittingIdeal_relativeDifferentials_comap`) together with
`AlgebraicGeometry.IdealSheafData.stalk_comap` makes the stalk of the Fitting ideal upstairs the
extension of the stalk downstairs, Tag 0C50
(`AlgebraicGeometry.map_maximalIdeal_stalkMap_eq_of_isReduced_tensorProduct`) makes the maximal
ideal upstairs the extension of the maximal ideal downstairs, and faithful flatness of the stalk
map retracts the extension of ideals.  That descent is carried out in
`StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealClosedPoint`, where
`Stacks.Curves.isNode_tfae_of_isClosed` states the six conditions at an arbitrary closed point;
it also needs reducedness and depth one to cross between the two points, and they cross in
opposite directions. -/
@[stacks 0C4D "all six clauses, at a closed point whose residue field is the base field"]
theorem isNode_tfae_of_rational
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X))
    (hrat : Function.Surjective ((X.residue x).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom)) :
    let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    let omega := f.relativeDifferentials
    let fittingCondition : Prop :=
      AlgebraicGeometry.IdealSheafData.stalk (AlgebraicGeometry.fittingIdeal omega 1) x =
        maximalIdeal (X.presheaf.stalk x)
    let c₁ : Prop := IsNode k X x
    let c₂ : Prop := IsNodalAlgebra k (X.presheaf.stalk x)
    let c₃ : Prop :=
      (let K := AlgebraicClosure k
       let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
         AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
       let Y := (CategoryTheory.Limits.pullback f g : Scheme.{u})
       let p : Y ⟶ X := CategoryTheory.Limits.pullback.fst f g
       let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := CategoryTheory.Limits.pullback.snd f g
       letI : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
       ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar)
    let c₄ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧ fittingCondition
    let c₅ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x) = 1 ∧
          fittingCondition
    let c₆ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            AlgebraicGeometry.numberOfGeometricBranches X x = 2
    List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆] := by
  intro f kToStalk omega fittingCondition c₁ c₂ c₃ c₄ c₅ c₆
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  have hNag : IsNagataRing (X.presheaf.stalk x) :=
    isNagataRing_stalk_of_locallyOfFiniteType k f x
  let : IsNoetherianRing (X.presheaf.stalk x) := hNag.isNoetherianRing
  have key : fittingCondition ↔ HasNodalQuadraticRelation (X.presheaf.stalk x) :=
    stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation_of_rational k f x hx hrat
  have h24 : c₂ ↔ c₄ := isNodalAlgebra_stalk_iff_of_rational k f x hx hrat k
  refine isNode_tfae_of_fittingIdeal_equivalence k X hX x hx
    ((isNode_iff_isNodalAlgebra_stalk k X hX x).trans h24) ?_
  rintro ⟨hsep, hdepth, hfit⟩
  have h5 : Algebra.IsSeparableExtension k (ResidueField (X.presheaf.stalk x)) ∧
      Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) = 1 ∧
        HasNodalQuadraticRelation (X.presheaf.stalk x) :=
    ⟨hsep, hdepth, key.mp hfit⟩
  exact h24.mp (((isNodalAlgebra_tfae k (X.presheaf.stalk x)).out 2 1).mp h5)

end Stacks.Curves

end
