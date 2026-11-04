module

public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphisms
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsTorsor
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.SpecialFibreThin
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent

/-!
# The `Inf` term of the deformation sequence of a scheme is a group of self-maps

Let `k` be a field and `X` a scheme over `k`. The term `Inf(𝓓_X)` that appears in the exact
sequences of [Stacks Project, Tag 06L5] and [Stacks Project, Tag 0E3V] is the `k`-vector space
`Deformation.localizedAutomorphismFunctorTangent`, the tangent space at the identity of the
automorphism functor of a chosen pushforward. That is an abstract object: it is built from the
category over `𝒞_Λ` and knows nothing about schemes.

This file identifies it with honest self-maps of the total space of a deformation of `X`. The
route is `Deformation.localizedTangentEquivKernel`, which presents it as the subgroup of
automorphisms of the chosen pushforward to the dual numbers that die under reduction to the
residue field. For a predeformation category that subgroup is **everything**: the special fibre
is thin (`Deformation.isThin_specialFiber`), so the automorphism group it reduces into is
trivial and the reduction homomorphism has everything in its kernel
(`Deformation.ker_transportAutHom_eq_top_of_isThin`). What is left is the full automorphism
group of a point of a fibre of the deformation category, which
`Deformation.Examples.autFiberBaseMulEquiv` and
`Deformation.Examples.fiberAutEquivLiftsOverBaseTop` turn into the self-maps of the total space
over the base fixing the special-fibre immersion.

## Main definitions

* `Deformation.Examples.localizedTangentEquivFiberAut`: the `Inf` term of the sequence is the
  automorphism group of the chosen first-order pushforward, read in its own fibre.
* `Deformation.Examples.localizedTangentEquivSelfMaps`: the `Inf` term is the set of invertible
  self-maps of the total space over the base fixing the special-fibre immersion.
* `Deformation.Examples.localizedTangentEquivLiftsOverBaseTop`: the `Inf` term is the set of
  global lifts of the identity of `X`, which is the set that
  [Stacks Project, Tag 0CK2] makes the derivations act on.

## Main results

* `Deformation.Examples.ker_transportAutHom_tangentReduction_eq_top`: for the deformation
  category of a scheme every automorphism of the chosen first-order pushforward is
  infinitesimal.

## Implementation notes

The three identifications are bijections of sets, not of groups, and deliberately so. The first
two are isomorphisms of groups —
`Deformation.Examples.autFiberBaseMulEquiv` is a `MulEquiv` and
`Deformation.Examples.fiberAutEquivSelfMaps_mul` records that the second takes the group law to
composition — but `Deformation.localizedTangentEquivKernel` is only a bijection: the group
structure on the `Inf` term is the *additive* one of the tangent space, and that composition of
self-maps corresponds to its addition is the content of the infinitesimal-automorphism clause of
[Stacks Project, Tag 0DY9], which the library has for algebras
(`Deformation.Examples.exists_infinitesimalAutomorphismGroupMulEquivDerivation`, Tag 0DY3) and
not for schemes. Nothing here asserts it.

In particular this file does **not** transport the `k`-vector space structure of the `Inf` term
onto the self-maps, and does not claim that the derivation action of
`Deformation.Examples.exists_simplyTransitive_addAction_deformationSelfMaps` is `k`-linear
through these bijections. Those are the two statements the arrows of
[Stacks Project, Tag 0E3V] out of the `Inf` terms need, and neither is asserted here: the scalar
action on the `Inf` term is implemented by
`Deformation.transportAutHom (Deformation.tangentScaling c)`, and nothing below says what that
transport does to a self-map or to a derivation.

Elsewhere in the library it is said, twice. On self-maps,
`Deformation.Examples.localizedTangentEquivSelfMaps_smul_comp` reads the transport on total
spaces: the self-map of `c • a` and the self-map of `a` are conjugate across the morphism
underlying the transport. On derivations,
`Deformation.Examples.conormalSelfMap_tangentScaling_eq_smul` computes what that morphism does
to the conormal sections of the special fibre, namely multiplication by the function `c`
determines on `X`. What neither supplies is the composite of the two, that the derivation
attached to the scaled tangent vector is `c` times the one attached to the vector; that is the
hypothesis `hscale` of `Deformation.map_smul_of_simplyTransitive`, which the arrow
`Deformation.Examples.schemeMorphismConjugationArrow` makes statable and which is still open.

The reduction arrow whose kernel is taken is `Deformation.tangentReduction`, which goes from
`Deformation.dualNumbersUnder` to `Deformation.specialFibreUnder`; that is precisely the shape
`Deformation.ker_transportAutHom_eq_top_of_isThin` consumes, so no comparison of reduction
arrows occurs.

The universes of the abstract machinery are written out as `.{u, u, u}`, as elsewhere in
`Deformation.Examples`: the deformation categories of schemes are stated over
`ArtinianLocalAlgCat.{u, u, u} Λ k`, and the abstract statements are indexed by a triple whose
second entry is `max v w`.

## References

* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X : Over (Spec (CommRingCat.of k))}

/-- The chosen pushforward of a point of the deformation category of `X` to the dual numbers
under its base: the first-order deformation at which the `Inf` term of the sequence is read. -/
abbrev firstOrderPushforward
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X :=
  (P.obj (dualNumbersUnder
    (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀))).1

/-! ### Every automorphism of the first-order pushforward is infinitesimal -/

/-- **For the deformation category of a scheme every automorphism of the chosen first-order
pushforward is infinitesimal.** The special fibre of a predeformation category is thin, so the
automorphism group that the reduction to the residue field lands in is trivial. -/
theorem ker_transportAutHom_tangentReduction_eq_top
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    MonoidHom.ker (P.transportAutHom
        (tangentReduction
          (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀))) = ⊤ :=
  ker_transportAutHom_eq_top_of_isThin.{u, u, u} hp.cofibered P
    (isThin_specialFiber.{u, u, u} hp) _

/-! ### The `Inf` term as an automorphism group -/

/-- **The `Inf` term of the deformation sequence of a scheme is the automorphism group of the
chosen first-order pushforward.** `Deformation.localizedTangentEquivKernel` presents the term as
the infinitesimal automorphisms of that pushforward, and
`Deformation.Examples.ker_transportAutHom_tangentReduction_eq_top` says that all of its
automorphisms are infinitesimal.

The bijection is of sets: the group law of the `Inf` term is the addition of the tangent space,
and that it corresponds to composition of automorphisms is the infinitesimal-automorphism clause
of [Stacks Project, Tag 0DY9], which is not asserted here. -/
def localizedTangentEquivFiberAut
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    localizedAutomorphismFunctorTangent P ≃
      Aut (deformationFiberObj
        (P.obj (dualNumbersUnder
          (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀))).1) :=
  (localizedTangentEquivKernel P).trans
    (((MulEquiv.subgroupCongr
        (ker_transportAutHom_tangentReduction_eq_top hp P)).trans
      (Subgroup.topEquiv)).toEquiv.trans
      (autFiberBaseMulEquiv
        (P.obj (dualNumbersUnder
          (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) (x := x₀)))).toEquiv)

/-- **The `Inf` term of the deformation sequence of a scheme is a set of self-maps.** Composing
`Deformation.Examples.localizedTangentEquivFiberAut` with
`Deformation.Examples.fiberAutEquivSelfMaps`: the term is the invertible self-maps of the total
space of the chosen first-order pushforward, over the base and fixing the special-fibre
immersion. -/
def localizedTangentEquivSelfMaps
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    localizedAutomorphismFunctorTangent P ≃
      { e : (firstOrderPushforward P).scheme ⟶ (firstOrderPushforward P).scheme //
        e ≫ (firstOrderPushforward P).toBase = (firstOrderPushforward P).toBase ∧
          (firstOrderPushforward P).specialMap ≫ e =
            (firstOrderPushforward P).specialMap ∧ IsIso e } :=
  (localizedTangentEquivFiberAut hp P).trans
    (fiberAutEquivSelfMaps (firstOrderPushforward P))

/-- **The `Inf` term of the deformation sequence of a scheme is the set of global lifts of the
identity of `X`.** This is the set that [Stacks Project, Tag 0CK2] makes the derivations act
simply transitively on, by
`Deformation.Examples.exists_simplyTransitive_addAction_deformationSelfMaps`. So the abstract
`Inf` term of the source's sequence and the geometric torsor of
[Stacks Project, Tag 0DY9] are the same set. -/
def localizedTangentEquivLiftsOverBaseTop
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    localizedAutomorphismFunctorTangent P ≃
      Stacks.Thickenings.liftsOverBase (firstOrderPushforward P).specialMap
        (firstOrderPushforward P).specialMap (firstOrderPushforward P).toBase
        (firstOrderPushforward P).toBase (𝟙 X.left) ⊤ :=
  (localizedTangentEquivFiberAut hp P).trans
    (fiberAutEquivLiftsOverBaseTop (firstOrderPushforward P))

/-! ### The `Inf` term as a torsor under the derivations -/

/-- **The `k`-derivations of `𝒪_X` act simply transitively on the `Inf` term of the deformation
sequence of `X`.** There is an action of the derivations on
`localizedAutomorphismFunctorTangent P`, the tangent space of the automorphism functor appearing
in the sequences of [Stacks Project, Tag 06L5] and [Stacks Project, Tag 0E3V], which is unital,
additive in the acting derivation, and simply transitive. It is the infinitesimal-automorphism
torsor of `Deformation.Examples.exists_simplyTransitive_addAction_deformationSelfMaps`
([Stacks Project, Tag 0DY9]) transported along
`Deformation.Examples.localizedTangentEquivLiftsOverBaseTop`. Compatibility of the action with the
`k`-vector space structure of the `Inf` term, the group-isomorphism half of
[Stacks Project, Tag 0DY9], is not proved here: the library has it for algebras, not schemes. -/
theorem exists_simplyTransitive_addAction_localizedTangent
    (hp : IsPredeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀)
    (coordinate : (firstOrderPushforward P).base ≃ₐ[Λ] DualNumber k) :
    ∃ act : schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom →
        localizedAutomorphismFunctorTangent P → localizedAutomorphismFunctorTangent P,
      (∀ c, act 0 c = c) ∧
        (∀ θ η c, act (θ + η) c = act θ (act η c)) ∧
        ∀ c₀ c₁, ∃! θ, act θ c₀ = c₁ := by
  obtain ⟨act, hzero, hadd, htrans⟩ :=
    exists_simplyTransitive_addAction_deformationSelfMaps (firstOrderPushforward P) coordinate
  set E := localizedTangentEquivLiftsOverBaseTop hp P with hE
  refine ⟨fun θ a => E.symm (act θ (E a)), ?_, ?_, ?_⟩
  · intro a
    show E.symm (act 0 (E a)) = a
    rw [hzero, E.symm_apply_apply]
  · intro θ η a
    show E.symm (act (θ + η) (E a)) = E.symm (act θ (E (E.symm (act η (E a)))))
    rw [hadd, E.apply_symm_apply]
  · intro a b
    show ∃! θ, E.symm (act θ (E a)) = b
    obtain ⟨θ, hθ, huniq⟩ := htrans (E a) (E b)
    refine ⟨θ, ?_, ?_⟩
    · show E.symm (act θ (E a)) = b
      rw [hθ, E.symm_apply_apply]
    · intro ψ hψ
      have hψ' : E.symm (act ψ (E a)) = b := hψ
      exact huniq ψ (E.symm_apply_eq.mp hψ')

end Deformation.Examples

end
