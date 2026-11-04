module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftGroup
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphisms
public import StacksFrontier.Deformation.Examples.Geometric.SpecialFibreFirstOrder

/-!
# Derivations act simply transitively on the infinitesimal automorphisms of a scheme

Let `k` be a field, `X` a scheme over `k`, and `P` a deformation of `X` over an object of `𝒞_Λ`
carrying a dual-number coordinate. [Stacks Project, Tag 04FJ] makes
`Hom_{𝒪_X}(Ω_{X/k}, 𝒞_{X/P.scheme})` act simply transitively on the lifts of the identity of `X`
to `P.scheme`, and the conormal sheaf of the special-fibre immersion of such a deformation is
the structure sheaf of `X` by `Deformation.Examples.deformationConormalIsoUnit`, so the acting
group is the derivations of `𝒪_X`. This file instantiates that action at a single deformation —
the case `Y = X` and `f = 𝟙` of the two-deformation statement
`Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts` — and transports it
along `Deformation.Examples.infinitesimalAutomorphismGroupEquivLiftsOverBaseTop` onto the
infinitesimal automorphism group itself.

The result is that `Inf(𝓓_X)` is a simply transitive `Der_k(𝒪_X, (𝟙_X)_*𝒪_X)`-set: the identity
automorphism is a distinguished point, so choosing it as origin identifies the two as sets.

## Main results

* `Deformation.Examples.exists_simplyTransitive_addAction_deformationSelfMaps`: the derivations
  act simply transitively on the lifts of the identity of `X` to the total space of a
  deformation.
* `Deformation.Examples.exists_simplyTransitive_addAction_infinitesimalAutomorphismGroup`: the
  same action read on `Inf(𝓓_X)`.

## Implementation notes

The instantiation takes `f := 𝟙 X.left`, both thickenings to be the special-fibre immersion of
`P`, both structure morphisms to be `P.toBase`, and the lift `F := 𝟙 P.scheme`. The three
hypotheses of the two-deformation statement are discharged by results in the library: the cartesian
square is `Deformation.Examples.SchemeDeformationCategory.specialCartesian` used twice, the
square-zero condition on the base is
`Deformation.Examples.maximalIdeal_sq_eq_bot_of_dualNumberEquiv` applied to the coordinate, and
the trivialisation of the conormal sheaf is
`Deformation.Examples.deformationConormalIsoUnit`.

The structure morphism `X.hom` of `X` over `Spec k` is passed where a morphism to
`Deformation.Examples.baseSpec (Deformation.Examples.residueFieldBase Λ k)` is expected. The two
targets are equal — the carrier of `residueFieldBase` is `k` itself — but the equality is not
reducible, so the coefficient arguments `Λ` and `k` are supplied by name; left implicit they
remain metavariables and instance search for `Algebra Λ k` gets stuck before the ascription can
pin them.

The acting group is `Der_k(𝒪_X, (𝟙_X)_*𝒪_X)`, the coefficients being the pushforward of the
structure sheaf along the identity rather than the structure sheaf itself. This is the shape in
which `Deformation.Examples.schemeMorphismDerivations` is stated, the general case being a
morphism `f : X ⟶ Y` with coefficients `f_*𝒪_X`; the identity pushforward is isomorphic to the
identity functor by `SheafOfModules.pushforwardId` but is not the same functor, and no such
transport is performed here.

No `@[stacks]` attribute is carried. The statement is [Stacks Project, Tag 04FJ] at a particular
instance, not a clause of its own lemma, and it is a simply transitive action rather than the
isomorphism of groups that the infinitesimal-automorphism clause of
[Stacks Project, Tag 0DY9] asserts: the torsor axioms give additivity in the acting derivation
but say nothing about composing two self-maps, so they do not by themselves make the induced
bijection a group isomorphism.

## References

* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X : Over (Spec (CommRingCat.of k))}

/-- **[Stacks Project, Tag 04FJ] at a single deformation of a scheme.** The `k`-derivations of
`𝒪_X` act simply transitively on the self-maps of the total space of a deformation `P` of `X`
over the base of `P`, fixing the special-fibre immersion — equivalently on the global lifts of
the identity of `X`.

This is `Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts` at `Y = X`,
`f = 𝟙 X`, both deformations equal to `P` and the lift equal to `𝟙 P.scheme`, whose conormal
hypothesis is discharged by `Deformation.Examples.deformationConormalIsoUnit` and whose
square-zero hypothesis by the dual-number coordinate. -/
theorem exists_simplyTransitive_addAction_deformationSelfMaps
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k) :
    ∃ act : schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom →
        Stacks.Thickenings.liftsOverBase P.specialMap P.specialMap P.toBase P.toBase
          (𝟙 X.left) ⊤ →
        Stacks.Thickenings.liftsOverBase P.specialMap P.specialMap P.toBase P.toBase
          (𝟙 X.left) ⊤,
      (∀ c, act 0 c = c) ∧
        (∀ θ η c, act (θ + η) c = act θ (act η c)) ∧
        ∀ c₀ c₁, ∃! θ, act θ c₀ = c₁ := by
  have : IsClosedImmersion P.specialMap := deformationSpecialMap_isClosedImmersion P
  exact exists_simplyTransitive_addAction_schemeMorphismLifts
    (Λ := Λ) (k := k) (𝟙 X.left) X.hom X.hom (Category.id_comp _)
    P.specialCartesian P.specialCartesian
    (maximalIdeal_sq_eq_bot_of_dualNumberEquiv coordinate)
    (Category.id_comp _) (by simp)
    (deformationConormalIsoUnit P coordinate)

/-- **The `k`-derivations of `𝒪_X` act simply transitively on `Inf(𝓓_X)`.** The infinitesimal
automorphism group of the deformation category of `X` at a point `xε` over an object of `𝒞_Λ`
with a dual-number coordinate is the set of global lifts of the identity of `X`, by
`Deformation.Examples.infinitesimalAutomorphismGroupEquivLiftsOverBaseTop`, and the derivations
act simply transitively on those by
`Deformation.Examples.exists_simplyTransitive_addAction_deformationSelfMaps`. Transporting the
action along that bijection gives the action on the group itself.

Since the identity is an element of `Inf(𝓓_X)`, simple transitivity identifies the two as sets;
what it does not supply is that the identification is a homomorphism, for which the interaction
of the action with composition of self-maps is needed. -/
theorem exists_simplyTransitive_addAction_infinitesimalAutomorphismGroup
    (hp : IsPredeformationCategory
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (coordinate : xε.1.base ≃ₐ[Λ] DualNumber k)
    (i : x₀.1 ⟶ xε.1)
    (hi : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift g i) :
    ∃ act : schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom →
        infinitesimalAutomorphismGroup hp g e hpair i hi →
        infinitesimalAutomorphismGroup hp g e hpair i hi,
      (∀ c, act 0 c = c) ∧
        (∀ θ η c, act (θ + η) c = act θ (act η c)) ∧
        ∀ c₀ c₁, ∃! θ, act θ c₀ = c₁ := by
  obtain ⟨act, hzero, hadd, htrans⟩ :=
    exists_simplyTransitive_addAction_deformationSelfMaps xε.1 coordinate
  set E := infinitesimalAutomorphismGroupEquivLiftsOverBaseTop hp g e hpair i hi with hE
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
