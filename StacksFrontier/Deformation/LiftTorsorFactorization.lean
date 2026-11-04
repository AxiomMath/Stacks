module

public import StacksFrontier.Deformation.ToposThickening.LiftingBetweenThickenings

/-!
# The bijection of Steps 1 to 3 of Stacks 08U8 out of a simply transitive action

`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff`, which is clause (1) of
[Stacks Project, Tag 08U8], and the principal homogeneous space structure
`AlgebraicGeometry.RingedSpaceThickening.existsUnique_liftTranslate` of its clause (2), both
take the content of Steps 1 to 3 of the source's proof as a hypothesis: an equivalence
`e : Lift ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ}` between the morphisms fitting into the source's
diagram and the factorizations of the difference homomorphism through the degree `0` term of
`NL(α)`.

This file reduces that hypothesis to the identification of the two acting groups. The
factorizations are a principal homogeneous space under `Hom(H⁰(NL(α)), 𝒢)`, written as the Hom
out of the cokernel of the differential, by
`Deformation.ToposThickening.factorizationEquivCokernelHom`. So whenever the lifts are a
principal homogeneous space under some group `A`, an identification `κ : A ≃ Hom(H⁰(NL(α)), 𝒢)`
of the two acting groups produces `e`, once a base point is chosen on each side.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.equivOfExistsUniqueAct`: a type acting on a set with
  every ordered pair of its elements joined by exactly one actor is in bijection with that set,
  once a base point of the set is chosen.
* `AlgebraicGeometry.RingedSpaceThickening.liftEquivFactorizationOfAct`: **the equivalence `e`
  of Steps 1 to 3 of [Stacks Project, Tag 08U8] from torsor data** — a simply transitive action
  on the lifts, an identification of its acting group with `Hom(H⁰(NL(α)), 𝒢)`, and a base point
  on each side.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.liftEquivFactorizationOfAct_apply`: the formula that
  determines the equivalence, so it is pinned to the data it is built from and is not an
  arbitrary reparametrisation.
* `AlgebraicGeometry.RingedSpaceThickening.liftEquivFactorizationOfAct_symm_apply`: the lift
  attached to a factorization is the translate of the chosen lift.

## Implementation notes

The hypothesis on the action is only simple transitivity, `∀ c₀ c₁, ∃! a, act a c₀ = c₁`; no
group structure on `A` and no action laws are used, since the construction evaluates the action
at a single base point. That is the weakest form in which the library states the conclusion of
[Stacks Project, Tag 0CK2] and of clause (2) of [Stacks Project, Tag 08U8], which is what makes
this usable at both.

Both base points are genuinely needed, and the reader should note what that costs. With a lift
`p` and a factorization `θ₀` in hand, both sides of clause (1) of **Stacks 08U8** already hold,
so an `e` built here discharges that clause only vacuously. What it discharges with content is
clause (2): through it the lifts become a principal homogeneous space under
`Hom(H⁰(NL(α)), 𝒢)`, the group that the source identifies with `Ext⁰(Lg^*NL_{X₁/S₁}, 𝒢₂)` and
whose identification with the concrete acting group is exactly the input `κ`. A non-vacuous
clause (1) needs the canonical map from lifts to factorizations, which in turn needs `ξ` to be
*constructed* from the pair of deformations as in Step 1 of the source's proof; the
implementation notes of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionTorsor.lean` record why the library
cannot do that yet.

`Deformation.ToposThickening.liftEquivFactorization` is the same construction for the concrete
lifts and derivations of a `Deformation.ToposThickening.LiftDiagram`, where the trivialization of
the lifts is the concrete difference-of-lifts bijection rather than an abstract simply transitive
action. Neither subsumes the other: that one needs no simple-transitivity hypothesis, this one
needs no `LiftDiagram`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' v u v' u'

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Trivialization of a simply transitive action -/

section Act

variable {A : Type w} {L : Type w'} (act : A → L → L)
  (hact : ∀ c₀ c₁ : L, ∃! a : A, act a c₀ = c₁) (p : L)

/-- Trivialization of a simply transitive action at a base point: if every ordered pair of
elements of `L` is joined by exactly one element of `A`, then evaluating the action at a chosen
`p : L` is a bijection `A ≃ L`, and an element of `L` corresponds to the unique actor carrying
`p` to it. -/
def equivOfExistsUniqueAct : L ≃ A :=
  (Equiv.ofBijective (fun a => act a p)
    ⟨fun _ b h => (hact p (act b p)).unique h rfl, fun q => (hact p q).exists⟩).symm

/-- The element of `L` attached to an actor by the trivialization at `p` is its translate of
`p`. -/
theorem equivOfExistsUniqueAct_symm_apply (a : A) :
    (equivOfExistsUniqueAct act hact p).symm a = act a p := rfl

/-- The actor attached to an element of `L` by the trivialization at `p` carries `p` to it. -/
theorem act_equivOfExistsUniqueAct (q : L) : act (equivOfExistsUniqueAct act hact p q) p = q :=
  (equivOfExistsUniqueAct act hact p).symm_apply_apply q

end Act

/-! ### The bijection of Steps 1 to 3 of Stacks 08U8 -/

section Factorization

variable {M : Type u} [Category.{v} M] [Abelian M] {D : Type u'} [Category.{v'} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] {single : M ⥤ D}

variable (P : NaiveCotangentTwoTerm single) (G : M) (ξ : P.conormal ⟶ G) {A : Type w}
  {L : Type w'} (act : A → L → L) (hact : ∀ c₀ c₁ : L, ∃! a : A, act a c₀ = c₁) (p : L)
  (κ : A ≃ (cokernel P.d ⟶ G)) (θ₀ : {θ : P.base ⟶ G // P.d ≫ θ = ξ})

/-- **The equivalence `e` of Steps 1 to 3 of [Stacks Project, Tag 08U8] from torsor data.**
Suppose a type `A` acts on the lifts `L` with every ordered pair of lifts joined by exactly one
actor, and that `κ` identifies `A` with `Hom(H⁰(NL(α)), 𝒢)`, the homomorphisms out of the
cokernel of the differential. Then a lift `p` and a factorization `θ₀` of `ξ` through the degree
`0` term identify the lifts with the factorizations: the two principal homogeneous space
structures are trivialized at the two base points and matched by `κ`.

This is the hypothesis `e` of
`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff` and of
`AlgebraicGeometry.RingedSpaceThickening.existsUnique_liftTranslate`. It is the *formal* half of
Steps 1 to 3; the one mathematical input is `κ`, the identification of the acting groups, which
the source obtains from the presentation of Step 1 of its proof and which
[Stacks Project, Tag 08U8] as formalized in this library explicitly does not prove. -/
def liftEquivFactorizationOfAct : L ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ} :=
  ((equivOfExistsUniqueAct act hact p).trans κ).trans
    (Deformation.ToposThickening.factorizationEquivCokernelHom P G ξ θ₀).symm

/-- **The formula that determines the equivalence.** The factorization attached to a lift `q` is
the chosen factorization `θ₀` translated by the image under `κ` of the unique actor carrying the
chosen lift `p` to `q`, composed with the projection onto the cokernel of the differential. So
the equivalence is pinned to the data it is built from, and is not an arbitrary
reparametrisation of either side. -/
theorem liftEquivFactorizationOfAct_apply (q : L) :
    (liftEquivFactorizationOfAct P G ξ act hact p κ θ₀ q).1 =
      θ₀.1 + cokernel.π P.d ≫ κ (equivOfExistsUniqueAct act hact p q) := rfl

/-- The lift attached to a factorization `θ` is the translate of the chosen lift `p` by the
actor that `κ` matches with the difference of `θ` and the chosen factorization `θ₀`. -/
theorem liftEquivFactorizationOfAct_symm_apply (θ : {θ : P.base ⟶ G // P.d ≫ θ = ξ}) :
    (liftEquivFactorizationOfAct P G ξ act hact p κ θ₀).symm θ =
      act (κ.symm (cokernel.desc P.d (θ.1 - θ₀.1) (by
        rw [Preadditive.comp_sub, θ.2, θ₀.2, sub_self]))) p := rfl

end Factorization

end AlgebraicGeometry.RingedSpaceThickening

end
