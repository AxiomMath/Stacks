module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassInverse
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.PowerTransitionPullback

/-!
# The inverse of the chart-wise class commutes with the transition `F_d → F_{a d}`

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `V` an open of
`S` and `a ≥ 1`. The inverse `...RelativeProjQcohSheaf.Fd.chartClassInv` of the chart-wise class
carries a point of `F_d(T)` for `𝒜|_V` to a point of `F_d(T)` for `𝒜`; this file proves it
**commutes with the transition `F_d → F_{a d}`** of
`...RelativeProjQcohSheaf.Fd.scale`.

That is the compatibility `equiv_scale` of a `...RelativeProjQcohSheaf.ProjDegreeRepresentation`
over a general base consumes alongside the chart-wise Veronese computation
`...RelativeProjQcohSheaf.Fd.chartHom_scale`, and it was proved nowhere.

## How

`Fd.chartClassInv` is two maps: the comparison
`...RelativeProjQcohSheaf.Fd.restrictPullbackEquiv` of the two spellings of the restriction,
which is an instance of `...RelativeProjQcohSheaf.Fd.algebraTransport`, and the base change of
[Stacks, Tag 01NT] in the upward direction, `...RelativeProjQcohSheaf.Fd.baseChangeUp`. **Both
leave the invertible module `L` of a quadruple untouched** and change only `ψ`, by precomposing
its degree-`i` component with a morphism attached to the degree `i d`.

So both carry a comparison of [Stacks, Tag 01NW] at a common multiple of two degrees to a
comparison of the transported quadruples with *the same* family of isomorphisms of the Laurent
algebras — `Quadruple.CompatibleAt.algebraTransport` and `Quadruple.CompatibleAt.baseChangeUp`
below — the only clause needing an argument being the one about `ψ`, where the morphism attached
to the degree has to be moved across the transport of the degree. In both cases that is the
naturality of a family indexed by `ℤ` along an equality of indices, proved by `subst` after
generalising the two degrees to variables.

With that, the two commutations are
`...Quadruple.strictlyEquivalent_of_compatibleAt_one` exactly as
`...Quadruple.strictlyEquivalent_pullback_scale` is: the transport of the transition and the
transition of the transport are both compatible at `(a, 1)` with the transport of the quadruple,
the first because `...Quadruple.compatibleAt_scale` transports and the second because it holds
of every quadruple.

## Main results

* `...RelativeProjQcohSheaf.Quadruple.CompatibleAt.algebraTransport` and
  `...Quadruple.CompatibleAt.baseChangeUp`: **a comparison at a common multiple of two degrees
  survives the transport along a unital homomorphism of graded algebras, and the base change of
  [Stacks, Tag 01NT].**
* `...RelativeProjQcohSheaf.Fd.algebraTransport_scale`,
  `...Fd.restrictPullbackEquiv_scale` and `...Fd.baseChangeUp_scale`: the two halves of
  `Fd.chartClassInv` commute with the transition.
* `...RelativeProjQcohSheaf.Fd.chartClassInv_scale`: **the inverse of the chart-wise class
  commutes with the transition `F_d → F_{a d}`.**

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### A comparison survives the transport along a unital homomorphism -/

/-- The rearrangement the `ψ`-clause of a comparison needs when the two quadruples have had
their `ψ` precomposed with a morphism attached to the degree: the clause for the originals and
the commutation of that morphism with the transport of the degree give the clause for the
transported pair.

Stated with every object and morphism a free variable, which is what lets a caller discharge it
by `exact` where the two spellings of an object are equal but not syntactically so. -/
private theorem comp_app_comp_of_comm {C : Type*} [Category C] {W W' X X' Y Y' : C}
    (c : W ⟶ X) (α : X ⟶ Y) (β : X' ⟶ Y') (κ : Y ⟶ Y') (e : X ⟶ X') (ε : W ⟶ W')
    (c' : W' ⟶ X') (hψ : α ≫ κ = e ≫ β) (hcomm : c ≫ e = ε ≫ c') :
    c ≫ α ≫ κ = ε ≫ c' ≫ β := by
  rw [hψ, ← Category.assoc, hcomm, Category.assoc]

namespace Quadruple

variable {T X : Scheme.{u}}
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
  {d d' : ℤ} {f : T ⟶ X}

/-- **A homomorphism of graded algebras commutes with the transport of the degree.** The
components of `Φ` form a family indexed by `ℤ`, so moving `Φ` across the identification of two
equal degrees is `subst` once the two degrees are variables — which is why it is stated here for
arbitrary `n`, `m` rather than at the compound degrees it is used at. -/
theorem unitalHom_app_comp_eqToHom (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    {n m : ℤ} (h : n = m) :
    Φ.app n ≫ eqToHom (congrArg B.piece h) = eqToHom (congrArg A.piece h) ≫ Φ.app m := by
  subst h
  simp

/-- **A comparison of [Stacks, Tag 01NW] at a common multiple of two degrees survives the
transport along a unital homomorphism of graded algebras.** The transport leaves the invertible
module of a quadruple unchanged, so the comparison is carried by *the same* family of
isomorphisms of the Laurent algebras, and its multiplicativity and unit clauses are the given
ones verbatim. The clause about `ψ` is the given one with `Φ` moved across the transport of the
degree by `unitalHom_app_comp_eqToHom`. -/
theorem CompatibleAt.algebraTransport (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (hiso : ∀ n : ℤ, IsIso (Φ.app n)) {P : Quadruple f B d} {Q : Quadruple f B d'} {a a' : ℤ}
    (hc : CompatibleAt P Q a a') :
    CompatibleAt (Quadruple.algebraTransport Φ hiso P)
      (Quadruple.algebraTransport Φ hiso Q) a a' := by
  obtain ⟨hm, γ, hmul, hone, hψ⟩ := hc
  refine ⟨hm, γ, hmul, hone, fun p q hpq => ?_⟩
  have hdeg : p * d = q * d' := hpq.degree_eq hm
  exact comp_app_comp_of_comm ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (p * d)))
    (P.twisting.app p) (Q.twisting.app q) (γ p q hpq).hom
    ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg B.piece hdeg)))
    ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece hdeg)))
    ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (q * d'))) (hψ p q hpq)
    (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      unitalHom_app_comp_eqToHom Φ hdeg])

/-- **The transport along a unital homomorphism commutes with the transition `F_d → F_{a d}` on
quadruples, up to strict equivalence.** The transport of the transition and the transition of
the transport are both compatible at `(a, 1)` with the transport of the quadruple — the first by
`CompatibleAt.algebraTransport` applied to `Quadruple.compatibleAt_scale`, the second by
`Quadruple.compatibleAt_scale` itself — so they are strictly equivalent. -/
theorem strictlyEquivalent_algebraTransport_scale
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (hiso : ∀ n : ℤ, IsIso (Φ.app n))
    (P : Quadruple f B d) {a : ℤ} (ha : 0 < a) :
    StrictlyEquivalent (Quadruple.algebraTransport Φ hiso (P.scale ha))
      ((Quadruple.algebraTransport Φ hiso P).scale ha) :=
  strictlyEquivalent_of_compatibleAt_one
    ((P.compatibleAt_scale ha).algebraTransport Φ hiso)
    ((Quadruple.algebraTransport Φ hiso P).compatibleAt_scale ha)

end Quadruple

/-! ### A comparison survives the base change of Tag 01NT -/

namespace Quadruple

variable {S S' T : Scheme.{u}} (g : S' ⟶ S) (f' : T ⟶ S')
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) {d d' : ℤ}

/-- **The comparison of an iterated pullback with the pullback along the composite commutes with
the transport of the degree.** The identification of Tag 01NT is natural in the sheaf of modules,
and the degrees it is read at here are compound; generalising them to variables makes the
statement a `subst`. -/
theorem compComparison_comp_eqToHom {n m : ℤ} (h : n = m) :
    compComparison f' g (A.piece n) ≫ (pullbackFunctor (ringedSpaceHom f')).map
          (eqToHom (congrArg (baseAlgebra g A).piece h))
      = (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map (eqToHom (congrArg A.piece h)) ≫
          compComparison f' g (A.piece m) := by
  subst h
  change compComparison f' g (A.piece n) ≫ (pullbackFunctor (ringedSpaceHom f')).map
        (CategoryStruct.id ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece n)))
      = (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map (CategoryStruct.id (A.piece n))
        ≫ compComparison f' g (A.piece n)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp]

/-- **A comparison of [Stacks, Tag 01NW] at a common multiple of two degrees survives the base
change of [Stacks, Tag 01NT].** The base change leaves the invertible module of a quadruple
unchanged, so the comparison is carried by *the same* family of isomorphisms of the Laurent
algebras; the clause about `ψ` is the given one with the identification of Tag 01NT moved across
the transport of the degree by `compComparison_comp_eqToHom`. -/
theorem CompatibleAt.baseChangeUp {P : Quadruple f' (baseAlgebra g A) d}
    {Q : Quadruple f' (baseAlgebra g A) d'} {a a' : ℤ} (hc : CompatibleAt P Q a a') :
    CompatibleAt (P.baseChangeUp g f' A d) (Q.baseChangeUp g f' A d') a a' := by
  obtain ⟨hm, γ, hmul, hone, hψ⟩ := hc
  refine ⟨hm, γ, hmul, hone, fun p q hpq => ?_⟩
  exact comp_app_comp_of_comm (compComparison f' g (A.piece (p * d))) (P.twisting.app p)
    (Q.twisting.app q) (γ p q hpq).hom
    ((pullbackFunctor (ringedSpaceHom f')).map
      (eqToHom (congrArg (baseAlgebra g A).piece (hpq.degree_eq hm))))
    ((pullbackFunctor (ringedSpaceHom (f' ≫ g))).map
      (eqToHom (congrArg A.piece (hpq.degree_eq hm))))
    (compComparison f' g (A.piece (q * d'))) (hψ p q hpq)
    (compComparison_comp_eqToHom g f' A (hpq.degree_eq hm))

/-- **The base change of [Stacks, Tag 01NT] commutes with the transition `F_d → F_{a d}` on
quadruples, up to strict equivalence.** -/
theorem strictlyEquivalent_baseChangeUp_scale (P : Quadruple f' (baseAlgebra g A) d) {a : ℤ}
    (ha : 0 < a) :
    StrictlyEquivalent ((P.scale ha).baseChangeUp g f' A (a * d))
      ((P.baseChangeUp g f' A d).scale ha) :=
  strictlyEquivalent_of_compatibleAt_one
    ((P.compatibleAt_scale ha).baseChangeUp g f' A)
    ((P.baseChangeUp g f' A d).compatibleAt_scale ha)

end Quadruple

/-! ### The two halves of the inverse of the chart-wise class -/

/-- **The transport along a unital homomorphism commutes with the transition `F_d → F_{a d}`.**
On classes of quadruples this is `Quadruple.strictlyEquivalent_algebraTransport_scale`. -/
theorem Fd.algebraTransport_scale {T X : Scheme.{u}}
    {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)} {d : ℤ}
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (hiso : ∀ n : ℤ, IsIso (Φ.app n))
    {a : ℤ} (ha : 0 < a) (ξ : Fd B d T) :
    Fd.algebraTransport Φ hiso (a * d) (Fd.scale ha ξ)
      = Fd.scale ha (Fd.algebraTransport Φ hiso d ξ) := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quotient.ind with
  | _ P =>
    exact (Fd.mk_eq_mk_iff (Quadruple.algebraTransport Φ hiso (P.scale ha))
        ((Quadruple.algebraTransport Φ hiso P).scale ha)).mpr
      (Quadruple.strictlyEquivalent_algebraTransport_scale Φ hiso P ha)

/-- **The comparison of the two spellings of the restriction commutes with the transition
`F_d → F_{a d}`**, being an instance of `Fd.algebraTransport`. -/
theorem Fd.restrictPullbackEquiv_scale {S X : Scheme.{u}} (A : SheafGradedAlgebra S)
    (f : X ⟶ S) [IsOpenImmersion f] {d a : ℤ} (ha : 0 < a) (T : Scheme.{u})
    (ξ : Fd (situationAlgebra (A.restrict f)) d T) :
    Fd.restrictPullbackEquiv A f (a * d) T (Fd.scale ha ξ)
      = Fd.scale ha (Fd.restrictPullbackEquiv A f d T ξ) :=
  Fd.algebraTransport_scale (restrictPullbackUnitalHom A f)
    (isIso_restrictPullbackUnitalHom_app_forall A f) ha ξ

/-- **The base change of [Stacks, Tag 01NT] commutes with the transition `F_d → F_{a d}`.** On
classes of quadruples this is `Quadruple.strictlyEquivalent_baseChangeUp_scale`. -/
theorem Fd.baseChangeUp_scale {S S' T : Scheme.{u}} (g : S' ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) {d a : ℤ}
    (ha : 0 < a) (ξ : Fd (baseAlgebra g A) d T) :
    Fd.baseChangeUp g A (a * d) (Fd.scale ha ξ)
      = Fd.scale ha (Fd.baseChangeUp g A d ξ) := by
  obtain ⟨f', q⟩ := ξ
  induction q using Quotient.ind with
  | _ P =>
    exact (Fd.mk_eq_mk_iff ((P.scale ha).baseChangeUp g f' A (a * d))
        ((P.baseChangeUp g f' A d).scale ha)).mpr
      (Quadruple.strictlyEquivalent_baseChangeUp_scale g f' A P ha)

/-! ### The inverse of the chart-wise class -/

/-- **The inverse of the chart-wise class commutes with the transition `F_d → F_{a d}`.** Both
halves of `...RelativeProjQcohSheaf.Fd.chartClassInv` do:
`Fd.restrictPullbackEquiv_scale` and `Fd.baseChangeUp_scale`.

This is the compatibility `equiv_scale` of a `...RelativeProjQcohSheaf.ProjDegreeRepresentation`
over a general base consumes alongside the chart-wise Veronese computation
`...RelativeProjQcohSheaf.Fd.chartHom_scale`. -/
theorem Fd.chartClassInv_scale {S : Scheme.{u}} (A : SheafGradedAlgebra S) (V : S.Opens)
    {k a : ℤ} (ha : 0 < a) {T : Scheme.{u}}
    (η : Fd (situationAlgebra (A.restrict V.ι)) k T) :
    Fd.chartClassInv A V (Fd.scale ha η) = Fd.scale ha (Fd.chartClassInv A V η) := by
  rw [Fd.chartClassInv, Fd.chartClassInv, Fd.restrictPullbackEquiv_scale A V.ι ha T η]
  exact Fd.baseChangeUp_scale V.ι (situationAlgebra A) ha _

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
