module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDividedPowerForms

/-!
# The bigraded family `Ω^a_{D(b)}`, with its de Rham differential and its wedge product

The double complex `K^{a,b} = M ⊗̂_D Ω^a_{D(b)}` of [Stacks, Proposition 60.21.3, Tag 07LG] needs
the forms of the cosimplicial ring `D(*)` in *two* gradings at once: the cosimplicial degree `b`
and the exterior degree `a`.  This file builds the bigraded family, its de Rham differential
`Ω^a_{D(b)} → Ω^{a+1}_{D(b)}` and its wedge product from the exterior calculus of a *fixed*
divided power ring in
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDividedPowerForms.lean`.

## What the family is built from

A cosimplicial family of divided power `A`-algebras — `Crystalline.CosimplicialDPAlgebra`, whose
transition maps are divided power morphisms over `A` — is all the input needed.  The bigraded
family is then `Ω^a_{D(b)} = Crystalline.completedDividedPowerForms` of the `b`-th member, and:

* the de Rham differential in the `a` direction is
  `Crystalline.completedDividedPowerDeRham`, with `d ∘ d = 0` and the Leibniz rule already
  discharged for it by `Crystalline.isGradedExterior_completedDividedPower` and
  `Crystalline.isGradedLeibniz_completedDividedPower`;
* the wedge product is `Crystalline.completedDividedPowerWedgeMul` in general bidegree and
  `Crystalline.completedDividedPowerWedge` in the bidegree `(a, 1)` the de Rham complex is built
  from, the two bridged by `Crystalline.completedDividedPowerWedge_eq_wedgeMul`;
* the transition maps in the `b` direction are
  `Crystalline.completedMapDifferentialForms` of the divided power morphisms, and they commute
  with the de Rham differential and with the wedge by
  `Crystalline.completedMapDifferentialForms_deRham` and `..._wedge`.

So the two differentials of the double complex commute in each exterior degree.

## The shape of the forms

`Ω^a_{D(b)}` is here the `p`-adic completion of the `a`-th exterior power of the *uncompleted*
divided power differentials of the envelope.  That is the shape of
`Crystalline.completedDividedPowerForms`, hence the shape of the target complex
`M ⊗^∧_D Ω^*_D` of [Stacks, Tag 07LG] as
`Crystalline.completedDividedPowerDeRhamComplex` builds it, and the shape in which the exterior
calculus is proved.  It is **not** the shape of [Stacks, Lemma 60.19.1, Tag 07LA], whose
`Ω^i_{D(n)}` is the completion of the `i`-th exterior power of the *completed* differentials
`Crystalline.CosimplicialEnvelope.differentials`.  The two agree in each cosimplicial degree, by
`Crystalline.completedFormsShapeEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShape.lean`, for a positive
exterior degree — which is the only degree [Stacks, Tag 07LA] is about.  That comparison is
linear over the completed ring, by `Crystalline.completedFormsShapeEquiv_smul` of
`Cosimplicial/CompletedFormsShapeLinear.lean`.

## Main definitions

* `Crystalline.CosimplicialDPAlgebra` — a cosimplicial family of divided power `A`-algebras with
  divided power transition maps.
* `Crystalline.CosimplicialDPAlgebra.forms` — **the bigraded family `Ω^a_{D(b)}`**.
* `Crystalline.CosimplicialDPAlgebra.deRham` — **the de Rham differential
  `Ω^a_{D(b)} → Ω^{a+1}_{D(b)}` of the cosimplicial forms**.
* `Crystalline.CosimplicialDPAlgebra.wedgeMul` and `...wedge` — **the wedge product of the
  cosimplicial forms**, in general bidegree and in the bidegree the de Rham complex uses.
* `Crystalline.CosimplicialDPAlgebra.formsMap` — the transition maps in the `b` direction.

## Main results

* `Crystalline.CosimplicialDPAlgebra.formsMap_deRham` — **the transition maps commute with the de
  Rham differential**, which is the commutation of the two differentials of `K^{•,•}`.
* `Crystalline.CosimplicialDPAlgebra.formsMap_wedge` — and with the wedge product.
* `Crystalline.CosimplicialDPAlgebra.formsMap_id` and `...formsMap_comp` — the transition maps are
  functorial, so `b ↦ Ω^a_{D(b)}` really is cosimplicial in each exterior degree.
* `Crystalline.CosimplicialDPAlgebra.isGradedLeibniz` and `...isGradedExterior` — in each
  cosimplicial degree the forms satisfy the two conditions
  `Crystalline.CompletedDeRham.complexOfIsIntegrable` carries, so the de Rham complex of a module
  with connection over `D(b)` exists with no hypothesis about the forms.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public section

open CategoryTheory DividedPowers

universe u v

namespace Crystalline

/-! ### Functoriality of the comparison of completed forms -/

section Functoriality

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)

/-- **The comparison of completed forms along a divided power morphism which is the identity is
the identity.**  The hypothesis is that the morphism *equals* the identity rather than being it,
so that the lemma applies to a transition map of a cosimplicial family without a dependent
rewrite along the semilinearity. -/
public theorem completedMapDifferentialForms_eq_self (g : B →ₐ[A] B)
    (hg : DividedPowers.IsDPMorphism hJ hJ g.toRingHom) (hgid : g = AlgHom.id A B) (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    completedMapDifferentialForms p A hJ hJ g hg i x = x := by
  subst hgid
  exact adicCompletionMapₛₗ_id_apply _ _
    (mapDifferentialFormsOfDPMorphism_id (A := A) (J := J) (delta := hJ) i hg) x

variable {C : Type v} [CommRing C] [Algebra A C] {K : Ideal C} (epsilon : DividedPowers K)
  {D : Type v} [CommRing D] [Algebra A D] {L : Ideal D} (zeta : DividedPowers L)

/-- **The comparisons of completed forms along two composable divided power morphisms compose.**
As for the identity, the composite is only required to *equal* the composition. -/
public theorem completedMapDifferentialForms_eq_comp (f : B →ₐ[A] C) (g : C →ₐ[A] D)
    (h : B →ₐ[A] D) (hf : DividedPowers.IsDPMorphism hJ epsilon f.toRingHom)
    (hg : DividedPowers.IsDPMorphism epsilon zeta g.toRingHom)
    (hh : DividedPowers.IsDPMorphism hJ zeta h.toRingHom) (hcomp : h = g.comp f) (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    completedMapDifferentialForms p A hJ zeta h hh i x =
      completedMapDifferentialForms p A epsilon zeta g hg i
        (completedMapDifferentialForms p A hJ epsilon f hf i x) := by
  subst hcomp
  exact adicCompletionMapₛₗ_comp_apply _ _ _ _ _ _
    (mapDifferentialFormsOfDPMorphism_comp (A := A) (J := J) (delta := hJ) epsilon zeta f g
      hf hg hh i) x

end Functoriality

/-! ### Cosimplicial families of divided power algebras -/

/-- **A cosimplicial family of divided power `A`-algebras.**

This is the input the bigraded family `Ω^a_{D(b)}` is built from: a divided power `A`-algebra for
each cosimplicial degree, and for each map of finite ordinals an `A`-algebra map of the carriers
which is a divided power morphism.  The cosimplicial ring `D(*)` of
[Stacks, Equation 60.17.3, Tag 07JF] is one, its transition maps being divided power morphisms by
`Crystalline.cosimplicialEnvelopeRing_isDPMorphism`.

The carriers are the *uncompleted* rings: the `p`-adic completion is taken by
`Crystalline.CosimplicialDPAlgebra.forms`, which is what makes the forms the completion of the
exterior power rather than the exterior power of a completion. -/
public structure CosimplicialDPAlgebra (A : Type u) [CommRing A] where
  /-- The carrier of the cosimplicial degree `b`. -/
  carrier : ℕ → Type v
  /-- Each carrier is a commutative ring. -/
  [commRing : ∀ b, CommRing (carrier b)]
  /-- Each carrier is an `A`-algebra. -/
  [algebra : ∀ b, Algebra A (carrier b)]
  /-- The divided power ideal of the cosimplicial degree `b`. -/
  ideal : ∀ b, Ideal (carrier b)
  /-- The divided powers on that ideal. -/
  dividedPowers : ∀ b, DividedPowers (ideal b)
  /-- The transition `A`-algebra map of a map of finite ordinals. -/
  map {m n : SimplexCategory} : (m ⟶ n) → (carrier m.len →ₐ[A] carrier n.len)
  /-- Every transition map is a divided power morphism. -/
  map_isDPMorphism {m n : SimplexCategory} (φ : m ⟶ n) :
    DividedPowers.IsDPMorphism (dividedPowers m.len) (dividedPowers n.len) (map φ).toRingHom
  /-- The transition map of an identity is the identity. -/
  map_id (n : SimplexCategory) : map (𝟙 n) = AlgHom.id A (carrier n.len)
  /-- The transition maps compose. -/
  map_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) :
    map (φ ≫ ψ) = (map ψ).comp (map φ)

attribute [instance] CosimplicialDPAlgebra.commRing CosimplicialDPAlgebra.algebra

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-- **The bigraded family `Ω^a_{D(b)}`**: the `p`-adic completion of the `a`-th exterior power of
the divided power differentials of the cosimplicial degree `b`. -/
public abbrev forms (a b : ℕ) : Type v :=
  completedDividedPowerForms p A (E.dividedPowers b) a

/-- **The de Rham differential `Ω^a_{D(b)} → Ω^{a+1}_{D(b)}` of the cosimplicial forms.**  It is
additive and not linear — the Leibniz rule forbids it — and in each cosimplicial degree it is the
de Rham differential of `Crystalline.completedDividedPowerForms`. -/
public noncomputable def deRham (b a : ℕ) : E.forms p a b →+ E.forms p (a + 1) b :=
  completedDividedPowerDeRham p A (E.dividedPowers b) a

/-- **The bigraded wedge product `Ω^a_{D(b)} × Ω^{a'}_{D(b)} → Ω^{a+a'}_{D(b)}` of the
cosimplicial forms.** -/
public noncomputable def wedgeMul (b a a' : ℕ) :
    E.forms p a b →ₗ[completedDividedPowerRing p (B := E.carrier b)]
      E.forms p a' b →ₗ[completedDividedPowerRing p (B := E.carrier b)]
        E.forms p (a + a') b :=
  completedDividedPowerWedgeMul p A (E.dividedPowers b) a a'

/-- **The wedge product of the cosimplicial forms in the bidegree the de Rham complex is built
from**, `Ω^a_{D(b)} × Ω^1_{D(b)} → Ω^{a+1}_{D(b)}`.  It is the bidegree `(1, a)` case of
`Crystalline.CosimplicialDPAlgebra.wedgeMul`, by
`Crystalline.completedDividedPowerWedge_eq_wedgeMul`. -/
public noncomputable def wedge (b a : ℕ) :
    E.forms p a b →ₗ[completedDividedPowerRing p (B := E.carrier b)]
      E.forms p 1 b →ₗ[completedDividedPowerRing p (B := E.carrier b)]
        E.forms p (a + 1) b :=
  completedDividedPowerWedge p A (E.dividedPowers b) a

/-- The universal differential `d : D(b) → Ω^1_{D(b)}`. -/
public noncomputable def differential (b : ℕ) :
    completedDividedPowerRing p (B := E.carrier b) → E.forms p 1 b :=
  completedFormsDifferential p A (E.dividedPowers b)

/-- **The transition map `Ω^a_{D(m)} → Ω^a_{D(n)}` of the cosimplicial forms**, semilinear over
the transition map of the rings. -/
public noncomputable def formsMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) :
    E.forms p a m.len →ₛₗ[(E.map φ).toRingHom] E.forms p a n.len :=
  completedMapDifferentialForms p A (E.dividedPowers m.len) (E.dividedPowers n.len)
    (E.map φ) (E.map_isDPMorphism φ) a

/-- **The transition maps commute with the de Rham differential.**

This is the commutation of the two differentials of the double complex
`K^{a,b} = M ⊗̂_D Ω^a_{D(b)}`, in each exterior degree: the `b` direction moves along `formsMap`
and the `a` direction along `deRham`, and the square commutes. -/
public theorem formsMap_deRham {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (x : E.forms p a m.len) :
    E.formsMap p φ (a + 1) (E.deRham p m.len a x) = E.deRham p n.len a (E.formsMap p φ a x) :=
  completedMapDifferentialForms_deRham p A (E.dividedPowers m.len) (E.dividedPowers n.len)
    (E.map φ) (E.map_isDPMorphism φ) a x

/-- **The transition maps respect the wedge product.** -/
public theorem formsMap_wedge {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (x : E.forms p a m.len) (y : E.forms p 1 m.len) :
    E.formsMap p φ (a + 1) (E.wedge p m.len a x y) =
      E.wedge p n.len a (E.formsMap p φ a x) (E.formsMap p φ 1 y) :=
  completedMapDifferentialForms_wedge p A (E.dividedPowers m.len) (E.dividedPowers n.len)
    (E.map φ) (E.map_isDPMorphism φ) a x y

/-- The transition map of an identity is the identity, so `b ↦ Ω^a_{D(b)}` is a cosimplicial
object in each exterior degree. -/
public theorem formsMap_id (n : SimplexCategory) (a : ℕ) (x : E.forms p a n.len) :
    E.formsMap p (𝟙 n) a x = x :=
  completedMapDifferentialForms_eq_self p A (E.dividedPowers n.len) (E.map (𝟙 n))
    (E.map_isDPMorphism (𝟙 n)) (E.map_id n) a x

/-- The transition maps compose. -/
public theorem formsMap_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) (a : ℕ)
    (x : E.forms p a m.len) :
    E.formsMap p (φ ≫ ψ) a x = E.formsMap p ψ a (E.formsMap p φ a x) :=
  completedMapDifferentialForms_eq_comp p A (E.dividedPowers m.len) (E.dividedPowers n.len)
    (E.dividedPowers k.len) (E.map φ) (E.map ψ) (E.map (φ ≫ ψ)) (E.map_isDPMorphism φ)
    (E.map_isDPMorphism ψ) (E.map_isDPMorphism (φ ≫ ψ)) (E.map_comp φ ψ) a x

/-- **The Leibniz rule for the cosimplicial forms, in each cosimplicial degree.**  This is the
hypothesis `Crystalline.CompletedDeRham.IsGradedLeibniz` of the completed de Rham complex,
discharged. -/
public theorem isGradedLeibniz (b : ℕ) :
    CompletedDeRham.IsGradedLeibniz (completedDividedPowerRing p (B := E.carrier b))
      (fun a => E.forms p a b) (E.wedge p b) (E.deRham p b) (E.differential p b) :=
  isGradedLeibniz_completedDividedPower p A (E.dividedPowers b)

/-- **The exterior identities for the cosimplicial forms, in each cosimplicial degree**: the de
Rham differential squares to zero, the wedge is alternating on one-forms, and the graded Leibniz
rule holds against a closed one-form.  This is the hypothesis
`Crystalline.CompletedDeRham.IsGradedExterior`, discharged. -/
public theorem isGradedExterior (b : ℕ) :
    CompletedDeRham.IsGradedExterior (completedDividedPowerRing p (B := E.carrier b))
      (fun a => E.forms p a b) (E.wedge p b) (E.deRham p b) :=
  isGradedExterior_completedDividedPower p A (E.dividedPowers b)

/-- **The wedge product of the cosimplicial forms used by the de Rham complex is the bigraded one
in bidegree `(1, a)`.** -/
public theorem wedge_eq_wedgeMul (b a : ℕ) (x : E.forms p a b) (y : E.forms p 1 b) :
    E.wedge p b a x y =
      AdicCompletion.map (pAdicIdeal (A := E.carrier b) p)
        (exteriorPower.degCongr (R := E.carrier b)
          (M := dividedPowerDifferentials (A := A) (E.dividedPowers b))
          (Nat.add_comm 1 a)).toLinearMap (E.wedgeMul p b 1 a y x) :=
  completedDividedPowerWedge_eq_wedgeMul p A (E.dividedPowers b) a x y

end CosimplicialDPAlgebra

end Crystalline

end
