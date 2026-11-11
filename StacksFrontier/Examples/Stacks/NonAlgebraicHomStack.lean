module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.Artin.FormalObject

/-!
# The example of a non-algebraic Hom-stack

Let `k` be an algebraically closed field which is not the algebraic closure of a finite
field, let `S = Spec k⟦t⟧` and let `Sₙ ⊆ S` be the thickenings of the closed point. Let
`f : X ⟶ S` be projective and flat with geometrically connected curves as fibres, with `X`
regular and with special fibre `X₀ = X ×_S S₀` a nodal curve whose irreducible components
are smooth and whose dual graph has a loop of rational curves. Let `A₀` be a non-zero
abelian variety over `k` and let `A = A₀ ×_{Spec k} S` be the constant abelian scheme.
The Hom-stack `𝒳 = Mor_S(X, [S/A])` has fibre category over an `S`-scheme `T` the groupoid
of fppf `A₀`-torsors on `X ×_S T`, so that the isomorphism classes of `𝒳(T)` are
`H¹_fppf(X ×_S T, A)`. The source's proof of the failure of essential surjectivity of
`𝒳(S) ⟶ lim 𝒳(Sₙ)` reduces, by that computation, to the failure of surjectivity of

  `H¹_fppf(X, A) ⟶ lim H¹_fppf(Xₙ, A)`,   `Xₙ = X ×_S Sₙ`,

and this file proves that reduction, from the three inputs the source isolates: `H¹(X, A)`
is torsion, the maps `H¹(X_{n+1}, A) ⟶ H¹(Xₙ, A)` are surjective, and `H¹(X₀, A)` is not
torsion. It also proves the deduction of non-algebraicity from the failure of essential
surjectivity, through Stacks 07X8.

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.exists_compatible_notMem_range` is the obstruction
  in pure form: in an inverse system of abelian groups with surjective transition maps,
  receiving compatible maps from a torsion group, a non-torsion element of the bottom group
  lifts to a compatible system that is in the image of no element.
* `Stacks.Examples.NonAlgebraicHomStack.exists_compatible_ne_restrictTotal` and
  `Stacks.Examples.NonAlgebraicHomStack.not_surjective_toCompatibleSystems` are the source's
  reduction of Stacks 0AFB: from the three inputs above, a compatible system of classes on the
  thickenings `Xₙ` which is not the restriction of a class on `X`, and the resulting failure of
  surjectivity of the comparison map onto the inverse limit.
* `Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_of_not_essSurj_approximationFunctor`,
  `Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_of_exists_not_isEffective` and
  `Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_powerSeriesBase` are the source's
  deduction of Stacks 0AFC, for a category over the big fppf site with arbitrary universes, with
  Stacks 07X8 at those universes as the hypothesis `h07X8`. The same deductions at the universes
  of the 2-category of algebraic stacks, where 07X8 is proved
  (`Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks`), are in
  `StacksFrontier.Examples.Stacks.HomStackAlgebraicStackUniverses`.

## Where Stacks 0AFB and 0AFC are proved

The three inputs are proved for the standing data of Section 0AF8
(`Stacks.Examples.NonAlgebraicHomStack.Situation`):

* `htorsion` is `Stacks.Examples.NonAlgebraicHomStack.isAddTorsion_H1_totalObj`, from Stacks 0AF9
  and Stacks 0AFA, `X` being a regular integral Noetherian surface
  (`StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.SituationGeometry`);
* `hsurjective`, the source's part (b), is
  `Stacks.Examples.NonAlgebraicHomStack.surjective_restrictSucc_pointsSheaf`;
* `hnotTorsion`, the source's part (a), is
  `Stacks.Examples.NonAlgebraicHomStack.not_isAddTorsion_H1_specialFibre`.

The Hom-stack `Mor_S(X, 𝒵)` is `AlgebraicGeometry.Stack.homStack`, and the passage from the
non-surjectivity on `H¹` to a formal object of `Mor_S(X, 𝒵)` which is not effective is
`StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.FormalObjects`, for any `𝒵` fibred in groupoids
with a classifying invariant with values in `H¹(-, A)`; for `[S/A]` that invariant is
`StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.ClassifyingStack`. Stacks 0AFB and Stacks 0AFC
themselves, for `Mor_S(X, [S/A])` in the situation of Section 0AF8, are
`Stacks.Examples.NonAlgebraicHomStack.Situation.exists_not_restriction_homStackClassifyingStack`
and `Stacks.Examples.NonAlgebraicHomStack.Situation.not_isAlgebraicStack_homStackClassifyingStack`
in `StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.Main`.

## The witness

The compatible system produced by `exists_compatible_ne_restrictTotal` is *constructed*: its
level `0` is the given non-torsion class, and each next level is a chosen preimage under the
surjection of the level below it, so the whole tower is built by recursion out of the two
hypotheses. The obstruction to it coming from `X` is then that its level `0` has infinite
order while the restriction of any class on `X` has finite order.

The theorems of this file are stated for an arbitrary family `X ⟶ S` and abelian sheaf `A`,
with the three inputs as hypotheses; the fixed data is the base `S = Spec k⟦t⟧`, the family
`f : X ⟶ S`, the tower of thickenings `Xₙ = X ×_S Sₙ` with its maps to `X`, and the abelian sheaf
`A` on the big fppf site over `S`.

## Implementation notes

Cohomology is Mathlib's `CategoryTheory.Sheaf.H'`, the degree-`n` sheaf cohomology of an object
of a site with values in an abelian sheaf, which is a presheaf on the site; the restriction maps
along `Xₙ ⟶ X` and `Xₙ ⟶ X_{n+1}` are therefore its functoriality and need no further input.
The thickenings are the adic base changes of `StacksFrontier.AlgebraicGeometry.Algebraization`,
whose index `n` is cut out by the `(n+1)`-st power of `(t)`. Index `0` is therefore
`X ×_S Spec k`, the special fibre, which is the source's `X₀` and the group carrying its
part (a); against the source's displayed formula `Sₙ = Spec (k[t]/(tⁿ))` the indexing is
shifted by one, and neither the tower nor its limit is affected by the shift.

The inverse limit is the explicit group of compatible systems, a subtype of the product; this
keeps the system that is not in the image visible in the statement.

The last section uses the library's own notions: `AlgebraicGeometry.Stack.IsAlgebraicStack` for
Stacks 026O, `Deformation.Artin.approximationFunctor` for the comparison functor of Stacks 07X6
and `Deformation.Artin.FormalObject.IsEffective` for Stacks 07X7. Since `IsAlgebraicStack` is an
existential over the fibred-in-groupoids property, which is a `Prop`, the proof `hp` of that
property taken as a hypothesis there and the one produced by the algebraicity hypothesis agree,
so the comparison functor appearing in the hypotheses is the one appearing in the conclusion.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Tag 0AFC](https://stacks.math.columbia.edu/tag/0AFC)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Section 0AF8](https://stacks.math.columbia.edu/tag/0AF8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w v t

namespace Stacks.Examples.NonAlgebraicHomStack

/-! ### The obstruction in an inverse system of abelian groups -/

/-- In an inverse system of abelian groups `G` with surjective transition maps `t`, receiving
compatible maps `r` from a torsion abelian group `H`, an element `x₀` of infinite order in
`G 0` lifts to a compatible system which is the image of no element of `H`.

The system is built by recursion: level `0` is `x₀` and each next level is a preimage of the
level below it. It is in the image of no element of `H` already at level `0`, because the
image of an element of finite order has finite order. -/
public theorem exists_compatible_notMem_range {H : Type*} [AddCommGroup H]
    {G : ℕ → Type*} [∀ n, AddCommGroup (G n)]
    (t : ∀ n, G (n + 1) →+ G n) (r : ∀ n, H →+ G n)
    (hsurjective : ∀ n, Function.Surjective (t n))
    (htorsion : IsAddTorsion H)
    {x₀ : G 0} (hx₀ : ¬ IsOfFinAddOrder x₀) :
    ∃ s : ∀ n, G n, s 0 = x₀ ∧ (∀ n, t n (s (n + 1)) = s n) ∧
      ∀ h : H, ∃ n, r n h ≠ s n := by
  classical
  refine ⟨fun n => Nat.rec x₀ (fun n y => Function.surjInv (hsurjective n) y) n, rfl,
    fun n => Function.surjInv_eq (hsurjective n) _, fun h => ⟨0, fun hcon => hx₀ ?_⟩⟩
  have h0 : r 0 h = x₀ := hcon
  exact h0 ▸ (r 0).isOfFinAddOrder (htorsion h)

/-! ### The base, the family and the tower of thickenings -/

/-- The base `S = Spec k⟦t⟧` of the family of curves. -/
public abbrev base (k : Type u) [Field k] : Scheme.{u} := Spec (.of (PowerSeries k))

/-- The ideal `(t) ⊆ k⟦t⟧`, whose powers cut out the thickenings `Sₙ ⊆ S` of the closed
point. -/
public abbrev uniformizer (k : Type u) [Field k] : Ideal (PowerSeries k) :=
  Ideal.span {PowerSeries.X}

section Family

variable {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ base k)

/-- The thickening `Xₙ = X ×_S Sₙ` of the special fibre, with `Sₙ = Spec (k⟦t⟧ / (tⁿ⁺¹))`. -/
public abbrev thickening (n : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.adicBaseChange (PowerSeries k) (uniformizer k) fX n

/-- The canonical morphism `Xₙ ⟶ X`. -/
public abbrev thickeningToTotal (n : ℕ) : thickening fX n ⟶ X :=
  pullback.fst fX (AlgebraicGeometry.adicThickeningι (PowerSeries k) (uniformizer k) n)

/-- The transition `Xₙ ⟶ X_{n+1}` of the tower of thickenings. -/
public abbrev thickeningSucc (n : ℕ) : thickening fX n ⟶ thickening fX (n + 1) :=
  AlgebraicGeometry.adicBaseChangeSucc (PowerSeries k) (uniformizer k) fX n

/-- The tower of thickenings is compatible with the morphisms to `X`. -/
@[reassoc]
public lemma thickeningSucc_toTotal (n : ℕ) :
    thickeningSucc fX n ≫ thickeningToTotal fX (n + 1) = thickeningToTotal fX n :=
  pullback.lift_fst _ _ _

end Family

/-! ### `X` and its thickenings as objects of the big fppf site over `S` -/

section Site

variable {k : Type u} [Field k] (B : AlgebraicGeometry.BigFppfSite.{u})
  (hS : B.Contains (base k)) {X : Scheme.{u}} (fX : X ⟶ base k) (hX : B.Contains X)
  (hXn : ∀ n, B.Contains (thickening fX n))

/-- `X`, as an object of the big fppf site over `S`. -/
public def totalObj : AlgebraicGeometry.BigFppfOver B (base k) hS :=
  Over.mk (Y := B.obj hX) (ObjectProperty.homMk fX)

/-- `Xₙ`, as an object of the big fppf site over `S`. -/
public def thickeningObj (n : ℕ) : AlgebraicGeometry.BigFppfOver B (base k) hS :=
  Over.mk (Y := B.obj (hXn n)) (ObjectProperty.homMk (thickeningToTotal fX n ≫ fX))

/-- The canonical morphism `Xₙ ⟶ X` of the big fppf site over `S`. -/
public def thickeningObjToTotal (n : ℕ) :
    thickeningObj B hS fX hXn n ⟶ totalObj B hS fX hX := by
  refine Over.homMk (ObjectProperty.homMk (X := B.obj (hXn n)) (Y := B.obj hX)
    (thickeningToTotal fX n)) ?_
  apply ObjectProperty.hom_ext
  rfl

/-- The transition `Xₙ ⟶ X_{n+1}` of the big fppf site over `S`. -/
public def thickeningObjSucc (n : ℕ) :
    thickeningObj B hS fX hXn n ⟶ thickeningObj B hS fX hXn (n + 1) := by
  refine Over.homMk (ObjectProperty.homMk (X := B.obj (hXn n)) (Y := B.obj (hXn (n + 1)))
    (thickeningSucc fX n)) ?_
  apply ObjectProperty.hom_ext
  change thickeningSucc fX n ≫ thickeningToTotal fX (n + 1) ≫ fX = thickeningToTotal fX n ≫ fX
  rw [← Category.assoc, thickeningSucc_toTotal]

/-- The tower of thickenings in the site is compatible with the morphisms to `X`. -/
public lemma thickeningObjSucc_toTotal (n : ℕ) :
    thickeningObjSucc B hS fX hXn n ≫ thickeningObjToTotal B hS fX hX hXn (n + 1) =
      thickeningObjToTotal B hS fX hX hXn n := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact thickeningSucc_toTotal fX n

/-! ### The comparison map on first fppf cohomology -/

variable
  [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B (base k) hS)
    AddCommGrpCat.{u})]
  (𝒜 : Sheaf (AlgebraicGeometry.BigFppfOver.topology B (base k) hS) AddCommGrpCat.{u})

/-- The restriction `H¹(X, A) ⟶ H¹(Xₙ, A)` along `Xₙ ⟶ X`. -/
public def restrictTotal (n : ℕ) :
    Sheaf.H' 𝒜 1 (totalObj B hS fX hX) →+
      Sheaf.H' 𝒜 1 (thickeningObj B hS fX hXn n) :=
  ((𝒜.cohomologyPresheaf 1).map (thickeningObjToTotal B hS fX hX hXn n).op).hom

/-- The restriction `H¹(X_{n+1}, A) ⟶ H¹(Xₙ, A)` along `Xₙ ⟶ X_{n+1}`. -/
public def restrictSucc (n : ℕ) :
    Sheaf.H' 𝒜 1 (thickeningObj B hS fX hXn (n + 1)) →+
      Sheaf.H' 𝒜 1 (thickeningObj B hS fX hXn n) :=
  ((𝒜.cohomologyPresheaf 1).map (thickeningObjSucc B hS fX hXn n).op).hom

/-- The restrictions of a class on `X` to the thickenings form a compatible system. -/
public lemma restrictSucc_restrictTotal (n : ℕ)
    (ξ : Sheaf.H' 𝒜 1 (totalObj B hS fX hX)) :
    restrictSucc B hS fX hXn 𝒜 n (restrictTotal B hS fX hX hXn 𝒜 (n + 1) ξ) =
      restrictTotal B hS fX hX hXn 𝒜 n ξ := by
  have h := congrArg (fun f => ((𝒜.cohomologyPresheaf 1).map f.op).hom ξ)
    (thickeningObjSucc_toTotal B hS fX hX hXn n)
  simpa only [restrictSucc, restrictTotal, op_comp, Functor.map_comp, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply] using h

/-- The group of compatible systems of classes on the thickenings: the inverse limit
`lim H¹(Xₙ, A)`. -/
public abbrev CompatibleSystem : Type w :=
  {s : ∀ n, Sheaf.H' 𝒜 1 (thickeningObj B hS fX hXn n) //
    ∀ n, restrictSucc B hS fX hXn 𝒜 n (s (n + 1)) = s n}

/-- The comparison map `H¹(X, A) ⟶ lim H¹(Xₙ, A)`. -/
public def toCompatibleSystems
    (ξ : Sheaf.H' 𝒜 1 (totalObj B hS fX hX)) :
    CompatibleSystem B hS fX hXn 𝒜 :=
  ⟨fun n => restrictTotal B hS fX hX hXn 𝒜 n ξ,
    fun n => restrictSucc_restrictTotal B hS fX hX hXn 𝒜 n ξ⟩

/-! ### Stacks 0AFB -/

/-- **The source's reduction of Stacks 0AFB.** For the example of a non-algebraic Hom-stack
over `S = Spec k⟦t⟧`, with `Xₙ = X ×_S Sₙ` the thickenings of the
special fibre and `A` the constant abelian scheme, there is a compatible system of classes
in `H¹_fppf(Xₙ, A)` which is the restriction of no class in `H¹_fppf(X, A)`.

The system is constructed: its level `0` is a class of infinite order, supplied by
`hnotTorsion`, and each next level is a preimage of the level below under the surjection of
`hsurjective`. No class on `X` restricts to it, because a class on `X` has finite order by
`htorsion` and hence so does its restriction to `X₀`. In the situation of Section 0AF8 the three
inputs are proved, see
`Stacks.Examples.NonAlgebraicHomStack.Situation.not_surjective_toCompatibleSystems`. -/
public theorem exists_compatible_ne_restrictTotal
    (htorsion : IsAddTorsion (Sheaf.H' 𝒜 1 (totalObj B hS fX hX)))
    (hsurjective : ∀ n, Function.Surjective (restrictSucc B hS fX hXn 𝒜 n))
    (hnotTorsion :
      ¬ IsAddTorsion (Sheaf.H' 𝒜 1 (thickeningObj B hS fX hXn 0))) :
    ∃ s : ∀ n, Sheaf.H' 𝒜 1 (thickeningObj B hS fX hXn n),
      (¬ IsOfFinAddOrder (s 0)) ∧
      (∀ n, restrictSucc B hS fX hXn 𝒜 n (s (n + 1)) = s n) ∧
      ∀ ξ : Sheaf.H' 𝒜 1 (totalObj B hS fX hX),
        ∃ n, restrictTotal B hS fX hX hXn 𝒜 n ξ ≠ s n := by
  obtain ⟨x₀, hx₀⟩ := not_isAddTorsion_iff _ |>.mp hnotTorsion
  obtain ⟨s, hs0, hstep, hout⟩ :=
    exists_compatible_notMem_range (restrictSucc B hS fX hXn 𝒜)
      (restrictTotal B hS fX hX hXn 𝒜) hsurjective htorsion hx₀
  exact ⟨s, hs0 ▸ hx₀, hstep, hout⟩

/-- **The source's reduction of Stacks 0AFB**: under the three inputs of its proof, the comparison
map `H¹_fppf(X, A) ⟶ lim H¹_fppf(Xₙ, A)` is not surjective. In the situation of Section 0AF8 the
inputs are proved, see
`Stacks.Examples.NonAlgebraicHomStack.Situation.not_surjective_toCompatibleSystems`. -/
public theorem not_surjective_toCompatibleSystems
    (htorsion : IsAddTorsion (Sheaf.H' 𝒜 1 (totalObj B hS fX hX)))
    (hsurjective : ∀ n, Function.Surjective (restrictSucc B hS fX hXn 𝒜 n))
    (hnotTorsion :
      ¬ IsAddTorsion (Sheaf.H' 𝒜 1 (thickeningObj B hS fX hXn 0))) :
    ¬ Function.Surjective (toCompatibleSystems B hS fX hX hXn 𝒜) := by
  obtain ⟨s, _, hstep, hout⟩ :=
    exists_compatible_ne_restrictTotal B hS fX hX hXn 𝒜 htorsion hsurjective hnotTorsion
  intro hsurj
  obtain ⟨ξ, hξ⟩ := hsurj ⟨s, hstep⟩
  obtain ⟨n, hn⟩ := hout ξ
  exact hn (congrFun (congrArg Subtype.val hξ) n)

end Site

/-! ### The deduction of Stacks 0AFC from Stacks 07X8 -/

section Algebraicity

/-- **The deduction of Stacks 0AFC**, as the source makes it, for an arbitrary category. Let `B`
be a big fppf site, `S` a locally Noetherian scheme in it and `𝒳` a category over the big fppf site
over `S` which is fibred in groupoids. Assume Stacks 07X8, as the hypothesis `h07X8`: every
algebraic stack over `S` has an equivalence for its comparison functor of Stacks 07X6, from
objects over a Noetherian complete local base to compatible systems over the infinitesimal
thickenings of its closed point. If that comparison functor is *not* essentially surjective for
`𝒳` — which is Stacks 0AFB for the source's `𝒳 = Mor_S(X, [S/A])` — then `𝒳` is not an
algebraic stack.

For the source's `𝒳`, Stacks 0AFC is
`Stacks.Examples.NonAlgebraicHomStack.Situation.not_isAlgebraicStack_homStackClassifyingStack`.
Stacks 07X8 is proved in this library,
`Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks`, for the objects of the
2-category `AlgebraicGeometry.Stack.AlgebraicStacks`, whose total categories have the universes
`{u, u + 1}`; here `𝒳` has arbitrary universes `{v, t}`, so 07X8 at those universes is the
hypothesis `h07X8`. At the universes `{u, u + 1}` the hypothesis is discharged in
`Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_of_not_essSurj`. -/
public theorem not_isAlgebraicStack_of_not_essSurj_approximationFunctor
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (𝒳 : CategoryTheory.BasedCategory.{v, t} (AlgebraicGeometry.BigFppfOver B S hS))
    (hp : 𝒳.p.IsFiberedInGroupoids)
    (h07X8 : ∀ 𝒴 : CategoryTheory.BasedCategory.{v, t}
        (AlgebraicGeometry.BigFppfOver B S hS),
        AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B S hS 𝒴 →
          ∀ hq : 𝒴.p.IsFiberedInGroupoids,
            (Deformation.Artin.approximationFunctor B S hS 𝒴.p hq).IsEquivalence)
    (h0AFB : ¬ (Deformation.Artin.approximationFunctor B S hS 𝒳.p hp).EssSurj) :
    ¬ AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B S hS 𝒳 :=
  fun h𝒳 => h0AFB (h07X8 𝒳 h𝒳 hp).essSurj

/-- **The deduction of Stacks 0AFC**, in the vocabulary of effective formal objects. Under
Stacks 07X8 as the
hypothesis `h07X8`, a category fibred in groupoids over the big fppf site of a locally
Noetherian base which has a formal object that is not effective, in the sense of Stacks 07X7,
is not an algebraic stack. This is the form in which the source's Remark 0AFD diagnoses the
example: "the problem is the non-effectivity of formal objects for `Mor_S(X, [S/A])`".

For the source's `𝒳`, Stacks 0AFC is
`Stacks.Examples.NonAlgebraicHomStack.Situation.not_isAlgebraicStack_homStackClassifyingStack`.
Stacks 07X8 is proved in this library,
`Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks`, for the objects of the
2-category `AlgebraicGeometry.Stack.AlgebraicStacks`, whose total categories have the universes
`{u, u + 1}`; here `𝒳` has arbitrary universes `{v, t}`, so 07X8 at those universes is the
hypothesis `h07X8`. At the universes `{u, u + 1}` the hypothesis is discharged in
`Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_of_not_essSurj`. -/
public theorem not_isAlgebraicStack_of_exists_not_isEffective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (𝒳 : CategoryTheory.BasedCategory.{v, t} (AlgebraicGeometry.BigFppfOver B S hS))
    (hp : 𝒳.p.IsFiberedInGroupoids)
    (h07X8 : ∀ 𝒴 : CategoryTheory.BasedCategory.{v, t}
        (AlgebraicGeometry.BigFppfOver B S hS),
        AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B S hS 𝒴 →
          ∀ hq : 𝒴.p.IsFiberedInGroupoids,
            (Deformation.Artin.approximationFunctor B S hS 𝒴.p hq).IsEquivalence)
    (h0AFB : ∃ ξ : Deformation.Artin.FormalObject B S hS 𝒳.p,
      ¬ Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.p hp ξ) :
    ¬ AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  intro h𝒳
  obtain ⟨ξ, hξ⟩ := h0AFB
  have := (h07X8 𝒳 h𝒳 hp).essSurj
  exact hξ (CategoryTheory.Functor.EssSurj.mem_essImage _ ξ)

/-- **The deduction of Stacks 0AFC** over the section's own base `S = Spec k⟦t⟧`. Under
Stacks 07X8 as the hypothesis `h07X8`, a category fibred in groupoids over the big fppf site over
`S` which has a formal object that is not effective is not an algebraic stack. For the source's
`𝒳 = Mor_S(X, [S/A])` this is
`Stacks.Examples.NonAlgebraicHomStack.Situation.not_isAlgebraicStack_homStackClassifyingStack`.
At the universes `{u, u + 1}` the hypothesis `h07X8` is discharged in
`Stacks.Examples.NonAlgebraicHomStack.not_isAlgebraicStack_powerSeriesBase_of_not_isEffective`.
See the module documentation. -/
public theorem not_isAlgebraicStack_powerSeriesBase
    {k : Type u} [Field k] (B : AlgebraicGeometry.BigFppfSite.{u})
    (hS : B.Contains (base k))
    (𝒳 : CategoryTheory.BasedCategory.{v, t} (AlgebraicGeometry.BigFppfOver B (base k) hS))
    (hp : 𝒳.p.IsFiberedInGroupoids)
    (h07X8 : ∀ 𝒴 : CategoryTheory.BasedCategory.{v, t}
        (AlgebraicGeometry.BigFppfOver B (base k) hS),
        AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B (base k) hS 𝒴 →
          ∀ hq : 𝒴.p.IsFiberedInGroupoids,
            (Deformation.Artin.approximationFunctor B (base k) hS 𝒴.p hq).IsEquivalence)
    (h0AFB : ∃ ξ : Deformation.Artin.FormalObject B (base k) hS 𝒳.p,
      ¬ Deformation.Artin.FormalObject.IsEffective B (base k) hS 𝒳.p hp ξ) :
    ¬ AlgebraicGeometry.Stack.IsAlgebraicStack.{u, w} B (base k) hS 𝒳 :=
  not_isAlgebraicStack_of_exists_not_isEffective B (base k) hS 𝒳 hp h07X8 h0AFB

end Algebraicity

end Stacks.Examples.NonAlgebraicHomStack

end
