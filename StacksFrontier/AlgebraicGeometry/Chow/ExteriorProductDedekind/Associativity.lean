module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.ChowGroups
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow

/-!
# Associativity of the exterior product over a Dedekind base

Stacks 0FC8 says that the exterior product of section 42.63 is associative: for `(S, δ)` as in
that section and `X`, `Y`, `Z` locally of finite type over `S`,

  `(α × β) × γ = α × (β × γ)`  in  `CH_*(X ×_S Y ×_S Z)`

for `α ∈ CH_*(X)`, `β ∈ CH_*(Y)`, `γ ∈ CH_*(Z)`. The source's proof is "Omitted. Hint:
associativity of fibre product of schemes."

Writing this down takes two identifications that the informal statement suppresses, and this
file supplies both.

* The two sides live on **different schemes**. With the chosen categorical fibre products they
  are `(X ×_S Y) ×_S Z` and `X ×_S (Y ×_S Z)`, canonically isomorphic but not equal, so the
  identity has to be transported along that isomorphism — this is the "associativity of fibre
  product" of the hint. `Stacks.Chow.tripleFibreProductAssoc` is the isomorphism, and
  `Stacks.Chow.tripleFibreProductAssoc_hom_structureMorphism` checks it lies over `S` for the
  structure morphisms the exterior product actually uses, so that proper pushforward along it is
  defined.
* The two sides live in **different delta-dimensions as written**: iterating the Dedekind rule
  gives `(n + m - 1) + l - 1` on the left and `n + (m + l - 1) - 1` on the right. These are the
  same integer, `n + m + l - 2`, but not the same term;
  `Stacks.Chow.exteriorProductDedekind_degree_assoc` is the equality, used as a transport.

## What is proved and what is assumed

What is **not** proved here is the cycle-level identity itself. Both sides of it are sums over
pairs of components with multiplicities read off a fibre product of reduced point closures
(`Stacks.Chow.exteriorProductDedekindTerm`), and the left side nests those multiplicities
through `X ×_S Y` while the right side nests them through `Y ×_S Z`. Equating them is the
statement that the multiplicity of a point in a triple fibre product factors as a product of
multiplicities in the two iterated double products — a length computation in the spirit of
Stacks 02M1, which this repository does not have in a form applicable to a fibre product of
three point closures. The associativity of the fibre product of *schemes*, which is the only
thing the source's hint asks for, is proved; it is not by itself enough to move the
multiplicities around.

So the cycle-level identity is carried as the hypothesis
`Stacks.Chow.IsExteriorProductDedekindAssociative`, and what is proved is that it implies the
identity on Chow groups — together with the two identifications above, which are what make
either statement well formed at all.

## Main definitions

* `Stacks.Chow.tripleFibreProductAssoc` — the associator `(X ×_S Y) ×_S Z ≅ X ×_S (Y ×_S Z)`.
* `Stacks.Chow.IsExteriorProductDedekindAssociative` — the cycle-level associativity identity,
  transported along the associator.

## Main results

* `Stacks.Chow.tripleFibreProductAssoc_hom_structureMorphism` — the associator lies over the
  base for the structure morphisms the exterior product uses.
* `Stacks.Chow.tripleFibreProductAssoc_hom_fst`,
  `Stacks.Chow.tripleFibreProductAssoc_hom_snd_fst`,
  `Stacks.Chow.tripleFibreProductAssoc_hom_snd_snd` — the associator matches the three
  projections to `X`, `Y` and `Z`.
* `Stacks.Chow.exteriorProductDedekind_degree_assoc` — the two iterated delta-dimensions agree.
* `Stacks.Chow.exteriorProductDedekindChow_assoc` — **Stacks 0FC8**, associativity on Chow
  groups, given the cycle-level identity.

## Implementation notes

The associator is built from Mathlib's `CategoryTheory.Limits.pullbackAssoc`, precomposed with
`CategoryTheory.Limits.pullback.congrHom` applied to `pullback.condition`: the structure
morphism of `X ×_S Y` used throughout this development is `pullback.fst f g ≫ f`, while
`pullbackAssoc` is stated for `pullback.snd f g ≫ g`, and those two morphisms are equal by the
cartesian square but not syntactically so.

An isomorphism of schemes is proper, so `Stacks.Chow.properPushforward` transports cycles along
the associator with no extra hypothesis; on Chow groups
`Stacks.Chow.properChowPushforward` additionally takes the Stacks 02S2 hypothesis, which is
threaded, as everywhere in this repository.

## References

* [Stacks Project, Tag 0FC8](https://stacks.math.columbia.edu/tag/0FC8)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The associator of a triple fibre product -/

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The associativity isomorphism `(X ×_S Y) ×_S Z ≅ X ×_S (Y ×_S Z)` of fibre products over the
base, written for the structure morphisms `pullback.fst f g ≫ f` and `pullback.fst g h ≫ g` that
the exterior product uses on the two double products.

This is the "associativity of fibre product of schemes" that the proof of Stacks 0FC8 appeals
to. -/
def tripleFibreProductAssoc :
    (pullback (pullback.fst f g ≫ f) h : Scheme.{u}) ≅
      (pullback f (pullback.fst g h ≫ g) : Scheme.{u}) :=
  (pullback.congrHom (pullback.condition (f := f) (g := g)) rfl).trans (pullbackAssoc f g g h)

/-- The first projection of a pullback, followed by any `k`, is unchanged by the canonical
isomorphism comparing two pullbacks along equal morphisms. -/
private theorem congrHom_hom_comp_fst_comp {C : Type u} [Category C] {A B D : C} {f₁ f₂ : A ⟶ D}
    {q : B ⟶ D} {W : C} (k : A ⟶ W) (h₁ : f₁ = f₂) [HasPullback f₁ q] [HasPullback f₂ q] :
    (pullback.congrHom h₁ rfl).hom ≫ pullback.fst f₂ q ≫ k = pullback.fst f₁ q ≫ k := by
  rw [← Category.assoc, pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The associator matches the projection to `X`. -/
@[simp]
theorem tripleFibreProductAssoc_hom_fst :
    (tripleFibreProductAssoc f g h).hom ≫ pullback.fst f (pullback.fst g h ≫ g) =
      pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g := by
  simp [tripleFibreProductAssoc, -pullback.congrHom_hom, congrHom_hom_comp_fst_comp]

/-- The associator matches the projection to `Y`. -/
@[simp]
theorem tripleFibreProductAssoc_hom_snd_fst :
    (tripleFibreProductAssoc f g h).hom ≫ pullback.snd f (pullback.fst g h ≫ g) ≫
        pullback.fst g h =
      pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.snd f g := by
  simp [tripleFibreProductAssoc, -pullback.congrHom_hom, congrHom_hom_comp_fst_comp]

/-- The associator matches the projection to `Z`. -/
@[simp]
theorem tripleFibreProductAssoc_hom_snd_snd :
    (tripleFibreProductAssoc f g h).hom ≫ pullback.snd f (pullback.fst g h ≫ g) ≫
        pullback.snd g h =
      pullback.snd (pullback.fst f g ≫ f) h := by
  rw [tripleFibreProductAssoc, Iso.trans_hom, Category.assoc, pullbackAssoc_hom_snd_snd,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The associator lies over the base: it carries the structure morphism of `X ×_S (Y ×_S Z)`
back to the structure morphism of `(X ×_S Y) ×_S Z`. This is what makes proper pushforward
along the associator a map of cycle groups over the base situation. -/
theorem tripleFibreProductAssoc_hom_structureMorphism :
    (tripleFibreProductAssoc f g h).hom ≫ (pullback.fst f (pullback.fst g h ≫ g) ≫ f) =
      pullback.fst (pullback.fst f g ≫ f) h ≫ (pullback.fst f g ≫ f) := by
  rw [← Category.assoc, tripleFibreProductAssoc_hom_fst, Category.assoc]

/-! ### The two iterated delta-dimensions -/

/-- Iterating the Dedekind rule gives `(n + m - 1) + l - 1` on one side and
`n + (m + l - 1) - 1` on the other; both are `n + m + l - 2`. -/
theorem exteriorProductDedekind_degree_assoc (n m l : ℤ) :
    n + m - 1 + l - 1 = n + (m + l - 1) - 1 := by
  ring

/-! ### Associativity -/

/-- Two cycles on one scheme whose underlying algebraic cycles agree have the same class in the
Chow group, after transport along the equality of their delta-dimensions. -/
private theorem mk_cast_eq_mk_of_val_eq {C : ChowSituation.{u}} {P : Scheme.{u}} (q : P ⟶ C.S)
    [LocallyOfFiniteType q] {i j : ℤ} (hij : i = j) (x : CycleGroup C q i)
    (y : CycleGroup C q j) (hxy : x.1 = y.1) :
    hij ▸ (QuotientAddGroup.mk' (rationalEquivalences C q i) x) =
      QuotientAddGroup.mk' (rationalEquivalences C q j) y := by
  cases hij
  exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C q i)) (Subtype.ext hxy)

variable (C : ChowSituation.{u}) (f' : X ⟶ C.S) [LocallyOfFiniteType f'] (g' : Y ⟶ C.S)
  [LocallyOfFiniteType g'] (h' : Z ⟶ C.S) [LocallyOfFiniteType h'] (n m l : ℤ)

/-- The cycle-level associativity of the exterior product over a Dedekind base: pushing the
iterated product `(α × β) × γ` forward along the associator gives `α × (β × γ)`.

Stated as an equality of the underlying algebraic cycles on `X ×_S (Y ×_S Z)`, since the two
sides are written in the delta-dimensions `(n + m - 1) + l - 1` and `n + (m + l - 1) - 1`, which
are the same integer but not the same term.

This is the identity the source leaves to "associativity of fibre product of schemes". It is
not proved in this repository: it needs the multiplicity of a point of a triple fibre product to
factor as a product of multiplicities in the two iterated double products. -/
def IsExteriorProductDedekindAssociative : Prop :=
  ∀ (α : CycleGroup C f' n) (β : CycleGroup C g' m) (γ : CycleGroup C h' l),
    (properPushforward C
        (pullback.fst (pullback.fst f' g' ≫ f') h' ≫ (pullback.fst f' g' ≫ f'))
        (pullback.fst f' (pullback.fst g' h' ≫ g') ≫ f')
        (tripleFibreProductAssoc f' g' h').hom
        (tripleFibreProductAssoc_hom_structureMorphism f' g' h')
        (n + m - 1 + l - 1)
        (exteriorProductDedekindCycles C (pullback.fst f' g' ≫ f') h' (n + m - 1) l
          (exteriorProductDedekindCycles C f' g' n m α β) γ)).1 =
      (exteriorProductDedekindCycles C f' (pullback.fst g' h' ≫ g') n (m + l - 1) α
        (exteriorProductDedekindCycles C g' h' m l β γ)).1

/-- **Stacks 0FC8.** Associativity of the exterior product over a Dedekind base, on Chow
groups: for Chow classes `a`, `b`, `c` the two iterated exterior products agree after transport
along the associator of the triple fibre product and along the equality of the two iterated
delta-dimensions.

Proved from the cycle-level identity `hassoc`, which is the step the source leaves to
"associativity of fibre product of schemes"; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.Associativity` for why that step is
not formal. The remaining hypotheses are the Stacks 0FC4 descent conditions for the three
exterior products involved and the Stacks 02S2 condition for the pushforward along the
associator, exactly as everywhere else in this repository. -/
@[stacks 0FC8 "associativity on Chow groups, together with the associator of the triple fibre \
product over the base and the agreement of the two iterated delta-dimensions; the cycle-level \
identity is a hypothesis, since it needs the multiplicity of a point of a triple fibre product \
to factor through the two iterated double products, which this repository does not have"]
theorem exteriorProductDedekindChow_assoc
    (hXY : ExteriorProductFactorsThroughRationalEquivalence C f' g' n m)
    (hXYZ : ExteriorProductFactorsThroughRationalEquivalence C
      (pullback.fst f' g' ≫ f') h' (n + m - 1) l)
    (hYZ : ExteriorProductFactorsThroughRationalEquivalence C g' h' m l)
    (hXYZ' : ExteriorProductFactorsThroughRationalEquivalence C f'
      (pullback.fst g' h' ≫ g') n (m + l - 1))
    (hpf : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst (pullback.fst f' g' ≫ f') h' ≫ (pullback.fst f' g' ≫ f'))
      (pullback.fst f' (pullback.fst g' h' ≫ g') ≫ f')
      (tripleFibreProductAssoc f' g' h').hom
      (tripleFibreProductAssoc_hom_structureMorphism f' g' h')
      (n + m - 1 + l - 1))
    (hassoc : IsExteriorProductDedekindAssociative C f' g' h' n m l)
    (α : CycleGroup C f' n) (β : CycleGroup C g' m) (γ : CycleGroup C h' l) :
    exteriorProductDedekind_degree_assoc n m l ▸
        properChowPushforward C
          (pullback.fst (pullback.fst f' g' ≫ f') h' ≫ (pullback.fst f' g' ≫ f'))
          (pullback.fst f' (pullback.fst g' h' ≫ g') ≫ f')
          (tripleFibreProductAssoc f' g' h').hom
          (tripleFibreProductAssoc_hom_structureMorphism f' g' h')
          (n + m - 1 + l - 1) hpf
          (exteriorProductDedekindChow C (pullback.fst f' g' ≫ f') h' (n + m - 1) l hXYZ
            (exteriorProductDedekindChow C f' g' n m hXY
              (QuotientAddGroup.mk' (rationalEquivalences C f' n) α)
              (QuotientAddGroup.mk' (rationalEquivalences C g' m) β))
            (QuotientAddGroup.mk' (rationalEquivalences C h' l) γ)) =
      exteriorProductDedekindChow C f' (pullback.fst g' h' ≫ g') n (m + l - 1) hXYZ'
        (QuotientAddGroup.mk' (rationalEquivalences C f' n) α)
        (exteriorProductDedekindChow C g' h' m l hYZ
          (QuotientAddGroup.mk' (rationalEquivalences C g' m) β)
          (QuotientAddGroup.mk' (rationalEquivalences C h' l) γ)) := by
  exact mk_cast_eq_mk_of_val_eq (pullback.fst f' (pullback.fst g' h' ≫ g') ≫ f')
    (exteriorProductDedekind_degree_assoc n m l) _ _ (hassoc α β γ)

end Stacks.Chow

end
