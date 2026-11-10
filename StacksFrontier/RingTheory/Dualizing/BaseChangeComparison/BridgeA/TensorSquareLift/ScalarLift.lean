module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompCancel
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareDerived
public import StacksFrontier.RingTheory.UliftTransport

/-!
# The scalar lift of a pushout square of rings, and of base change along one of its edges

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareDerived` proves the
projection formula at the two ring maps of a pushout square

```
S --g--> T
|        |
p        w
v        v
S' --h-> T'
```

in the derived category, for four rings in **one** universe.  The keystone
`Dualizing.TensorComparisonCompatibility`, through
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`, reads the projection formula at
`R → A` and at `R' → A ⊗_R R'`, whose four rings occupy the four independent universes `uR`,
`uA`, `uR'` and `max uA uR'`.  The independent-universe projection formula
`Dualizing.derivedExtendRestrictScalarsTensorIso` is *defined* by replacing both rings by their
universe lifts, applying the equal-universe statement there and carrying the result back along
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`;
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` presents the result as a
composite in which the one factor that is not a transport is the equal-universe formula at the
lifted ring map.

This file supplies the transport data that the same lift asks of a *square*, rather than of a
single ring map, and assembles the lifted pairing from it:

* the scalar lift of the square is again a pushout square, so that the equal-universe pairing
  `Dualizing.extendRestrictScalarsComplexIso_square` is available at the lifted rings;
* degreewise extension of scalars along `p` commutes with the two lift equivalences, the
  identification being the one that reads extension of scalars along a ring isomorphism as
  restriction of scalars along its inverse;
* hence an arbitrary model of derived base change along `p`, with its comparison morphism, has a
  comparison morphism against degreewise extension of scalars along the *lifted* map `p'`, read
  through the two lift equivalences, and it uses no universal property of the model: a comparison
  morphism is all that `Stacks.CategoryTheory.comp_eq_of_chain_pairing` asks of the edge it base
  changes along; and
* the component of the independent-universe projection formula is a chain-level pairing at the
  lifted ring map, whose transport prefix the transport tail and the chain-level formula retract,
  so that at the far edge of the square the prefix never has to be written down.

`Dualizing.derivedExtendRestrictScalarsTensorIso_square` is what these are for: the projection
formula at the two ring maps of a pushout square, in the derived category, at four independent
ring universes.

## Main definitions

* `Dualizing.extendScalarsIsoRestrictScalarsSymm`,
  `Dualizing.extendScalarsSymmIsoRestrictScalars` — extension of scalars along a ring isomorphism
  is restriction of scalars along its inverse, in both readings.
* `Dualizing.uliftExtendScalarsComm`, `Dualizing.uliftExtendScalarsCommComplex`,
  `Dualizing.uliftExtendScalarsCommUp`, `Dualizing.uliftExtendScalarsCommUpComplex`,
  `Dualizing.uliftExtendScalarsCommUpApp` — extension of scalars along `p`, conjugated by the two
  universe-lift restrictions, is extension of scalars along the lifted map `p'`; on modules, on
  cochain complexes, in both directions of the lift, and at a single complex.
* `Dualizing.scalarLiftInverseFactors` — the inverse of
  `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` factors through degreewise
  restriction of scalars along the lift.
* `Dualizing.liftedBaseChangeComparison` — the comparison morphism of an arbitrary model of
  derived base change along `p`, read against degreewise extension of scalars along `p'`.
* `Dualizing.liftTransportPrefix` — the six transport factors of
  `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` that precede the chain-level
  projection formula: the unit of the lift over the target ring,
  `CategoryTheory.Adjunction.leftAdjointUniq` of the two derived extensions of scalars across the
  lift, `Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, and the comparison of the lifted
  model at the lifted complex.
* `Dualizing.liftFlipConjugate`, `Dualizing.liftCoeffIso`, `Dualizing.liftTensorPsi`,
  `Dualizing.liftKFlatTensorIso`, `Dualizing.liftTransportTail` — the four isomorphisms of the
  transport tail, and the tail itself.
* `Dualizing.liftTransportFactors` — the factor between the transport prefix and the chain-level
  projection formula: derived restriction of scalars along the lifted map read through its own
  `CategoryTheory.Functor.mapDerivedCategoryFactors`.
* `Dualizing.liftSquareTensorTransport`, `Dualizing.liftSquarePrefixTransported`,
  `Dualizing.liftSquareTailTransported`, `Dualizing.liftSquareRetraction` — the prefix, the tail
  and the retraction of the prefix, each carried along a comparison `θ` between a complex over
  the lifted ring and the lift of a complex, which is the form the far edge of a square needs
  them in.
* `Dualizing.liftSquareConjugateTail`, `Dualizing.liftSquareConjugate`,
  `Dualizing.liftSquareConjugatedFormula` — the right-hand side of the transported pairing, in
  three nested pieces: the far edge with the two comparisons after it; those preceded by the
  pushout comparison of the lifted square and the identification of its two extensions of scalars
  along the diagonal; and those preceded by the base-changed transport prefix at `g`.

## Main results

* `Stacks.CategoryTheory.comp_cancel_last_through`,
  `Stacks.CategoryTheory.comp_cancel_last_through_symm` — the two readings of a seven-factor
  composite, four of whose factors are the image of a functor, with the last four factors
  cancelled against a retraction.  These are the shape in which
  `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` becomes an input of
  `Stacks.CategoryTheory.comp_eq_of_chain_pairing`.
* `Stacks.CategoryTheory.comp_retraction_four`,
  `Stacks.CategoryTheory.comp_retraction_four_grouped`,
  `Stacks.CategoryTheory.comp_retraction_pair`, `Stacks.CategoryTheory.inv_comp_four`,
  `Stacks.CategoryTheory.inv_comp_seven` — retractions of composites from retractions of their
  factors.
* `Stacks.CategoryTheory.map_comp_square`, `Stacks.CategoryTheory.map_comp_eq_id`,
  `Stacks.CategoryTheory.comp_eq_of_transport`,
  `Stacks.CategoryTheory.retraction_of_comp_eq` — a functor carries a commuting square to a
  commuting square and a retraction to a retraction; a factorization transported along a square;
  and the retraction a factorization into invertible factors provides.
* `Dualizing.uliftSquareComm`, `Dualizing.uliftIsPushoutSquare` — **the scalar lift of a pushout
  square of commutative rings is a pushout square**, so that the equal-universe chain-level
  pairing `Dualizing.extendRestrictScalarsComplexIso_square` is available at the lifted rings.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing` — **the
  transported pairing's one derived input**: the component of the independent-universe projection
  formula at the class of a K-flat complex, read against the transport tail, is the transport
  prefix followed by `DerivedCategory.Q` of the *equal-universe* chain-level projection formula at
  the lifted ring map and the lifted complex.  This is exactly the second hypothesis of
  `Stacks.CategoryTheory.comp_eq_of_chain_pairing` with `DerivedCategory.Q ⋙ E.inverse` for its
  localization functor, and it is where all six transport isomorphisms of the lift occur.
* `Dualizing.liftTransportTail_retraction`,
  `Dualizing.liftSquareTailTransported_retraction` — the transport tail is a retraction, before
  and after being carried along `θ`.
* `Dualizing.liftSquarePrefixTransported_comp`, `Dualizing.liftSquareRetraction_comp` — the two
  inputs the far edge of a square needs: the transported prefix read against the chain-level
  projection formula at the complex the square's pairing uses, and the fact that
  `Dualizing.liftSquareRetraction` retracts it.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_square` — **the projection formula at the two
  ring maps of a pushout square, derived, at four independent ring universes**: the base change
  along `p` of the formula at `g`, read at the class of a K-flat complex and against the transport
  tail, is `Dualizing.liftSquareConjugatedFormula`.

## Implementation notes

The three cancellation lemmas are stated over a variable category with every morphism a
variable, for the reason recorded on `Stacks.CategoryTheory.eq_of_glued_factorizations`: at the
instantiation the intermediate objects carry two definitionally but not syntactically equal
spellings, and a tactic that rebuilds the goal in place rejects the composite as ill-typed.
Instantiating with `exact` crosses each gap once, at default transparency.

`Dualizing.uliftExtendScalarsComm` is the one place where the three-universe composition
isomorphism `StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp` is needed: the two
composites it compares are extension of scalars along `p ∘ e_S` and along `e_{S'} ∘ p'`, whose
three rings are the lifted `S`, and `S`, and `S'`, in three universes that do not collapse.

The transport prefix, the factor after it and the four isomorphisms of the transport tail are
separate definitions rather than subterms of the statements that mention them.  That is forced by
the heartbeat budget, which is per declaration: the prefix is built from two composites of
adjunctions and one `CategoryTheory.Adjunction.leftAdjointUniq`, and a statement that writes it
out, at two ring maps, exceeds the budget on its own.  For the same reason
`Dualizing.uliftExtendScalarsCommUpApp` states the comparison at a single complex with both
objects written out: a consumer that mentions `Ep'.obj Kt` and
`(up ⋙ Ep').obj K` has to reconcile them, and that reconciliation is cheap only when one
declaration does it once.

The same budget shapes the transported pairing itself.  Its right-hand side is three nested
definitions, each a right-associated composite whose last factor is the next one, so that
unfolding them returns exactly the composite
`Stacks.CategoryTheory.comp_eq_of_chain_pairing` produces — the nesting regroups nothing, which
it would if a definition stopped short of the end of the composite.  Its proof leaves every
morphism and all four functors to unification: the two lift equivalences, degreewise extension of
scalars along `p'` and the model `Bp` are read off the type of
`Dualizing.liftedBaseChangeComparison`, the four comparisons of the lifted square off
`Dualizing.extendRestrictScalarsComplexIso_square`, and the far edge off
`Dualizing.liftSquareRetraction_comp`.  Writing any of them out instead elaborates the lifted ring
maps a second time, and reconciling two elaborations of one lifted map costs more than the budget
allows.

**What is not done here.**  `Dualizing.TensorComparisonCompatibility` is not proved and no tag
loses its conditional caveat.  What the keystone still needs of
`Dualizing.derivedExtendRestrictScalarsTensorIso_square` is the identification of the four
comparisons read here at chain level, through `DerivedCategory.Q` and the inverse of the scalar
lift, with the derived comparisons the keystone is stated with; those identifications are listed
in the implementation notes of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareDerived`, each with
the equation that evaluates the derived comparison at a class.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.MonoidalCategory
open StacksDraft.DerivedHom
open StacksDraft.DerivedExtensionScalarsModelComp

universe w u₁ u₂ v uR uA uS uT uSp uTp

namespace Stacks.CategoryTheory

/-- **A four-factor tail cancels, through a functor.**  A morphism `x` equal to the seven-factor
composite `a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ G (m₁ ≫ (m₂ ≫ m₃ ≫ m₄ ≫ m₅) ≫ m₆) ≫ G n ≫ z`, read against a
morphism `t` which retracts the last four of its factors, is the five-factor composite that
remains, grouped so that `G m₃ ≫ G m₄` is separated off.

This is the shape of `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj`, whose
right-hand side has exactly this nesting, read as the second hypothesis of
`Stacks.CategoryTheory.comp_eq_of_chain_pairing`. -/
theorem comp_cancel_last_through {C : Type*} {D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {P W₁ W₂ W₃ W : D} {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    (x : P ⟶ W) (a₁ : P ⟶ W₁) (a₂ : W₁ ⟶ W₂) (a₃ : W₂ ⟶ W₃) (a₄ : W₃ ⟶ G.obj X₀)
    (m₁ : X₀ ⟶ X₁) (m₂ : X₁ ⟶ X₂) (m₃ : X₂ ⟶ X₃) (m₄ : X₃ ⟶ X₄) (m₅ : X₄ ⟶ X₅)
    (m₆ : X₅ ⟶ X₆) (n : X₆ ⟶ X₇) (z : G.obj X₇ ⟶ W) (t : W ⟶ G.obj X₄)
    (hx : x = a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫
      G.map (m₁ ≫ (m₂ ≫ m₃ ≫ m₄ ≫ m₅) ≫ m₆) ≫ G.map n ≫ z)
    (ht : G.map m₅ ≫ G.map m₆ ≫ G.map n ≫ z ≫ t = 𝟙 (G.obj X₄)) :
    x ≫ t =
      (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ G.map m₁ ≫ G.map m₂) ≫ G.map m₃ ≫ G.map m₄ := by
  subst hx
  simp only [G.map_comp, Category.assoc]
  rw [ht, Category.comp_id]

/-- `Stacks.CategoryTheory.comp_cancel_last_through` with the surviving prefix grouped as a
single morphism and the equation read in the other direction, which is the shape of the third
hypothesis of `Stacks.CategoryTheory.comp_eq_of_chain_pairing`. -/
theorem comp_cancel_last_through_symm {C : Type*} {D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D)
    {P W₁ W₂ W₃ W : D} {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    (x : P ⟶ W) (a₁ : P ⟶ W₁) (a₂ : W₁ ⟶ W₂) (a₃ : W₂ ⟶ W₃) (a₄ : W₃ ⟶ G.obj X₀)
    (m₁ : X₀ ⟶ X₁) (m₂ : X₁ ⟶ X₂) (m₃ : X₂ ⟶ X₃) (m₄ : X₃ ⟶ X₄) (m₅ : X₄ ⟶ X₅)
    (m₆ : X₅ ⟶ X₆) (n : X₆ ⟶ X₇) (z : G.obj X₇ ⟶ W) (t : W ⟶ G.obj X₄)
    (hx : x = a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫
      G.map (m₁ ≫ (m₂ ≫ m₃ ≫ m₄ ≫ m₅) ≫ m₆) ≫ G.map n ≫ z)
    (ht : G.map m₅ ≫ G.map m₆ ≫ G.map n ≫ z ≫ t = 𝟙 (G.obj X₄)) :
    (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ G.map m₁ ≫ G.map m₂ ≫ G.map m₃) ≫ G.map m₄ = x ≫ t := by
  refine Eq.trans ?_ (comp_cancel_last_through G x a₁ a₂ a₃ a₄ m₁ m₂ m₃ m₄ m₅ m₆ n z t hx ht).symm
  simp only [Category.assoc]

/-- **A four-factor tail, three of whose factors are the image of a functor, has the reversed
composite of the retractions for a retraction.**

Stated over variable categories with every morphism a variable, so that the instantiation
crosses each gap between two definitionally but not syntactically equal spellings once, by
`exact`, at default transparency: at the instantiation this file needs, a tactic that rebuilds
the goal in place reports that the target is not type-correct at `implicit` transparency and
rewrites nothing. -/
theorem comp_retraction_four {C : Type*} {D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {X₄ X₅ X₆ X₇ : C} {W : D}
    (m₅ : X₄ ⟶ X₅) (m₅' : X₅ ⟶ X₄) (m₆ : X₅ ⟶ X₆) (m₆' : X₆ ⟶ X₅)
    (n : X₆ ⟶ X₇) (n' : X₇ ⟶ X₆) (z : G.obj X₇ ⟶ W) (z' : W ⟶ G.obj X₇)
    (h₅ : m₅ ≫ m₅' = 𝟙 X₄) (h₆ : m₆ ≫ m₆' = 𝟙 X₅) (hn : n ≫ n' = 𝟙 X₆)
    (hz : z ≫ z' = 𝟙 (G.obj X₇)) :
    G.map m₅ ≫ G.map m₆ ≫ G.map n ≫ z ≫
        (z' ≫ G.map n' ≫ G.map m₆' ≫ G.map m₅') = 𝟙 (G.obj X₄) := by
  calc G.map m₅ ≫ G.map m₆ ≫ G.map n ≫ z ≫ (z' ≫ G.map n' ≫ G.map m₆' ≫ G.map m₅')
      = G.map m₅ ≫ G.map m₆ ≫ G.map n ≫ G.map n' ≫ G.map m₆' ≫ G.map m₅' := by
        rw [← Category.assoc z z', hz, Category.id_comp]
    _ = G.map (m₅ ≫ m₆ ≫ n ≫ n' ≫ m₆' ≫ m₅') := by
        simp only [G.map_comp]
    _ = 𝟙 (G.obj X₄) := by
        rw [← Category.assoc n n', hn, Category.id_comp, ← Category.assoc m₆ m₆', h₆,
          Category.id_comp, h₅, CategoryTheory.Functor.map_id]

/-- **A functor carries a commuting square to a commuting square.**  Stated over variable
categories with every morphism a variable, so that at the instantiation the functor is a
composite whose intermediate object has two definitionally but not syntactically equal
spellings. -/
theorem map_comp_square {C : Type*} {D : Type*} [Category* C] [Category* D] (Q : C ⥤ D)
    {a b c d : C} (f : a ⟶ b) (g : b ⟶ d) (f' : a ⟶ c) (g' : c ⟶ d)
    (h : f ≫ g = f' ≫ g') : Q.map f ≫ Q.map g = Q.map f' ≫ Q.map g' := by
  rw [← Q.map_comp, ← Q.map_comp, h]

/-- **A factorization transported along a commuting square.**  If `q ≫ k₁` factors as `ph ≫ t`
and `ν ≫ k₂ = k₁ ≫ μ`, then `(q ≫ ν) ≫ k₂` factors as `ph ≫ t ≫ μ`.  This is how the
projection formula at `h`, read at a complex over `S'`, is moved to the complex the chain-level
pairing of the square reads it at: `ν` and `μ` are the comparison of
`Dualizing.uliftExtendScalarsCommUpComplex` and `k₁`, `k₂` are the chain-level projection formula
at the two complexes. -/
theorem comp_eq_of_transport {D : Type*} [Category* D] {Z W A₁ A₂ B₁ B₂ : D}
    (q : Z ⟶ A₁) (k₁ : A₁ ⟶ B₁) (ph : Z ⟶ W) (t : W ⟶ B₁)
    (ν : A₁ ⟶ A₂) (k₂ : A₂ ⟶ B₂) (μ : B₁ ⟶ B₂)
    (h₁ : q ≫ k₁ = ph ≫ t) (h₂ : ν ≫ k₂ = k₁ ≫ μ) :
    (q ≫ ν) ≫ k₂ = ph ≫ t ≫ μ := by
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

/-- **A morphism factoring as an invertible composite has the evident retraction.**  If
`q ≫ k = ph ≫ t` with `k`, `ph` and `t` invertible — recorded through retractions rather than
`IsIso`, in the manner of `Stacks.CategoryTheory.inv_comp_two` — then `k ≫ t' ≫ ph'` is a
retraction of `q`.

This is what replaces the seven-factor transport prefix of
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing` by three factors in
the statement of the transported pairing: on the side of the square at which only the retraction
of the prefix occurs, the prefix itself need never be written down. -/
theorem retraction_of_comp_eq {D : Type*} [Category* D] {Z W A B : D}
    (q : Z ⟶ A) (k : A ⟶ B) (k' : B ⟶ A) (ph : Z ⟶ W) (ph' : W ⟶ Z) (t : W ⟶ B) (t' : B ⟶ W)
    (heq : q ≫ k = ph ≫ t) (hk : k ≫ k' = 𝟙 A) (hph : ph' ≫ ph = 𝟙 W)
    (ht : t' ≫ t = 𝟙 B) :
    (k ≫ t' ≫ ph') ≫ q = 𝟙 A := by
  have hq : q = ph ≫ t ≫ k' := by
    rw [← Category.assoc, ← heq, Category.assoc, hk, Category.comp_id]
  rw [hq]
  simp only [Category.assoc]
  rw [← Category.assoc ph' ph, hph, Category.id_comp, ← Category.assoc t' t, ht,
    Category.id_comp, hk]

/-- **A retraction of a two-factor composite from retractions of the factors.**  Stated over a
variable category with every morphism a variable, for the reason recorded on
`Stacks.CategoryTheory.inv_comp_two`. -/
theorem comp_retraction_pair {D : Type*} [Category* D] {W X Y : D}
    (r : W ⟶ X) (r' : X ⟶ W) (m : X ⟶ Y) (m' : Y ⟶ X)
    (hr : r' ≫ r = 𝟙 X) (hm : m' ≫ m = 𝟙 Y) : (m' ≫ r') ≫ r ≫ m = 𝟙 Y := by
  rw [Category.assoc, ← Category.assoc r' r, hr, Category.id_comp, hm]

/-- `Stacks.CategoryTheory.comp_retraction_four` with the two four-factor composites each grouped
as a single morphism, which is the shape in which the retraction of the tail is fed to
`Stacks.CategoryTheory.comp_retraction_pair`. -/
theorem comp_retraction_four_grouped {C : Type*} {D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {X₄ X₅ X₆ X₇ : C} {W : D}
    (m₅ : X₄ ⟶ X₅) (m₅' : X₅ ⟶ X₄) (m₆ : X₅ ⟶ X₆) (m₆' : X₆ ⟶ X₅)
    (n : X₆ ⟶ X₇) (n' : X₇ ⟶ X₆) (z : G.obj X₇ ⟶ W) (z' : W ⟶ G.obj X₇)
    (h₅ : m₅ ≫ m₅' = 𝟙 X₄) (h₆ : m₆ ≫ m₆' = 𝟙 X₅) (hn : n ≫ n' = 𝟙 X₆)
    (hz : z ≫ z' = 𝟙 (G.obj X₇)) :
    (G.map m₅ ≫ G.map m₆ ≫ G.map n ≫ z) ≫
        (z' ≫ G.map n' ≫ G.map m₆' ≫ G.map m₅') = 𝟙 (G.obj X₄) := by
  refine Eq.trans ?_ (comp_retraction_four G m₅ m₅' m₆ m₆' n n' z z' h₅ h₆ hn hz)
  simp only [Category.assoc]

/-- **A functor carries a retraction to a retraction.**

Stated over variable categories with the two morphisms variables, so that the instantiation is
one unification at default transparency.  At the instantiations this file needs the functor is a
scalar-lift equivalence reaching the goal through two different abbreviations, and a tactic that
matches the goal syntactically finds no occurrence of `CategoryTheory.Functor.map_comp`. -/
theorem map_comp_eq_id {C : Type*} {D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 X) :
    G.map a ≫ G.map b = 𝟙 (G.obj X) := by
  rw [← G.map_comp, h, CategoryTheory.Functor.map_id]

/-- **Four retractions compose to a retraction of the four-factor composite.**

Recorded as the equation rather than through `IsIso`, in the manner of
`Stacks.CategoryTheory.inv_comp_two`: an `IsIso` hypothesis carries the object spellings in its
indices, where instance resolution does not cross between two definitionally equal ones. -/
theorem inv_comp_four {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ : C}
    (f₁ : X₀ ⟶ X₁) (g₁ : X₁ ⟶ X₀) (f₂ : X₁ ⟶ X₂) (g₂ : X₂ ⟶ X₁)
    (f₃ : X₂ ⟶ X₃) (g₃ : X₃ ⟶ X₂) (f₄ : X₃ ⟶ X₄) (g₄ : X₄ ⟶ X₃)
    (h₁ : g₁ ≫ f₁ = 𝟙 X₁) (h₂ : g₂ ≫ f₂ = 𝟙 X₂) (h₃ : g₃ ≫ f₃ = 𝟙 X₃)
    (h₄ : g₄ ≫ f₄ = 𝟙 X₄) :
    (g₄ ≫ g₃ ≫ g₂ ≫ g₁) ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ = 𝟙 X₄ := by
  simp [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

/-- **Seven retractions compose to a retraction of the seven-factor composite.**

Recorded as the equation rather than through `IsIso`, in the manner of
`Stacks.CategoryTheory.inv_comp_two`: an `IsIso` hypothesis carries the object spellings in its
indices, where instance resolution does not cross between two definitionally equal ones. -/
theorem inv_comp_seven {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C}
    (f₁ : X₀ ⟶ X₁) (g₁ : X₁ ⟶ X₀) (f₂ : X₁ ⟶ X₂) (g₂ : X₂ ⟶ X₁)
    (f₃ : X₂ ⟶ X₃) (g₃ : X₃ ⟶ X₂) (f₄ : X₃ ⟶ X₄) (g₄ : X₄ ⟶ X₃)
    (f₅ : X₄ ⟶ X₅) (g₅ : X₅ ⟶ X₄) (f₆ : X₅ ⟶ X₆) (g₆ : X₆ ⟶ X₅)
    (f₇ : X₆ ⟶ X₇) (g₇ : X₇ ⟶ X₆)
    (h₁ : g₁ ≫ f₁ = 𝟙 X₁) (h₂ : g₂ ≫ f₂ = 𝟙 X₂) (h₃ : g₃ ≫ f₃ = 𝟙 X₃)
    (h₄ : g₄ ≫ f₄ = 𝟙 X₄) (h₅ : g₅ ≫ f₅ = 𝟙 X₅) (h₆ : g₆ ≫ f₆ = 𝟙 X₆)
    (h₇ : g₇ ≫ f₇ = 𝟙 X₇) :
    (g₇ ≫ g₆ ≫ g₅ ≫ g₄ ≫ g₃ ≫ g₂ ≫ g₁) ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ ≫ f₇ = 𝟙 X₇ := by
  simp [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, reassoc_of% h₅,
    reassoc_of% h₆, h₇]

end Stacks.CategoryTheory

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

/-- **Extension of scalars along a ring isomorphism is restriction of scalars along its
inverse.**  Both are left adjoint to restriction of scalars along the isomorphism itself —
extension by `ModuleCat.extendRestrictScalarsAdj`, restriction along the inverse because
restriction along an isomorphism is an equivalence — so uniqueness of left adjoints identifies
them.

This is what lets the two universe-lift restrictions be absorbed into extensions of scalars, and
hence `StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp` be applied to them. -/
def extendScalarsIsoRestrictScalarsSymm {R₀ : Type u₁} {R : Type u₂} [CommRing R₀] [CommRing R]
    (e : R₀ ≃+* R) :
    ModuleCat.extendScalars.{u₁, u₂, max w u₁ u₂} (e : R₀ →+* R) ≅
      ModuleCat.restrictScalars.{max w u₁ u₂} (e.symm : R →+* R₀) :=
  (ModuleCat.extendRestrictScalarsAdj.{max w u₁ u₂, u₁, u₂} (e : R₀ →+* R)).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

/-- **Restriction of scalars along a ring isomorphism is extension of scalars along its
inverse.**  The reading of `Dualizing.extendScalarsIsoRestrictScalarsSymm` in which the
isomorphism itself, rather than its inverse, labels the restriction; it is the one the *upward*
universe lift is spelled with, since `Dualizing.derivedAlgebraSingleLiftIso` and
`CategoryTheory.Functor.mapDerivedCategoryFactors` carry a complex over the base ring to one over
the lifted ring by restricting along `ULift.ringEquiv` itself. -/
def extendScalarsSymmIsoRestrictScalars {R₀ : Type u₁} {R : Type u₂} [CommRing R₀] [CommRing R]
    (e : R₀ ≃+* R) :
    ModuleCat.extendScalars.{u₂, u₁, max w u₁ u₂} (e.symm : R →+* R₀) ≅
      ModuleCat.restrictScalars.{max w u₁ u₂} e.toRingHom :=
  (ModuleCat.extendRestrictScalarsAdj.{max w u₁ u₂, u₂, u₁} (e.symm : R →+* R₀)).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).toAdjunction


section Pushout

private lemma isPushout_of_bijective_base {R₀ R A B C : Type*}
    [CommRing R₀] [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R₀ R] [Algebra R₀ A] [Algebra R A] [Algebra R₀ B] [Algebra R B]
    [Algebra R₀ C] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R₀ R A] [IsScalarTower R₀ R B] [IsScalarTower R₀ A C]
    [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower R₀ B C]
    (hbij : Function.Bijective (algebraMap R₀ R))
    (H : Algebra.IsPushout R A B C) : Algebra.IsPushout R₀ A B C := by
  have : Algebra.IsPushout R₀ R B B :=
    Algebra.IsPushout.symm (Algebra.IsPushout.of_bijective_left _ _ hbij)
  exact (Algebra.IsPushout.comp_iff R₀ R B (S' := B) (T := A) (T' := C)).mpr H

private lemma isPushout_of_bijective_leg {R A B₀ B C : Type*}
    [CommRing R] [CommRing A] [CommRing B₀] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B₀] [Algebra R B] [Algebra B₀ B]
    [Algebra R C] [Algebra A C] [Algebra B C] [Algebra B₀ C]
    [IsScalarTower R B₀ B] [IsScalarTower R A C] [IsScalarTower R B C]
    [IsScalarTower R B₀ C] [IsScalarTower B₀ B C]
    (hbij : Function.Bijective (algebraMap B₀ B))
    (H : Algebra.IsPushout R A B C) : Algebra.IsPushout R A B₀ C := by
  have : Algebra.IsPushout R R B₀ B :=
    Algebra.IsPushout.symm (Algebra.IsPushout.of_bijective_right _ _ hbij)
  exact (Algebra.IsPushout.comp_iff R R B₀ (S' := B) (T := A) (T' := C)).mpr H

/-- The universe lifts of a commuting square of commutative rings commute. -/
theorem uliftSquareComm {S : Type uS} {T : Type uT} {S' : Type uSp} {T' : Type uTp}
    [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
    (comm : w.comp g = h.comp p) :
      (((ULift.ringEquiv.symm.toRingHom.comp w).comp ULift.ringEquiv.toRingHom :
          ULift.{max v uS uT uSp uTp} T →+* ULift.{max v uS uT uSp uTp} T')).comp
        ((ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom :
          ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} T) =
      (((ULift.ringEquiv.symm.toRingHom.comp h).comp ULift.ringEquiv.toRingHom :
          ULift.{max v uS uT uSp uTp} S' →+* ULift.{max v uS uT uSp uTp} T')).comp
        ((ULift.ringEquiv.symm.toRingHom.comp p).comp ULift.ringEquiv.toRingHom :
          ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} S') := by
  ext x
  exact RingHom.congr_fun comm x.down

/-- A pushout square of commutative rings stays a pushout square after lifting all four
corners into one universe. -/
theorem uliftIsPushoutSquare {S : Type uS} {T : Type uT} {S' : Type uSp} {T' : Type uTp}
    [CommRing S] [CommRing T] [CommRing S'] [CommRing T']
    (g : S →+* T) (p : S →+* S') (w : T →+* T') (h : S' →+* T')
    (comm : w.comp g = h.comp p) (hp : MilnorPatching.IsPushoutSquare g p w h comm)
    (comm' :
      (((ULift.ringEquiv.symm.toRingHom.comp w).comp ULift.ringEquiv.toRingHom :
          ULift.{max v uS uT uSp uTp} T →+* ULift.{max v uS uT uSp uTp} T')).comp
        ((ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom :
          ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} T) =
      (((ULift.ringEquiv.symm.toRingHom.comp h).comp ULift.ringEquiv.toRingHom :
          ULift.{max v uS uT uSp uTp} S' →+* ULift.{max v uS uT uSp uTp} T')).comp
        ((ULift.ringEquiv.symm.toRingHom.comp p).comp ULift.ringEquiv.toRingHom :
          ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} S')) :
    MilnorPatching.IsPushoutSquare
      ((ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom :
        ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} T)
      ((ULift.ringEquiv.symm.toRingHom.comp p).comp ULift.ringEquiv.toRingHom :
        ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} S')
      ((ULift.ringEquiv.symm.toRingHom.comp w).comp ULift.ringEquiv.toRingHom :
        ULift.{max v uS uT uSp uTp} T →+* ULift.{max v uS uT uSp uTp} T')
      ((ULift.ringEquiv.symm.toRingHom.comp h).comp ULift.ringEquiv.toRingHom :
        ULift.{max v uS uT uSp uTp} S' →+* ULift.{max v uS uT uSp uTp} T')
      comm' := by
  -- the five algebra structures of the lifted square, as `IsPushoutSquare` installs them
  let : Algebra (ULift.{max v uS uT uSp uTp} S) (ULift.{max v uS uT uSp uTp} T) :=
    ((ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom).toAlgebra
  let : Algebra (ULift.{max v uS uT uSp uTp} S) (ULift.{max v uS uT uSp uTp} S') :=
    ((ULift.ringEquiv.symm.toRingHom.comp p).comp ULift.ringEquiv.toRingHom).toAlgebra
  let : Algebra (ULift.{max v uS uT uSp uTp} T) (ULift.{max v uS uT uSp uTp} T') :=
    ((ULift.ringEquiv.symm.toRingHom.comp w).comp ULift.ringEquiv.toRingHom).toAlgebra
  let : Algebra (ULift.{max v uS uT uSp uTp} S') (ULift.{max v uS uT uSp uTp} T') :=
    ((ULift.ringEquiv.symm.toRingHom.comp h).comp ULift.ringEquiv.toRingHom).toAlgebra
  let : Algebra (ULift.{max v uS uT uSp uTp} S) (ULift.{max v uS uT uSp uTp} T') :=
    ((((ULift.ringEquiv.symm.toRingHom.comp w).comp ULift.ringEquiv.toRingHom :
        ULift.{max v uS uT uSp uTp} T →+* ULift.{max v uS uT uSp uTp} T')).comp
      ((ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom :
        ULift.{max v uS uT uSp uTp} S →+* ULift.{max v uS uT uSp uTp} T)).toAlgebra
  -- the five algebra structures of the given square
  let : Algebra S T := g.toAlgebra
  let : Algebra S S' := p.toAlgebra
  let : Algebra T T' := w.toAlgebra
  let : Algebra S' T' := h.toAlgebra
  let : Algebra S T' := (w.comp g).toAlgebra
  -- the comparison maps between the two squares
  let : Algebra (ULift.{max v uS uT uSp uTp} S) S :=
    (ULift.ringEquiv : ULift.{max v uS uT uSp uTp} S ≃+* S).toRingHom.toAlgebra
  let : Algebra (ULift.{max v uS uT uSp uTp} T) T :=
    (ULift.ringEquiv : ULift.{max v uS uT uSp uTp} T ≃+* T).toRingHom.toAlgebra
  let : Algebra (ULift.{max v uS uT uSp uTp} S') S' :=
    (ULift.ringEquiv : ULift.{max v uS uT uSp uTp} S' ≃+* S').toRingHom.toAlgebra
  let : Algebra S (ULift.{max v uS uT uSp uTp} T) :=
    (ULift.ringEquiv.symm.toRingHom.comp g).toAlgebra
  let : Algebra S (ULift.{max v uS uT uSp uTp} S') :=
    (ULift.ringEquiv.symm.toRingHom.comp p).toAlgebra
  let : Algebra S (ULift.{max v uS uT uSp uTp} T') :=
    (ULift.ringEquiv.symm.toRingHom.comp (w.comp g)).toAlgebra
  let : Algebra T (ULift.{max v uS uT uSp uTp} T') :=
    (ULift.ringEquiv.symm.toRingHom.comp w).toAlgebra
  let : Algebra S' (ULift.{max v uS uT uSp uTp} T') :=
    (ULift.ringEquiv.symm.toRingHom.comp h).toAlgebra
  -- the two scalar towers of the lifted square
  have hsLift := IsScalarTower.of_algebraMap_eq
    (R := ULift.{max v uS uT uSp uTp} S) (S := ULift.{max v uS uT uSp uTp} T)
    (A := ULift.{max v uS uT uSp uTp} T') fun _ => rfl
  have htLift := IsScalarTower.of_algebraMap_eq
    (R := ULift.{max v uS uT uSp uTp} S) (S := ULift.{max v uS uT uSp uTp} S')
    (A := ULift.{max v uS uT uSp uTp} T') (RingHom.ext_iff.1 comm')
  -- the scalar towers mixing the two squares
  have := IsScalarTower.of_algebraMap_eq
    (R := S) (S := ULift.{max v uS uT uSp uTp} T) (A := T) fun _ => rfl
  have := IsScalarTower.of_algebraMap_eq
    (R := S) (S := ULift.{max v uS uT uSp uTp} S') (A := S') fun _ => rfl
  have := IsScalarTower.of_algebraMap_eq
    (R := S) (S := T) (A := ULift.{max v uS uT uSp uTp} T') fun _ => rfl
  have := IsScalarTower.of_algebraMap_eq
    (R := S) (S := ULift.{max v uS uT uSp uTp} T)
    (A := ULift.{max v uS uT uSp uTp} T') fun _ => rfl
  have := IsScalarTower.of_algebraMap_eq
    (R := ULift.{max v uS uT uSp uTp} T) (S := T)
    (A := ULift.{max v uS uT uSp uTp} T') fun _ => rfl
  have := IsScalarTower.of_algebraMap_eq
    (R := ULift.{max v uS uT uSp uTp} S') (S := S')
    (A := ULift.{max v uS uT uSp uTp} T') fun _ => rfl
  have := IsScalarTower.of_algebraMap_eq
    (R := ULift.{max v uS uT uSp uTp} S) (S := S)
    (A := ULift.{max v uS uT uSp uTp} S') fun _ => rfl
  have := IsScalarTower.of_algebraMap_eq
    (R := ULift.{max v uS uT uSp uTp} S) (S := S)
    (A := ULift.{max v uS uT uSp uTp} T) fun _ => rfl
  have := IsScalarTower.of_algebraMap_eq
    (R := S) (S := S') (A := ULift.{max v uS uT uSp uTp} T')
    fun x => congrArg ULift.up (RingHom.congr_fun comm x)
  have := IsScalarTower.of_algebraMap_eq
    (R := S) (S := ULift.{max v uS uT uSp uTp} S') (A := ULift.{max v uS uT uSp uTp} T')
    fun x => congrArg ULift.up (RingHom.congr_fun comm x)
  -- the given square is a pushout square
  obtain ⟨hs, ht, hp0⟩ := hp
  have := hs
  have := ht
  have := hp0
  -- move the fourth corner, then the two legs, then the base
  have step1 : Algebra.IsPushout S S' T (ULift.{max v uS uT uSp uTp} T') :=
    Algebra.IsPushout.of_equiv
      (AlgEquiv.ofRingEquiv
        (f := (ULift.ringEquiv : ULift.{max v uS uT uSp uTp} T' ≃+* T').symm) fun _ => rfl)
      (RingHom.ext fun _ => rfl)
  have step2 : Algebra.IsPushout S S' (ULift.{max v uS uT uSp uTp} T)
      (ULift.{max v uS uT uSp uTp} T') :=
    isPushout_of_bijective_leg (B₀ := ULift.{max v uS uT uSp uTp} T) (B := T)
      ULift.ringEquiv.bijective step1
  have step3 : Algebra.IsPushout S (ULift.{max v uS uT uSp uTp} T)
      (ULift.{max v uS uT uSp uTp} S') (ULift.{max v uS uT uSp uTp} T') :=
    isPushout_of_bijective_leg (B₀ := ULift.{max v uS uT uSp uTp} S') (B := S')
      ULift.ringEquiv.bijective (Algebra.IsPushout.symm step2)
  exact ⟨hsLift, htLift,
    isPushout_of_bijective_base (R₀ := ULift.{max v uS uT uSp uTp} S) (R := S)
      ULift.ringEquiv.bijective (Algebra.IsPushout.symm step3)⟩

end Pushout

section Lift

variable {S : Type uS} {S' : Type uSp} [CommRing S] [CommRing S'] (p : S →+* S')

/-- **Extension of scalars along `p`, conjugated by the two universe-lift restrictions, is
extension of scalars along the lifted map.**  On modules: the lifted map `p'` is
`e_{S'}⁻¹ ∘ p ∘ e_S`, so `e_{S'} ∘ p' = p ∘ e_S`, and both conjugates are extension of scalars
along that one ring map, by
`StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp` at three independent ring
universes. -/
def uliftExtendScalarsComm :
    ModuleCat.restrictScalars.{max v uS uSp}
          ((ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).symm :
            S →+* ULift.{max v uS uSp} S) ⋙
        ModuleCat.extendScalars.{uS, uSp, max v uS uSp} p ≅
      ModuleCat.extendScalars.{max v uS uSp, max v uS uSp, max v uS uSp}
          ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
            (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
              ULift.{max v uS uSp} S →+* ULift.{max v uS uSp} S')) ⋙
        ModuleCat.restrictScalars.{max v uS uSp}
          ((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm :
            S' →+* ULift.{max v uS uSp} S') :=
  isoWhiskerRight (extendScalarsIsoRestrictScalarsSymm.{v}
      (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S)).symm
    (ModuleCat.extendScalars.{uS, uSp, max v uS uSp} p) ≪≫
  (extendScalarsComp.{max v uS uSp, uS, uSp, v}
    (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom p).symm ≪≫
  eqToIso (congrArg (fun φ : ULift.{max v uS uSp} S →+* S' =>
      ModuleCat.extendScalars.{max v uS uSp, uSp, max v uS uSp} φ)
    (RingHom.ext fun _ => rfl)) ≪≫
  extendScalarsComp.{max v uS uSp, max v uS uSp, uSp, v}
    ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
      (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
        ULift.{max v uS uSp} S →+* ULift.{max v uS uSp} S'))
    (ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').toRingHom ≪≫
  isoWhiskerLeft _ (extendScalarsIsoRestrictScalarsSymm.{v}
    (ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S'))

/-- `Dualizing.uliftExtendScalarsComm` applied degreewise to cochain complexes. -/
def uliftExtendScalarsCommComplex :
    (ModuleCat.restrictScalars.{max v uS uSp}
            ((ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).symm :
              S →+* ULift.{max v uS uSp} S)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{uS, uSp, max v uS uSp} p).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{max v uS uSp, max v uS uSp, max v uS uSp}
            ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
              (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
                ULift.{max v uS uSp} S →+* ULift.{max v uS uSp} S'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars.{max v uS uSp}
            ((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm :
              S' →+* ULift.{max v uS uSp} S')).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (uliftExtendScalarsComm.{v} p) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- **The upward reading of `Dualizing.uliftExtendScalarsComm`.**  Extension of scalars along `p`
followed by the upward universe lift is the upward lift followed by extension of scalars along
the lifted map: both are extension of scalars along `e_{S'}⁻¹ ∘ p`, at three independent ring
universes.

This is the direction in which the lift of a complex of `S`-modules is compared with the
extension of scalars of its lift, which is what reads the projection formula at `h` on the
extension of scalars along `p` of a complex. -/
def uliftExtendScalarsCommUp :
    ModuleCat.restrictScalars.{max v uS uSp}
          (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom ⋙
        ModuleCat.extendScalars.{max v uS uSp, max v uS uSp, max v uS uSp}
          ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
            (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
              ULift.{max v uS uSp} S →+* ULift.{max v uS uSp} S')) ≅
      ModuleCat.extendScalars.{uS, uSp, max v uS uSp} p ⋙
        ModuleCat.restrictScalars.{max v uS uSp}
          (ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').toRingHom :=
  isoWhiskerRight (extendScalarsSymmIsoRestrictScalars.{v}
      (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S)).symm
    (ModuleCat.extendScalars.{max v uS uSp, max v uS uSp, max v uS uSp}
      ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
        (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
          ULift.{max v uS uSp} S →+* ULift.{max v uS uSp} S'))) ≪≫
  (extendScalarsComp.{uS, max v uS uSp, max v uS uSp, v}
    ((ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).symm : S →+* ULift.{max v uS uSp} S)
    ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
      (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
        ULift.{max v uS uSp} S →+* ULift.{max v uS uSp} S'))).symm ≪≫
  eqToIso (congrArg (fun φ : S →+* ULift.{max v uS uSp} S' =>
      ModuleCat.extendScalars.{uS, max v uS uSp, max v uS uSp} φ)
    (RingHom.ext fun _ => rfl)) ≪≫
  extendScalarsComp.{uS, uSp, max v uS uSp, v} p
    ((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm : S' →+* ULift.{max v uS uSp} S') ≪≫
  isoWhiskerLeft _ (extendScalarsSymmIsoRestrictScalars.{v}
    (ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S'))

/-- `Dualizing.uliftExtendScalarsCommUp` applied degreewise to cochain complexes. -/
def uliftExtendScalarsCommUpComplex :
    (ModuleCat.restrictScalars.{max v uS uSp}
            (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+*
              S).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{max v uS uSp, max v uS uSp, max v uS uSp}
            ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
              (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
                ULift.{max v uS uSp} S →+*
                  ULift.{max v uS uSp} S'))).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{uS, uSp, max v uS uSp} p).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars.{max v uS uSp}
            (ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+*
              S').toRingHom).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (uliftExtendScalarsCommUp.{v} p) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- `Dualizing.uliftExtendScalarsCommUpComplex` at a single complex, with both objects written
out: the lifted extension of scalars along the lifted map, applied to the lift of `K`, is the
lift of the extension of scalars along `p` applied to `K`.  Stated separately so that a consumer
mentioning both objects crosses no `CategoryTheory.Functor.comp`. -/
def uliftExtendScalarsCommUpApp (K : CochainComplex (ModuleCat.{max v uS uSp} S) ℤ) :
    ((ModuleCat.extendScalars.{max v uS uSp, max v uS uSp, max v uS uSp}
          ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
            (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
              ULift.{max v uS uSp} S →+*
                ULift.{max v uS uSp} S'))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars
            (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+*
              S).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((ModuleCat.restrictScalars
          (ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+*
            S').toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{uS, uSp, max v uS uSp} p).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  (uliftExtendScalarsCommUpComplex.{v} p).app K

end Lift

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The inverse of the scalar-lift equivalence factors through degreewise restriction of
scalars along the lift.**  `Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence` is
built by localizing the equivalence of module categories induced by `ULift.ringEquiv`, so its
inverse is `CategoryTheory.Functor.mapDerivedCategory` of restriction of scalars along
`ULift.ringEquiv.symm`, and the factorization is that functor's own
`CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
def scalarLiftInverseFactors (S : Type uS) [CommRing S] :
    DerivedCategory.Q ⋙
        (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uS,
          max v uS} S).inverse ≅
      (ModuleCat.restrictScalars.{max v uS}
          ((ULift.ringEquiv : ULift.{max v uS} S ≃+* S).symm :
            S →+* ULift.{max v uS} S)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (ModuleCat.restrictScalars.{max v uS}
      ((ULift.ringEquiv : ULift.{max v uS} S ≃+* S).symm :
        S →+* ULift.{max v uS} S)).mapDerivedCategoryFactors

variable {S : Type uS} {S' : Type uSp} [CommRing S] [CommRing S'] (p : S →+* S')
  (Bp : DerivedCategory (ModuleCat.{max v uS uSp} S) ⥤
    DerivedCategory (ModuleCat.{max v uS uSp} S'))
  (betaP : DerivedCategory.Q ⋙ Bp ⟶
    (ModuleCat.extendScalars.{uS, uSp, max v uS uSp} p).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

/-- **The comparison morphism of a model of derived base change, read through the scalar lift.**
For an arbitrary model `Bp` of derived base change along `p` with comparison morphism `betaP`,
this is the comparison morphism of `Bp` against degreewise extension of scalars along the lifted
map `p'`, with both derived categories read through the lift equivalences.

It is the composite of `Dualizing.scalarLiftInverseFactors` at `S`, the given comparison,
`Dualizing.uliftExtendScalarsCommComplex` localized, and
`Dualizing.scalarLiftInverseFactors` at `S'` inverted.  No universal property of `Bp` is used:
this is exactly the datum that `Stacks.CategoryTheory.comp_eq_of_chain_pairing` asks of the edge
it base changes along, and it is a natural transformation, so its naturality is free. -/
def liftedBaseChangeComparison :
    (DerivedCategory.Q ⋙
          (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uS,
            max v uS uSp} S).inverse) ⋙ Bp ⟶
      (ModuleCat.extendScalars.{max v uS uSp, max v uS uSp, max v uS uSp}
            ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
              (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
                ULift.{max v uS uSp} S →+* ULift.{max v uS uSp} S'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Q ⋙
          (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uSp,
            max v uS uSp} S').inverse) :=
  Functor.whiskerRight (scalarLiftInverseFactors.{max v uSp, uS} S).hom Bp ≫
    Functor.whiskerLeft
      ((ModuleCat.restrictScalars.{max v uS uSp}
        ((ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).symm :
          S →+* ULift.{max v uS uSp} S)).mapHomologicalComplex (ComplexShape.up ℤ)) betaP ≫
    Functor.whiskerRight (uliftExtendScalarsCommComplex.{v} p).hom DerivedCategory.Q ≫
    Functor.whiskerLeft
      ((ModuleCat.extendScalars.{max v uS uSp, max v uS uSp, max v uS uSp}
            ((((ULift.ringEquiv : ULift.{max v uS uSp} S' ≃+* S').symm.toRingHom.comp p).comp
              (ULift.ringEquiv : ULift.{max v uS uSp} S ≃+* S).toRingHom :
                ULift.{max v uS uSp} S →+* ULift.{max v uS uSp} S'))).mapHomologicalComplex
          (ComplexShape.up ℤ))
      (scalarLiftInverseFactors.{max v uS, uSp} S').inv

end Derived

end Dualizing

end
