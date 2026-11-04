module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem

/-!
# The two Gysin compatibilities at the Gysin system of the first Chern class rule

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. The Gysin system
`Stacks.Chow.gysinSystemOfInvertible`, whose rule is the first Chern class
`Stacks.Chow.firstChernComponentClass`, satisfies the two Gysin compatibilities
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`, the isomorphism case of Stacks 02TA, and
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`, the invariance of the Gysin
operation under the comparison of iterated pullbacks. Hence the composition of bivariant classes of
Stacks 0B75 and its composition formula (Stacks 0FE0) hold at that Gysin system with no hypothesis.

## Main definitions

* `Stacks.Chow.bivariantCompositeOfInvertible`: the composite of two bivariant classes at the Gysin
  system of the first Chern class rule.
* `Stacks.Chow.bivariantCompositeBilinearOfInvertible`: the composition of bivariant classes at
  that Gysin system, as a bilinear map.

## Main results

* `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso`: the Gysin system of the first
  Chern class rule is natural under pushforward along an isomorphism over a test scheme.
* `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward`: its Gysin operation
  is invariant under the comparison of iterated pullbacks.
* `Stacks.Chow.isBivariantClassComposition_bivariantCompositeOfInvertible`: the composite class at
  that Gysin system satisfies the composition formula.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Pushforward along the transport of an equality of closed subschemes -/

/-- Pushforward of Chow classes along the transport of an equality of closed subschemes carries the
value of a map to the value of any heterogeneously equal map. -/
theorem chowPushforwardOfIso_eqToHom_apply_of_heq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {D₁ D₂ : X.IdealSheafData} (hD : D₁ = D₂)
    [LocallyOfFiniteType (D₁.subschemeι ≫ p)] [LocallyOfFiniteType (D₂.subschemeι ≫ p)]
    (F₁ : chowGroup C p (k + 1) →+ chowGroup C (D₁.subschemeι ≫ p) k)
    (F₂ : chowGroup C p (k + 1) →+ chowGroup C (D₂.subschemeι ≫ p) k) (hF : F₁ ≍ F₂)
    (α : chowGroup C p (k + 1)) :
    chowPushforwardOfIso C (D₁.subschemeι ≫ p) (D₂.subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD))
        (by rw [← Category.assoc, subschemeι_eqToHom hD]) k (F₁ α) = F₂ α := by
  cases hD
  obtain rfl := eq_of_heq hF
  exact DFunLike.congr_fun (properChowPushforward_id C (D₁.subschemeι ≫ p) k _) (F₁ α)

/-- Pushforward of Chow classes along the transport of an equality `D₁ = D₂` of closed subschemes
followed by a proper morphism `h` carries the value of a map to the pushforward along `h` of the
value of any heterogeneously equal map. -/
theorem properChowPushforward_eqToHom_comp_apply_of_heq (C : ChowSituation.{u})
    {X W : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (k : ℤ) {D₁ D₂ : X.IdealSheafData} (hD : D₁ = D₂)
    [LocallyOfFiniteType (D₁.subschemeι ≫ p)] [LocallyOfFiniteType (D₂.subschemeι ≫ p)]
    (h : D₂.subscheme ⟶ W) [IsProper h] (hh : h ≫ sW = D₂.subschemeι ≫ p)
    (hcomp : (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD) ≫ h) ≫ sW =
      D₁.subschemeι ≫ p)
    (hfac₁ : ProperPushforwardFactorsThroughRationalEquivalence C (D₁.subschemeι ≫ p) sW
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD) ≫ h) hcomp k)
    (hfac₂ : ProperPushforwardFactorsThroughRationalEquivalence C (D₂.subschemeι ≫ p) sW h hh k)
    (F₁ : chowGroup C p (k + 1) →+ chowGroup C (D₁.subschemeι ≫ p) k)
    (F₂ : chowGroup C p (k + 1) →+ chowGroup C (D₂.subschemeι ≫ p) k) (hF : F₁ ≍ F₂)
    (α : chowGroup C p (k + 1)) :
    properChowPushforward C (D₁.subschemeι ≫ p) sW
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme hD) ≫ h) hcomp k hfac₁ (F₁ α) =
      properChowPushforward C (D₂.subschemeι ≫ p) sW h hh k hfac₂ (F₂ α) := by
  cases hD
  obtain rfl := eq_of_heq hF
  exact properChowPushforward_congr_hom C (D₁.subschemeι ≫ p) sW (by simp) hcomp hh k hfac₁
    hfac₂ (F₁ α)

/-! ### The Gysin system of the first Chern class rule satisfies both compatibilities -/

/-- The Gysin system of the first Chern class rule of an invertible module is natural under
pushforward along an isomorphism `u : A ⟶ B` of two schemes over a test scheme carrying the module,
the module on `A` and on `B` being its pullbacks from the test scheme. -/
@[stacks 02TA "the isomorphism case of the naturality of the Gysin operation of a Gysin system, \
for an invertible module pulled back from a test scheme to both schemes -- the form the Gysin \
axiom of a bivariant class quantifies over -- with no hypothesis"]
theorem gysinSystemOfInvertible_isNaturalUnderBaseChangeIso (C : ChowSituation.{u}) :
    (gysinSystemOfInvertible C).IsNaturalUnderBaseChangeIso := by
  intro A B T t _ qA _ qB _ u _ hu L _ s k _ _ j _ hjsq hj hfac α
  subst hu
  have hZZ := zeroScheme_pullback_pullback u qB L s
  have hassoc : u ≫ (qB ≫ t) = (u ≫ qB) ≫ t := (Category.assoc u qB t).symm
  have hφ := zeroSchemePullbackHom_subschemeι u ((Scheme.Modules.pullback qB).obj L)
    (AlgebraicGeometry.pullbackGlobalSections qB L s)
  obtain rfl : j = eqToHom (congrArg Scheme.IdealSheafData.subscheme hZZ.symm) ≫
      zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s) := by
    refine (cancel_mono (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι).1 ?_
    rw [hjsq, Category.assoc, hφ, ← Category.assoc, subschemeι_eqToHom hZZ.symm]
  refine (gysinSystemOfInvertible_isNaturalUnderProperPushforward C ((u ≫ qB) ≫ t) (qB ≫ t) u
    hassoc _ _ k _ hφ (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) α).trans ?_
  exact (properChowPushforward_eqToHom_comp_apply_of_heq C ((u ≫ qB) ≫ t) _ k hZZ.symm _
    (zeroSchemeSquare_comp_structureMorphism C ((u ≫ qB) ≫ t) (qB ≫ t) u hassoc _ _ _ hφ)
    hj hfac (properPushforwardDescends C _ _ _ _ _) _ _
    (heq_gysinHomomorphismOnChowOfInvertible C ((u ≫ qB) ≫ t) k
      ((Scheme.Modules.pullback (u ≫ qB)).obj L)
      ((Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback qB).obj L)) _ _
      ((Scheme.Modules.pullbackComp u qB).app L).symm hZZ.symm _ _) α).symm

/-- The Gysin operation of the Gysin system of the first Chern class rule does not see the
difference between an iterated pullback of an invertible module and the pullback along the
composite, the two equal zero schemes being identified by proper pushforward along the transport of
their equality. -/
theorem gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward (C : ChowSituation.{u}) :
    (gysinSystemOfInvertible C).IsNaturalUnderPullbackCompPushforward := by
  intro A B T q₁ q₂ p _ L _ s k α
  refine chowPushforwardOfIso_eqToHom_apply_of_heq C p k
    (Stacks.Divisors.zeroScheme_pullback_comp q₁ q₂ L s) _ _ ?_ α
  exact heq_gysinHomomorphismOnChowOfInvertible C p k
    ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
    ((Scheme.Modules.pullback (q₁ ≫ q₂)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
      (AlgebraicGeometry.pullbackGlobalSections q₂ L s))
    (AlgebraicGeometry.pullbackGlobalSections (q₁ ≫ q₂) L s)
    ((Scheme.Modules.pullbackComp q₁ q₂).app L)
    (Stacks.Divisors.zeroScheme_pullback_comp q₁ q₂ L s) _ _

/-! ### Stacks 0B75 at the Gysin system of the first Chern class rule -/

section Unconditional

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX)
  (hg : g ≫ sZ = sY) (p q : ℤ)

/-- The composite `a ∘ b ∈ A^{p+q}(X ⟶ Z)` of bivariant classes at the Gysin system of the first
Chern class rule of an invertible module. -/
@[stacks 0B75 "the composite bivariant class at the Gysin system of the first Chern class rule, \
with both cases of Stacks 02TA discharged"]
def bivariantCompositeOfInvertible
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) (p + q) :=
  bivariantComposite C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q a b
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- The composition `A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)` of bivariant classes as a bilinear
map, at the Gysin system of the first Chern class rule. -/
@[stacks 0B75 "the composition as a bilinear map, at the Gysin system of the first Chern class \
rule, with both cases of Stacks 02TA discharged"]
def bivariantCompositeBilinearOfInvertible :
    BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p →+
      BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q →+
        BivariantClass C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
          (comp_comp_structureMorphism_eq hf hg) (p + q) :=
  bivariantCompositeBilinear C (gysinSystemOfInvertible C) sX sY sZ f g hf hg p q
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- The composite class at the Gysin system of the first Chern class rule is *the* composite: on
every test scheme its cap operation is cap with `b` followed by cap with `a`, pushed forward along
the associativity isomorphism of pullbacks. -/
@[stacks 0FE0 "the composite class satisfies the composition formula, at the Gysin system of the \
first Chern class rule, with both cases of Stacks 02TA discharged"]
theorem isBivariantClassComposition_bivariantCompositeOfInvertible
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    IsBivariantClassComposition C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
      (properPushforwardDescends C) p q a b
      (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b) :=
  isBivariantClassComposition_bivariantComposite C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
    p q a b (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)

/-- The bilinear composition map applied to `a` and `b` is the composite class of `a` and `b`. -/
@[simp]
theorem bivariantCompositeBilinearOfInvertible_apply
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q) :
    bivariantCompositeBilinearOfInvertible C sX sY sZ f g hf hg p q a b =
      bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b :=
  rfl

end Unconditional

end Stacks.Chow

end
