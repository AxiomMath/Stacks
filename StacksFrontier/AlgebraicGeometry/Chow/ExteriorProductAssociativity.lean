module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FieldFibreDegreeBound
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Associativity of the exterior product

Let `X`, `Y` and `Z` be schemes locally of finite type over the base scheme `S` of chapter 42 of
the Stacks Project. The exterior product of cycles sends a pair of cycles on `X` and `Y` to a
cycle on `X ×_S Y`, so iterating it produces cycles on the two schemes

  `(X ×_S Y) ×_S Z`  and  `X ×_S (Y ×_S Z)`,

which are not the same scheme but are canonically isomorphic. Associativity of the exterior
product is therefore a statement about transport along that canonical isomorphism, and the
source's proof is the single observation that the fibre product of schemes is associative.

This file supplies the geometric half of that argument. The associator

  `(X ×_S Y) ×_S Z ≅ X ×_S (Y ×_S Z)`

is built from the associator of fibre products in an arbitrary category, mediated by the
identification of the two structure morphisms `pr_X ≫ f` and `pr_Y ≫ g` of `X ×_S Y`, and it is
characterised by its three projections. Under it the two bracketings of a triple product of
closed subschemes correspond: the ideal sheaf

  `pr_X⁻¹(I) + pr_Y⁻¹(J) + pr_Z⁻¹(K)`

computed with the left bracketing is the inverse image, along the associator, of the one
computed with the right bracketing. Consequently the multiplicity of a point in a triple product
of closed subschemes is the same on both sides, which is the content of the tag below at the
level of multiplicities: the weight attached to a point of the triple product does not depend on
how the product is bracketed.

Specialising the three ideal sheaves to the vanishing ideals of reduced point closures gives the
triple analogue of `Stacks.Chow.exteriorProductWeight`, and
`Stacks.Chow.tripleProductWeight_assoc` says that it is associative.

The two iterated exterior products of three cycles are also computed here. Writing `x`, `y` and
`z` for the three coordinates of a point `w` of `X ×_S (Y ×_S Z)`, both coefficients are

  `α(x) · β(y) · γ(z) · (first multiplicity) · (second multiplicity)`,

with the same three cycle coefficients on each side; the left bracketing contributes the
multiplicity of `closure {x} ×_S closure {y}` followed by that of a product with
`closure {z}`, and the right bracketing contributes the multiplicity of
`closure {y} ×_S closure {z}` followed by that of a product with `closure {x}`.

Each of those two products of multiplicities is the multiplicity of the triple product of the
three reduced point closures, because the multiplicity is multiplicative in a product of closed
subschemes one of whose factors is flat of constant fibre dimension over the base, and over a
field every reduced point closure is such a factor. Since the two triple multiplicities agree,
so do the two iterated exterior products: that is
`Stacks.Chow.exteriorProduct_assoc`, the associativity of the exterior product of cycles.

The multiplicativity rests in turn on the flat pullback cycle identity for an arbitrary — not
necessarily integral — closed subscheme, which is obtained here from the coherent-sheaf form of
that identity by passing from a closed subscheme to its structure sheaf.

Reading that identity modulo rational equivalence gives the tag itself, which is a statement
about Chow groups: `Stacks.Chow.chowExteriorProduct_assoc`.

## Main definitions

* `Stacks.Chow.tripleProductAssoc` — the canonical associator
  `(X ×_S Y) ×_S Z ≅ X ×_S (Y ×_S Z)`.
* `Stacks.Chow.FlatPullbackDescends` — Stacks 02S1 for every flat morphism over the base,
  bundled as a single hypothesis.
* `Stacks.Chow.tripleProductIdealLeft`, `Stacks.Chow.tripleProductIdealRight` — the ideal sheaf
  of a triple product of closed subschemes, in the two bracketings.
* `Stacks.Chow.tripleProductWeightLeft`, `Stacks.Chow.tripleProductWeightRight` — the
  multiplicity of a point in a triple product of reduced point closures, in the two bracketings.

## Main results

* `Stacks.Chow.tripleProductAssoc_hom_fst`, `Stacks.Chow.tripleProductAssoc_hom_snd_fst`,
  `Stacks.Chow.tripleProductAssoc_hom_snd_snd` — the three projections of the associator, which
  characterise it.
* `Stacks.Chow.comap_tripleProductIdealRight` — the two bracketings of a triple product of
  closed subschemes correspond under the associator.
* `Stacks.Chow.closedSubschemeCycleCoeff_tripleProductIdeal_assoc` — hence the cycle coefficient
  of a triple product of closed subschemes is the same in both bracketings, after transport
  along the associator.
* `Stacks.Chow.tripleProductWeight_assoc` — the multiplicity of a point in a triple product of
  reduced point closures is independent of the bracketing.
* `Stacks.Chow.exteriorProduct_exteriorProduct_apply` and
  `Stacks.Chow.exteriorProduct_exteriorProduct_apply_tripleProductAssoc_inv` — the coefficients
  of the two iterated exterior products of three cycles, both written in the three coordinates
  of a point of `X ×_S (Y ×_S Z)`.
* `Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme_of_le` — **Stacks 02RE, part (1),
  cycle identity**: the flat pullback of the cycle of an arbitrary closed subscheme of
  delta-dimension at most `k` is the cycle of its scheme-theoretic inverse image, and
  `Stacks.Chow.closedSubschemeCycleCoeff_comap` its coefficientwise form.
* `Stacks.Chow.closedSubschemeCycleCoeff_product_right` and
  `Stacks.Chow.closedSubschemeCycleCoeff_product_left` — the multiplicity of a point in a
  product of two closed subschemes factors as a product of two multiplicities, when one factor
  is flat of constant fibre dimension over the base.
* `Stacks.Chow.schemeDeltaDimension_product_le` — the delta-dimension of such a product is at
  most the sum.
* `Stacks.Chow.exteriorProduct_assoc` — the associativity of the exterior product of cycles over
  a field, stated coefficientwise.
* `Stacks.Chow.chowExteriorProduct_assoc_unconditional` — Tag 0FBZ with nothing assumed, and
  `Stacks.Chow.chowExteriorProduct_assoc` — Tag 0FBZ: the associativity of the
  exterior product on Chow groups over a field.

## Implementation notes

The associator is an honest composite of two canonical isomorphisms, not a choice of some
isomorphism asserted to exist: `(X ×_S Y) ×_S Z` is presented with structure morphism
`pr_X ≫ f`, whereas `CategoryTheory.Limits.pullbackAssoc` presents it with `pr_Y ≫ g`, and
`CategoryTheory.Limits.pullback.congrHom` applied to `pullback.condition` bridges the two. Its
three projection identities are then read off from the corresponding identities for
`CategoryTheory.Limits.pullbackAssoc`.

The associator, the correspondence of the two triple product ideal sheaves and the equality of
the two triple multiplicities need no hypothesis beyond a `Stacks.Chow.ChowSituation`: they are
consequences of the associativity of the fibre product alone. The base enters only in the
factorisation of a product multiplicity into two, where the second factor must be flat of
constant fibre dimension over the base; the final associativity statement is therefore over
`Stacks.Chow.fieldChowSituation`, the base situation of the spectrum of a field with its
constant-zero dimension function, which is also the setting of the source. No cycle-level result
here is stated as an equality of cycles, because the two iterated exterior products live in
cycle groups of delta-dimension `(n + m) + l` and `n + (m + l)`, equal integers but not
syntactically equal ones; those results are therefore phrased coefficientwise, at a point of
`X ×_S (Y ×_S Z)` and its image under the inverse of the associator.

The Chow-group statement is an honest equality, with both discrepancies made explicit: the left
bracketing is carried across by `Stacks.Chow.chowPushforwardOfIso` along the associator, which
is an isomorphism over the base, and then across the two readings of the degree by
`Stacks.Chow.chowGroupDegreeEquiv`. Neither transport changes a coefficient, so no content is
hidden in them: pushforward along an isomorphism only reindexes coefficients
(`Stacks.Chow.properPushforward_apply_of_isIso`) and the degree transport is the identity after
substituting the equality of degrees. It is stated on pure tensors of classes, which is how
`Stacks.Chow.chowExteriorProduct` is evaluated on a pair of classes, and it carries no
hypothesis: over the spectrum of a field the exterior product on Chow groups is unconditional,
the instances of Stacks 02S1 needed for it to be well defined being discharged inside
`Stacks.Chow.chowExteriorProduct` itself.

The two bracketings of the triple ideal sheaf are built, as in
`Stacks.Chow.exteriorProductIdeal`, from the sum of the inverse images of the three ideal
sheaves; `Stacks.Chow.tripleProductIdealLeft_eq_exteriorProductIdeal_comap_sup` and its mirror
record that each of them is the exterior product ideal of a pair, pulled back and summed with
the inverse image of the remaining factor, which is the form in which an iterated exterior
product presents it.

## References

* [Stacks Project, Tag 0FBZ](https://stacks.math.columbia.edu/tag/0FBZ)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The associator of a triple fibre product -/

/-- The canonical associator `(X ×_S Y) ×_S Z ≅ X ×_S (Y ×_S Z)` of a triple fibre product over
a common base. The left-hand product is formed along the structure morphism `pr_X ≫ f` of
`X ×_S Y`; replacing it by the equal morphism `pr_Y ≫ g` turns the left-hand product into the
shape handled by `CategoryTheory.Limits.pullbackAssoc`. -/
@[ega "I 3.3.5" "special case"]
def tripleProductAssoc {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    (pullback (pullback.fst f g ≫ f) h : Scheme.{u}) ≅
      (pullback f (pullback.fst g h ≫ g) : Scheme.{u}) :=
  pullback.congrHom (pullback.condition (f := f) (g := g)) rfl ≪≫ pullbackAssoc f g g h

/-- The first projection of the associator: the `X`-component of `X ×_S (Y ×_S Z)` is the
`X`-component of the `X ×_S Y`-component of `(X ×_S Y) ×_S Z`. -/
theorem tripleProductAssoc_hom_fst {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    (tripleProductAssoc f g h).hom ≫ pullback.fst f (pullback.fst g h ≫ g) =
      pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g := by
  rw [tripleProductAssoc, Iso.trans_hom, Category.assoc, pullbackAssoc_hom_fst,
    pullback.congrHom_hom, pullback.map, ← Category.assoc]
  simp only [pullback.lift_fst, Category.comp_id]

/-- The `Y`-component of the associator: the `Y`-component of the `Y ×_S Z`-component of
`X ×_S (Y ×_S Z)` is the `Y`-component of the `X ×_S Y`-component of `(X ×_S Y) ×_S Z`. -/
theorem tripleProductAssoc_hom_snd_fst {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) :
    (tripleProductAssoc f g h).hom ≫ pullback.snd f (pullback.fst g h ≫ g) ≫
        pullback.fst g h =
      pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.snd f g := by
  rw [tripleProductAssoc, Iso.trans_hom, Category.assoc, pullbackAssoc_hom_snd_fst,
    pullback.congrHom_hom, pullback.map, ← Category.assoc]
  simp only [pullback.lift_fst, Category.comp_id]

/-- The `Z`-component of the associator: the `Z`-component of the `Y ×_S Z`-component of
`X ×_S (Y ×_S Z)` is the `Z`-component of `(X ×_S Y) ×_S Z`. -/
theorem tripleProductAssoc_hom_snd_snd {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) :
    (tripleProductAssoc f g h).hom ≫ pullback.snd f (pullback.fst g h ≫ g) ≫
        pullback.snd g h =
      pullback.snd (pullback.fst f g ≫ f) h := by
  rw [tripleProductAssoc, Iso.trans_hom, Category.assoc, pullbackAssoc_hom_snd_snd,
    pullback.congrHom_hom, pullback.map]
  simp only [pullback.lift_snd, Category.comp_id]

/-- The associator is a morphism over the base: it carries the structure morphism of
`X ×_S (Y ×_S Z)` to the structure morphism of `(X ×_S Y) ×_S Z`. -/
theorem tripleProductAssoc_hom_comp_base {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) :
    (tripleProductAssoc f g h).hom ≫ pullback.fst f (pullback.fst g h ≫ g) ≫ f =
      pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f := by
  rw [← Category.assoc, tripleProductAssoc_hom_fst, Category.assoc]

/-- Applying the associator to the inverse image of a point returns the point. -/
@[simp]
theorem tripleProductAssoc_hom_base_inv_base {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (tripleProductAssoc f g h).hom.base ((tripleProductAssoc f g h).inv.base w) = w := by
  change ((tripleProductAssoc f g h).inv ≫ (tripleProductAssoc f g h).hom).base w = w
  rw [Iso.inv_hom_id]
  rfl

/-- A projection of the left bracketing, applied to the transport along the inverse associator,
is the corresponding projection of the right bracketing. -/
private theorem base_tripleProductAssoc_inv {S X Y Z T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) (a : (pullback (pullback.fst f g ≫ f) h : Scheme.{u}) ⟶ T)
    (b : (pullback f (pullback.fst g h ≫ g) : Scheme.{u}) ⟶ T)
    (hab : (tripleProductAssoc f g h).hom ≫ b = a)
    (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    a.base ((tripleProductAssoc f g h).inv.base w) = b.base w := by
  rw [← hab, Scheme.Hom.comp_apply, tripleProductAssoc_hom_base_inv_base]

/-- The `X`-coordinate of a point of `(X ×_S Y) ×_S Z` transported from `X ×_S (Y ×_S Z)` is the
`X`-coordinate of the original point. -/
theorem fst_fst_tripleProductAssoc_inv {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (pullback.fst f g).base ((pullback.fst (pullback.fst f g ≫ f) h).base
        ((tripleProductAssoc f g h).inv.base w)) =
      (pullback.fst f (pullback.fst g h ≫ g)).base w := by
  exact base_tripleProductAssoc_inv f g h _ _ (tripleProductAssoc_hom_fst f g h) w

/-- The `Y`-coordinate of a point of `(X ×_S Y) ×_S Z` transported from `X ×_S (Y ×_S Z)` is the
`Y`-coordinate of the original point. -/
theorem snd_fst_tripleProductAssoc_inv {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (pullback.snd f g).base ((pullback.fst (pullback.fst f g ≫ f) h).base
        ((tripleProductAssoc f g h).inv.base w)) =
      (pullback.fst g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w) := by
  exact base_tripleProductAssoc_inv f g h _ _ (tripleProductAssoc_hom_snd_fst f g h) w

/-- The `Z`-coordinate of a point of `(X ×_S Y) ×_S Z` transported from `X ×_S (Y ×_S Z)` is the
`Z`-coordinate of the original point. -/
theorem snd_tripleProductAssoc_inv {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (pullback.snd (pullback.fst f g ≫ f) h).base ((tripleProductAssoc f g h).inv.base w) =
      (pullback.snd g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w) := by
  exact base_tripleProductAssoc_inv f g h _ _ (tripleProductAssoc_hom_snd_snd f g h) w

/-! ### The triple product of three closed subschemes -/

/-- The ideal sheaf on `(X ×_S Y) ×_S Z` cutting out the triple product of the closed subschemes
of `I`, `J` and `K`: the sum of the inverse images of the three ideal sheaves along the three
projections, with the product bracketed to the left. -/
def tripleProductIdealLeft {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (K : Z.IdealSheafData) :
    (pullback (pullback.fst f g ≫ f) h : Scheme.{u}).IdealSheafData :=
  (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).comap
      (pullback.fst (pullback.fst f g ≫ f) h) ⊔
    K.comap (pullback.snd (pullback.fst f g ≫ f) h)

/-- The ideal sheaf on `X ×_S (Y ×_S Z)` cutting out the triple product of the closed subschemes
of `I`, `J` and `K`, with the product bracketed to the right. -/
def tripleProductIdealRight {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (K : Z.IdealSheafData) :
    (pullback f (pullback.fst g h ≫ g) : Scheme.{u}).IdealSheafData :=
  I.comap (pullback.fst f (pullback.fst g h ≫ g)) ⊔
    (J.comap (pullback.fst g h) ⊔ K.comap (pullback.snd g h)).comap
      (pullback.snd f (pullback.fst g h ≫ g))

/-- The left-bracketed triple product of three reduced point closures is the product of the
first two, pulled back to `(X ×_S Y) ×_S Z`, together with the inverse image of the third. -/
theorem tripleProductIdealLeft_eq_exteriorProductIdeal_comap_sup {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (x : X) (y : Y) (z : Z) :
    tripleProductIdealLeft f g h
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y)))
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set Z))) =
      (exteriorProductIdeal f g x y).comap (pullback.fst (pullback.fst f g ≫ f) h) ⊔
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set Z))).comap
          (pullback.snd (pullback.fst f g ≫ f) h) :=
  rfl

/-- The right-bracketed triple product of three reduced point closures is the inverse image of
the first factor together with the product of the last two, pulled back to `X ×_S (Y ×_S Z)`. -/
theorem tripleProductIdealRight_eq_exteriorProductIdeal_comap_sup {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (x : X) (y : Y) (z : Z) :
    tripleProductIdealRight f g h
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y)))
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set Z))) =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).comap
          (pullback.fst f (pullback.fst g h ≫ g)) ⊔
        (exteriorProductIdeal g h y z).comap (pullback.snd f (pullback.fst g h ≫ g)) :=
  rfl

/-- **The associativity of the triple product of closed subschemes.** The ideal sheaf of the
left-bracketed triple product is the inverse image, along the associator, of the ideal sheaf of
the right-bracketed one: the three projections agree, and the sum of three ideal sheaves does
not depend on how it is bracketed. -/
theorem comap_tripleProductIdealRight {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) (I : X.IdealSheafData) (J : Y.IdealSheafData) (K : Z.IdealSheafData) :
    (tripleProductIdealRight f g h I J K).comap (tripleProductAssoc f g h).hom =
      tripleProductIdealLeft f g h I J K := by
  simp only [tripleProductIdealRight, tripleProductIdealLeft,
    Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp]
  rw [tripleProductAssoc_hom_fst, tripleProductAssoc_hom_snd_fst,
    tripleProductAssoc_hom_snd_snd]
  simp only [Scheme.IdealSheafData.comap_comp, sup_assoc]

/-! ### The cycle coefficient of a triple product -/

/-- **The associativity of the multiplicity in a triple product of closed subschemes.** The
coefficient of the cycle of the left-bracketed triple product at the transport of a point `w`
along the associator equals the coefficient of the cycle of the right-bracketed triple product
at `w`.

The associator identifies the two triple products as closed subschemes, by
`Stacks.Chow.comap_tripleProductIdealRight`, and the coefficient of the cycle of a closed
subscheme depends only on that subscheme and is unchanged by transporting the ambient scheme
along an isomorphism over the base. -/
theorem closedSubschemeCycleCoeff_tripleProductIdeal_assoc (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (h : Z ⟶ C.S) [LocallyOfFiniteType h] (I : X.IdealSheafData)
    (J : Y.IdealSheafData) (K : Z.IdealSheafData) (d : ℤ)
    (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    closedSubschemeCycleCoeff C
        (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
        (tripleProductIdealLeft f g h I J K).subschemeι d
        ((tripleProductAssoc f g h).inv.base w) =
      closedSubschemeCycleCoeff C (pullback.fst f (pullback.fst g h ≫ g) ≫ f)
        (tripleProductIdealRight f g h I J K).subschemeι d w := by
  set e := tripleProductAssoc f g h with he
  set IR := tripleProductIdealRight f g h I J K with hIR
  rw [← closedSubschemeCycleCoeff_congr_idealSheaf C
    (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
    (comap_tripleProductIdealRight f g h I J K) d ((tripleProductAssoc f g h).inv.base w)]
  rw [closedSubschemeCycleCoeff_of_isIso_ambient C
    (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
    (pullback.fst f (pullback.fst g h ≫ g) ≫ f) e.hom
    (tripleProductAssoc_hom_comp_base f g h) (IR.comap e.hom).subschemeι d
    (e.inv.base w), he, tripleProductAssoc_hom_base_inv_base]
  exact closedSubschemeCycleCoeff_eq_of_iso C (pullback.fst f (pullback.fst g h ≫ g) ≫ f)
    ((IR.comap e.hom).subschemeι ≫ e.hom) IR.subschemeι
    (comapSubschemeIsoOfIsIso e.hom IR) (comapSubschemeIsoOfIsIso_hom_subschemeι e.hom IR) d w

/-! ### The multiplicity of a triple product of reduced point closures -/

/-- The multiplicity with which a point of `(X ×_S Y) ×_S Z` enters the delta-dimension `j`
cycle of the triple product `(closure {x} ×_S closure {y}) ×_S closure {z}` of the reduced
closures of three points. -/
def tripleProductWeightLeft (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (h : Z ⟶ C.S)
    [LocallyOfFiniteType h] (j : ℤ) (x : X) (y : Y) (z : Z)
    (u : (pullback (pullback.fst f g ≫ f) h : Scheme.{u})) : ℤ :=
  closedSubschemeCycleCoeff C (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
    (tripleProductIdealLeft f g h
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y)))
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set Z)))).subschemeι j u

/-- The multiplicity with which a point of `X ×_S (Y ×_S Z)` enters the delta-dimension `j`
cycle of the triple product `closure {x} ×_S (closure {y} ×_S closure {z})` of the reduced
closures of three points. -/
def tripleProductWeightRight (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (h : Z ⟶ C.S)
    [LocallyOfFiniteType h] (j : ℤ) (x : X) (y : Y) (z : Z)
    (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) : ℤ :=
  closedSubschemeCycleCoeff C (pullback.fst f (pullback.fst g h ≫ g) ≫ f)
    (tripleProductIdealRight f g h
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y)))
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set Z)))).subschemeι j w

/-- **Associativity of the triple product multiplicity.** The multiplicity of a point of
`X ×_S (Y ×_S Z)` in a triple product of three reduced point closures does not depend on how the
product is bracketed, the two sides being compared along the canonical associator. -/
theorem tripleProductWeight_assoc (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (h : Z ⟶ C.S)
    [LocallyOfFiniteType h] (j : ℤ) (x : X) (y : Y) (z : Z)
    (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    tripleProductWeightLeft C f g h j x y z ((tripleProductAssoc f g h).inv.base w) =
      tripleProductWeightRight C f g h j x y z w :=
  closedSubschemeCycleCoeff_tripleProductIdeal_assoc C f g h _ _ _ j w

/-! ### The coefficients of the two iterated exterior products -/

/-- The coefficient of the left-bracketed iterated exterior product `(α × β) × γ`, evaluated at
the transport along the associator of a point `w` of `X ×_S (Y ×_S Z)` and expressed in the
three coordinates of `w`: it is the product of the three cycle coefficients with the two
multiplicities that the iteration contributes, namely that of `closure {x} ×_S closure {y}` at
the `X ×_S Y`-coordinate and that of `closure {pr_{XY} w} ×_S closure {z}` at `w` itself. -/
theorem exteriorProduct_exteriorProduct_apply_tripleProductAssoc_inv (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (h : Z ⟶ C.S) [LocallyOfFiniteType h] (n m l : ℤ)
    (α : CycleGroup C f n) (β : CycleGroup C g m) (γ : CycleGroup C h l)
    (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (exteriorProduct C (pullback.fst f g ≫ f) h (n + m) l
        (exteriorProduct C f g n m α β) γ).1 ((tripleProductAssoc f g h).inv.base w) =
      α.1 ((pullback.fst f (pullback.fst g h ≫ g)).base w) *
          β.1 ((pullback.fst g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w)) *
          γ.1 ((pullback.snd g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w)) *
        (exteriorProductWeight C f g (n + m)
            ((pullback.fst f (pullback.fst g h ≫ g)).base w)
            ((pullback.fst g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w))
            ((pullback.fst (pullback.fst f g ≫ f) h).base
              ((tripleProductAssoc f g h).inv.base w)) *
          exteriorProductWeight C (pullback.fst f g ≫ f) h (n + m + l)
            ((pullback.fst (pullback.fst f g ≫ f) h).base
              ((tripleProductAssoc f g h).inv.base w))
            ((pullback.snd g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w))
            ((tripleProductAssoc f g h).inv.base w)) := by
  rw [exteriorProduct_apply, exteriorProduct_apply, snd_tripleProductAssoc_inv,
    fst_fst_tripleProductAssoc_inv, snd_fst_tripleProductAssoc_inv]
  ring

/-- The coefficient of the right-bracketed iterated exterior product `α × (β × γ)` at a point
`w` of `X ×_S (Y ×_S Z)`, expressed in the three coordinates of `w`: it is the product of the
three cycle coefficients with the multiplicity of `closure {y} ×_S closure {z}` at the
`Y ×_S Z`-coordinate and that of `closure {x} ×_S closure {pr_{YZ} w}` at `w` itself. -/
theorem exteriorProduct_exteriorProduct_apply (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (h : Z ⟶ C.S)
    [LocallyOfFiniteType h] (n m l : ℤ) (α : CycleGroup C f n) (β : CycleGroup C g m)
    (γ : CycleGroup C h l) (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (exteriorProduct C f (pullback.fst g h ≫ g) n (m + l) α
        (exteriorProduct C g h m l β γ)).1 w =
      α.1 ((pullback.fst f (pullback.fst g h ≫ g)).base w) *
          β.1 ((pullback.fst g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w)) *
          γ.1 ((pullback.snd g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w)) *
        (exteriorProductWeight C g h (m + l)
            ((pullback.fst g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w))
            ((pullback.snd g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w))
            ((pullback.snd f (pullback.fst g h ≫ g)).base w) *
          exteriorProductWeight C f (pullback.fst g h ≫ g) (n + (m + l))
            ((pullback.fst f (pullback.fst g h ≫ g)).base w)
            ((pullback.snd f (pullback.fst g h ≫ g)).base w) w) := by
  rw [exteriorProduct_apply, exteriorProduct_apply]
  ring

/-! ### Flat pullback of the cycle of an arbitrary closed subscheme -/

/-- **Stacks 02RE, part (1), cycle identity.** For `q : X' ⟶ X` flat of relative dimension `r`
between schemes locally of finite type over the base of chapter 42, and `i : Z ⟶ X` a closed
subscheme of delta-dimension at most `k`, the flat pullback of the cycle `[Z]_k` is the cycle
`[q^{-1}(Z)]_{k+r}` of the scheme-theoretic inverse image, here presented as `pullback.fst q i`:

`q^*[Z]_k = [X' ×_X Z]_{k+r}`.

No irreducibility is assumed of `Z` and only an inequality on its delta-dimension is required,
so this is the full generality of the source; the integral case is
`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme`, which carries `@[stacks 02RB]`.
The companion dimension bound `dim_δ(q^{-1}(Z)) ≤ k + r`, in the same presentation of the
inverse image, is `Stacks.Chow.schemeDeltaDimension_pullback_le`.

The source deduces part (1) from part (2), and so does this proof: `[Z]_k` is the cycle of the
coherent sheaf `i_* 𝒪_Z` by Stacks 02QY, flat pullback commutes with passing to the cycle of a
coherent sheaf by Stacks 02RE part (2),
`Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf`, and the inverse image of `i_* 𝒪_Z`
along `q` is the direct image of the structure sheaf of `X' ×_X Z` — the identity
`q^* 𝒪_Z = 𝒪_{q^{-1}(Z)}` of the source — because a closed immersion is affine and so its
direct image commutes with the flat base change. -/
@[stacks 02RE "part (1): cycle identity"]
theorem flatPullback_cycleAssociatedToClosedSubscheme_of_le (C : ChowSituation.{u})
    {X' X Z : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (q : X' ⟶ X) [LocallyOfFiniteType q] [Flat q]
    (hbase : q ≫ sX = sX') (r : ℕ) (hq : AlgebraicGeometry.RelativeDimension q r)
    (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (hZ : schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt)) :
    flatPullback C sX' sX q hbase r hq k (cycleAssociatedToClosedSubscheme C sX i k) =
      cycleAssociatedToClosedSubscheme C sX' (pullback.fst q i) (k + (r : ℤ)) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let _ : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
  let _ : ((Scheme.Modules.pullback q).obj
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback q _
  rw [cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C sX i k hZ,
    flatPullback_cycleAssociatedToCoherentSheaf C sX' sX q hbase r hq
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) k
      (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C sX i hZ),
    cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C sX' (pullback.fst q i)
      (k + (r : ℤ)) (schemeDeltaDimension_pullback_le C sX' sX q hbase r hq i k hZ)]
  exact cycleAssociatedToCoherentSheaf_eq_of_iso C sX'
    (pullbackPushforwardStructureSheafIso (IsPullback.of_hasPullback q i).flip) _ _ _

/-- The coefficientwise form of the flat pullback cycle identity: the coefficient at `x'` of the
cycle of the inverse image of a closed subscheme of delta-dimension at most `d` is the
coefficient of the subscheme at `q x'` times the flat pullback multiplicity at `x'`. -/
theorem closedSubschemeCycleCoeff_comap (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (q : X' ⟶ X) [LocallyOfFiniteType q] [Flat q] (hbase : q ≫ sX = sX') (r : ℕ)
    (hq : AlgebraicGeometry.RelativeDimension q r) (I : X.IdealSheafData) (d : ℤ)
    (hI : schemeDeltaDimension C (I.subschemeι ≫ sX) ≤ (d : EInt)) (x' : X') :
    closedSubschemeCycleCoeff C sX' (I.comap q).subschemeι (d + (r : ℤ)) x' =
      closedSubschemeCycleCoeff C sX I.subschemeι d (q.base x') *
        flatPullbackWeight C sX' q (d + (r : ℤ)) x' := by
  have h := congrArg (fun c : CycleGroup C sX' (d + (r : ℤ)) ↦ c.1 x')
    (flatPullback_cycleAssociatedToClosedSubscheme_of_le C sX' sX q hbase r hq
      I.subschemeι d hI)
  rw [flatPullback_apply] at h
  refine Eq.trans ?_ h.symm
  exact closedSubschemeCycleCoeff_eq_of_iso C sX' (I.comap q).subschemeι
    (pullback.fst q I.subschemeι) (I.comapIso q) (I.comapIso_hom_fst q) (d + (r : ℤ)) x'

/-! ### Restricting the ambient scheme along a closed immersion -/

/-- The cycle coefficient of a closed subscheme of a closed subscheme `j : Y ⟶ X` may be computed
inside `Y`: the multiplicity is a length of the same stalk, and the relative dimension over the
base is unchanged by a closed immersion. -/
private theorem closedSubschemeCycleCoeff_comp_closedImmersion (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (j : Y ⟶ X)
    [IsClosedImmersion j] (i : Z ⟶ Y) [IsClosedImmersion i] (k : ℤ) (y : Y) :
    closedSubschemeCycleCoeff C p (i ≫ j) k (j.base y) =
      closedSubschemeCycleCoeff C (j ≫ p) i k y := by
  classical
  have hdim : relativeDimension C.dimensionFunction p (j.base y) =
      relativeDimension C.dimensionFunction (j ≫ p) y :=
    (relativeDimension_comp_closedImmersion C.dimensionFunction j p y).symm
  have hPQ : ∀ ξ : genericPoints Z,
      ((i ≫ j).base ξ.1 = j.base y ∧ relativeDimension C.dimensionFunction p (j.base y) = k) ↔
        (i.base ξ.1 = y ∧ relativeDimension C.dimensionFunction (j ≫ p) y = k) := by
    intro ξ
    constructor
    · rintro ⟨hpt, hd⟩
      exact ⟨j.isClosedEmbedding.injective (by simpa only [Scheme.Hom.comp_apply] using hpt),
        hdim ▸ hd⟩
    · rintro ⟨hpt, hd⟩
      exact ⟨by simp only [Scheme.Hom.comp_apply, hpt], hdim.trans hd⟩
  unfold closedSubschemeCycleCoeff
  by_cases h : ∃ ξ : genericPoints Z,
      (i ≫ j).base ξ.1 = j.base y ∧ relativeDimension C.dimensionFunction p (j.base y) = k
  · have h' : ∃ ξ : genericPoints Z,
        i.base ξ.1 = y ∧ relativeDimension C.dimensionFunction (j ≫ p) y = k := by
      obtain ⟨ξ, hξ⟩ := h
      exact ⟨ξ, (hPQ ξ).1 hξ⟩
    rw [dite_eq_left h, dite_eq_left h']
    have hchoose : Classical.choose h = Classical.choose h' := by
      apply Subtype.ext
      refine i.isClosedEmbedding.injective (Eq.trans ?_ (Classical.choose_spec h').1.symm)
      exact j.isClosedEmbedding.injective
        (by simpa only [Scheme.Hom.comp_apply] using (Classical.choose_spec h).1)
    rw [hchoose]
    exact componentMultiplicity_comp_of_isClosedImmersion i j (Classical.choose h')
  · have h' : ¬ ∃ ξ : genericPoints Z,
        i.base ξ.1 = y ∧ relativeDimension C.dimensionFunction (j ≫ p) y = k :=
      fun hq ↦ h ⟨hq.choose, (hPQ hq.choose).2 hq.choose_spec⟩
    rw [dite_eq_right h, dite_eq_right h']

/-- The cycle coefficient of the closed subscheme pushed forward along a closed immersion
`j : Y ⟶ X` is the cycle coefficient computed inside `Y`. -/
private theorem closedSubschemeCycleCoeff_map_closedImmersion (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (j : Y ⟶ X)
    [IsClosedImmersion j] (I : Y.IdealSheafData) (d : ℤ) (y : Y) :
    closedSubschemeCycleCoeff C p (I.map j).subschemeι d (j.base y) =
      closedSubschemeCycleCoeff C (j ≫ p) I.subschemeι d y := by
  refine Eq.trans ?_ (closedSubschemeCycleCoeff_comp_closedImmersion C p j I.subschemeι d y)
  exact (closedSubschemeCycleCoeff_eq_of_iso C p (I.subschemeι ≫ j) (I.map j).subschemeι
    (imageIsoOfIsClosedImmersion j I) (imageIsoOfIsClosedImmersion_hom_subschemeι j I)
    d (j.base y)).symm

/-- Pulling an ideal sheaf back along a closed immersion and pushing it forward again adds the
kernel of the immersion: the inverse image records nothing outside the closed subscheme. -/
private theorem map_comap_closedImmersion {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] (I : X.IdealSheafData) : (I.comap j).map j = I ⊔ j.ker := by
  refine le_antisymm ?_ (sup_le (I.le_map_comap j) ?_)
  · have ha : IsClosedImmersion.lift j (I ⊔ j.ker).subschemeι
        (by simpa only [Scheme.IdealSheafData.ker_subschemeι] using
          (le_sup_right : j.ker ≤ I ⊔ j.ker)) ≫ j = (I ⊔ j.ker).subschemeι :=
      IsClosedImmersion.lift_fac _ _ _
    have hb : Scheme.IdealSheafData.inclusion (show I ≤ I ⊔ j.ker from le_sup_left) ≫
        I.subschemeι = (I ⊔ j.ker).subschemeι := by simp
    rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker,
      ← (I ⊔ j.ker).ker_subschemeι,
      ← show pullback.lift _ _ (ha.trans hb.symm) ≫ (pullback.fst j I.subschemeι ≫ j) =
          (I ⊔ j.ker).subschemeι by simp only [pullback.lift_fst_assoc, ha]]
    exact Scheme.Hom.le_ker_comp _ _
  · rw [← Scheme.IdealSheafData.map_bot j]
    exact Scheme.IdealSheafData.map_mono j bot_le

/-- The coefficientwise flat pullback identity, transported into a closed subscheme `j : T ⟶ X`
of the ambient scheme along which the flat morphism `q` is taken. -/
private theorem closedSubschemeCycleCoeff_map_comap (C : ChowSituation.{u})
    {X Y T : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (j : T ⟶ X) [IsClosedImmersion j] (q : T ⟶ Y)
    [LocallyOfFiniteType q] [Flat q] (hbase : q ≫ sY = j ≫ p) (r : ℕ)
    (hq : AlgebraicGeometry.RelativeDimension q r) (I : Y.IdealSheafData) (d : ℤ)
    (hI : schemeDeltaDimension C (I.subschemeι ≫ sY) ≤ (d : EInt)) (t : T) :
    closedSubschemeCycleCoeff C p ((I.comap q).map j).subschemeι (d + (r : ℤ)) (j.base t) =
      closedSubschemeCycleCoeff C sY I.subschemeι d (q.base t) *
        closedSubschemeCycleCoeff C p
          ((((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({q.base t} : Set Y))).comap q).map j).subschemeι)
          (d + (r : ℤ)) (j.base t) := by
  simp only [closedSubschemeCycleCoeff_map_closedImmersion]
  exact closedSubschemeCycleCoeff_comap C (j ≫ p) sY q hbase r hq I d hI t

/-! ### Multiplicativity of the multiplicity in a product -/

/-- The projection `(X ×_S Y) ×_Y K ⟶ X ×_S Y ⟶ X` is flat of relative dimension `r` and locally of
finite type when `K ⟶ S` is: it is a base change of `K ⟶ S`. -/
private theorem flat_relativeDimension_pullback_snd_subschemeι {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (K : Y.IdealSheafData) [Flat (K.subschemeι ≫ g)]
    [LocallyOfFiniteType (K.subschemeι ≫ g)] (r : ℕ)
    (hK : AlgebraicGeometry.RelativeDimension (K.subschemeι ≫ g) r) :
    ∃ (_ : Flat (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g))
      (_ : LocallyOfFiniteType (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)),
      AlgebraicGeometry.RelativeDimension
        (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g) r := by
  have sq : IsPullback (pullback.snd (pullback.snd f g) K.subschemeι)
      (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)
      (K.subschemeι ≫ g) f :=
    (IsPullback.of_hasPullback (pullback.snd f g) K.subschemeι).flip.paste_vert
      (IsPullback.of_hasPullback f g).flip
  exact ⟨MorphismProperty.of_isPullback sq (P := @Flat) inferInstance,
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance,
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hK⟩

/-- The product of an ideal sheaf pulled back to `(X ×_S Y) ×_Y K` and pushed forward again is the
product of `A` with `K`. -/
private theorem map_comap_pullback_snd_subschemeι {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : Y.IdealSheafData) (A : X.IdealSheafData) :
    (A.comap (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)).map
        (pullback.fst (pullback.snd f g) K.subschemeι) =
      A.comap (pullback.fst f g) ⊔ K.comap (pullback.snd f g) := by
  rw [Scheme.IdealSheafData.comap_comp, map_comap_closedImmersion]
  rfl

/-- **Multiplicativity of the multiplicity in a product, peeling off the second factor.** Let
`I` be an ideal sheaf on `X` whose closed subscheme has delta-dimension at most `d`, and let `K`
be an ideal sheaf on `Y` whose closed subscheme is flat of relative dimension `r` over the base.
At a point `z` of `X ×_S Y` lying over the closed subscheme of `K`, the multiplicity of `z` in
the product of the two closed subschemes factors as the multiplicity of `pr_X z` in the closed
subscheme of `I`, times the multiplicity of `z` in the product of the reduced closure of
`pr_X z` with the closed subscheme of `K`.

The product `(I ×_S K)` is the inverse image of `I` along the projection
`(X ×_S Y) ×_Y K ⟶ X`, which is a flat morphism of relative dimension `r` because it is a base
change of `K ⟶ S`; the factorisation is then the coefficientwise flat pullback identity
transported into the closed subscheme `(X ×_S Y) ×_Y K` of `X ×_S Y`. -/
theorem closedSubschemeCycleCoeff_product_right (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g]
    (I : X.IdealSheafData) (K : Y.IdealSheafData) [Flat (K.subschemeι ≫ g)] (r : ℕ)
    (hK : AlgebraicGeometry.RelativeDimension (K.subschemeι ≫ g) r)
    (d : ℤ) (hI : schemeDeltaDimension C (I.subschemeι ≫ f) ≤ (d : EInt))
    (z : (pullback f g : Scheme.{u})) (hz : (pullback.snd f g).base z ∈ K.support) :
    closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        (I.comap (pullback.fst f g) ⊔ K.comap (pullback.snd f g)).subschemeι
        (d + (r : ℤ)) z =
      closedSubschemeCycleCoeff C f I.subschemeι d ((pullback.fst f g).base z) *
        closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
          ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({(pullback.fst f g).base z} : Set X))).comap
              (pullback.fst f g) ⊔ K.comap (pullback.snd f g)).subschemeι
          (d + (r : ℤ)) z := by
  obtain ⟨_, _, hq⟩ := flat_relativeDimension_pullback_snd_subschemeι f g K r hK
  have hz' : z ∈ Set.range (pullback.fst (pullback.snd f g) K.subschemeι).base := by
    rw [Scheme.Pullback.range_fst, K.range_subschemeι]
    exact hz
  obtain ⟨t, ht⟩ := hz'
  have H := closedSubschemeCycleCoeff_map_comap C (pullback.fst f g ≫ f) f
    (pullback.fst (pullback.snd f g) K.subschemeι)
    (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)
    (by simp only [Category.assoc]) r hq I d hI t
  have hqt : (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g).base t =
      (pullback.fst f g).base z := by
    rw [Scheme.Hom.comp_apply, ht]
  rw [map_comap_pullback_snd_subschemeι, map_comap_pullback_snd_subschemeι, ht, hqt] at H
  exact H

/-! ### Delta-dimension of a product -/

/-- A delta-dimension bound transports along an isomorphism over the base. The two structure
morphisms and the triangle relating them are taken as arguments rather than rewritten, because
the delta-dimension of a morphism carries that morphism in the type of its finite-type
instance. -/
private theorem schemeDeltaDimension_le_of_iso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ≅ B)
    (hcomp : e.hom ≫ sB = sA) (k : ℤ) (hB : schemeDeltaDimension C sB ≤ (k : EInt)) :
    schemeDeltaDimension C sA ≤ (k : EInt) := by
  have hpt : ∀ a : A, relativeDimension C.dimensionFunction sA a ≤ k := by
    intro a
    rw [← relativeDimension_of_iso C.dimensionFunction sA sB e hcomp a]
    simpa using relativeDimension_le_of_schemeDeltaDimension_le C sB (𝟙 B)
      (by simpa using hB) (e.hom.base a)
  simpa using schemeDeltaDimension_le_of_forall_point C sA (𝟙 A) (by simpa using hpt)

/-- A delta-dimension bound for a closed subscheme depends only on the ideal sheaf. -/
private theorem schemeDeltaDimension_le_congr_idealSheaf (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] {I J : X.IdealSheafData} (hIJ : I = J)
    (k : EInt) :
    schemeDeltaDimension C (I.subschemeι ≫ p) ≤ k ↔
      schemeDeltaDimension C (J.subschemeι ≫ p) ≤ k := by
  subst hIJ
  exact Iff.rfl

/-- Pushing an ideal sheaf forward along a closed immersion does not raise the
delta-dimension of its closed subscheme. -/
private theorem schemeDeltaDimension_map_closedImmersion_le (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (j : Y ⟶ X)
    [IsClosedImmersion j] (I : Y.IdealSheafData) (k : ℤ)
    (hI : schemeDeltaDimension C (I.subschemeι ≫ j ≫ p) ≤ (k : EInt)) :
    schemeDeltaDimension C ((I.map j).subschemeι ≫ p) ≤ (k : EInt) := by
  have hQ : (imageIsoOfIsClosedImmersion j I).hom ≫ ((I.map j).subschemeι ≫ p) =
      I.subschemeι ≫ j ≫ p := by
    rw [← Category.assoc, imageIsoOfIsClosedImmersion_hom_subschemeι, Category.assoc]
  refine schemeDeltaDimension_le_of_iso C ((I.map j).subschemeι ≫ p)
    (I.subschemeι ≫ j ≫ p) (imageIsoOfIsClosedImmersion j I).symm ?_ k hI
  rw [Iso.symm_hom, ← hQ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The delta-dimension of a product.** The product of a closed subscheme of delta-dimension
at most `d` with one that is flat of relative dimension `r` over the base has delta-dimension at
most `d + r`: the product is the inverse image of the first factor along a flat morphism of
relative dimension `r`, so the bound is the one for a flat inverse image. -/
theorem schemeDeltaDimension_product_le (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g]
    (I : X.IdealSheafData) (K : Y.IdealSheafData) [Flat (K.subschemeι ≫ g)] (r : ℕ)
    (hK : AlgebraicGeometry.RelativeDimension (K.subschemeι ≫ g) r)
    (d : ℤ) (hI : schemeDeltaDimension C (I.subschemeι ≫ f) ≤ (d : EInt)) :
    schemeDeltaDimension C
        ((I.comap (pullback.fst f g) ⊔ K.comap (pullback.snd f g)).subschemeι ≫
          pullback.fst f g ≫ f) ≤ ((d + (r : ℤ) : ℤ) : EInt) := by
  obtain ⟨_, _, hq⟩ := flat_relativeDimension_pullback_snd_subschemeι f g K r hK
  refine (schemeDeltaDimension_le_congr_idealSheaf C (pullback.fst f g ≫ f)
    (map_comap_pullback_snd_subschemeι f g K I)
    ((d + (r : ℤ) : ℤ) : EInt)).mp ?_
  refine schemeDeltaDimension_map_closedImmersion_le C (pullback.fst f g ≫ f)
    (pullback.fst (pullback.snd f g) K.subschemeι) _ _ ?_
  refine schemeDeltaDimension_le_of_iso C _
    (pullback.fst (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)
        I.subschemeι ≫
      (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g) ≫ f)
    (I.comapIso (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g)) ?_ _
    (schemeDeltaDimension_pullback_le C
      ((pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g) ≫ f) f
      (pullback.fst (pullback.snd f g) K.subschemeι ≫ pullback.fst f g) rfl r hq
      I.subschemeι d hI)
  rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  simp only [Category.assoc]

/-! ### Multiplicativity, peeling off the first factor -/

/-- The cycle coefficient of the inverse image of an ideal sheaf along an isomorphism over the
base is the cycle coefficient of that ideal sheaf at the image point. -/
private theorem closedSubschemeCycleCoeff_comap_iso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ≅ B)
    (hcomp : e.hom ≫ sB = sA) (I : B.IdealSheafData) (d : ℤ) (a : A) :
    closedSubschemeCycleCoeff C sA (I.comap e.hom).subschemeι d a =
      closedSubschemeCycleCoeff C sB I.subschemeι d (e.hom.base a) := by
  rw [closedSubschemeCycleCoeff_of_isIso_ambient C sA sB e.hom hcomp
    (I.comap e.hom).subschemeι d a]
  exact closedSubschemeCycleCoeff_eq_of_iso C sB ((I.comap e.hom).subschemeι ≫ e.hom)
    I.subschemeι (comapSubschemeIsoOfIsIso e.hom I)
    (comapSubschemeIsoOfIsIso_hom_subschemeι e.hom I) d (e.hom.base a)

/-- The multiplicity of a point in a product of two closed subschemes is symmetric in the two
factors, the two products being compared along the symmetry isomorphism of the fibre product. -/
private theorem closedSubschemeCycleCoeff_product_symm (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (I : X.IdealSheafData) (J : Y.IdealSheafData) (d : ℤ)
    (z : (pullback f g : Scheme.{u})) :
    closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).subschemeι d z =
      closedSubschemeCycleCoeff C (pullback.fst g f ≫ g)
        (J.comap (pullback.fst g f) ⊔ I.comap (pullback.snd g f)).subschemeι d
        ((pullbackSymmetry f g).hom.base z) := by
  have hbase : (pullbackSymmetry f g).hom ≫ (pullback.fst g f ≫ g) =
      pullback.fst f g ≫ f := by
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst, ← pullback.condition]
  have hi : (J.comap (pullback.fst g f) ⊔ I.comap (pullback.snd g f)).comap
      (pullbackSymmetry f g).hom =
      I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g) := by
    simp only [Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp,
      pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd, sup_comm]
  rw [← closedSubschemeCycleCoeff_congr_idealSheaf C (pullback.fst f g ≫ f) hi d z]
  exact closedSubschemeCycleCoeff_comap_iso C (pullback.fst f g ≫ f)
    (pullback.fst g f ≫ g) (pullbackSymmetry f g) hbase _ d z

/-- **Multiplicativity of the multiplicity in a product, peeling off the first factor.** The
mirror image of `Stacks.Chow.closedSubschemeCycleCoeff_product_right`, with the roles of the two
factors exchanged: now the first factor is required to be flat of relative dimension `r` over
the base and the second only to have delta-dimension at most `d`. -/
theorem closedSubschemeCycleCoeff_product_left (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) [Flat (I.subschemeι ≫ f)] (r : ℕ)
    (hI : AlgebraicGeometry.RelativeDimension (I.subschemeι ≫ f) r) (d : ℤ)
    (hJ : schemeDeltaDimension C (J.subschemeι ≫ g) ≤ (d : EInt))
    (z : (pullback f g : Scheme.{u})) (hz : (pullback.fst f g).base z ∈ I.support) :
    closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        (I.comap (pullback.fst f g) ⊔ J.comap (pullback.snd f g)).subschemeι
        ((r : ℤ) + d) z =
      closedSubschemeCycleCoeff C g J.subschemeι d ((pullback.snd f g).base z) *
        closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
          (I.comap (pullback.fst f g) ⊔ (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({(pullback.snd f g).base z} : Set Y))).comap
              (pullback.snd f g)).subschemeι ((r : ℤ) + d) z := by
  have hfst : (pullback.fst g f).base ((pullbackSymmetry f g).hom.base z) =
      (pullback.snd f g).base z :=
    congrArg (fun a : (pullback f g : Scheme.{u}) ⟶ Y ↦ a.base z)
      (pullbackSymmetry_hom_comp_fst f g)
  have hsnd : (pullback.snd g f).base ((pullbackSymmetry f g).hom.base z) =
      (pullback.fst f g).base z :=
    congrArg (fun a : (pullback f g : Scheme.{u}) ⟶ X ↦ a.base z)
      (pullbackSymmetry_hom_comp_snd f g)
  have H := closedSubschemeCycleCoeff_product_right C g f J I r hI d hJ
    ((pullbackSymmetry f g).hom.base z) (by simpa only [hsnd] using hz)
  rw [hfst] at H
  rw [closedSubschemeCycleCoeff_product_symm C f g I J,
    closedSubschemeCycleCoeff_product_symm C f g I
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(pullback.snd f g).base z} : Set Y)))]
  simpa only [add_comm] using H

/-! ### Relative dimension over a field -/

/-- Over the spectrum of a field the relative dimension of a point is non-negative: the base
dimension function vanishes, so the relative dimension is a transcendence degree. -/
public theorem relativeDimension_fieldChowSituation_nonneg (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S) (x : X) :
    0 ≤ relativeDimension (fieldChowSituation k).dimensionFunction p x := by
  unfold relativeDimension
  rw [fieldChowSituation_dimensionFunction_eq_zero, zero_add]
  exact Int.natCast_nonneg _

/-- An integral scheme locally of finite type over the spectrum of a field has constant fibre
dimension, equal to the relative dimension of its generic point: the base has a single point
whose residue field is the field itself, so the fibre is the scheme, and the dimension of an
irreducible scheme at any point is the transcendence degree of its function field. -/
@[ega "IV 5.2.1" "special case", ega "IV 5.6.5" "special case"]
public theorem relativeDimension_of_isIntegral_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ (fieldChowSituation k).S)
    [LocallyOfFiniteType p] :
    AlgebraicGeometry.RelativeDimension p
      (relativeDimension (fieldChowSituation k).dimensionFunction p (genericPoint X)).toNat := by
  set x := genericPoint X with hxdef
  let _ : ∀ s : (fieldChowSituation k).S,
      IsIso ((fieldChowSituation k).S.fromSpecResidueField s) :=
    isIso_fromSpecResidueField_of_field k
  have hdim : topologicalKrullDim (p.fiber (p.base x)) =
      ((relativeDimension (fieldChowSituation k).dimensionFunction p x).toNat :
        WithBot ℕ∞) := by
    let _ : IsIso (p.fiberι (p.base x)) := inferInstanceAs (IsIso (pullback.fst _ _))
    let _ : IsIntegral (p.fiber (p.base x)) := IsIntegral.of_isIso (inv (p.fiberι (p.base x)))
    have hx : p.asFiber x ∈ genericPoints (p.fiber (p.base x)) := by
      have hx' : x ∈ genericPoints X := by
        simp [hxdef, genericPoints, irreducibleComponents_eq_singleton]
      have H := (genericPointsIso (asIso (p.fiberι (p.base x))).symm ⟨x, hx'⟩).2
      have hpt : (inv (p.fiberι (p.base x))).base x = p.asFiber x := by
        apply (p.fiberι (p.base x)).isOpenEmbedding.injective
        simp only [Scheme.Hom.fiberι_asFiber, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        rfl
      change (inv (p.fiberι (p.base x))).base x ∈ genericPoints (p.fiber (p.base x)) at H
      simpa only [hpt] using H
    have hring := isField_stalk_of_closure_mem_irreducibleComponents
      (p.fiber (p.base x)) (p.asFiber x) hx
    let _ : LocallyOfFiniteType (p.fiberToSpecResidueField (p.base x)) := by
      change LocallyOfFiniteType
        (pullback.snd p ((fieldChowSituation k).S.fromSpecResidueField (p.base x)))
      infer_instance
    rw [AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      ((fieldChowSituation k).S.residueField (p.base x)) (p.fiber (p.base x))
      (p.fiberToSpecResidueField (p.base x)) (p.asFiber x)]
    rw [AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg,
      ringKrullDim_eq_zero_of_isField hring, zero_add]
    let _ := (p.residueFieldMap x).hom.toAlgebra
    let _ : Algebra.EssFiniteType ((fieldChowSituation k).S.residueField (p.base x))
        (X.residueField x) :=
      RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap p x)
    have ht : Algebra.trdeg ((fieldChowSituation k).S.residueField (p.base x))
        (X.residueField x) < Cardinal.aleph0 := trdeg_lt_aleph0 _ _
    have hrel : relativeDimension (fieldChowSituation k).dimensionFunction p x =
        (Cardinal.toNat (Algebra.trdeg
          ((fieldChowSituation k).S.residueField (p.base x)) (X.residueField x)) : ℤ) := by
      change (fieldChowSituation k).dimensionFunction (p.base x) + _ = _
      rw [fieldChowSituation_dimensionFunction, zero_add]
    rw [hrel, Int.toNat_natCast]
    exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
      (by rw [← Cardinal.toNat_toENat,
        ENat.natCast_toNat (Cardinal.toENat_lt_top.mpr ht).ne])
  intro s _
  have heq : s = p.base x := Subsingleton.elim _ _
  subst heq
  let _ : IsIso (p.fiberι (p.base x)) := inferInstanceAs (IsIso (pullback.fst _ _))
  let _ : IsIntegral (p.fiber (p.base x)) := IsIntegral.of_isIso (inv (p.fiberι (p.base x)))
  exact ⟨TopologicalSpace.Equidimensional.of_preirreducibleSpace _, hdim⟩

/-- Over the spectrum of a field the reduced closure of a point of relative dimension `d` is
flat of constant fibre dimension `d` over the base, and `d` is non-negative. -/
public theorem pointClosure_relativeDimension (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] (x : X) (d : ℤ)
    (hx : relativeDimension (fieldChowSituation k).dimensionFunction p x = d) :
    (d.toNat : ℤ) = d ∧
      AlgebraicGeometry.RelativeDimension
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ p) d.toNat := by
  refine ⟨Int.toNat_of_nonneg (hx ▸ relativeDimension_fieldChowSituation_nonneg k p x), ?_⟩
  have _ : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme := isIntegral_integralComponentAt x
  have H := relativeDimension_of_isIntegral_over_field k
    ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι ≫ p)
  have hgen : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι.base
        (genericPoint (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subscheme) = x :=
    genericPointOf_integralComponentAt x
  rwa [relativeDimension_comp_closedImmersion, hgen, hx] at H

/-- A point at which a cycle of delta-dimension `d` has a nonzero coefficient has relative
dimension `d`. -/
private theorem relativeDimension_of_cycle_ne_zero (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (d : ℤ) (a : CycleGroup C p d) (x : X)
    (hx : a.1 x ≠ 0) : relativeDimension C.dimensionFunction p x = d := by
  have he : (⟨closure ({x} : Set X), isIrreducible_singleton.closure,
      isClosed_closure⟩ : IrreducibleCloseds X).isIrreducible.genericPoint = x :=
    (IrreducibleCloseds.isIrreducible
      (⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds X)).isGenericPoint_genericPoint isClosed_closure |>.eq
      isGenericPoint_closure
  have hd := a.2 ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
    (by simpa only [he] using hx)
  simpa only [deltaDimension, he] using hd

/-! ### Associativity of the exterior product of cycles -/

/-- The exterior product multiplicity, written as the cycle coefficient of the product of the
two reduced point closures. -/
private theorem exteriorProductWeight_eq_closedSubschemeCycleCoeff (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (j : ℤ) (x : X) (y : Y) (z : (pullback f g : Scheme.{u})) :
    exteriorProductWeight C f g j x y z =
      closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).comap
            (pullback.fst f g) ⊔
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).comap
            (pullback.snd f g)).subschemeι j z :=
  rfl

/-- A point lies in the support of the vanishing ideal of its own reduced closure. -/
public alias mem_support_vanishingIdeal_closure_self :=
  AlgebraicGeometry.mem_support_vanishingIdeal_closure_singleton

/-- **Associativity of the exterior product of cycles.** Let `X`, `Y` and `Z` be schemes locally
of finite type over a field `k` and let `α`, `β`, `γ` be cycles on them of delta-dimensions `n`,
`m`, `l`. The two iterated exterior products `(α × β) × γ` and `α × (β × γ)` agree after
transport along the canonical associator `(X ×_k Y) ×_k Z ≅ X ×_k (Y ×_k Z)`.

The two sides live in cycle groups of delta-dimension `(n + m) + l` and `n + (m + l)`, equal
integers but not syntactically equal ones, so the identity is stated coefficientwise: at a point
`w` of `X ×_k (Y ×_k Z)` and its image under the inverse of the associator.

Both coefficients are the product of the three cycle coefficients at the three coordinates of
`w` with a product of two multiplicities, and each of those products of two multiplicities is the
multiplicity of the triple product of the three reduced point closures: the multiplicity is
multiplicative in a product of closed subschemes, one of whose factors is flat over the base,
and over a field every reduced point closure is flat of constant fibre dimension. The two triple
multiplicities then agree by `Stacks.Chow.tripleProductWeight_assoc`. -/
theorem exteriorProduct_assoc (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (h : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType h] (n m l : ℤ)
    (α : CycleGroup (fieldChowSituation k) f n)
    (β : CycleGroup (fieldChowSituation k) g m)
    (γ : CycleGroup (fieldChowSituation k) h l)
    (w : (pullback f (pullback.fst g h ≫ g) : Scheme.{u})) :
    (exteriorProduct (fieldChowSituation k) (pullback.fst f g ≫ f) h (n + m) l
          (exteriorProduct (fieldChowSituation k) f g n m α β) γ).1
        ((tripleProductAssoc f g h).inv.base w) =
      (exteriorProduct (fieldChowSituation k) f (pullback.fst g h ≫ g) n (m + l) α
        (exteriorProduct (fieldChowSituation k) g h m l β γ)).1 w := by
  rw [exteriorProduct_exteriorProduct_apply_tripleProductAssoc_inv,
    exteriorProduct_exteriorProduct_apply]
  by_cases hα : α.1 ((pullback.fst f (pullback.fst g h ≫ g)).base w) = 0
  · rw [hα]; ring
  by_cases hβ : β.1 ((pullback.fst g h).base
      ((pullback.snd f (pullback.fst g h ≫ g)).base w)) = 0
  · rw [hβ]; ring
  by_cases hγ : γ.1 ((pullback.snd g h).base
      ((pullback.snd f (pullback.fst g h ≫ g)).base w)) = 0
  · rw [hγ]; ring
  have hdα := relativeDimension_of_cycle_ne_zero (fieldChowSituation k) f n α _ hα
  have hdβ := relativeDimension_of_cycle_ne_zero (fieldChowSituation k) g m β _ hβ
  have hdγ := relativeDimension_of_cycle_ne_zero (fieldChowSituation k) h l γ _ hγ
  obtain ⟨hn, hIn⟩ := pointClosure_relativeDimension k f _ n hdα
  obtain ⟨hm, hJm⟩ := pointClosure_relativeDimension k g _ m hdβ
  obtain ⟨hl, hKl⟩ := pointClosure_relativeDimension k h _ l hdγ
  have hI : schemeDeltaDimension (fieldChowSituation k)
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        ({(pullback.fst f (pullback.fst g h ≫ g)).base w} : Set X))).subschemeι ≫ f) ≤
      (n : EInt) :=
    le_of_eq ((schemeDeltaDimension_integralComponentAt (fieldChowSituation k) f _).trans
      (congrArg WithBotTop.coe hdα))
  have hJ : schemeDeltaDimension (fieldChowSituation k)
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        ({(pullback.fst g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w)} :
          Set Y))).subschemeι ≫ g) ≤ (m : EInt) :=
    le_of_eq ((schemeDeltaDimension_integralComponentAt (fieldChowSituation k) g _).trans
      (congrArg WithBotTop.coe hdβ))
  have hXY := schemeDeltaDimension_product_le (fieldChowSituation k) f g _ _ m.toNat hJm n hI
  have hYZ := schemeDeltaDimension_product_le (fieldChowSituation k) g h _ _ l.toNat hKl m hJ
  rw [hm] at hXY
  rw [hl] at hYZ
  have Hleft := closedSubschemeCycleCoeff_product_right (fieldChowSituation k)
    (pullback.fst f g ≫ f) h _ _ l.toNat hKl (n + m) hXY
    ((tripleProductAssoc f g h).inv.base w)
    (by rw [snd_tripleProductAssoc_inv]; exact mem_support_vanishingIdeal_closure_self _)
  have Hright := closedSubschemeCycleCoeff_product_left (fieldChowSituation k) f
    (pullback.fst g h ≫ g) _ _ n.toNat hIn (m + l) hYZ w
    (mem_support_vanishingIdeal_closure_self _)
  rw [hl] at Hleft
  rw [hn] at Hright
  have Hfull := closedSubschemeCycleCoeff_tripleProductIdeal_assoc (fieldChowSituation k) f g h
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      ({(pullback.fst f (pullback.fst g h ≫ g)).base w} : Set X)))
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      ({(pullback.fst g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w)} : Set Y)))
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      ({(pullback.snd g h).base ((pullback.snd f (pullback.fst g h ≫ g)).base w)} : Set Z)))
    (n + m + l) w
  simp only [tripleProductIdealLeft, tripleProductIdealRight] at Hfull
  congr 1
  rw [exteriorProductWeight_eq_closedSubschemeCycleCoeff,
    exteriorProductWeight_eq_closedSubschemeCycleCoeff,
    exteriorProductWeight_eq_closedSubschemeCycleCoeff,
    exteriorProductWeight_eq_closedSubschemeCycleCoeff]
  rw [← Hleft, Hfull, ← Hright, add_assoc n m l]

/-! ### Stacks 02S1 as a single hypothesis -/

/-- The instances of Stacks 02S1 that make the exterior product on Chow groups well defined are
instances of Stacks 02S1 in the bundled form above: the projection of the product of a point
closure with the second factor is one of the flat morphisms over the base that it quantifies
over. -/
theorem flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_descends
    (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] (hfp : FlatPullbackDescends C)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (j : ℤ) :
    FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres C f g j :=
  flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_forall C f g j
    fun sX' hsX' v hv hvflat hbase r hr ↦ by
      have := hsX'
      have := hv
      have := hvflat
      exact hfp sX' g v hbase r hr j

/-! ### Associativity of the exterior product on Chow groups -/

/-- Transport along an equality of delta-dimensions, on the class of a cycle: two cycles with the
same coefficient at every point have the same class in either of two equal degrees. -/
private theorem chowGroupDegreeEquiv_mk_eq_mk (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {d e : ℤ} (hde : d = e)
    (a : CycleGroup C sX d) (b : CycleGroup C sX e) (hab : ∀ x : X, a.1 x = b.1 x) :
    chowGroupDegreeEquiv C sX hde (QuotientAddGroup.mk a) = QuotientAddGroup.mk b := by
  subst hde
  have hab' : a = b := Subtype.ext (DFunLike.ext _ _ hab)
  subst hab'
  rfl

/-- **Stacks 0FBZ.** The exterior product on Chow groups is associative. Let `k` be a field, let
`X`, `Y` and `Z` be schemes locally of finite type over `k` and let `a ∈ CH_n(X)`,
`b ∈ CH_m(Y)`, `c ∈ CH_l(Z)`. Then

  `(a × b) × c = a × (b × c)`

in `CH_{n + m + l}(X ×_k Y ×_k Z)`.

The two sides are formed on the two bracketings of the triple product and in the two bracketings
of the degree, so the left-hand side is carried into the group of the right-hand side by
pushforward along the associator `Stacks.Chow.tripleProductAssoc`, which is an isomorphism over
the base by `Stacks.Chow.tripleProductAssoc_hom_comp_base`, followed by
`Stacks.Chow.chowGroupDegreeEquiv` for the degrees `(n + m) + l` and `n + (m + l)`. Both of those
transports are the identity on cycle coefficients, so what is asserted is the source's identity.

On classes of cycles it is `Stacks.Chow.exteriorProduct_assoc`, the cycle-level identity, read
modulo rational equivalence. Nothing is assumed beyond the base being the spectrum of a field:
the exterior product on Chow groups, `Stacks.Chow.chowExteriorProduct`, is itself unconditional
over such a base, the instances of Stacks 02S1 that make it well defined being discharged inside
it by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds`. -/
@[stacks 0FBZ]
theorem chowExteriorProduct_assoc_unconditional (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (h : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType h] (n m l : ℤ)
    (a : chowGroup (fieldChowSituation k) f n)
    (b : chowGroup (fieldChowSituation k) g m)
    (c : chowGroup (fieldChowSituation k) h l) :
    chowGroupDegreeEquiv (fieldChowSituation k)
        (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (add_assoc n m l)
        (chowPushforwardOfIso (fieldChowSituation k)
          (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
          (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (tripleProductAssoc f g h).hom
          (tripleProductAssoc_hom_comp_base f g h) (n + m + l)
          (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
            (pullback.fst f g ≫ f) h (n + m) l
            (TensorProduct.tmul ℤ
              (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) f g n m
                (TensorProduct.tmul ℤ a b)) c))) =
      chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) f (pullback.fst g h ≫ g) n
        (m + l)
        (TensorProduct.tmul ℤ a
          (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) g h m l
            (TensorProduct.tmul ℤ b c))) := by
  induction a using QuotientAddGroup.induction_on with
  | H α =>
    induction b using QuotientAddGroup.induction_on with
    | H β =>
      induction c using QuotientAddGroup.induction_on with
      | H γ =>
        refine chowGroupDegreeEquiv_mk_eq_mk (fieldChowSituation k)
          (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (add_assoc n m l)
          (properPushforward (fieldChowSituation k)
            (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
            (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (tripleProductAssoc f g h).hom
            (tripleProductAssoc_hom_comp_base f g h) (n + m + l)
            (exteriorProduct (fieldChowSituation k) (pullback.fst f g ≫ f) h (n + m) l
              (exteriorProduct (fieldChowSituation k) f g n m α β) γ))
          (exteriorProduct (fieldChowSituation k) f (pullback.fst g h ≫ g) n (m + l) α
            (exteriorProduct (fieldChowSituation k) g h m l β γ)) fun w ↦ ?_
        have key := properPushforward_apply_of_isIso (fieldChowSituation k)
          (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
          (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (tripleProductAssoc f g h).hom
          (tripleProductAssoc_hom_comp_base f g h) (n + m + l)
          (exteriorProduct (fieldChowSituation k) (pullback.fst f g ≫ f) h (n + m) l
            (exteriorProduct (fieldChowSituation k) f g n m α β) γ)
          ((tripleProductAssoc f g h).inv.base w)
        rw [tripleProductAssoc_hom_base_inv_base] at key
        rw [key]
        exact exteriorProduct_assoc k f g h n m l α β γ w


/-- **Stacks 0FBZ.** The exterior product on Chow groups is associative. Let `k` be a field, let
`X`, `Y` and `Z` be schemes locally of finite type over `k` and let `a ∈ CH_n(X)`,
`b ∈ CH_m(Y)`, `c ∈ CH_l(Z)`. Then

  `(a × b) × c = a × (b × c)`

in `CH_{n + m + l}(X ×_k Y ×_k Z)`.

The two sides are formed on the two bracketings of the triple product and in the two bracketings
of the degree, so the left-hand side is carried into the group of the right-hand side by
pushforward along the associator `Stacks.Chow.tripleProductAssoc`, which is an isomorphism over
the base by `Stacks.Chow.tripleProductAssoc_hom_comp_base`, followed by
`Stacks.Chow.chowGroupDegreeEquiv` for the degrees `(n + m) + l` and `n + (m + l)`. Both of those
transports are the identity on cycle coefficients, so what is asserted is the source's identity.

On classes of cycles it is `Stacks.Chow.exteriorProduct_assoc`, the cycle-level identity, read
modulo rational equivalence. Nothing is assumed: it is
`Stacks.Chow.chowExteriorProduct_assoc_unconditional`. -/
@[stacks 0FBZ]
theorem chowExteriorProduct_assoc (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f]
    (g : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType g]
    (h : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType h] (n m l : ℤ)
    (a : chowGroup (fieldChowSituation k) f n)
    (b : chowGroup (fieldChowSituation k) g m)
    (c : chowGroup (fieldChowSituation k) h l) :
    chowGroupDegreeEquiv (fieldChowSituation k)
        (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (add_assoc n m l)
        (chowPushforwardOfIso (fieldChowSituation k)
          (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g ≫ f)
          (pullback.fst f (pullback.fst g h ≫ g) ≫ f) (tripleProductAssoc f g h).hom
          (tripleProductAssoc_hom_comp_base f g h) (n + m + l)
          (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl)
            (pullback.fst f g ≫ f) h (n + m) l
            (TensorProduct.tmul ℤ
              (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) f g n m
                (TensorProduct.tmul ℤ a b)) c))) =
      chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) f (pullback.fst g h ≫ g) n
        (m + l)
        (TensorProduct.tmul ℤ a
          (chowExteriorProduct (fieldChowSituation k) (fun _ _ ↦ rfl) g h m l
            (TensorProduct.tmul ℤ b c))) :=
    chowExteriorProduct_assoc_unconditional k f g h n m l a b c

end Stacks.Chow

end
