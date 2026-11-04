module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleRoundTrip
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChangeCompAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionAlgebraTransport
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeInG
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruples

/-!
# The restriction datum of the functor of quadruples, and its functoriality in the test object

In Situation 0849 let `X` be an algebraic space over a scheme `S` and let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra.  Stacks 084A writes down the *value* `F(T)` of the functor of quadruples on
a test object `T` of the big fppf site: the union over `d ≥ 1` of the quadruples
`(d, f : T → X, ℒ, ψ)`, modulo strict equivalence inside a degree and the equivalence of Tag 01NW
across degrees.  In this library that value is
`AlgebraicGeometry.Space.GradedAlgebraPoints.F`, built from the datum
`AlgebraicGeometry.Space.GradedAlgebraPoints`, which records for every `T`-point `f` of `X` the
restricted algebra `f^*𝒜` on the scheme of `T`.

The source calls `F` a functor `Sch^{opp} ⟶ Sets` without comment, but the datum as recorded
carries nothing that moves a quadruple along a morphism `τ : T' ⟶ T` of test objects: a quadruple
over `f` is built from `𝒜` at `f`, a quadruple over `yoneda.map τ ≫ f` from `𝒜` at
`yoneda.map τ ≫ f`, and the two are different sheaves of graded algebras on different schemes.
What relates them is a comparison

`r.algebra T' (yoneda.map τ ≫ f) ≅ (toScheme.map τ)^* (r.algebra T f)`,

which is exactly the pseudofunctoriality of the inverse image applied to `f^*𝒜`, and which the
bare datum does not carry.  This file supplies it, as the structure
`AlgebraicGeometry.Space.GradedAlgebraRestriction` over a given datum, together with the two
coherences such a comparison must satisfy to make `F` a presheaf — and then builds the
restriction map on `F`.

## Why a separate structure and not a field

The comparison is deliberately *not* added as a field of
`AlgebraicGeometry.Space.GradedAlgebraPoints`.  That datum is built in three places, and one of
them,
`AlgebraicGeometry.Space.GradedAlgebraPoints.ofQuasicoherentFamily`, takes an **arbitrary**
family of quasi-coherent graded algebras indexed by the scheme points of `X`, with no
compatibility between the members.  Such a family structurally cannot supply the comparison, so
adding the field would force `ofQuasicoherentFamily` to take the comparison family as a further
argument, which propagates to each of its twenty-four call sites in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesRepresentability` and
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesSections`.  Keeping the comparison in
its own structure leaves every existing construction untouched and lets a caller that *has* the
comparison — as Situation 0849 does, `f^*𝒜` being functorial in `f` — provide it.

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraRestriction` is the restriction datum over a datum of
  Stacks 084A: the comparison above, its degreewise invertibility, and the two coherences.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.restrict_id` is the identity coherence and
  `AlgebraicGeometry.Space.GradedAlgebraRestriction.restrict_comp` the cocycle condition.  These
  are the verification the source omits; neither holds definitionally, because neither
  `(𝟙 S)^*A = A` nor `(g')^*(g^*A) = (g' ∘ g)^*A` does.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleRestrict` moves a quadruple of
  Stacks 084A along a morphism of test objects: pull back along the scheme morphism, read the
  result over the identity of the new scheme, and transport along the comparison.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.fibreRestrict` and
  `AlgebraicGeometry.Space.GradedAlgebraRestriction.FRestrict` are the induced maps on the fibre
  of `F(T)` over a point and on `F(T)` itself.

## Implementation notes

`restrict` takes the restricted point `f'` and the identification `yoneda.map τ ≫ f = f'` as
separate arguments rather than using `yoneda.map τ ≫ f` directly.  This is the named-composite
idiom of `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseAlgebraCompHomOf`, and it is what
lets the two coherences be stated on the nose: at `τ = 𝟙 T` the point `yoneda.map (𝟙 T) ≫ f` is
only propositionally `f`, so without the named argument the identity coherence would need a
transport of a sheaf of graded algebras along an equality of morphisms.

The target of `restrict` is written with `(toScheme.map τ)^*` rather than with a named scheme
morphism, because `toScheme.map (𝟙 T) = 𝟙` and `toScheme.map (τ' ≫ τ) = toScheme.map τ' ≫
toScheme.map τ` are available as `CategoryTheory.Functor.map_id` and
`CategoryTheory.Functor.map_comp`, and `...RelativeProjQcohSheaf.baseAlgebraCongrHom` absorbs
each of them into the statement of the corresponding coherence.

`quadrupleRestrict` is a composite of three existing operations on quadruples, in this order:
`...RelativeProjQcohSheaf.Quadruple.pullback` along the scheme morphism, which lands over
`toScheme.map τ ≫ 𝟙`; `...RelativeProjQcohSheaf.Quadruple.congrBase` to read that over
`𝟙 ≫ toScheme.map τ`; `...RelativeProjQcohSheaf.Quadruple.baseChangeDown` to move the base
change into the algebra; and `...RelativeProjQcohSheaf.Quadruple.algebraTransport` along the
comparison.  Each step is known to respect strict equivalence and the equivalence of Tag 01NW, so
the composite descends to the quotient.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The restriction datum -/

/-- **The restriction datum of the functor of quadruples of Stacks 084A.**

Over a datum `r` of Stacks 084A, the comparison that makes the value `F(T)` functorial in the
test object: for every morphism `τ : T' ⟶ T` of test objects and every `T`-point `f` of `X`, an
identification of the algebra of `r` at the restricted point with the inverse image along the
scheme morphism of `τ` of the algebra of `r` at `f`, degreewise invertible, subject to the
identity coherence and the cocycle condition.

In Situation 0849 the datum is the restriction `f ↦ f^*𝒜` of a single quasi-coherent graded
`𝒪_X`-algebra, and the comparison is the pseudofunctoriality of the inverse image:
`(f ∘ τ)^*𝒜 ≅ τ^*(f^*𝒜)`.  The source treats `F` as a functor without verifying the two
coherences; they are what this structure records.

**Nothing in this library constructs one of these.**  It is an interface — a datum together with
the coherences such a datum must satisfy — and as such it asserts nothing whatever about any
particular `𝒜`: every result below is conditional on being handed one.  In particular it is *not*
a proof that the functor of Stacks 084A is functorial in the test object, and a reader should not
read it as one.  Situation 0849's own datum ought to carry such a comparison, the inverse image
being pseudofunctorial, but that construction is not performed here;
`AlgebraicGeometry.Space.GradedAlgebraPoints.laurentUnit` cannot supply one either, there being
no base-change comparison for the Laurent algebra in this library. -/
structure GradedAlgebraRestriction (r : GradedAlgebraPoints B S hS X) where
  /-- The comparison of the algebra at a restricted point with the inverse image of the algebra
  at the original point. -/
  restrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X)
      (f' : yoneda.obj T' ⟶ X) (hf : yoneda.map τ ≫ f = f') :
    SheafOfModules.GradedAlgebra.UnitalHom (r.algebra T' f')
      (baseAlgebra ((BigFppfOver.toScheme B S hS).map τ) (r.algebra T f))
  /-- The comparison is an isomorphism in every degree. -/
  isIso_restrict_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X)
      (f' : yoneda.obj T' ⟶ X) (hf : yoneda.map τ ≫ f = f') (n : ℤ) :
    IsIso ((restrict τ f f' hf).app n)
  /-- **The identity coherence.** Restricting along the identity of a test object is the
  canonical identification of the inverse image along the identity with the identity.  This does
  not hold definitionally: `(𝟙 S)^*A` is not `A`. -/
  restrict_id (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (restrict (𝟙 T) f f (by simp)).comp
        ((baseAlgebraCongrHom (r.algebra T f)
            ((BigFppfOver.toScheme B S hS).map_id T)).comp
          (Stacks.Conormal.gradedPullbackId (r.algebra T f))) =
      SheafOfModules.GradedAlgebra.UnitalHom.id (r.algebra T f)
  /-- **The cocycle condition.** Restricting along a composite is restricting along the two
  factors in turn, compared with the composition law of the inverse image.  This does not hold
  definitionally: `(g')^*(g^*A)` is not `(g' ∘ g)^*A`. -/
  restrict_comp {T T' T'' : BigFppfOver B S hS} (τ : T' ⟶ T) (τ' : T'' ⟶ T')
      (f : yoneda.obj T ⟶ X) (f' : yoneda.obj T' ⟶ X) (f'' : yoneda.obj T'' ⟶ X)
      (hf : yoneda.map τ ≫ f = f') (hf' : yoneda.map τ' ≫ f' = f'')
      (hf'' : yoneda.map (τ' ≫ τ) ≫ f = f'') :
    restrict (τ' ≫ τ) f f'' hf'' =
      (restrict τ' f' f'' hf').comp
        ((baseAlgebraMapHom ((BigFppfOver.toScheme B S hS).map τ') (restrict τ f f' hf)).comp
          (baseAlgebraCompHomOf (r.algebra T f)
            ((BigFppfOver.toScheme B S hS).map τ')
            ((BigFppfOver.toScheme B S hS).map τ)
            ((BigFppfOver.toScheme B S hS).map (τ' ≫ τ))
            ((BigFppfOver.toScheme B S hS).map_comp τ' τ).symm))

namespace GradedAlgebraRestriction

variable {r : GradedAlgebraPoints B S hS X} (ρ : GradedAlgebraRestriction r)

attribute [instance] GradedAlgebraRestriction.isIso_restrict_app

/-! ### The restriction of a quadruple -/

/-- Reading a quadruple over an equal base morphism respects strict equivalence: the transport is
`Eq.mpr`, so substituting the equality removes it. -/
private theorem strictlyEquivalent_congrBase {T₀ S₀ : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S₀.toRingedSpace)} {d : ℤ}
    {g g' : T₀ ⟶ S₀} (h : g = g') {P Q : Quadruple g A d}
    (hPQ : Quadruple.StrictlyEquivalent P Q) :
    Quadruple.StrictlyEquivalent (Quadruple.congrBase h P) (Quadruple.congrBase h Q) := by
  subst h
  exact hPQ

/-- Reading a quadruple over an equal base morphism respects the equivalence of Tag 01NW, for the
same reason as `strictlyEquivalent_congrBase`. -/
private theorem equivalent_congrBase {T₀ S₀ : Scheme.{u}}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S₀.toRingedSpace)} {d d' : ℤ}
    {g g' : T₀ ⟶ S₀} (h : g = g') {P : Quadruple g A d} {Q : Quadruple g A d'}
    (hPQ : Quadruple.Equivalent P Q) :
    Quadruple.Equivalent (Quadruple.congrBase h P) (Quadruple.congrBase h Q) := by
  subst h
  exact hPQ

/-- **The identity of the new scheme, followed by the scheme morphism, is the scheme morphism
followed by the identity of the old one.** The reassociation that lets a quadruple pulled back
along `toScheme.map τ` be read as one over the identity of the new scheme. -/
theorem comp_id_eq_id_comp {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) :
    (BigFppfOver.toScheme B S hS).map τ ≫ 𝟙 ((BigFppfOver.toScheme B S hS).obj T) =
      𝟙 ((BigFppfOver.toScheme B S hS).obj T') ≫ (BigFppfOver.toScheme B S hS).map τ := by
  rw [Category.comp_id, Category.id_comp]

/-- **The restriction of a quadruple of Stacks 084A along a morphism of test objects.**

Pull the quadruple back along the scheme morphism of `τ`, read the result over the identity of
the new scheme, move the base change into the algebra, and transport along the comparison of the
restriction datum.  This is the operation the source's `F` needs in order to be a functor on the
big fppf site, and which the datum of Stacks 084A alone does not provide. -/
def quadrupleRestrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X)
    (f' : yoneda.obj T' ⟶ X) (hf : yoneda.map τ ≫ f = f') {d : ℤ}
    (P : r.Quadruples T f d) : r.Quadruples T' f' d :=
  Quadruple.algebraTransport (ρ.restrict τ f f' hf) (ρ.isIso_restrict_app τ f f' hf)
    ((Quadruple.congrBase (comp_id_eq_id_comp τ)
      (P.pullback ((BigFppfOver.toScheme B S hS).map τ))).baseChangeDown
        ((BigFppfOver.toScheme B S hS).map τ)
        (𝟙 ((BigFppfOver.toScheme B S hS).obj T')) (r.algebra T f) d)

/-- **Restriction carries strictly equivalent quadruples to strictly equivalent quadruples.**
Each of the four steps does: the pullback by
`...RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent.pullback`, the transport over an equal
base morphism by `subst`, the base change by
`...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_baseChangeDown`, and the algebra transport
by `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_algebraTransport_iff`. -/
theorem strictlyEquivalent_quadrupleRestrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X) (f' : yoneda.obj T' ⟶ X) (hf : yoneda.map τ ≫ f = f') {d : ℤ}
    {P Q : r.Quadruples T f d} (h : Quadruple.StrictlyEquivalent P Q) :
    Quadruple.StrictlyEquivalent (ρ.quadrupleRestrict τ f f' hf P)
      (ρ.quadrupleRestrict τ f f' hf Q) := by
  refine (Quadruple.strictlyEquivalent_algebraTransport_iff _ _).mpr ?_
  refine Quadruple.strictlyEquivalent_baseChangeDown _ _ _ _ ?_
  exact strictlyEquivalent_congrBase _ (Quadruple.StrictlyEquivalent.pullback h _)

/-- **Restriction carries equivalent quadruples to equivalent quadruples**, by the same four
steps as `strictlyEquivalent_quadrupleRestrict`, with the equivalence of Tag 01NW in place of
strict equivalence in each. -/
theorem equivalent_quadrupleRestrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X) (f' : yoneda.obj T' ⟶ X) (hf : yoneda.map τ ≫ f = f') {d d' : ℤ}
    {P : r.Quadruples T f d} {Q : r.Quadruples T f d'} (h : Quadruple.Equivalent P Q) :
    Quadruple.Equivalent (ρ.quadrupleRestrict τ f f' hf P)
      (ρ.quadrupleRestrict τ f f' hf Q) := by
  refine Quadruple.Equivalent.algebraTransport _ _ ?_
  refine Quadruple.Equivalent.baseChangeDown _ _ _ ?_
  exact equivalent_congrBase _ (Quadruple.Equivalent.pullback h _)

/-! ### The restriction map on the functor of quadruples -/

/-- **The restriction map on the fibre of `F(T)` over a `T`-point of `X`.**

The restriction of quadruples respects both identifications of Stacks 084A, so it descends to
the quotient: the fibre of `F(T)` over `f` maps to the fibre of `F(T')` over the restricted
point. -/
def fibreRestrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X)
    (f' : yoneda.obj T' ⟶ X) (hf : yoneda.map τ ≫ f = f')
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T))
      (A := r.algebra T f))) :
    Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj T'))
      (A := r.algebra T' f')) :=
  Quot.lift
    (fun P : PositiveQuadruple (𝟙 ((BigFppfOver.toScheme B S hS).obj T)) (r.algebra T f) =>
      Quot.mk _ ⟨P.1, ρ.quadrupleRestrict τ f f' hf P.2⟩)
    (fun _ _ hrel => by
      cases hrel with
      | strict hs =>
        exact Quot.sound (UnionRel.strict (ρ.strictlyEquivalent_quadrupleRestrict τ f f' hf hs))
      | equivalent he =>
        exact Quot.sound
          (UnionRel.equivalent (ρ.equivalent_quadrupleRestrict τ f f' hf he)))
    q

/-- **The restriction map on the value of the functor of quadruples of Stacks 084A.**

A point of `F(T)` is a `T`-point `f` of `X` together with a class of quadruples over it; its
restriction along `τ : T' ⟶ T` lies over the restricted point `yoneda.map τ ≫ f`, and is the
class of the restricted quadruples.  This is the functoriality in the test object that the
datum of Stacks 084A alone does not carry. -/
def FRestrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (ξ : r.F T) : r.F T' :=
  ⟨yoneda.map τ ≫ GradedAlgebraPoints.F.point r ξ,
    ρ.fibreRestrict τ (GradedAlgebraPoints.F.point r ξ)
      (yoneda.map τ ≫ GradedAlgebraPoints.F.point r ξ) rfl ξ.2⟩

/-- The point of `X` under a restricted point of `F` is the restriction of the point. -/
theorem point_FRestrict {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (ξ : r.F T) :
    GradedAlgebraPoints.F.point r (ρ.FRestrict τ ξ) =
      yoneda.map τ ≫ GradedAlgebraPoints.F.point r ξ :=
  rfl

/-- The restriction of the class of a quadruple of positive degree is the class of the restricted
quadruple. -/
theorem FRestrict_mk {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X)
    {d : ℤ} (hd : 0 < d) (P : r.Quadruples T f d) :
    ρ.FRestrict τ (GradedAlgebraPoints.F.mk r f hd P) =
      GradedAlgebraPoints.F.mk r (yoneda.map τ ≫ f) hd
        (ρ.quadrupleRestrict τ f (yoneda.map τ ≫ f) rfl P) :=
  rfl

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
