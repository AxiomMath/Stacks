module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace

/-!
# Relative projective space base-changes

`AlgebraicGeometry.projectiveSpaceOver n S` is the base change of the integral model
`AlgebraicGeometry.projectiveSpaceAtUniverse n` along `S ⟶ Spec ℤ`, i.e. the product of `S` with
that model over the terminal scheme. This file records that it is therefore functorial in the
base and that **the resulting square is cartesian**: for any `t : T ⟶ S`,

```
ℙⁿ_T ⟶ ℙⁿ_S
 |        |
 ↓        ↓
 T  ⟶    S
```

is a fibre product. No hypothesis on `t` is needed: the statement is the associativity of a
double fibre product, since the cospan `T ⟶ Spec ℤ ⟵ ℙⁿ_ℤ` factors through `S`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.map`: the morphism `ℙⁿ_T ⟶ ℙⁿ_S` induced by
  a morphism of bases.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.map_fst`: it is a morphism over the given
  morphism of bases.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.map_id` and
  `Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.map_comp`: functoriality.
* `Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange.isPullback_map`: **the square is
  cartesian**, so `ℙⁿ_T` is the inverse image of `ℙⁿ_S` over `T`.

## Implementation notes

Both `AlgebraicGeometry.projectiveSpaceOver` and the morphism built here are plain
`CategoryTheory.Limits.pullback` data, so every proof is `pullback.hom_ext` together with the two
defining equations of the lift, and the uniqueness of a morphism to the terminal object discharges
every commutativity obligation of a lift into a product over the terminal object.

The cartesian square is obtained from `CategoryTheory.IsPullback.of_bot`: the vertical paste of
the square below with the product square of `S` is the product square of `T`, because
`t ≫ terminal.from S = terminal.from T`.

`Stacks.Tag0B3I.baseTransport` is the special case of an isomorphism of bases, proved there
directly; it is not reused here because its statement carries the isomorphism rather than a bare
morphism.

Nothing here is said about the twisting sheaves of `ℙⁿ_S` or about their pullbacks along `map`.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange

universe u

variable (n : ℕ)

/-- **The base change of relative projective space along a morphism of bases.** -/
public def map {T S : Scheme.{u}} (t : T ⟶ S) :
    projectiveSpaceOver n T ⟶ projectiveSpaceOver n S :=
  pullback.lift (pullback.fst _ _ ≫ t) (pullback.snd _ _) (terminal.hom_ext _ _)

variable {T S : Scheme.{u}}

/-- The base change is a morphism over the given morphism of bases. -/
@[reassoc (attr := simp)]
public theorem map_fst (t : T ⟶ S) :
    map n t ≫ pullback.fst _ _ = pullback.fst _ _ ≫ t :=
  pullback.lift_fst _ _ _

/-- The base change commutes with the projections to the integral model. -/
@[reassoc (attr := simp)]
public theorem map_snd (t : T ⟶ S) :
    map n t ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- Functoriality: the base change along the identity is the identity. -/
@[simp]
public theorem map_id : map n (𝟙 S) = 𝟙 (projectiveSpaceOver n S) := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- Functoriality: the base change of a composite is the composite of the base changes. -/
@[reassoc]
public theorem map_comp {R : Scheme.{u}} (t : R ⟶ T) (t' : T ⟶ S) :
    map n (t ≫ t') = map n t ≫ map n t' := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- Two successive base changes, with the composite of the two morphisms of bases given as a
separate morphism.

Stated with all three morphisms of bases as variables so that it can be applied where the
composite is a morphism whose proof argument makes the goal ill-typed at `implicit`
transparency — which is what `AlgebraicGeometry.Scheme.homOfLE` applied to an inclusion of the
objects of `AlgebraicGeometry.Scheme.AffineZariskiSite` does, that being a `def` for a
subtype. -/
public theorem comp_map_comp_map {Z A B C : Scheme.{u}} (f : Z ⟶ projectiveSpaceOver n A)
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (hab : a ≫ b = c) :
    (f ≫ map n a) ≫ map n b = f ≫ map n c := by
  rw [Category.assoc, ← map_comp, hab]

/-- A base change followed by the projection to the base, with the morphism of bases as a
variable. -/
public theorem comp_map_comp_fst {Z A B : Scheme.{u}} (f : Z ⟶ projectiveSpaceOver n A)
    (t : A ⟶ B) :
    (f ≫ map n t) ≫ pullback.fst (terminal.from B)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      (f ≫ pullback.fst _ _) ≫ t := by
  rw [Category.assoc, map_fst, Category.assoc]

/-- A base change followed by the projection to the integral model, with the morphism of bases as
a variable. -/
public theorem comp_map_comp_snd {Z A B : Scheme.{u}} (f : Z ⟶ projectiveSpaceOver n A)
    (t : A ⟶ B) :
    (f ≫ map n t) ≫ pullback.snd (terminal.from B)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      f ≫ pullback.snd _ _ := by
  rw [Category.assoc, map_snd]

/-- **Relative projective space over `T` is the inverse image of relative projective space over
`S`.** For any morphism of bases the base-change square is cartesian. -/
public theorem isPullback_map (t : T ⟶ S) :
    IsPullback (pullback.fst (terminal.from T) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
      (map n t) t
      (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))) := by
  refine IsPullback.of_bot ?_ (map_fst n t).symm (IsPullback.of_hasPullback _ _)
  have h₁ : map n t ≫ pullback.snd (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      pullback.snd (terminal.from T) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
    map_snd n t
  have h₂ : t ≫ terminal.from S = terminal.from T := terminal.hom_ext _ _
  rw [h₁, h₂]
  exact IsPullback.of_hasPullback _ _

end Stacks.AlgebraicGeometry.ProjectiveSpaceBaseChange

end
