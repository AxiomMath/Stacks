module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleDescentFork
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct

/-!
# The descent fork of the adjunction unit on small étale topoi (towards Stacks 0DFX)

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let `F` be a sheaf on
`X_étale`. For a morphism `p : P ⟶ Y` and a morphism `g : P ⟶ X` with `p ≫ f = g`, applying
`f_*` to the adjunction unit of `p` and then the composition comparisons of Stacks 03G2,
part (3), gives the canonical restriction map
`f_* f⁻¹ F ⟶ g_* g⁻¹ F`,
here `AlgebraicGeometry.Space.descentMapOver`. Taking `P = Y ×_X Y` with its two projections
and `g` its structure morphism to `X`, the two restriction maps so obtained have equal
composites with the unit of `f`: this is the commutativity of the fork

`F ⟶ f_* f⁻¹ F ⇉ g_* g⁻¹ F`

whose limit property is the second assertion of **Stacks 0DFX**.

**Stacks 0DFX itself is not proved here.** Its first assertion — that `F ⟶ f_* f⁻¹ F` is a
monomorphism when `f` is surjective — is proved in Stacks by comparing stalks at geometric
points (Properties of Spaces, Stacks 04K2 and 04K5), and the stalk of a small étale sheaf of
an algebraic space at a geometric point is not available in this repository. Its second
assertion — that the fork below is a limit when `f` is in addition proper — is proved in
Stacks by reduction to a scheme (Cohomology of Spaces, Stacks 089J), a ph covering
(Topologies, Stacks 0DES) and Étale Cohomology, Stacks 0DDW; equivalently it follows from
effective descent for small étale sheaves along a surjective proper morphism (Stacks 0GFW),
which this repository also does not have. What this file supplies is the fork itself.

## Main definitions

* `AlgebraicGeometry.Space.descentMapOver`: the restriction map
  `AlgebraicGeometry.Space.smallToposDescentMap` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleDescentFork`, with its target
  indexed by a morphism
  `g : P ⟶ X` presented together with an identification `p ≫ f = g`.

## Main results

* `AlgebraicGeometry.Space.unit_comp_descentMap`: the unit of `f` followed by the restriction
  map along `p` is the unit of `p ≫ f`. This is the only substantive step; everything else is
  a specialization of it.
* `AlgebraicGeometry.Space.unit_equalizes_over`: two morphisms `P ⟶ Y` lying over one and the
  same `g : P ⟶ X` give restriction maps with equal composites with the unit of `f`.
* `AlgebraicGeometry.Space.unit_equalizes`: the fork of Stacks 0DFX commutes, i.e. the two
  projections of `Y ×_X Y` give the same composite.

## Implementation notes

The target of a restriction map must be indexed by a *single* morphism `g : P ⟶ X` carrying an
identification `p ≫ f = g`, rather than by `p ≫ f` itself. For the two projections `p₁, p₂` of
`Y ×_X Y` the composites `p₁ ≫ f` and `p₂ ≫ f` are equal only propositionally — `rfl` fails on
them — so `f_* f⁻¹ F ⟶ (p₁ ≫ f)_* (p₁ ≫ f)⁻¹ F` and `f_* f⁻¹ F ⟶ (p₂ ≫ f)_* (p₂ ≫ f)⁻¹ F` are
*different* types and no equation between their elements can even be stated. Indexing by the
structure morphism `g` of `Y ×_X Y`, which is what Stacks 0DFX itself does, removes the
problem; `descentMapOver` transports along the identification with an `eqToHom`, exactly as
`AlgebraicGeometry.Space.smallToposPushforwardBaseChange` does for the base-change comparison.

`unit_comp_descentMap` is proved from the mate coherence
`AlgebraicGeometry.Space.smallToposMorphism_comp_mate` evaluated at the inverse of the
inverse-image comparison: the mate equation then reads exactly as the claim, once the two
transposes are expanded by `CategoryTheory.Adjunction.homEquiv_unit` and the unit of the
composite adjunction by `CategoryTheory.Adjunction.comp_unit_app`. Those three facts are
supplied as applications rather than as rewrites, and the final reassociation is supplied as a
term, because the two spellings `(f_* ∘ p_*)` and `(f ∘ p)_*` of the composite direct image
are interchangeable only at default transparency.

## References

* [Stacks Project, Tag 0DFX](https://stacks.math.columbia.edu/tag/0DFX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The restriction map of `AlgebraicGeometry.Space.descentMap` with its target indexed by a
morphism `g : P ⟶ X` presented together with an identification `p ≫ f = g`. This is the form
in which the two projections of a fibre product can be compared, their composites with `f`
being equal only propositionally. -/
noncomputable def descentMapOver {P Y X : AlgebraicSpaces B S hS}
    (p : P ⟶ Y) (f : Y ⟶ X) (g : P ⟶ X) (h : p ≫ f = g)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (smallToposMorphism B S hS f).pushforward.obj
        ((smallToposMorphism B S hS f).inverseImage.obj F) ⟶
      (smallToposMorphism B S hS g).pushforward.obj
        ((smallToposMorphism B S hS g).inverseImage.obj F) :=
  smallToposDescentMap B S hS p f F ≫
    eqToHom (congrArg (fun q : P ⟶ X =>
      (smallToposMorphism B S hS q).pushforward.obj
        ((smallToposMorphism B S hS q).inverseImage.obj F)) h)

/-- The adjunction unit of `f` followed by the restriction map along `p` over `g` is the
adjunction unit of `g`. -/
theorem unit_comp_descentMapOver {P Y X : AlgebraicSpaces B S hS}
    (p : P ⟶ Y) (f : Y ⟶ X) (g : P ⟶ X) (h : p ≫ f = g)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (smallToposMorphism B S hS f).adj.unit.app F ≫
        descentMapOver B S hS p f g h F =
      (smallToposMorphism B S hS g).adj.unit.app F := by
  subst h
  rw [descentMapOver, eqToHom_refl, Category.comp_id]
  exact AlgebraicGeometry.Space.unit_comp_smallToposDescentMap B S hS p f F

/-- Two morphisms `P ⟶ Y` lying over one and the same morphism `g : P ⟶ X` give restriction
maps whose composites with the adjunction unit of `f` agree: both are the adjunction unit of
`g`. No hypothesis on `f` is needed. -/
theorem unit_equalizes_over {P Y X : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (p₁ p₂ : P ⟶ Y) (g : P ⟶ X)
    (h₁ : p₁ ≫ f = g) (h₂ : p₂ ≫ f = g)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (smallToposMorphism B S hS f).adj.unit.app F ≫
        descentMapOver B S hS p₁ f g h₁ F =
      (smallToposMorphism B S hS f).adj.unit.app F ≫
        descentMapOver B S hS p₂ f g h₂ F := by
  rw [unit_comp_descentMapOver, unit_comp_descentMapOver]

/-- **Stacks 0DFX.** The fork of Stacks 0DFX commutes: the adjunction unit
`F ⟶ f_* f⁻¹ F` has equal composites with the two restriction maps `f_* f⁻¹ F ⟶ g_* g⁻¹ F`
coming from the two projections of `Y ×_X Y`, where `g` is its structure morphism to `X`.
Neither surjectivity nor properness of `f` is needed for this. -/
@[stacks 0DFX "the unit equalizes the two restrictions"]
theorem unit_equalizes {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    let P := AlgebraicSpaces.fiberProduct B S hS f f
    let p₁ : P ⟶ Y := ObjectProperty.homMk (pullback.fst f.hom f.hom)
    let p₂ : P ⟶ Y := ObjectProperty.homMk (pullback.snd f.hom f.hom)
    let g : P ⟶ X := p₁ ≫ f
    (smallToposMorphism B S hS f).adj.unit.app F ≫
        descentMapOver B S hS p₁ f g rfl F =
      (smallToposMorphism B S hS f).adj.unit.app F ≫
        descentMapOver B S hS p₂ f g
          (AlgebraicSpaces.isPullback_fiberProduct B S hS f f).w.symm F :=
  unit_equalizes_over B S hS f _ _ _ rfl _ F

end AlgebraicGeometry.Space

end
