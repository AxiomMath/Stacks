module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidStructure

/-!
# The finite part of a groupoid in algebraic spaces

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over `B` whose source morphism is
separated and locally of finite type. This file collects, in one statement, everything the
construction of the finite part `(U', Z_univ, s', t', c', e', i')` in Stacks 04RT produces: the
object space `U' = (R_s/U, e)_fin` with its étale morphism `g : U' ⟶ U`, the universal open and
closed subspace `Z_univ` containing the base change of the unit, the rules defining the five
structure morphisms, and the canonical morphism of groupoids to `(U, R, s, t, c, e, i)`.

## Main results

* `Deformation.PointwiseGroupoid.inverseArrow_eq`: the inverse of an arrow of a septuple does not
  depend on the groupoid structure witnessing it.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.finitePartGroupoid_spec`: **Stacks 04RT**.

## Implementation notes

A groupoid in algebraic spaces does not carry its unit and inverse as data, so the rules for `e'`
and `i'` are stated as equalities between the unit and the inverse of
`finitePartGroupoid hsep hft` and the morphisms built by those rules; they follow because units
and inverses in a groupoid are unique.

## References

* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace Deformation.PointwiseGroupoid

variable {U R : Type w} {source target : R → U}
  {comp : { p : R × R // source p.1 = target p.2 } → R}

/-- The inverse of an arrow of a septuple does not depend on which groupoid structure witnesses
it: `i(a) = (P'.i(a) ∘ a) ∘ i(a) = e(s(a)) ∘ i(a)`, and a two-sided inverse is unique. -/
theorem inverseArrow_eq (P P' : PointwiseGroupoid source target comp) (a : R) :
    P.inverseArrow a = P'.inverseArrow a := by
  have hab : source (P'.inverseArrow a) = target a := P'.source_inverseArrow a
  have h₁ : source (comp ⟨(P'.inverseArrow a, a), hab⟩) = target (P.inverseArrow a) :=
    (P'.source_comp _ a hab).trans (P.target_inverseArrow a).symm
  have h₂ : source (P.identityArrow (source a)) = target (P.inverseArrow a) :=
    (P.source_identityArrow _).trans (P.target_inverseArrow a).symm
  have hid : comp ⟨(P'.inverseArrow a, a), hab⟩ = P.identityArrow (source a) :=
    (P'.comp_inverseArrow_fst a hab).trans (identityArrow_eq P' P (source a))
  calc P.inverseArrow a
      = comp ⟨(P.identityArrow (source a), P.inverseArrow a), h₂⟩ :=
        (P.comp_identityArrow_fst _ _ (P.target_inverseArrow a) h₂).symm
    _ = comp ⟨(comp ⟨(P'.inverseArrow a, a), hab⟩, P.inverseArrow a), h₁⟩ :=
        P.comp_congr hid.symm rfl h₂ h₁
    _ = P'.inverseArrow a := P.comp_comp_inverseArrow' _ a hab h₁

end Deformation.PointwiseGroupoid

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_GroupoidSpec
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_GroupoidSpec
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  hasPullbacks_presheaf_GroupoidSpec.has_limit _

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

/-- **Stacks 04RT, the finite part of a groupoid.** Let `(U, R, s, t, c, e, i)` be a groupoid in
algebraic spaces over `B` whose source morphism `s` is separated and locally of finite type. The
construction of Stacks 04RT produces the following, all of which are recorded here for the finite
part `fp = finitePart G hsep hft`, its groupoid `finitePartGroupoid hsep hft` and the canonical
morphism `finitePartGroupoidHom hsep hft`.

* The object space `U'` is `(R_s/U, e)_fin`: the inclusion of `U'` into `(R_s/U)_fin` is an open
  immersion whose range is the subfunctor of pairs containing the unit.
* The morphism `g : U' ⟶ U` is the projection of `(R_s/U)_fin` restricted to `U'`, and is étale.
* `Z_univ` is the universal open subspace of the fibre product of `g` and `s`, finite over `U'`,
  namely the pair which the inclusion of `U'` names under Stacks 04PE; it is closed as well as
  open, and the base change of the unit factors through it.
* The groupoid has object space `U'` and arrow space `Z_univ`, with
  - `s' : (u, Z, z) ↦ (u, Z)`, the first projection;
  - `t' : (u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z))`: the pair that `t'` names is the translate of the
    tautological pair by the tautological arrow, and its base morphism is `t ∘ z`;
  - `e' : (u, Z) ↦ (u, Z, e ∘ u)`, the unit of the groupoid;
  - `i' : (u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z), i ∘ z)`, the inverse of the groupoid;
  - `c' : ((u₁, Z₁, z₁), (u₂, Z₂, z₂)) ↦ (u₂, Z₂, z₁ ∘ z₂)`, the composition of the groupoid.
* The canonical morphism of groupoids over `B` to `(U, R, s, t, c, e, i)` is `g` on objects and
  `(u, Z, z) ↦ z` on arrows.

The hypotheses are on `s` alone; the source also assumes `t` separated and locally of finite type,
which the construction does not use. As in the rest of the formalization, the ambient fibre
product of `Z_univ` is `U' ×_{g, U, s} R` rather than `R ×_{s, U, g} U'`. -/
@[stacks 04RT "the finite part (U', Z_univ, s', t', c', e', i') of the groupoid, with the rules \
  for its structure morphisms and its morphism of groupoids to (U, R, s, t, c, e, i)"]
theorem finitePartGroupoid_spec (hsep : Space.IsSeparated C S hS G.source.hom)
    (hft : Space.IsLocallyOfFiniteType C S hS G.source.hom) :
    -- `U' = (R_s/U, e)_fin`, an open subspace of `(R_s/U)_fin`
    Subfunctor.range (finitePart G hsep hft).inclusion =
        (Space.finitePartWithSection C S hS G.source (identityHom G)
          (identityHom_comp_source G)).toSubfunctor ∧
      Space.IsOpenImmersion C S hS (finitePart G hsep hft).inclusion ∧
      -- `g : U' ⟶ U` is the projection of the finite part, and is étale
      (finitePart G hsep hft).pair.toBase.hom =
        (finitePart G hsep hft).inclusion ≫
          (Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap ∧
      Space.IsEtale C S hS (finitePart G hsep hft).pair.toBase.hom ∧
      -- `Z_univ` is universal, closed, and contains the base change of the unit
      (finitePart G hsep hft).pair =
        (Space.finiteOpenSubspaceEquiv C S hS G.source (finitePart G hsep hft).objects).1
          (finitePart G hsep hft).inclusion ∧
      Space.IsClosedSubspace C S hS (finitePart G hsep hft).pair.subspace ∧
      Space.ContainsSection C S hS G.source (identityHom G) (identityHom_comp_source G)
        (finitePart G hsep hft).pair ∧
      -- the groupoid has object space `U'` and arrow space `Z_univ`
      (finitePartGroupoid hsep hft).objects = (finitePart G hsep hft).objects ∧
      (finitePartGroupoid hsep hft).arrows = FinitePart.arrowSpace (finitePart G hsep hft) ∧
      -- `s' : (u, Z, z) ↦ (u, Z)`
      (finitePartGroupoid hsep hft).source.hom = FinitePart.sourceHom (finitePart G hsep hft) ∧
      -- `t' : (u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z))`
      (finitePartGroupoid hsep hft).target.hom = targetHom hsep hft ∧
      (Space.finiteOpenSubspaceEquiv C S hS G.source
          (FinitePart.arrowSpace (finitePart G hsep hft))).1
          (targetHom hsep hft ≫ (finitePart G hsep hft).inclusion) =
        translatePair (FinitePart.sourcePair (finitePart G hsep hft))
          (FinitePart.arrowMap (finitePart G hsep hft))
          (FinitePart.arrowMap_comp_source (finitePart G hsep hft)) ∧
      targetHom hsep hft ≫ (finitePart G hsep hft).pair.toBase.hom =
        (finitePart G hsep hft).arrowHom ≫ G.target.hom ∧
      -- `e' : (u, Z) ↦ (u, Z, e ∘ u)`
      (identityHom (finitePartGroupoid hsep hft)).hom = unitHom hsep hft ∧
      unitHom hsep hft ≫ FinitePart.sourceHom (finitePart G hsep hft) =
        𝟙 (finitePart G hsep hft).objects.obj ∧
      unitHom hsep hft ≫ (finitePart G hsep hft).arrowHom =
        (finitePart G hsep hft).pair.toBase.hom ≫ (identityHom G).hom ∧
      -- `i' : (u, Z, z) ↦ (t ∘ z, c(Z, i ∘ z), i ∘ z)`
      (inverseHom (finitePartGroupoid hsep hft)).hom = invHom hsep hft ∧
      invHom hsep hft ≫ FinitePart.sourceHom (finitePart G hsep hft) = targetHom hsep hft ∧
      invHom hsep hft ≫ (finitePart G hsep hft).arrowHom =
        (finitePart G hsep hft).arrowHom ≫ (inverseHom G).hom ∧
      -- `c' : ((u₁, Z₁, z₁), (u₂, Z₂, z₂)) ↦ (u₂, Z₂, z₁ ∘ z₂)`
      (finitePartGroupoid hsep hft).comp.hom = compHom hsep hft ∧
      compHom hsep hft ≫ FinitePart.sourceHom (finitePart G hsep hft) =
        pullback.snd (FinitePart.sourceHom (finitePart G hsep hft)) (targetHom hsep hft) ≫
          FinitePart.sourceHom (finitePart G hsep hft) ∧
      compHom hsep hft ≫ (finitePart G hsep hft).arrowHom =
        composeHom
          (pullback.fst (FinitePart.sourceHom (finitePart G hsep hft)) (targetHom hsep hft) ≫
            (finitePart G hsep hft).arrowHom)
          (pullback.snd (FinitePart.sourceHom (finitePart G hsep hft)) (targetHom hsep hft) ≫
            (finitePart G hsep hft).arrowHom)
          (FinitePart.composable_compose (finitePart G hsep hft) (targetHom hsep hft)
            (targetHom_comp_inclusion hsep hft)) ∧
      -- the canonical morphism of groupoids: `g` on objects, `(u, Z, z) ↦ z` on arrows
      (finitePartGroupoidHom hsep hft).toGroupoidHom.mapObjects =
        (finitePart G hsep hft).pair.toBase.hom ∧
      (finitePartGroupoidHom hsep hft).toGroupoidHom.mapArrows =
        (finitePart G hsep hft).arrowHom := by
  refine ⟨(finitePart G hsep hft).range_inclusion,
    (finitePart G hsep hft).isOpenImmersion_inclusion, (finitePart G hsep hft).toBase_pair,
    (finitePart G hsep hft).isEtale_toBase, (finitePart G hsep hft).pair_eq,
    (finitePart G hsep hft).isClosed_subspace, (finitePart G hsep hft).containsUnit,
    rfl, rfl, rfl, rfl, ?_, targetHom_comp_toBase hsep hft, ?_,
    unitHom_comp_sourceHom hsep hft, unitHom_comp_arrowHom hsep hft, ?_,
    invHom_comp_sourceHom hsep hft, invHom_comp_arrowHom hsep hft, rfl,
    compHom_comp_sourceHom hsep hft, compHom_comp_arrowHom hsep hft, rfl, rfl⟩
  · rw [targetHom_comp_inclusion]
    exact FinitePart.targetSection_spec (finitePart G hsep hft)
  · ext V x
    exact Deformation.PointwiseGroupoid.identityArrow_eq _
      (FinitePart.pointwise (finitePart G hsep hft) (targetHom hsep hft)
        (targetHom_comp_inclusion hsep hft) (finitePart_inclusion_injective hsep hft) V) x
  · ext V x
    exact Deformation.PointwiseGroupoid.inverseArrow_eq _
      (FinitePart.pointwise (finitePart G hsep hft) (targetHom hsep hft)
        (targetHom_comp_inclusion hsep hft) (finitePart_inclusion_injective hsep hft) V) x

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
