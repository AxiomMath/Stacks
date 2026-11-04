module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.ConstantRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposDiagram
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism of constant-coefficient ringed topoi induced by a functor

A functor `f : C' ⥤ C` and a commutative ring `B` give, through the standing data of Stacks 08PA
applied to `Stacks.ChaoticSite.functorSituation`, a morphism of ringed topoi
`(Sh(C'), B̲) ⟶ (Sh(C), B̲)`. The 08PA construction presents its two ends with the *inverse
image* `π⁻¹B̲` of the coefficient sheaf of the point as structure sheaf, and on the topologies
`C` and `C'` inherit from the point. This file identifies both with the constant sheaf on the
chaotic topology and so lands the morphism on `Stacks.ChaoticSite.constantRingedTopos`, which
depends on neither the functor nor the presentation.

The identification is not vacuous: the inverse image of a sheaf of *commutative rings* along
restriction carries transported ring operations, isomorphic but not equal to the original ones.
What makes the whole thing usable downstream is that the comparison is the identity on
underlying sheaves of sets — a *transport* in the sense of `Stacks.IsTransport` — and therefore
so is the inverse-image structure map of the resulting morphism. That is the single fact the
double square of Stacks 08QN consumes.

## Main definitions

* `Stacks.ChaoticSite.constantTotalRingSheaf` and `constantSourceRingSheaf`: the constant sheaf
  of rings read on the inherited topologies.
* `Stacks.ChaoticSite.totalConstantRingSheafIso` and `sourceConstantRingSheafIso`: the
  comparison of the inverse-image coefficient sheaf with the constant sheaf.
* `Stacks.ChaoticSite.constantRingedMorphism` and `constantRingedMorphismOnTrivial`: the induced
  morphism of ringed topoi, on the inherited presentation and on
  `Stacks.ChaoticSite.constantRingedTopos`.

## Main results

* `Stacks.ChaoticSite.isTransport_forget_totalConstantRingSheafIso` and its source counterpart:
  the comparison is the identity on underlying sheaves of sets.
* `Stacks.ChaoticSite.constantRingedMorphismOnTrivial_inverseImage`: the inverse image of the
  induced morphism is restriction along `f` for the chaotic topologies — in particular it does
  not depend on the coefficient ring.
* `Stacks.ChaoticSite.isTransport_constantRingedMorphismOnTrivial_fSharpInverseImageForget`: its
  inverse-image structure map is a transport.
* `Stacks.Sites.FibredCategory.MorphismSituation.isTransport_gRinged_fSharpInverseImageForget`:
  the same statement for the 08PA comparison morphism of any situation, which is where it comes
  from.

## Implementation notes

The last result does not derive the inverse-image structure map of the 08PA morphism from the
commutativity of the ringed triangle through the mate calculus, which needs a raised heartbeat
count. That is unnecessary —
`Stacks.Sites.FibredCategory.MorphismSituation.forget_map_gRinged_fSharpInverseImage` computes it
directly, and `inverseImageComparison_hom_app` identifies the answer with the comparison of the
two restrictions.

`constantRingedMorphismOnTrivial` is a `cast` of `constantRingedMorphism` along two equalities of
ringed topoi, so every statement about it is proved by transporting the corresponding statement
about `constantRingedMorphism` along `constantRingedMorphismOnTrivial_heq`. The equalities are
genuine equalities, not isomorphisms: the topology is *equal* to the chaotic one and the
structure sheaf of the inherited presentation is *defined* as the transport of the constant sheaf
along that equality.

## References

* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe w u₀ u₁ u₂ v₀ v₁ v₂

/-- The inverse-image structure map of the 08PA comparison morphism `g` is a transport: on
underlying sheaves of sets it is the canonical comparison of restriction along `p` and then `u`
with restriction along `p' = u ⋙ p`, which is the identity on sections. -/
theorem isTransport_gRinged_fSharpInverseImageForget
    (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    Stacks.IsTransport S.gRinged.fSharpInverseImageForget := by
  have h : S.gRinged.fSharpInverseImageForget = S.restrictionComp :=
    (AlgebraicGeometry.RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
        S.gRinged).symm.trans
      S.forget_map_gRinged_fSharpInverseImage
  rw [h]
  exact (CategoryTheory.Functor.isTransport_sheafPushforwardContinuousComp'_hom
    S.isFibredOneMorphism.comp_eq _ _ _ _).app _

end Stacks.Sites.FibredCategory.MorphismSituation

namespace Stacks.ChaoticSite

section Transport

universe wA uA vA uD vD

/-- Transporting a sheaf along an equality of topologies does not change its presheaf. -/
theorem sheaf_obj_mp_topology_eq {D : Type uD} [Category.{vD} D] {A : Type uA}
    [Category.{vA} A] {J K : GrothendieckTopology D} (h : J = K) (F : Sheaf J A) :
    (Eq.mp (congrArg (fun L : GrothendieckTopology D => Sheaf L A) h) F).obj = F.obj := by
  cases h
  rfl

/-- Transporting a morphism of ringed topoi along equalities of its source and target does not
change its inverse image. Stated with `HEq` because the inverse image lives in a type that
depends on the two ringed topoi. -/
theorem heq_inverseImage_cast {X X' : AlgebraicGeometry.RingedTopos.{vD, uD, wA}}
    {Y Y' : AlgebraicGeometry.RingedTopos.{vA, uA, wA}}
    [X.J.HasSheafCompose (forget RingCat.{wA})] [Y.J.HasSheafCompose (forget RingCat.{wA})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
    (g : AlgebraicGeometry.RingedToposHom X Y) (hx : X = X') (hy : Y = Y')
    (h : AlgebraicGeometry.RingedToposHom X Y = AlgebraicGeometry.RingedToposHom X' Y') :
    HEq (cast h g).toToposHom.inverseImage g.toToposHom.inverseImage := by
  subst hx
  subst hy
  rfl

/-- Transporting a morphism of ringed topoi along equalities of its source and target keeps its
inverse-image structure map a transport. -/
theorem isTransport_fSharpInverseImageForget_cast
    {X X' : AlgebraicGeometry.RingedTopos.{vD, uD, wA}}
    {Y Y' : AlgebraicGeometry.RingedTopos.{vA, uA, wA}}
    [X.J.HasSheafCompose (forget RingCat.{wA})] [Y.J.HasSheafCompose (forget RingCat.{wA})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{wA} RingCat.{wA})]
    (g : AlgebraicGeometry.RingedToposHom X Y)
    (hg : Stacks.IsTransport g.fSharpInverseImageForget) (hx : X = X') (hy : Y = Y')
    (h : AlgebraicGeometry.RingedToposHom X Y = AlgebraicGeometry.RingedToposHom X' Y') :
    Stacks.IsTransport (cast h g).fSharpInverseImageForget := by
  subst hx
  subst hy
  exact hg

/-- Restriction of sheaves of sets along a functor depends on the two topologies only through
their values, so two presentations of the chaotic topology give the same functor. -/
theorem heq_sheafPushforwardContinuous_trivial {D : Type uD} {D' : Type uA} [Category.{vD} D]
    [Category.{vA} D'] (g : D' ⥤ D) (J : GrothendieckTopology D) (J' : GrothendieckTopology D')
    (h : J = GrothendieckTopology.trivial D) (h' : J' = GrothendieckTopology.trivial D')
    [g.IsContinuous J' J] :
    HEq (g.sheafPushforwardContinuous (Type wA) J' J)
      (g.sheafPushforwardContinuous (Type wA) (GrothendieckTopology.trivial D')
        (GrothendieckTopology.trivial D)) := by
  subst h
  subst h'
  rfl

end Transport

universe w v v' u u'

variable (C : Type u) (C' : Type u') [Category.{v} C] [Category.{v'} C']
  (f : C' ⥤ C) (B : CommRingCat.{max w u u' v v'})

/-- The constant sheaf of rings `B̲` on `C`, read on the topology `C` inherits from the chaotic
point. -/
noncomputable def constantTotalRingSheaf :
    Sheaf (functorSituation.{w} C C' f B).totalTopology CommRingCat.{max w u u' v v'} :=
  Eq.mp (congrArg (fun J : GrothendieckTopology C => Sheaf J CommRingCat.{max w u u' v v'})
    (functorSituation_totalTopology.{w} C C' f B).symm) (constantRingSheaf C B)

/-- The constant sheaf of rings `B̲` on `C'`, read on the topology `C'` inherits from the chaotic
point. -/
noncomputable def constantSourceRingSheaf :
    Sheaf (functorSituation.{w} C C' f B).sourceTopology CommRingCat.{max w u u' v v'} :=
  Eq.mp (congrArg (fun J : GrothendieckTopology C' => Sheaf J CommRingCat.{max w u u' v v'})
    (functorSituation_sourceTopology.{w} C C' f B).symm) (constantRingSheaf C' B)


/-- Restricting the constant sheaf of the chaotic point along the structure functor of `C` gives
the constant sheaf on `C`: precomposing a constant functor with anything is constant. -/
theorem restriction_base_eq_constantTotalRingSheaf :
    ((functorSituation.{w} C C' f B).p.sheafPushforwardContinuous
        CommRingCat.{max w u u' v v'} (functorSituation.{w} C C' f B).totalTopology
        (functorSituation.{w} C C' f B).base.J).obj
      (functorSituation.{w} C C' f B).base.O = constantTotalRingSheaf.{w} C C' f B := by
  refine ObjectProperty.FullSubcategory.ext ?_
  have h : (constantTotalRingSheaf.{w} C C' f B).obj = (constantRingSheaf C B).obj :=
    sheaf_obj_mp_topology_eq (functorSituation_totalTopology.{w} C C' f B).symm
      (constantRingSheaf C B)
  rw [h]
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- The same for the source: restricting along the structure functor of `C'` gives the constant
sheaf on `C'`. -/
theorem restriction_base_eq_constantSourceRingSheaf :
    ((functorSituation.{w} C C' f B).p'.sheafPushforwardContinuous
        CommRingCat.{max w u u' v v'} (functorSituation.{w} C C' f B).sourceTopology
        (functorSituation.{w} C C' f B).base.J).obj
      (functorSituation.{w} C C' f B).base.O = constantSourceRingSheaf.{w} C C' f B := by
  refine ObjectProperty.FullSubcategory.ext ?_
  have h : (constantSourceRingSheaf.{w} C C' f B).obj = (constantRingSheaf C' B).obj :=
    sheaf_obj_mp_topology_eq (functorSituation_sourceTopology.{w} C C' f B).symm
      (constantRingSheaf C' B)
  rw [h]
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- The inverse-image coefficient sheaf on `C` is the constant sheaf `B̲`. -/
noncomputable def totalConstantRingSheafIso :
    ((functorSituation.{w} C C' f B).totalTopos (functorSituation.{w} C C' f B).pi).O ≅
      constantTotalRingSheaf.{w} C C' f B :=
  inverseImageCommRingRestrictionIso (functorSituation.{w} C C' f B).totalTopology
      (functorSituation.{w} C C' f B).base.J (functorSituation.{w} C C' f B).p
      (functorSituation.{w} C C' f B).pi (Iso.refl _)
      (functorSituation.{w} C C' f B).base.O ≪≫
    eqToIso (restriction_base_eq_constantTotalRingSheaf.{w} C C' f B)

/-- The inverse-image coefficient sheaf on `C'` is the constant sheaf `B̲`. -/
noncomputable def sourceConstantRingSheafIso :
    ((functorSituation.{w} C C' f B).sourceTopos (functorSituation.{w} C C' f B).pi').O ≅
      constantSourceRingSheaf.{w} C C' f B :=
  inverseImageCommRingRestrictionIso (functorSituation.{w} C C' f B).sourceTopology
      (functorSituation.{w} C C' f B).base.J (functorSituation.{w} C C' f B).p'
      (functorSituation.{w} C C' f B).pi' (Iso.refl _)
      (functorSituation.{w} C C' f B).base.O ≪≫
    eqToIso (restriction_base_eq_constantSourceRingSheaf.{w} C C' f B)

/-- The comparison on `C` is the identity on underlying sheaves of sets: the transported ring
operations are carried by the same sections. -/
theorem isTransport_forget_totalConstantRingSheafIso :
    Stacks.IsTransport ((sheafCompose (functorSituation.{w} C C' f B).totalTopology
      (forget CommRingCat.{max w u u' v v'})).map
        (totalConstantRingSheafIso.{w} C C' f B).hom) := by
  have key : (sheafCompose (functorSituation.{w} C C' f B).totalTopology
        (forget CommRingCat.{max w u u' v v'})).map
          (totalConstantRingSheafIso.{w} C C' f B).hom =
      (Iso.refl ((functorSituation.{w} C C' f B).pi.inverseImage)).hom.app
          ((sheafCompose (functorSituation.{w} C C' f B).base.J
            (forget CommRingCat.{max w u u' v v'})).obj
              (functorSituation.{w} C C' f B).base.O) ≫
        (sheafCompose (functorSituation.{w} C C' f B).totalTopology
          (forget CommRingCat.{max w u u' v v'})).map
            (eqToHom (restriction_base_eq_constantTotalRingSheaf.{w} C C' f B)) :=
    ((sheafCompose (functorSituation.{w} C C' f B).totalTopology
        (forget CommRingCat.{max w u u' v v'})).map_comp _ _).trans
      (congrArg (fun m ↦ m ≫ (sheafCompose (functorSituation.{w} C C' f B).totalTopology
          (forget CommRingCat.{max w u u' v v'})).map
            (eqToHom (restriction_base_eq_constantTotalRingSheaf.{w} C C' f B)))
        (inverseImageCommRingRestrictionIso_hom_forget
          (functorSituation.{w} C C' f B).totalTopology (functorSituation.{w} C C' f B).base.J
          (functorSituation.{w} C C' f B).p (functorSituation.{w} C C' f B).pi
          (Iso.refl ((functorSituation.{w} C C' f B).pi.inverseImage))
          (functorSituation.{w} C C' f B).base.O))
  rw [key]
  exact ((Stacks.IsTransport.id _).app _).comp ((Stacks.IsTransport.eqToHom _).map _)

/-- The comparison on `C'` is likewise the identity on underlying sheaves of sets. -/
theorem isTransport_forget_sourceConstantRingSheafIso :
    Stacks.IsTransport ((sheafCompose (functorSituation.{w} C C' f B).sourceTopology
      (forget CommRingCat.{max w u u' v v'})).map
        (sourceConstantRingSheafIso.{w} C C' f B).hom) := by
  have key : (sheafCompose (functorSituation.{w} C C' f B).sourceTopology
        (forget CommRingCat.{max w u u' v v'})).map
          (sourceConstantRingSheafIso.{w} C C' f B).hom =
      (Iso.refl ((functorSituation.{w} C C' f B).pi'.inverseImage)).hom.app
          ((sheafCompose (functorSituation.{w} C C' f B).base.J
            (forget CommRingCat.{max w u u' v v'})).obj
              (functorSituation.{w} C C' f B).base.O) ≫
        (sheafCompose (functorSituation.{w} C C' f B).sourceTopology
          (forget CommRingCat.{max w u u' v v'})).map
            (eqToHom (restriction_base_eq_constantSourceRingSheaf.{w} C C' f B)) :=
    ((sheafCompose (functorSituation.{w} C C' f B).sourceTopology
        (forget CommRingCat.{max w u u' v v'})).map_comp _ _).trans
      (congrArg (fun m ↦ m ≫ (sheafCompose (functorSituation.{w} C C' f B).sourceTopology
          (forget CommRingCat.{max w u u' v v'})).map
            (eqToHom (restriction_base_eq_constantSourceRingSheaf.{w} C C' f B)))
        (inverseImageCommRingRestrictionIso_hom_forget
          (functorSituation.{w} C C' f B).sourceTopology (functorSituation.{w} C C' f B).base.J
          (functorSituation.{w} C C' f B).p' (functorSituation.{w} C C' f B).pi'
          (Iso.refl ((functorSituation.{w} C C' f B).pi'.inverseImage))
          (functorSituation.{w} C C' f B).base.O))
  rw [key]
  exact ((Stacks.IsTransport.id _).app _).comp ((Stacks.IsTransport.eqToHom _).map _)

/-- The ringed topos `(Sh(C), B̲)` in the inherited presentation. -/
noncomputable def constantTotalRingedTopos : AlgebraicGeometry.RingedTopos.{v, u,
    max w u u' v v'} where
  C := C
  J := (functorSituation.{w} C C' f B).totalTopology
  O := constantTotalRingSheaf.{w} C C' f B

/-- The ringed topos `(Sh(C'), B̲)` in the inherited presentation. -/
noncomputable def constantSourceRingedTopos : AlgebraicGeometry.RingedTopos.{v', u',
    max w u u' v v'} where
  C := C'
  J := (functorSituation.{w} C C' f B).sourceTopology
  O := constantSourceRingSheaf.{w} C C' f B

/-- The inherited presentation on `C` *is* the constant-coefficient ringed topos: the equality
carries the topology and the structure sheaf together. -/
theorem constantTotalRingedTopos_eq :
    constantTotalRingedTopos.{w} C C' f B = constantRingedTopos C B :=
  constantRingedTopos_mk_eq C B _ (functorSituation_totalTopology.{w} C C' f B)

/-- The inherited presentation on `C'` is the constant-coefficient ringed topos. Consequently two
different functors out of `C'` give morphisms with the same source. -/
theorem constantSourceRingedTopos_eq :
    constantSourceRingedTopos.{w} C C' f B = constantRingedTopos C' B :=
  constantRingedTopos_mk_eq C' B _ (functorSituation_sourceTopology.{w} C C' f B)

/-- The morphism of ringed topoi `(Sh(C'), B̲) ⟶ (Sh(C), B̲)` induced by `f`, in the inherited
presentation: the 08PA comparison morphism with its two coefficient sheaves read as the constant
sheaf. -/
noncomputable def constantRingedMorphism :
    AlgebraicGeometry.RingedToposHom (constantSourceRingedTopos.{w} C C' f B)
      (constantTotalRingedTopos.{w} C C' f B) :=
  (functorSituation.{w} C C' f B).gRinged.ofStructureIso
    (sourceConstantRingSheafIso.{w} C C' f B) (totalConstantRingSheafIso.{w} C C' f B)

/-- Its inverse-image structure map is a transport, because the 08PA one is and both comparisons
are. -/
theorem isTransport_constantRingedMorphism_fSharpInverseImageForget :
    Stacks.IsTransport (constantRingedMorphism.{w} C C' f B).fSharpInverseImageForget :=
  AlgebraicGeometry.RingedToposHom.isTransport_ofStructureIso_fSharpInverseImageForget
    (functorSituation.{w} C C' f B).gRinged
    (sourceConstantRingSheafIso.{w} C C' f B) (totalConstantRingSheafIso.{w} C C' f B)
    ((functorSituation.{w} C C' f B).isTransport_gRinged_fSharpInverseImageForget)
    (isTransport_forget_sourceConstantRingSheafIso.{w} C C' f B)
    (isTransport_forget_totalConstantRingSheafIso.{w} C C' f B)

/-- The two presentations have the same type of morphisms of ringed topoi between them. -/
theorem constantRingedToposHom_type_eq :
    AlgebraicGeometry.RingedToposHom (constantSourceRingedTopos.{w} C C' f B)
        (constantTotalRingedTopos.{w} C C' f B) =
      AlgebraicGeometry.RingedToposHom (constantRingedTopos C' B) (constantRingedTopos C B) := by
  rw [constantSourceRingedTopos_eq.{w} C C' f B, constantTotalRingedTopos_eq.{w} C C' f B]

/-- The morphism of ringed topoi `(Sh(C'), B̲) ⟶ (Sh(C), B̲)` induced by `f`, on the fixed
chaotic presentation `Stacks.ChaoticSite.constantRingedTopos`. -/
noncomputable def constantRingedMorphismOnTrivial :
    AlgebraicGeometry.RingedToposHom (constantRingedTopos C' B) (constantRingedTopos C B) :=
  cast (constantRingedToposHom_type_eq.{w} C C' f B) (constantRingedMorphism.{w} C C' f B)

/-- Changing the presentation does not change the morphism. -/
theorem constantRingedMorphismOnTrivial_heq :
    HEq (constantRingedMorphismOnTrivial.{w} C C' f B) (constantRingedMorphism.{w} C C' f B) :=
  cast_heq _ _

/-- The inverse image of the induced morphism is restriction along `f` for the chaotic
topologies. In particular it does not mention the coefficient ring, so the same functor serves
for every `B`; that is what lets the two squares of Stacks 08QN be compared. -/
theorem constantRingedMorphismOnTrivial_inverseImage :
    (constantRingedMorphismOnTrivial.{w} C C' f B).toToposHom.inverseImage =
      f.sheafPushforwardContinuous (Type (max w u u' v v'))
        (GrothendieckTopology.trivial C') (GrothendieckTopology.trivial C) := by
  have hc : f.IsContinuous (functorSituation.{w} C C' f B).sourceTopology
      (functorSituation.{w} C C' f B).totalTopology :=
    (functorSituation.{w} C C' f B).uContinuous
  refine eq_of_heq ((heq_inverseImage_cast (constantRingedMorphism.{w} C C' f B)
    (constantSourceRingedTopos_eq.{w} C C' f B) (constantTotalRingedTopos_eq.{w} C C' f B)
    (constantRingedToposHom_type_eq.{w} C C' f B)).trans ?_)
  exact heq_sheafPushforwardContinuous_trivial f _ _
    (functorSituation_totalTopology.{w} C C' f B)
    (functorSituation_sourceTopology.{w} C C' f B)

/-- The inverse-image structure map of the induced morphism is a transport. This is the whole of
what the double square of Stacks 08QN needs from this file. -/
theorem isTransport_constantRingedMorphismOnTrivial_fSharpInverseImageForget :
    Stacks.IsTransport
      (constantRingedMorphismOnTrivial.{w} C C' f B).fSharpInverseImageForget :=
  isTransport_fSharpInverseImageForget_cast (constantRingedMorphism.{w} C C' f B)
    (isTransport_constantRingedMorphism_fSharpInverseImageForget.{w} C C' f B)
    (constantSourceRingedTopos_eq.{w} C C' f B) (constantTotalRingedTopos_eq.{w} C C' f B)
    (constantRingedToposHom_type_eq.{w} C C' f B)

end Stacks.ChaoticSite

/- The morphism of ringed topoi induced by a functor of chaotic sites with constant
coefficients is `constantRingedMorphism`, read on the constant-coefficient presentation by
`constantRingedMorphismOnTrivial`, whose inverse image is restriction along the functor. The
tags are registered on those declarations rather than on copies of them. -/
add_to_stacks 08PH "ringed_morphism" Stacks.ChaoticSite.constantRingedMorphism

add_to_stacks 08PH "ringed_morphism" Stacks.ChaoticSite.constantRingedMorphismOnTrivial

add_to_stacks 08PH "ringed_morphism"
  Stacks.ChaoticSite.constantRingedMorphismOnTrivial_inverseImage

end
