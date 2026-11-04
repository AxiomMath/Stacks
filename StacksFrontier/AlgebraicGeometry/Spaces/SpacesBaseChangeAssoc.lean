module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism

/-!
# Associativity of the composition isomorphisms of étale base change

Base change along a composite of morphisms of algebraic spaces is canonically isomorphic to the
iterated base change, which is `AlgebraicGeometry.Space.spacesBaseChange_comp` (Stacks 03G2,
part (2)), and the same holds for the induced morphisms of small étale topoi, which is
`AlgebraicGeometry.Space.smallToposMorphism_comp` (Stacks 03G2, part (3)).  "Compatible with
compositions" in those two parts asks for more than the mere existence of the isomorphisms: for
three morphisms the two ways of reassociating a threefold composite must agree.  This file proves
that coherence at the three levels in which the tag states compatibility with composition — the
spaces-étale *sites*, their *direct images*, and the *morphisms of small étale topoi* — each from
the previous one.

The statement at the level of sites is the exact analogue, for the spaces-étale sites, of
Mathlib's `CategoryTheory.GrothendieckTopology.overMapPullback_assoc`, which is the same pentagon
for the slice categories; the orientation differs only in that the equation is here written with
the two composition isomorphisms in the forward direction and the identification
`(f ≫ g) ≫ h = f ≫ g ≫ h` carried by a `CategoryTheory.eqToIso`.

## Main results

* `AlgebraicGeometry.Space.spacesBaseChange_comp_assoc`: the associativity coherence of
  `AlgebraicGeometry.Space.spacesBaseChange_comp`.
* `AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp_assoc'`: the associativity coherence
  of `AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp`, that is, the same coherence for
  the direct images on the spaces-étale topoi, as an equality of isomorphisms. The unprimed name
  is the same coherence as an equality of natural transformations.
* `AlgebraicGeometry.Space.smallToposMorphism_comp_assoc`: the associativity coherence of
  `AlgebraicGeometry.Space.smallToposMorphism_comp`, the direct-image composition isomorphism of
  Stacks 03G2, part (3).
* `CategoryTheory.Functor.sheafPushforwardContinuousComp'_assoc_of_pentagon`: for continuous
  functors between sites, `CategoryTheory.Functor.sheafPushforwardContinuousComp'` inherits any
  associativity coherence holding between the four isomorphisms of functors of sites it is
  applied to. The coherence is a hypothesis, which is what distinguishes this statement from
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'_assoc`, where the four isomorphisms
  are `eqToIso` of equalities and the coherence is automatic.
* `MorphismOfTopoi.transport_comp_pushforward_comp_assoc`: transport of morphisms of topoi along
  equivalences likewise inherits any associativity coherence of the direct-image composition
  isomorphisms it is applied to.
* `AlgebraicGeometry.Space.spacesBaseChange_eqToHom_app_projection`,
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'_trans_eqToIso` and
  `CategoryTheory.Functor.isoWhiskerLeft_isoWhiskerRight_eqToIso`: the three bookkeeping lemmas
  absorbing the identification `(f ≫ g) ≫ h = f ≫ g ≫ h` at the three levels.

## Implementation notes

The proof of the pentagon at the level of sites does not compute either composition isomorphism.
Both sides are, at every object, a morphism into the fibre product `X ×_W V` presenting the base
change along `f ≫ g ≫ h`, so they are equal as soon as they agree after composition with the two
projections of that fibre product, which is `CategoryTheory.IsPullback.hom_ext` applied to the
`isPullback` field of `AlgebraicGeometry.Space.spacesBaseChange`.  The component towards `X` is
automatic: both sides are morphisms of the slice over `X`, so `CategoryTheory.Over.w` applies to
each.  The component towards `V` turns both sides into the threefold iterated projection by
`AlgebraicGeometry.Space.spacesBaseChange_comp_projection`, applied once for each of the three
composition isomorphisms involved, together with one instance of naturality of the projection of
`AlgebraicGeometry.Space.spacesBaseChange` along `f`.  This is why no hypothesis beyond the ones
already carried by `AlgebraicGeometry.Space.spacesBaseChange` is needed.

Peeling that equation of isomorphisms down to the level of fibre products is done with
`CategoryTheory.ObjectProperty.hom_ext` and `CategoryTheory.Over.OverMorphism.ext` rather than
with `ext`, which descends all the way to elements of the presheaves involved, and the
reassociation is `simp only [Category.assoc]` rather than `aesop_cat`, which does not close the
goal.

The two passages upwards are stated for arbitrary coherence hypotheses rather than only for base
change, because nothing in either argument is geometric.  For sheaf pushforward the proof is the
one Mathlib uses for `CategoryTheory.GrothendieckTopology.overMapPullback_assoc`, except that the
final step, where functoriality of the sheaf merges two restriction maps, has to be taken after a
`change` restating the goal with the objects spelled as values of the sheaf: in the goal as the
simp set leaves it those objects are spelled as values of the pushforward functors, and `rw` then
rejects the merge with *"the target expression is not type-correct under the `implicit`
transparency level"*.  For transport the content is naturality of the unit isomorphism of the
equivalence of the middle topos, exactly as in
`MorphismOfTopoi.transport_comp_pushforward_comparison`, together with naturality of the
composition isomorphism of the middle pair and the coherence hypothesis itself; all four are
supplied as `have`s with their statements written out, since the forms that
`CategoryTheory.NatTrans.naturality` produces for a composite functor are not the ones `rw` can
use.

The three `CategoryTheory.eqToIso` bookkeeping lemmas take the equality they transport as a
hypothesis and are proved by induction on it; this is what allows the geometric statements to name
their own `congrArg`, since any two proofs of an equality are interchangeable.  Absorbing them has
to be done in term mode rather than by `rw`: the pattern is only definitionally present in the
goal, because `AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp` and
`AlgebraicGeometry.Space.smallToposMorphism_comp` are definitions, and `rw` rejects the rewrite at
the `implicit` transparency level even where the pattern is displayed verbatim in the goal.

The three coherences belong to parts (2) and (3) of Tag 03G2, and two of them carry a
part-stringed `@[stacks 03G2]` attribute: the one at the level of sites, as part (2), and the one
for the morphisms of small étale topoi, as part (3).  The intermediate one for the direct images,
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp_assoc'`, is the step between those two
and carries no attribute.  The other clauses of that tag are already tagged in
`StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange` and
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆ v₇ u₇ v₈ u₈ t₁ t₂ u

namespace CategoryTheory.Functor

/-- Whiskering an identification of functors on both sides gives the identification of the two
composites.

The identification of the composites is a hypothesis rather than a `congrArg` built here, so that
a caller may supply its own spelling of it; any proof of the equality will do, since proofs of an
equality are interchangeable. -/
theorem isoWhiskerLeft_isoWhiskerRight_eqToIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {X : Type u₃} [Category.{v₃} X] {Y : Type u₄} [Category.{v₄} Y]
    (K : C ⥤ D) {M M' : D ⥤ X} (p : M = M') (L : X ⥤ Y)
    (q : K ⋙ M ⋙ L = K ⋙ M' ⋙ L) :
    isoWhiskerLeft K (isoWhiskerRight (eqToIso p) L) = eqToIso q := by
  subst p
  simp

section Sites

variable {C₀ : Type u₁} [Category.{v₁} C₀] {C₁ : Type u₂} [Category.{v₂} C₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {C₃ : Type u₄} [Category.{v₄} C₃]

/-- Pushforward of sheaves along a continuous functor turns an identification of that functor with
another one into the identification of the two pushforwards, compatibly with
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`.

The identification of the pushforwards is a hypothesis rather than a `congrArg` built here,
because the continuity instances of the two functors are different arguments; any proof of the
equality will do, since proofs of an equality are interchangeable. -/
theorem sheafPushforwardContinuousComp'_trans_eqToIso {F : C₂ ⥤ C₁} {G : C₁ ⥤ C₀}
    {FG FG' : C₂ ⥤ C₀} (e : F ⋙ G ≅ FG) (p : FG = FG') (A : Type t₁) [Category.{t₂} A]
    (J₂ : GrothendieckTopology C₂) (J₁ : GrothendieckTopology C₁)
    (J₀ : GrothendieckTopology C₀) [F.IsContinuous J₂ J₁] [G.IsContinuous J₁ J₀]
    [FG.IsContinuous J₂ J₀] [FG'.IsContinuous J₂ J₀]
    (q : FG.sheafPushforwardContinuous A J₂ J₀ = FG'.sheafPushforwardContinuous A J₂ J₀) :
    sheafPushforwardContinuousComp' (e ≪≫ eqToIso p) A J₂ J₁ J₀ =
      sheafPushforwardContinuousComp' e A J₂ J₁ J₀ ≪≫ eqToIso q := by
  subst p
  simp

/-- Pushforward of sheaves along continuous functors between sites carries an associativity
coherence between four isomorphisms of functors of sites to the corresponding associativity
coherence between the four induced isomorphisms of pushforward functors.

This is the site-independent content of Mathlib's
`CategoryTheory.GrothendieckTopology.overMapPullback_assoc`, which is the case of the three slice
functors `CategoryTheory.Over.map` and the isomorphisms `CategoryTheory.Over.mapComp`. -/
theorem sheafPushforwardContinuousComp'_assoc_of_pentagon {u : C₁ ⥤ C₀} {v : C₂ ⥤ C₁}
    {w : C₃ ⥤ C₂} {uv : C₂ ⥤ C₀} {vw : C₃ ⥤ C₁} {uvw : C₃ ⥤ C₀}
    (e₁ : v ⋙ u ≅ uv) (e₂ : w ⋙ v ≅ vw) (e₃ : vw ⋙ u ≅ uvw) (e₄ : w ⋙ uv ≅ uvw)
    (A : Type t₁) [Category.{t₂} A]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
    [u.IsContinuous J₁ J₀] [v.IsContinuous J₂ J₁] [w.IsContinuous J₃ J₂]
    [uv.IsContinuous J₂ J₀] [vw.IsContinuous J₃ J₁] [uvw.IsContinuous J₃ J₀]
    (hpent : isoWhiskerRight e₂ u ≪≫ e₃ =
      associator w v u ≪≫ isoWhiskerLeft w e₁ ≪≫ e₄) :
    isoWhiskerRight (sheafPushforwardContinuousComp' e₁ A J₂ J₁ J₀)
          (w.sheafPushforwardContinuous A J₃ J₂) ≪≫
        sheafPushforwardContinuousComp' e₄ A J₃ J₂ J₀ =
      associator _ _ _ ≪≫
        isoWhiskerLeft (u.sheafPushforwardContinuous A J₁ J₀)
          (sheafPushforwardContinuousComp' e₂ A J₃ J₂ J₁) ≪≫
        sheafPushforwardContinuousComp' e₃ A J₃ J₁ J₀ := by
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  have hinv : e₃.inv.app (Opposite.unop U) ≫ u.map (e₂.inv.app (Opposite.unop U)) =
      e₄.inv.app (Opposite.unop U) ≫ e₁.inv.app (w.obj (Opposite.unop U)) := by
    simpa using NatTrans.congr_app (congrArg Iso.inv hpent) (Opposite.unop U)
  dsimp
  simp only [Category.id_comp, sheafPushforwardContinuousComp'_hom_app_hom_app,
    sheafPushforwardContinuous_map_hom_app, sheafPushforwardContinuous_obj_obj_map,
    Quiver.Hom.unop_op]
  change M.obj.map (e₁.inv.app (w.obj (Opposite.unop U))).op ≫
        M.obj.map (e₄.inv.app (Opposite.unop U)).op =
      M.obj.map (u.map (e₂.inv.app (Opposite.unop U))).op ≫
        M.obj.map (e₃.inv.app (Opposite.unop U)).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hinv]

end Sites

end CategoryTheory.Functor

namespace MorphismOfTopoi

variable {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
  {G : Type u₃} [Category.{v₃} G] {H : Type u₄} [Category.{v₄} H]
  {E' : Type u₅} [Category.{v₅} E'] {F' : Type u₆} [Category.{v₆} F']
  {G' : Type u₇} [Category.{v₇} G'] {H' : Type u₈} [Category.{v₈} H']

/-- Transport of morphisms of topoi along equivalences of the topoi involved carries an
associativity coherence between four isomorphisms of direct images to the corresponding
associativity coherence between the four transported ones.

The composition isomorphisms are arbitrary isomorphisms onto the direct image of a *given*
morphism of topoi, rather than the identity isomorphism onto the direct image of
`MorphismOfTopoi.comp`, because that is the situation of base change along a composite: the
morphism of topoi attached to `f ≫ g` is not the composite of those attached to `f` and `g`, only
canonically isomorphic to it. -/
theorem transport_comp_pushforward_comp_assoc (φ : MorphismOfTopoi E F)
    (ψ : MorphismOfTopoi F G) (χ : MorphismOfTopoi G H) (φψ : MorphismOfTopoi E G)
    (ψχ : MorphismOfTopoi F H) (φψχ : MorphismOfTopoi E H)
    (p₁ : φ.pushforward ⋙ ψ.pushforward ≅ φψ.pushforward)
    (p₂ : ψ.pushforward ⋙ χ.pushforward ≅ ψχ.pushforward)
    (p₃ : φ.pushforward ⋙ ψχ.pushforward ≅ φψχ.pushforward)
    (p₄ : φψ.pushforward ⋙ χ.pushforward ≅ φψχ.pushforward)
    (eE : E ≌ E') (eF : F ≌ F') (eG : G ≌ G') (eH : H ≌ H')
    (hpent : Functor.isoWhiskerRight p₁ χ.pushforward ≪≫ p₄ =
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft φ.pushforward p₂ ≪≫ p₃) :
    Functor.isoWhiskerRight
          (transport_comp_pushforward φ ψ eE eF eG ≪≫
            Functor.isoWhiskerLeft eE.inverse (Functor.isoWhiskerRight p₁ eG.functor))
          (χ.transport eG eH).pushforward ≪≫
        transport_comp_pushforward φψ χ eE eG eH ≪≫
          Functor.isoWhiskerLeft eE.inverse (Functor.isoWhiskerRight p₄ eH.functor) =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (φ.transport eE eF).pushforward
          (transport_comp_pushforward ψ χ eF eG eH ≪≫
            Functor.isoWhiskerLeft eF.inverse (Functor.isoWhiskerRight p₂ eH.functor)) ≪≫
        transport_comp_pushforward φ ψχ eE eF eH ≪≫
          Functor.isoWhiskerLeft eE.inverse (Functor.isoWhiskerRight p₃ eH.functor) := by
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  have hp : χ.pushforward.map (p₁.hom.app (eE.inverse.obj x)) ≫
        p₄.hom.app (eE.inverse.obj x) =
      p₂.hom.app (φ.pushforward.obj (eE.inverse.obj x)) ≫ p₃.hom.app (eE.inverse.obj x) := by
    simpa using NatTrans.congr_app (congrArg Iso.hom hpent) (eE.inverse.obj x)
  have hunit : ∀ {a b : G} (k : a ⟶ b),
      eG.inverse.map (eG.functor.map k) ≫ eG.unitIso.inv.app b = eG.unitIso.inv.app a ≫ k :=
    fun k => eG.unitIso.inv.naturality k
  have hn₂ : χ.pushforward.map (ψ.pushforward.map (eF.unitIso.inv.app
          (φ.pushforward.obj (eE.inverse.obj x)))) ≫
        p₂.hom.app (φ.pushforward.obj (eE.inverse.obj x)) =
      p₂.hom.app (eF.inverse.obj (eF.functor.obj
          (φ.pushforward.obj (eE.inverse.obj x)))) ≫
        ψχ.pushforward.map (eF.unitIso.inv.app
          (φ.pushforward.obj (eE.inverse.obj x))) :=
    p₂.hom.naturality _
  have innerG : eG.inverse.map (eG.functor.map (ψ.pushforward.map (eF.unitIso.inv.app
            (φ.pushforward.obj (eE.inverse.obj x)))) ≫
          eG.functor.map (p₁.hom.app (eE.inverse.obj x))) ≫
        eG.unitIso.inv.app (φψ.pushforward.obj (eE.inverse.obj x)) =
      eG.unitIso.inv.app (ψ.pushforward.obj (eF.inverse.obj (eF.functor.obj
          (φ.pushforward.obj (eE.inverse.obj x))))) ≫
        ψ.pushforward.map (eF.unitIso.inv.app
            (φ.pushforward.obj (eE.inverse.obj x))) ≫
          p₁.hom.app (eE.inverse.obj x) := by
    rw [eG.inverse.map_comp, Category.assoc, hunit, ← Category.assoc, hunit, Category.assoc]
    rfl
  have hn₂' : χ.pushforward.map (ψ.pushforward.map (eF.unitIso.inv.app
          (φ.pushforward.obj (eE.inverse.obj x)))) ≫
        p₂.hom.app (φ.pushforward.obj (eE.inverse.obj x)) ≫
          p₃.hom.app (eE.inverse.obj x) =
      p₂.hom.app (eF.inverse.obj (eF.functor.obj
          (φ.pushforward.obj (eE.inverse.obj x)))) ≫
        ψχ.pushforward.map (eF.unitIso.inv.app
            (φ.pushforward.obj (eE.inverse.obj x))) ≫
          p₃.hom.app (eE.inverse.obj x) := by
    rw [← Category.assoc, hn₂, Category.assoc]
  have key : χ.pushforward.map (eG.inverse.map
          (eG.functor.map (ψ.pushforward.map (eF.unitIso.inv.app
              (φ.pushforward.obj (eE.inverse.obj x)))) ≫
            eG.functor.map (p₁.hom.app (eE.inverse.obj x)))) ≫
        χ.pushforward.map (eG.unitIso.inv.app (φψ.pushforward.obj (eE.inverse.obj x))) ≫
          p₄.hom.app (eE.inverse.obj x) =
      χ.pushforward.map (eG.unitIso.inv.app (ψ.pushforward.obj (eF.inverse.obj
          (eF.functor.obj (φ.pushforward.obj (eE.inverse.obj x)))))) ≫
        p₂.hom.app (eF.inverse.obj (eF.functor.obj
            (φ.pushforward.obj (eE.inverse.obj x)))) ≫
          ψχ.pushforward.map (eF.unitIso.inv.app
              (φ.pushforward.obj (eE.inverse.obj x))) ≫
            p₃.hom.app (eE.inverse.obj x) := by
    rw [← Category.assoc, ← Functor.map_comp, innerG]
    simp only [Functor.map_comp, Category.assoc, hp, hn₂']
  have h3 : ∀ {A₁ A₂ A₃ A₄ : H} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄),
      eH.functor.map a ≫ eH.functor.map b ≫ eH.functor.map c =
        eH.functor.map (a ≫ b ≫ c) := by
    intro A₁ A₂ A₃ A₄ a b c
    simp
  have h4 : ∀ {A₁ A₂ A₃ A₄ A₅ : H} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄)
      (d : A₄ ⟶ A₅),
      (eH.functor.map a ≫ eH.functor.map b) ≫ eH.functor.map c ≫ eH.functor.map d =
        eH.functor.map (a ≫ b ≫ c ≫ d) := by
    intro A₁ A₂ A₃ A₄ A₅ a b c d
    simp
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app]
  simp only [Category.id_comp]
  exact (h3 _ _ _).trans
    ((congrArg (fun k => eH.functor.map k) key).trans (h4 _ _ _ _).symm)

end MorphismOfTopoi

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Equal morphisms of algebraic spaces have equal base-change functors, and the resulting
identification of base-changed objects respects the cartesian projections to the original object:
after an induction on the equality it is the identity. -/
theorem spacesBaseChange_eqToHom_app_projection {X W : AlgebraicSpaces B S hS}
    {k₁ k₂ : X ⟶ W} (e : k₁ = k₂) (V : SpacesEtale B S hS W) :
    Over.Hom.left ((eqToHom (congrArg
          (fun k => (spacesBaseChange B S hS k).functor) e)).app V).hom ≫
        (spacesBaseChange B S hS k₂).projection.app V =
      (spacesBaseChange B S hS k₁).projection.app V := by
  subst e
  simp

/-- **Stacks 03G2, part (2).** The composition isomorphism of spaces-étale base change is
associative: for `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ W` the two ways of identifying the
threefold iterated base change with base change along `f ≫ g ≫ h` — first contracting `g` and
`h`, or first contracting `f` and `g` — agree.

This is the coherence that makes `AlgebraicGeometry.Space.spacesBaseChange_comp` a genuine
compatibility of base change with composition, and it is the spaces-étale analogue of
`CategoryTheory.GrothendieckTopology.overMapPullback_assoc`. -/
@[stacks 03G2 "part (2), associativity of the composition isomorphism"]
theorem spacesBaseChange_comp_assoc {W X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) :
    Functor.isoWhiskerRight (spacesBaseChange_comp B S hS g h)
          (spacesBaseChange B S hS f).functor ≪≫ spacesBaseChange_comp B S hS f (g ≫ h) =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (spacesBaseChange B S hS h).functor
          (spacesBaseChange_comp B S hS f g) ≪≫
        spacesBaseChange_comp B S hS (f ≫ g) h ≪≫
        eqToIso (congrArg (fun k => (spacesBaseChange B S hS k).functor)
          (Category.assoc f g h)) := by
  refine Iso.ext (NatTrans.ext (funext fun V => ?_))
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  refine ((spacesBaseChange B S hS (f ≫ g ≫ h)).isPullback V).hom_ext ?_ ?_
  · have hnat : Over.Hom.left ((spacesBaseChange B S hS f).functor.map
            ((spacesBaseChange_comp B S hS g h).hom.app V)).hom ≫
          (spacesBaseChange B S hS f).projection.app
            ((spacesBaseChange B S hS (g ≫ h)).functor.obj V) =
        (spacesBaseChange B S hS f).projection.app
            (((spacesBaseChange B S hS h).functor ⋙
              (spacesBaseChange B S hS g).functor).obj V) ≫
          Over.Hom.left ((spacesBaseChange_comp B S hS g h).hom.app V).hom :=
      (spacesBaseChange B S hS f).projection.naturality _
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, eqToIso.hom,
      ObjectProperty.FullSubcategory.comp_hom, Over.comp_left,
      ObjectProperty.FullSubcategory.id_hom, Over.id_left]
    simp only [Category.assoc, Category.id_comp]
    rw [spacesBaseChange_eqToHom_app_projection B S hS (Category.assoc f g h),
      spacesBaseChange_comp_projection B S hS f (g ≫ h) V,
      spacesBaseChange_comp_projection B S hS (f ≫ g) h V, ← Category.assoc, hnat,
      Category.assoc, spacesBaseChange_comp_projection B S hS g h V, ← Category.assoc,
      ← Category.assoc, spacesBaseChange_comp_projection B S hS f g
        ((spacesBaseChange B S hS h).functor.obj V)]
    rfl
  · exact (Over.w _).trans (Over.w _).symm

/-- **Stacks 03G2, part (2) on direct images.** The composition isomorphism of the direct images
along spaces-étale base change is associative.

This is `AlgebraicGeometry.Space.spacesBaseChange_comp_assoc` carried through sheaf pushforward by
`CategoryTheory.Functor.sheafPushforwardContinuousComp'_assoc_of_pentagon`.

`AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp_assoc` is the same coherence as an
equality of natural transformations, with the composition comparisons entering through `Iso.hom`
and `Iso.inv`; this statement is the equality of the isomorphisms themselves, so it carries the
primed name. -/
theorem spacesBaseChange_pushforward_comp_assoc' {W X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Functor.isoWhiskerRight (spacesBaseChange_pushforward_comp B S hS f g)
          ((spacesBaseChange B S hS h).functor.sheafPushforwardContinuous (Type (u + 1))
            (SpacesEtale.topology B S hS W) (SpacesEtale.topology B S hS Z)) ≪≫
        spacesBaseChange_pushforward_comp B S hS (f ≫ g) h ≪≫
        eqToIso (congrArg
          (fun k => (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
            (Type (u + 1)) (SpacesEtale.topology B S hS W)
            (SpacesEtale.topology B S hS X)) (Category.assoc f g h)) =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
            ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X))
            (spacesBaseChange_pushforward_comp B S hS g h) ≪≫
        spacesBaseChange_pushforward_comp B S hS f (g ≫ h) := by
  have habs : spacesBaseChange_pushforward_comp B S hS (f ≫ g) h ≪≫
        eqToIso (congrArg
          (fun k => (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
            (Type (u + 1)) (SpacesEtale.topology B S hS W)
            (SpacesEtale.topology B S hS X)) (Category.assoc f g h)) =
      Functor.sheafPushforwardContinuousComp'
        (spacesBaseChange_comp B S hS (f ≫ g) h ≪≫ eqToIso (congrArg
          (fun k => (spacesBaseChange B S hS k).functor) (Category.assoc f g h)))
        (Type (u + 1)) (SpacesEtale.topology B S hS W) (SpacesEtale.topology B S hS Z)
        (SpacesEtale.topology B S hS X) :=
    (Functor.sheafPushforwardContinuousComp'_trans_eqToIso
      (spacesBaseChange_comp B S hS (f ≫ g) h)
      (congrArg (fun k => (spacesBaseChange B S hS k).functor) (Category.assoc f g h))
      (Type (u + 1)) (SpacesEtale.topology B S hS W) (SpacesEtale.topology B S hS Z)
      (SpacesEtale.topology B S hS X) _).symm
  rw [habs]
  exact Functor.sheafPushforwardContinuousComp'_assoc_of_pentagon
    (spacesBaseChange_comp B S hS f g) (spacesBaseChange_comp B S hS g h)
    (spacesBaseChange_comp B S hS f (g ≫ h))
    (spacesBaseChange_comp B S hS (f ≫ g) h ≪≫ eqToIso (congrArg
      (fun k => (spacesBaseChange B S hS k).functor) (Category.assoc f g h)))
    (Type (u + 1)) (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
    (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS W)
    (spacesBaseChange_comp_assoc B S hS f g h)

/-- **Stacks 03G2, part (3).** The direct-image composition isomorphism of the morphisms of small
étale topoi is associative: for `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ W` the two ways of
identifying the threefold composite of direct images with the direct image of `f ≫ g ≫ h` agree.

This is the coherence that makes the construction of
`AlgebraicGeometry.Space.smallToposMorphism` "compatible with compositions" in the sense of part
(3) of the tag, rather than merely equipped with composition isomorphisms.  It is
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp_assoc'` transported along the comparison
equivalences of Stacks 03G1 by
`MorphismOfTopoi.transport_comp_pushforward_comp_assoc`. -/
@[stacks 03G2 "part (3), associativity of the composition isomorphism"]
theorem smallToposMorphism_comp_assoc {W X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Z ⟶ W) :
    Functor.isoWhiskerRight (smallToposMorphism_comp B S hS f g)
          (smallToposMorphism B S hS h).pushforward ≪≫
        smallToposMorphism_comp B S hS (f ≫ g) h ≪≫
        eqToIso (congrArg (fun k => (smallToposMorphism B S hS k).pushforward)
          (Category.assoc f g h)) =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (smallToposMorphism B S hS f).pushforward
          (smallToposMorphism_comp B S hS g h) ≪≫
        smallToposMorphism_comp B S hS f (g ≫ h) := by
  have hW : Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS X).inverse
        (Functor.isoWhiskerRight
          (spacesBaseChange_pushforward_comp B S hS (f ≫ g) h ≪≫ eqToIso (congrArg
            (fun k => (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
              (Type (u + 1)) (SpacesEtale.topology B S hS W)
              (SpacesEtale.topology B S hS X)) (Category.assoc f g h)))
          (smallEtaleToposEquiv B S hS W).functor) =
      Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS X).inverse
          (Functor.isoWhiskerRight (spacesBaseChange_pushforward_comp B S hS (f ≫ g) h)
            (smallEtaleToposEquiv B S hS W).functor) ≪≫
        eqToIso (congrArg (fun k => (smallToposMorphism B S hS k).pushforward)
          (Category.assoc f g h)) := by
    rw [Functor.isoWhiskerRight_trans, Functor.isoWhiskerLeft_trans]
    exact congrArg (fun t => Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS X).inverse
        (Functor.isoWhiskerRight (spacesBaseChange_pushforward_comp B S hS (f ≫ g) h)
          (smallEtaleToposEquiv B S hS W).functor) ≪≫ t)
      (Functor.isoWhiskerLeft_isoWhiskerRight_eqToIso _ _ _ _)
  have habs : MorphismOfTopoi.transport_comp_pushforward
        (spacesBaseChange_isMorphismOfSites B S hS (f ≫ g)).morphismOfTopoi
        (spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi
        (smallEtaleToposEquiv B S hS X) (smallEtaleToposEquiv B S hS Z)
        (smallEtaleToposEquiv B S hS W) ≪≫
      Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS X).inverse
        (Functor.isoWhiskerRight
          (spacesBaseChange_pushforward_comp B S hS (f ≫ g) h ≪≫ eqToIso (congrArg
            (fun k => (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
              (Type (u + 1)) (SpacesEtale.topology B S hS W)
              (SpacesEtale.topology B S hS X)) (Category.assoc f g h)))
          (smallEtaleToposEquiv B S hS W).functor) =
      smallToposMorphism_comp B S hS (f ≫ g) h ≪≫
        eqToIso (congrArg (fun k => (smallToposMorphism B S hS k).pushforward)
          (Category.assoc f g h)) :=
    (congrArg (fun t => MorphismOfTopoi.transport_comp_pushforward
      (spacesBaseChange_isMorphismOfSites B S hS (f ≫ g)).morphismOfTopoi
      (spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi
      (smallEtaleToposEquiv B S hS X) (smallEtaleToposEquiv B S hS Z)
      (smallEtaleToposEquiv B S hS W) ≪≫ t) hW).trans (Iso.trans_assoc _ _ _).symm
  exact (congrArg (fun t => Functor.isoWhiskerRight (smallToposMorphism_comp B S hS f g)
      (smallToposMorphism B S hS h).pushforward ≪≫ t) habs.symm).trans
    (MorphismOfTopoi.transport_comp_pushforward_comp_assoc
      (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi
      (spacesBaseChange_isMorphismOfSites B S hS g).morphismOfTopoi
      (spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi
      (spacesBaseChange_isMorphismOfSites B S hS (f ≫ g)).morphismOfTopoi
      (spacesBaseChange_isMorphismOfSites B S hS (g ≫ h)).morphismOfTopoi
      (spacesBaseChange_isMorphismOfSites B S hS (f ≫ g ≫ h)).morphismOfTopoi
      (spacesBaseChange_pushforward_comp B S hS f g)
      (spacesBaseChange_pushforward_comp B S hS g h)
      (spacesBaseChange_pushforward_comp B S hS f (g ≫ h))
      (spacesBaseChange_pushforward_comp B S hS (f ≫ g) h ≪≫ eqToIso (congrArg
        (fun k => (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
          (Type (u + 1)) (SpacesEtale.topology B S hS W)
          (SpacesEtale.topology B S hS X)) (Category.assoc f g h)))
      (smallEtaleToposEquiv B S hS X) (smallEtaleToposEquiv B S hS Y)
      (smallEtaleToposEquiv B S hS Z) (smallEtaleToposEquiv B S hS W)
      (spacesBaseChange_pushforward_comp_assoc' B S hS f g h))

end AlgebraicGeometry.Space

end
