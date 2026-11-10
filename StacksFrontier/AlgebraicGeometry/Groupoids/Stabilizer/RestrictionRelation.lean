module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Restriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a groupoid and its relation

Restricting groupoid schemes and restricting (pre-)equivalence relations agree via the
constructions of Tags 0232 and 0233.  Restricting a groupoid scheme and then taking its
pre-relation gives the restriction of its pre-relation, and restricting an equivalence relation
and then taking its groupoid scheme gives the restriction of its groupoid scheme, as groupoid
schemes.

## Main definitions

* `AlgebraicGeometry.restrictionIso` is the canonical identification of the arrow scheme of the
  restricted groupoid with the arrow scheme of the restricted pre-relation.
* `Stacks.Groupoids.GroupoidScheme.Isomorphism` is an isomorphism of groupoid schemes, and
  `Stacks.Groupoids.GroupoidScheme.Isomorphism.ofMono` builds one from compatible isomorphisms
  of objects and arrows when the target and source maps are jointly monic.

## Main results

* `AlgebraicGeometry.restrictionIso_relation` and `AlgebraicGeometry.restrictionIso_arrows`
  identify the two projections of the comparison, and `AlgebraicGeometry.restrictionIso_unique`
  characterizes the comparison by them.
* `AlgebraicGeometry.existsUnique_isomorphism_restriction_of_extendsRelation`: a groupoid
  scheme extending the restriction of a monic pre-relation is isomorphic, as a groupoid scheme,
  to the restriction of a groupoid scheme extending the pre-relation.
* `AlgebraicGeometry.restriction_groupoidScheme_agrees_restriction_preRelation`: restricting
  groupoid schemes and restricting (pre-)equivalence relations agree.

## References

* [Stacks Project, Tag 0232](https://stacks.math.columbia.edu/tag/0232)
* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
* [Stacks Project, Tag 02VD](https://stacks.math.columbia.edu/tag/02VD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The canonical map from the restricted groupoid's arrow scheme to the restricted relation's
arrow scheme. -/
noncomputable def restrictionIsoHom {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) :
    restrictionArrows G g ⟶
      PreRelation.restriction (groupoidPreRelation G) g :=
  pullback.lift
    (prod.lift (restrictionTarget G g) (restrictionSource G g))
    (restrictionArrowsToArrows G g) (by
      have ht : restrictionTarget G g ≫ g =
          restrictionArrowsToArrows G g ≫ G.target := by
        simpa only [restrictionTarget, restrictionArrowsToArrows,
          restrictionArrows, ← Category.assoc] using
          congrArg (fun h => pullback.fst (pullback.snd g G.target)
            (pullback.fst G.source g) ≫ h)
            (pullback.condition (f := g) (g := G.target))
      have hs : restrictionSource G g ≫ g =
          restrictionArrowsToArrows G g ≫ G.source := by
        simpa only [restrictionSource, restrictionArrowsToArrows,
          restrictionArrows, ← Category.assoc] using
          (show (pullback.snd (pullback.snd g G.target)
              (pullback.fst G.source g) ≫ pullback.snd G.source g) ≫ g =
              (pullback.fst (pullback.snd g G.target)
                (pullback.fst G.source g) ≫ pullback.snd g G.target) ≫ G.source from by
            calc
              _ = (pullback.snd (pullback.snd g G.target)
                    (pullback.fst G.source g) ≫ pullback.fst G.source g) ≫ G.source := by
                  simpa only [← Category.assoc] using
                    congrArg (fun h => pullback.snd (pullback.snd g G.target)
                      (pullback.fst G.source g) ≫ h)
                      (pullback.condition (f := G.source) (g := g)).symm
              _ = _ := by
                  simpa only [← Category.assoc] using
                    congrArg (fun h => h ≫ G.source)
                      (pullback.condition (f := pullback.snd g G.target)
                        (g := pullback.fst G.source g)).symm)
      simp only [groupoidPreRelation, prod.lift_map, prod.comp_lift,
        ht, hs])

/-- The inverse map from the restricted relation's arrow scheme to the restricted groupoid's
arrow scheme. -/
noncomputable def restrictionIsoInv {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) :
    PreRelation.restriction (groupoidPreRelation G) g ⟶
      restrictionArrows G g :=
  pullback.lift
    (pullback.lift
      (pullback.fst (prod.map g g) (groupoidPreRelation G) ≫ prod.fst)
      (pullback.snd (prod.map g g) (groupoidPreRelation G))
      (by
        simpa only [groupoidPreRelation, Category.assoc,
          prod.map_fst, prod.lift_fst] using
          (pullback.condition_assoc (f := prod.map g g)
            (g := groupoidPreRelation G) prod.fst)))
    (pullback.lift
      (pullback.snd (prod.map g g) (groupoidPreRelation G))
      (pullback.fst (prod.map g g) (groupoidPreRelation G) ≫ prod.snd)
      (by
        simpa only [groupoidPreRelation, Category.assoc,
          prod.map_snd, prod.lift_snd] using
          (pullback.condition_assoc (f := prod.map g g)
            (g := groupoidPreRelation G) prod.snd).symm))
    (by simp only [pullback.lift_snd, pullback.lift_fst])

/-- The groupoid restriction and the restriction of its associated pre-equivalence relation have
canonically isomorphic arrow schemes. -/
noncomputable def restrictionIso {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    restrictionArrows G g ≅
      PreRelation.restriction (groupoidPreRelation G) g := by
  refine ⟨restrictionIsoHom G g, restrictionIsoInv G g, ?_, ?_⟩
  all_goals repeat' (first | apply pullback.hom_ext | apply prod.hom_ext)
  all_goals simp only [restrictionArrows, PreRelation.restriction,
    Category.assoc, restrictionIsoInv, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_fst_assoc, pullback.lift_snd_assoc, restrictionIsoHom,
    prod.lift_fst, prod.lift_snd,
    prod.comp_lift, groupoidPreRelation, restrictionTarget,
    restrictionSource, restrictionArrowsToArrows,
    pullback.condition, Category.id_comp]

/-- Under the canonical comparison, the restricted relation map is the pair of target and source
maps of the restricted groupoid. -/
theorem restrictionIso_relation {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    (restrictionIso G g).hom ≫
        PreRelation.restrict (groupoidPreRelation G) g =
      prod.lift (restrictionTarget G g) (restrictionSource G g) := by
  change restrictionIsoHom G g ≫ _ = _
  exact pullback.lift_fst _ _ _

/-- Under the canonical comparison, the projection to the original arrow scheme is the map from
the restricted groupoid. -/
theorem restrictionIso_arrows {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    (restrictionIso G g).hom ≫
        pullback.snd (prod.map g g) (groupoidPreRelation G) =
      restrictionArrowsToArrows G g := by
  change restrictionIsoHom G g ≫ _ = _
  exact pullback.lift_snd _ _ _

/-- The canonical comparison is the unique isomorphism commuting with the relation map and the
projection to the original arrow scheme. -/
theorem restrictionIso_unique {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects)
    (i : restrictionArrows G g ≅
      PreRelation.restriction (groupoidPreRelation G) g)
    (hrelation : i.hom ≫
        PreRelation.restrict (groupoidPreRelation G) g =
      prod.lift (restrictionTarget G g) (restrictionSource G g))
    (harrows : i.hom ≫ pullback.snd (prod.map g g) (groupoidPreRelation G) =
      restrictionArrowsToArrows G g) :
    i = restrictionIso G g :=
  Iso.ext <| pullback.hom_ext (hrelation.trans (restrictionIso_relation G g).symm)
    (harrows.trans (restrictionIso_arrows G g).symm)

end AlgebraicGeometry

/-! ### Isomorphisms of groupoid schemes -/

namespace Stacks.Groupoids.GroupoidScheme

/-- An isomorphism of groupoid schemes: morphisms of groupoid schemes in both directions whose
maps on objects and on arrows are mutually inverse. -/
structure Isomorphism {S : Scheme.{u}} (G H : GroupoidScheme S) where
  /-- The morphism from `G` to `H`. -/
  hom : Hom G H
  /-- The morphism from `H` to `G`. -/
  inv : Hom H G
  hom_inv_id_objects : hom.mapObjects ≫ inv.mapObjects = 𝟙 G.objects
  inv_hom_id_objects : inv.mapObjects ≫ hom.mapObjects = 𝟙 H.objects
  hom_inv_id_arrows : hom.mapArrows ≫ inv.mapArrows = 𝟙 G.arrows
  inv_hom_id_arrows : inv.mapArrows ≫ hom.mapArrows = 𝟙 H.arrows

variable {S : Scheme.{u}} {G H : GroupoidScheme S}

/-- When the target and source maps of `H` are jointly monic, a pair of maps on objects and
arrows compatible with source and target is a morphism of groupoid schemes. -/
noncomputable def Hom.ofMono (φ : G.objects ⟶ H.objects) (ψ : G.arrows ⟶ H.arrows)
    (hs : ψ ≫ H.source = G.source ≫ φ) (ht : ψ ≫ H.target = G.target ≫ φ)
    [Mono (AlgebraicGeometry.groupoidPreRelation H)] : Hom G H where
  mapObjects := φ
  mapArrows := ψ
  map_source := hs
  map_target := ht
  map_identity := by
    refine (cancel_mono (AlgebraicGeometry.groupoidPreRelation H)).1 (prod.hom_ext ?_ ?_)
    · simp only [Category.assoc, prod.lift_fst, H.target_identity, Category.comp_id, ht,
        reassoc_of% G.target_identity]
    · simp only [Category.assoc, prod.lift_snd, H.source_identity, Category.comp_id, hs,
        reassoc_of% G.source_identity]
  map_comp := by
    intro T f g w w'
    refine (cancel_mono (AlgebraicGeometry.groupoidPreRelation H)).1 (prod.hom_ext ?_ ?_)
    · simp only [compose, Category.assoc, prod.lift_fst, ht, reassoc_of% G.target_comp,
        H.target_comp, pullback.lift_fst_assoc]
    · simp only [compose, Category.assoc, prod.lift_snd, hs, reassoc_of% G.source_comp,
        H.source_comp, pullback.lift_snd_assoc]

/-- An isomorphism of the schemes of objects and of the schemes of arrows of two groupoid
schemes, compatible with source and target, is an isomorphism of groupoid schemes as soon as
the target and source maps of one of them are jointly monic. -/
noncomputable def Isomorphism.ofMono (φ : G.objects ≅ H.objects) (ψ : G.arrows ≅ H.arrows)
    (hs : ψ.hom ≫ H.source = G.source ≫ φ.hom) (ht : ψ.hom ≫ H.target = G.target ≫ φ.hom)
    [Mono (AlgebraicGeometry.groupoidPreRelation G)] : Isomorphism G H :=
  have hs' : ψ.inv ≫ G.source = H.source ≫ φ.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% hs, Iso.hom_inv_id, Category.comp_id]
  have ht' : ψ.inv ≫ G.target = H.target ≫ φ.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% ht, Iso.hom_inv_id, Category.comp_id]
  have hrel : AlgebraicGeometry.groupoidPreRelation H =
      ψ.inv ≫ AlgebraicGeometry.groupoidPreRelation G ≫ (prod.mapIso φ φ).hom := by
    apply prod.hom_ext
    · simp only [prod.lift_fst, prod.mapIso_hom, Category.assoc, prod.map_fst,
        prod.lift_fst_assoc, reassoc_of% ht', Iso.inv_hom_id, Category.comp_id]
    · simp only [prod.lift_snd, prod.mapIso_hom, Category.assoc, prod.map_snd,
        prod.lift_snd_assoc, reassoc_of% hs', Iso.inv_hom_id, Category.comp_id]
  have : Mono (AlgebraicGeometry.groupoidPreRelation H) := by rw [hrel]; infer_instance
  { hom := Hom.ofMono φ.hom ψ.hom hs ht
    inv := Hom.ofMono φ.inv ψ.inv hs' ht'
    hom_inv_id_objects := φ.hom_inv_id
    inv_hom_id_objects := φ.inv_hom_id
    hom_inv_id_arrows := ψ.hom_inv_id
    inv_hom_id_arrows := ψ.inv_hom_id }

/-- Two morphisms of groupoid schemes with the same maps on objects and on arrows are
equal. -/
theorem Hom.ext_of_map {F₁ F₂ : Hom G H} (h₁ : F₁.mapObjects = F₂.mapObjects)
    (h₂ : F₁.mapArrows = F₂.mapArrows) : F₁ = F₂ := by
  rcases F₁ with ⟨a₁, b₁, _, _, _, _⟩
  rcases F₂ with ⟨a₂, b₂, _, _, _, _⟩
  dsimp only at h₁ h₂
  subst h₁ h₂
  rfl

/-- A left inverse of `f₁` and a right inverse of `f₂ = f₁` are equal. -/
private theorem inv_eq_of_hom_eq {C : Type*} [Category C] {X Y : C} {f₁ f₂ : X ⟶ Y}
    {g₁ g₂ : Y ⟶ X} (h : f₁ = f₂) (h₁ : g₁ ≫ f₁ = 𝟙 Y) (h₂ : f₂ ≫ g₂ = 𝟙 X) : g₁ = g₂ := by
  rw [← Category.comp_id g₁, ← h₂, ← h, ← Category.assoc, h₁, Category.id_comp]

/-- An isomorphism of groupoid schemes is determined by the maps on objects and on arrows of
its forward morphism. -/
theorem Isomorphism.ext_of_hom {e₁ e₂ : Isomorphism G H}
    (h₁ : e₁.hom.mapObjects = e₂.hom.mapObjects) (h₂ : e₁.hom.mapArrows = e₂.hom.mapArrows) :
    e₁ = e₂ := by
  have i₁ := inv_eq_of_hom_eq h₁ e₁.inv_hom_id_objects e₂.hom_inv_id_objects
  have i₂ := inv_eq_of_hom_eq h₂ e₁.inv_hom_id_arrows e₂.hom_inv_id_arrows
  rcases e₁ with ⟨f₁, g₁, _, _, _, _⟩
  rcases e₂ with ⟨f₂, g₂, _, _, _, _⟩
  dsimp only at h₁ h₂ i₁ i₂
  obtain rfl := Hom.ext_of_map h₁ h₂
  obtain rfl := Hom.ext_of_map i₁ i₂
  rfl

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry

/-! ### The two restrictions agree -/

/-- **Restricting a groupoid, then taking its relation.** For any groupoid scheme realizing the
restriction of `G` along `g`, its scheme of arrows is isomorphic to the restriction of the
pre-relation of `G` along `g`, compatibly with the maps to `U' ×_S U'` and to the arrows of
`G`. -/
theorem exists_iso_restriction_groupoidPreRelation {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (RG : GroupoidScheme.Restriction G g) :
    ∃ e : RG.groupoid.arrows ≅ PreRelation.restriction (groupoidPreRelation G) g,
      e.hom ≫ PreRelation.restrict (groupoidPreRelation G) g =
          groupoidPreRelation RG.groupoid ≫
            prod.map (eqToHom RG.objects_eq) (eqToHom RG.objects_eq) ∧
        e.hom ≫ pullback.snd (prod.map g g) (groupoidPreRelation G) = RG.hom.mapArrows := by
  refine ⟨eqToIso RG.arrows_eq ≪≫ restrictionIso G g, ?_, ?_⟩
  · simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, restrictionIso_relation]
    apply prod.hom_ext <;> simp [RG.target_eq, RG.source_eq]
  · simp [restrictionIso_arrows, RG.mapArrows_eq]

/-- The canonical arrow comparison of `exists_iso_restriction_groupoidPreRelation` is the only
isomorphism with these two compatibilities. -/
theorem existsUnique_iso_restriction_groupoidPreRelation {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) (RG : GroupoidScheme.Restriction G g) :
    ∃! e : RG.groupoid.arrows ≅ PreRelation.restriction (groupoidPreRelation G) g,
      e.hom ≫ PreRelation.restrict (groupoidPreRelation G) g =
          groupoidPreRelation RG.groupoid ≫
            prod.map (eqToHom RG.objects_eq) (eqToHom RG.objects_eq) ∧
        e.hom ≫ pullback.snd (prod.map g g) (groupoidPreRelation G) = RG.hom.mapArrows := by
  obtain ⟨e, he⟩ := exists_iso_restriction_groupoidPreRelation G g RG
  exact ⟨e, he, fun e' he' => Iso.ext (pullback.hom_ext (he'.1.trans he.1.symm)
    (he'.2.trans he.2.symm))⟩

/-- A morphism of groupoid schemes into a restriction of `G` is determined by its map on
objects and by its composite, on arrows, with the morphism from the restriction to `G`. -/
theorem GroupoidScheme.Restriction.mapArrows_ext {S : Scheme.{u}} {G : GroupoidScheme S}
    {U' : Over S} {g : U' ⟶ G.objects} (RG : GroupoidScheme.Restriction G g)
    {A : GroupoidScheme S} {F₁ F₂ : GroupoidScheme.Hom A RG.groupoid}
    (h₁ : F₁.mapObjects = F₂.mapObjects)
    (h₂ : F₁.mapArrows ≫ RG.hom.mapArrows = F₂.mapArrows ≫ RG.hom.mapArrows) :
    F₁.mapArrows = F₂.mapArrows := by
  have hs₁ := F₁.map_source
  have hs₂ := F₂.map_source
  have ht₁ := F₁.map_target
  have ht₂ := F₂.map_target
  rw [RG.source_eq] at hs₁ hs₂
  rw [RG.target_eq] at ht₁ ht₂
  rw [RG.mapArrows_eq] at h₂
  refine (cancel_mono (eqToHom RG.arrows_eq)).1
    (GroupoidScheme.restriction_hom_ext G g _ _ ?_ ?_ ?_)
  · refine (cancel_mono (eqToHom RG.objects_eq.symm)).1 ?_
    simp only [Category.assoc] at hs₁ hs₂ ⊢
    rw [hs₁, hs₂, h₁]
  · refine (cancel_mono (eqToHom RG.objects_eq.symm)).1 ?_
    simp only [Category.assoc] at ht₁ ht₂ ⊢
    rw [ht₁, ht₂, h₁]
  · simpa only [Category.assoc] using h₂

/-- A groupoid scheme extending a monic pre-relation has jointly monic target and source. -/
theorem mono_groupoidPreRelation_of_extendsRelation {S : Scheme.{u}} {R U : Over S}
    {k : PreRelation R U} [Mono k] {A : GroupoidScheme S} (hA : ExtendsRelation k A) :
    Mono (groupoidPreRelation A) := by
  rcases A with ⟨Ao, Aa, As, At, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases hA with ⟨hAo, hAa, hAs, hAt⟩
  dsimp only at hAo hAa
  subst hAo hAa
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hAs hAt
  subst hAs hAt
  change Mono (prod.lift (k ≫ prod.fst) (k ≫ prod.snd))
  rw [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id]
  infer_instance

/-- **Taking the groupoid of a restricted relation.** Let `j` be a monic pre-relation, `A` a
groupoid scheme extending the restriction of `j` along `g`, and `G` a groupoid scheme extending
`j`. Then `A` is isomorphic, as a groupoid scheme, to any groupoid scheme realizing the
restriction of `G` along `g`; the isomorphism is the identity of `U'` on objects and commutes
with the maps of arrows to `R`. -/
theorem exists_isomorphism_restriction_of_extendsRelation {S : Scheme.{u}} {R U U' : Over S}
    (j : PreRelation R U) [Mono j] (g : U' ⟶ U)
    (A : GroupoidScheme S) (hA : ExtendsRelation (PreRelation.restrict j g) A)
    (G : GroupoidScheme S) (hG : ExtendsRelation j G) (g' : U' ⟶ G.objects)
    (hg : g' ≫ eqToHom hG.objects_eq = g) (RB : GroupoidScheme.Restriction G g') :
    ∃ e : GroupoidScheme.Isomorphism A RB.groupoid,
      e.hom.mapObjects = eqToHom (hA.objects_eq.trans RB.objects_eq.symm) ∧
        e.hom.mapArrows ≫ RB.hom.mapArrows ≫ eqToHom hG.arrows_eq =
          eqToHom hA.arrows_eq ≫ pullback.snd (prod.map g g) j := by
  have hAmono : Mono (groupoidPreRelation A) := mono_groupoidPreRelation_of_extendsRelation hA
  obtain ⟨hGo, hGa, hGs, hGt⟩ := id hG
  subst hGo hGa
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hGs hGt hg
  have hj : groupoidPreRelation G = j := prod.hom_ext (by simp [hGt]) (by simp [hGs])
  subst hj hg
  rcases A with ⟨Ao, Aa, As, At, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨hAo, hAa, hAs, hAt⟩ := id hA
  dsimp only at hAo hAa hAs hAt
  subst hAo hAa
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hAs hAt
  subst hAs hAt
  have key : (restrictionIso G g').inv ≫ prod.lift (restrictionTarget G g')
      (restrictionSource G g') = PreRelation.restrict (groupoidPreRelation G) g' := by
    rw [Iso.inv_comp_eq, restrictionIso_relation]
  have key_arr : (restrictionIso G g').inv ≫ restrictionArrowsToArrows G g' =
      pullback.snd (prod.map g' g') (groupoidPreRelation G) := by
    rw [Iso.inv_comp_eq, restrictionIso_arrows]
  refine ⟨GroupoidScheme.Isomorphism.ofMono (eqToIso RB.objects_eq.symm)
    ((restrictionIso G g').symm ≪≫ eqToIso RB.arrows_eq.symm) ?_ ?_, rfl, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc, RB.source_eq,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simpa only [Category.assoc, prod.lift_snd_assoc] using congrArg (· ≫ prod.snd ≫
      eqToHom RB.objects_eq.symm) key
  · simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc, RB.target_eq,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simpa only [Category.assoc, prod.lift_fst_assoc] using congrArg (· ≫ prod.fst ≫
      eqToHom RB.objects_eq.symm) key
  · simp only [GroupoidScheme.Isomorphism.ofMono, GroupoidScheme.Hom.ofMono, Iso.trans_hom,
      Iso.symm_hom, eqToIso.hom, Category.assoc, RB.mapArrows_eq, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Category.comp_id, key_arr]

/-- The isomorphism of `exists_isomorphism_restriction_of_extendsRelation` is the only one
with these two compatibilities. -/
theorem existsUnique_isomorphism_restriction_of_extendsRelation {S : Scheme.{u}}
    {R U U' : Over S} (j : PreRelation R U) [Mono j] (g : U' ⟶ U)
    (A : GroupoidScheme S) (hA : ExtendsRelation (PreRelation.restrict j g) A)
    (G : GroupoidScheme S) (hG : ExtendsRelation j G) (g' : U' ⟶ G.objects)
    (hg : g' ≫ eqToHom hG.objects_eq = g) (RB : GroupoidScheme.Restriction G g') :
    ∃! e : GroupoidScheme.Isomorphism A RB.groupoid,
      e.hom.mapObjects = eqToHom (hA.objects_eq.trans RB.objects_eq.symm) ∧
        e.hom.mapArrows ≫ RB.hom.mapArrows ≫ eqToHom hG.arrows_eq =
          eqToHom hA.arrows_eq ≫ pullback.snd (prod.map g g) j := by
  obtain ⟨e, he₁, he₂⟩ := exists_isomorphism_restriction_of_extendsRelation j g A hA G hG g' hg RB
  refine ⟨e, ⟨he₁, he₂⟩, fun e' ⟨h₁, h₂⟩ => GroupoidScheme.Isomorphism.ext_of_hom
    (h₁.trans he₁.symm) (RB.mapArrows_ext (h₁.trans he₁.symm) ?_)⟩
  exact (cancel_mono (eqToHom hG.arrows_eq)).1
    (by simpa only [Category.assoc] using h₂.trans he₂.symm)

/-- Restricting groupoid schemes and restricting (pre-)equivalence relations
agree via the constructions of Tags 0232 and 0233.

1. For a groupoid scheme `G` and `g : U' ⟶ G.objects`, the pre-relation of the restriction
   `G|_{U'}` (Tag 02VC) agrees with the restriction (Tag 02V9) of the pre-relation of `G`
   (Tag 0232): there is a unique isomorphism of their schemes of arrows compatible with the
   maps to `U' ×_S U'` and to the arrows of `G`.
2. For an equivalence relation `j : R ⟶ U ×_S U` and `g : U' ⟶ U`, the groupoid scheme of the
   restricted relation `j|_{U'}` (Tag 0233) agrees with the restriction to `U'` of the groupoid
   scheme of `j`: there is a unique isomorphism of groupoid schemes between them which is the
   identity of `U'` on objects and commutes with the maps of arrows to `R`. Being a pair of
   mutually inverse morphisms of groupoid schemes, it identifies the compositions, identities
   and inverses of the two groupoid structures. -/
@[stacks 02VD]
theorem restriction_groupoidScheme_agrees_restriction_preRelation {S : Scheme.{u}} :
    (∀ (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects),
      ∃! e : (GroupoidScheme.restrict G g).groupoid.arrows ≅
          PreRelation.restriction (groupoidPreRelation G) g,
        e.hom ≫ PreRelation.restrict (groupoidPreRelation G) g =
            groupoidPreRelation (GroupoidScheme.restrict G g).groupoid ≫
              prod.map (eqToHom (GroupoidScheme.restrict G g).objects_eq)
                (eqToHom (GroupoidScheme.restrict G g).objects_eq) ∧
          e.hom ≫ pullback.snd (prod.map g g) (groupoidPreRelation G) =
            (GroupoidScheme.restrict G g).hom.mapArrows) ∧
    (∀ {R U U' : Over S} (j : PreRelation R U) [IsEquivalenceRelation j.target j.source]
        (g : U' ⟶ U),
      ∃! e : GroupoidScheme.Isomorphism
          (groupoidSchemeOfIsEquivalenceRelation (PreRelation.restrict j g))
          (GroupoidScheme.restrict (groupoidSchemeOfIsEquivalenceRelation j)
            (g ≫ eqToHom
              (groupoidSchemeOfIsEquivalenceRelation_extendsRelation j).objects_eq.symm)).groupoid,
        e.hom.mapObjects = eqToHom
            ((groupoidSchemeOfIsEquivalenceRelation_extendsRelation
                (PreRelation.restrict j g)).objects_eq.trans
              (GroupoidScheme.restrict _ _).objects_eq.symm) ∧
          e.hom.mapArrows ≫ (GroupoidScheme.restrict _ _).hom.mapArrows ≫
              eqToHom (groupoidSchemeOfIsEquivalenceRelation_extendsRelation j).arrows_eq =
            eqToHom (groupoidSchemeOfIsEquivalenceRelation_extendsRelation
                (PreRelation.restrict j g)).arrows_eq ≫ pullback.snd (prod.map g g) j) := by
  refine ⟨fun G _ g => existsUnique_iso_restriction_groupoidPreRelation G g _, ?_⟩
  intro R U U' j hj g
  have : Mono j :=
    ((Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1 hj).1
  exact existsUnique_isomorphism_restriction_of_extendsRelation j g _
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation (PreRelation.restrict j g)) _
    (groupoidSchemeOfIsEquivalenceRelation_extendsRelation j) _
    (by simp) _

end AlgebraicGeometry

end
