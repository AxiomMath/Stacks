module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage

/-!
# Transitivity of the fibre comparison of Stacks 04K2, part (4)

Let `a : W ⟶ Y` and `b : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` and let `w` be
a geometric point of `W`.  The fibre comparisons of Stacks 04K2, part (4), for sheaves of
commutative rings on the small étale sites,
`AlgebraicGeometry.Space.smallEtaleInverseImageFiberRingIso`, are functorial along the composite:
for a sheaf of commutative rings `F` on the small étale site of `Z`,
```
F_{b(a(w))} ≅ (b⁻¹F)_{a(w)} ≅ (a⁻¹b⁻¹F)_w ≅ ((a ≫ b)⁻¹F)_w
```
is the fibre comparison of `a ≫ b`, the last step being the fibre at `w` of the composition law
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso` of Stacks 03G8.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInverseImageFiberRingIso_comp`: the transitivity.
* `AlgebraicGeometry.Space.smallEtaleSkyscraperRingIso_comp_of_forgetRing`: the transitivity of
  the skyscraper comparisons of which the fibre comparisons are the conjugates.
* `AlgebraicGeometry.Space.spacesBaseChangeSkyscraperRingIso_comp` and
  `AlgebraicGeometry.Space.spacesBaseChangeFiberIso_inv_comp`: the same on the spaces-étale
  sites, where it is compatibility of the lifts of geometric points with pullback pasting.
* `MorphismOfTopoi.forget_map_conjugateEquiv_ringAdjunction_comp`: conjugating a ring-level
  composition law of inverse images across the ring-level adjunctions gives, on underlying
  sheaves of sets, the inverse of the geometric composition law of direct images.
* `CategoryTheory.conjugateIsoEquiv_symm_comp_of_rightAdjoint`: the abstract reduction of
  transitivity of conjugate comparisons of left adjoints to that of their right adjoints.

## Implementation notes

Each fibre comparison is the conjugate, across the composite of the ring-level adjunction
`f⁻¹ ⊣ f_*` and the skyscraper adjunction, of the skyscraper comparison
`AlgebraicGeometry.Space.smallEtaleSkyscraperRingIso`.  Conjugation turns vertical composites of
left adjoints into vertical composites of right adjoints, whiskerings into whiskerings, and the
composition law of inverse images into a comparison `(a ≫ b)_* ⟶ a_* ⋙ b_*`, so the statement
reduces to one about skyscrapers.  That one is checked on projections: the skyscraper
comparisons are the ring-level direct-image comparisons of Stacks 03G8 followed by restriction of
the base-change skyscraper comparisons, the direct-image comparisons compose by cartesian
composition (`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_comparison`, seen through the
faithful forgetful functor to sheaves of sets), and the projections of the base-change
skyscraper comparisons are reindexings along the lifts of Stacks 03G2, part (1).

The ring-level comparisons whose types mention two descriptions of the same functor (the
inverse image as `AlgebraicGeometry.Space.smallEtaleInverseImageRing` or as
`MorphismOfTopoi.inverseImageRing`; the direct image of a composite) are passed as variables
with their defining property, so that no equation between the two descriptions is ever
rewritten.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

/-- **Transitivity of conjugate comparisons of left adjoints.**  Let `LA ⊣ RA`, `LB ⊣ RB` and
`LAB ⊣ RAB` be adjunctions with `c : LB ⋙ LA ≅ LAB`, and let `Fw ⊣ Sw`, `Faw ⊣ Saw`,
`Fbaw ⊣ Sbaw` be three further adjunctions.  For isomorphisms `sa : Sw ⋙ RA ≅ Saw`,
`sb : Saw ⋙ RB ≅ Sbaw` and `sab : Sw ⋙ RAB ≅ Sbaw` of right adjoints, write `ea`, `eb`, `eab`
for the conjugate isomorphisms of left adjoints.  If `sab` is `sb ∘ RB(sa)` after the conjugate
`RAB ⟶ RA ⋙ RB` of `c`, then `eab` is `eb`, then `ea`, then `c`. -/
theorem conjugateIsoEquiv_symm_comp_of_rightAdjoint
    {CW : Type u₀} {CY : Type u₁} {CZ : Type u₂} {A : Type u₃}
    [Category.{v₀} CW] [Category.{v₁} CY] [Category.{v₂} CZ] [Category.{v₃} A]
    {LA : CY ⥤ CW} {RA : CW ⥤ CY} {LB : CZ ⥤ CY} {RB : CY ⥤ CZ}
    {LAB : CZ ⥤ CW} {RAB : CW ⥤ CZ}
    {Fw : CW ⥤ A} {Sw : A ⥤ CW} {Faw : CY ⥤ A} {Saw : A ⥤ CY}
    {Fbaw : CZ ⥤ A} {Sbaw : A ⥤ CZ}
    (ra : LA ⊣ RA) (rb : LB ⊣ RB) (rab : LAB ⊣ RAB)
    (pw : Fw ⊣ Sw) (paw : Faw ⊣ Saw) (pbaw : Fbaw ⊣ Sbaw)
    (sa : Sw ⋙ RA ≅ Saw) (sb : Saw ⋙ RB ≅ Sbaw) (sab : Sw ⋙ RAB ≅ Sbaw) (c : LB ⋙ LA ≅ LAB)
    (h : ∀ M : A, (conjugateEquiv rab (rb.comp ra) c.hom).app (Sw.obj M) ≫
        RB.map (sa.hom.app M) ≫ sb.hom.app M = sab.hom.app M)
    (F : CZ) :
    ((conjugateIsoEquiv (rb.comp paw) pbaw).symm sb).hom.app F ≫
        ((conjugateIsoEquiv (ra.comp pw) paw).symm sa).hom.app (LB.obj F) ≫
        Fw.map (c.hom.app F) =
      ((conjugateIsoEquiv (rab.comp pw) pbaw).symm sab).hom.app F := by
  have h2 : Functor.whiskerLeft LB ((conjugateEquiv (ra.comp pw) paw).symm sa.hom) =
      (conjugateEquiv (rb.comp (ra.comp pw)) (rb.comp paw)).symm
        (Functor.whiskerRight sa.hom RB) := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_whiskerLeft, Equiv.apply_symm_apply]
  have h3 : (Functor.associator LB LA Fw).inv =
      (conjugateEquiv ((rb.comp ra).comp pw) (rb.comp (ra.comp pw))).symm
        (Functor.associator Sw RA RB).inv := by
    rw [Equiv.eq_symm_apply]
    apply (cancel_epi (Functor.associator Sw RA RB).hom).1
    rw [← conjugateEquiv_associator_hom rb ra pw, conjugateEquiv_comp, Iso.inv_hom_id,
      conjugateEquiv_id, conjugateEquiv_associator_hom, Iso.hom_inv_id]
  have h4 : Functor.whiskerRight c.hom Fw =
      (conjugateEquiv (rab.comp pw) ((rb.comp ra).comp pw)).symm
        (Functor.whiskerLeft Sw (conjugateEquiv rab (rb.comp ra) c.hom)) := by
    rw [Equiv.eq_symm_apply, conjugateEquiv_whiskerRight]
  have key : (conjugateEquiv (rb.comp paw) pbaw).symm sb.hom ≫
      Functor.whiskerLeft LB ((conjugateEquiv (ra.comp pw) paw).symm sa.hom) ≫
      (Functor.associator LB LA Fw).inv ≫ Functor.whiskerRight c.hom Fw =
      (conjugateEquiv (rab.comp pw) pbaw).symm sab.hom := by
    rw [h2, h3, h4, conjugateEquiv_symm_comp, conjugateEquiv_symm_comp,
      conjugateEquiv_symm_comp]
    congr 1
    ext M
    simpa using h M
  simpa using congrArg (fun t => t.app F) key

end CategoryTheory

namespace MorphismOfTopoi

universe w w' w'' t t' t'' s s' s''

variable {C : Type s} [Category.{t} C] {D : Type s'} [Category.{t'} D]
  {E : Type s''} [Category.{t''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}

/-- **The conjugate of a ring-level composition law of inverse images.**  Let `f`, `g` and `h` be
morphisms of topoi with an isomorphism `ν : (g ∘ f)_* ≅ h_*`, and let `c : g⁻¹ ⋙ f⁻¹ ≅ h⁻¹` be an
isomorphism of inverse images of sheaves of commutative rings which, on underlying sheaves of sets,
is the comparison of left adjoints induced by `ν`.  Then the conjugate `h_* ⟶ f_* ⋙ g_*` of `c`
across the ring-level adjunctions is `ν⁻¹` on underlying sheaves of sets. -/
theorem forget_map_conjugateEquiv_ringAdjunction_comp
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (g : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))
    (h : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf L (Type w'')))
    (ν : (g.comp f).pushforward ≅ h.pushforward)
    (c : g.inverseImageRing ⋙ f.inverseImageRing ≅ h.inverseImageRing)
    (hc : ∀ O : Sheaf L CommRingCat.{w''}, (sheafCompose J (forget CommRingCat.{w})).map
        (c.hom.app O) = (((g.comp f).adj.ofNatIsoRight ν).leftAdjointUniq h.adj).hom.app
          ((sheafCompose L (forget CommRingCat.{w''})).obj O))
    (O : Sheaf J CommRingCat.{w}) :
    (sheafCompose L (forget CommRingCat.{w''})).map
        ((conjugateEquiv h.ringAdjunction (g.ringAdjunction.comp f.ringAdjunction) c.hom).app O) =
      ν.inv.app ((sheafCompose J (forget CommRingCat.{w})).obj O) := by
  have h1 : (conjugateEquiv h.ringAdjunction (g.ringAdjunction.comp f.ringAdjunction)
      c.hom).app O = g.ringAdjunction.homEquiv _ _ (f.ringAdjunction.homEquiv _ _
        (c.hom.app (h.pushforwardRing.obj O) ≫ h.ringAdjunction.counit.app O)) := by
    rw [conjugateEquiv_apply_app, ← Functor.map_comp, ← Adjunction.homEquiv_unit,
      Adjunction.comp_homEquiv_apply]
    rfl
  have hcounit : (sheafCompose J (forget CommRingCat.{w})).map
      (h.ringAdjunction.counit.app O) =
      h.adj.counit.app ((sheafCompose J (forget CommRingCat.{w})).obj O) := by
    refine (congrArg (sheafCompose J (forget CommRingCat.{w})).map
      (Adjunction.homEquiv_symm_id _ _).symm).trans ?_
    refine (ringAdjunction_homEquiv_symm_forget h _ _ _).trans ?_
    refine (congrArg ((h.adj.homEquiv _ _).symm)
      (CategoryTheory.Functor.map_id (sheafCompose L (forget CommRingCat.{w''})) _)).trans ?_
    exact Adjunction.homEquiv_symm_id _ _
  have hset : g.adj.homEquiv _ _ (f.adj.homEquiv _ _
      ((((g.comp f).adj.ofNatIsoRight ν).leftAdjointUniq h.adj).hom.app
          (h.pushforward.obj ((sheafCompose J (forget CommRingCat.{w})).obj O)) ≫
        h.adj.counit.app ((sheafCompose J (forget CommRingCat.{w})).obj O))) =
      ν.inv.app ((sheafCompose J (forget CommRingCat.{w})).obj O) := by
    refine (congrArg (fun t => g.adj.homEquiv _ _ (f.adj.homEquiv _ _ t))
      ((congrArg (fun t => _ ≫ t) (Adjunction.homEquiv_symm_id h.adj _).symm).trans
        (Adjunction.leftAdjointUniq_ofNatIsoRight_hom_app_comp_homEquiv_symm (g.comp f).adj h.adj
          ν (𝟙 _)))).trans ?_
    refine (Adjunction.comp_homEquiv_apply g.adj f.adj _).symm.trans ?_
    exact (((g.comp f).adj.homEquiv _ _).apply_symm_apply _).trans (Category.id_comp _)
  refine (congrArg (sheafCompose L (forget CommRingCat.{w''})).map h1).trans ?_
  refine (ringAdjunction_homEquiv_forget g _ _ _).trans ?_
  refine (congrArg (g.adj.homEquiv _ _)
    ((ringAdjunction_homEquiv_forget f _ _ _).trans
      (congrArg (f.adj.homEquiv _ _)
        (((sheafCompose J (forget CommRingCat.{w})).map_comp _ _).trans
          (congrArg₂ (· ≫ ·) (hc _) hcounit))))).trans ?_
  exact hset

end MorphismOfTopoi

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W Y Z : AlgebraicSpaces B S hS}

/-- The ring-level composition law in inverse-image form is, on underlying sheaves of sets, the
geometric one, at every sheaf of commutative rings. -/
theorem forgetRing_map_compInverseImageRingIso_hom (a : W ⟶ Y) (b : Y ⟶ Z)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) :
    (smallEtaleRingedTopos B S hS W).forgetRing.map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS a b).hom.app G) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS a b).hom.app
        ((smallEtaleRingedTopos B S hS Z).forgetRing.obj G) := by
  refine Eq.trans ((smallEtaleRingedTopos B S hS W).forgetRing.map_comp _ _) ?_
  refine Eq.trans (congrArg₂ (fun a b ↦ a ≫ b)
    (Stacks.Sheaves.ToposPushforward.forget_map_inverseImageCommRingComp_hom
      (smallEtaleRingedToposHom B S hS b).toToposHom
      (smallEtaleRingedToposHom B S hS a).toToposHom G)
    (underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (smallEtaleRingedTopos B S hS W).J G
      (smallEtaleRingedToposHom_compInverseImageIso B S hS a b))) ?_
  exact Category.id_comp _

/-- The cartesian projections of the base change along `a ≫ b` factor through those along `a`
and along `b`, across the composition isomorphism of Stacks 03G2, part (2). -/
theorem spacesBaseChange_comp_inv_projection (a : W ⟶ Y) (b : Y ⟶ Z) (U : SpacesEtale B S hS Z) :
    (SpacesEtale.toSpaces B S hS W).map ((spacesBaseChange_comp B S hS a b).inv.app U) ≫
        (spacesBaseChange B S hS a).projection.app ((spacesBaseChange B S hS b).functor.obj U) ≫
        (spacesBaseChange B S hS b).projection.app U =
      (spacesBaseChange B S hS (a ≫ b)).projection.app U := by
  rw [← spacesBaseChange_comp_projection B S hS a b U, ← Category.assoc]
  refine Eq.trans ?_ (Category.id_comp _)
  congr 1
  exact congrArg (fun k => (SpacesEtale.toSpaces B S hS W).map k)
    ((spacesBaseChange_comp B S hS a b).inv_hom_id_app U) |>.symm.trans
      ((SpacesEtale.toSpaces B S hS W).map_comp _ _) |>.symm.trans
        ((SpacesEtale.toSpaces B S hS W).map_id _)

/-- **Compatibility of the lifts of geometric points with pullback pasting.**  The lift of `w`
into the base change along `a ≫ b` that the cartesian square of Stacks 03G2, part (1) assigns to
a lift `q` of the image point, carried along the composition isomorphism of Stacks 03G2,
part (2), is the lift obtained in two steps: first along `b`, then along `a`. -/
theorem spacesBaseChangeFiberIso_inv_comp (a : W ⟶ Y) (b : Y ⟶ Z) (w : GeometricPoint B S hS W.1)
    (U : SpacesEtale B S hS Z)
    (q : (spacesEtaleSitePoint (geometricPointMap (a ≫ b).hom w)).fiber.obj U) :
    (spacesEtaleSitePoint w).fiber.map ((spacesBaseChange_comp B S hS a b).inv.app U)
        ((spacesBaseChangeFiberIso B S hS (a ≫ b) w).inv.app U q) =
      (spacesBaseChangeFiberIso B S hS a w).inv.app ((spacesBaseChange B S hS b).functor.obj U)
        ((spacesBaseChangeFiberIso B S hS b (geometricPointMap a.hom w)).inv.app U q) := by
  set r := (spacesBaseChangeFiberIso B S hS (a ≫ b) w).inv.app U q with hr
  set t := (spacesEtaleSitePoint w).fiber.map ((spacesBaseChange_comp B S hS a b).inv.app U) r
    with ht
  have hq : (spacesBaseChangeFiberIso B S hS b (geometricPointMap a.hom w)).hom.app U
      ((spacesBaseChangeFiberIso B S hS a w).hom.app ((spacesBaseChange B S hS b).functor.obj U)
        t) = q := by
    have hrq : (spacesBaseChangeFiberIso B S hS (a ≫ b) w).hom.app U r = q :=
      ((spacesBaseChangeFiberIso B S hS (a ≫ b) w).app U).inv_hom_id_apply q
    refine Eq.trans (Subtype.ext ?_) hrq
    exact congrArg (fun k => k.hom.app (Opposite.op w.val.siteObject) r.1)
      (spacesBaseChange_comp_inv_projection B S hS a b U)
  rw [← hq, Iso.hom_inv_id_app_apply]
  exact (((spacesBaseChangeFiberIso B S hS a w).app _).hom_inv_id_apply t).symm

/-- **Cartesian composition for the ring-level direct-image comparisons.**  Let
`γ : (a ≫ b)_* ⟶ a_* ⋙ b_*` be a comparison of direct images of sheaves of commutative rings that
is the inverse of the geometric composition law on underlying sheaves of sets.  Then for a sheaf
of commutative rings `H` on the spaces-étale site of `W`, the comparison of Stacks 03G8 for
`a ≫ b` at `H` is `γ`, followed by the comparisons for `a` and for `b`, followed by the
composition isomorphism of base changes of Stacks 03G2, part (2). -/
theorem pushforwardRing_comp_of_forgetRing (a : W ⟶ Y) (b : Y ⟶ Z)
    (γ : (smallEtaleRingedToposHom B S hS (a ≫ b)).toToposHom.pushforwardRing ⟶
      (smallEtaleRingedToposHom B S hS a).toToposHom.pushforwardRing ⋙
        (smallEtaleRingedToposHom B S hS b).toToposHom.pushforwardRing)
    (hγ : ∀ G : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u},
      (smallEtaleRingedTopos B S hS Z).forgetRing.map (γ.app G) =
        (smallToposMorphismTypeU_comp B S hS a b).inv.app
          ((smallEtaleRingedTopos B S hS W).forgetRing.obj G))
    (H : Sheaf (SpacesEtale.topology B S hS W) CommRingCat.{u}) :
    γ.app (((comparisonFunctor B S hS W).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B S hS W.1) (SpacesEtale.topology B S hS W)).obj H) ≫
        (smallEtaleRingedToposHom B S hS b).toToposHom.pushforwardRing.map
          ((smallEtaleRingedToposHom_pushforwardRing B S hS a).hom.app H) ≫
        (smallEtaleRingedToposHom_pushforwardRing B S hS b).hom.app
          (((spacesBaseChange B S hS a).functor.sheafPushforwardContinuous CommRingCat.{u}
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS W)).obj H) ≫
        ((comparisonFunctor B S hS Z).sheafPushforwardContinuous CommRingCat.{u}
            (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).map
          ((Functor.sheafPushforwardContinuousComp' (spacesBaseChange_comp B S hS a b)
            CommRingCat.{u} (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)
            (SpacesEtale.topology B S hS W)).hom.app H) =
      (smallEtaleRingedToposHom_pushforwardRing B S hS (a ≫ b)).hom.app H := by
  have hset := smallToposMorphismTypeU_comp_comparison B S hS a b
    (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS W) H)
  have hset' := (Iso.inv_comp_eq ((smallToposMorphismTypeU_comp B S hS a b).app
    ((smallEtaleComparisonRestriction B S hS W).obj
      (Stacks.underlyingRingSheaf (SpacesEtale.topology B S hS W) H)))).mpr hset
  refine (smallEtaleRingedTopos B S hS Z).forgetRing.map_injective ?_
  refine ((smallEtaleRingedTopos B S hS Z).forgetRing.map_comp _ _).trans ?_
  refine (congrArg₂ (· ≫ ·) (hγ _) ?_).trans
    ((hset'.trans (smallEtaleRingedToposHom_pushforwardRing_forget B S hS (a ≫ b) H).symm))
  refine ((smallEtaleRingedTopos B S hS Z).forgetRing.map_comp _ _).trans ?_
  refine congrArg₂ (· ≫ ·) ((MorphismOfTopoi.pushforwardRing_map_forget _ _).trans
    (congrArg (smallEtaleRingedToposHom B S hS b).toToposHom.pushforward.map
      (smallEtaleRingedToposHom_pushforwardRing_forget B S hS a H))) ?_
  refine ((smallEtaleRingedTopos B S hS Z).forgetRing.map_comp _ _).trans ?_
  exact congrArg₂ (· ≫ ·) (smallEtaleRingedToposHom_pushforwardRing_forget B S hS b _) rfl

/-- **Transitivity of the base-change skyscraper comparisons.**  On the spaces-étale sites, the
skyscraper comparison of `a ≫ b` at `w` is the direct image along base change by `b` of the
comparison of `a` at `w`, followed by the comparison of `b` at `a ∘ w`, across the composition
isomorphism of base changes of Stacks 03G2, part (2).  On projections this is
`AlgebraicGeometry.Space.spacesBaseChangeFiberIso_inv_comp`. -/
theorem spacesBaseChangeSkyscraperRingIso_comp (a : W ⟶ Y) (b : Y ⟶ Z)
    (w : GeometricPoint B S hS W.1) (M : CommRingCat.{u}) :
    ((spacesBaseChange B S hS b).functor.sheafPushforwardContinuous CommRingCat.{u}
          (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)).map
        ((spacesBaseChangeSkyscraperRingIso B S hS a w).hom.app M) ≫
        (spacesBaseChangeSkyscraperRingIso B S hS b (geometricPointMap a.hom w)).hom.app M =
      (Functor.sheafPushforwardContinuousComp' (spacesBaseChange_comp B S hS a b)
          CommRingCat.{u} (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)
          (SpacesEtale.topology B S hS W)).hom.app
          ((spacesEtaleSitePoint w).skyscraperSheafFunctor.obj M) ≫
        (spacesBaseChangeSkyscraperRingIso B S hS (a ≫ b) w).hom.app M := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => Pi.hom_ext _ _ fun q => ?_))
  obtain ⟨U⟩ := U
  have hc : ((Functor.sheafPushforwardContinuousComp' (spacesBaseChange_comp B S hS a b)
      CommRingCat.{u} (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS W)).hom.app
        ((spacesEtaleSitePoint w).skyscraperSheafFunctor.obj M)).hom.app (op U) =
      ((spacesEtaleSitePoint w).skyscraperPresheaf M).map
        ((spacesBaseChange_comp B S hS a b).inv.app U).op :=
    Category.id_comp _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (spacesBaseChangeSkyscraperRingIso_hom_app_π B S hS b
    (geometricPointMap a.hom w) M U q)).trans ?_
  refine (spacesBaseChangeSkyscraperRingIso_hom_app_π B S hS a w M
    ((spacesBaseChange B S hS b).functor.obj U)
    ((spacesBaseChangeFiberIso B S hS b (geometricPointMap a.hom w)).inv.app U q)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (spacesBaseChangeSkyscraperRingIso_hom_app_π B S hS
    (a ≫ b) w M U q)).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) hc).symm
  exact (congrArg (Pi.π _) (spacesBaseChangeFiberIso_inv_comp B S hS a b w U q)).symm.trans
    (Point.skyscraperPresheaf_map_π (spacesEtaleSitePoint w)
      ((spacesBaseChange_comp B S hS a b).inv.app U) M _).symm

/-- The small étale skyscraper comparison of Stacks 03G8 is the ring-level direct-image comparison
at the spaces-étale skyscraper followed by the restriction of the base-change skyscraper
comparison: four of its six factors are identities. -/
theorem smallEtaleSkyscraperRingIso_hom_app_eq (a : W ⟶ Y) (w : GeometricPoint B S hS W.1)
    (M : CommRingCat.{u}) :
    (smallEtaleSkyscraperRingIso B S hS a w).hom.app M =
      (smallEtaleRingedToposHom_pushforwardRing B S hS a).hom.app
          ((spacesEtaleSitePoint w).skyscraperSheafFunctor.obj M) ≫
        ((comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
            (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
          ((spacesBaseChangeSkyscraperRingIso B S hS a w).hom.app M) := by
  have h0 : (smallEtaleSkyscraperRingIso B S hS a w).hom.app M =
      (smallEtaleRingedToposHom B S hS a).toToposHom.pushforwardRing.map
            (𝟙 (((etaleSitePoint B S hS W.1 w W.2).skyscraperSheafFunctor
              (A := CommRingCat.{u})).obj M)) ≫
          𝟙 _ ≫
          (smallEtaleRingedToposHom_pushforwardRing B S hS a).hom.app
            ((spacesEtaleSitePoint w).skyscraperSheafFunctor.obj M) ≫
          𝟙 _ ≫
          ((comparisonFunctor B S hS Y).sheafPushforwardContinuous CommRingCat.{u}
              (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y)).map
            ((spacesBaseChangeSkyscraperRingIso B S hS a w).hom.app M) ≫ 𝟙 _ := rfl
  rw [h0, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
    Category.id_comp, Category.comp_id]
  rfl

/-- **Transitivity of the skyscraper comparisons of Stacks 03G8.**  For `a : W ⟶ Y`,
`b : Y ⟶ Z` and a geometric point `w` of `W`, the skyscraper comparison of `a ≫ b` at `w` is
the comparison `γ : (a ≫ b)_* ⟶ a_* ⋙ b_*` (any one that is the inverse of the geometric
composition law on underlying sheaves of sets), followed by the direct image along `b` of the
comparison of `a` at `w` and the comparison of `b` at `a ∘ w`. -/
theorem smallEtaleSkyscraperRingIso_comp_of_forgetRing (a : W ⟶ Y) (b : Y ⟶ Z)
    (w : GeometricPoint B S hS W.1)
    (γ : (smallEtaleRingedToposHom B S hS (a ≫ b)).toToposHom.pushforwardRing ⟶
      (smallEtaleRingedToposHom B S hS a).toToposHom.pushforwardRing ⋙
        (smallEtaleRingedToposHom B S hS b).toToposHom.pushforwardRing)
    (hγ : ∀ G : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u},
      (smallEtaleRingedTopos B S hS Z).forgetRing.map (γ.app G) =
        (smallToposMorphismTypeU_comp B S hS a b).inv.app
          ((smallEtaleRingedTopos B S hS W).forgetRing.obj G))
    (M : CommRingCat.{u}) :
    γ.app ((etaleSitePoint B S hS W.1 w W.2).skyscraperSheafFunctor.obj M) ≫
        (smallEtaleRingedToposHom B S hS b).toToposHom.pushforwardRing.map
          ((smallEtaleSkyscraperRingIso B S hS a w).hom.app M) ≫
        (smallEtaleSkyscraperRingIso B S hS b (geometricPointMap a.hom w)).hom.app M =
      (smallEtaleSkyscraperRingIso B S hS (a ≫ b) w).hom.app M := by
  have hD := pushforwardRing_comp_of_forgetRing B S hS a b γ hγ
    ((spacesEtaleSitePoint w).skyscraperSheafFunctor.obj M)
  have hnat := (smallEtaleRingedToposHom_pushforwardRing B S hS b).hom.naturality
    ((spacesBaseChangeSkyscraperRingIso B S hS a w).hom.app M)
  have hE := spacesBaseChangeSkyscraperRingIso_comp B S hS a b w M
  rw [smallEtaleSkyscraperRingIso_hom_app_eq B S hS a w M,
    smallEtaleSkyscraperRingIso_hom_app_eq B S hS b (geometricPointMap a.hom w) M,
    smallEtaleSkyscraperRingIso_hom_app_eq B S hS (a ≫ b) w M, ← hD]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hnat).trans (Category.assoc _ _ _)))).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine (((comparisonFunctor B S hS Z).sheafPushforwardContinuous CommRingCat.{u}
    (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).map_comp _ _).symm.trans ?_
  exact (congrArg ((comparisonFunctor B S hS Z).sheafPushforwardContinuous CommRingCat.{u}
    (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).map hE).trans
      (((comparisonFunctor B S hS Z).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).map_comp _ _)

/-- **The conjugate of the ring-level composition law in inverse-image form.**  Conjugating
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compInverseImageRingIso` across the ring-level
adjunctions gives a comparison `(a ≫ b)_* ⟶ a_* ⋙ b_*` of direct images of sheaves of
commutative rings which, on underlying sheaves of sets, is the inverse of the geometric
composition law `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`. -/
theorem forgetRing_map_conjugateEquiv_compInverseImageRingIso (a : W ⟶ Y) (b : Y ⟶ Z)
    (G : Sheaf (SmallEtale.topology B S hS W.1) CommRingCat.{u}) :
    (smallEtaleRingedTopos B S hS Z).forgetRing.map
        ((conjugateEquiv (smallEtaleRingedToposHom B S hS (a ≫ b)).toToposHom.ringAdjunction
          ((smallEtaleRingedToposHom B S hS b).toToposHom.ringAdjunction.comp
            (smallEtaleRingedToposHom B S hS a).toToposHom.ringAdjunction)
          (smallEtaleRingedToposHom_compInverseImageRingIso B S hS a b).hom).app G) =
      (smallToposMorphismTypeU_comp B S hS a b).inv.app
        ((smallEtaleRingedTopos B S hS W).forgetRing.obj G) :=
  MorphismOfTopoi.forget_map_conjugateEquiv_ringAdjunction_comp
    (smallEtaleRingedToposHom B S hS a).toToposHom (smallEtaleRingedToposHom B S hS b).toToposHom
    (smallEtaleRingedToposHom B S hS (a ≫ b)).toToposHom (smallToposMorphismTypeU_comp B S hS a b)
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS a b)
    (forgetRing_map_compInverseImageRingIso_hom B S hS a b) G

/-- **Transitivity of the fibre comparison of Stacks 04K2, part (4).**  For `a : W ⟶ Y`,
`b : Y ⟶ Z`, a geometric point `w` of `W` and a sheaf of commutative rings `F` on the small
étale site of `Z`, the fibre comparison of `b` at `a ∘ w`, followed by that of `a` at `w` (at
`b⁻¹F`) and by the fibre at `w` of the composition law `b⁻¹ ⋙ a⁻¹ ≅ (a ≫ b)⁻¹` of Stacks 03G8,
is the fibre comparison of `a ≫ b` at `w`.

The image point `b ∘ (a ∘ w)` is `(a ≫ b) ∘ w` by definition, so no transport is needed. -/
theorem smallEtaleInverseImageFiberRingIso_comp (a : W ⟶ Y) (b : Y ⟶ Z)
    (w : GeometricPoint B S hS W.1) (F : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) :
    (smallEtaleInverseImageFiberRingIso B S hS b (geometricPointMap a.hom w)).hom.app F ≫
        (smallEtaleInverseImageFiberRingIso B S hS a w).hom.app
          ((smallEtaleInverseImageRing B S hS b).obj F) ≫
        ((etaleSitePoint B S hS W.1 w W.2).sheafFiber (A := CommRingCat.{u})).map
          ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS a b).hom.app F) =
      (smallEtaleInverseImageFiberRingIso B S hS (a ≫ b) w).hom.app F :=
  conjugateIsoEquiv_symm_comp_of_rightAdjoint
    (smallEtaleRingedToposHom B S hS a).toToposHom.ringAdjunction
    (smallEtaleRingedToposHom B S hS b).toToposHom.ringAdjunction
    (smallEtaleRingedToposHom B S hS (a ≫ b)).toToposHom.ringAdjunction
    (etaleSitePoint B S hS W.1 w W.2).skyscraperSheafAdjunction
    (etaleSitePoint B S hS Y.1 (geometricPointMap a.hom w) Y.2).skyscraperSheafAdjunction
    (etaleSitePoint B S hS Z.1 (geometricPointMap (a ≫ b).hom w) Z.2).skyscraperSheafAdjunction
    (smallEtaleSkyscraperRingIso B S hS a w)
    (smallEtaleSkyscraperRingIso B S hS b (geometricPointMap a.hom w))
    (smallEtaleSkyscraperRingIso B S hS (a ≫ b) w)
    (smallEtaleRingedToposHom_compInverseImageRingIso B S hS a b)
    (smallEtaleSkyscraperRingIso_comp_of_forgetRing B S hS a b w _
      (forgetRing_map_conjugateEquiv_compInverseImageRingIso B S hS a b)) F

end AlgebraicGeometry.Space

end
