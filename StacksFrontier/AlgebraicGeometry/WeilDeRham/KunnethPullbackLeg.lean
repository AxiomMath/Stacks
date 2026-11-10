module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethCupWithClassCanonical

/-!
# The pullback leg of the Künneth map is pullback of cohomology classes

Let `a : X ⟶ S` and `p : W ⟶ X` be morphisms of ringed spaces. The global Künneth map of
[Stacks, Tag 0G7V] pulls a class of `Hⁿ(X, K)` back to `W` along its *pullback leg*
`Ra_*K ⟶ R(p ≫ a)_*Lp^*K`, the adjoint of the counit leg
`L(p ≫ a)^*Ra_*K ⟶ Lp^*K` (`Stacks.Cohomology.KunnethCupWithClass.pullbackLeg`), read through
the Leray identifications of [Stacks, Tag 0D5W] over `S`. This file proves that this is the
pullback of cohomology classes along `p`, `Stacks.Cohomology.HomologyPullback.homologyPullback`:
the derived unit `K ⟶ Rp_*Lp^*K` followed by the Leray identification over `X`.

## Main results

* `Stacks.WeilDeRham.pullbackLeg_eq_map_unit`: the pullback leg is `Ra_*` of the derived unit of
  `Lp^* ⊣ Rp_*`, followed by the composition isomorphism `Ra_*Rp_* ≅ R(p ≫ a)_*`.
* `Stacks.WeilDeRham.lerayCohomologyIso_pullbackLeg`: **on cohomology the pullback leg, read
  through the Leray identifications, is `homologyPullback`.**

## References

* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u


namespace Stacks.WeilDeRham

variable {S X W : RingedSpace.{u, u}} (a : X ⟶ S) (p : W ⟶ X)

section Generic

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- The transpose along a second right adjoint is the transpose along the first, followed by the
uniqueness isomorphism of right adjoints. -/
theorem homEquiv_eq_homEquiv_comp_rightAdjointUniq {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F ⊣ G') (x : C) (y : D) (g : F.obj x ⟶ y) :
    adj2.homEquiv x y g =
      adj1.homEquiv x y g ≫ (Adjunction.rightAdjointUniq adj1 adj2).hom.app y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    ← Adjunction.unit_rightAdjointUniq_hom_app adj1 adj2, Category.assoc, Category.assoc,
    ← NatTrans.naturality]

/-- **The transpose of a counit leg along a composite adjunction.** For adjunctions
`La ⊣ Ra` and `Lp ⊣ Rp`, an isomorphism `e : La ⋙ Lp ≅ L`, and `g : L(Ra k) ⟶ Lp k` with
`e ≫ g = Lp(εₐ)`, the transpose of `g` along the composite adjunction is `Ra(ηₚ)`. -/
theorem homEquiv_ofNatIsoLeft_comp {La : C ⥤ D} {Ra : D ⥤ C} {Lp : D ⥤ E} {Rp : E ⥤ D}
    {L : C ⥤ E} (adja : La ⊣ Ra) (adjp : Lp ⊣ Rp) (e : La ⋙ Lp ≅ L) (k : D)
    (g : L.obj (Ra.obj k) ⟶ Lp.obj k) (hg : e.hom.app (Ra.obj k) ≫ g = Lp.map (adja.counit.app k)) :
    ((adja.comp adjp).ofNatIsoLeft e).homEquiv _ _ g = Ra.map (adjp.unit.app k) := by
  rw [Adjunction.homEquiv_unit]
  change ((adja.comp adjp).unit.app _ ≫ Ra.map (Rp.map (e.hom.app _))) ≫ Ra.map (Rp.map g) = _
  rw [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, hg, Adjunction.comp_unit_app, Category.assoc,
    ← Functor.map_comp, adjp.unit_naturality, Functor.map_comp, ← Category.assoc,
    Adjunction.right_triangle_components]
  exact Category.id_comp _

end Generic

/-- **The pullback leg is `Ra_*` of the derived unit**, followed by the composition isomorphism
`Ra_*Rp_* ≅ R(p ≫ a)_*`. The pullback leg is the transpose under `L(p ≫ a)^* ⊣ R(p ≫ a)_*` of the
counit leg; the composition isomorphism is the uniqueness isomorphism between `R(p ≫ a)_*` and
`Ra_*Rp_*` as right adjoints of `L(p ≫ a)^*`, so the statement is the triangle identity of
`La^* ⊣ Ra_*` and the naturality of the unit of `Lp^* ⊣ Rp_*`. -/
theorem pullbackLeg_eq_map_unit
    (K : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    Stacks.Cohomology.KunnethCupWithClass.pullbackLeg a p (p ≫ a) rfl K =
      (derivedPushforward a).map ((derivedAdjunction p).unit.app K) ≫
        (derivedPushforwardCompIso p a).hom.app ((derivedPullback p).obj K) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have hg : (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).hom.app
        ((derivedPushforward a).obj K) ≫
      (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p (p ≫ a) rfl).app K =
      (derivedPullback p).map ((derivedAdjunction a).counit.app K) := by
    simp only [Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg,
      Stacks.Cohomology.DerivedKunneth.pullbackCounitLegComp, eqToHom_refl, NatTrans.comp_app,
      Category.id_comp, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app]
    exact
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).hom_inv_id_app_assoc
        ((derivedPushforward a).obj K) _).trans (Category.comp_id _)
  rw [Stacks.Cohomology.KunnethCupWithClass.pullbackLeg, derivedPushforwardCompIso,
    homEquiv_eq_homEquiv_comp_rightAdjointUniq
      (((derivedAdjunction a).comp (derivedAdjunction p)).ofNatIsoLeft
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a)),
    homEquiv_ofNatIsoLeft_comp _ _ _ _ _ hg]

/-- **On cohomology the pullback leg, read through the Leray identifications over `S`, is the
pullback of classes along `p`**: for `x ∈ Hⁿ(X, K)`, read as a class of `Hⁿ(S, Ra_*K)`, its image
under the pullback leg, read back on `W`, is `homologyPullback p K n x`. -/
theorem lerayCohomologyIso_pullbackLeg
    (K : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ)
    (x : letI := @HasDerivedCategory.standard.{u, u + 1}; cohomologyModule K n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (lerayCohomologyIso (p ≫ a) ((derivedPullback p).obj K) n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections S).map
          (Stacks.Cohomology.KunnethCupWithClass.pullbackLeg a p (p ≫ a) rfl K))).hom
          ((lerayCohomologyIso a K n).inv x)) =
      Stacks.Cohomology.HomologyPullback.homologyPullback p K n x := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have hleg : Stacks.Cohomology.KunnethCupWithClass.pullbackLeg a p (p ≫ a) rfl K ≫
      (derivedPushforwardCompIso p a).inv.app ((derivedPullback p).obj K) =
      (derivedPushforward a).map ((derivedAdjunction p).unit.app K) := by
    rw [pullbackLeg_eq_map_unit, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have h₁ := Stacks.Cohomology.LerayComposite.lerayCohomologyIso_comp p a
    ((derivedPullback p).obj K) n
    (((DerivedCategory.homologyFunctor _ n).map ((baseSections S).map
      (Stacks.Cohomology.KunnethCupWithClass.pullbackLeg a p (p ≫ a) rfl K))).hom
      ((lerayCohomologyIso a K n).inv x))
  have h₂ := (Stacks.Cohomology.HomologyPullback.map_map_comp_apply (baseSections S)
    (DerivedCategory.homologyFunctor _ n)
    (Stacks.Cohomology.KunnethCupWithClass.pullbackLeg a p (p ≫ a) rfl K)
    ((derivedPushforwardCompIso p a).inv.app ((derivedPullback p).obj K))
    ((lerayCohomologyIso a K n).inv x)).symm.trans
    (congrArg (fun t => ((DerivedCategory.homologyFunctor _ n).map ((baseSections S).map t)).hom
      ((lerayCohomologyIso a K n).inv x)) hleg)
  have h₃ := lerayCohomologyIso_naturality_apply a ((derivedAdjunction p).unit.app K) n
    ((lerayCohomologyIso a K n).inv x)
  have h₄ := congrArg (fun t => ((DerivedCategory.homologyFunctor _ n).map
    ((baseSections X).map ((derivedAdjunction p).unit.app K))).hom t)
    ((lerayCohomologyIso a K n).inv_hom_id_apply x)
  refine h₁.symm.trans ((congrArg (fun t => (lerayCohomologyIso p ((derivedPullback p).obj K) n).hom
    ((lerayCohomologyIso a ((derivedPushforward p).obj ((derivedPullback p).obj K)) n).hom t))
    h₂).trans ((congrArg (fun t => (lerayCohomologyIso p ((derivedPullback p).obj K) n).hom t)
    (h₃.trans h₄)).trans ?_))
  rfl

/-- `lerayCohomologyIso_pullbackLeg` for a factorization `p ≫ a = f` given as a hypothesis. -/
theorem lerayCohomologyIso_pullbackLeg_of_eq (f : W ⟶ S) (hp : p ≫ a = f)
    (K : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ)
    (x : letI := @HasDerivedCategory.standard.{u, u + 1}; cohomologyModule K n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (lerayCohomologyIso f ((derivedPullback p).obj K) n).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections S).map
          (Stacks.Cohomology.KunnethCupWithClass.pullbackLeg a p f hp K))).hom
          ((lerayCohomologyIso a K n).inv x)) =
      Stacks.Cohomology.HomologyPullback.homologyPullback p K n x := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  subst hp
  exact lerayCohomologyIso_pullbackLeg a p K n x

end Stacks.WeilDeRham

end
