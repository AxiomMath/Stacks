module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationSetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDirectedSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedPushforwardStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationStalkIdentifications
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteSectionPullbackTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalkPBCSets

/-!
# Stacks 03Q9 in degree zero for abelian sheaves

Let `f : X ⟶ Y` be quasi-compact and quasi-separated, `s` a geometric point of `Y` and
`p : X ×_Y Spec 𝒪^{sh}_{Y,s} ⟶ X` the projection. This file proves that the canonical map
`(f_*F)_s ⟶ Γ(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹F)` of Stacks 0GIX is an isomorphism for every abelian
sheaf `F` on `X_étale`.

The strict henselization is the limit of a directed system `(V_i)` of affine étale neighbourhoods
of `s` (`AlgebraicGeometry.nbhdConeIsLimit`), and `X ×_Y Spec 𝒪^{sh}_{Y,s}` is the limit of the
quasi-compact quasi-separated `X ×_Y V_i`. Over both limits, global sections of an inverse image
are the colimit of the sections over the stages: this is Stacks 09YQ in degree zero, proved for
sheaves of sets in `Stacks.EtaleCohomology.EtaleLimitSections.limitSections_colimit` and
transported here to abelian sheaves (`Stacks.EtaleCohomology.LimitExt.limitSectionsAb_colimit`)
through the comparison of the inverse images of abelian sheaves and of sheaves of sets with the
one built from the Kan extension. On germs at the `V_i` the map is restriction of sections
(`AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber`), and every
germ at `s` is a germ at some `V_i`, since the stalk is the group of sections over the strict
henselization (`AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id`), which is again such a
colimit.

## Main results

* `Stacks.EtaleCohomology.LimitExt.limitSectionsAb_colimit`.
* `Stacks.EtaleCohomology.LimitExt.isIso_pushforwardStalkToStrictHenselizationSectionsAb_app`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance high]
  Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

section Transfer

variable {S' T : Scheme.{u}} (q : T ⟶ S') (M : Sheaf S'.smallEtaleTopology Ab.{u + 1})

/-- **The unit of inverse image of abelian sheaves, read on sheaves of sets.** On sections over
an étale object `W`, the unit of the inverse-image adjunction for abelian sheaves and the unit of
the inverse-image adjunction for sheaves of sets, at the underlying sheaf of sets, agree after the
comparisons of both inverse images with the inverse image built from the Kan extension. -/
theorem sheafPullbackIso_unit_apply (W : S'.Etale) (x : M.obj.obj (op W)) :
    ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange q) Ab.{u + 1}
        S'.smallEtaleTopology T.smallEtaleTopology).hom.app M).hom.app
          (op ((smallEtaleBaseChange q).obj W))
      (((smallEtaleAdjunctionAb q).unit.app M).hom.app (op W) x) =
    ((coefficientPullbackTwoSquare (smallEtaleBaseChange q) S'.smallEtaleTopology
        T.smallEtaleTopology (forget Ab.{u + 1})).natTrans.app M).hom.app
          (op ((smallEtaleBaseChange q).obj W))
      (((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app
        ((sheafCompose S'.smallEtaleTopology (forget Ab.{u + 1})).obj M)).hom.app (op W) x) := by
  have h1 := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op W))
    (Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleAdjunctionAb q)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange q)
        Ab.{u + 1} S'.smallEtaleTopology T.smallEtaleTopology) M)) x
  have h2 := congrFun (congrArg (fun φ => φ.hom.app (op W))
    (Stacks.Sites.coefficientPullbackTwoSquare_unit (smallEtaleBaseChange q)
      S'.smallEtaleTopology T.smallEtaleTopology (forget Ab.{u + 1}) M)) x
  exact h1.trans h2.symm

/-- The restricted units agree after the two comparisons, at the final object of `T`. -/
theorem sheafPullbackIso_restrictedUnit_apply (W : S'.Etale) (r : T ⟶ W.left)
    (hr : r ≫ W.hom = q) (x : M.obj.obj (op W)) :
    ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange q) Ab.{u + 1}
        S'.smallEtaleTopology T.smallEtaleTopology).hom.app M).hom.app
          (op (Scheme.Etale.mk (𝟙 T)))
      (((smallEtalePullbackAb q).obj M).obj.map (smallEtaleBaseChangeLift q W r hr).op
        (((smallEtaleAdjunctionAb q).unit.app M).hom.app (op W) x)) =
    ((coefficientPullbackTwoSquare (smallEtaleBaseChange q) S'.smallEtaleTopology
        T.smallEtaleTopology (forget Ab.{u + 1})).natTrans.app M).hom.app
          (op (Scheme.Etale.mk (𝟙 T)))
      (((smallEtaleInverseImage.{u, 0} q).obj
          ((sheafCompose S'.smallEtaleTopology (forget Ab.{u + 1})).obj M)).obj.map
          (smallEtaleBaseChangeLift q W r hr).op
        (((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app
          ((sheafCompose S'.smallEtaleTopology (forget Ab.{u + 1})).obj M)).hom.app (op W) x)) := by
  have n1 := ConcreteCategory.congr_hom
    (((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange q) Ab.{u + 1}
        S'.smallEtaleTopology T.smallEtaleTopology).hom.app M).hom.naturality
      (smallEtaleBaseChangeLift q W r hr).op)
    (((smallEtaleAdjunctionAb q).unit.app M).hom.app (op W) x)
  have n2 := congrArg (fun φ => φ (((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app
          ((sheafCompose S'.smallEtaleTopology (forget Ab.{u + 1})).obj M)).hom.app (op W) x))
    (((coefficientPullbackTwoSquare (smallEtaleBaseChange q) S'.smallEtaleTopology
        T.smallEtaleTopology (forget Ab.{u + 1})).natTrans.app M).hom.naturality
      (smallEtaleBaseChangeLift q W r hr).op)
  exact n1.trans ((congrArg (ConcreteCategory.hom
    (((Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange q) Ab.{u + 1}
      S'.smallEtaleTopology T.smallEtaleTopology).obj M).obj.map
        (smallEtaleBaseChangeLift q W r hr).op))
      (sheafPullbackIso_unit_apply q M W x)).trans n2.symm)

end Transfer

section Limit

open Stacks.EtaleCohomology.EtaleLimitSections

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  {S' : Scheme.{u}} (W : Iᵒᵖ ⥤ S'.Etale)
  (c : Cone (W ⋙ Scheme.Etale.forget S' ⋙ Over.forget S')) {q : c.pt ⟶ S'}
  (hq : ∀ i, c.π.app i ≫ (W.obj i).hom = q) (M : Sheaf S'.smallEtaleTopology Ab.{u + 1})

/-- **Restriction of a section of an abelian sheaf over a stage to the limit**: the unit of the
inverse image along `q : T ⟶ S'` over `W_i`, restricted along the morphism from `T` to
`W_i ×_{S'} T` given by the projection `T ⟶ W_i`. The abelian counterpart of
`Stacks.EtaleCohomology.EtaleLimitSections.limitSections`. -/
def limitSectionsAb (i : Iᵒᵖ) :
    M.obj.obj (op (W.obj i)) ⟶
      ((smallEtalePullbackAb q).obj M).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))) :=
  ((smallEtaleAdjunctionAb q).unit.app M).hom.app (op (W.obj i)) ≫
    ((smallEtalePullbackAb q).obj M).obj.map
      (smallEtaleBaseChangeLift q (W.obj i) (c.π.app i) (hq i)).op

omit [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I] in
/-- Restriction to the limit, read as a global section, is `smallEtaleSectionsPullbackAb`. -/
theorem smallEtaleSectionsPullbackAb_app_eq_limitSectionsAb (i : Iᵒᵖ) :
    (smallEtaleSectionsPullbackAb q (W.obj i) (c.π.app i) (hq i)).app M =
      limitSectionsAb W c hq M i ≫
        (Sheaf.ΓNatIsoSheafSections c.pt.smallEtaleTopology Ab.{u + 1}
          (isTerminalEtaleMkId c.pt)).inv.app ((smallEtalePullbackAb q).obj M) :=
  rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I] in
/-- Restriction to the limit is compatible with the transition maps of the system. -/
theorem limitSectionsAb_transition {i j : I} (d : i ≤ j) :
    M.obj.map (W.map (homOfLE d).op).op ≫ limitSectionsAb W c hq M (op j) =
      limitSectionsAb W c hq M (op i) := by
  have hn := ((smallEtaleAdjunctionAb q).unit.app M).hom.naturality (W.map (homOfLE d).op).op
  have hl : smallEtaleBaseChangeLift q (W.obj (op j)) (c.π.app (op j)) (hq _) ≫
      (smallEtaleBaseChange q).map (W.map (homOfLE d).op) =
      smallEtaleBaseChangeLift q (W.obj (op i)) (c.π.app (op i)) (hq _) := by
    apply smallEtaleBaseChange_hom_ext
    refine (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (smallEtaleBaseChange_map_left_fst _ _)).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    refine ((congrArg (· ≫ _) (pullback.lift_fst _ _ _)).trans ?_).trans
      (pullback.lift_fst _ _ _).symm
    exact c.w (homOfLE d).op
  have hm := congrArg (fun m => ((smallEtalePullbackAb q).obj M).obj.map (Quiver.Hom.op m)) hl
  simp only [op_comp, Functor.map_comp] at hm
  rw [limitSectionsAb, limitSectionsAb]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hm)))

omit [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I] in
/-- The abelian restriction to the limit agrees with the restriction of sheaves of sets, after
the comparisons of the inverse images with the one built from the Kan extension. -/
theorem sheafPullbackIso_limitSectionsAb_apply (i : Iᵒᵖ) (x : M.obj.obj (op (W.obj i))) :
    ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange q) Ab.{u + 1}
        S'.smallEtaleTopology c.pt.smallEtaleTopology).hom.app M).hom.app
          (op (Scheme.Etale.mk (𝟙 c.pt))) (limitSectionsAb W c hq M i x) =
    ((coefficientPullbackTwoSquare (smallEtaleBaseChange q) S'.smallEtaleTopology
        c.pt.smallEtaleTopology (forget Ab.{u + 1})).natTrans.app M).hom.app
          (op (Scheme.Etale.mk (𝟙 c.pt)))
      (limitSections W c hq ((sheafCompose S'.smallEtaleTopology (forget Ab.{u + 1})).obj M) i x) :=
  sheafPullbackIso_restrictedUnit_apply q M (W.obj i) (c.π.app i) (hq i) x

/-- **Stacks 09YQ in degree zero, for abelian sheaves and étale neighbourhoods.** For an inverse
system `(W_i)` of étale `S'`-schemes over a directed set with a least element, with affine
transition morphisms and `W_⊥` quasi-compact and quasi-separated, with limit `T`: every section of
`q⁻¹M` over `T` is the restriction of a section over some `W_i`, a section over `W_i` restricting
to zero vanishes on some `W_j`, and restriction is compatible with the transition maps. -/
theorem limitSectionsAb_colimit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (W.map a).left]
    (hc : IsLimit c) [CompactSpace (W.obj (op ⊥)).left] [QuasiSeparatedSpace (W.obj (op ⊥)).left] :
    (∀ t : ((smallEtalePullbackAb q).obj M).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))),
        ∃ (i : I) (x : M.obj.obj (op (W.obj (op i)))), limitSectionsAb W c hq M (op i) x = t) ∧
      (∀ (i : I) (x : M.obj.obj (op (W.obj (op i)))), limitSectionsAb W c hq M (op i) x = 0 →
        ∃ (j : I) (d : i ≤ j), M.obj.map (W.map (homOfLE d).op).op x = 0) ∧
      (∀ (i j : I) (d : i ≤ j) (x : M.obj.obj (op (W.obj (op i)))),
        limitSectionsAb W c hq M (op i) x =
          limitSectionsAb W c hq M (op j) (M.obj.map (W.map (homOfLE d).op).op x)) := by
  obtain ⟨hls, hli⟩ := limitSections_colimit W c hc hq
    ((sheafCompose S'.smallEtaleTopology (forget Ab.{u + 1})).obj M)
  let a := ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange q) Ab.{u + 1}
    S'.smallEtaleTopology c.pt.smallEtaleTopology).hom.app M).hom.app
      (op (Scheme.Etale.mk (𝟙 c.pt)))
  let b := ((coefficientPullbackTwoSquare (smallEtaleBaseChange q) S'.smallEtaleTopology
    c.pt.smallEtaleTopology (forget Ab.{u + 1})).natTrans.app M).hom.app
      (op (Scheme.Etale.mk (𝟙 c.pt)))
  have ha : Function.Bijective a := ConcreteCategory.bijective_of_isIso a
  have hb : Function.Bijective b := by
    have := isIso_coefficientPullbackTwoSquare (smallEtaleBaseChange q) S'.smallEtaleTopology
      c.pt.smallEtaleTopology (forget Ab.{u + 1})
    have : IsIso ((coefficientPullbackTwoSquare (smallEtaleBaseChange q) S'.smallEtaleTopology
        c.pt.smallEtaleTopology (forget Ab.{u + 1})).natTrans.app M) :=
      NatIso.isIso_app_of_isIso _ _
    rw [← isIso_iff_bijective]
    infer_instance
  have key := sheafPullbackIso_limitSectionsAb_apply W c hq M
  refine ⟨fun t => ?_, fun i x hx => ?_, fun i j d x =>
    (ConcreteCategory.congr_hom (limitSectionsAb_transition W c hq M d) x).symm⟩
  · obtain ⟨v, hv⟩ := hb.2 (a t)
    obtain ⟨i, x, rfl⟩ := hls v
    exact ⟨i, x, ha.1 ((key (op i) x).trans hv)⟩
  · have h0 : limitSectionsAb W c hq M (op i) x = limitSectionsAb W c hq M (op i) 0 := by
      rw [hx, map_zero]
    have h1 := (key (op i) x).symm.trans ((congrArg a h0).trans (key (op i) 0))
    obtain ⟨j, d, hd⟩ := hli i x
      (show ((sheafCompose S'.smallEtaleTopology (forget Ab.{u + 1})).obj M).obj.obj
        (op (W.obj (op i))) from (0 : M.obj.obj (op (W.obj (op i))))) (hb.1 h1)
    exact ⟨j, d, hd.trans (map_zero (M.obj.map (W.map (homOfLE d).op).op).hom)⟩

end Limit

section DegreeZero

open Stacks.EtaleCohomology.EtaleLimitSections

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hY : B.Contains Y) (f : X ⟶ Y)
  (s : GeometricPoint Y)

/-- Each member of the directed system of affine étale neighbourhoods of `s` carries a lift of
`s` for which the morphism from the strict henselization is the leg of the limit cone. -/
theorem exists_strictHenselizationNeighborhoodLift_eq_nbhdCone {α : Type u} [PartialOrder α]
    [IsDirected α (· ≤ ·)] (G : α ⥤ (etaleNeighborhoodAffineIndex B Y hY s)ᵒᵖ) [G.Final] (a₀ : α)
    (i : (nbhdIndex a₀)ᵒᵖ) :
    ∃ w : (Scheme.pointSmallEtale s.hom).fiber.obj ((nbhdSystem B Y hY s G a₀).obj i),
      strictHenselizationNeighborhoodLift B Y hY s ((nbhdSystem B Y hY s G a₀).obj i) w =
        (nbhdCone B Y hY s G a₀).π.app i := by
  let e := (etaleNeighborhoodAffineInclusion B Y hY s).obj ((nbhdIndexFunctor B Y hY s G a₀).obj i)
  exact ⟨Over.homMk e.2.1 e.2.2,
    (strictHenselizationNeighborhoodLift_eq B Y hY s ((nbhdSystem B Y hY s G a₀).obj i)
      (Over.homMk e.2.1 e.2.2) ((nbhdCone B Y hY s G a₀).π.app i)
      (nbhdCone_π_comp_hom B Y hY s G a₀ i)
      (geometricPointToStrictHenselization_comp_strictHenselizationAffineCone_π_app B Y hY s
        ((nbhdIndexFunctor B Y hY s G a₀).obj i))).symm⟩

/-- **Stacks 03Q9 in degree zero, for abelian sheaves.** For `f : X ⟶ Y` quasi-compact and
quasi-separated, `s` a geometric point of `Y` and `p : X ×_Y Spec 𝒪^{sh}_{Y,s} ⟶ X` the
projection, the canonical map `(f_*F)_s ⟶ Γ(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹F)` is an isomorphism for
every abelian sheaf `F` on `X_étale`.

The strict henselization is the limit of a directed system `(V_i)` of affine étale neighbourhoods
of `s`, and `X ×_Y Spec 𝒪^{sh}_{Y,s}` the limit of the quasi-compact quasi-separated `X ×_Y V_i`.
Global sections over both limits are the colimits of the sections over the stages
(`Stacks.EtaleCohomology.LimitExt.limitSectionsAb_colimit`); on germs at the `V_i` the map is
restriction (`AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber`),
and every germ is a germ at some `V_i` because the stalk is the sections over the strict
henselization (`AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id`). -/
theorem isIso_pushforwardStalkToStrictHenselizationSectionsAb_app [QuasiCompact f]
    [QuasiSeparated f] (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    IsIso ((pushforwardStalkToStrictHenselizationSectionsAb B hY f s).app F) := by
  obtain ⟨α, _, _, ⟨a₀⟩, G, _⟩ := exists_directed_nbhd B Y hY s
  let W := nbhdSystem B Y hY s G a₀
  let c := nbhdCone B Y hY s G a₀
  have hc : IsLimit c := nbhdConeIsLimit B Y hY s G a₀
  let π := strictHenselizationToBase B Y hY s
  have hπ : ∀ i, c.π.app i ≫ (W.obj i).hom = π := nbhdCone_π_comp_hom B Y hY s G a₀
  have hπ1 : ∀ i, c.π.app i ≫ (W.obj i).hom = 𝟙 _ ≫ π := fun i =>
    (hπ i).trans (Category.id_comp _).symm
  choose w hw using exists_strictHenselizationNeighborhoodLift_eq_nbhdCone B hY s G a₀
  have : ∀ {i j : (nbhdIndex a₀)ᵒᵖ} (a : i ⟶ j), IsAffineHom (W.map a).left := fun {i j} a =>
    @isAffineHom_of_isAffine _ _ (W.map a).left (inferInstanceAs (IsAffine (W.obj i).left))
      (inferInstanceAs (IsAffine (W.obj j).left))
  have : ∀ {i j : (nbhdIndex a₀)ᵒᵖ} (a : i ⟶ j), IsAffineHom ((baseChangeSystem W f).map a).left :=
    fun a => MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_smallEtaleBaseChange_map_left f (W.map a)) inferInstance
  have hcpt : CompactSpace (W.obj (op ⊥)).left := inferInstance
  have hqs : QuasiSeparatedSpace (W.obj (op ⊥)).left := inferInstance
  have : CompactSpace ((baseChangeSystem W f).obj (op ⊥)).left := by
    show CompactSpace ↥(Limits.pullback (W.obj (op ⊥)).hom f)
    exact @AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatPullbackSchemeOfQuasiCompact_1
      _ _ _ (W.obj (op ⊥)).hom f _ hcpt
  have : QuasiSeparatedSpace ((baseChangeSystem W f).obj (op ⊥)).left := by
    show QuasiSeparatedSpace ↥(Limits.pullback (W.obj (op ⊥)).hom f)
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.fst (W.obj (op ⊥)).hom f) hqs _
  let Fp := (smallEtalePushforwardAb f).obj F
  obtain ⟨hAs, -, hAt⟩ := limitSectionsAb_colimit W c hπ1 Fp hc
  obtain ⟨hBs, hBi, -⟩ := limitSectionsAb_colimit (baseChangeSystem W f) (baseChangeCone W c hπ f)
    (baseChangeCone_π_comp_hom W c hπ f) F (baseChangeConeIsLimit W c hπ f hc)
  let ΓA := (Sheaf.ΓNatIsoSheafSections (strictHenselization B Y hY s).smallEtaleTopology
    Ab.{u + 1} (isTerminalEtaleMkId _)).app ((smallEtalePullbackAb (𝟙 _ ≫ π)).obj Fp)
  let ΓB := (Sheaf.ΓNatIsoSheafSections (strictHenselizationBaseChange B hY f s).smallEtaleTopology
    Ab.{u + 1} (isTerminalEtaleMkId _)).app
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hY f s)).obj F)
  have := isIso_etaleStalkToSectionsAb_id B Y hY s
  let E := (etaleStalkToSectionsAb B Y hY s (𝟙 (strictHenselization B Y hY s))).app Fp
  have hE : Function.Bijective E := ConcreteCategory.bijective_of_isIso E
  let φ := (pushforwardStalkToStrictHenselizationSectionsAb B hY f s).app F
  have gA : ∀ i (x : Fp.obj.obj (op (W.obj i))),
      E ((Scheme.pointSmallEtale s.hom).toPresheafFiber (W.obj i) (w i) Fp.obj x) =
        ΓA.inv (limitSectionsAb W c hπ1 Fp i x) := by
    intro i x
    refine (ConcreteCategory.congr_hom
      (etaleStalkToSectionsAb_toPresheafFiber B Y hY s (𝟙 _) Fp (W.obj i) (w i)) x).trans ?_
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (smallEtaleSectionsPullbackAb_congr
      (𝟙 _ ≫ π) (W.obj i) (𝟙 _ ≫ strictHenselizationNeighborhoodLift B Y hY s (W.obj i) (w i))
      (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp]) (hπ1 i)
      ((Category.id_comp _).trans (hw i))) Fp) x
  have hlift : ∀ i, strictHenselizationBaseChangeEtaleLift B hY f s (W.obj i) (w i) =
      (baseChangeCone W c hπ f).π.app i := by
    intro i
    apply pullback.hom_ext
    · refine (pullback.lift_fst _ _ _).trans ?_
      refine Eq.trans ?_ (baseChangeLeg_fst W c hπ f i).symm
      rw [hw i]
      rfl
    · exact (pullback.lift_snd _ _ _).trans (baseChangeLeg_snd W c hπ f i).symm
  have gB : ∀ i (x : F.obj.obj (op ((baseChangeSystem W f).obj i))),
      φ ((Scheme.pointSmallEtale s.hom).toPresheafFiber (W.obj i) (w i) Fp.obj x) =
        ΓB.inv (limitSectionsAb (baseChangeSystem W f) (baseChangeCone W c hπ f)
          (baseChangeCone_π_comp_hom W c hπ f) F i x) := by
    intro i x
    refine (ConcreteCategory.congr_hom
      (pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber B hY f s (W.obj i) (w i) F)
        x).trans ?_
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (smallEtaleSectionsPullbackAb_congr
      (strictHenselizationBaseChangeToSource B hY f s) ((baseChangeSystem W f).obj i)
      (strictHenselizationBaseChangeEtaleLift B hY f s (W.obj i) (w i))
      (pullback.lift_snd _ _ _) (baseChangeCone_π_comp_hom W c hπ f i) (hlift i)) F) x
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero φ.hom).2 fun g hg => ?_, fun t => ?_⟩
  · obtain ⟨i, y, hy⟩ := hAs (ΓA.hom (E g))
    have hg' : E ((Scheme.pointSmallEtale s.hom).toPresheafFiber (W.obj (op i)) (w (op i)) Fp.obj y)
        = E g :=
      (gA (op i) y).trans ((congrArg ΓA.inv.hom hy).trans (ΓA.hom_inv_id_apply (E g)))
    obtain rfl := (hE.1 hg').symm
    have h0 := congrArg ΓB.hom.hom ((gB (op i) y).symm.trans hg)
    have hy0 : limitSectionsAb (baseChangeSystem W f) (baseChangeCone W c hπ f)
        (baseChangeCone_π_comp_hom W c hπ f) F (op i) y = 0 :=
      (ΓB.inv_hom_id_apply _).symm.trans (h0.trans (map_zero ΓB.hom.hom))
    obtain ⟨j, d, hd⟩ := hBi i y hy0
    have hd' : Fp.obj.map (W.map (homOfLE d).op).op y = 0 := hd
    have hl : limitSectionsAb W c hπ1 Fp (op i) y = 0 :=
      (hAt i j d y).trans ((congrArg (limitSectionsAb W c hπ1 Fp (op j)).hom hd').trans
        (map_zero _))
    exact hE.1 ((gA (op i) y).trans ((congrArg ΓA.inv.hom hl).trans
      ((map_zero ΓA.inv.hom).trans (map_zero E.hom).symm)))
  · obtain ⟨i, x, hx⟩ := hBs (ΓB.hom t)
    exact ⟨(Scheme.pointSmallEtale s.hom).toPresheafFiber (W.obj (op i)) (w (op i)) Fp.obj x,
      (gB (op i) x).trans ((congrArg ΓB.inv.hom hx).trans (ΓB.hom_inv_id_apply t))⟩

end DegreeZero

end Stacks.EtaleCohomology.LimitExt
