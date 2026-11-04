module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.ProObject.FiniteLevel

/-!
# The pro-object of a completed crystalline thickening

For a completed thickening `B` of the affine crystalline site, the inverse system of its
finite-level crystalline quotients `B/(p)^e` defines a pro-object of the little crystalline
category `Cris(C/A)`, implemented as an ind-object of the opposite category. This file
constructs that pro-object (`Crystalline.proObject`), the map of pro-objects induced by a
morphism of completed thickenings (`Crystalline.proMap`) together with its functoriality, the
comparison of the chosen presenting colimit with Mathlib's, and the description of an arbitrary
map of pro-objects by morphisms between finite levels.

## References

* [Stacks Project, Tag 07KH](https://stacks.math.columbia.edu/tag/07KH)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Crystalline

section ProObject

open Limits Opposite

/-- The pro-objects of the ordinary affine crystalline category, using Mathlib's
ind-object category of its opposite. -/
public abbrev ProCrystallineThickening
    (S : AffineCrystallineSituation.{u, v}) :=
  (ObjectProperty.FullSubcategory
    (IsIndObject (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)))ᵒᵖ

namespace FiniteLevelSystem

variable {S : AffineCrystallineSituation.{u, v}}
variable {X :
  CompletedCrystallineThickening.{u, v, w} S}

/-- The inverse diagram of finite-level crystalline quotients. -/
public def diagram
    (T : FiniteLevelSystem X) :
    ℕᵒᵖ ⥤ CrystallineThickening.{u, v, w} S where
  obj n := T.term n.unop
  map f := T.transition (leOfHom f.unop)
  map_id n := T.transition_id n.unop
  map_comp f g := (T.transition_comp (leOfHom g.unop) (leOfHom f.unop)).symm

end FiniteLevelSystem

/-- A choice, for every completed crystalline thickening, of a finite-level system
approximating it. -/
noncomputable def finiteSystems
    (S : AffineCrystallineSituation.{u, v}) :
    ∀ X : CompletedCrystallineThickening.{u, v, w} S,
      FiniteLevelSystem X :=
  fun X => Classical.choice
    (exists_finiteLevelSystem X)

/-- The diagram of representables of the terms of a finite-level system, whose colimit is
the pro-object attached to that system. -/
abbrev proPresentation
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) :
    ℕᵒᵖᵒᵖ ⥤ ((CrystallineThickening.{u, v, w} S)ᵒᵖ)ᵒᵖ ⥤ Type w :=
  (FiniteLevelSystem.diagram T).op ⋙
    yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)

/-- The chosen colimit cocone presenting the pro-object of a finite-level system: the
colimit of the representables of its terms, taken in the category of ind-objects of the
opposite little crystalline category. -/
@[implicit_reducible] noncomputable def presentationColimit
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) :
    ColimitCocone ((FiniteLevelSystem.diagram T).op ⋙
      yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)) :=
  ⟨colimit.cocone _, colimit.isColimit _⟩

/-- The legs of the presenting colimit cocone are compatible with the transition maps. -/
private theorem yoneda_transition_comp_presentation_ι
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) {e e' : ℕ} (h : e ≤ e') :
    yoneda.map (T.transition h).op ≫ (presentationColimit T).cocone.ι.app (op (op e')) =
      (presentationColimit T).cocone.ι.app (op (op e)) := by
  simpa [proPresentation, FiniteLevelSystem.diagram] using
    (presentationColimit T).cocone.w ((homOfLE h).op.op)

/-- The colimit presenting a finite-level system really is an ind-object of the opposite
little crystalline category: it is a filtered colimit of representables. -/
theorem proPresentation_isInd
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) :
    IsIndObject (presentationColimit T).cocone.pt := by
  let : Category.{0, w} (ULift.{w} (ℕᵒᵖᵒᵖ)) :=
    @uliftCategory.{0, 0, w} (ℕᵒᵖᵒᵖ) inferInstance
  let Q : ULiftHom.{w} (ULift.{w} (ℕᵒᵖᵒᵖ)) ⥤ ℕᵒᵖᵒᵖ :=
    ULiftHom.down ⋙ ULift.downFunctor
  let : ULiftHom.down.IsRightAdjoint :=
    (ULiftHom.equiv (C := ULift.{w} (ℕᵒᵖᵒᵖ))).isRightAdjoint_inverse
  let : ULift.downFunctor.IsRightAdjoint :=
    (ULift.equivalence (C := ℕᵒᵖᵒᵖ)).isRightAdjoint_inverse
  let L : ULiftHom.{w} (ULift.{w} (ℕᵒᵖᵒᵖ)) ⥤
      ((CrystallineThickening.{u, v, w} S)ᵒᵖ)ᵒᵖ ⥤
        Type w :=
    Q ⋙ proPresentation T
  have hL : IsIndObject (C :=
      (CrystallineThickening.{u, v, w} S)ᵒᵖ) (colimit L) :=
    isIndObject_colimit _ L fun i => isIndObject_yoneda (C :=
      (CrystallineThickening.{u, v, w} S)ᵒᵖ) (op (T.term (Q.obj i).unop.unop))
  have hfinal : Q.Final := Functor.final_of_isRightAdjoint Q
  let hc : IsColimit ((presentationColimit T).cocone.whisker Q) :=
    (Functor.Final.isColimitWhiskerEquiv
      Q
      (presentationColimit T).cocone).symm (presentationColimit T).isColimit
  exact IsIndObject.map (IsColimit.coconePointUniqueUpToIso (colimit.isColimit L) hc).hom hL

/-- The pro-object of the little crystalline category attached to a finite-level system of
a completed crystalline thickening. -/
@[implicit_reducible] noncomputable def proObject
    {S : AffineCrystallineSituation.{u, v}}
    (X : CompletedCrystallineThickening.{u, v, w} S)
    (T : FiniteLevelSystem X) :
    ProCrystallineThickening.{u, v, w} S :=
  op ⟨(presentationColimit T).cocone.pt, proPresentation_isInd T⟩

/-- The map induced on quotients by a projection of a finite-level system is injective,
because both quotients are identified with `C`. -/
theorem finiteLevel_projection_quotientMap_injective
    {S : AffineCrystallineSituation.{u, v}}
    {Y : CompletedCrystallineThickening.{u, v, w} S}
    (TY : FiniteLevelSystem Y) (e : ℕ) :
    Function.Injective
      (Ideal.quotientMap (TY.term e).1.ring.ideal
        (TY.projection e).toRingHom
        (Ideal.map_le_iff_le_comap.mp (TY.projection e).ideal_comp)) := by
  intro a b hab
  obtain ⟨c, rfl⟩ := Y.toQuotient_bijective.surjective a
  obtain ⟨d, rfl⟩ := Y.toQuotient_bijective.surjective b
  have hcd : c = d := (TY.term e).2.injective <| by
    rw [← TY.projection_toQuotient e]
    exact hab
  rw [hcd]

/-- The divided power ideal of a finite-level term is the image of the divided power ideal
of the completed thickening. -/
theorem finiteLevel_projection_ideal_eq_map
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) (e : ℕ) :
    (T.term e).1.ring.ideal = X.ring.ideal.map (T.projection e).toRingHom := by
  let q := (T.projection e).toRingHom
  let qmap := Ideal.quotientMap (T.term e).1.ring.ideal q
    (Ideal.map_le_iff_le_comap.mp (T.projection e).ideal_comp)
  have hqmap : Function.Injective qmap := finiteLevel_projection_quotientMap_injective T e
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx⟩ := T.projection_surjective e y
    change q x = y at hx
    have hzero : Ideal.Quotient.mk X.ring.ideal x = 0 := by
      apply hqmap
      dsimp [qmap]
      rw [Ideal.quotientMap_mk, hx]
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hy
    rw [← hx]
    exact Ideal.mem_map_of_mem q (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  · exact (T.projection e).ideal_comp

/-- If the level `i` of the source is deep enough compared with the level `e` of the
target, the kernel of the source projection is killed by the composite to the target
quotient. -/
theorem finiteLevel_kernel_le
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) (i e : ℕ) (hlev : TY.cutoff + e ≤ TX.cutoff + i) :
    RingHom.ker (TX.projection i).toRingHom ≤
      RingHom.ker ((TY.projection e).toRingHom.comp f.hom.toRingHom) := by
  let qY := (TY.projection e).toRingHom.comp f.hom.toRingHom
  have hpow : ((TY.projection e).toRingHom (S.p : Y.ring)) ^ (TY.cutoff + e) = 0 := by
    rw [← map_pow, ← RingHom.mem_ker, TY.projection_ker]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) _
  have hkill : qY ((S.p : X.ring) ^ (TX.cutoff + i)) = 0 := by
    rw [map_pow, show qY (S.p : X.ring) = (TY.projection e).toRingHom (S.p : Y.ring) by
      simp [qY], ← Nat.add_sub_of_le hlev, pow_add, hpow, zero_mul]
  rw [TX.projection_ker i, DividedPowers.pAdicIdeal, Ideal.span_singleton_pow]
  refine Ideal.span_le.mpr ?_
  rintro z ⟨rfl⟩
  exact RingHom.mem_ker.mpr hkill

/-- At sufficiently deep levels, a morphism of completed thickenings induces a divided
power map between the finite-level quotients. -/
theorem finiteLevel_factor_dpmorphism
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) (i e : ℕ) (hlev : TY.cutoff + e ≤ TX.cutoff + i) :
    ∃ g : DividedPowers.DPMorphism (TX.term i).1.ring.dividedPowers
        (TY.term e).1.ring.dividedPowers,
      g.toRingHom.comp (TX.projection i).toRingHom =
        (TY.projection e).toRingHom.comp f.hom.toRingHom := by
  let q := TX.projection i
  let r := TY.projection e
  let rhs := r.toRingHom.comp f.hom.toRingHom
  have hker := finiteLevel_kernel_le TX TY f i e hlev
  have hq : Function.Surjective q.toRingHom := TX.projection_surjective i
  let gRing := RingHom.liftOfSurjective q.toRingHom hq ⟨rhs, hker⟩
  have hfactor : gRing.comp q.toRingHom = rhs := by
    ext x
    exact RingHom.liftOfRightInverse_comp_apply q.toRingHom (Function.surjInv hq)
      (Function.rightInverse_surjInv hq) ⟨rhs, hker⟩ x
  have hdpcomp : X.ring.dividedPowers.IsDPMorphism
      (TY.term e).1.ring.dividedPowers (gRing.comp q.toRingHom) := by
    rw [hfactor]
    exact (f.hom ≫ r).isDPMorphism
  have hdp := DividedPowers.IsDPMorphism.of_comp
    X.ring.dividedPowers (TX.term i).1.ring.dividedPowers
    (TY.term e).1.ring.dividedPowers q.toRingHom gRing
    (finiteLevel_projection_ideal_eq_map TX i) q.isDPMorphism hdpcomp
  exact ⟨DividedPowers.DPMorphism.mk' hdp, hfactor⟩

/-- At sufficiently deep levels, a morphism of completed thickenings induces a morphism of
the finite-level quotients in the little crystalline category. -/
theorem finiteLevel_factor
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) (i e : ℕ) (hlev : TY.cutoff + e ≤ TX.cutoff + i) :
    ∃ g : TX.term i ⟶ TY.term e,
      g.hom.hom.toRingHom.comp (TX.projection i).toRingHom =
        (TY.projection e).toRingHom.comp f.hom.toRingHom := by
  obtain ⟨m, hm⟩ := finiteLevel_factor_dpmorphism TX TY f i e hlev
  let q := TX.projection i
  let r := TY.projection e
  have hbase : m.comp (TX.term i).1.fromBase = (TY.term e).1.fromBase := by
    apply DividedPowers.DPMorphism.ext
    funext a
    have hXval : q.toRingHom (X.fromBase.toRingHom a) =
        (TX.term i).1.fromBase.toRingHom a := by
      simpa [q] using congrArg (fun h : DividedPowers.DPMorphism S.A.dividedPowers
        (TX.term i).1.ring.dividedPowers => h.toRingHom a) (TX.projection_fromBase i)
    have hYval : r.toRingHom (Y.fromBase.toRingHom a) =
        (TY.term e).1.fromBase.toRingHom a := by
      simpa [r] using congrArg (fun h : DividedPowers.DPMorphism S.A.dividedPowers
        (TY.term e).1.ring.dividedPowers => h.toRingHom a) (TY.projection_fromBase e)
    have hfval : f.hom.toRingHom (X.fromBase.toRingHom a) =
        Y.fromBase.toRingHom a := by
      simpa using congrArg (fun h : DividedPowers.DPMorphism S.A.dividedPowers
        Y.ring.dividedPowers => h.toRingHom a) f.fromBase_comp
    calc
      m.toRingHom ((TX.term i).1.fromBase.toRingHom a) =
          m.toRingHom (q.toRingHom (X.fromBase.toRingHom a)) := by
        rw [← hXval]
      _ = (r.toRingHom.comp f.hom.toRingHom) (X.fromBase.toRingHom a) :=
        congrArg (fun k : X.ring →+* (TY.term e).1.ring => k (X.fromBase.toRingHom a)) hm
      _ = r.toRingHom (Y.fromBase.toRingHom a) := by
        change r.toRingHom (f.hom.toRingHom (X.fromBase.toRingHom a)) = _
        exact congrArg (fun z : Y.ring => r.toRingHom z) hfval
      _ = (TY.term e).1.fromBase.toRingHom a := hYval
  have hquotientMap :
      (Ideal.quotientMap (TY.term e).1.ring.ideal m.toRingHom
          (Ideal.map_le_iff_le_comap.mp m.ideal_comp)).comp
          (Ideal.quotientMap (TX.term i).1.ring.ideal q.toRingHom
            (Ideal.map_le_iff_le_comap.mp q.ideal_comp)) =
        (Ideal.quotientMap (TY.term e).1.ring.ideal r.toRingHom
          (Ideal.map_le_iff_le_comap.mp r.ideal_comp)).comp
          (DividedPowerRing.quotientRingHom
            f.hom) := by
    apply RingHom.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hx := congrArg (fun k : X.ring →+* (TY.term e).1.ring => k x) hm
    change m.toRingHom (q.toRingHom x) = r.toRingHom (f.hom.toRingHom x) at hx
    change Ideal.Quotient.mk (TY.term e).1.ring.ideal
      (m.toRingHom (q.toRingHom x)) =
      Ideal.Quotient.mk (TY.term e).1.ring.ideal (r.toRingHom (f.hom.toRingHom x))
    exact congrArg (Ideal.Quotient.mk (TY.term e).1.ring.ideal) hx
  have hquotient :
      (Ideal.quotientMap (TY.term e).1.ring.ideal m.toRingHom
        (Ideal.map_le_iff_le_comap.mp m.ideal_comp)).comp (TX.term i).1.toQuotient =
        (TY.term e).1.toQuotient := by
    rw [← TX.projection_toQuotient i]
    calc
      _ = ((Ideal.quotientMap (TY.term e).1.ring.ideal m.toRingHom
          (Ideal.map_le_iff_le_comap.mp m.ideal_comp)).comp
          (Ideal.quotientMap (TX.term i).1.ring.ideal q.toRingHom
            (Ideal.map_le_iff_le_comap.mp q.ideal_comp))).comp X.toQuotient := by
        rw [RingHom.comp_assoc]
      _ = ((Ideal.quotientMap (TY.term e).1.ring.ideal r.toRingHom
          (Ideal.map_le_iff_le_comap.mp r.ideal_comp)).comp
          (DividedPowerRing.quotientRingHom
            f.hom)).comp X.toQuotient := by rw [hquotientMap]
      _ = (Ideal.quotientMap (TY.term e).1.ring.ideal r.toRingHom
          (Ideal.map_le_iff_le_comap.mp r.ideal_comp)).comp Y.toQuotient := by
        rw [RingHom.comp_assoc, f.toQuotient_comp]
      _ = (TY.term e).1.toQuotient := TY.projection_toQuotient e
  exact ⟨⟨{ hom := m, fromBase_comp := hbase, toQuotient_comp := hquotient }⟩, hm⟩

/-- A choice of the induced morphism of finite-level quotients, at the level
`TY.cutoff + e` of the source. -/
noncomputable def factorAtLevel
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) (e : ℕ) : TX.term (TY.cutoff + e) ⟶ TY.term e :=
  Classical.choose (finiteLevel_factor TX TY f (TY.cutoff + e) e (by omega))

/-- The chosen induced morphism does factor the composite of the projection with the given
morphism. -/
theorem factorAtLevel_spec
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) (e : ℕ) :
    (factorAtLevel TX TY f e).hom.hom.toRingHom.comp
        (TX.projection (TY.cutoff + e)).toRingHom =
      (TY.projection e).toRingHom.comp f.hom.toRingHom :=
  Classical.choose_spec (finiteLevel_factor TX TY f (TY.cutoff + e) e (by omega))

/-- Two morphisms out of a finite-level term agree if they agree after composing with the
projection from the completed thickening. -/
private theorem hom_eq_of_comp_projection_eq
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) {i : ℕ} {W : CrystallineThickening.{u, v, w} S}
    (a b : T.term i ⟶ W)
    (h : a.hom.hom.toRingHom.comp (T.projection i).toRingHom =
      b.hom.hom.toRingHom.comp (T.projection i).toRingHom) : a = b := by
  apply ObjectProperty.hom_ext
  apply DividedPowerThickening.Hom.ext
  apply DividedPowers.DPMorphism.ext
  funext x
  obtain ⟨y, rfl⟩ := T.projection_surjective i x
  exact congrArg (fun k => k y) h

/-- The chosen induced morphisms commute with the transition maps of the two systems. -/
theorem factorAtLevel_compatible
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) {e e' : ℕ} (h : e ≤ e') :
    factorAtLevel TX TY f e' ≫ TY.transition h =
      TX.transition (Nat.add_le_add_left h TY.cutoff) ≫ factorAtLevel TX TY f e := by
  let i := TY.cutoff + e
  let i' := TY.cutoff + e'
  let s := TX.transition (Nat.add_le_add_left h TY.cutoff)
  let t := TY.transition h
  let u := factorAtLevel TX TY f e
  let u' := factorAtLevel TX TY f e'
  have hs : s.hom.hom.toRingHom.comp (TX.projection i').toRingHom =
      (TX.projection i).toRingHom :=
    congrArg (fun g : DividedPowers.DPMorphism X.ring.dividedPowers
      (TX.term i).1.ring.dividedPowers => g.toRingHom)
      (TX.transition_projection (Nat.add_le_add_left h TY.cutoff))
  have ht : t.hom.hom.toRingHom.comp (TY.projection e').toRingHom =
      (TY.projection e).toRingHom :=
    congrArg (fun g : DividedPowers.DPMorphism Y.ring.dividedPowers
      (TY.term e).1.ring.dividedPowers => g.toRingHom) (TY.transition_projection h)
  have hcomp :
      (t.hom.hom.toRingHom.comp u'.hom.hom.toRingHom).comp
          (TX.projection i').toRingHom =
        (u.hom.hom.toRingHom.comp s.hom.hom.toRingHom).comp
          (TX.projection i').toRingHom := by
    calc
      _ = (TY.projection e).toRingHom.comp f.hom.toRingHom := by
        rw [RingHom.comp_assoc, factorAtLevel_spec, ← RingHom.comp_assoc, ht]
      _ = (u.hom.hom.toRingHom.comp s.hom.hom.toRingHom).comp
            (TX.projection i').toRingHom := by
        rw [RingHom.comp_assoc, hs, factorAtLevel_spec]
  exact hom_eq_of_comp_projection_eq TX _ _ hcomp

/-- The cocone over the target's presenting diagram whose legs are given by the induced
morphisms of finite-level quotients; its universal map is the map of pro-objects. -/
noncomputable def proMapCocone
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) : Cocone ((FiniteLevelSystem.diagram TY).op ⋙
      yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)) where
  pt := (presentationColimit TX).cocone.pt
  ι := {
    app := fun j =>
      yoneda.map (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)
          (factorAtLevel TX TY f j.unop.unop).op ≫
        (presentationColimit TX).cocone.ι.app (op (op (TY.cutoff + j.unop.unop)))
    naturality := by
      intro j j' h
      dsimp only [Functor.comp_map, Functor.const_obj_map, Category.comp_id]
      let he := leOfHom h.unop.unop
      let hi := Nat.add_le_add_left he TY.cutoff
      change yoneda.map (TY.transition he).op ≫
          yoneda.map (factorAtLevel TX TY f j'.unop.unop).op ≫
            (presentationColimit TX).cocone.ι.app (op (op (TY.cutoff + j'.unop.unop))) =
        (yoneda.map (factorAtLevel TX TY f j.unop.unop).op ≫
          (presentationColimit TX).cocone.ι.app (op (op (TY.cutoff + j.unop.unop))))
      have hlegs :
          yoneda.map (TY.transition he).op ≫
              yoneda.map (factorAtLevel TX TY f j'.unop.unop).op =
            yoneda.map (factorAtLevel TX TY f j.unop.unop).op ≫
              yoneda.map (TX.transition hi).op := by
        simpa only [← Functor.map_comp, ← op_comp] using
          congrArg (yoneda.map (C :=
            (CrystallineThickening.{u, v, w} S)ᵒᵖ))
            (congrArg (fun g => g.op) (factorAtLevel_compatible TX TY f he))
      have hcolim :
          yoneda.map (TX.transition hi).op ≫
              (presentationColimit TX).cocone.ι.app (op (op (TY.cutoff + j'.unop.unop))) =
              (presentationColimit TX).cocone.ι.app (op (op (TY.cutoff + j.unop.unop))) := by
        simpa [proPresentation, FiniteLevelSystem.diagram] using
          (presentationColimit TX).cocone.w ((homOfLE hi).op.op)
      dsimp only [proPresentation, FiniteLevelSystem.diagram] at hcolim ⊢
      rw [← Category.assoc, hlegs, Category.assoc, hcolim]
  }

/-- The map of pro-objects induced by a morphism of completed crystalline thickenings. -/
@[implicit_reducible] noncomputable def proMap
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) : proObject X TX ⟶ proObject Y TY := by
  let m := (presentationColimit TY).isColimit.desc (proMapCocone TX TY f)
  exact Quiver.Hom.op (ObjectProperty.homMk m)

/-- The morphism induced by the identity is the transition map of the system. -/
theorem factorAtLevel_id
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) (e : ℕ) :
    factorAtLevel T T (𝟙 X) e = T.transition (by omega) := by
  refine hom_eq_of_comp_projection_eq T _ _ ?_
  exact (factorAtLevel_spec T T (𝟙 X) e).trans (congrArg (fun g : DividedPowers.DPMorphism
      X.ring.dividedPowers (T.term e).1.ring.dividedPowers => g.toRingHom)
      (T.transition_projection (show e ≤ T.cutoff + e by omega))).symm

/-- The component of the induced map of pro-objects at a finite level is the induced
morphism of finite-level quotients. -/
theorem proMap_ι
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (f : X ⟶ Y) (e : ℕ) :
    (presentationColimit TY).cocone.ι.app (op (op e)) ≫
        ((proMap TX TY f).unop).hom =
      yoneda.map (factorAtLevel TX TY f e).op ≫
        (presentationColimit TX).cocone.ι.app (op (op (TY.cutoff + e))) := by
  change (presentationColimit TY).cocone.ι.app (op (op e)) ≫
      (presentationColimit TY).isColimit.desc (proMapCocone TX TY f) =
    (proMapCocone TX TY f).ι.app (op (op e))
  exact (presentationColimit TY).isColimit.fac (proMapCocone TX TY f)
    (op (op e))

/-- The pro-object construction sends the identity to the identity. -/
theorem proMap_id
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) :
    proMap T T (𝟙 X) = 𝟙 (proObject X T) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  dsimp only [proMap, proObject]
  apply (presentationColimit T).isColimit.hom_ext
  intro j
  let e := j.unop.unop
  change (presentationColimit T).cocone.ι.app j ≫
      (presentationColimit T).isColimit.desc (proMapCocone T T (𝟙 X)) =
    (presentationColimit T).cocone.ι.app j ≫
      𝟙 (proMapCocone T T (𝟙 X)).pt
  rw [(presentationColimit T).isColimit.fac]
  dsimp only [proMapCocone]
  rw [factorAtLevel_id]
  exact yoneda_transition_comp_presentation_ι T (show e ≤ T.cutoff + e by omega)

/-- The chosen induced morphisms are compatible with composition, after passing to a deep
enough level of the source. -/
theorem factorAtLevel_comp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (TZ : FiniteLevelSystem Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (e : ℕ) :
    TX.transition (show TZ.cutoff + e ≤ TY.cutoff + (TZ.cutoff + e) by omega) ≫
        factorAtLevel TX TZ (f ≫ g) e =
      factorAtLevel TX TY f (TZ.cutoff + e) ≫ factorAtLevel TY TZ g e := by
  let i := TZ.cutoff + e
  let i' := TY.cutoff + (TZ.cutoff + e)
  let s := TX.transition (show i ≤ i' by omega)
  let p := TX.projection i
  let p' := TX.projection i'
  let u := factorAtLevel TX TZ (f ≫ g) e
  let v := factorAtLevel TX TY f (TZ.cutoff + e)
  let z := factorAtLevel TY TZ g e
  have hs : s.hom.hom.toRingHom.comp p'.toRingHom = p.toRingHom :=
    congrArg (fun m : DividedPowers.DPMorphism X.ring.dividedPowers
      (TX.term i).1.ring.dividedPowers => m.toRingHom)
      (TX.transition_projection (show i ≤ i' by omega))
  have hfg : (f ≫ g).hom.toRingHom =
      g.hom.toRingHom.comp f.hom.toRingHom := rfl
  have hring :
      (u.hom.hom.toRingHom.comp s.hom.hom.toRingHom).comp p'.toRingHom =
        (z.hom.hom.toRingHom.comp v.hom.hom.toRingHom).comp p'.toRingHom := by
    calc
      _ = u.hom.hom.toRingHom.comp p.toRingHom := by
        rw [RingHom.comp_assoc, hs]
      _ = (TZ.projection e).toRingHom.comp
          (g.hom.toRingHom.comp f.hom.toRingHom) := by
        simpa [u, p, i, hfg] using factorAtLevel_spec TX TZ (f ≫ g) e
      _ = (z.hom.hom.toRingHom.comp
          (TY.projection (TZ.cutoff + e)).toRingHom).comp
            f.hom.toRingHom := by
        rw [← RingHom.comp_assoc, factorAtLevel_spec TY TZ g e]
      _ = (z.hom.hom.toRingHom.comp v.hom.hom.toRingHom).comp p'.toRingHom := by
        rw [RingHom.comp_assoc, ← factorAtLevel_spec TX TY f (TZ.cutoff + e), RingHom.comp_assoc]
  exact hom_eq_of_comp_projection_eq TX _ _ hring

/-- The pro-object construction is compatible with composition. -/
theorem proMap_comp
    {S : AffineCrystallineSituation.{u, v}}
    {X Y Z : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (TZ : FiniteLevelSystem Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    proMap TX TY f ≫ proMap TY TZ g = proMap TX TZ (f ≫ g) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  dsimp only [proObject]
  apply (presentationColimit TZ).isColimit.hom_ext
  intro j
  let e := j.unop.unop
  let h : TZ.cutoff + e ≤ TY.cutoff + (TZ.cutoff + e) := by omega
  let s := TX.transition h
  let u := factorAtLevel TX TZ (f ≫ g) e
  let v := factorAtLevel TX TY f (TZ.cutoff + e)
  let z := factorAtLevel TY TZ g e
  have hstage :
      yoneda.map z.op ≫ yoneda.map v.op =
        yoneda.map u.op ≫ yoneda.map (TX.transition h).op := by
    simpa only [← Functor.map_comp, ← op_comp] using
      congrArg (fun k => yoneda.map (C :=
        (CrystallineThickening.{u, v, w} S)ᵒᵖ) k.op)
        (factorAtLevel_comp TX TY TZ f g e).symm
  change ((presentationColimit TZ).cocone.ι.app (op (op e)) ≫
        ((proMap TY TZ g).unop).hom) ≫ ((proMap TX TY f).unop).hom =
      (presentationColimit TZ).cocone.ι.app (op (op e)) ≫
        ((proMap TX TZ (f ≫ g)).unop).hom
  let legZ : (yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)).obj
      (op (TZ.term e)) ⟶
      (presentationColimit TZ).cocone.pt :=
    (presentationColimit TZ).cocone.ι.app (op (op e))
  let legY : (yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)).obj
      (op (TY.term (TZ.cutoff + e))) ⟶
      (presentationColimit TY).cocone.pt :=
    (presentationColimit TY).cocone.ι.app (op (op (TZ.cutoff + e)))
  let legX : (yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)).obj
      (op (TX.term (TY.cutoff + (TZ.cutoff + e)))) ⟶
      (presentationColimit TX).cocone.pt :=
    (presentationColimit TX).cocone.ι.app (op (op (TY.cutoff + (TZ.cutoff + e))))
  let legXsmall : (yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)).obj
      (op (TX.term (TZ.cutoff + e))) ⟶
      (presentationColimit TX).cocone.pt :=
    (presentationColimit TX).cocone.ι.app (op (op (TZ.cutoff + e)))
  change (legZ ≫ (proMap TY TZ g).unop.hom) ≫
      (proMap TX TY f).unop.hom = legZ ≫ (proMap TX TZ (f ≫ g)).unop.hom
  have hY' : legZ ≫ (proMap TY TZ g).unop.hom = yoneda.map z.op ≫ legY := by
    simpa [legZ, legY, FiniteLevelSystem.diagram] using proMap_ι TY TZ g e
  have hX' : legY ≫ (proMap TX TY f).unop.hom = yoneda.map v.op ≫ legX := by
    simpa [legY, legX, FiniteLevelSystem.diagram] using proMap_ι TX TY f (TZ.cutoff + e)
  have hFG' : legZ ≫ (proMap TX TZ (f ≫ g)).unop.hom = yoneda.map u.op ≫ legXsmall := by
    simpa [legZ, legXsmall, FiniteLevelSystem.diagram] using proMap_ι TX TZ (f ≫ g) e
  have hshift' : yoneda.map (TX.transition h).op ≫ legX = legXsmall := by
    simpa [legX, legXsmall, FiniteLevelSystem.diagram] using
      yoneda_transition_comp_presentation_ι TX h
  rw [hY', Category.assoc, hX', ← Category.assoc, hstage,
    Category.assoc, hshift', ← hFG']

/-- The comparison isomorphism between the chosen presenting colimit and Mathlib's chosen
colimit of the same diagram. -/
noncomputable def presentationIso
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) :
    (presentationColimit T).cocone.pt ≅
    colimit ((FiniteLevelSystem.diagram T).op ⋙
        yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)) :=
  (presentationColimit T).isColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((FiniteLevelSystem.diagram T).op ⋙
      yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)))

/-- The comparison isomorphism identifies the legs of the two colimit cocones. -/
theorem presentationIso_ι_hom
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) (e : ℕ) :
    (presentationColimit T).cocone.ι.app (op (op e)) ≫ (presentationIso T).hom =
      colimit.ι ((FiniteLevelSystem.diagram T).op ⋙
        yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)) (op (op e)) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (presentationColimit T).isColimit
    (colimit.isColimit ((FiniteLevelSystem.diagram T).op ⋙
      yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ))) (op (op e))

/-- The inverse comparison isomorphism identifies the legs of the two colimit cocones. -/
theorem presentationIso_ι_inv
    {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X) (e : ℕ) :
    colimit.ι ((FiniteLevelSystem.diagram T).op ⋙
        yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)) (op (op e)) ≫
        (presentationIso T).inv =
      (presentationColimit T).cocone.ι.app (op (op e)) :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (presentationColimit T).isColimit
    (colimit.isColimit ((FiniteLevelSystem.diagram T).op ⋙
      yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ))) (op (op e))

/-- Every map of pro-objects is, at each finite level of the target, represented by a
morphism from some finite level of the source. -/
theorem proHom_has_level_map
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (h : proObject X TX ⟶ proObject Y TY) (e : ℕ) :
    ∃ (i : ℕ) (g : TX.term i ⟶ TY.term e),
      (presentationColimit TY).cocone.ι.app (op (op e)) ≫ h.unop.hom =
        yoneda.map g.op ≫ (presentationColimit TX).cocone.ι.app (op (op i)) := by
  let C := (CrystallineThickening.{u, v, w} S)ᵒᵖ
  let α : (yoneda (C := C)).obj (op (TY.term e)) ⟶ (presentationColimit TX).cocone.pt :=
    (presentationColimit TY).cocone.ι.app (op (op e)) ≫ h.unop.hom
  let x := yonedaEquiv α
  obtain ⟨j, y, hy⟩ := FunctorToTypes.jointly_surjective
    ((FiniteLevelSystem.diagram TX).op ⋙ yoneda (C := C))
    (op (op (TY.term e))) (presentationColimit TX).isColimit x
  rcases j with ⟨⟨i⟩⟩
  let g : TX.term i ⟶ TY.term e := y.unop
  let legX : (yoneda (C := C)).obj (op (TX.term i)) ⟶
      (presentationColimit TX).cocone.pt :=
    (presentationColimit TX).cocone.ι.app (op (op i))
  refine ⟨i, g, ?_⟩
  apply yonedaEquiv.injective
  calc
    yonedaEquiv α = x := rfl
    _ = legX.app (op (op (TY.term e))) y := hy
    _ = yonedaEquiv (yoneda.map g.op ≫ legX) := by
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      change (legX.app (op (op (TY.term e)))).hom y =
        (legX.app (op (op (TY.term e)))).hom g.op
      congr 1

/-- Two level representatives of the same map of pro-objects agree after passing to a deep
enough level of the source. -/
theorem proHom_level_representatives_eventually_equal
    {S : AffineCrystallineSituation.{u, v}}
    {X Y : CompletedCrystallineThickening.{u, v, w} S}
    (TX : FiniteLevelSystem X)
    (TY : FiniteLevelSystem Y)
    (h : proObject X TX ⟶ proObject Y TY) {e e' i i' : ℕ}
    (g : TX.term i ⟶ TY.term e) (g' : TX.term i' ⟶ TY.term e')
    (he : e ≤ e')
    (hg : (presentationColimit TY).cocone.ι.app (op (op e)) ≫ h.unop.hom =
      yoneda.map g.op ≫ (presentationColimit TX).cocone.ι.app (op (op i)))
    (hg' : (presentationColimit TY).cocone.ι.app (op (op e')) ≫ h.unop.hom =
      yoneda.map g'.op ≫ (presentationColimit TX).cocone.ι.app (op (op i'))) :
    ∃ (k : ℕ) (hi : i ≤ k) (hi' : i' ≤ k),
      TX.transition hi ≫ g = TX.transition hi' ≫ g' ≫ TY.transition he := by
  let legY : (yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)).obj
      (op (TY.term e)) ⟶ (presentationColimit TY).cocone.pt :=
    (presentationColimit TY).cocone.ι.app (op (op e))
  let legY' : (yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)).obj
      (op (TY.term e')) ⟶ (presentationColimit TY).cocone.pt :=
    (presentationColimit TY).cocone.ι.app (op (op e'))
  let legX : (yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)).obj
      (op (TX.term i)) ⟶ (presentationColimit TX).cocone.pt :=
    (presentationColimit TX).cocone.ι.app (op (op i))
  let legX' : (yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)).obj
      (op (TX.term i')) ⟶ (presentationColimit TX).cocone.pt :=
    (presentationColimit TX).cocone.ι.app (op (op i'))
  have hleg : legY = yoneda.map (TY.transition he).op ≫ legY' := by
    simpa [legY, legY', FiniteLevelSystem.diagram] using
      (yoneda_transition_comp_presentation_ι TY he).symm
  have hg'' : legY' ≫ h.unop.hom = yoneda.map g'.op ≫ legX' := hg'
  have hmaps : yoneda.map g.op ≫ legX =
      yoneda.map (g' ≫ TY.transition he).op ≫ legX' := by
    calc
      yoneda.map g.op ≫ legX = legY ≫ h.unop.hom := hg.symm
      _ = (yoneda.map (TY.transition he).op ≫ legY') ≫ h.unop.hom := by rw [hleg]
      _ = yoneda.map (TY.transition he).op ≫ (legY' ≫ h.unop.hom) := by
        rw [Category.assoc]
      _ = yoneda.map (TY.transition he).op ≫
            (yoneda.map g'.op ≫ legX') := by rw [hg'']
      _ = yoneda.map (g' ≫ TY.transition he).op ≫ legX' := by
        rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  have hpoint := congrArg (fun η => yonedaEquiv η) hmaps
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map,
    yonedaEquiv_comp, yonedaEquiv_yoneda_map] at hpoint
  let F := (FiniteLevelSystem.diagram TX).op ⋙
    yoneda (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)
  let eval : (((CrystallineThickening.{u, v, w} S)ᵒᵖ)ᵒᵖ ⥤ Type w) ⥤ Type w :=
    (evaluation ((CrystallineThickening.{u, v, w} S)ᵒᵖ)ᵒᵖ (Type w)).obj
      (op (op (TY.term e)))
  let c := eval.mapCocone (presentationColimit TX).cocone
  let hcolim := isColimitOfPreserves eval (presentationColimit TX).isColimit
  have hcol :
      (c.ι.app (op (op i))) g.op =
        (c.ι.app (op (op i'))) (g' ≫ TY.transition he).op := hpoint
  obtain ⟨k, f, f', hmap⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (F ⋙ eval) hcolim).mp hcol
  rcases k with ⟨⟨k⟩⟩
  let hi : i ≤ k := leOfHom (f.unop.unop)
  let hi' : i' ≤ k := leOfHom (f'.unop.unop)
  have hmap' :
      (TX.transition hi ≫ g).op =
        (TX.transition hi' ≫ g' ≫ TY.transition he).op := by
    change g.op ≫ (TX.transition hi).op =
      (g' ≫ TY.transition he).op ≫ (TX.transition hi').op at hmap
    simpa only [← op_comp] using hmap
  exact ⟨k, hi, hi', Quiver.Hom.op_inj hmap'⟩

end ProObject

end Crystalline

end
