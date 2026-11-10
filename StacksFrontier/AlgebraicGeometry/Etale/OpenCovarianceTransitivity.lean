module

public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality

/-!
# Transitivity of covariance for the finite-support direct image

Let `f : X ⟶ Y` be locally of finite type and locally quasi-finite in a big étale site and let
`j : X'' ⟶ X'` and `k : X' ⟶ X` be open immersions. Restricting an abelian sheaf on the small
étale site of `X` to `X''` in two steps or in one gives canonically isomorphic finite-support
direct images along the composite, and the covariance map of the one-step open immersion
`j ≫ k` is the composite of the covariance maps of `j` and of `k`.

## References

* [Stacks Project, Tag 0F6S](https://stacks.math.columbia.edu/tag/0F6S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w₁ w₂ w₃

namespace AlgebraicGeometry.SmallEtale

section Reassociation

/-- Substituting in the left two factors and the right two factors of a threefold composite. -/
public theorem comp_eq_comp_of_comp {C : Type w₁} [Category.{w₂} C] {a b c d e : C}
    {p : a ⟶ b} {q : b ⟶ c} {r : a ⟶ d} {s : d ⟶ c} (h : p ≫ q = r ≫ s)
    {t : c ⟶ e} {w : d ⟶ e} (h2 : s ≫ t = w) : p ≫ q ≫ t = r ≫ w := by
  rw [← Category.assoc, h, Category.assoc, h2]

/-- A fourfold composite, reassociated so that the first three factors are grouped. -/
public theorem comp_assoc_three {C : Type w₁} [Category.{w₂} C] {a b c d e : C}
    (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d) (t : d ⟶ e) :
    p ≫ q ≫ r ≫ t = ((p ≫ q) ≫ r) ≫ t := by
  rw [Category.assoc, Category.assoc]

end Reassociation

section SmallEtaleBasics

variable (B : BigEtaleSite.{u})

/-- A morphism of the small étale site is compatible with the structure morphisms. -/
public theorem toScheme_map_comp_structure {P : B.Scheme}
    {W W' : SmallEtale B P.obj P.property} (a : W' ⟶ W) :
    (SmallEtale.toScheme B P.obj P.property).map a ≫ B.inclusion.map W.obj.hom =
      B.inclusion.map W'.obj.hom :=
  (B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map (Over.w ((SmallEtale.inclusion B P.obj P.property).map a)))

/-- Small étale base change of an étale test object is a fibre product of schemes. -/
public theorem isPullback_smallEtaleBaseChange {P Q : B.Scheme} (g : P ⟶ Q)
    (W : SmallEtale B Q.obj Q.property) :
    IsPullback (B.inclusion.map (pullback.fst W.obj.hom g))
      (B.inclusion.map (((smallEtaleBaseChange B g).obj W).obj.hom))
      (B.inclusion.map W.obj.hom) (B.inclusion.map g) :=
  IsPullback.map B.inclusion (IsPullback.of_hasPullback W.obj.hom g)

end SmallEtaleBasics

section Instances

variable (B : BigEtaleSite.{u}) {X'' X' X : B.Scheme} (j : X'' ⟶ X') (k : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)]

/-- A composite of open immersions of a big étale site is an open immersion. -/
public instance isOpenImmersion_comp : IsOpenImmersion (B.inclusion.map (j ≫ k)) := by
  change IsOpenImmersion (B.inclusion.map j ≫ B.inclusion.map k)
  infer_instance

/-- Post-composition with a composite of open immersions is the composite of the
post-compositions. -/
public theorem openPostcompose_comp :
    openPostcompose B j ⋙ openPostcompose B k = openPostcompose B (j ≫ k) := rfl

end Instances

section BaseChangeHomComp

variable (B : BigEtaleSite.{u}) {X'' X' X Y : B.Scheme} (j : X'' ⟶ X') (k : X' ⟶ X)
  (f : X ⟶ Y) [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)]

/-- The induced open immersion on étale base changes lies over the open immersion itself: it
carries the structure morphism of the base change along the composite to the structure morphism
of the base change, followed by the open immersion. -/
public theorem openBaseChangeHom_structure (g : X' ⟶ Y)
    (V : SmallEtale B Y.obj Y.property) :
    openBaseChangeHom B j g V ≫ B.inclusion.map ((baseChange B g V).obj.hom) =
      B.inclusion.map ((baseChange B (j ≫ g) V).obj.hom) ≫ B.inclusion.map j := by
  exact (congrArg (fun z => z ≫ B.inclusion.map ((baseChange B g V).obj.hom))
      (openBaseChangeMap_toScheme B j g V)).symm.trans
    ((toScheme_map_comp_structure B ((openBaseChangeMap B j g).app V)).trans
      (B.inclusion.map_comp _ _))

/-- **The induced open immersions on étale base changes compose.** The open immersion induced
by `j ≫ k` is the composite of those induced by `j` and by `k`. -/
public theorem openBaseChangeHom_trans (V : SmallEtale B Y.obj Y.property) :
    openBaseChangeHom B j (k ≫ f) V ≫ openBaseChangeHom B k f V =
      openBaseChangeHom B (j ≫ k) f V := by
  have hfst :=
    (congrArg (fun z => openBaseChangeHom B j (k ≫ f) V ≫ z)
      (openBaseChangeHom_comp B k f V)).trans
      ((openBaseChangeHom_comp B j (k ≫ f) V).trans
        (openBaseChangeHom_comp B (j ≫ k) f V).symm)
  have hsnd :=
    (congrArg (fun z => openBaseChangeHom B j (k ≫ f) V ≫ z)
      (openBaseChangeHom_structure B k f V)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ B.inclusion.map k)
          (openBaseChangeHom_structure B j (k ≫ f) V)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg
                (fun z => B.inclusion.map ((baseChange B (j ≫ (k ≫ f)) V).obj.hom) ≫ z)
              (B.inclusion.map_comp j k).symm).trans
              (openBaseChangeHom_structure B (j ≫ k) f V).symm))))
  exact (isPullback_smallEtaleBaseChange B f V).hom_ext
    ((Category.assoc _ _ _).trans hfst) ((Category.assoc _ _ _).trans hsnd)

end BaseChangeHomComp

section Uniqueness

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] (f : X ⟶ Y)

/-- The comparison of canonical support opens is pinned down by its compatibility with the two
open inclusions: a morphism into the base change of the canonical open of the image support is
determined by its two projections, and the projection to the canonical open is determined
because the open inclusion is a monomorphism. -/
public theorem eq_covarianceOpenMap (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1)
    (a : openCovarianceSupportObject B (j ≫ f) V E ⟶
      (smallEtaleBaseChange B j).obj (openCovarianceSupportObject B f V D))
    (ha : (SmallEtale.toScheme B X'.obj X'.property).map a ≫
        B.inclusion.map (pullback.fst ((openCovarianceSupportObject B f V D).obj.hom) j) ≫
        (openCovarianceSupportOpen B f V D).ι =
      (openCovarianceSupportOpen B (j ≫ f) V E).ι ≫ openBaseChangeHom B j f V) :
    a = covarianceOpenMap B j f V E D hD := by
  apply (SmallEtale.toScheme B X'.obj X'.property).map_injective
  refine (isPullback_smallEtaleBaseChange B j
    (openCovarianceSupportObject B f V D)).hom_ext ?_ ?_
  · refine (cancel_mono (openCovarianceSupportOpen B f V D).ι).1 ?_
    exact (Category.assoc _ _ _).trans
      (ha.trans ((covarianceOpenMap_commutes B j f V E D hD).symm.trans
        (Category.assoc _ _ _).symm))
  · exact (toScheme_map_comp_structure B a).trans
      (toScheme_map_comp_structure B (covarianceOpenMap B j f V E D hD)).symm

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- Restricting a section of `F` through the unit of the restriction adjunction along the
comparison of canonical support opens is the same as restricting it along the comparison of
canonical opens over the source and then comparing the two descriptions of restriction. -/
public theorem unit_comp_covarianceOpenMap (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
        (op (openCovarianceSupportObject B f V D)) ≫
      ((openRestriction B j).obj F).obj.map (covarianceOpenMap B j f V E D hD).op =
    F.obj.map (covarianceTargetOpenMap B j f V E D hD).op ≫
      ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
        (op (openCovarianceSupportObject B (j ≫ f) V E)) := by
  have hunit : F.obj.map ((openPostcomposeAdjunction B j).counit.app
          (openCovarianceSupportObject B f V D)).op ≫
        ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
          (op ((smallEtaleBaseChange B j).obj (openCovarianceSupportObject B f V D))) =
      (((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
          (op (openCovarianceSupportObject B f V D)) := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    exact (ConcreteCategory.comp_apply _ _ s).trans
      (openRestrictionIso_unit_app.{u, v} B j F (openCovarianceSupportObject B f V D) s)
  have hnat := ((openRestrictionIso.{u, v} B j).hom.app F).hom.naturality
    (covarianceOpenMap B j f V E D hD).op
  have hcounit : F.obj.map ((openPostcomposeAdjunction B j).counit.app
          (openCovarianceSupportObject B f V D)).op ≫
        F.obj.map ((openPostcompose B j).map (covarianceOpenMap B j f V E D hD)).op =
      F.obj.map (covarianceTargetOpenMap B j f V E D hD).op := by
    rw [← Functor.map_comp, ← op_comp, covarianceOpenMap_counit B j f V E D hD]
  calc
    _ = (F.obj.map ((openPostcomposeAdjunction B j).counit.app
            (openCovarianceSupportObject B f V D)).op ≫
          ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
            (op ((smallEtaleBaseChange B j).obj (openCovarianceSupportObject B f V D)))) ≫
          ((openRestriction B j).obj F).obj.map (covarianceOpenMap B j f V E D hD).op :=
      congrArg (fun z => z ≫ ((openRestriction B j).obj F).obj.map
        (covarianceOpenMap B j f V E D hD).op) hunit.symm
    _ = F.obj.map ((openPostcomposeAdjunction B j).counit.app
          (openCovarianceSupportObject B f V D)).op ≫
          (((openRestrictionIso.{u, v} B j).hom.app F).hom.app
            (op ((smallEtaleBaseChange B j).obj (openCovarianceSupportObject B f V D))) ≫
          ((openRestriction B j).obj F).obj.map (covarianceOpenMap B j f V E D hD).op) :=
      Category.assoc _ _ _
    _ = F.obj.map ((openPostcomposeAdjunction B j).counit.app
          (openCovarianceSupportObject B f V D)).op ≫
          (F.obj.map ((openPostcompose B j).map
            (covarianceOpenMap B j f V E D hD)).op ≫
          ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
            (op (openCovarianceSupportObject B (j ≫ f) V E))) :=
      congrArg (fun z => F.obj.map ((openPostcomposeAdjunction B j).counit.app
        (openCovarianceSupportObject B f V D)).op ≫ z) hnat.symm
    _ = (F.obj.map ((openPostcomposeAdjunction B j).counit.app
            (openCovarianceSupportObject B f V D)).op ≫
          F.obj.map ((openPostcompose B j).map (covarianceOpenMap B j f V E D hD)).op) ≫
          ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
            (op (openCovarianceSupportObject B (j ≫ f) V E)) :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z => z ≫ ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
      (op (openCovarianceSupportObject B (j ≫ f) V E))) hcounit

/-- Components of an isomorphism of abelian sheaves are injective. -/
public theorem sheafIso_app_injective {C : Type w₁} [Category.{w₂} C]
    {J : GrothendieckTopology C} {G H : Sheaf J AddCommGrpCat.{w₃}} (e : G ≅ H)
    (U : Cᵒᵖ) : Function.Injective (e.hom.hom.app U) := by
  have hinv (z : G.obj.obj U) : e.inv.hom.app U (e.hom.hom.app U z) = z := by
    have h0 := congrArg (fun φ : G ⟶ G => φ.hom.app U) e.hom_inv_id
    have h1 : (e.hom.hom.app U ≫ e.inv.hom.app U) z = z :=
      ConcreteCategory.congr_hom h0 z
    rw [ConcreteCategory.comp_apply] at h1
    exact h1
  intro x y hxy
  rw [← hinv x, ← hinv y, hxy]

/-- Restriction through the unit of the restriction adjunction along the comparison of
canonical support opens is injective on sections supported on the image support. -/
public theorem unit_covarianceOpenMap_injective (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (D : FiniteSupport B f V)
    (hD : D.1 = (openBaseChangeHom B j f V).base '' E.1) :
    Function.Injective (fun t : supportedSections B X.obj X.property F (baseChange B f V) D.1
      (finiteSupport_isLocallyClosed B f V D) =>
        ((openRestriction B j).obj F).obj.map (covarianceOpenMap B j f V E D hD).op
          ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
            AddCommGrpCat.{max (u + 1) v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op (openCovarianceSupportObject B f V D)) t.val)) := by
  have key (t : supportedSections B X.obj X.property F (baseChange B f V) D.1
      (finiteSupport_isLocallyClosed B f V D)) :
      ((openRestriction B j).obj F).obj.map (covarianceOpenMap B j f V E D hD).op
          ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
            AddCommGrpCat.{max (u + 1) v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op (openCovarianceSupportObject B f V D)) t.val) =
        ((openRestrictionIso.{u, v} B j).hom.app F).hom.app
          (op (openCovarianceSupportObject B (j ≫ f) V E))
          (F.obj.map (covarianceTargetOpenMap B j f V E D hD).op t.val) :=
    (ConcreteCategory.comp_apply _ _ t.val).symm.trans
      ((ConcreteCategory.congr_hom
        (unit_comp_covarianceOpenMap.{u, v} B j f F V E D hD) t.val).trans
        (ConcreteCategory.comp_apply _ _ t.val))
  exact fun s t hst => covarianceTargetOpenMap_restrict_injective B j f F V E D hD
    (sheafIso_app_injective ((openRestrictionIso.{u, v} B j).app F)
      (op (openCovarianceSupportObject B (j ≫ f) V E)) ((key s).symm.trans (hst.trans (key t))))

end Uniqueness

section SpecUnique

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The contribution of a covariance datum on a finite-support generator to the colimit does
not depend on the datum: its support is the image of the original support, its comparison of
canonical support opens is determined by compatibility with the open inclusions, and its
extension of supported sections is then determined by restricting back. -/
public theorem covarianceGeneratorData_ι_eq (V : SmallEtale B Y.obj Y.property)
    (E : FiniteSupport B (j ≫ f) V) (d d' : CovarianceGeneratorData B j f F V E) :
    AddCommGrpCat.ofHom d.sectionMap ≫ colimit.ι (finiteSupportDiagram B f F V) d.support =
      AddCommGrpCat.ofHom d'.sectionMap ≫
        colimit.ι (finiteSupportDiagram B f F V) d'.support := by
  obtain ⟨D, hD, φ, om, hom, hap⟩ := d
  obtain ⟨D', hD', φ', om', hom', hap'⟩ := d'
  have hDD : D = D' := Subtype.ext (hD.trans hD'.symm)
  subst hDD
  have hom2 := eq_covarianceOpenMap B j f V E D hD om hom
  subst hom2
  have hom3 := eq_covarianceOpenMap B j f V E D hD' om' hom'
  subst hom3
  have hφ : φ = φ' :=
    AddMonoidHom.ext fun s => unit_covarianceOpenMap_injective.{u, v} B j f F V E D hD
      ((hap s).trans (hap' s).symm)
  subst hφ
  rfl

/-- The characterization of the covariance map on finite-support generators determines it. -/
public theorem openCovariancePresheafMapSpec_eq
    {α β : openFiniteSupportPushforward.{u, v} B j f ⟶
      wholeFiniteSupportPushforward.{u, v} B f}
    (hα : OpenCovariancePresheafMapSpec B j f α)
    (hβ : OpenCovariancePresheafMapSpec B j f β) : α = β := by
  apply NatTrans.ext
  funext G
  apply NatTrans.ext
  funext V
  apply finiteSupportPushforwardGenerator_hom_ext B (j ≫ f) ((openRestriction B j).obj G) V.unop
  intro E
  obtain ⟨d, hd⟩ := hα G V.unop E
  obtain ⟨d', hd'⟩ := hβ G V.unop E
  have h := hd.trans
    ((covarianceGeneratorData_ι_eq.{u, v} B j f G V.unop E d d').trans hd'.symm)
  refine (cancel_mono (eqToHom ((finiteSupportPushforward.{u, max (u + 1) v} B f
    (fun _ => inferInstance)).property.obj_eq G V.unop))).1 ?_
  simp only [finiteSupportPushforwardGenerator, Category.assoc]
  simpa only [Category.assoc] using h

end SpecUnique

section TransitivityHelpers

variable (B : BigEtaleSite.{u}) {X'' X' X Y : B.Scheme} (j : X'' ⟶ X') (k : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)] (f : X ⟶ Y)

/-- Post-composition with a composite open immersion is the composite of the
post-compositions, on morphisms. -/
public theorem openPostcompose_map_comp {Z Z' : SmallEtale B X''.obj X''.property}
    (a : Z' ⟶ Z) :
    (openPostcompose B (j ≫ k)).map a =
      (openPostcompose B k).map ((openPostcompose B j).map a) := rfl

/-- The natural transformations of base-change functors induced by two nested open immersions
compose to the one induced by the composite. -/
public theorem openBaseChangeMap_trans (V : SmallEtale B Y.obj Y.property) :
    (openPostcompose B k).map ((openBaseChangeMap B j (k ≫ f)).app V) ≫
        (openBaseChangeMap B k f).app V =
      (openBaseChangeMap B (j ≫ k) f).app V := by
  apply (SmallEtale.toScheme B X.obj X.property).map_injective
  rw [Functor.map_comp, openPostcompose_toScheme_map, openBaseChangeMap_toScheme,
    openBaseChangeMap_toScheme]
  exact (openBaseChangeHom_trans B j k f V).trans
    (openBaseChangeMap_toScheme B (j ≫ k) f V).symm

/-- The counit of the adjunction for a composite open immersion factors through the
comparison of successive small étale base changes. -/
public theorem openPostcompose_counit_compIso (W : SmallEtale B X.obj X.property) :
    (openPostcompose B k).map ((openPostcompose B j).map
          ((smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W)) ≫
        (openPostcomposeAdjunction B (j ≫ k)).counit.app W =
      (openPostcompose B k).map ((openPostcomposeAdjunction B j).counit.app
        ((smallEtaleBaseChange B k).obj W)) ≫
        (openPostcomposeAdjunction B k).counit.app W := by
  have hl : ((SmallEtale.inclusion B X''.obj X''.property).map
        ((smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W)).left ≫
        pullback.fst W.obj.hom (j ≫ k) =
      pullback.fst (((smallEtaleBaseChange B k).obj W).obj.hom) j ≫
        pullback.fst W.obj.hom k := by
    rw [smallEtaleBaseChange_compIso_app]
    exact Over.pullbackComp_inv_app_left_fst j k W.obj
  exact (SmallEtale.inclusion B X.obj X.property).map_injective (Over.OverMorphism.ext hl)

/-- **The comparison of canonical opens composes.** If the comparison morphisms of two nested
open immersions are each compatible with the open inclusions and the induced open immersions of
base changes, then so is the morphism built from them for the composite open immersion. -/
public theorem comp_openMap_fac (V : SmallEtale B Y.obj Y.property)
    {A : SmallEtale B X''.obj X''.property} {Wj : SmallEtale B X'.obj X'.property}
    {W : SmallEtale B X.obj X.property}
    (aj : A ⟶ (smallEtaleBaseChange B j).obj Wj)
    (ak : Wj ⟶ (smallEtaleBaseChange B k).obj W)
    (iE : A ⟶ baseChange B ((j ≫ k) ≫ f) V) (ij : Wj ⟶ baseChange B (k ≫ f) V)
    (iD : W ⟶ baseChange B f V)
    (hj : (openPostcompose B j).map aj ≫
        (openPostcomposeAdjunction B j).counit.app Wj ≫ ij =
      (openPostcompose B j).map iE ≫ (openBaseChangeMap B j (k ≫ f)).app V)
    (hk : (openPostcompose B k).map ak ≫
        (openPostcomposeAdjunction B k).counit.app W ≫ iD =
      (openPostcompose B k).map ij ≫ (openBaseChangeMap B k f).app V) :
    (openPostcompose B k).map ((openPostcompose B j).map
          (aj ≫ (smallEtaleBaseChange B j).map ak ≫
            (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W)) ≫
        (openPostcomposeAdjunction B (j ≫ k)).counit.app W ≫ iD =
      (openPostcompose B k).map ((openPostcompose B j).map iE) ≫
        (openBaseChangeMap B (j ≫ k) f).app V := by
  have hF := openPostcompose_counit_compIso B j k W
  have hF' : ∀ {Z : SmallEtale B X.obj X.property} (x : W ⟶ Z),
      (openPostcompose B k).map ((openPostcompose B j).map
          ((smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W)) ≫
        (openPostcomposeAdjunction B (j ≫ k)).counit.app W ≫ x =
      (openPostcompose B k).map ((openPostcomposeAdjunction B j).counit.app
          ((smallEtaleBaseChange B k).obj W)) ≫
        (openPostcomposeAdjunction B k).counit.app W ≫ x := fun x =>
    (Category.assoc _ _ x).symm.trans
      ((congrArg (fun z => z ≫ x) hF).trans (Category.assoc _ _ x))
  have hnat := (openPostcomposeAdjunction B j).counit.naturality ak
  simp only [Functor.comp_map, Functor.id_map] at hnat
  have hA := openBaseChangeMap_trans B j k f V
  calc
    (openPostcompose B k).map ((openPostcompose B j).map
            (aj ≫ (smallEtaleBaseChange B j).map ak ≫
              (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W)) ≫
          (openPostcomposeAdjunction B (j ≫ k)).counit.app W ≫ iD
        = (openPostcompose B k).map ((openPostcompose B j).map aj) ≫
            (openPostcompose B k).map ((openPostcompose B j).map
              ((smallEtaleBaseChange B j).map ak)) ≫
            (openPostcompose B k).map ((openPostcompose B j).map
              ((smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W)) ≫
            (openPostcomposeAdjunction B (j ≫ k)).counit.app W ≫ iD := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (openPostcompose B k).map ((openPostcompose B j).map aj) ≫
          (openPostcompose B k).map ((openPostcompose B j).map
            ((smallEtaleBaseChange B j).map ak)) ≫
          (openPostcompose B k).map ((openPostcomposeAdjunction B j).counit.app
            ((smallEtaleBaseChange B k).obj W)) ≫
          (openPostcomposeAdjunction B k).counit.app W ≫ iD := by
      rw [hF' iD]
    _ = (openPostcompose B k).map ((openPostcompose B j).map aj) ≫
          (openPostcompose B k).map ((openPostcompose B j).map
              ((smallEtaleBaseChange B j).map ak) ≫
            (openPostcomposeAdjunction B j).counit.app
              ((smallEtaleBaseChange B k).obj W)) ≫
          (openPostcomposeAdjunction B k).counit.app W ≫ iD := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (openPostcompose B k).map ((openPostcompose B j).map aj) ≫
          (openPostcompose B k).map
            ((openPostcomposeAdjunction B j).counit.app Wj ≫ ak) ≫
          (openPostcomposeAdjunction B k).counit.app W ≫ iD := by
      rw [hnat]
    _ = (openPostcompose B k).map ((openPostcompose B j).map aj) ≫
          (openPostcompose B k).map ((openPostcomposeAdjunction B j).counit.app Wj) ≫
          (openPostcompose B k).map ak ≫
          (openPostcomposeAdjunction B k).counit.app W ≫ iD := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (openPostcompose B k).map ((openPostcompose B j).map aj) ≫
          (openPostcompose B k).map ((openPostcomposeAdjunction B j).counit.app Wj) ≫
          (openPostcompose B k).map ij ≫ (openBaseChangeMap B k f).app V := by
      rw [hk]
    _ = (openPostcompose B k).map ((openPostcompose B j).map aj ≫
            (openPostcomposeAdjunction B j).counit.app Wj ≫ ij) ≫
          (openBaseChangeMap B k f).app V := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (openPostcompose B k).map ((openPostcompose B j).map iE ≫
            (openBaseChangeMap B j (k ≫ f)).app V) ≫
          (openBaseChangeMap B k f).app V := by
      rw [hj]
    _ = (openPostcompose B k).map ((openPostcompose B j).map iE) ≫
          (openPostcompose B k).map ((openBaseChangeMap B j (k ≫ f)).app V) ≫
          (openBaseChangeMap B k f).app V :=
      (congrArg (fun z => z ≫ (openBaseChangeMap B k f).app V)
        ((openPostcompose B k).map_comp _ _)).trans (Category.assoc _ _ _)
    _ = _ :=
      congrArg (fun z => (openPostcompose B k).map ((openPostcompose B j).map iE) ≫ z) hA

end TransitivityHelpers

section CompIso

variable (B : BigEtaleSite.{u}) {X'' X' X Y : B.Scheme} (j : X'' ⟶ X') (k : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)]

/-- Restricting an abelian sheaf to two nested open subschemes in two steps or in one step
along the composite open immersion gives canonically isomorphic sheaves. -/
public def openRestrictionCompIso :
    openRestriction.{u, v} B (j ≫ k) ≅
      openRestriction.{u, v} B k ⋙ openRestriction.{u, v} B j :=
  (smallEtaleSheafPullbackCompIso B X'' X' X j k AddCommGrpCat.{max (u + 1) v}).symm

variable (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]

/-- The induced comparison of the finite-support direct-image presheaves over `Y`. -/
public def openFiniteSupportCompIso :
    openFiniteSupportPushforward.{u, v} B (j ≫ k) f ≅
      openRestriction.{u, v} B k ⋙ openFiniteSupportPushforward.{u, v} B j (k ≫ f) :=
  Functor.isoWhiskerRight (openRestrictionCompIso.{u, v} B j k)
      (finiteSupportPushforward.{u, max (u + 1) v} B ((j ≫ k) ≫ f)
        (fun _ => inferInstance)).val ≪≫
    Functor.associator _ _ _

/-- The comparison of the finite-support direct-image presheaves is, on each abelian sheaf, the
image of the comparison of restrictions. -/
public theorem openFiniteSupportCompIso_hom_app
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (openFiniteSupportCompIso.{u, v} B j k f).hom.app G =
      (finiteSupportPushforward.{u, max (u + 1) v} B ((j ≫ k) ≫ f)
        (fun _ => inferInstance)).val.map
          ((openRestrictionCompIso.{u, v} B j k).hom.app G) :=
  Category.comp_id _

/-- The induced comparison of the direct images with compact support. -/
public def openShriekCompIso :
    openShriekPushforward.{u, v} B (j ≫ k) f ≅
      openRestriction.{u, v} B k ⋙ openShriekPushforward.{u, v} B j (k ≫ f) :=
  Functor.isoWhiskerRight (openFiniteSupportCompIso.{u, v} B j k f)
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
        AddCommGrpCat.{max (u + 1) v}) ≪≫
    Functor.associator _ _ _

end CompIso

section UnitCoherence

variable (B : BigEtaleSite.{u}) {X'' X' X : B.Scheme} (j : X'' ⟶ X') (k : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)] in
/-- The two descriptions of restriction to a nested open subscheme agree on germs of sections
pulled back through the units of the restriction adjunctions: restricting in two steps and
comparing is the same as restricting in one step. -/
public theorem openRestrictionCompIso_unit (W : SmallEtale B X.obj X.property)
    (t : F.obj.obj (op W)) :
    ((openRestriction.{u, v} B j).obj ((openRestriction.{u, v} B k).obj F)).obj.map
        ((smallEtaleBaseChange_compIso B X'' X' X j k).val.app W).inv.op
        ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
              AddCommGrpCat.{max (u + 1) v}
              (SmallEtale.topology B X'.obj X'.property)
              (SmallEtale.topology B X''.obj X''.property)).unit.app
            ((openRestriction.{u, v} B k).obj F)).hom.app
          (op ((smallEtaleBaseChange B k).obj W))
          ((((smallEtaleBaseChange B k).sheafAdjunctionContinuous
              AddCommGrpCat.{max (u + 1) v}
              (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) t)) =
      ((openRestrictionCompIso.{u, v} B j k).hom.app F).hom.app
        (op ((smallEtaleBaseChange B (j ≫ k)).obj W))
        ((((smallEtaleBaseChange B (j ≫ k)).sheafAdjunctionContinuous
            AddCommGrpCat.{max (u + 1) v}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B X''.obj X''.property)).unit.app F).hom.app (op W) t) := by
  have hcoh := CategoryTheory.unit_conjugateEquiv
    (((smallEtaleBaseChange B k).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B X'.obj X'.property)).comp
      ((smallEtaleBaseChange B j).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B X'.obj X'.property)
        (SmallEtale.topology B X''.obj X''.property)))
    ((smallEtaleBaseChange B (j ≫ k)).sheafAdjunctionContinuous
      AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B X''.obj X''.property))
    (smallEtaleSheafPullbackCompIso B X'' X' X j k AddCommGrpCat.{max (u + 1) v}).inv F
  simp only [smallEtaleSheafPullbackCompIso, Functor.sheafPullbackComp',
    CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
    CategoryTheory.Adjunction.comp_unit_app] at hcoh
  have hcohVal := ConcreteCategory.congr_hom (congrArg (fun m => m.hom.app (op W)) hcoh) t
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at hcohVal
  exact hcohVal

end UnitCoherence

section Bridge

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] (f : X ⟶ Y)

/-- The compatibility of a comparison of canonical opens with the open inclusions, read in the
small étale site of the source or on the underlying schemes: the two forms are equivalent
because the functor to schemes is faithful. -/
public theorem openMap_fac_iff (V : SmallEtale B Y.obj Y.property)
    {A : SmallEtale B X'.obj X'.property} {W : SmallEtale B X.obj X.property}
    (om : A ⟶ (smallEtaleBaseChange B j).obj W)
    (iE : A ⟶ baseChange B (j ≫ f) V) (iD : W ⟶ baseChange B f V) :
    ((openPostcompose B j).map om ≫
          (openPostcomposeAdjunction B j).counit.app W ≫ iD =
        (openPostcompose B j).map iE ≫ (openBaseChangeMap B j f).app V) ↔
      ((SmallEtale.toScheme B X'.obj X'.property).map om ≫
          B.inclusion.map (pullback.fst W.obj.hom j) ≫
          (SmallEtale.toScheme B X.obj X.property).map iD =
        (SmallEtale.toScheme B X'.obj X'.property).map iE ≫ openBaseChangeHom B j f V) := by
  have hL : (SmallEtale.toScheme B X.obj X.property).map
        ((openPostcompose B j).map om ≫
          (openPostcomposeAdjunction B j).counit.app W ≫ iD) =
      (SmallEtale.toScheme B X'.obj X'.property).map om ≫
        B.inclusion.map (pullback.fst W.obj.hom j) ≫
        (SmallEtale.toScheme B X.obj X.property).map iD :=
    (((SmallEtale.toScheme B X.obj X.property).map_comp _ _).trans
      (congrArg
        (fun z => (SmallEtale.toScheme B X.obj X.property).map ((openPostcompose B j).map om) ≫ z)
        (((SmallEtale.toScheme B X.obj X.property).map_comp _ _).trans
          (congrArg (fun z => z ≫ (SmallEtale.toScheme B X.obj X.property).map iD)
            (openPostcomposeAdjunction_counit_toScheme B j W))))).trans
      (congrArg (fun z => z ≫ B.inclusion.map (pullback.fst W.obj.hom j) ≫
          (SmallEtale.toScheme B X.obj X.property).map iD)
        (openPostcompose_toScheme_map B j om))
  have hR : (SmallEtale.toScheme B X.obj X.property).map
        ((openPostcompose B j).map iE ≫ (openBaseChangeMap B j f).app V) =
      (SmallEtale.toScheme B X'.obj X'.property).map iE ≫ openBaseChangeHom B j f V :=
    (((SmallEtale.toScheme B X.obj X.property).map_comp _ _).trans
      (congrArg
        (fun z => (SmallEtale.toScheme B X.obj X.property).map ((openPostcompose B j).map iE) ≫ z)
        (openBaseChangeMap_toScheme B j f V))).trans
      (congrArg (fun z => z ≫ openBaseChangeHom B j f V)
        (openPostcompose_toScheme_map B j iE))
  constructor
  · intro h
    exact hL.symm.trans
      ((congrArg (SmallEtale.toScheme B X.obj X.property).map h).trans hR)
  · intro h
    exact (SmallEtale.toScheme B X.obj X.property).map_injective (hL.trans (h.trans hR.symm))

end Bridge

section SectionCoherence

variable (B : BigEtaleSite.{u}) {X'' X' X : B.Scheme} (j : X'' ⟶ X') (k : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

omit [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)] in
/-- Restricting a section of `F` through the unit of the one-step restriction adjunction along
the comparison morphism of the composite is, after comparing the two descriptions of
restriction, the two-step restriction through the two units. -/
public theorem comp_restrict_unit
    {A : SmallEtale B X''.obj X''.property} {Wj : SmallEtale B X'.obj X'.property}
    {W : SmallEtale B X.obj X.property}
    (aj : A ⟶ (smallEtaleBaseChange B j).obj Wj)
    (ak : Wj ⟶ (smallEtaleBaseChange B k).obj W) (t : F.obj.obj (op W)) :
    ((openRestrictionCompIso.{u, v} B j k).hom.app F).hom.app (op A)
        (((openRestriction.{u, v} B (j ≫ k)).obj F).obj.map
          (aj ≫ (smallEtaleBaseChange B j).map ak ≫
            (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W).op
          ((((smallEtaleBaseChange B (j ≫ k)).sheafAdjunctionContinuous
              AddCommGrpCat.{max (u + 1) v}
              (SmallEtale.topology B X.obj X.property)
              (SmallEtale.topology B X''.obj X''.property)).unit.app F).hom.app (op W) t)) =
      ((openRestriction.{u, v} B j).obj ((openRestriction.{u, v} B k).obj F)).obj.map aj.op
        ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
            AddCommGrpCat.{max (u + 1) v}
            (SmallEtale.topology B X'.obj X'.property)
            (SmallEtale.topology B X''.obj X''.property)).unit.app
              ((openRestriction.{u, v} B k).obj F)).hom.app (op Wj)
          (((openRestriction.{u, v} B k).obj F).obj.map ak.op
            ((((smallEtaleBaseChange B k).sheafAdjunctionContinuous
                AddCommGrpCat.{max (u + 1) v}
                (SmallEtale.topology B X.obj X.property)
                (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app (op W) t))) := by
  have hiso : (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W ≫
      ((smallEtaleBaseChange_compIso B X'' X' X j k).val.app W).inv = 𝟙 _ :=
    (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom_inv_id_app W
  have hcancel : (aj ≫ (smallEtaleBaseChange B j).map ak ≫
        (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W) ≫
      ((smallEtaleBaseChange_compIso B X'' X' X j k).val.app W).inv =
    aj ≫ (smallEtaleBaseChange B j).map ak := by
    rw [Category.assoc, Category.assoc, hiso]
    exact congrArg (fun z => aj ≫ z) (Category.comp_id _)
  have hmap : ((openRestriction.{u, v} B j).obj
        ((openRestriction.{u, v} B k).obj F)).obj.map
      (aj ≫ (smallEtaleBaseChange B j).map ak).op =
      ((openRestriction.{u, v} B j).obj ((openRestriction.{u, v} B k).obj F)).obj.map
          ((smallEtaleBaseChange B j).map ak).op ≫
        ((openRestriction.{u, v} B j).obj ((openRestriction.{u, v} B k).obj F)).obj.map aj.op := by
    rw [op_comp, Functor.map_comp]
  have hunitnat := ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
      AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B X'.obj X'.property)
      (SmallEtale.topology B X''.obj X''.property)).unit.app
        ((openRestriction.{u, v} B k).obj F)).hom.naturality ak.op)
  have hnatε := ((openRestrictionCompIso.{u, v} B j k).hom.app F).hom.naturality
    (aj ≫ (smallEtaleBaseChange B j).map ak ≫
      (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W).op
  calc
    _ = ((openRestriction.{u, v} B j).obj ((openRestriction.{u, v} B k).obj F)).obj.map
          (aj ≫ (smallEtaleBaseChange B j).map ak ≫
            (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W).op
          (((openRestrictionCompIso.{u, v} B j k).hom.app F).hom.app
            (op ((smallEtaleBaseChange B (j ≫ k)).obj W))
            ((((smallEtaleBaseChange B (j ≫ k)).sheafAdjunctionContinuous
                AddCommGrpCat.{max (u + 1) v}
                (SmallEtale.topology B X.obj X.property)
                (SmallEtale.topology B X''.obj X''.property)).unit.app F).hom.app
              (op W) t)) :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom hnatε _).trans (ConcreteCategory.comp_apply _ _ _))
    _ = ((openRestriction.{u, v} B j).obj ((openRestriction.{u, v} B k).obj F)).obj.map
          (aj ≫ (smallEtaleBaseChange B j).map ak ≫
            (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W).op
          (((openRestriction.{u, v} B j).obj
              ((openRestriction.{u, v} B k).obj F)).obj.map
            ((smallEtaleBaseChange_compIso B X'' X' X j k).val.app W).inv.op
            ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
                AddCommGrpCat.{max (u + 1) v}
                (SmallEtale.topology B X'.obj X'.property)
                (SmallEtale.topology B X''.obj X''.property)).unit.app
                  ((openRestriction.{u, v} B k).obj F)).hom.app
              (op ((smallEtaleBaseChange B k).obj W))
              ((((smallEtaleBaseChange B k).sheafAdjunctionContinuous
                  AddCommGrpCat.{max (u + 1) v}
                  (SmallEtale.topology B X.obj X.property)
                  (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
                (op W) t))) :=
      congrArg (((openRestriction.{u, v} B j).obj
          ((openRestriction.{u, v} B k).obj F)).obj.map
        (aj ≫ (smallEtaleBaseChange B j).map ak ≫
          (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app W).op)
        (openRestrictionCompIso_unit.{u, v} B j k F W t).symm
    _ = ((openRestriction.{u, v} B j).obj ((openRestriction.{u, v} B k).obj F)).obj.map
          (aj ≫ (smallEtaleBaseChange B j).map ak).op
          ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
              AddCommGrpCat.{max (u + 1) v}
              (SmallEtale.topology B X'.obj X'.property)
              (SmallEtale.topology B X''.obj X''.property)).unit.app
                ((openRestriction.{u, v} B k).obj F)).hom.app
            (op ((smallEtaleBaseChange B k).obj W))
            ((((smallEtaleBaseChange B k).sheafAdjunctionContinuous
                AddCommGrpCat.{max (u + 1) v}
                (SmallEtale.topology B X.obj X.property)
                (SmallEtale.topology B X'.obj X'.property)).unit.app F).hom.app
              (op W) t)) :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        (ConcreteCategory.congr_hom
          ((((openRestriction.{u, v} B j).obj
              ((openRestriction.{u, v} B k).obj F)).obj.map_comp _ _).symm.trans
            (congrArg (fun m => ((openRestriction.{u, v} B j).obj
                ((openRestriction.{u, v} B k).obj F)).obj.map
              (Opposite.op m)) hcancel)) _)
    _ = _ :=
      (ConcreteCategory.congr_hom hmap _).trans
        ((ConcreteCategory.comp_apply _ _ _).trans
          (congrArg (((openRestriction.{u, v} B j).obj
              ((openRestriction.{u, v} B k).obj F)).obj.map aj.op)
            ((ConcreteCategory.comp_apply _ _ _).symm.trans
              ((ConcreteCategory.congr_hom hunitnat.symm _).trans
                (ConcreteCategory.comp_apply _ _ _)))))

end SectionCoherence

section Transitivity

variable (B : BigEtaleSite.{u}) {X'' X' X Y : B.Scheme} (j : X'' ⟶ X') (k : X' ⟶ X)
  [IsOpenImmersion (B.inclusion.map j)] [IsOpenImmersion (B.inclusion.map k)]
  (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (V : SmallEtale B Y.obj Y.property)

/-- The covariance datum of the composite open immersion on a finite-support generator, built
from the covariance data of the two factors: the supports and the extensions of supported
sections compose, and so do the comparisons of canonical support opens. -/
public def compCovarianceGeneratorData (E : FiniteSupport B ((j ≫ k) ≫ f) V)
    (dj : CovarianceGeneratorData B j (k ≫ f) ((openRestriction.{u, v} B k).obj F) V E)
    (dk : CovarianceGeneratorData B k f F V dj.support) :
    CovarianceGeneratorData B (j ≫ k) f F V E where
  support := dk.support
  support_eq := by
    have hpt : ∀ x, (openBaseChangeHom B k f V).base
          ((openBaseChangeHom B j (k ≫ f) V).base x) =
        (openBaseChangeHom B (j ≫ k) f V).base x :=
      fun x => congrArg (fun m => m.base x) (openBaseChangeHom_trans B j k f V)
    have hcomp : (openBaseChangeHom B (j ≫ k) f V).base '' E.1 =
        (openBaseChangeHom B k f V).base ''
          ((openBaseChangeHom B j (k ≫ f) V).base '' E.1) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro y ⟨x, hx, rfl⟩
        exact ⟨(openBaseChangeHom B j (k ≫ f) V).base x, ⟨x, hx, rfl⟩, hpt x⟩
      · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, (hpt x).symm⟩
    rw [hcomp, ← dj.support_eq]
    exact dk.support_eq
  sectionMap := dk.sectionMap.comp (dj.sectionMap.comp
    (supportedSectionsSheafMap B X''.obj X''.property
      ((openRestrictionCompIso.{u, v} B j k).hom.app F)
      (baseChange B ((j ≫ k) ≫ f) V) E.1
      (finiteSupport_isLocallyClosed B ((j ≫ k) ≫ f) V E)))
  openMap := dj.openMap ≫ (smallEtaleBaseChange B j).map dk.openMap ≫
    (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app
      (openCovarianceSupportObject B f V dk.support)
  openMap_commutes := by
    have hj : (openPostcompose B j).map dj.openMap ≫
          (openPostcomposeAdjunction B j).counit.app
              (openCovarianceSupportObject B (k ≫ f) V dj.support) ≫
            openObjectι B X'.obj X'.property (baseChange B (k ≫ f) V)
              (openCovarianceSupportOpen B (k ≫ f) V dj.support) =
        (openPostcompose B j).map (openObjectι B X''.obj X''.property
            (baseChange B ((j ≫ k) ≫ f) V)
            (openCovarianceSupportOpen B ((j ≫ k) ≫ f) V E)) ≫
          (openBaseChangeMap B j (k ≫ f)).app V := by
      refine (openMap_fac_iff B j (k ≫ f) V dj.openMap _ _).2 ?_
      exact (congrArg (fun z => (SmallEtale.toScheme B X''.obj X''.property).map dj.openMap ≫
            B.inclusion.map (pullback.fst
              ((openCovarianceSupportObject B (k ≫ f) V dj.support).obj.hom) j) ≫ z)
          (openObjectι_map B X'.obj X'.property (baseChange B (k ≫ f) V)
            (openCovarianceSupportOpen B (k ≫ f) V dj.support))).trans
        (dj.openMap_commutes.trans
          (congrArg (fun z => z ≫ openBaseChangeHom B j (k ≫ f) V)
            (openObjectι_map B X''.obj X''.property (baseChange B ((j ≫ k) ≫ f) V)
              (openCovarianceSupportOpen B ((j ≫ k) ≫ f) V E)).symm))
    have hk : (openPostcompose B k).map dk.openMap ≫
          (openPostcomposeAdjunction B k).counit.app
              (openCovarianceSupportObject B f V dk.support) ≫
            openObjectι B X.obj X.property (baseChange B f V)
              (openCovarianceSupportOpen B f V dk.support) =
        (openPostcompose B k).map (openObjectι B X'.obj X'.property
            (baseChange B (k ≫ f) V)
            (openCovarianceSupportOpen B (k ≫ f) V dj.support)) ≫
          (openBaseChangeMap B k f).app V := by
      refine (openMap_fac_iff B k f V dk.openMap _ _).2 ?_
      exact (congrArg (fun z => (SmallEtale.toScheme B X'.obj X'.property).map dk.openMap ≫
            B.inclusion.map (pullback.fst
              ((openCovarianceSupportObject B f V dk.support).obj.hom) k) ≫ z)
          (openObjectι_map B X.obj X.property (baseChange B f V)
            (openCovarianceSupportOpen B f V dk.support))).trans
        (dk.openMap_commutes.trans
          (congrArg (fun z => z ≫ openBaseChangeHom B k f V)
            (openObjectι_map B X'.obj X'.property (baseChange B (k ≫ f) V)
              (openCovarianceSupportOpen B (k ≫ f) V dj.support)).symm))
    have hres := (openMap_fac_iff B (j ≫ k) f V
        (dj.openMap ≫ (smallEtaleBaseChange B j).map dk.openMap ≫
          (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app
            (openCovarianceSupportObject B f V dk.support))
        (openObjectι B X''.obj X''.property (baseChange B ((j ≫ k) ≫ f) V)
          (openCovarianceSupportOpen B ((j ≫ k) ≫ f) V E))
        (openObjectι B X.obj X.property (baseChange B f V)
          (openCovarianceSupportOpen B f V dk.support))).1
      (comp_openMap_fac B j k f V dj.openMap dk.openMap
        (openObjectι B X''.obj X''.property (baseChange B ((j ≫ k) ≫ f) V)
          (openCovarianceSupportOpen B ((j ≫ k) ≫ f) V E))
        (openObjectι B X'.obj X'.property (baseChange B (k ≫ f) V)
          (openCovarianceSupportOpen B (k ≫ f) V dj.support))
        (openObjectι B X.obj X.property (baseChange B f V)
          (openCovarianceSupportOpen B f V dk.support)) hj hk)
    exact (congrArg (fun z => (SmallEtale.toScheme B X''.obj X''.property).map
            (dj.openMap ≫ (smallEtaleBaseChange B j).map dk.openMap ≫
              (smallEtaleBaseChange_compIso B X'' X' X j k).val.hom.app
                (openCovarianceSupportObject B f V dk.support)) ≫
            B.inclusion.map (pullback.fst
              ((openCovarianceSupportObject B f V dk.support).obj.hom) (j ≫ k)) ≫ z)
          (openObjectι_map B X.obj X.property (baseChange B f V)
            (openCovarianceSupportOpen B f V dk.support))).symm.trans
      (hres.trans (congrArg (fun z => z ≫ openBaseChangeHom B (j ≫ k) f V)
        (openObjectι_map B X''.obj X''.property (baseChange B ((j ≫ k) ≫ f) V)
          (openCovarianceSupportOpen B ((j ≫ k) ≫ f) V E))))
  sectionMap_apply := by
    intro s
    refine sheafIso_app_injective ((openRestrictionCompIso.{u, v} B j k).app F)
      (op (openCovarianceSupportObject B ((j ≫ k) ≫ f) V E)) ?_
    refine (comp_restrict_unit.{u, v} B j k F dj.openMap dk.openMap _).trans ?_
    exact (congrArg (fun z => ((openRestriction.{u, v} B j).obj
            ((openRestriction.{u, v} B k).obj F)).obj.map dj.openMap.op
          ((((smallEtaleBaseChange B j).sheafAdjunctionContinuous
              AddCommGrpCat.{max (u + 1) v}
              (SmallEtale.topology B X'.obj X'.property)
              (SmallEtale.topology B X''.obj X''.property)).unit.app
                ((openRestriction.{u, v} B k).obj F)).hom.app
            (op (openCovarianceSupportObject B (k ≫ f) V dj.support)) z))
        (dk.sectionMap_apply (dj.sectionMap
          (supportedSectionsSheafMap B X''.obj X''.property
            ((openRestrictionCompIso.{u, v} B j k).hom.app F)
            (baseChange B ((j ≫ k) ≫ f) V) E.1
            (finiteSupport_isLocallyClosed B ((j ≫ k) ≫ f) V E) s)))).trans
      (dj.sectionMap_apply _)

/-- **Stacks 0F6S, part (3).** Transitivity of covariance for the finite-support direct-image
presheaves: for nested open subschemes of the source, the covariance map of the composite open
immersion is the composite of the two covariance maps, once the two descriptions of restriction
to the smallest open subscheme are identified. -/
@[stacks 0F6S "part (3), transitivity, presheaf form"]
public theorem openCovariancePresheafMap_comp :
    (openFiniteSupportCompIso.{u, v} B j k f).hom ≫
        Functor.whiskerLeft (openRestriction.{u, v} B k)
          (openCovariancePresheafMap.{u, v} B j (k ≫ f)).val ≫
        (openCovariancePresheafMap.{u, v} B k f).val =
      (openCovariancePresheafMap.{u, v} B (j ≫ k) f).val := by
  apply NatTrans.ext
  funext G
  apply NatTrans.ext
  funext VV
  obtain ⟨W⟩ := VV
  apply finiteSupportPushforwardGenerator_hom_ext B ((j ≫ k) ≫ f)
    ((openRestriction.{u, v} B (j ≫ k)).obj G) W
  intro E
  have hα : ((((openFiniteSupportCompIso.{u, v} B j k f).hom ≫
        Functor.whiskerLeft (openRestriction.{u, v} B k)
          (openCovariancePresheafMap.{u, v} B j (k ≫ f)).val ≫
        (openCovariancePresheafMap.{u, v} B k f).val).app G).app (op W)) =
      ((finiteSupportPushforward.{u, max (u + 1) v} B ((j ≫ k) ≫ f)
          (fun _ => inferInstance)).val.map
        ((openRestrictionCompIso.{u, v} B j k).hom.app G)).app (op W) ≫
      covariancePresheafApp B j (k ≫ f) ((openRestriction.{u, v} B k).obj G) W ≫
      covariancePresheafApp B k f G W := by
    change ((openFiniteSupportCompIso.{u, v} B j k f).hom.app G).app (op W) ≫
        covariancePresheafApp B j (k ≫ f) ((openRestriction.{u, v} B k).obj G) W ≫
        covariancePresheafApp B k f G W = _
    rw [openFiniteSupportCompIso_hom_app]
    rfl
  have h1 := finiteSupportPushforwardGenerator_sheaf B ((j ≫ k) ≫ f)
    ((openRestriction.{u, v} B (j ≫ k)).obj G)
    ((openRestriction.{u, v} B j).obj ((openRestriction.{u, v} B k).obj G))
    ((openRestrictionCompIso.{u, v} B j k).hom.app G) W E
  have hA := covariancePresheafApp_generator B j (k ≫ f)
    ((openRestriction.{u, v} B k).obj G) W E
    (imageFiniteSupport B j (k ≫ f) W E)
    (imageFiniteSupport_coe B j (k ≫ f) W E)
  have hC := covariancePresheafApp_generator B k f G W
    (imageFiniteSupport B j (k ≫ f) W E)
    (imageFiniteSupport B k f W (imageFiniteSupport B j (k ≫ f) W E))
    (imageFiniteSupport_coe B k f W (imageFiniteSupport B j (k ≫ f) W E))
  have hM := covariancePresheafApp_generator B (j ≫ k) f G W E
    (imageFiniteSupport B (j ≫ k) f W E)
    (imageFiniteSupport_coe B (j ≫ k) f W E)
  have hEq := covarianceGeneratorData_ι_eq.{u, v} B (j ≫ k) f G W E
    (compCovarianceGeneratorData.{u, v} B j k f G W E
      (covarianceGeneratorData B j (k ≫ f) ((openRestriction.{u, v} B k).obj G) W E)
      (covarianceGeneratorData B k f G W
        (imageFiniteSupport B j (k ≫ f) W E)))
    (covarianceGeneratorData B (j ≫ k) f G W E)
  have hEqGen := (Category.assoc _ _ (eqToHom
      ((finiteSupportPushforward.{u, max (u + 1) v} B f
        (fun _ => inferInstance)).property.obj_eq G W).symm)).symm.trans
    ((congrArg (fun z => z ≫ eqToHom
        ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).property.obj_eq G W).symm) hEq).trans
      (Category.assoc _ _ _))
  have hAC := comp_eq_comp_of_comp hA hC
  refine Eq.trans ?_ hM.symm
  refine (congrArg (fun z => finiteSupportPushforwardGenerator B ((j ≫ k) ≫ f)
    ((openRestriction.{u, v} B (j ≫ k)).obj G) W E ≫ z) hα).trans ?_
  exact (comp_eq_comp_of_comp h1 hAC).trans ((comp_assoc_three _ _ _ _).trans hEqGen)

/-- **Stacks 0F6S, part (3).** Transitivity of covariance after sheafification: for nested open
subschemes of the source, the covariance map of the direct image with compact support along the
composite open immersion is the composite of the two covariance maps. -/
@[stacks 0F6S "part (3), transitivity"]
public theorem openCovarianceShriekMap_comp :
    (openShriekCompIso.{u, v} B j k f).hom ≫
        Functor.whiskerLeft (openRestriction.{u, v} B k)
          (openCovarianceShriekMap.{u, v} B j (k ≫ f)) ≫
        openCovarianceShriekMap.{u, v} B k f =
      openCovarianceShriekMap.{u, v} B (j ≫ k) f := by
  apply NatTrans.ext
  funext G
  have hG := congrArg (fun φ => (presheafToSheaf (SmallEtale.topology B Y.obj Y.property)
      AddCommGrpCat.{max (u + 1) v}).map (φ.app G))
    (openCovariancePresheafMap_comp.{u, v} B j k f)
  simp only [NatTrans.comp_app, Functor.map_comp] at hG
  simp only [NatTrans.comp_app, openShriekCompIso, openCovarianceShriekMap, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc]
  exact hG

end Transitivity

end AlgebraicGeometry.SmallEtale

end
