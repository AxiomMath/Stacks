module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleAlgebras
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleCover
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.SurjectiveBaseChange

/-!
# The lift of affine ind-étale objects along a closed immersion

Let `i : Z ⟶ X` be a closed immersion of affine schemes. Base change along `i` is a functor
`u : X_app ⥤ Z_app` between the affine ind-étale sites, and it has a fully faithful left adjoint
`v : Z_app ⥤ X_app`, the lift: on coordinate rings it is the right adjoint of quotient base
change of ind-étale algebras, Stacks 097P. Consequently every affine ind-étale `Z`-scheme `T` is
the closed fibre `v(T) ×_X Z` of its lift, and a morphism `T ⟶ V ×_X Z` from it into the closed
fibre of an affine ind-étale `X`-scheme `V` comes from a unique morphism `v(T) ⟶ V`.

## Main definitions

* `AlgebraicGeometry.ProEtale.appLift`: the lift `v`.
* `AlgebraicGeometry.ProEtale.appLiftAdjunction`: the adjunction `v ⊣ u`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_adjunction_indEtaleExtendScalars_of_surjective`: extension
  of scalars of ind-étale algebras along a surjective ring map has a fully faithful right
  adjoint (Stacks 097P for a surjection).
* `AlgebraicGeometry.ProEtale.isIso_appLiftAdjunction_unit`: the unit `T ⟶ v(T) ×_X Z` is an
  isomorphism, that is, `v` is fully faithful.

## Implementation notes

The lift is obtained by transporting the adjunction of Stacks 097P along the global-sections
equivalences `AlgebraicGeometry.ProEtale.appGammaEquivalence`, using that on coordinate rings
base change along `i` is extension of scalars along `Γ(X, ⊤) ⟶ Γ(Z, ⊤)`
(`AlgebraicGeometry.ProEtale.appGammaCompExtendScalarsIso`).

## References

* [Stacks Project, Tag 097P](https://stacks.math.columbia.edu/tag/097P)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.ProEtale

/-! ### Stacks 097P for a surjective ring map -/

/-- Restriction of scalars of ind-étale algebras along an isomorphism of rings is fully
faithful. -/
theorem indEtaleRestrictScalarsOfIso_full {R S : CommRingCat.{u}} (e : R ≅ S) :
    (indEtaleRestrictScalarsOfIso e).Full where
  map_surjective {A B} f := by
    refine ⟨ObjectProperty.homMk (Under.homMk f.hom.right ?_), rfl⟩
    have h := Under.w f.hom
    change e.hom ≫ A.obj.hom ≫ f.hom.right = e.hom ≫ B.obj.hom at h
    exact (cancel_epi e.hom).1 h

theorem indEtaleRestrictScalarsOfIso_faithful {R S : CommRingCat.{u}} (e : R ≅ S) :
    (indEtaleRestrictScalarsOfIso e).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    exact congrArg (fun k ↦ k.hom.right) h

/-- **Stacks 097P for a surjective ring map.** Extension of scalars of ind-étale algebras along a
surjective ring map has a fully faithful right adjoint. -/
theorem exists_adjunction_indEtaleExtendScalars_of_surjective {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (hφ : Function.Surjective φ.hom) :
    ∃ (G : IndEtaleAlgebra ↥S ⥤ IndEtaleAlgebra ↥R) (_ : indEtaleExtendScalars φ ⊣ G),
      G.Full ∧ G.Faithful := by
  set I : Ideal ↥R := RingHom.ker φ.hom
  set e : CommRingCat.of (↥R ⧸ I) ≅ S :=
    (RingHom.quotientKerEquivOfSurjective hφ).toCommRingCatIso
  obtain ⟨adjq⟩ := indEtaleBaseChange_hasFullyFaithfulRightAdjoint ↥R I
  obtain ⟨ffq⟩ := indEtaleQuotientLift_fullyFaithful ↥R I
  have := ffq.full
  have := ffq.faithful
  have := indEtaleRestrictScalarsOfIso_full e
  have := indEtaleRestrictScalarsOfIso_faithful e
  have hfac : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ e.hom = φ := by
    ext x
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hφ x
  have hnat : indEtaleExtendScalars φ ≅
      indEtaleExtendScalars (CommRingCat.ofHom (Ideal.Quotient.mk I)) ⋙
        indEtaleExtendScalars e.hom :=
    eqToIso (congrArg (fun ψ ↦ indEtaleExtendScalars ψ) hfac.symm) ≪≫
      indEtaleExtendScalarsComp _ _
  have adjq' : indEtaleExtendScalars (CommRingCat.ofHom (Ideal.Quotient.mk I)) ⊣
      indEtaleQuotientLift ↥R I := by
    rw [indEtaleExtendScalars_quotient]
    exact adjq
  exact ⟨indEtaleRestrictScalarsOfIso e ⋙ indEtaleQuotientLift ↥R I,
    (adjq'.comp (indEtaleExtendScalarsIsoAdj e)).ofNatIsoLeft hnat.symm,
    inferInstance, inferInstance⟩

/-! ### Base change on coordinate rings -/

variable {Z X : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X)

/-- On coordinate rings, base change along a morphism of affine schemes `i : Z ⟶ X` of affine
ind-étale objects is extension of scalars along `Γ(X, ⊤) ⟶ Γ(Z, ⊤)`, naturally. -/
def appGammaCompExtendScalarsIso :
    appGamma X ⋙ indEtaleExtendScalars i.appTop ≅ (appBaseChange i).op ⋙ appGamma Z :=
  NatIso.ofComponents (fun V ↦ indEtaleExtendScalarsAppTopObjIso i V.unop) fun {V V'} f ↦ by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    have hV : IsAffine V.unop.obj.left := V.unop.property.1
    have hV' : IsAffine V'.unop.obj.left := V'.unop.property.1
    have hP := isPushout_appTop_pullback_proEt i V.unop.obj hV
    have hP' := isPushout_appTop_pullback_proEt i V'.unop.obj hV'
    change pushout.desc _ _ _ ≫ hP'.isoPushout.inv = hP.isoPushout.inv ≫ _
    apply pushout.hom_ext
    · refine (pushout.inl_desc_assoc _ _ _ _).trans ?_
      refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hP'.inl_isoPushout_inv)).trans ?_
      refine Eq.trans ?_ ((congrArg (· ≫ _) hP.inl_isoPushout_inv.symm).trans
        (Category.assoc _ _ _))
      change f.unop.hom.left.appTop ≫ (pullback.fst V'.unop.obj.hom i).appTop =
        (pullback.fst V.unop.obj.hom i).appTop ≫
          ((Scheme.proetaleBaseChange i).map f.unop.hom).left.appTop
      have h₁ : ((Scheme.proetaleBaseChange i).map f.unop.hom).left ≫
          pullback.fst V.unop.obj.hom i = pullback.fst V'.unop.obj.hom i ≫ f.unop.hom.left :=
        pullback.lift_fst _ _ _
      exact ((Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop h₁.symm)).trans
        (Scheme.Hom.comp_appTop _ _)
    · refine (pushout.inr_desc_assoc _ _ _ _).trans ?_
      refine hP'.inr_isoPushout_inv.trans ?_
      refine Eq.trans ?_ ((congrArg (· ≫ _) hP.inr_isoPushout_inv.symm).trans
        (Category.assoc _ _ _))
      change (pullback.snd V'.unop.obj.hom i).appTop =
        (pullback.snd V.unop.obj.hom i).appTop ≫
          ((Scheme.proetaleBaseChange i).map f.unop.hom).left.appTop
      have h₂ : ((Scheme.proetaleBaseChange i).map f.unop.hom).left ≫
          pullback.snd V.unop.obj.hom i = pullback.snd V'.unop.obj.hom i :=
        pullback.lift_snd _ _ _
      exact (congrArg Scheme.Hom.appTop h₂.symm).trans (Scheme.Hom.comp_appTop _ _)

/-! ### The lift -/

variable [IsClosedImmersion i]

/-- A right adjoint of extension of scalars along `Γ(X, ⊤) ⟶ Γ(Z, ⊤)`, chosen. -/
def indEtaleExtendScalarsAppTopRightAdjoint :
    IndEtaleAlgebra ↥Γ(Z, ⊤) ⥤ IndEtaleAlgebra ↥Γ(X, ⊤) :=
  (exists_adjunction_indEtaleExtendScalars_of_surjective i.appTop
    (i.app_surjective ⊤ (isAffineOpen_top X))).choose

/-- Extension of scalars along `Γ(X, ⊤) ⟶ Γ(Z, ⊤)` is left adjoint to
`AlgebraicGeometry.ProEtale.indEtaleExtendScalarsAppTopRightAdjoint`. -/
def indEtaleExtendScalarsAppTopAdjunction :
    indEtaleExtendScalars i.appTop ⊣ indEtaleExtendScalarsAppTopRightAdjoint i :=
  (exists_adjunction_indEtaleExtendScalars_of_surjective i.appTop
    (i.app_surjective ⊤ (isAffineOpen_top X))).choose_spec.choose

instance : (indEtaleExtendScalarsAppTopRightAdjoint i).Full :=
  (exists_adjunction_indEtaleExtendScalars_of_surjective i.appTop
    (i.app_surjective ⊤ (isAffineOpen_top X))).choose_spec.choose_spec.1

instance : (indEtaleExtendScalarsAppTopRightAdjoint i).Faithful :=
  (exists_adjunction_indEtaleExtendScalars_of_surjective i.appTop
    (i.app_surjective ⊤ (isAffineOpen_top X))).choose_spec.choose_spec.2

/-- The right adjoint of the opposite of base change along a closed immersion of affine schemes
on the affine ind-étale sites, read through the global-sections equivalences. -/
def appLiftOp : (AppProetale Z)ᵒᵖ ⥤ (AppProetale X)ᵒᵖ :=
  (appGammaEquivalence Z).functor ⋙ indEtaleExtendScalarsAppTopRightAdjoint i ⋙
    (appGammaEquivalence X).inverse

/-- The opposite of base change is left adjoint to `AlgebraicGeometry.ProEtale.appLiftOp`. -/
def appLiftOpAdjunction : (appBaseChange i).op ⊣ appLiftOp i :=
  ((appGammaEquivalence X).toAdjunction.comp ((indEtaleExtendScalarsAppTopAdjunction i).comp
    (appGammaEquivalence Z).symm.toAdjunction)).ofNatIsoLeft
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (appGammaCompExtendScalarsIso i) (appGammaEquivalence Z).inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (appBaseChange i).op (appGammaEquivalence Z).unitIso.symm ≪≫
      Functor.rightUnitor _)

/-- **Stacks 09BK, the lift.** For a closed immersion of affine schemes `i : Z ⟶ X`, the lift
`v : Z_app ⥤ X_app` of affine ind-étale objects. -/
def appLift : AppProetale Z ⥤ AppProetale X := (appLiftOp i).unop

/-- **Stacks 09BK.** The lift is left adjoint to base change on the affine ind-étale sites. -/
def appLiftAdjunction : appLift i ⊣ appBaseChange i := (appLiftOpAdjunction i).unop

instance : (appLiftOp i).Full := by dsimp [appLiftOp]; infer_instance

instance : (appLiftOp i).Faithful := by dsimp [appLiftOp]; infer_instance

instance : (appLift i).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful (appLiftOp i)).unop).full

instance : (appLift i).Faithful :=
  ((Functor.FullyFaithful.ofFullyFaithful (appLiftOp i)).unop).faithful

/-- **Stacks 09BK.** The lift is fully faithful: the unit `T ⟶ v(T) ×_X Z` is an isomorphism. -/
instance isIso_appLiftAdjunction_unit : IsIso (appLiftAdjunction i).unit :=
  (appLiftAdjunction i).unit_isIso_of_L_fully_faithful

/-! ### The direct image along a closed immersion of affine schemes is fully faithful -/

section Sheaves

variable (A : Type*) [Category* A]

/-- Precomposition with base change along a closed immersion of affine schemes is fully faithful
on presheaves on the affine ind-étale sites: base change has a fully faithful left adjoint. -/
def whiskeringLeftAppBaseChangeOpFullyFaithful :
    ((Functor.whiskeringLeft _ _ A).obj (appBaseChange i).op).FullyFaithful := by
  let adj := (appLiftAdjunction i).op.whiskerLeft A
  have : IsIso (appLiftAdjunction i).op.counit := by
    have : ∀ W : (AppProetale Z)ᵒᵖ, IsIso ((appLiftAdjunction i).op.counit.app W) := fun W ↦ by
      change IsIso ((appLiftAdjunction i).unit.app W.unop).op
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have : IsIso adj.counit := by
    have : ∀ P, IsIso (adj.counit.app P) := fun P ↦ by
      dsimp [adj, Adjunction.whiskerLeft]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact adj.fullyFaithfulROfIsIsoCounit

variable (JX : GrothendieckTopology (AppProetale X)) (JZ : GrothendieckTopology (AppProetale Z))
  [(appBaseChange i).IsContinuous JX JZ]

/-- Restriction of sheaves along base change on the affine ind-étale sites, for a closed
immersion of affine schemes, is fully faithful. -/
def appBaseChangeSheafPushforwardFullyFaithful :
    ((appBaseChange i).sheafPushforwardContinuous A JX JZ).FullyFaithful := by
  have h :
      ((appBaseChange i).sheafPushforwardContinuous A JX JZ ⋙ sheafToPresheaf JX A).FullyFaithful :=
    ((fullyFaithfulSheafToPresheaf JZ A).comp
      (whiskeringLeftAppBaseChangeOpFullyFaithful i A)).ofIso (Iso.refl _)
  exact h.ofCompFaithful

end Sheaves

/-- **Stacks 09BL, the direct image is fully faithful.** For a closed immersion of affine schemes
`i : Z ⟶ X`, direct image of sheaves on the small pro-étale sites is fully faithful. -/
theorem proetaleDirectImage_fullyFaithful (A : Type*) [Category* A]
    [∀ V, Limits.HasLimitsOfShape (StructuredArrow V (AppProetale.inclusion X).op) A]
    [∀ V, Limits.HasLimitsOfShape (StructuredArrow V (AppProetale.inclusion Z).op) A] :
    Nonempty ((Scheme.proetaleBaseChange i).sheafPushforwardContinuous A
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)).FullyFaithful := by
  let JX := (AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)
  let JZ := (AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z)
  have := appInclusion_isDenseSubsite X (hasAppCover X)
  have := appInclusion_isDenseSubsite Z (hasAppCover Z)
  have := appBaseChange_isContinuous i JX JZ (appInclusion_isDenseSubsite X (hasAppCover X))
    (appInclusion_isDenseSubsite Z (hasAppCover Z))
  let RX := (AppProetale.inclusion X).sheafPushforwardContinuous A JX (Scheme.ProEt.topology X)
  let RZ := (AppProetale.inclusion Z).sheafPushforwardContinuous A JZ (Scheme.ProEt.topology Z)
  let SG := (Scheme.proetaleBaseChange i).sheafPushforwardContinuous A
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)
  let Su := (appBaseChange i).sheafPushforwardContinuous A JX JZ
  have : (AppProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).IsContinuous
      JX (Scheme.ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
  have c1 : SG ⋙ RX ≅
      (AppProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).sheafPushforwardContinuous
        A JX (Scheme.ProEt.topology Z) :=
    Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _) (A := A) (J := JX)
      (K := Scheme.ProEt.topology X) (L := Scheme.ProEt.topology Z)
  have c2 : RZ ⋙ Su ≅
      (AppProetale.inclusion X ⋙ Scheme.proetaleBaseChange i).sheafPushforwardContinuous
        A JX (Scheme.ProEt.topology Z) :=
    Functor.sheafPushforwardContinuousComp' (eFG := eqToIso (appBaseChange_comp_inclusion i))
      (A := A) (J := JX) (K := JZ) (L := Scheme.ProEt.topology Z)
  have hRX : RX.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful RX
  have hRZ : RZ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful RZ
  have hSu : (SG ⋙ RX).FullyFaithful :=
    (hRZ.comp (appBaseChangeSheafPushforwardFullyFaithful i A JX JZ)).ofIso (c2 ≪≫ c1.symm)
  exact ⟨hSu.ofCompFaithful⟩

/-- **Stacks 09BL (5).** For a closed immersion of affine schemes `i : Z ⟶ X`, the counit
`i⁻¹ i_* ⟶ id` of the inverse image/direct image adjunction on abelian sheaves on the small
pro-étale sites is an isomorphism. -/
theorem isIso_proetaleInverseImageDirectImageAdj_counit :
    IsIso (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).counit := by
  obtain ⟨hff⟩ := proetaleDirectImage_fullyFaithful i AddCommGrpCat.{max (u + 1) v}
  have : (Abelian.proetaleDirectImage.{u, v} i).Full := hff.full
  have : (Abelian.proetaleDirectImage.{u, v} i).Faithful := hff.faithful
  exact (Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).counit_isIso_of_R_fully_faithful

end AlgebraicGeometry.ProEtale

end
