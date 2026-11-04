module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.OpenImmersionComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Transverse
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothPulledBackFormsToTarget

/-!
# Canonical maps into derived direct images along a composite

For morphisms of ringed spaces `i : Z ⟶ X` and `p : X ⟶ Y`, the composition isomorphism
`Ri_* ⋙ Rp_* ≅ R(i ≫ p)_*` of [Stacks, Tag 079W] commutes with the shift, and canonical maps
`Q(d) ≫ (p_* ⟶ Rp_*)` compose: the composite of the canonical maps of `d : M ⟶ p_*N` and
`e : N ⟶ i_*L` is the canonical map of the composite `M ⟶ p_*i_*L = (i ≫ p)_*L`. For the
canonical maps of de Rham complexes this says that the maps of two horizontally composable
squares compose to the map of the outer square.

## Main results

* `Stacks.Cohomology.LerayComposite.natTransCommShift_derivedPushforwardCompIso_hom`.
* `Stacks.Cohomology.LerayComposite.comparisonQ_comp_of_heq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)

universe u

namespace Stacks.Cohomology.LerayComposite

open scoped Stacks.StandardDerivedModel

attribute [local instance]
  Stacks.Cohomology.DerivedPushforwardComposition.isRightDerivedFunctor_comp_canonical

variable {Z X Y : RingedSpace.{u, u}} (i : Z ⟶ X) (p : X ⟶ Y)

/-- The comparison of degreewise pushforward along `i ≫ p` with `Ri_* ⋙ Rp_*` commutes with
the shift. -/
instance natTransCommShift_derivedPushforwardCompUnit :
    NatTrans.CommShift
      (Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit i p
        (derivedPushforward i) (derivedPushforward p) (derivedPushforwardUnit i)
        (derivedPushforwardUnit p)) ℤ := by
  let A := (modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)
  have h₁ : NatTrans.CommShift (Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp i p) (ComplexShape.up ℤ)).inv
        DerivedCategory.Qh ≫ (Functor.associator _ _ _).hom) ℤ := inferInstance
  have h₂ : NatTrans.CommShift (Functor.whiskerLeft A (derivedPushforwardUnit p) ≫
      (Functor.associator _ _ _).inv) ℤ := inferInstance
  have h₃ : NatTrans.CommShift (Functor.whiskerRight (derivedPushforwardUnit i)
      (derivedPushforward p) ≫ (Functor.associator _ _ _).hom) ℤ := inferInstance
  have h₄ := NatTrans.CommShift.comp (A := ℤ)
    (τ := Functor.whiskerLeft A (derivedPushforwardUnit p) ≫ (Functor.associator _ _ _).inv)
    (τ' := Functor.whiskerRight (derivedPushforwardUnit i) (derivedPushforward p) ≫
      (Functor.associator _ _ _).hom)
  have h₅ := NatTrans.CommShift.comp (A := ℤ) (τ := Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp i p) (ComplexShape.up ℤ)).inv
        DerivedCategory.Qh ≫ (Functor.associator _ _ _).hom)
    (τ' := (Functor.whiskerLeft A (derivedPushforwardUnit p) ≫ (Functor.associator _ _ _).inv) ≫
      (Functor.whiskerRight (derivedPushforwardUnit i) (derivedPushforward p) ≫
        (Functor.associator _ _ _).hom))
  have heq : Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit i p
      (derivedPushforward i) (derivedPushforward p) (derivedPushforwardUnit i)
        (derivedPushforwardUnit p) =
      (Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp i p) (ComplexShape.up ℤ)).inv
          DerivedCategory.Qh ≫ (Functor.associator _ _ _).hom) ≫
      ((Functor.whiskerLeft A (derivedPushforwardUnit p) ≫ (Functor.associator _ _ _).inv) ≫
        (Functor.whiskerRight (derivedPushforwardUnit i) (derivedPushforward p) ≫
          (Functor.associator _ _ _).hom)) := by
    ext K
    simp [Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit, A]
  rw [heq]
  exact h₅

/-- The composition isomorphism is the descent of the unit of `R(i ≫ p)_*` along the comparison
of `Ri_* ⋙ Rp_*`. -/
theorem derivedPushforwardCompIso_hom_eq :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso i p).hom =
      (derivedPushforward i ⋙ derivedPushforward p).rightDerivedDesc
        (Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit i p
          (derivedPushforward i) (derivedPushforward p)
          (derivedPushforwardUnit i) (derivedPushforwardUnit p))
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
        (derivedPushforward (i ≫ p)) (derivedPushforwardUnit (i ≫ p)) := by
  refine Functor.rightDerived_ext _
    (Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit i p
      (derivedPushforward i) (derivedPushforward p) (derivedPushforwardUnit i)
      (derivedPushforwardUnit p))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
    _ _ _ ?_
  rw [Functor.rightDerived_fac]
  ext K
  open Stacks.Cohomology.DerivedPushforwardComposition in
  exact derivedPushforwardCompUnit_comp_derivedPushforwardCompIso i p K

/-- **The composition isomorphism `Ri_* ⋙ Rp_* ≅ R(i ≫ p)_*` commutes with the shift.** -/
instance natTransCommShift_derivedPushforwardCompIso_hom :
    NatTrans.CommShift
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso i p).hom ℤ := by
  rw [derivedPushforwardCompIso_hom_eq]
  exact Stacks.Triangulated.natTransCommShift_rightDerivedDesc _ _ _ ℤ _ _

/-- The bookkeeping of `comparisonQ_comp_of_heq`, with every object and morphism a variable. -/
private theorem comp_paste {C : Type*} [Category* C] {A B B' D₁ E F G H : C}
    (qD : A ⟶ B) (cc : B ⟶ B') (qd : A ⟶ D₁) (qpe : D₁ ⟶ B') (pcI : B' ⟶ F) (pcN : D₁ ⟶ E)
    (rqe : E ⟶ F) (rpc : F ⟶ G) (ci : G ⟶ H) (rqepc : E ⟶ G)
    (h₃ : qD ≫ cc = qd ≫ qpe) (h₂ : qpe ≫ pcI = pcN ≫ rqe) (hm : rqepc = rqe ≫ rpc) :
    (qd ≫ pcN) ≫ rqepc ≫ ci = qD ≫ (cc ≫ pcI ≫ rpc ≫ ci) := by
  rw [hm]
  simp only [Category.assoc]
  rw [reassoc_of% h₃, reassoc_of% h₂]

/-- **Canonical maps into derived direct images compose.** For `d : M ⟶ p_*N`, `e : N ⟶ i_*L` and
`D : M ⟶ k_*L` with `k = i ≫ p` and `D` the composite `M ⟶ p_*N ⟶ p_*i_*L` on local sections, the
canonical map of `d` followed by `Rp_*` of the canonical map of `e` and the composition
isomorphism is the canonical map of `D`. -/
theorem comparisonQ_comp_of_heq (k : Z ⟶ Y) (hk : i ≫ p = k)
    {M : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ}
    {N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    {L : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    (d : M ⟶ (pushforwardComplex p).obj N) (e : N ⟶ (pushforwardComplex i).obj L)
    (D : M ⟶ (pushforwardComplex k).obj L)
    (hD : ∀ (n : ℤ) (V : (Opens Y.carrier)ᵒᵖ) (x : (M.X n).val.obj V),
      HEq ((D.f n).val.app V x)
        ((e.f n).val.app ((Opens.map p.hom.base).op.obj V) ((d.f n).val.app V x))) :
    (DerivedCategory.Q.map d ≫ pushforwardComparisonQ p N) ≫
        (derivedPushforward p).map (DerivedCategory.Q.map e ≫ pushforwardComparisonQ i L) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso i p).hom.app
          (DerivedCategory.Q.obj L) ≫
        eqToHom (congrArg (fun k : Z ⟶ Y => (derivedPushforward k).obj (DerivedCategory.Q.obj L))
          hk) =
      DerivedCategory.Q.map D ≫ pushforwardComparisonQ k L := by
  subst hk
  have hD' : D ≫ pushforwardCompComplexHom i p L = d ≫ (pushforwardComplex p).map e := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact eq_of_heq (hD n V x)
  have h₁ := pushforwardComparisonQ_comp i p L
  have h₂ := pushforwardComparisonQ_naturality p e
  have h₃ := (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map hD').trans
    (DerivedCategory.Q.map_comp _ _))
  have h₄ : pushforwardComparisonQ (i ≫ p) L =
      DerivedCategory.Q.map (pushforwardCompComplexHom i p L) ≫
        pushforwardComparisonQ p ((pushforwardComplex i).obj L) ≫
        (derivedPushforward p).map (pushforwardComparisonQ i L) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso i p).hom.app
          (DerivedCategory.Q.obj L) :=
    ((Category.comp_id _).symm.trans (congrArg (pushforwardComparisonQ (i ≫ p) L ≫ ·)
      (Iso.inv_hom_id_app _ _).symm)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          i p).hom.app (DerivedCategory.Q.obj L)) h₁).trans ((Category.assoc _ _ _).trans
            (congrArg (DerivedCategory.Q.map (pushforwardCompComplexHom i p L) ≫ ·)
              (Category.assoc _ _ _)))))
  rw [eqToHom_refl, Category.comp_id]
  exact (comp_paste _ _ _ _ _ _ _ _ _ _ h₃ h₂ (Functor.map_comp _ _ _)).trans
    (congrArg (DerivedCategory.Q.map D ≫ ·) h₄.symm)

end Stacks.Cohomology.LerayComposite

namespace AlgebraicGeometry.DeRhamLerayHirsch

open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

variable {X X' X'' S S' S'' : Scheme.{u}} (b : X' ⟶ X) (s : X ⟶ S) (s' : X' ⟶ S') (g₁ : S' ⟶ S)
  (h₁ : b ≫ s = s' ≫ g₁) (a : X'' ⟶ X') (s'' : X'' ⟶ S'') (g₂ : S'' ⟶ S')
  (h₂ : a ≫ s' = s'' ≫ g₂) (c : X'' ⟶ X) (t : S'' ⟶ S) (h₃ : c ≫ s = s'' ≫ t)

/-- The morphisms of inverse-image ringed spaces of two horizontally composable squares compose to
the morphism of the outer square. -/
theorem inverseImageBaseMap_comp (hc : a ≫ b = c) (ht : g₂ ≫ g₁ = t) :
    inverseImageBaseMap a s'' s' g₂ h₂ ≫ inverseImageBaseMap b s' s g₁ h₁ =
      inverseImageBaseMap c s'' s t h₃ := by
  subst hc ht
  refine RingedSpace.inverseImage_hom_ext S.toRingedSpace s.base _ _ ?_ ?_
  · change (inverseImageBaseMap a s'' s' g₂ h₂).hom.base ≫
        (inverseImageBaseMap b s' s g₁ h₁).hom.base =
      (inverseImageBaseMap (a ≫ b) s'' s (g₂ ≫ g₁) h₃).hom.base
    rw [inverseImageBaseMap_base, inverseImageBaseMap_base, inverseImageBaseMap_base,
      Scheme.Hom.comp_base]
    exact rfl
  · rw [Category.assoc, inverseImageBaseMap_comp_inverseImageBaseProjection, ← Category.assoc,
      inverseImageBaseMap_comp_inverseImageBaseProjection, Category.assoc,
      inverseImageBaseMap_comp_inverseImageBaseProjection]
    rfl

/-- **The canonical maps of two horizontally composable squares compose** to the canonical map
of the outer square, through the composition isomorphism of derived direct images. -/
theorem deRhamComparisonQ_comp (hc : a ≫ b = c) (ht : g₂ ≫ g₁ = t) :
    deRhamComparisonQ b s' s g₁ h₁ ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          (inverseImageBaseMap b s' s g₁ h₁)).map (deRhamComparisonQ a s'' s' g₂ h₂) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          (inverseImageBaseMap a s'' s' g₂ h₂) (inverseImageBaseMap b s' s g₁ h₁)).hom.app
          (DerivedCategory.Q.obj (deRhamComplexModules s'')) ≫
        eqToHom (congrArg (fun k =>
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward k).obj
            (DerivedCategory.Q.obj (deRhamComplexModules s'')))
          (inverseImageBaseMap_comp b s s' g₁ h₁ a s'' g₂ h₂ c t h₃ hc ht)) =
      deRhamComparisonQ c s'' s t h₃ := by
  unfold deRhamComparisonQ
  refine (Stacks.Cohomology.LerayComposite.comparisonQ_comp_of_heq
      (inverseImageBaseMap a s'' s' g₂ h₂)
      (inverseImageBaseMap b s' s g₁ h₁) (inverseImageBaseMap c s'' s t h₃)
      (inverseImageBaseMap_comp b s s' g₁ h₁ a s'' g₂ h₂ c t h₃ hc ht)
      (deRhamPushforwardModules b s' s g₁ h₁) (deRhamPushforwardModules a s'' s' g₂ h₂)
      (deRhamPushforwardModules c s'' s t h₃) fun n V x => ?_)
  subst hc ht
  by_cases hn : 0 ≤ n
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    let x' : Γ(Scheme.Hom.relativeDifferentialForms s (q : ℤ), V.unop) :=
      cast (congrArg (fun M : _root_.SheafOfModules.{u}
        (SheafOfModules.underlyingRingSheaf.{u, u} (DeRhamKatzOdaCech.baseSheaf s)) =>
          (M.val.obj V : Type u))
        (SheafOfModules.deRhamComplexInt_X_of_nonneg (Scheme.Hom.deRhamAlgebras s)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras s)) (q : ℤ)
          (Int.natCast_nonneg q))) x
    have hx : HEq x x' := (cast_heq _ x).symm
    have hL := dgaPushforward_f_app_heq (a ≫ b) s'' s (g₂ ≫ g₁) h₃ q q rfl V x x' hx
    have hM := dgaPushforward_f_app_heq b s' s g₁ h₁ q q rfl V x x' hx
    have hR := dgaPushforward_f_app_heq a s'' s' g₂ h₂ q q rfl
      ((Opens.map (inverseImageBaseMap b s' s g₁ h₁).hom.base).op.obj V) _ _ hM
    have hC := Stacks.Gysin.relativeDifferentialFormsPullback_comp b a s s' s'' g₁ g₂ (g₂ ≫ g₁)
      h₁ h₂ h₃ (q : ℤ) V.unop x'
    exact hL.trans ((heq_of_eq hC).trans hR.symm)
  · exact heq_of_eq ((dga_section_eq_zero s'' n (by omega) _ _).trans
      (dga_section_eq_zero s'' n (by omega) _ _).symm)

end AlgebraicGeometry.DeRhamLerayHirsch
