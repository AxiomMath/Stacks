module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesCompConjugate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardIsoSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoIsoPullbackCoherence
public import StacksFrontier.CategoryTheory.Adjunction.CompOfNatIsoRight
public import StacksFrontier.CategoryTheory.Adjunction.MateTransportedAdjunctions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom

/-!
# The compositor of the derived transitions through the 2-isomorphism of the transitions

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site. The
compositor `Lf_ψ^* ⋙ Lf_φ^* ≅ Lf_{ψ ≫ φ}^*` of the derived transitions (Stacks 0D6D,
`CategoryTheory.SimplicialSiteSituation.derivedTransitionCompIso`) is built from the compositor
of pullbacks of modules of Stacks 09WE. The transitions are morphisms of ringed topoi, and the
same composite also has the compositor of derived pullbacks along morphisms of ringed topoi
(`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackCompComparison`),
followed by the derived pullback isomorphism of the 2-isomorphism
`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHomCompTwoIso`, which is
`f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}`. The two agree: `derivedTransitionCompComparison_eq_twoIso`.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedBaseChangeOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

namespace AlgebraicGeometry.RingedToposHom

universe w w' w'' v u' v' u'' v''

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

variable {X : RingedTopos.{v, u', w}} {Y : RingedTopos.{v', u'', w'}}
  {Z : RingedTopos.{v'', u, w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **The compositor of pullbacks of modules read through a 2-isomorphism `t : g ∘ f ≅ h`.** The
compositor `(g ∘ f)^* ≅ g^* ⋙ f^*` of morphisms of ringed topoi followed by the pullback
isomorphism of `t` is the comparison of left adjoints attached to any isomorphism
`E : f_* ⋙ g_* ≅ h_*` of direct images of modules whose underlying map of sheaves of sets is
`t`. -/
theorem pullbackModulesCompIso_inv_comp_twoIso_eq (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) {h : RingedToposHom X Z} (t : TwoIso (g.comp f) h)
    (E : Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom ⋙
        Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom ≅
      Stacks.Sheaves.RingedToposModules.pushforwardModules h.toModulesHom)
    (hE : ∀ M, (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (E.hom.app M) =
      t.e.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :
    (pullbackModulesCompIso f g).inv ≫ t.pullbackModulesIso.hom =
      (Adjunction.leftAdjointUniq
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          h.toModulesHom).ofNatIsoRight E.symm)
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
            f.toModulesHom))).inv := by
  apply (conjugateEquiv (pullbackAdjPushforwardModules h)
    ((pullbackAdjPushforwardModules g).comp (pullbackAdjPushforwardModules f))).injective
  refine (conjugateEquiv_pullbackModulesCompIso_inv_comp f g t).trans ?_
  have hc := Stacks.CategoryTheory.comp_ofNatIsoRight
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
    g.toModulesPushforwardIso f.toModulesPushforwardIso
  simp only [pullbackAdjPushforwardModules] at hc ⊢
  rw [hc, Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight,
    Adjunction.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv, Iso.eq_inv_comp]
  refine NatTrans.ext (funext fun M => ?_)
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  have hEinv : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      (E.inv.app M) =
        t.e.inv.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :=
    congrArg Iso.inv (@Iso.ext _ _ _ _
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).mapIso (E.app M))
      (t.e.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) (hE M))
  have a₁ : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((pushforwardModulesCompIso f g).hom.app M) = 𝟙 _ := rfl
  have a₂ : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      (t.pushforwardModulesIso.inv.app M) =
        t.e.inv.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) := rfl
  have hw : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (g.pushforwardModules.map (f.toModulesPushforwardIso.hom.app M)) =
      CategoryStruct.id (g.toToposHom.pushforward.obj
        (f.toToposHom.pushforward.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))) :=
    (moduleSheafFunctor_map_pushforwardModules_map g (f.toModulesPushforwardIso.hom.app M)).trans
      ((congrArg g.toToposHom.pushforward.map
          (moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id f M)).trans
        (CategoryTheory.Functor.map_id g.toToposHom.pushforward
          (f.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))))
  simp only [NatTrans.comp_app, CategoryTheory.Functor.map_comp, Iso.symm_hom, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, hw,
    moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id, a₁, a₂, hEinv]
  exact Sheaf.hom_ext_sections fun _ _ ↦ rfl

end AlgebraicGeometry.RingedToposHom

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The compositor of pullbacks of modules of Stacks 09WE is that of morphisms of ringed topoi
followed by the 2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}`.** -/
theorem transitionPullbackModulesCompIso_inv_eq_twoIso {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
          (S.transitionRingedToposHom O ψ)).inv ≫
        (S.transitionRingedToposHomCompTwoIso O ψ φ).pullbackModulesIso.hom =
      (S.transitionPullbackModulesCompIso O ψ φ).inv :=
  RingedToposHom.pullbackModulesCompIso_inv_comp_twoIso_eq _ _ _
    (S.transitionPushforwardModulesCompIso O ψ φ)
    (fun M ↦ S.moduleSheaf_transitionPushforwardModulesCompIso_hom O ψ φ M)

/-- The compositor of the derived transitions and the compositor of derived pullbacks followed by
the 2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}` agree after the comparison with degreewise pullback, at
a complex. -/
theorem derivedTransitionCompComparison_app_eq_twoIso {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (K : HomotopyCategory (S.componentRingedTopos O l).Modules (ComplexShape.up ℤ)) :
    (S.derivedTransitionCompComparison O ψ φ).app (DerivedCategory.Qh.obj K) ≫
        (S.derivedTransitionComparison O (ψ ≫ φ)).app K =
      ((derivedPullbackCompComparison (S.transitionRingedToposHom O φ)
          (S.transitionRingedToposHom O ψ)).app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackIsoOfTwoIso (S.transitionRingedToposHomCompTwoIso O ψ φ)).hom.app
          (DerivedCategory.Qh.obj K)) ≫
        (derivedPullbackComparison' (S.transitionRingedToposHom O (ψ ≫ φ))).app K := by
  have h₁ := (NatTrans.congr_app (S.derivedTransitionComp_fac O ψ φ) K).trans
    (S.derivedTransitionCompCounit_app O ψ φ K)
  have h₂ := derivedPullbackIsoOfTwoIso_hom_fac (S.transitionRingedToposHomCompTwoIso O ψ φ) K
  have h₃ := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app'
    (S.transitionRingedToposHom O φ) (S.transitionRingedToposHom O ψ) K
  have h₄ : (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
        (S.transitionRingedToposHom O ψ)).symm ≪≫
      (S.transitionRingedToposHomCompTwoIso O ψ φ).pullbackModulesIso =
        (S.transitionPullbackModulesCompIso O ψ φ).symm :=
    Iso.ext (S.transitionPullbackModulesCompIso_inv_eq_twoIso O ψ φ)
  have h₅ := mapHomotopyCategoryCompIso_trans_hom_app
    (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
      (S.transitionRingedToposHom O ψ)).symm
    (S.transitionRingedToposHomCompTwoIso O ψ φ).pullbackModulesIso K
  rw [h₄] at h₅
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁
  have g : ((derivedPullbackCompComparison (S.transitionRingedToposHom O φ)
          (S.transitionRingedToposHom O ψ)).app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackIsoOfTwoIso (S.transitionRingedToposHomCompTwoIso O ψ φ)).hom.app
          (DerivedCategory.Qh.obj K)) ≫
        (derivedPullbackComparison' (S.transitionRingedToposHom O (ψ ≫ φ))).app K =
      (derivedPullback (S.transitionRingedToposHom O φ)).map
          ((derivedPullbackComparison' (S.transitionRingedToposHom O ψ)).app K) ≫
        (derivedPullbackComparison' (S.transitionRingedToposHom O φ)).app
          ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (S.transitionPullbackModulesCompIso O ψ φ).symm (ComplexShape.up ℤ)).hom.app K) := by
    rw [Category.assoc, h₂, reassoc_of% h₃, ← DerivedCategory.Qh.map_comp, ← h₅]
  exact h₁.trans g.symm

/-- **The compositor of the derived transitions is the compositor of derived pullbacks along
morphisms of ringed topoi, followed by the 2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}`.** Both are
maps into the left derived functor `Lf_{ψ ≫ φ}^*`, and they agree after restriction along the
localization, where they are the two compositors of pullbacks of modules. -/
theorem derivedTransitionCompComparison_eq_twoIso {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    S.derivedTransitionCompComparison O ψ φ =
      derivedPullbackCompComparison (S.transitionRingedToposHom O φ)
          (S.transitionRingedToposHom O ψ) ≫
        (derivedPullbackIsoOfTwoIso (S.transitionRingedToposHomCompTwoIso O ψ φ)).hom :=
  Functor.leftDerived_ext (S.derivedTransitionPullback O (ψ ≫ φ))
    (S.derivedTransitionComparison O (ψ ≫ φ))
    (targetQuasiIso (S.componentRingedTopos O l)) _ _ _
    (NatTrans.ext (funext fun K ↦ S.derivedTransitionCompComparison_app_eq_twoIso O ψ φ K))

end CategoryTheory.SimplicialSiteSituation

end
