module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonAdjunction
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback

/-!
# The two pullbacks of modules along a morphism of ringed sites as left adjoints

For a morphism of ringed sites `f`, the identification
`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso` of the pullback of sheaves of modules
along the four-field morphism of ringed topoi with Mathlib's pullback along `f.u`, preceded by the
equation of the pullbacks along the two four-field forms of `f.ringedToposHom`, is the comparison
of left adjoints of the adjunction of Stacks 03D7 for `f.ringedToposHom`, transported along
`AlgebraicGeometry.RingedSite.Hom.pushforwardToposIso`, with the adjunction of the site-presented
morphism.

## Main results

* `Stacks.Sheaves.RingedToposModules.eqToIso_trans_leftAdjointUniq_ofNatIsoRight`: for equal
  morphisms of ringed topoi `g₁ = g₂`, the equation of their pullbacks of modules followed by the
  comparison of the `g₂`-pullback with a left adjoint `L` is the comparison of the `g₁`-pullback
  with `L`, the adjunctions being transported to a common right adjoint.
* `AlgebraicGeometry.RingedSite.Hom.eqToIso_trans_pullbackModulesToposIso`: the identification
  `AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`, preceded by the equation of the
  pullbacks along the two four-field forms of `f.ringedToposHom`, is the comparison of left
  adjoints.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe w w' v u v' u'

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Comparing pullbacks along equal morphisms, then with a third left adjoint.** Let
`g₁ = g₂`, and let the adjunctions of Stacks 03D7 for `g₁` and `g₂` be transported to a common
right adjoint `P` along `α` and `i`, which agree up to the equation. Then the `eqToIso` of the
equation of pullbacks followed by the comparison of the `g₂`-pullback with a left adjoint `L` of
`Q`, through `i ≪≫ τ`, is the comparison of the `g₁`-pullback with `L` through `α` and `τ`. -/
theorem eqToIso_trans_leftAdjointUniq_ofNatIsoRight {g₁ g₂ : RingedToposHom X Y} (hg : g₁ = g₂)
    {P Q : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    {L : _root_.SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (α : pushforwardModules g₁ ≅ P) (i : pushforwardModules g₂ ≅ P) (τ : P ≅ Q) (b : L ⊣ Q)
    (hαi : ∀ F, i.hom.app F ≫ α.inv.app F ≫
      eqToHom (congrArg (fun g : RingedToposHom X Y ↦ (pushforwardModules g).obj F) hg) = 𝟙 _) :
    eqToIso (congrArg (fun g : RingedToposHom X Y ↦ g.pullbackModules) hg) ≪≫
        Adjunction.leftAdjointUniq ((pullbackAdjPushforwardModules g₂).ofNatIsoRight (i ≪≫ τ)) b =
      Adjunction.leftAdjointUniq
        (((pullbackAdjPushforwardModules g₁).ofNatIsoRight α).ofNatIsoRight τ) b := by
  subst hg
  obtain rfl : i = α := by
    refine Iso.ext (NatTrans.ext (funext fun F ↦ ?_))
    simpa using congrArg (· ≫ α.hom.app F) (hαi F)
  have hadj : (pullbackAdjPushforwardModules g₁).ofNatIsoRight (i ≪≫ τ) =
      ((pullbackAdjPushforwardModules g₁).ofNatIsoRight i).ofNatIsoRight τ := by
    refine Adjunction.ext (NatTrans.ext (funext fun G => ?_))
    simp [Adjunction.ofNatIsoRight]
  rw [hadj, eqToIso_refl, Iso.refl_trans]

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedSite

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The comparison of the two pullbacks of modules is the comparison of left adjoints.** The
equation of the pullbacks along `f.ringedToposHom.toModulesHom` and
`f.ringedToposHom.toRingedToposModulesHom`, followed by
`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`, is the comparison of the left
adjoints of the adjunction of Stacks 03D7 for `f.ringedToposHom`, transported along
`AlgebraicGeometry.RingedSite.Hom.pushforwardToposIso`, and of the site-presented morphism. -/
theorem Hom.eqToIso_trans_pullbackModulesToposIso :
    eqToIso (RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom
        f.ringedToposHom) ≪≫ f.pullbackModulesToposIso =
      Adjunction.leftAdjointUniq
        ((RingedToposHom.pullbackAdjPushforwardModules f.ringedToposHom).ofNatIsoRight
          f.pushforwardToposIso)
        f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos :=
  Stacks.Sheaves.RingedToposModules.eqToIso_trans_leftAdjointUniq_ofNatIsoRight
    (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom f.ringedToposHom)
    f.ringedToposHom.toModulesPushforwardIso f.ringedToposHom.pushforwardModulesIso
    f.pushforwardToposIso f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    (RingedToposHom.pushforwardModulesIso_hom_app_comp_eqToHom f.ringedToposHom)

end AlgebraicGeometry.RingedSite

end
