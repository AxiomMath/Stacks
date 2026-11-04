module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetNormalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint

/-!
# Lower shriek of modules along an isomorphic structure map

Let `F : C ⥤ D` be a continuous functor of sites, `R` a sheaf of rings on `D`, and let
`φ : S ⟶ F_* R` and `φ' : S' ⟶ F_* R` be two structure maps that differ by an isomorphism
`e : S' ≅ S` of sheaves of rings on `C`, `φ' = e ≫ φ`. The two pushforwards of modules differ by
restriction of scalars along `e`, which is an equivalence, so the two lower shrieks differ by
restriction of scalars along `e⁻¹`. Restriction of scalars does not change the underlying
abelian sheaf, so whenever lower shriek along `φ` commutes with forgetting the module structure,
so does lower shriek along `φ'`.

This is how a statement proved for the structure map `𝟙 : u⁻¹O ⟶ u⁻¹O` of
`Stacks.SheafOfModules.structureMap` transfers to a ringed site whose structure sheaf is only
*isomorphic* to `u⁻¹O`, as in Situation 08PA.

## Main definitions

* `Stacks.SheafOfModules.pullbackIsoRestrictScalarsPullback`: `g_!` along `φ'` is restriction of
  scalars along `e⁻¹` followed by `g_!` along `φ`.
* `Stacks.SheafOfModules.lowerShriekForgetIsoOfRestrictScalars`: if the Stacks 0798 comparison
  along `φ` is invertible, then `forget ∘ g_!` along `φ'` is isomorphic to `g_!^{Ab} ∘ forget`.

## Main results

* `Stacks.SheafOfModules.lowerShriekForgetComparison_app_comp_pullbackIsoRestrictScalarsPullback`:
  the Stacks 0798 comparison along `φ'` at `M`, followed by the identification of
  `pullbackIsoRestrictScalarsPullback`, is the comparison along `φ` at `M` with scalars
  restricted.
* `Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_restrictScalars`: so the comparison
  along `φ'` is invertible as soon as the comparison along `φ` is.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w u₁ u₂ v₁ v₂

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K]
  {S S' : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (phi : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (phi' : S' ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (e : S' ≅ S) (h : e.hom ≫ phi = phi')

include h

/-- Pushforward of modules along `φ' = e ≫ φ` is pushforward along `φ` followed by restriction
of scalars along `e`; the two functors agree on the nose. -/
theorem pushforward_comp_restrictScalars :
    _root_.SheafOfModules.pushforward.{u} phi ⋙ _root_.SheafOfModules.restrictScalars e.hom =
      _root_.SheafOfModules.pushforward.{u} phi' := by
  subst h
  rfl

variable [(_root_.SheafOfModules.pushforward.{u} phi).IsRightAdjoint]
  [(_root_.SheafOfModules.pushforward.{u} phi').IsRightAdjoint]

/-- **Lower shriek along an isomorphic structure map.** If `φ' = e ≫ φ` for an isomorphism
`e : S' ≅ S`, then `g_!` along `φ'` is restriction of scalars along `e⁻¹` followed by `g_!` along
`φ`: both are left adjoint to pushforward along `φ'`, the second through the adjoint equivalence
of restriction of scalars along `e` and `e⁻¹`. -/
def pullbackIsoRestrictScalarsPullback :
    _root_.SheafOfModules.pullback.{u} phi' ≅
      _root_.SheafOfModules.restrictScalars e.inv ⋙ _root_.SheafOfModules.pullback.{u} phi :=
  (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} phi').leftAdjointUniq
    (((Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso e).toAdjunction.comp
      (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u} phi)).ofNatIsoRight
      (eqToIso (pushforward_comp_restrictScalars F phi phi' e h)))

variable [(F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsRightAdjoint]

/-- **Commutation with the forgetful functors transfers along an isomorphic structure map.** If
the Stacks 0798 comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` along `φ` is an isomorphism, then
for `φ' = e ≫ φ` the square of `g_!` along `φ'`, `g_!^{Ab}` and the two forgetful functors
commutes up to isomorphism: restriction of scalars does not change the underlying abelian sheaf,
and `g_!` along `φ'` is `g_!` along `φ` after restriction of scalars along `e⁻¹`
(`pullbackIsoRestrictScalarsPullback`). -/
def lowerShriekForgetIsoOfRestrictScalars [IsIso (lowerShriekForgetComparison.{u, u} F phi)] :
    _root_.SheafOfModules.pullback.{u} phi' ⋙ _root_.SheafOfModules.toSheaf.{u} R ≅
      _root_.SheafOfModules.toSheaf.{u} S' ⋙ F.sheafPullback AddCommGrpCat.{u} J K :=
  Functor.isoWhiskerRight (pullbackIsoRestrictScalarsPullback F phi phi' e h) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (_root_.SheafOfModules.restrictScalars e.inv)
      (asIso (lowerShriekForgetComparison F phi)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- **The Stacks 0798 comparison along `φ' = e ≫ φ` is the comparison along `φ`.** At a sheaf of
`S'`-modules `M`, the comparison along `φ'` followed by `forget` of the identification
`g_! M ≅ g_!(M` with scalars restricted along `e⁻¹)` of `pullbackIsoRestrictScalarsPullback` is the
comparison along `φ` at `M` with scalars restricted. Both are characterised by their adjoint
transposes, which are the forgotten units of the two module adjunctions; and the unit of the
adjunction of `pullbackIsoRestrictScalarsPullback` is the unit along `φ` up to restriction of
scalars, which forgetting does not see. -/
theorem lowerShriekForgetComparison_app_comp_pullbackIsoRestrictScalarsPullback
    (M : _root_.SheafOfModules.{u} S') :
    (lowerShriekForgetComparison F phi').app M ≫
        (_root_.SheafOfModules.toSheaf.{u} R).map
          ((pullbackIsoRestrictScalarsPullback F phi phi' e h).hom.app M) =
      (lowerShriekForgetComparison F phi).app
        ((_root_.SheafOfModules.restrictScalars e.inv).obj M) := by
  apply ((F.sheafAdjunctionContinuous AddCommGrpCat.{u} J K).homEquiv _ _).injective
  refine (homEquiv_lowerShriekForgetComparison_app_comp F phi' M _ _).trans
    (Eq.trans ?_ (lowerShriekForgetComparison_homEquiv F phi
      ((_root_.SheafOfModules.restrictScalars e.inv).obj M)).symm)
  rw [Adjunction.homEquiv_unit]
  refine (congrArg (_root_.SheafOfModules.toSheaf.{u} S').map
    (Adjunction.unit_leftAdjointUniq_hom_app _ _ M)).trans ?_
  subst h
  ext X x
  rfl

/-- **The Stacks 0798 comparison is invertible along an isomorphic structure map.** If the
comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` along `φ` is an isomorphism, so is the comparison
along `φ' = e ≫ φ` for any isomorphism `e` of sheaves of rings: by
`lowerShriekForgetComparison_app_comp_pullbackIsoRestrictScalarsPullback` each of its components
is a component of the first followed by the inverse of an isomorphism. -/
theorem isIso_lowerShriekForgetComparison_of_restrictScalars
    [hc : IsIso (lowerShriekForgetComparison.{u, u} F phi)] :
    IsIso (lowerShriekForgetComparison.{u, u} F phi') := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hfac := lowerShriekForgetComparison_app_comp_pullbackIsoRestrictScalarsPullback
    F phi phi' e h M
  have h1 : IsIso ((lowerShriekForgetComparison.{u, u} F phi).app
      ((_root_.SheafOfModules.restrictScalars e.inv).obj M)) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hc _
  rw [← hfac] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance h1

end Stacks.SheafOfModules

end
