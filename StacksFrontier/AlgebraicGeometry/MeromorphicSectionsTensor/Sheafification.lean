module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Restriction of scalars commutes with sheafification

Let `θ : R ⟶ R'` be a morphism of sheaves of rings on a site and let `Q` be a presheaf of
`R'`-modules. Sheafifying `Q` and then restricting its scalars along `θ` gives the same sheaf of
`R`-modules as restricting the scalars of `Q` first and sheafifying afterwards.

## Main results

* `Stacks.SheafOfModules.RestrictScalarsSheafification.smul_sheafify_eq`: the two scalar
  multiplications on the sections of the sheafification agree.
* `Stacks.SheafOfModules.RestrictScalarsSheafification.sheafificationRestrictScalarsIso`: the
  resulting isomorphism of sheaves of `R`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v v' u u'

namespace Stacks.SheafOfModules.RestrictScalarsSheafification

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  {R R' : Sheaf J RingCat.{u}} (θ : R ⟶ R') (Q : PresheafOfModules.{v} R'.obj)

/-- Acting by `r` through the module structure which sheafification puts on the restriction of
scalars of `Q` is acting by `θ r` through the module structure it puts on `Q`. -/
theorem smul_sheafify_eq (U : Cᵒᵖ) (r : R.obj.obj U)
    (m : ((presheafToSheaf J AddCommGrpCat.{v}).obj
      ((PresheafOfModules.restrictScalars θ.hom).obj Q).presheaf).obj.obj U) :
    PresheafOfModules.Sheafify.smul (𝟙 R.obj)
        (CategoryTheory.toSheafify J ((PresheafOfModules.restrictScalars θ.hom).obj Q).presheaf)
        r m =
      PresheafOfModules.Sheafify.smul (𝟙 R'.obj) (CategoryTheory.toSheafify J Q.presheaf)
        ((θ.hom.app U) r) m := by
  refine congrArg PresheafOfModules.Sheafify.SMulCandidate.x
    (Subsingleton.elim (PresheafOfModules.Sheafify.smulCandidate (𝟙 R.obj)
      (CategoryTheory.toSheafify J
        ((PresheafOfModules.restrictScalars θ.hom).obj Q).presheaf) r m) ⟨_, ?_⟩)
  intro Y f r₀ hr₀ m₀ hm₀
  refine PresheafOfModules.Sheafify.map_smul_eq (𝟙 R'.obj)
    (CategoryTheory.toSheafify J Q.presheaf) ((θ.hom.app U) r) m f ((θ.hom.app Y) r₀) ?_ m₀ hm₀
  exact (congrArg (θ.hom.app Y) hr₀).trans (ConcreteCategory.congr_hom (θ.hom.naturality f) r)

/-- The comparison morphism of sheaves of `R`-modules, the identity on the common underlying
sheaf of abelian groups. -/
def sheafifyRestrictScalarsHom :
    ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.restrictScalars θ.hom).obj Q)).val ⟶
      ((_root_.SheafOfModules.restrictScalars θ).obj
        ((PresheafOfModules.sheafification (𝟙 R'.obj)).obj Q)).val :=
  PresheafOfModules.homMk (𝟙 _) fun U r m ↦ smul_sheafify_eq θ Q U r m

/-- The comparison morphism in the other direction, again the identity on underlying sections. -/
def sheafifyRestrictScalarsInv :
    ((_root_.SheafOfModules.restrictScalars θ).obj
        ((PresheafOfModules.sheafification (𝟙 R'.obj)).obj Q)).val ⟶
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.restrictScalars θ.hom).obj Q)).val :=
  PresheafOfModules.homMk (𝟙 _) fun U r m ↦ (smul_sheafify_eq θ Q U r m).symm

/-- **Restriction of scalars commutes with sheafification.** -/
def sheafificationRestrictScalarsIso :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.restrictScalars θ.hom).obj Q) ≅
      (_root_.SheafOfModules.restrictScalars θ).obj
        ((PresheafOfModules.sheafification (𝟙 R'.obj)).obj Q) where
  hom := ⟨sheafifyRestrictScalarsHom θ Q⟩
  inv := ⟨sheafifyRestrictScalarsInv θ Q⟩
  hom_inv_id := by
    apply _root_.SheafOfModules.Hom.ext
    refine PresheafOfModules.hom_ext fun U ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    rfl
  inv_hom_id := by
    apply _root_.SheafOfModules.Hom.ext
    refine PresheafOfModules.hom_ext fun U ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    rfl

end Stacks.SheafOfModules.RestrictScalarsSheafification

end
