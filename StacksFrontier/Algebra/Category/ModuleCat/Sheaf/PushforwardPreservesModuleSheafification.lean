module

public import Mathlib.Topology.Sheaves.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction

/-!
# Pushforward and sheafification of presheaves of modules

For a continuous functor `G` between sites and a sheaf of rings `R` on the target, we consider the
condition that, for every presheaf of `R`-modules, the sheafification unit whiskered along `G` is
locally injective and locally surjective, and show that it holds when `G` is cocontinuous.

## Main definitions

* `PreservesModuleSheafification`: pushforward along `G` is compatible with sheafification of
  presheaves of `R`-modules.

## Main results

* `preservesModuleSheafification_of_isCocontinuous`: a cocontinuous functor is compatible with
  sheafification of presheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
  AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

universe w t v u v' u'

/-! ### Sheafification commutes with pushforward along a cocontinuous functor -/

namespace Stacks.SheafOfModules.PushforwardSheafification

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D} (G : C ⥤ D)
  [G.IsContinuous J K] (R : Sheaf K RingCat.{t})

variable [HasWeakSheafify K AddCommGrpCat.{w}]

/-- **Pushforward along `G` is compatible with sheafification of presheaves of `R`-modules**:
for every presheaf of `R`-modules `P`, the sheafification unit of `P`, whiskered along `G`, is
locally injective and locally surjective. This holds when `G` is cocontinuous
(`preservesModuleSheafification_of_isCocontinuous`), and also for the preimage functor of a
closed embedding of topological spaces, which is not cocontinuous in general. -/
class PreservesModuleSheafification : Prop where
  isLocallyInjective (P : PresheafOfModules.{w} R.obj) :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerLeft G.op (CategoryTheory.toSheafify K P.presheaf))
  isLocallySurjective (P : PresheafOfModules.{w} R.obj) :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerLeft G.op (CategoryTheory.toSheafify K P.presheaf))

variable [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A cocontinuous functor is compatible with sheafification of presheaves of modules. -/
instance preservesModuleSheafification_of_isCocontinuous [G.IsCocontinuous J K] :
    PreservesModuleSheafification.{w} J G R where
  isLocallyInjective _ := Presheaf.isLocallyInjective_whisker J K G _
  isLocallySurjective _ := Presheaf.isLocallySurjective_whisker J K G _

variable [PreservesModuleSheafification.{w} J G R] (P : PresheafOfModules.{w} R.obj)

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

end Stacks.SheafOfModules.PushforwardSheafification

namespace PresheafOfModules

section SitePushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (G : C ⥤ D)
  {O : Dᵒᵖ ⥤ CommRingCat.{w}} (n : ℕ)
  (P : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

end SitePushforward

section SymPowZero

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

end SymPowZero

end PresheafOfModules

namespace SheafOfModules

open PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

end SheafOfModules

namespace Stacks.SheafOfModules

open _root_.PresheafOfModules Stacks.SheafOfModules.PushforwardSheafification

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (G : Cs ⥤ Ct)
  [G.IsContinuous Js Jt]
  {Osharp : Sheaf Jt CommRingCat.{w}}
  [Jt.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}]
  [PreservesModuleSheafification.{w} Js G (toRingCat Jt Osharp)]
  (M : _root_.SheafOfModules.{w} (toRingCat Jt Osharp)) (n : ℕ)

section Symmetric

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat Jt Osharp))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A gen)
  (B : _root_.SheafOfModules.GradedAlgebra.{w, w}
    (toRingCat Js (pushforwardCommRingSheaf Js G (Osharp := Osharp))))
  (gen' : (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra B gen')

end Symmetric

section Exterior

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat Jt Osharp))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)
  (B : _root_.SheafOfModules.GradedAlgebra.{w, w}
    (toRingCat Js (pushforwardCommRingSheaf Js G (Osharp := Osharp))))
  (gen' : (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra B gen')

end Exterior

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.PushforwardSheafification

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

variable (F : _root_.SheafOfModules.{u} (structureSheafRing X))

variable (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

section Conclusions

variable {X : RingedSpace.{u, u}} (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  [F.IsQuasicoherent]
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

end Conclusions

end Stacks.SheafOfModules

end
