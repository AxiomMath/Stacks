module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeStageAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleRestrictionInternalHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleInternalHom

/-!
# `ℋom(G, L)` with `L` injective is acyclic on `Y_K`

Let `k` be a field, `K/k` a separable algebraic extension and `Y` a quasi-compact and
quasi-separated `k`-scheme. Let `G` be a sheaf of `Λ`-modules on `Y_étale` whose underlying
abelian sheaf is that of a sheaf `G'` of `ℤ/n`-modules, and let `L` be an injective sheaf of
`ℤ/n`-modules. Then the restriction to `Y_K` of the sheaf of `Λᵐᵒᵖ`-modules `ℋom_ℤ(G, L)` has no
higher cohomology. At every finite stage `Y_E`, `E ⊆ K` finite, the restriction is
`ℋom_{ℤ/n}(G'|_{Y_E}, L|_{Y_E})` with `L|_{Y_E}` injective, hence acyclic; one then concludes by
Stacks 09YQ (`Stacks.EtaleCohomology.isZero_rightDerived_fieldBaseChange_of_stage`).

`ℋom(G, L)` itself need not be injective. This is the acyclicity input for computing
`RΓ^Gal(Y, ℋom(G, -))` on an injective resolution in sheaves of `ℤ/n`-modules.

## Main results

* `Stacks.EtaleCohomology.rightAcyclic_fieldBaseChange_etaleHomOp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Frobenius

universe w₃ w₄ u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the object
universe. -/
local instance (priority := 3000) etaleModules_enoughInjectives_fieldBaseChangeInternalHom
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- `Ext` of abelian sheaves on the small étale site at its object universe, pinned. -/
local instance (priority := 3000) hasExt_smallEtale_objectUniverse_fieldBaseChangeInternalHom
    (Y : Scheme.{u}) : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  CategoryTheory.IsGrothendieckAbelian.hasExt _

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] in
/-- **`H^q(Y_E, ℋom(G, L)|_{Y_E}) = 0` for `q > 0`** at every finite stage `Y_E`, for `L` an
injective sheaf of `ℤ/n`-modules and `G` with the underlying abelian sheaf of a sheaf of
`ℤ/n`-modules. -/
theorem subsingleton_H_fieldStage_etaleHomOp {n : ℕ} (G : EtaleModules.{u, 0} Λ Y.left)
    (G' L : EtaleModules.{u, 0} (ZMod n) Y.left) [Injective L]
    (e : Stacks.AbelianInternalHom.toAb _ G ≅ Stacks.AbelianInternalHom.toAb _ G')
    (i : FExt k kbar) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian _ Λᵐᵒᵖ).obj
      ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldStageSystem Y kbar |>.obj (op i)).hom).obj
        ((etaleHomOp Λ Y.left G).obj (Stacks.AbelianInternalHom.toAb _ L)))) q) := by
  let g := (fieldStageSystem Y kbar |>.obj (op i)).hom
  let H := (etaleHomOp Λ Y.left G).obj (Stacks.AbelianInternalHom.toAb _ L)
  let E : (etaleModuleUnderlyingAbelian _ Λᵐᵒᵖ).obj
        ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ g).obj H) ≅
      (etaleRestriction.{u, 0} g).obj (internalHomSheaf Y.left.smallEtaleTopology
        (Stacks.AbelianInternalHom.toAb _ G') (Stacks.AbelianInternalHom.toAb _ L)) :=
    ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λᵐᵒᵖ g).app H).symm ≪≫
      (etaleAbelianInverseImageRestrictionIso.{u, 0} g).app _ ≪≫
      (etaleRestriction.{u, 0} g).mapIso
        ((internalHomFunctor _ (Stacks.AbelianInternalHom.toAb _ L)).mapIso e.symm.op)
  exact (subsingleton_H_iff_of_iso E q).2
    (subsingleton_H_etaleRestriction_internalHomSheaf g G' L q hq)

/-- **`ℋom(G, L)` with `L` injective is `Γ(Y_K, -)`-acyclic after restriction to `Y_K`**, for
`L` an injective sheaf of `ℤ/n`-modules and `G` with the underlying abelian sheaf of a sheaf of
`ℤ/n`-modules. -/
theorem rightAcyclic_fieldBaseChange_etaleHomOp
    [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y kbar))]
    [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)] {n : ℕ} (G : EtaleModules.{u, 0} Λ Y.left)
    (G' L : EtaleModules.{u, 0} (ZMod n) Y.left) [Injective L]
    (e : Stacks.AbelianInternalHom.toAb _ G ≅ Stacks.AbelianInternalHom.toAb _ G') :
    (etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y kbar)).rightAcyclic
      ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj Y kbar)).obj
        ((etaleHomOp Λ Y.left G).obj (Stacks.AbelianInternalHom.toAb _ L))) :=
  (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).2 fun q hq =>
    isZero_rightDerived_fieldBaseChange_of_stage Λᵐᵒᵖ Y kbar _
      (fun i q hq => subsingleton_H_fieldStage_etaleHomOp Λ Y kbar G G' L e i q hq) q hq

end Stacks.EtaleCohomology

end
