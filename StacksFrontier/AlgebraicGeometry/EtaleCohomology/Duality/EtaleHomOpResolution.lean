module

public import StacksFrontier.CategoryTheory.Sites.ZModInternalHom
public import StacksFrontier.CategoryTheory.Sites.ModuleInternalHomResolution
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpComplex
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomSwap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing

/-!
# `ℋom_ℤ(G, -)` carries a resolution by `ℤ/n`-injectives to a resolution

Let `G` be a sheaf of `Λ`-modules on `X_étale` whose underlying abelian sheaf is that of a sheaf
`G'` of `ℤ/n`-modules which is locally constant with finitely presented values, and let
`ω ⟶ J` be a resolution of a sheaf of `ℤ/n`-modules `ω`, locally constant on an injective
module, by a complex of sheaves of `ℤ/n`-modules with injective sections. Then
`ℋom_ℤ(G, ω) ⟶ ℋom_ℤ(G, J)` is a quasi-isomorphism of complexes of sheaves of `Λᵐᵒᵖ`-modules:
forgetting the `Λᵐᵒᵖ`-structure it is `ℋom_{ℤ/n}(G', ω) ⟶ ℋom_{ℤ/n}(G', J)`, which is a
quasi-isomorphism by the vanishing of local `Ext`
(`Stacks.ModuleInternalHom.quasiIso_homFunctor_map`).

## Main results

* `Stacks.ModuleInternalHom.zmodHomForgetNatIso`.
* `Stacks.EtaleCohomology.quasiIso_etaleHomOp_map`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.AbelianInternalHom
  Stacks.ConstantSheaf

universe v u

namespace Stacks.ModuleInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (n : ℕ)
  (G : Sheaf K (ModuleCat.{max u v} (ZMod n)))

/-- `forget ℋom_{ℤ/n}(G, F) ≅ ℋom_ℤ(G, F)` is natural in `F`. -/
lemma zmodHomForgetIso_hom_naturality {F F' : Sheaf K (ModuleCat.{max u v} (ZMod n))}
    (f : F ⟶ F') :
    (homAbFunctor (ZMod n) K G).map f ≫ (zmodHomForgetIso K n G F').hom =
      (zmodHomForgetIso K n G F).hom ≫ internalHomSheafMapRight K (toAb K G)
        ((sheafCompose K (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).map f) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ =>
    NatTrans.ext (funext fun _ => rfl))))

/-- **`forget ∘ ℋom_{ℤ/n}(G, -) ≅ ℋom_ℤ(G, forget -)`.** -/
def zmodHomForgetNatIso :
    homAbFunctor (ZMod n) K G ≅
      sheafCompose K (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v}) ⋙
        internalHomRightFunctor K (toAb K G) :=
  NatIso.ofComponents (zmodHomForgetIso K n G) (fun f => zmodHomForgetIso_hom_naturality K n G f)

end Stacks.ModuleInternalHom

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)

/-- Pre- and postcomposition on the internal Hom commute. -/
lemma internalHomSheafMapRight_comp_mapLeft {G G' : Sheaf K AddCommGrpCat.{max u v}}
    (f : G' ⟶ G) {I I' : Sheaf K AddCommGrpCat.{max u v}} (h : I ⟶ I') :
    internalHomSheafMapRight K G h ≫ internalHomSheafMapLeft K f I' =
      internalHomSheafMapLeft K f I ≫ internalHomSheafMapRight K G' h :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ =>
    NatTrans.ext (funext fun _ => rfl))))

/-- **`ℋom_ℤ(G, -) ≅ ℋom_ℤ(G', -)` for `G ≅ G'`**, as functors. -/
def internalHomRightFunctorIsoOfIso {G G' : Sheaf K AddCommGrpCat.{max u v}} (e : G ≅ G') :
    internalHomRightFunctor K G ≅ internalHomRightFunctor K G' :=
  NatIso.ofComponents (fun B => (internalHomFunctor K B).mapIso e.symm.op)
    (fun h => internalHomSheafMapRight_comp_mapLeft K e.inv h)

end Stacks.AbelianInternalHom

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {X : Scheme.{u}} {n : ℕ} [NeZero n]

/-- `ℋom_ℤ(G, -)` preserves zero morphisms. -/
local instance homOpFunctor_preservesZeroMorphisms_resolution (G : EtaleModules.{u, 0} Λ X) :
    (homOpFunctor X.smallEtaleTopology G).PreservesZeroMorphisms :=
  ⟨fun F F' => homOpMap_zero X.smallEtaleTopology G F F'⟩

/-- `forget ∘ ℋom_{ℤ/n}(G', -)` preserves zero morphisms. -/
local instance homAbFunctor_preservesZeroMorphisms_resolution
    (G' : EtaleModules.{u, 0} (ZMod n) X) :
    (Stacks.ModuleInternalHom.homAbFunctor (ZMod n) X.smallEtaleTopology
      G').PreservesZeroMorphisms :=
  inferInstanceAs ((Stacks.ModuleInternalHom.homFunctor X.smallEtaleTopology (ZMod n) G' ⋙
    etaleModuleForgetAb.{u, 0} (ZMod n) X).PreservesZeroMorphisms)

/-- The abelian sheaf underlying `ℋom_ℤ(G, F)`, for `F` a sheaf of `ℤ/n`-modules, is
`ℋom_{ℤ/n}(G', F)`, naturally in `F`. -/
def etaleHomOpForgetZModIso (G : EtaleModules.{u, 0} Λ X)
    (G' : EtaleModules.{u, 0} (ZMod n) X) (e : toAb _ G ≅ toAb _ G') :
    etaleModuleForgetAb.{u, 0} (ZMod n) X ⋙ homOpFunctor X.smallEtaleTopology G ⋙
        etaleModuleForgetAb.{u, 0} Λᵐᵒᵖ X ≅
      Stacks.ModuleInternalHom.homAbFunctor (ZMod n) X.smallEtaleTopology G' :=
  Functor.isoWhiskerLeft _ (homOpFunctorForgetIso X.smallEtaleTopology G ≪≫
      internalHomRightFunctorIsoOfIso X.smallEtaleTopology e) ≪≫
    (Stacks.ModuleInternalHom.zmodHomForgetNatIso X.smallEtaleTopology n G').symm

/-- `etaleHomOpForgetZModIso` on complexes. -/
def etaleHomOpForgetZModComplexIso (G : EtaleModules.{u, 0} Λ X)
    (G' : EtaleModules.{u, 0} (ZMod n) X) (e : toAb _ G ≅ toAb _ G') :
    (etaleModuleForgetAb.{u, 0} (ZMod n) X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (homOpFunctor X.smallEtaleTopology G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          (etaleModuleForgetAb.{u, 0} Λᵐᵒᵖ X).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (Stacks.ModuleInternalHom.homAbFunctor (ZMod n) X.smallEtaleTopology
        G').mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.isoWhiskerLeft _ (Functor.mapHomologicalComplexCompIso (Iso.refl _) _) ≪≫
    Functor.mapHomologicalComplexCompIso (etaleHomOpForgetZModIso Λ G G' e) _

/-- **`ℋom_ℤ(G, ω) ⟶ ℋom_ℤ(G, J)` is a quasi-isomorphism** for a resolution `ω ⟶ J` by sheaves
of `ℤ/n`-modules with injective sections, `ω` locally constant on an injective module and `G`
with the underlying abelian sheaf of a locally constant sheaf of `ℤ/n`-modules with finitely
presented values. -/
theorem quasiIso_etaleHomOp_map (G : EtaleModules.{u, 0} Λ X)
    (G' : EtaleModules.{u, 0} (ZMod n) X) (e : toAb _ G ≅ toAb _ G')
    (hG' : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} X.smallEtaleTopology
      (ZMod n) G')
    {ω : EtaleModules.{u, 0} (ZMod n) X}
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective X.smallEtaleTopology (ZMod n) ω)
    (J : CochainComplex (EtaleModules.{u, 0} (ZMod n) X) ℤ) [J.IsStrictlyGE 0]
    (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ω ⟶ J) [QuasiIso ι]
    (hJ : ∀ (m : ℤ) (U : X.Etaleᵒᵖ), Module.Injective (ZMod n) ((J.X m).obj.obj U)) :
    QuasiIso (((homOpFunctor X.smallEtaleTopology G).mapHomologicalComplex _).map
      (((etaleModuleForgetAb.{u, 0} (ZMod n) X).mapHomologicalComplex _).map ι)) := by
  have h₀ := Stacks.ModuleInternalHom.quasiIso_homFunctor_map X.smallEtaleTopology (ZMod n) J ι hJ
    G' hG' hω
  have h : QuasiIso (((Stacks.ModuleInternalHom.homAbFunctor (ZMod n) X.smallEtaleTopology
      G').mapHomologicalComplex (ComplexShape.up ℤ)).map ι) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
      (etaleModuleForgetAb.{u, 0} (ZMod n) X)).2 h₀
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (etaleModuleForgetAb.{u, 0} Λᵐᵒᵖ X)]
  have key := (quasiIso_iff_comp_left
    ((etaleHomOpForgetZModComplexIso Λ G G' e).hom.app _) _).2 h
  rw [← (etaleHomOpForgetZModComplexIso Λ G G' e).hom.naturality ι] at key
  exact (quasiIso_iff_comp_right _ ((etaleHomOpForgetZModComplexIso Λ G G' e).hom.app J)).1 key

end Stacks.EtaleCohomology

end
