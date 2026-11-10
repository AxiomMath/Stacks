module
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.OverSiteDisjointCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsiteFiniteType

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.LocallyConstantOpens
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteTypeLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap

/-!
# Finite type local constancy is Zariski local

A sheaf of `Λ`-modules on the small étale site of a scheme `S` is locally constant of finite type
as soon as its restrictions to the members of an open cover of `S` are.

## Main results

* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstantModuleSheaf_of_isOpenCover`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

/-- **Restriction to an object of the étale site, read on the slice.** For `W` in `S_étale`, the
restriction of `G` to the slice site over `W`, read on the small étale site of `W.left`, is the
restriction of `G` along the étale structure morphism of `W`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_over_iff {S : Scheme.{u}}
    (G : EtaleModules.{u, r} Λ S) (W : S.Etale) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
        (S.smallEtaleTopology.over W) Λ (G.over W) ↔
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
        W.left.smallEtaleTopology Λ ((etaleModuleRestriction.{u, r} Λ W.hom).obj G) := by
  have := _root_.Stacks.ConstantSheaf.smallEtaleOverInverse_isDenseSubsite W
  exact (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff
    W.left.smallEtaleTopology (S.smallEtaleTopology.over W)
    (_root_.Stacks.ConstantSheaf.smallEtaleOverEquivalence W).inverse Λ (G.over W)).symm

/-- **Finite type local constancy is Zariski local.** A sheaf `G` of `Λ`-modules on `S_étale`
whose restrictions to the members of an open cover of `S` are locally constant of finite type is
locally constant of finite type: an object `W` of `S_étale` is covered by the inverse images of
the members, over which `G` is the inverse image of its restriction to a member. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_isOpenCover {S : Scheme.{u}}
    (G : EtaleModules.{u, r} Λ S) {I : Type u} (U : I → S.Opens) (hU : ⨆ k, U k = ⊤)
    (h : ∀ k, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      (U k).toScheme.smallEtaleTopology Λ ((etaleModuleRestriction.{u, r} Λ (U k).ι).obj G)) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      S.smallEtaleTopology Λ G := by
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_local _ Λ G fun W ↦ ?_
  let V : I → W.left.Opens := fun k ↦ W.hom ⁻¹ᵁ U k
  let Wk : ULift.{u + 1} I → S.Etale := fun k ↦ Etale.mk ((V k.down).ι ≫ W.hom)
  let fk : ∀ k, Wk k ⟶ W := fun k ↦ MorphismProperty.Over.homMk (V k.down).ι rfl trivial
  refine ⟨ULift.{u + 1} I, Wk, fk, ?_, fun k ↦ ?_⟩
  · rw [ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun x ↦ ?_
    have hx : W.hom x ∈ (⨆ k, U k : S.Opens) := by
      rw [hU]
      trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact Set.mem_iUnion.2 ⟨ULift.up k, ⟨⟨x, hk⟩, rfl⟩⟩
  · rw [isFiniteTypeLocallyConstantModuleSheaf_over_iff]
    refine ObjectProperty.prop_of_iso _ ?_
      (isFiniteTypeLocallyConstantModuleSheaf_etaleModuleInverseImage Λ
        (W.hom ∣_ U k.down) _ (h k.down))
    exact (etaleModuleInverseImage.{u, r} Λ (W.hom ∣_ U k.down)).mapIso
        ((etaleModuleInverseImageRestrictionIso.{u, r} Λ (U k.down).ι).app G).symm ≪≫
      ((etaleModuleInverseImageCompIso.{u, r} Λ (W.hom ∣_ U k.down) (U k.down).ι).app G).symm ≪≫
      eqToIso (congrArg (fun g ↦ (etaleModuleInverseImage.{u, r} Λ g).obj G)
        (morphismRestrict_ι W.hom (U k.down))) ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, r} Λ ((V k.down).ι ≫ W.hom)).app G

/-- **The stalk of an inverse image is the stalk at the image point** (Tag 03Q1), on the underlying
abelian sheaves of sheaves of `Λ`-modules. -/
def smallEtaleStalkAbEtaleModuleInverseImageIso (Λ : Type (u + 1)) [CommRing Λ]
    {X' X : Scheme.{u}} (g : X' ⟶ X) (x : GeometricPoint X') (M : EtaleModules.{u, u + 1} Λ X) :
    (smallEtaleStalkAb x.hom).obj
        ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ X').obj
          ((etaleModuleInverseImage.{u, u + 1} Λ g).obj M)) ≅
      (smallEtaleStalkAb (x.hom ≫ g)).obj
        ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ X).obj M) :=
  (smallEtaleStalkAb x.hom).mapIso
      (asIso ((etaleModuleInverseImageForget.{u, u + 1} Λ g).app M)).symm ≪≫
    (smallEtaleStalkAb x.hom).mapIso
      (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} g).leftAdjointUniq
        (smallEtaleAdjunctionAb g)).app
          ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ X).obj M)) ≪≫
    (smallEtalePullbackStalkAbIso g x.hom).app _

/-- The annihilation of the stalks at geometric points by integers prime to the residue
characteristics passes to inverse images. -/
theorem nsmul_stalk_etaleModuleInverseImage (Λ : Type (u + 1)) [CommRing Λ]
    {X' X : Scheme.{u}} (g : X' ⟶ X) (M : EtaleModules.{u, u + 1} Λ X)
    (hn : ∀ x : GeometricPoint X, ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj
        ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ X).obj M), n • a = 0)
    (x : GeometricPoint X') : ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj
        ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ X').obj
          ((etaleModuleInverseImage.{u, u + 1} Λ g).obj M)), n • a = 0 := by
  obtain ⟨n, hn0, hp, h⟩ := hn (x.map g)
  refine ⟨n, hn0, hp, fun a ↦ ?_⟩
  let e := smallEtaleStalkAbEtaleModuleInverseImageIso Λ g x M
  apply ConcreteCategory.injective_of_mono_of_preservesPullback e.hom
  rw [map_nsmul, h (e.hom a), map_zero]

end Stacks.EtaleCohomology

end
