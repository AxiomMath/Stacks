module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing

/-!
# Forgetting the module structure commutes with inverse image and base change, in every universe

For a ring `Λ : Type w` and a morphism of schemes `g : Y ⟶ X`, the underlying
abelian sheaf of the inverse image `g^{-1} M` of a sheaf of `Λ`-modules is the inverse image of
the underlying abelian sheaf of `M`, the coefficients of both being in the universe
`max (u + 1) w` of `Stacks.EtaleCohomology.EtaleModules`. Through it, forgetting the module
structure carries the base change comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` of sheaves of modules
to the one of abelian sheaves.

These are the forms of `Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianInverseImageIso` and
`Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianInverseImageIso_comp_map_etaleModuleBaseChange`
(stated for a commutative `Λ : Type`, with the coefficient universe written `u + 1`) for any
ring in an arbitrary universe. They are stated with the universe `max (u + 1) w` of the abelian
functors `etaleAbelianInverseImage.{u, w}` and `etaleAbelianBaseChange.{u, w}`, the universe
variable being named so that instance resolution spells these levels as the abelian files do: the
kernel compares large terms built from both sides only when the spellings agree.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso`: `g^{-1}(U M) ≅ U(g^{-1} M)`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso_comp_map_etaleModuleBaseChange`: the
  forgetful functor carries the module base change comparison to the abelian one.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.Scheme

/- The abelian base change statements these are compared with find the sheafification of abelian
presheaves on small étale sites through `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`;
stating the results here with the same instance keeps the two spellings syntactically equal, which
the kernel needs when it compares terms built from both. -/
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

universe u w

namespace Stacks.EtaleCohomology

open ModuleBaseChangeForget

variable (Λ : Type w) [Ring Λ]

section Pullback

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Postcomposition with the forgetful functor carries sheaves of modules to abelian sheaves. -/
local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{max (u + 1) w} Λ Z.smallEtaleTopology

/-- Sheafification commutes with forgetting the module structure. -/
local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w}) :=
  ModuleSheaf.preservesSheafification_forget₂.{max (u + 1) w} Λ Z.smallEtaleTopology

/-- **Forgetting the module structure preserves the left Kan extensions defining inverse
image**: the comma categories are filtered (base change of étale schemes is representably
flat), and the forgetful functor preserves filtered colimits. -/
theorem forget₂_preservesLeftKanExtensions_smallEtaleBaseChange :
    (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w}).PreservesLeftKanExtensions
      (smallEtaleBaseChange g).op := by
  intro P
  have hfil : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange g).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange g) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) w, max (u + 1) w, u, u + 1} _
  infer_instance

attribute [local instance] forget₂_preservesLeftKanExtensions_smallEtaleBaseChange

/-- **Inverse image commutes with forgetting the module structure**:
`g^{-1}(U M) ≅ U(g^{-1} M)`, the inverse image of abelian sheaves being
`Stacks.EtaleCohomology.etaleAbelianInverseImage`. -/
def etaleModuleForgetInverseImageIso :
    etaleModuleForgetAb.{u, w} Λ X ⋙ etaleAbelianInverseImage.{u, w} g ≅
      etaleModuleInverseImage.{u, w} Λ g ⋙ etaleModuleForgetAb.{u, w} Λ Y :=
  Functor.isoWhiskerLeft _ (Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallEtaleBaseChange g) AddCommGrpCat.{max (u + 1) w} X.smallEtaleTopology
      Y.smallEtaleTopology).symm ≪≫
    asIso (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) X.smallEtaleTopology
      Y.smallEtaleTopology
      (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w})).natTrans

/-- **The comparison matches the units**: `U` applied to the unit of `g^{-1} ⊣ g_*` on modules is
the unit of `g^{-1} ⊣ g_*` on abelian sheaves followed by `g_*` of the comparison. -/
theorem etaleModuleForgetInverseImageIso_unit (M : EtaleModules.{u, w} Λ X) :
    (etaleModuleForgetAb.{u, w} Λ X).map ((etaleModuleInverseImageAdj.{u, w} Λ g).unit.app M) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
          AddCommGrpCat.{max (u + 1) w} X.smallEtaleTopology Y.smallEtaleTopology).unit.app
          ((etaleModuleForgetAb.{u, w} Λ X).obj M) ≫
        ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) w}
          X.smallEtaleTopology Y.smallEtaleTopology).map
          ((etaleModuleForgetInverseImageIso Λ g).hom.app M) := by
  have h1 := coefficientSheafPullbackTwoSquare_unit (smallEtaleBaseChange g) X.smallEtaleTopology
    Y.smallEtaleTopology (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w}) M
  have h2 := Adjunction.unit_leftAdjointUniq_hom_app
    ((smallEtaleBaseChange g).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) w}
      X.smallEtaleTopology Y.smallEtaleTopology)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
      AddCommGrpCat.{max (u + 1) w} X.smallEtaleTopology Y.smallEtaleTopology)
    ((etaleModuleForgetAb.{u, w} Λ X).obj M)
  refine h1.trans ?_
  simp only [etaleModuleForgetInverseImageIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, asIso_hom,
    Functor.map_comp, ← h2, Category.assoc]
  simp only [Functor.sheafPullbackConstruction.sheafPullbackIso, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl


/-- `Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso_unit`, for the
inverse image adjunction `Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj`. -/
theorem etaleModuleForgetInverseImageIso_unit' (M : EtaleModules.{u, w} Λ X) :
    (etaleModuleForgetAb.{u, w} Λ X).map ((etaleModuleInverseImageAdj.{u, w} Λ g).unit.app M) =
      (etaleAbelianInverseImageDirectImageAdj.{u, w} g).unit.app
          ((etaleModuleForgetAb.{u, w} Λ X).obj M) ≫
        ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) w}
          X.smallEtaleTopology Y.smallEtaleTopology).map
          ((etaleModuleForgetInverseImageIso Λ g).hom.app M) :=
  etaleModuleForgetInverseImageIso_unit Λ g M


end Pullback

/-- **The mate of the comparison `g^{-1} U ≅ U g^{-1}` is the identity of `U g_* = g_* U`**: the
comparison matches the units of the two inverse image adjunctions, and the unit followed by the
direct image of the counit is the identity. -/
theorem mateEquiv_etaleModuleForgetInverseImageIso {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (mateEquiv (etaleModuleInverseImageAdj.{u, w} Λ g)
      (etaleAbelianInverseImageDirectImageAdj.{u, w} g)
      (TwoSquare.mk _ _ _ _ (etaleModuleForgetInverseImageIso Λ g).hom)).natTrans =
      𝟙 (etaleModuleDirectImage.{u, w} Λ g ⋙ etaleModuleForgetAb.{u, w} Λ X) := by
  ext N : 2
  have hu := etaleModuleForgetInverseImageIso_unit' Λ g
    ((etaleModuleDirectImage.{u, w} Λ g).obj N)
  have ht := (etaleModuleInverseImageAdj.{u, w} Λ g).right_triangle_components N
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Category.id_comp, NatTrans.id_app]
  show (etaleAbelianInverseImageDirectImageAdj.{u, w} g).unit.app
        ((etaleModuleForgetAb.{u, w} Λ X).obj ((etaleModuleDirectImage.{u, w} Λ g).obj N)) ≫
      (etaleAbelianDirectImage.{u, w} g).map
        ((etaleModuleForgetInverseImageIso Λ g).hom.app
          ((etaleModuleDirectImage.{u, w} Λ g).obj N)) ≫
      (etaleModuleForgetAb.{u, w} Λ X).map ((etaleModuleDirectImage.{u, w} Λ g).map
        ((etaleModuleInverseImageAdj.{u, w} Λ g).counit.app N)) = 𝟙 _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hu.symm).trans
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg (etaleModuleForgetAb.{u, w} Λ X).map ht).trans
        (CategoryTheory.Functor.map_id _ _))))

/-- `Stacks.EtaleCohomology.mateEquiv_etaleModuleForgetInverseImageIso`, as an
equality of 2-squares. -/
theorem mateEquiv_etaleModuleForgetInverseImageIso' {X Y : Scheme.{u}} (g : Y ⟶ X) :
    mateEquiv (etaleModuleInverseImageAdj.{u, w} Λ g)
      (etaleAbelianInverseImageDirectImageAdj.{u, w} g)
      (TwoSquare.mk _ _ _ _ (etaleModuleForgetInverseImageIso Λ g).hom) =
      TwoSquare.mk (etaleModuleDirectImage.{u, w} Λ g) (etaleModuleForgetAb.{u, w} Λ Y)
        (etaleModuleForgetAb.{u, w} Λ X) (etaleAbelianDirectImage.{u, w} g) (𝟙 _) :=
  TwoSquare.ext _ _ fun N => by
    have := congrArg (fun t => t.app N) (mateEquiv_etaleModuleForgetInverseImageIso Λ g)
    exact this

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (h : g' ≫ f = f' ≫ g)

/-- **The forgetful functor carries the module base change comparison to the abelian one**: at a
sheaf of `Λ`-modules `M` on `X_étale`, `U` of the module comparison
`g^{-1} f_* M ⟶ f'_* (g')^{-1} M`, preceded by the comparison `g^{-1} U ≅ U g^{-1}`, is the
abelian comparison at `U M` followed by `f'_*` of the comparison `(g')^{-1} U ≅ U (g')^{-1}`. -/
theorem etaleModuleForgetInverseImageIso_comp_map_etaleModuleBaseChange
    (M : EtaleModules.{u, w} Λ X) :
    (etaleModuleForgetInverseImageIso Λ g).hom.app
        ((etaleModuleDirectImage.{u, w} Λ f).obj M) ≫
      (etaleModuleForgetAb.{u, w} Λ Y').map ((etaleModuleBaseChange Λ f f' g g' h.symm).app M) =
    (etaleAbelianBaseChange.{u, w} f g g' f' h).app
        ((etaleModuleForgetAb.{u, w} Λ X).obj M) ≫
      (etaleAbelianDirectImage.{u, w} f').map
        ((etaleModuleForgetInverseImageIso Λ g').hom.app M) := by
  have hcube := Stacks.CategoryTheory.mateEquiv_symm_hComp_eq
    (G := etaleModuleDirectImage.{u, w} Λ f) (H := etaleModuleDirectImage.{u, w} Λ f')
    (G' := etaleAbelianDirectImage.{u, w} f) (H' := etaleAbelianDirectImage.{u, w} f')
    (etaleModuleInverseImageAdj.{u, w} Λ g') (etaleModuleInverseImageAdj.{u, w} Λ g)
    (etaleAbelianInverseImageDirectImageAdj.{u, w} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, w} g)
    (TwoSquare.mk _ _ _ _ (etaleModuleForgetInverseImageIso Λ g').hom)
    (TwoSquare.mk _ _ _ _ (etaleModuleForgetInverseImageIso Λ g).hom)
    (𝟙 (etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleForgetAb.{u, w} Λ Y) :
      etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleForgetAb.{u, w} Λ Y ⟶
        etaleModuleForgetAb.{u, w} Λ X ⋙ etaleAbelianDirectImage.{u, w} f)
    (𝟙 (etaleModuleDirectImage.{u, w} Λ f' ⋙ etaleModuleForgetAb.{u, w} Λ Y') :
      etaleModuleForgetAb.{u, w} Λ X' ⋙ etaleAbelianDirectImage.{u, w} f' ⟶
        etaleModuleDirectImage.{u, w} Λ f' ⋙ etaleModuleForgetAb.{u, w} Λ Y')
    (TwoSquare.mk _ _ _ _ ((etaleModuleDirectImageComp.{u, w} Λ g' f (f' ≫ g) h.symm).hom ≫
      (etaleModuleDirectImageComp.{u, w} Λ f' g (f' ≫ g) rfl).inv))
    (TwoSquare.mk _ _ _ _ ((etaleAbelianDirectImageCompIso'.{u, w} g' f (f' ≫ g) h.symm).hom ≫
      (etaleAbelianDirectImageCompIso'.{u, w} f' g (f' ≫ g) rfl).inv)) (by
        rw [mateEquiv_etaleModuleForgetInverseImageIso',
          mateEquiv_etaleModuleForgetInverseImageIso']
        refine TwoSquare.ext _ _ fun M => ?_
        refine Sheaf.hom_ext ?_
        refine NatTrans.ext (funext fun U => ?_)
        rfl)
  have h0 := congrArg (fun t => t.natTrans.app M) hcube
  simp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at h0
  rw [etaleModuleBaseChange_eq_mateEquiv_symm,
    etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, w} f g g' f' h
      (f' ≫ g) h.symm rfl]
  refine h0.trans ((Category.comp_id _).trans ?_)
  exact (congrArg (· ≫ _) (show (Functor.whiskerRight
      (𝟙 (etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleForgetAb.{u, w} Λ Y) :
        etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleForgetAb.{u, w} Λ Y ⟶
          etaleModuleForgetAb.{u, w} Λ X ⋙ etaleAbelianDirectImage.{u, w} f)
      (etaleAbelianInverseImage.{u, w} g)).app M = 𝟙 _ from
        CategoryTheory.Functor.map_id (etaleAbelianInverseImage.{u, w} g) _)).trans
    (Category.id_comp _)

end Stacks.EtaleCohomology

end
