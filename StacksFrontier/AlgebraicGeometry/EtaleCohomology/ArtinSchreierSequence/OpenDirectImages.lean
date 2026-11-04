module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem

/-!
# The direct images of `𝐆_a` from the open subschemes, as a presheaf on the opens

Let `X` be a scheme. For an open `U ⊆ X` write `ι_U : U ⟶ X` for the inclusion. The direct image
`ι_{U,*} 𝐆_{a,U}` is the abelian sheaf on the small étale site of `X` whose sections over an étale
`X`-scheme `W` are the global functions on `W ×_X U`. For `V ≤ U` restriction along
`W ×_X V ⟶ W ×_X U` is a morphism `ι_{U,*} 𝐆_{a,U} ⟶ ι_{V,*} 𝐆_{a,V}`, so these sheaves form a
presheaf on the opens of `X` with values in abelian sheaves on `X_étale`.

## Main definitions

* `Stacks.ArtinSchreier.openPullbackNatTrans`: the morphisms `W ×_X V ⟶ W ×_X U`, natural in `W`.
* `Stacks.ArtinSchreier.openDirectImage`: the direct image `ι_{U,*} 𝐆_{a,U}`.
* `Stacks.ArtinSchreier.openDirectImageRestriction`: the restriction
  `ι_{U,*} 𝐆_{a,U} ⟶ ι_{V,*} 𝐆_{a,V}` for `V ≤ U`.
* `Stacks.ArtinSchreier.openDirectImagePresheaf`: `U ↦ ι_{U,*} 𝐆_{a,U}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Stacks.ArtinSchreier

variable (X : Scheme.{u})

/-- The functor `W ↦ W ×_X U` from étale `X`-schemes to schemes, for an open `U ⊆ X`. -/
abbrev openPullbackFunctor (U : X.Opens) : X.Etale ⥤ Scheme.{u} :=
  smallEtaleBaseChange U.ι ⋙ Scheme.Etale.forget U ⋙ Over.forget (U : Scheme.{u})

/-- The underlying morphism of schemes of the image of `φ` under `Scheme.Etale.forget Y` is
`φ.left`. -/
@[simp]
theorem etaleForget_map_left {Y : Scheme.{u}} {A B : Y.Etale} (φ : A ⟶ B) :
    ((Scheme.Etale.forget Y).map φ).left = φ.left :=
  rfl

/-- The first projection `W ×_X U ⟶ W` is natural in `W`. -/
theorem openPullbackFunctor_map_fst (U : X.Opens) {W W' : X.Etale} (g : W ⟶ W') :
    (openPullbackFunctor X U).map g ≫ pullback.fst W'.hom U.ι = pullback.fst W.hom U.ι ≫ g.left :=
  smallEtaleBaseChange_map_left_fst _ _

/-- The second projection `W ×_X U ⟶ U` is natural in `W`. -/
theorem openPullbackFunctor_map_snd (U : X.Opens) {W W' : X.Etale} (g : W ⟶ W') :
    (openPullbackFunctor X U).map g ≫ pullback.snd W'.hom U.ι = pullback.snd W.hom U.ι :=
  smallEtaleBaseChange_w U.ι ((smallEtaleBaseChange U.ι).map g)

/-- The morphism `W ×_X V ⟶ W ×_X U` for opens `V ≤ U` of `X`. -/
abbrev openPullbackMap {V U : X.Opens} (h : V ≤ U) (W : X.Etale) :
    pullback W.hom V.ι ⟶ pullback W.hom U.ι :=
  pullback.map W.hom V.ι W.hom U.ι (𝟙 _) (X.homOfLE h) (𝟙 _) (by simp) (by simp)

/-- `openPullbackMap X h W` commutes with the first projections to `W`. -/
theorem openPullbackMap_fst {V U : X.Opens} (h : V ≤ U) (W : X.Etale) :
    openPullbackMap X h W ≫ pullback.fst W.hom U.ι = pullback.fst W.hom V.ι := by
  rw [pullback.lift_fst, Category.comp_id]

/-- `openPullbackMap X h W` covers the inclusion `V ⟶ U` on the second projections. -/
theorem openPullbackMap_snd {V U : X.Opens} (h : V ≤ U) (W : X.Etale) :
    openPullbackMap X h W ≫ pullback.snd W.hom U.ι = pullback.snd W.hom V.ι ≫ X.homOfLE h :=
  pullback.lift_snd _ _ _

/-- The morphisms `W ×_X V ⟶ W ×_X U` for opens `V ≤ U` of `X`, natural in `W`. -/
def openPullbackNatTrans {V U : X.Opens} (h : V ≤ U) :
    openPullbackFunctor X V ⟶ openPullbackFunctor X U where
  app W := openPullbackMap X h W
  naturality W W' g := by
    refine pullback.hom_ext (f := W'.hom) (g := U.ι) ?_ ?_
    · exact (Category.assoc _ _ _).trans
        ((congrArg ((openPullbackFunctor X V).map g ≫ ·) (openPullbackMap_fst X h W')).trans
        ((openPullbackFunctor_map_fst X V g).trans
        ((congrArg (· ≫ g.left) (openPullbackMap_fst X h W)).symm.trans
        ((Category.assoc _ _ _).trans
        ((congrArg (openPullbackMap X h W ≫ ·) (openPullbackFunctor_map_fst X U g)).symm.trans
        (Category.assoc _ _ _).symm)))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg ((openPullbackFunctor X V).map g ≫ ·) (openPullbackMap_snd X h W')).trans
        ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ X.homOfLE h) (openPullbackFunctor_map_snd X V g)).trans
        ((openPullbackMap_snd X h W).symm.trans
        ((congrArg (openPullbackMap X h W ≫ ·) (openPullbackFunctor_map_snd X U g)).symm.trans
        (Category.assoc _ _ _).symm)))))

/-- The component of `openPullbackNatTrans X h` at `W` is `openPullbackMap X h W`. -/
theorem openPullbackNatTrans_app {V U : X.Opens} (h : V ≤ U) (W : X.Etale) :
    (openPullbackNatTrans X h).app W = openPullbackMap X h W :=
  rfl

/-- `openPullbackNatTrans` is the identity for `U ≤ U`. -/
theorem openPullbackNatTrans_id (U : X.Opens) : openPullbackNatTrans X (le_refl U) = 𝟙 _ := by
  ext W : 2
  rw [NatTrans.id_app, openPullbackNatTrans_app]
  refine pullback.hom_ext (f := W.hom) (g := U.ι) ?_ ?_
  · exact (openPullbackMap_fst X _ W).trans (Category.id_comp _).symm
  · exact (openPullbackMap_snd X _ W).trans
      (((congrArg (pullback.snd W.hom U.ι ≫ ·) (X.homOfLE_rfl U)).trans
        (Category.comp_id _)).trans (Category.id_comp _).symm)

/-- `openPullbackNatTrans` is compatible with composition of inclusions `Z ≤ V ≤ U`. -/
theorem openPullbackNatTrans_comp {Z V U : X.Opens} (h₁ : Z ≤ V) (h₂ : V ≤ U) :
    openPullbackNatTrans X (h₁.trans h₂) =
      openPullbackNatTrans X h₁ ≫ openPullbackNatTrans X h₂ := by
  ext W : 2
  rw [NatTrans.comp_app, openPullbackNatTrans_app, openPullbackNatTrans_app,
    openPullbackNatTrans_app]
  refine pullback.hom_ext (f := W.hom) (g := U.ι) ?_ ?_
  · exact (openPullbackMap_fst X _ W).trans (((congrArg (openPullbackMap X h₁ W ≫ ·)
      (openPullbackMap_fst X h₂ W)).trans (openPullbackMap_fst X h₁ W)).symm.trans
      (Category.assoc _ _ _).symm)
  · exact (openPullbackMap_snd X _ W).trans (((congrArg (openPullbackMap X h₁ W ≫ ·)
      (openPullbackMap_snd X h₂ W)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ X.homOfLE h₂) (openPullbackMap_snd X h₁ W)).trans
      ((Category.assoc _ _ _).trans (congrArg (pullback.snd W.hom Z.ι ≫ ·)
        (X.homOfLE_homOfLE h₁ h₂)))))).symm.trans (Category.assoc _ _ _).symm)

/-- **The direct image `ι_{U,*} 𝐆_{a,U}` from an open subscheme.** -/
abbrev openDirectImage (U : X.Opens) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (etaleAbelianDirectImage.{u, 0} U.ι).obj (additiveSheaf.{u, 0} U)

/-- Restriction `ι_{U,*} 𝐆_{a,U} ⟶ ι_{V,*} 𝐆_{a,V}` along `W ×_X V ⟶ W ×_X U`, for `V ≤ U`. -/
def openDirectImageRestriction {V U : X.Opens} (h : V ≤ U) :
    openDirectImage X U ⟶ openDirectImage X V :=
  ⟨{ app W := (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
        ((openPullbackNatTrans X h).app W.unop).op
     naturality W W' g := by
       have hn := (openPullbackNatTrans X h).naturality g.unop
       change (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
             ((openPullbackFunctor X U).map g.unop).op ≫
           (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
             ((openPullbackNatTrans X h).app W'.unop).op =
         (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
             ((openPullbackNatTrans X h).app W.unop).op ≫
           (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
             ((openPullbackFunctor X V).map g.unop).op
       rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hn] }⟩

/-- `openDirectImageRestriction` is the identity for `U ≤ U`. -/
theorem openDirectImageRestriction_id (U : X.Opens) :
    openDirectImageRestriction X (le_refl U) = 𝟙 _ := by
  apply Sheaf.hom_ext
  simp only [openDirectImageRestriction, openPullbackNatTrans_id]
  rfl

/-- `openDirectImageRestriction` is compatible with composition of inclusions `Z ≤ V ≤ U`. -/
theorem openDirectImageRestriction_comp {Z V U : X.Opens} (h₁ : Z ≤ V) (h₂ : V ≤ U) :
    openDirectImageRestriction X (h₁.trans h₂) =
      openDirectImageRestriction X h₂ ≫ openDirectImageRestriction X h₁ := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W => ?_)
  show (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
      ((openPullbackNatTrans X (h₁.trans h₂)).app W.unop).op =
    (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map ((openPullbackNatTrans X h₂).app W.unop).op ≫
      (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map ((openPullbackNatTrans X h₁).app W.unop).op
  rw [openPullbackNatTrans_comp, NatTrans.comp_app, op_comp, Functor.map_comp]

/-- **The presheaf `U ↦ ι_{U,*} 𝐆_{a,U}` on the opens of `X`**, with values in abelian sheaves on
the small étale site of `X`. -/
def openDirectImagePresheaf : X.Opensᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj U := openDirectImage X U.unop
  map h := openDirectImageRestriction X h.unop.le
  map_id U := openDirectImageRestriction_id X U.unop
  map_comp h₁ h₂ := openDirectImageRestriction_comp X h₂.unop.le h₁.unop.le

end Stacks.ArtinSchreier

end
