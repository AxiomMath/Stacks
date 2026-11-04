module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealBaseRingTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSection

/-!
# The sections `1 ⊗ c` of the conormal module of `T ⊆ T'`

For a closed immersion `j : T ⟶ T'` of objects of the big fppf site with `T'` affine, the conormal
module of `T ⊆ T'` is `𝒪_T ⊗_{R'} I`, `R' = Γ(T', 𝒪_{T'})`, `I = Ker(R' → Γ(T, 𝒪_T))`
(`AlgebraicGeometry.Space.conormalModuleRangeIso`, [Stacks Project, Tag 04CN]). This file
computes that identification on global sections: the section `1 ⊗ c` of `𝒪_T ⊗_{R'} I` is the
class of `c ∈ I` in the conormal module, that is the pullback to `T` of the section `c` of the
defining ideal sheaf
(`AlgebraicGeometry.Space.baseRingTensorSection_conormalModuleRangeSchemeIso_inv`).
On the way it records how the sections `1 ⊗ m` of [Stacks Project, Tag 0D3F] behave under
pullback ([Stacks Project, Tag 03LU]) and under the morphism `𝒪_W ⊗_R I ⟶ 𝓘_{g⁻¹(Z)}`. This is a
step of the computation of the map of ideals of a morphism of deformations in the proof of
[Stacks Project, Tag 0D1K].

## Main definitions

* `AlgebraicGeometry.Space.rangeIdealSection`: the section `c` of the ideal sheaf of `T ⊆ T'`.
* `AlgebraicGeometry.Space.rangeConormalSection`: the class of `c` in the conormal module.
* `AlgebraicGeometry.Space.rangeSchemeSpaceIso`,
  `AlgebraicGeometry.Space.conormalModuleRangeSchemeIso`:
  `AlgebraicGeometry.Space.rangeSpaceIso` and `AlgebraicGeometry.Space.conormalModuleRangeIso` with
  the spaces spelled as `schemeSpace T` and as the source of the inclusion of the subspace.

## Main results

* `AlgebraicGeometry.Space.modulePullbackGlobalSection_baseRingTensorSection`: pulling back
  `1 ⊗ m`.
* `AlgebraicGeometry.Space.baseRingTensorSection_baseRingTensorPreimageIdealHom`: `1 ⊗ a ↦ g^♯a`.
* `AlgebraicGeometry.Space.baseRingTensorSection_conormalModuleRangeSchemeIso_inv`.

## Implementation notes

The source space of `(AlgebraicGeometry.Space.rangeSpaceIso j hj).hom` is spelled
`⟨yoneda.obj T, _⟩`, not `AlgebraicGeometry.Space.schemeSpace T` (a `def`), and its target is
`AlgebraicGeometry.Space.closedSubspaceRangeSpace`, not the source of the inclusion of
`AlgebraicGeometry.Space.rangeSubspace` over which the conormal module lives. Terms mixing the
spellings make unification, and the kernel, unfold the module categories. The computation is
therefore carried out along `AlgebraicGeometry.Space.rangeSchemeSpaceIso`, whose source and target
are spelled as the spaces they are composed with. Sections into the conormal module are typed with
`AlgebraicGeometry.Space.conormalModule` itself, for the same reason.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Composing with the inverse of a composite of three isomorphisms, one at a time. -/
theorem comp_trans_trans_inv {C : Type*} [Category C] {U P Q Q' Q'' : C} (σ : U ⟶ Q'')
    (a : P ≅ Q) (b : Q ≅ Q') (c : Q' ≅ Q'') :
    σ ≫ (a ≪≫ b ≪≫ c).inv = ((σ ≫ c.inv) ≫ b.inv) ≫ a.inv := by
  simp

section Pullback

variable {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T)

/-- **The pullback of the section `1 ⊗ m`** of `𝒪_T ⊗_R M` along `f : X ⟶ T`, read through
`f^*(𝒪_T ⊗_R M) ≅ 𝒪_X ⊗_R M`, is the section `1 ⊗ m` of `𝒪_X ⊗_R M`. -/
theorem modulePullbackGlobalSection_baseRingTensorSection (M : ModuleCat.{u} (baseRing B S hS T))
    (m : M) :
    modulePullbackGlobalSection B S hS f (baseRingTensorSection B S hS (schemeSpace T)
          (baseRingHomOfMap (𝟙 (schemeSpace T))) M m) ≫
        (baseRingTensorModulePullbackIso B S hS f).hom.app M =
      baseRingTensorSection B S hS X (baseRingHomOfMap f) M m :=
  (Category.assoc _ _ _).trans (baseRingTensorSection_pullbackIso_hom B S hS f M m)

/-- The section `1 ⊗ m` of `𝒪_X ⊗_R M`, read on `f^*(𝒪_T ⊗_R M)`, is the pullback of the
section `1 ⊗ m` of `𝒪_T ⊗_R M`. -/
theorem baseRingTensorSection_comp_pullbackIso_inv (M : ModuleCat.{u} (baseRing B S hS T))
    (m : M) :
    baseRingTensorSection B S hS X (baseRingHomOfMap f) M m ≫
        (baseRingTensorModulePullbackIso B S hS f).inv.app M =
      modulePullbackGlobalSection B S hS f (baseRingTensorSection B S hS (schemeSpace T)
          (baseRingHomOfMap (𝟙 (schemeSpace T))) M m) :=
  ((Iso.app (baseRingTensorModulePullbackIso B S hS f) M).eq_comp_inv.2
    (modulePullbackGlobalSection_baseRingTensorSection B S hS f M m)).symm

/-- `AlgebraicGeometry.Space.baseRingTensorSection_comp_pullbackIso_inv`, with the inverse of
the component isomorphism. -/
theorem baseRingTensorSection_comp_pullbackIso_app_inv (M : ModuleCat.{u} (baseRing B S hS T))
    (m : M) :
    baseRingTensorSection B S hS X (baseRingHomOfMap f) M m ≫
        ((baseRingTensorModulePullbackIso B S hS f).app M).inv =
      modulePullbackGlobalSection B S hS f (baseRingTensorSection B S hS (schemeSpace T)
          (baseRingHomOfMap (𝟙 (schemeSpace T))) M m) :=
  baseRingTensorSection_comp_pullbackIso_inv B S hS f M m

end Pullback

/-- The sections `1 ⊗ m` along an equality of base-ring data. -/
theorem baseRingTensorSection_eqToHom (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
    {φ φ' : R →+* modelGlobalFunctions B S hS X} (h : φ = φ') (M : ModuleCat.{u} R) (m : M) :
    baseRingTensorSection B S hS X φ M m ≫
        eqToHom (congrArg (fun φ => (baseRingTensorModule B S hS X φ).obj M) h) =
      baseRingTensorSection B S hS X φ' M m := by
  subst h
  exact Category.comp_id _

/-- Pulling back sections along equal morphisms, read through the identification of the
pulled-back modules. -/
theorem modulePullbackGlobalSection_eqToHom_obj {X Y : AlgebraicSpaces B S hS} {f f' : X ⟶ Y}
    (h : f = f') {M : Modules.{u, u} B S hS Y.1 Y.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M) :
    modulePullbackGlobalSection B S hS f s ≫
        eqToHom (congrArg (fun f => (modulePullback B S hS f).obj M) h) =
      modulePullbackGlobalSection B S hS f' s := by
  subst h
  exact Category.comp_id _

/-- Pulling back twice, read on the pullback along the composite. -/
theorem modulePullbackGlobalSection_comp_modulePullbackCompIso_inv {X Y Z : AlgebraicSpaces B S hS}
    (g : Z ⟶ X) (f : X ⟶ Y) {M : Modules.{u, u} B S hS Y.1 Y.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M) :
    modulePullbackGlobalSection B S hS (g ≫ f) s ≫ (modulePullbackCompIso B S hS g f).inv.app M =
      modulePullbackGlobalSection B S hS g (modulePullbackGlobalSection B S hS f s) :=
  ((Iso.app (modulePullbackCompIso B S hS g f) M).comp_inv_eq.2
    (modulePullbackGlobalSection_modulePullbackGlobalSection B S hS g f s).symm)

/-- `AlgebraicGeometry.Space.modulePullbackGlobalSection_comp_modulePullbackCompIso_inv`, with the
inverse of the component isomorphism. -/
theorem modulePullbackGlobalSection_comp_modulePullbackCompIso_app_inv
    {X Y Z : AlgebraicSpaces B S hS} (g : Z ⟶ X) (f : X ⟶ Y) {M : Modules.{u, u} B S hS Y.1 Y.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M) :
    modulePullbackGlobalSection B S hS (g ≫ f) s ≫ ((modulePullbackCompIso B S hS g f).app M).inv =
      modulePullbackGlobalSection B S hS g (modulePullbackGlobalSection B S hS f s) :=
  modulePullbackGlobalSection_comp_modulePullbackCompIso_inv B S hS g f s

/-- `AlgebraicGeometry.Space.modulePullbackGlobalSection_modulePullbackGlobalSection`, with the
component isomorphism of the comparison. -/
theorem modulePullbackGlobalSection_comp_modulePullbackCompIso_app_hom
    {X Y Z : AlgebraicSpaces B S hS} (g : Z ⟶ X) (f : X ⟶ Y) {M : Modules.{u, u} B S hS Y.1 Y.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M) :
    modulePullbackGlobalSection B S hS g (modulePullbackGlobalSection B S hS f s) ≫
        ((modulePullbackCompIso B S hS g f).app M).hom =
      modulePullbackGlobalSection B S hS (g ≫ f) s :=
  modulePullbackGlobalSection_modulePullbackGlobalSection B S hS g f s

section Ideal

variable {W : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} (g : W ⟶ schemeSpace T)
  (Z : ClosedSubspaces B S hS (schemeSpace T).1)

/-- **The section `1 ⊗ a` of `𝒪_W ⊗_R I` goes to the section `g^♯ a` of the ideal of
`g⁻¹(Z)`.** -/
theorem baseRingTensorSection_baseRingTensorPreimageIdealHom
    (a : closedSubspaceBaseIdeal B S hS Z) :
    baseRingTensorSection B S hS W (baseRingHomOfMap g)
        (ModuleCat.of _ (closedSubspaceBaseIdeal B S hS Z)) a ≫
      baseRingTensorPreimageIdealHom B S hS g Z = preimageIdealSection B S hS g Z a :=
  (cancel_mono (preimageIdealι B S hS g Z)).1 (((Category.assoc _ _ _).trans
    (modelSectionsHomEquiv_unit_comp_baseRingTensorPreimageIdealHom_ι B S hS g Z a)).trans
    (preimageIdealSection_ι B S hS g Z a).symm)

end Ideal

section Conormal

variable {T T' : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))

/-- The global section `c` of the defining ideal sheaf of a closed subspace `T ⊆ T'`, `c` a
function on `T'` vanishing on `T`. -/
abbrev rangeIdealSection (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    unitModule B S hS (schemeSpace T').2 ⟶
      (definingIdealSheaf B S hS (schemeSpace T') (rangeSubspace B S hS j hj)).toSheafOfModules :=
  preimageIdealSection B S hS (𝟙 (schemeSpace T')) (rangeSubspace B S hS j hj) c ≫
    eqToHom (congrArg (fun Z => (definingIdealSheaf B S hS (schemeSpace T') Z).toSheafOfModules)
      (preimageSubspace_id B S hS (rangeSubspace B S hS j hj)))

/-- **The conormal module of `T ⊆ T'`**, `AlgebraicGeometry.Space.conormalModule` of
`AlgebraicGeometry.Space.rangeSubspace`, typed as a module on
`AlgebraicGeometry.Space.closedSubspaceRangeSpace`. -/
def rangeConormalModule :
    Modules.{u, u} B S hS (closedSubspaceRangeSpace B S hS j hj).1
      (closedSubspaceRangeSpace B S hS j hj).2 :=
  conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj)

/-- **The class of `c` in the conormal module of `T ⊆ T'`**: the pullback of the section `c` of
the defining ideal sheaf to the closed subspace, `c` a function on `T'` vanishing on `T`. -/
def rangeConormalSection (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    unitModule B S hS (closedSubspaceRangeSpace B S hS j hj).2 ⟶
      rangeConormalModule B S hS j hj :=
  modulePullbackGlobalSection B S hS
    (subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj))
    (rangeIdealSection B S hS j hj c)

/-- **`T` is the closed subspace of `T'` cut out by `j`**: `AlgebraicGeometry.Space.rangeSpaceIso`,
with source spelled `AlgebraicGeometry.Space.schemeSpace T`. -/
def rangeSchemeSpaceIso : schemeSpace T ≅ closedSubspaceRangeSpace B S hS j hj :=
  rangeSpaceIso B S hS j hj

/-- The isomorphism `AlgebraicGeometry.Space.rangeSchemeSpaceIso` followed by the inclusion of the
closed subspace is the morphism `j`. -/
theorem rangeSchemeSpaceIso_hom_comp_subspaceInclusion :
    (rangeSchemeSpaceIso B S hS j hj).hom ≫
        subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj) =
      schemeSpaceMap j :=
  rangeSpaceIso_hom_comp_subspaceInclusion B S hS j hj

/-- **The conormal module of `T ⊆ T'` is `𝒪_T ⊗_{R'} I`**:
`AlgebraicGeometry.Space.conormalModuleRangeIso`, read along
`AlgebraicGeometry.Space.rangeSchemeSpaceIso`. -/
def conormalModuleRangeSchemeIso :
    (modulePullback B S hS (rangeSchemeSpaceIso B S hS j hj).hom).obj
        (rangeConormalModule B S hS j hj) ≅
      (baseRingTensorModule B S hS (schemeSpace T) (baseRingHomOfMap (schemeSpaceMap j))).obj
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))) :=
  (modulePullbackCompIso B S hS (rangeSchemeSpaceIso B S hS j hj).hom
      (subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj))).app
      (definingIdealSheaf B S hS (schemeSpace T') (rangeSubspace B S hS j hj)).toSheafOfModules ≪≫
    eqToIso (congrArg (fun m => (modulePullback B S hS m).obj
        (definingIdealSheaf B S hS (schemeSpace T') (rangeSubspace B S hS j hj)).toSheafOfModules)
      (rangeSchemeSpaceIso_hom_comp_subspaceInclusion B S hS j hj)) ≪≫
    (modulePullback B S hS (schemeSpaceMap j)).mapIso
      (definingIdealSheafRangeIso B S hS j hj hT').symm ≪≫
    (baseRingTensorModulePullbackIso B S hS (schemeSpaceMap j)).app _

/-- **The section `1 ⊗ c` of `𝒪_T ⊗_{R'} I` is the class of `c` in the conormal module of
`T ⊆ T'`**, read through `AlgebraicGeometry.Space.conormalModuleRangeSchemeIso`. -/
theorem baseRingTensorSection_conormalModuleRangeSchemeIso_inv
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    baseRingTensorSection B S hS (schemeSpace T) (baseRingHomOfMap (schemeSpaceMap j))
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))) c ≫
        (conormalModuleRangeSchemeIso B S hS j hj hT').inv =
      modulePullbackGlobalSection B S hS (rangeSchemeSpaceIso B S hS j hj).hom
        (rangeConormalSection B S hS j hj c) := by
  have hm : schemeSpaceMap j = (rangeSchemeSpaceIso B S hS j hj).hom ≫
      subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj) :=
    (rangeSchemeSpaceIso_hom_comp_subspaceInclusion B S hS j hj).symm
  have h3 := modulePullbackGlobalSection_comp_modulePullbackCompIso_app_inv B S hS
    (rangeSchemeSpaceIso B S hS j hj).hom
    (subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj))
    (rangeIdealSection B S hS j hj c)
  refine (comp_trans_trans_inv _ _ _ _).trans ?_
  refine (congrArg (fun t => (t ≫ _) ≫ _) (?_ : _ = modulePullbackGlobalSection B S hS
    (schemeSpaceMap j) (rangeIdealSection B S hS j hj c))).trans ?_
  · refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (modulePullback B S hS (schemeSpaceMap j)).map
      (definingIdealSheafRangeIso B S hS j hj hT').hom)
      (baseRingTensorSection_comp_pullbackIso_inv B S hS (schemeSpaceMap j)
        (ModuleCat.of (baseRing B S hS T')
          (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))) c)).trans ?_
    refine (modulePullbackGlobalSection_comp B S hS _ _ _).symm.trans ?_
    refine congrArg (modulePullbackGlobalSection B S hS (schemeSpaceMap j)) ?_
    refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)
    exact (congrArg (_ ≫ ·) (definingIdealSheafPreimageIso_hom B S hS _ _ _ _)).trans
      (baseRingTensorSection_baseRingTensorPreimageIdealHom B S hS _ _ c)
  refine (congrArg (· ≫ _) (?_ : _ = modulePullbackGlobalSection B S hS
    ((rangeSchemeSpaceIso B S hS j hj).hom ≫
      subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj))
    (rangeIdealSection B S hS j hj c))).trans ?_
  · exact modulePullbackGlobalSection_eqToHom_obj B S hS hm _
  exact h3

end Conormal

end AlgebraicGeometry.Space

end
