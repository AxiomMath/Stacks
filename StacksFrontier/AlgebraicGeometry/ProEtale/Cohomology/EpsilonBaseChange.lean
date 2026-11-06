module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.AbelianDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ComparisonWithEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMapIsDerivedBaseChangeMap
public import StacksFrontier.CategoryTheory.Adjunction.MateCube
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetAbelianBaseChangeTransfer

/-!
# The pro-étale base change map at sheaves coming from the étale site

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. The base change maps `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian
sheaves on the small étale and on the small pro-étale sites are compared through the inverse
images `ε⁻¹` along the comparison morphisms `ε : X_proétale → X_étale`: the four faces of the
cube formed by the two base change squares and the comparison squares of `ε` are squares of
direct images along functors of sites, and the cube of direct images commutes. By the calculus of
mates (`CategoryTheory.mateEquiv_symm_vComp_eq_of_cube`) the cube of inverse images commutes,
which is the compatibility of the two base change maps with `ε⁻¹`.

## Main results

* `AlgebraicGeometry.ProEtale.epsilon_pushforwardCube`: the cube of direct images commutes.
* `AlgebraicGeometry.ProEtale.epsilon_baseChange_cube`: the two base change maps are compatible
  with `ε⁻¹`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TwoSquare
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.ProEtale

section Squares

variable {Z W : Scheme.{u}} (h : Z ⟶ W)

/-- Viewing an étale `W`-scheme as a pro-étale one and base changing it along `h` is base
changing it and viewing it as a pro-étale `Z`-scheme, on the nose; so the square of direct images
`ε_* ⋙ h_{étale,*} = h_{proétale,*} ⋙ ε_*` is the identity. -/
abbrev epsilonDirectImageSquare :
    TwoSquare (epsilonDirectImage.{u, 0} Z) (proetaleAbelianDirectImage h)
      (etaleAbelianDirectImage.{u, 0} h) (epsilonDirectImage.{u, 0} W) :=
  𝟙 _

/-- The canonical map `ε⁻¹ h_{étale,*} ⟶ h_{proétale,*} ε⁻¹` of Stacks 09A6, the mate of the
square of direct images `AlgebraicGeometry.ProEtale.epsilonDirectImageSquare`. -/
abbrev epsilonDirectImageComparison :
    TwoSquare (etaleAbelianDirectImage.{u, 0} h) (epsilonInverseImage.{u, 0} Z)
      (epsilonInverseImage.{u, 0} W) (proetaleAbelianDirectImage h) :=
  (mateEquiv (epsilonAdjunction.{u, 0} Z) (epsilonAdjunction.{u, 0} W)).symm
    (epsilonDirectImageSquare h)

/-- The comparison `ε⁻¹ ⋙ h_{proétale}⁻¹ ⟶ h_{étale}⁻¹ ⋙ ε⁻¹` of inverse images: the
conjugate of the identity of the composite direct images. -/
abbrev epsilonInverseImageSquare :
    epsilonInverseImage.{u, 0} W ⋙ proetaleAbelianInverseImage h ⟶
      etaleAbelianInverseImage.{u, 0} h ⋙ epsilonInverseImage.{u, 0} Z :=
  (conjugateEquiv ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).comp
      (epsilonAdjunction.{u, 0} Z))
    ((epsilonAdjunction.{u, 0} W).comp (proetaleAbelianInverseImageAdjunction h))).symm
    (eqToHom rfl)

/-- The comparison `h_{étale}⁻¹ ⋙ ε⁻¹ ⟶ ε⁻¹ ⋙ h_{proétale}⁻¹`, the conjugate in the other
direction, inverse to `AlgebraicGeometry.ProEtale.epsilonInverseImageSquare`. -/
abbrev epsilonInverseImageSquareInv :
    etaleAbelianInverseImage.{u, 0} h ⋙ epsilonInverseImage.{u, 0} Z ⟶
      epsilonInverseImage.{u, 0} W ⋙ proetaleAbelianInverseImage h :=
  (conjugateEquiv ((epsilonAdjunction.{u, 0} W).comp (proetaleAbelianInverseImageAdjunction h))
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).comp
      (epsilonAdjunction.{u, 0} Z))).symm (eqToHom rfl)

/-- The comparison `ε⁻¹ ⋙ h_{proétale}⁻¹ ⟶ h_{étale}⁻¹ ⋙ ε⁻¹` of inverse images is an
isomorphism. -/
instance isIso_epsilonInverseImageSquare : IsIso (epsilonInverseImageSquare h) :=
  @conjugateEquiv_symm_iso _ _ _ _ _ _ _ _ _ _ _ (IsIso.id _)

/-- The comparison `h_{étale}⁻¹ ⋙ ε⁻¹ ⟶ ε⁻¹ ⋙ h_{proétale}⁻¹` of inverse images is an
isomorphism. -/
instance isIso_epsilonInverseImageSquareInv : IsIso (epsilonInverseImageSquareInv h) :=
  @conjugateEquiv_symm_iso _ _ _ _ _ _ _ _ _ _ _ (IsIso.id _)

/-- The square of direct images `ε_* ⋙ h_{étale,*} = h_{proétale,*} ⋙ ε_*` is an isomorphism. -/
instance isIso_epsilonDirectImageSquare : IsIso (epsilonDirectImageSquare h).natTrans :=
  IsIso.id _

end Squares

section Comparison

/-- A morphism `L A ⟶ B` into an object of the essential image of a fully faithful left adjoint
`L` is invertible as soon as its image under the right adjoint is. -/
theorem isIso_of_isIso_map_of_mem_essImage {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.unit] {A : C} {B : D} (φ : L.obj A ⟶ B)
    (hB : L.essImage B) (hφ : IsIso (R.map φ)) : IsIso φ := by
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have : L.Full := hff.full
  have : L.Faithful := hff.faithful
  have : IsIso (adj.counit.app B) := adj.isIso_counit_app_iff_mem_essImage.2 hB
  have : IsIso (adj.counit.app (L.obj A)) :=
    adj.isIso_counit_app_iff_mem_essImage.2 (L.obj_mem_essImage A)
  have e := adj.counit.naturality φ
  have : IsIso (adj.counit.app (L.obj A) ≫ φ) := by
    rw [← show (R ⋙ L).map φ ≫ adj.counit.app B = adj.counit.app (L.obj A) ≫ φ from e,
      Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_comp_left (adj.counit.app (L.obj A)) φ

variable {Z W : Scheme.{u}} (h : Z ⟶ W) [QuasiCompact h] [QuasiSeparated h]

/-- **Stacks 09A6 (1) for abelian sheaves, the canonical map**: for `h` quasi-compact and
quasi-separated, the canonical map `ε⁻¹ h_{étale,*} ⟶ h_{proétale,*} ε⁻¹` is invertible. -/
instance isIso_epsilonDirectImageComparison :
    IsIso (epsilonDirectImageComparison h).natTrans := by
  have : ∀ c, IsIso ((epsilonDirectImageComparison h).natTrans.app c) := fun c =>
    isIso_of_isIso_map_of_mem_essImage (epsilonAdjunction.{u, 0} W) _
      (epsilonInverseImage_essImage_proetaleDirectImage.{u, 0} h c)
      (isIso_map_mateEquiv_symm_app_of_isIso_unit (epsilonAdjunction.{u, 0} Z)
        (epsilonAdjunction.{u, 0} W) (epsilonDirectImageSquare h) c)
  exact NatIso.isIso_of_isIso_app _

end Comparison

section Cube

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The identification of the two composite base change functors `Y_étale ⥤ X'_étale` around
the square. -/
def etaleBaseChangeCompSquareIso :
    Stacks.EtaleCohomology.smallEtaleBaseChange f ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange g' ≅
      Stacks.EtaleCohomology.smallEtaleBaseChange g ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange f' :=
  (smallEtaleBaseChangeComp' g' f (g' ≫ f) rfl).symm ≪≫ smallEtaleBaseChangeComp' f' g (g' ≫ f) h

/-- The identification of the two composite base change functors `Y_proétale ⥤ X'_proétale`
around the square. -/
def proetaleBaseChangeCompSquareIso :
    Scheme.proetaleBaseChange f ⋙ Scheme.proetaleBaseChange g' ≅
      Scheme.proetaleBaseChange g ⋙ Scheme.proetaleBaseChange f' :=
  Scheme.proetaleBaseChangeCompIso g' f ≪≫ eqToIso (congrArg Scheme.proetaleBaseChange h) ≪≫
    (Scheme.proetaleBaseChangeCompIso f' g).symm

/-- For `p = q`, the image under `Z.etaleToProetale` of the components at `U` of the
identifications of étale base change functors along `p = q` and `q = q` composes to the component
at `U` of the identification of pro-étale base change functors along `p = q`. -/
theorem etaleToProetale_map_eqToHom_app_comp {Z W : Scheme.{u}} {p q : Z ⟶ W} (hpq : p = q)
    (hqq : q = q) (U : W.Etale) :
    Z.etaleToProetale.map
        ((eqToHom (congrArg Stacks.EtaleCohomology.smallEtaleBaseChange hpq)).app U) ≫
      Z.etaleToProetale.map
        ((eqToHom (congrArg Stacks.EtaleCohomology.smallEtaleBaseChange hqq)).app U) =
      (eqToHom (congrArg Scheme.proetaleBaseChange hpq)).app (W.etaleToProetale.obj U) := by
  subst hpq
  simp only [eqToHom_refl, NatTrans.id_app]
  rw [Z.etaleToProetale.map_id]
  exact Category.id_comp _

/-- **The cube of functors of sites commutes**: on the étale objects of `Y`, the identification
of the composite pro-étale base changes is the identification of the composite étale ones. -/
theorem epsilon_siteCore (U : Y.Etale) :
    (proetaleBaseChangeCompSquareIso f g g' f' h).inv.app (Y.etaleToProetale.obj U) =
      X'.etaleToProetale.map ((etaleBaseChangeCompSquareIso f g g' f' h).inv.app U) := by
  simp only [proetaleBaseChangeCompSquareIso, etaleBaseChangeCompSquareIso, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, smallEtaleBaseChangeComp', Iso.trans_hom,
    eqToIso.inv, eqToIso.hom, Category.assoc]
  rw [← etaleToProetale_map_eqToHom_app_comp (p := f' ≫ g) (q := g' ≫ f) h.symm rfl U]
  exact congrArg ((Scheme.proetaleBaseChangeCompIso f' g).hom.app (Y.etaleToProetale.obj U) ≫ ·)
    (Category.assoc _ _ _)

/-- **The cube of direct images commutes.** -/
theorem epsilon_pushforwardCube :
    TwoSquare.mk _ _ _ _ (proetaleAbelianDirectImageSquare f g f' g' h.symm).hom ≫ₕ
        epsilonDirectImageSquare f =
      ((epsilonDirectImageSquare f' ≫ₕ abelianDirectImageSquare f g g' f' h).whiskerBottom
        (𝟙 _)).whiskerTop (𝟙 _) := by
  ext M : 3
  refine NatTrans.ext (funext fun U => ?_)
  show 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ M.obj.map _ ≫ 𝟙 _ =
    𝟙 _ ≫ ((𝟙 _ ≫ ((𝟙 _ ≫ M.obj.map _) ≫ (M.obj.map _ ≫ 𝟙 _)) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]
  refine (congrArg M.obj.map ?_).trans (M.obj.map_comp _ _)
  exact congrArg Quiver.Hom.op ((epsilon_siteCore f g g' f' h U.unop).trans
    (X'.etaleToProetale.map_comp _ _))

/-- **The cube of inverse images commutes**: the base change of the canonical map of
Stacks 09A6 for `f` along the pro-étale base change map is the étale base change map followed
by the canonical map for `f'`, read through the comparisons of `ε⁻¹` with the inverse images. -/
theorem epsilon_mateCube :
    epsilonDirectImageComparison f ≫ᵥ
        (mateEquiv (proetaleAbelianInverseImageAdjunction g')
          (proetaleAbelianInverseImageAdjunction g)).symm
          (TwoSquare.mk _ _ _ _ (proetaleAbelianDirectImageSquare f g f' g' h.symm).hom) =
      (((mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, 0} g')
          (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)).symm
            (abelianDirectImageSquare f g g' f' h) ≫ᵥ
          epsilonDirectImageComparison f').whiskerRight (epsilonInverseImageSquare g)).whiskerLeft
        (epsilonInverseImageSquareInv g') := by
  refine mateEquiv_symm_vComp_eq_of_cube (epsilonAdjunction.{u, 0} X) (epsilonAdjunction.{u, 0} Y)
    (epsilonAdjunction.{u, 0} X') (epsilonAdjunction.{u, 0} Y')
    (proetaleAbelianInverseImageAdjunction g') (proetaleAbelianInverseImageAdjunction g)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
    _ _ _ _ _ _ ?_
  dsimp only [epsilonInverseImageSquare, epsilonInverseImageSquareInv]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact epsilon_pushforwardCube f g g' f' h

/-- **The étale and pro-étale base change maps are compatible with `ε⁻¹`**, at an abelian sheaf
`c` on `X_étale`. -/
theorem epsilon_baseChange_cube [QuasiCompact f'] [QuasiSeparated f']
    (c : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (epsilonInverseImageSquare g).app ((etaleAbelianDirectImage.{u, 0} f).obj c) ≫
        (epsilonInverseImage.{u, 0} Y').map ((etaleAbelianBaseChange.{u, 0} f g g' f' h).app c) =
      (proetaleAbelianInverseImage g).map ((epsilonDirectImageComparison f).natTrans.app c) ≫
        (proetaleAbelianBaseChange f g f' g' h.symm).app ((epsilonInverseImage.{u, 0} X).obj c) ≫
        (proetaleAbelianDirectImage f').map ((inv (epsilonInverseImageSquareInv g')).app c) ≫
        (inv (epsilonDirectImageComparison f').natTrans).app
          ((etaleAbelianInverseImage.{u, 0} g').obj c) := by
  have e := congrArg (fun t => t.natTrans.app c) (epsilon_mateCube f g g' f' h)
  simp only [vComp_app, TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
    Functor.comp_obj] at e
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso f g g' f' h (g' ≫ f) rfl h,
    NatIso.isIso_inv_app, NatIso.isIso_inv_app]
  rw [Functor.map_inv]
  have e' := e =≫ (inv ((proetaleAbelianDirectImage f').map
      ((epsilonInverseImageSquareInv g').app c)) ≫
    inv ((epsilonDirectImageComparison f').natTrans.app
      ((etaleAbelianInverseImage.{u, 0} g').obj c)))
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, Category.comp_id] at e'
  exact e'.symm

end Cube

end AlgebraicGeometry.ProEtale

end
