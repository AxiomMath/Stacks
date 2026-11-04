module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.OpenDirectImages
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.CoveringResolution.Augmentation

/-!
# The Čech complex of `𝐆_a` for a Zariski covering, on the small étale site

Let `X` be a scheme and `U : ι → X.Opens` a family of opens. The Čech complex of the presheaf
`V ↦ ι_{V,*} 𝐆_{a,V}` of `Stacks.ArtinSchreier.openDirectImagePresheaf` for the family `U` is a
cochain complex of abelian sheaves on the small étale site of `X` whose degree `n` term is the
product over the `(n + 1)`-tuples `x` of the direct images `ι_{U_x,*} 𝐆_{a,U_x}`,
`U_x = U_{x_0} ∩ ⋯ ∩ U_{x_n}`. Restricting a function on `W` to the `W ×_X U_i` augments it by
`𝐆_a`. The Frobenius of `𝐆_a`, applied termwise, is an endomorphism of the augmented complex.

## Main definitions

* `Stacks.ArtinSchreier.openDirectImageUnit`: `𝐆_a ⟶ ι_{U,*} 𝐆_{a,U}`.
* `Stacks.ArtinSchreier.openDirectImageFrobenius`: the Frobenius of the presheaf
  `V ↦ ι_{V,*} 𝐆_{a,V}`.
* `Stacks.ArtinSchreier.zariskiCechComplex`, `Stacks.ArtinSchreier.zariskiCechAugmentation`:
  the Čech complex and its augmentation by `𝐆_a`.
* `Stacks.ArtinSchreier.zariskiCechFrobenius`: the Frobenius of the Čech complex.

## Main results

* `Stacks.ArtinSchreier.zariskiCechAugmentation_comp_frobenius`: the augmentation intertwines
  the Frobenius of `𝐆_a` and that of the Čech complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechZero

universe u

namespace Stacks.ArtinSchreier

variable (X : Scheme.{u})

/-- On sections, `𝐆_a` over `W` is the additive group of `Γ(W, 𝒪_W)` and its restriction along
`g : W' ⟶ W` is the pullback of functions along `g`. -/
theorem additiveSheaf_map {W W' : X.Etale} (g : W' ⟶ W) :
    (additiveSheaf.{u, 0} X).obj.map g.op =
      (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map g.left.op :=
  rfl

/-- On sections, `ι_{U,*} 𝐆_{a,U}` over `W` is `Γ(W ×_X U)`, with restriction maps the pullbacks
of functions along the induced maps of fibre products. -/
theorem openDirectImage_map (U : X.Opens) {W W' : X.Etale} (g : W' ⟶ W) :
    (openDirectImage X U).obj.map g.op =
      (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map ((openPullbackFunctor X U).map g).op :=
  rfl

/-- **The restriction `𝐆_a ⟶ ι_{U,*} 𝐆_{a,U}`** of a function on `W` to `W ×_X U`. -/
def openDirectImageUnit (U : X.Opens) : additiveSheaf.{u, 0} X ⟶ openDirectImage X U :=
  ⟨{ app W := (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map (pullback.fst W.unop.hom U.ι).op
     naturality W W' g := by
       change (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map g.unop.left.op ≫
           (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map (pullback.fst W'.unop.hom U.ι).op =
         (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map (pullback.fst W.unop.hom U.ι).op ≫
           (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map ((openPullbackFunctor X U).map g.unop).op
       exact ((Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map_comp _ _).symm.trans
         ((congrArg (fun z ↦ (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map z)
           ((op_comp ..).symm.trans (congrArg Quiver.Hom.op
             (openPullbackFunctor_map_fst X U g.unop).symm |>.trans (op_comp ..)))).trans
           ((Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map_comp _ _)) }⟩

/-- On sections over `W`, the restriction `𝐆_a ⟶ ι_{U,*} 𝐆_{a,U}` is the pullback of functions
along the projection `W ×_X U ⟶ W`. -/
theorem openDirectImageUnit_app (U : X.Opens) (W : X.Etaleᵒᵖ) :
    (openDirectImageUnit X U).hom.app W =
      (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map (pullback.fst W.unop.hom U.ι).op :=
  rfl

/-- On sections over `W`, the transition map `ι_{U,*} 𝐆_{a,U} ⟶ ι_{V,*} 𝐆_{a,V}` for `V ≤ U` is the
pullback of functions along the induced map `W ×_X V ⟶ W ×_X U`. -/
theorem openDirectImageRestriction_app {V U : X.Opens} (h : V ≤ U) (W : X.Etaleᵒᵖ) :
    (openDirectImageRestriction X h).hom.app W =
      (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map (openPullbackMap X h W.unop).op :=
  rfl

/-- The restrictions `𝐆_a ⟶ ι_{U,*} 𝐆_{a,U}` are compatible with the transition maps. -/
theorem openDirectImageUnit_comp_restriction {V U : X.Opens} (h : V ≤ U) :
    openDirectImageUnit X U ≫ openDirectImageRestriction X h = openDirectImageUnit X V := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W => ?_)
  refine (NatTrans.comp_app _ _ _).trans ?_
  rw [openDirectImageUnit_app, openDirectImageRestriction_app, openDirectImageUnit_app]
  exact ((Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map_comp _ _).symm.trans
    (congrArg (fun z ↦ (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map z)
      ((op_comp ..).symm.trans (congrArg Quiver.Hom.op (openPullbackMap_fst X h W.unop))))

section Frobenius

variable {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)

/-- **The Frobenius commutes with pullback of functions.** -/
theorem Γ_map_comp_frobenius {Y Z : Scheme.{u}} (g : Y ⟶ Z) (hZ : (p : Γ(Z, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) :
    Scheme.Γ.map g.op ≫ CommRingCat.ofHom (frobeniusRingHom Γ(Y, ⊤) hp hY) =
      CommRingCat.ofHom (frobeniusRingHom Γ(Z, ⊤) hp hZ) ≫ Scheme.Γ.map g.op := by
  ext x
  exact (map_pow (Scheme.Γ.map g.op).hom x p).symm

/-- **The Frobenius of the presheaf `V ↦ ι_{V,*} 𝐆_{a,V}`**: the direct image of the Frobenius of
`𝐆_{a,V}` on each open `V`. -/
def openDirectImageFrobenius : openDirectImagePresheaf X ⟶ openDirectImagePresheaf X where
  app V := (etaleAbelianDirectImage.{u, 0} V.unop.ι).map
    (frobeniusMap.{u, 0} V.unop hp (natCast_eq_zero_of_hom V.unop.ι hX))
  naturality V V' h := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun W => ?_)
    change (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map
        (openPullbackMap X h.unop.le W.unop).op ≫
          additiveCoefficients.{u, 0}.map (CommRingCat.ofHom (frobeniusRingHom _ hp
            (natCast_eq_zero_of_hom (pullback.snd W.unop.hom V'.unop.ι ≫ V'.unop.ι) hX))) =
      additiveCoefficients.{u, 0}.map (CommRingCat.ofHom (frobeniusRingHom _ hp
          (natCast_eq_zero_of_hom (pullback.snd W.unop.hom V.unop.ι ≫ V.unop.ι) hX))) ≫
        (Scheme.Γ ⋙ additiveCoefficients.{u, 0}).map (openPullbackMap X h.unop.le W.unop).op
    exact (additiveCoefficients.{u, 0}.map_comp _ _).symm.trans
      ((congrArg additiveCoefficients.{u, 0}.map (Γ_map_comp_frobenius hp _ _ _)).trans
        (additiveCoefficients.{u, 0}.map_comp _ _))

/-- The restriction `𝐆_a ⟶ ι_{U,*} 𝐆_{a,U}` intertwines the Frobenii. -/
theorem openDirectImageUnit_comp_frobenius (U : X.Opens) :
    openDirectImageUnit X U ≫ (openDirectImageFrobenius X hp hX).app (op U) =
      frobeniusMap.{u, 0} X hp hX ≫ openDirectImageUnit X U := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W => ?_)
  exact (additiveCoefficients.{u, 0}.map_comp _ _).symm.trans
    ((congrArg additiveCoefficients.{u, 0}.map (Γ_map_comp_frobenius hp _ _ _)).trans
      (additiveCoefficients.{u, 0}.map_comp _ _))

end Frobenius

section Cech

variable {ι : Type} (U : ι → X.Opens)

/-- **The Čech complex of `𝐆_a` for the family of opens `U`**: in degree `n` the product over the
`(n + 1)`-tuples `x` of the direct images `ι_{U_x,*} 𝐆_{a,U_x}`. -/
abbrev zariskiCechComplex : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ :=
  (cechComplexFunctor U).obj (openDirectImagePresheaf X)

/-- The degree-`0` component of the augmentation of the Čech complex by `𝐆_a`. -/
def zariskiCechAugmentationZero : additiveSheaf.{u, 0} X ⟶ (zariskiCechComplex X U).X 0 :=
  openDirectImageUnit X (⊤_ X.Opens) ≫ aug U (openDirectImagePresheaf X) terminalIsTerminal

/-- The degree-`0` augmentation followed by the first Čech differential is zero. -/
theorem zariskiCechAugmentationZero_comp_d :
    zariskiCechAugmentationZero X U ≫ (zariskiCechComplex X U).d 0 1 = 0 :=
  (Category.assoc _ _ _).trans ((congrArg (openDirectImageUnit X (⊤_ X.Opens) ≫ ·)
    (aug_comp_d U (openDirectImagePresheaf X) terminalIsTerminal)).trans comp_zero)

/-- **The augmentation of the Čech complex by `𝐆_a`**, restricting a function on `W` to the
`W ×_X U_i`. -/
def zariskiCechAugmentation :
    (CochainComplex.single₀ _).obj (additiveSheaf.{u, 0} X) ⟶ zariskiCechComplex X U :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨zariskiCechAugmentationZero X U, zariskiCechAugmentationZero_comp_d X U⟩

/-- The degree-`0` component of `zariskiCechAugmentation` is `zariskiCechAugmentationZero`. -/
theorem zariskiCechAugmentation_f_zero :
    (zariskiCechAugmentation X U).f 0 = zariskiCechAugmentationZero X U :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

variable {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)

/-- **The Frobenius of the Čech complex of `𝐆_a`**, termwise. -/
abbrev zariskiCechFrobenius : zariskiCechComplex X U ⟶ zariskiCechComplex X U :=
  (cechComplexFunctor U).map (openDirectImageFrobenius X hp hX)

/-- **The augmentation intertwines the Frobenius of `𝐆_a` with that of the Čech complex.** -/
theorem zariskiCechAugmentationZero_comp_frobenius :
    zariskiCechAugmentationZero X U ≫ (zariskiCechFrobenius X U hp hX).f 0 =
      frobeniusMap.{u, 0} X hp hX ≫ zariskiCechAugmentationZero X U :=
  (Category.assoc _ _ _).trans ((congrArg (openDirectImageUnit X (⊤_ X.Opens) ≫ ·)
    (Stacks.AlgebraicGeometry.CoveringResolution.augmentation_naturality U
      (openDirectImageFrobenius X hp hX))).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ aug U (openDirectImagePresheaf X) terminalIsTerminal)
          (openDirectImageUnit_comp_frobenius X hp hX (⊤_ X.Opens))).trans
          (Category.assoc _ _ _))))

/-- As a map of complexes, the augmentation of the Čech complex by `𝐆_a` intertwines the Frobenius
of `𝐆_a` with the Frobenius `zariskiCechFrobenius` of the Čech complex. -/
theorem zariskiCechAugmentation_comp_frobenius :
    zariskiCechAugmentation X U ≫ zariskiCechFrobenius X U hp hX =
      (CochainComplex.single₀ _).map (frobeniusMap.{u, 0} X hp hX) ≫
        zariskiCechAugmentation X U := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, zariskiCechAugmentation_f_zero]
  exact zariskiCechAugmentationZero_comp_frobenius X U hp hX

end Cech

end Stacks.ArtinSchreier

end
