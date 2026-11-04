module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomA
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Pull and push for sheaves of differential graded modules, in all degrees

Let `f : (C, J, R) ⟶ (C', J', R')` be a morphism of ringed sites, let `A` and `A'` be sheaves of
differential graded algebras on the source and the target and let `φ : A' ⟶ f_*A` be a semilinear
homomorphism. For a pullback `f^*` of right differential graded `A'`-modules, the homogeneous
right-linear maps `P ⟶ f_*M` of degree `n` are the homogeneous right-linear maps `f^*P ⟶ M` of
degree `n`, for every `n`, by precomposition with the unit of the pullback.

## Main definitions

* `SheafOfModules.sitePushforwardBiprodIso`: the direct image of a binary biproduct of sheaves of
  modules is the biproduct of the direct images.
* `SheafOfModules.DifferentialGradedModule.isoOfDegreewiseIso`: a morphism of right differential
  graded modules which is an isomorphism in every degree is an isomorphism.
* `SheafOfModules.DifferentialGradedModule.shiftForget`: the underlying graded module of a right
  differential graded module, shifted.
* `SheafOfModules.DifferentialGradedModule.shiftCochain`: the homogeneous cochain attached to a
  graded morphism into such a shift.
* `SheafOfModules.DifferentialGradedModule.pushforwardCofreeIso`: the direct image of the cofree
  differential graded module on `M[n]` is the cofree differential graded module on `(f_*M)[n]`.

## Main results

* `SheafOfModules.DifferentialGradedModule.homogeneousMapEquivShift` and
  `homogeneousMapEquivCofree`: the degree-`n` homogeneous right-linear maps `Q ⟶ M` are the
  graded homomorphisms `Q ⟶ M[n]`, equivalently the morphisms of right differential graded
  modules from `Q` into the cofree module on `M[n]`.
* `SheafOfModules.DifferentialGradedModule.PullbackData.homogeneousMapEquiv`,
  `homogeneousMapEquiv_val` and `delta_homogeneousMapEquiv`: the identification of the
  differential graded Hom objects in every degree, that it is precomposition with the unit of the
  pullback, and its compatibility with the differentials of the two Hom complexes.
* `SheafOfModules.DifferentialGradedModule.PullbackData.toGradedPullbackData`: a pullback in the
  sense of degree-zero morphisms is a pullback in all degrees.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u a' v' u' z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

/-- The first coordinate of a section of a biproduct written through the two inclusions. -/
theorem biprodFst_inl_add_inr {Z W : SheafOfModules.{m} R} (U : Cᵒᵖ) (x : Z.val.obj U)
    (y : W.val.obj U) :
    biprodFst Z W U (biprodInl Z W U x + biprodInr Z W U y) = x := by
  rw [map_add, biprodFst_inl, biprodFst_inr, add_zero]

/-- The second coordinate of a section of a biproduct written through the two inclusions. -/
theorem biprodSnd_inl_add_inr {Z W : SheafOfModules.{m} R} (U : Cᵒᵖ) (x : Z.val.obj U)
    (y : W.val.obj U) :
    biprodSnd Z W U (biprodInl Z W U x + biprodInr Z W U y) = y := by
  rw [map_add, biprodSnd_inl, biprodSnd_inr, zero_add]

section Pushforward

variable (w : C' ⥤ C) [w.IsContinuous J' J] (σ : R'.obj ⟶ w.op ⋙ R.obj)

/-- The comparison of the direct image of a binary biproduct with the biproduct of the direct
images. -/
noncomputable def sitePushforwardBiprodHom (Z W : SheafOfModules.{m} R) :
    (sitePushforward w σ).obj (Z ⊞ W) ⟶
      (sitePushforward w σ).obj Z ⊞ (sitePushforward w σ).obj W :=
  biprod.lift ((sitePushforward w σ).map biprod.fst) ((sitePushforward w σ).map biprod.snd)

/-- The inverse comparison, out of the biproduct of the direct images. -/
noncomputable def sitePushforwardBiprodInv (Z W : SheafOfModules.{m} R) :
    (sitePushforward w σ).obj Z ⊞ (sitePushforward w σ).obj W ⟶
      (sitePushforward w σ).obj (Z ⊞ W) :=
  biprod.desc ((sitePushforward w σ).map biprod.inl) ((sitePushforward w σ).map biprod.inr)

variable {Z W : SheafOfModules.{m} R}

/-- The first coordinate of the biproduct comparison of a section of the direct image of `Z ⊞ W`
is its first coordinate in `Z ⊞ W`. -/
@[simp] theorem biprodFst_sitePushforwardBiprodHom (V : C'ᵒᵖ)
    (ξ : ((sitePushforward w σ).obj (Z ⊞ W)).val.obj V) :
    biprodFst _ _ V (homSections (sitePushforwardBiprodHom w σ Z W) V ξ) =
      biprodFst Z W (w.op.obj V) ξ := by
  rw [← homSections_comp]
  exact homSections_congr (biprod.lift_fst _ _) V ξ

/-- The second coordinate of the biproduct comparison of a section of the direct image of `Z ⊞ W`
is its second coordinate in `Z ⊞ W`. -/
@[simp] theorem biprodSnd_sitePushforwardBiprodHom (V : C'ᵒᵖ)
    (ξ : ((sitePushforward w σ).obj (Z ⊞ W)).val.obj V) :
    biprodSnd _ _ V (homSections (sitePushforwardBiprodHom w σ Z W) V ξ) =
      biprodSnd Z W (w.op.obj V) ξ := by
  rw [← homSections_comp]
  exact homSections_congr (biprod.lift_snd _ _) V ξ

/-- The inverse biproduct comparison sends a section to the sum of the inclusions of its two
coordinates. -/
theorem homSections_sitePushforwardBiprodInv (V : C'ᵒᵖ)
    (ξ : ((sitePushforward w σ).obj Z ⊞ (sitePushforward w σ).obj W).val.obj V) :
    homSections (sitePushforwardBiprodInv w σ Z W) V ξ =
      biprodInl Z W (w.op.obj V) (biprodFst _ _ V ξ) +
        biprodInr Z W (w.op.obj V) (biprodSnd _ _ V ξ) :=
  homSections_desc _ _ V ξ

/-- The direct image of a binary biproduct of sheaves of modules is the biproduct of the direct
images. -/
noncomputable def sitePushforwardBiprodIso (Z W : SheafOfModules.{m} R) :
    (sitePushforward w σ).obj (Z ⊞ W) ≅
      (sitePushforward w σ).obj Z ⊞ (sitePushforward w σ).obj W where
  hom := sitePushforwardBiprodHom w σ Z W
  inv := sitePushforwardBiprodInv w σ Z W
  hom_inv_id := by
    ext V ξ
    change homSections (sitePushforwardBiprodHom w σ Z W ≫ sitePushforwardBiprodInv w σ Z W) V ξ
      = homSections (𝟙 _) V ξ
    rw [homSections_comp, homSections_sitePushforwardBiprodInv,
      biprodFst_sitePushforwardBiprodHom, biprodSnd_sitePushforwardBiprodHom, homSections_id]
    exact biprodSections_total Z W (w.op.obj V) ξ
  inv_hom_id := by
    ext V ξ
    change homSections (sitePushforwardBiprodInv w σ Z W ≫ sitePushforwardBiprodHom w σ Z W) V ξ
      = homSections (𝟙 _) V ξ
    rw [homSections_comp, homSections_id]
    refine biprodSections_ext _ _ V ?_ ?_
    · rw [biprodFst_sitePushforwardBiprodHom, homSections_sitePushforwardBiprodInv]
      exact biprodFst_inl_add_inr _ _ _
    · rw [biprodSnd_sitePushforwardBiprodHom, homSections_sitePushforwardBiprodInv]
      exact biprodSnd_inl_add_inr _ _ _

/-- The forward map of `sitePushforwardBiprodIso` is `sitePushforwardBiprodHom`. -/
@[simp] theorem sitePushforwardBiprodIso_hom (Z W : SheafOfModules.{m} R) :
    (sitePushforwardBiprodIso w σ Z W).hom = sitePushforwardBiprodHom w σ Z W :=
  rfl

end Pushforward

namespace DifferentialGradedModule

open CochainComplex.HomComplex

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- A morphism of right differential graded modules which is an isomorphism in every degree is an
isomorphism of right differential graded modules. -/
noncomputable def isoOfDegreewiseIso {K L : DifferentialGradedModule.{t, a, m} A} (h : K ⟶ L)
    (hiso : ∀ p : ℤ, IsIso (h.toHomologicalComplex.f p)) : K ≅ L where
  hom := h
  inv :=
    { toHomologicalComplex :=
        { f := fun p => inv (h.toHomologicalComplex.f p)
          comm' := fun p q hpq => by
            rw [IsIso.inv_comp_eq, ← Category.assoc, h.toHomologicalComplex.comm' p q hpq,
              Category.assoc, IsIso.hom_inv_id, Category.comp_id] }
      map_mul := fun p i U x b => by
        change homSections (inv (h.toHomologicalComplex.f (p + i))) U ((L.mul p i).app U x b)
          = (K.mul p i).app U (homSections (inv (h.toHomologicalComplex.f p)) U x) b
        have hinv : ∀ (r : ℤ) (y : (L.complex.X r).val.obj U),
            homSections (h.toHomologicalComplex.f r) U
              (homSections (inv (h.toHomologicalComplex.f r)) U y) = y := fun r y => by
          rw [← homSections_comp, homSections_congr (IsIso.inv_hom_id _) U y, homSections_id]
        have hcancel : ∀ (r : ℤ) (y : (K.complex.X r).val.obj U),
            homSections (inv (h.toHomologicalComplex.f r)) U
              (homSections (h.toHomologicalComplex.f r) U y) = y := fun r y => by
          rw [← homSections_comp, homSections_congr (IsIso.hom_inv_id _) U y, homSections_id]
        have hmul : ∀ y : (K.complex.X p).val.obj U,
            homSections (h.toHomologicalComplex.f (p + i)) U ((K.mul p i).app U y b)
              = (L.mul p i).app U (homSections (h.toHomologicalComplex.f p) U y) b :=
          fun y => h.map_mul p i U y b
        have key := hmul (homSections (inv (h.toHomologicalComplex.f p)) U x)
        rw [hinv p x] at key
        exact (congrArg (fun z => homSections (inv (h.toHomologicalComplex.f (p + i))) U z)
          key.symm).trans (hcancel _ _) }
  hom_inv_id := Hom.ext fun p => by simp
  inv_hom_id := Hom.ext fun p => by simp

/-- The forward map of `isoOfDegreewiseIso h hiso` is `h`. -/
@[simp] theorem isoOfDegreewiseIso_hom {K L : DifferentialGradedModule.{t, a, m} A} (h : K ⟶ L)
    (hiso : ∀ p : ℤ, IsIso (h.toHomologicalComplex.f p)) :
    (isoOfDegreewiseIso h hiso).hom = h :=
  rfl

/-- Postcomposition with an isomorphism of right differential graded modules is a bijection on
morphisms. -/
def postcompEquiv {Z Z' : DifferentialGradedModule.{t, a, m} A} (e : Z ≅ Z')
    (P : DifferentialGradedModule.{t, a, m} A) : (P ⟶ Z) ≃ (P ⟶ Z') where
  toFun k := k ≫ e.hom
  invFun k := k ≫ e.inv
  left_inv k := by simp
  right_inv k := by simp

/-- `postcompEquiv e P` sends `k` to `k ≫ e.hom`. -/
@[simp] theorem postcompEquiv_apply {Z Z' : DifferentialGradedModule.{t, a, m} A} (e : Z ≅ Z')
    (P : DifferentialGradedModule.{t, a, m} A) (k : P ⟶ Z) : postcompEquiv e P k = k ≫ e.hom :=
  rfl

section Homogeneous

open CochainComplex.HomComplex AlgebraicGeometry

variable {Y : RingedSite.{z, z, z}}
  {B : DifferentialGradedAlgebra.{z, a} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

/-- The underlying graded module of a right differential graded module, shifted by `n`. -/
noncomputable abbrev shiftForget (M : DifferentialGradedModule.{z, a, m} B) (n : ℤ) :
    GradedModule.{z, a, m} B.toGradedAlgebra :=
  ((forgetToGradedModule B).obj M).shift n

/-- The degree-`n` cochain attached to a homomorphism of graded modules into the shift `M[n]`. -/
noncomputable def shiftCochain (Q M : DifferentialGradedModule.{z, a, m} B) (n : ℤ)
    (g : (forgetToGradedModule B).obj Q ⟶ ((forgetToGradedModule B).obj M).shift n) :
    Cochain Q.complex M.complex n :=
  Cochain.mk fun p _q h =>
    (g.app p : Q.complex.X p ⟶ M.complex.X (p + n)) ≫ degCastHom M.complex.X h

/-- The component of `shiftCochain Q M n g` from degree `p` to degree `q` is the component of `g`
in degree `p`, followed by the identification of degree `p + n` with degree `q`. -/
@[simp] theorem shiftCochain_v_app {Q M : DifferentialGradedModule.{z, a, m} B} {n : ℤ}
    (g : (forgetToGradedModule B).obj Q ⟶ ((forgetToGradedModule B).obj M).shift n)
    (p q : ℤ) (h : p + n = q) (V : Y.Cᵒᵖ) (x : (Q.complex.X p).val.obj V) :
    ((shiftCochain Q M n g).v p q h).val.app V x =
      castHom M.complex.X h V ((g.app p).val.app V x) := by
  subst h
  rfl

/-- A homogeneous cochain evaluated in two spellings of the same target degree. -/
theorem cochain_v_heq
    {K L : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    {n : ℤ}
    (z : Cochain K L n) (p q q' : ℤ) (h : p + n = q) (h' : p + n = q') (V : Y.Cᵒᵖ)
    (x : (K.X p).val.obj V) :
    HEq ((z.v p q h).val.app V x) ((z.v p q' h').val.app V x) := by
  obtain rfl : q = q' := h.symm.trans h'
  rfl

/-- Pull and push for the underlying graded categories: a homogeneous right-linear map of degree
`n` from `Q` to `M` is a homomorphism of graded modules from `Q` to the shift `M[n]`. -/
noncomputable def homogeneousMapEquivShift
    (B : DifferentialGradedAlgebra.{z, a} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (Q M : DifferentialGradedModule.{z, a, m} B) (n : ℤ) :
    HomogeneousMap B Q M n ≃
      ((forgetToGradedModule B).obj Q ⟶ ((forgetToGradedModule B).obj M).shift n) where
  toFun w :=
    { app := fun p => w.val.v p (p + n) rfl
      map_smul := fun p i V x y => by
        refine eq_of_heq ((cochain_v_heq w.val (p + i) (p + i + n) (p + n + i)
          rfl (by omega) V _).trans ?_)
        exact (w.2 p (p + n) i rfl V x y).trans
          (heq_castHom M.complex.X (show p + n + i = p + i + n by omega) V _).symm }
  invFun g :=
    ⟨shiftCochain Q M n g, by
      intro p q i hpq V x b
      obtain rfl : p + n = q := hpq
      have key : (g.app (p + i)).val.app V ((Q.mul p i).app V x b)
          = castHom M.complex.X (show p + n + i = p + i + n by omega) V
              ((M.mul (p + n) i).app V ((g.app p).val.app V x) b) :=
        g.map_smul p i V x b
      refine heq_of_eq ?_
      rw [shiftCochain_v_app, shiftCochain_v_app, key, Cofree.castHom_castHom]
      rfl⟩
  left_inv w := by
    refine Subtype.ext (Cochain.ext _ _ fun p q hpq => ?_)
    obtain rfl : p + n = q := hpq
    ext V x
    rw [shiftCochain_v_app]
    rfl
  right_inv g := by
    refine GradedModule.Hom.ext fun p => ?_
    ext V x
    exact shiftCochain_v_app g p (p + n) rfl V x

/-- The degree-`p` component of the graded homomorphism attached to `w` is the component of `w`
from degree `p` to degree `p + n`. -/
@[simp] theorem homogeneousMapEquivShift_apply_app
    (B : DifferentialGradedAlgebra.{z, a} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (Q M : DifferentialGradedModule.{z, a, m} B) (n : ℤ) (w : HomogeneousMap B Q M n) (p : ℤ) :
    (homogeneousMapEquivShift B Q M n w).app p = w.val.v p (p + n) rfl :=
  rfl

/-- The cochain underlying the homogeneous map attached to a graded homomorphism `g` into `M[n]`
is `shiftCochain Q M n g`. -/
@[simp] theorem homogeneousMapEquivShift_symm_val
    (B : DifferentialGradedAlgebra.{z, a} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (Q M : DifferentialGradedModule.{z, a, m} B) (n : ℤ)
    (g : (forgetToGradedModule B).obj Q ⟶ ((forgetToGradedModule B).obj M).shift n) :
    ((homogeneousMapEquivShift B Q M n).symm g).val = shiftCochain Q M n g :=
  rfl

/-- A homogeneous right-linear map of degree `n` from `Q` to `M` is a morphism of right
differential graded modules from `Q` into the cofree module on the shift `M[n]`. -/
noncomputable def homogeneousMapEquivCofree
    (B : DifferentialGradedAlgebra.{z, a} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (Q M : DifferentialGradedModule.{z, a, m} B) (n : ℤ) :
    HomogeneousMap B Q M n ≃ (Q ⟶ Cofree.cofree (shiftForget M n)) :=
  (homogeneousMapEquivShift B Q M n).trans (Cofree.homEquiv Q (shiftForget M n))


section PushPull

open CochainComplex.HomComplex AlgebraicGeometry

variable {X X' : RingedSite.{z, z, z}} {u : X'.C ⥤ X.C} [u.IsContinuous X'.J X.J]
  {σ : (Stacks.SheafOfModules.Tensor.ringSheaf X'.O).obj ⟶
    u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
  {A : DifferentialGradedAlgebra.{z, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {A' : DifferentialGradedAlgebra.{z, a'} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}

variable (φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A)
  (M : DifferentialGradedModule.{z, a, m} A) (n : ℤ)

/-- The first coordinate of the biproduct comparison on the cofree module. -/
@[simp] theorem coordFst_sitePushforwardBiprodHom_cofree (p : ℤ) (V : X'.Cᵒᵖ)
    (ξ : ((pushforwardObj φ (Cofree.cofree (shiftForget M n))).complex.X p).val.obj V) :
    Cofree.coordFst (shiftForget (pushforwardObj φ M) n) p V
        (homSections (sitePushforwardBiprodHom u σ
          ((shiftForget M n).piece p) ((shiftForget M n).piece (p + 1))) V ξ)
      = Cofree.coordFst (shiftForget M n) p (u.op.obj V) ξ :=
  biprodFst_sitePushforwardBiprodHom u σ V ξ

/-- The second coordinate of the biproduct comparison on the cofree module. -/
@[simp] theorem coordSnd_sitePushforwardBiprodHom_cofree (p : ℤ) (V : X'.Cᵒᵖ)
    (ξ : ((pushforwardObj φ (Cofree.cofree (shiftForget M n))).complex.X p).val.obj V) :
    Cofree.coordSnd (shiftForget (pushforwardObj φ M) n) p V
        (homSections (sitePushforwardBiprodHom u σ
          ((shiftForget M n).piece p) ((shiftForget M n).piece (p + 1))) V ξ)
      = Cofree.coordSnd (shiftForget M n) p (u.op.obj V) ξ :=
  biprodSnd_sitePushforwardBiprodHom u σ V ξ

/-- The shifted action on the direct image is the shifted action of `M` through `φ`. -/
theorem shiftForget_pushforward_smul (p i : ℤ) (V : X'.Cᵒᵖ)
    (y : ((shiftForget (pushforwardObj φ M) n).piece p).val.obj V)
    (b : (A'.complex.X i).val.obj V) :
    (shiftForget (pushforwardObj φ M) n).smul p i V y b
      = (shiftForget M n).smul p i (u.op.obj V) y (φ.app i V b) :=
  ((GradedModule.shift_smul ((forgetToGradedModule A').obj (pushforwardObj φ M)) n p i V y b).trans
      (eq_of_heq ((heq_castHom _ _ _ _).trans (heq_castHom _ _ _ _).symm))).trans
    (GradedModule.shift_smul ((forgetToGradedModule A).obj M) n p i (u.op.obj V) y
      (φ.app i V b)).symm

/-- The comparison of the direct image of the cofree module on `M[n]` with the cofree module on
`(f_*M)[n]`: degreewise the biproduct comparison of the direct image. -/
noncomputable def pushforwardCofreeHom :
    pushforwardObj φ (Cofree.cofree (shiftForget M n)) ⟶
      Cofree.cofree (shiftForget (pushforwardObj φ M) n) where
  toHomologicalComplex :=
    { f := fun p => (sitePushforwardBiprodIso u σ
        ((shiftForget M n).piece p) ((shiftForget M n).piece (p + 1))).hom
      comm' := fun p q hpq => by
        obtain rfl : p + 1 = q := hpq
        rw [show (Cofree.cofree (shiftForget (pushforwardObj φ M) n)).complex.d p (p + 1)
              = Cofree.d (shiftForget (pushforwardObj φ M) n) p from CochainComplex.of_d _ _ p,
          show (pushforwardObj φ (Cofree.cofree (shiftForget M n))).complex.d p (p + 1)
              = (sitePushforward u σ).map (Cofree.d (shiftForget M n) p) from
            congrArg (fun g => (sitePushforward u σ).map g) (CochainComplex.of_d _ _ p)]
        ext V ξ
        change homSections (Cofree.d (shiftForget (pushforwardObj φ M) n) p) V
            (homSections (sitePushforwardBiprodIso u σ _ _).hom V ξ)
          = homSections (sitePushforwardBiprodIso u σ _ _).hom V
            (homSections (Cofree.d (shiftForget M n) p) (u.op.obj V) ξ)
        refine Cofree.sections_ext _ V ?_ ?_
        · exact (Cofree.coordFst_d _ p V _).trans
            ((biprodSnd_sitePushforwardBiprodHom u σ V ξ).trans
              ((Cofree.coordFst_d (shiftForget M n) p (u.op.obj V) ξ).symm.trans
                (biprodFst_sitePushforwardBiprodHom u σ V _).symm))
        · exact (Cofree.coordSnd_d _ p V _).trans
            ((biprodSnd_sitePushforwardBiprodHom u σ V _).trans
              (Cofree.coordSnd_d (shiftForget M n) p (u.op.obj V) ξ)).symm }

  map_mul := fun p i V ξ b => by
    change homSections (sitePushforwardBiprodHom u σ
          ((shiftForget M n).piece (p + i)) ((shiftForget M n).piece (p + i + 1))) V
        (Cofree.mulHom (shiftForget M n) p i (u.op.obj V) (φ.app i V b) ξ)
      = Cofree.mulHom (shiftForget (pushforwardObj φ M) n) p i V b
          (homSections (sitePushforwardBiprodHom u σ
            ((shiftForget M n).piece p) ((shiftForget M n).piece (p + 1))) V ξ)
    have hd : Cofree.algD i (u.op.obj V) (φ.app i V b)
        = φ.app (i + 1) V (Cofree.algD (A := A') i V b) := (φ.comm_d i V b).symm
    refine Cofree.sections_ext (shiftForget (pushforwardObj φ M) n) V ?_ ?_
    · refine Eq.trans ((biprodFst_sitePushforwardBiprodHom u σ V _).trans
        (Cofree.coordFst_mulHom (shiftForget M n) p i (u.op.obj V) (φ.app i V b) ξ)) ?_
      refine Eq.trans ?_ ((Cofree.coordFst_mulHom (shiftForget (pushforwardObj φ M) n) p i V b
        (homSections (sitePushforwardBiprodHom u σ
          ((shiftForget M n).piece p) ((shiftForget M n).piece (p + 1))) V ξ)).trans
        (congrArg (fun y => (shiftForget (pushforwardObj φ M) n).smul p i V y b)
          (biprodFst_sitePushforwardBiprodHom u σ V ξ))).symm
      exact (shiftForget_pushforward_smul φ M n p i V _ b).symm
    · refine Eq.trans ((biprodSnd_sitePushforwardBiprodHom u σ V _).trans
        (Cofree.coordSnd_mulHom (shiftForget M n) p i (u.op.obj V) (φ.app i V b) ξ)) ?_
      refine Eq.trans ?_ ((Cofree.coordSnd_mulHom (shiftForget (pushforwardObj φ M) n) p i V b
        (homSections (sitePushforwardBiprodHom u σ
          ((shiftForget M n).piece p) ((shiftForget M n).piece (p + 1))) V ξ)).trans
        (congrArg₂ (· + ·)
          (congrArg (fun y => castHom (shiftForget (pushforwardObj φ M) n).piece
              (add_right_comm p 1 i) V
            ((shiftForget (pushforwardObj φ M) n).smul (p + 1) i V y b))
            (biprodSnd_sitePushforwardBiprodHom u σ V ξ))
          (congrArg (fun y => (Int.negOnePow p : ℤ) •
              castHom (shiftForget (pushforwardObj φ M) n).piece (add_assoc p i 1).symm V
            ((shiftForget (pushforwardObj φ M) n).smul p (i + 1) V y
              (Cofree.algD i V b)))
            (biprodFst_sitePushforwardBiprodHom u σ V ξ)))).symm
      refine congrArg₂ (· + ·) ?_ (congrArg (fun y => (Int.negOnePow p : ℤ) • y) ?_)
      · exact eq_of_heq ((heq_castHom _ _ _ _).trans
          ((heq_of_eq (shiftForget_pushforward_smul φ M n (p + 1) i V _ b).symm).trans
            (heq_castHom _ _ _ _).symm))
      · refine eq_of_heq ((heq_castHom _ _ _ _).trans
          ((heq_of_eq ?_).trans (heq_castHom _ _ _ _).symm))
        refine Eq.trans (congrArg (fun c => (shiftForget M n).smul p (i + 1) (u.op.obj V)
          (Cofree.coordFst (shiftForget M n) p (u.op.obj V) ξ) c) hd) ?_
        exact (shiftForget_pushforward_smul φ M n p (i + 1) V _ (Cofree.algD i V b)).symm

/-- In degree `p`, `pushforwardCofreeHom φ M n` is the biproduct comparison of the direct
image. -/
@[simp] theorem pushforwardCofreeHom_f (p : ℤ) :
    (pushforwardCofreeHom φ M n).toHomologicalComplex.f p =
      (sitePushforwardBiprodIso u σ
        ((shiftForget M n).piece p) ((shiftForget M n).piece (p + 1))).hom :=
  rfl

/-- The direct image of the cofree differential graded module on `M[n]` is the cofree
differential graded module on `(f_*M)[n]`. -/
noncomputable def pushforwardCofreeIso :
    pushforwardObj φ (Cofree.cofree (shiftForget M n)) ≅
      Cofree.cofree (shiftForget (pushforwardObj φ M) n) :=
  isoOfDegreewiseIso (pushforwardCofreeHom φ M n) fun p => by
    rw [pushforwardCofreeHom_f]
    exact Iso.isIso_hom _


namespace PullbackData

/-- Pull and push for sheaves of differential graded modules: for every degree `n`, the
homogeneous right-linear maps of degree `n` from `f^*P` to `M` are the homogeneous right-linear
maps of degree `n` from `P` to `f_*M`. -/
noncomputable def homogeneousMapEquiv (PD : PullbackData φ)
    (P : DifferentialGradedModule.{z, a', m} A') :
    HomogeneousMap A (PD.obj P) M n ≃ HomogeneousMap A' P (pushforwardObj φ M) n :=
  (homogeneousMapEquivCofree A (PD.obj P) M n).trans
    (((PD.isPullback P).homEquiv (Cofree.cofree (shiftForget M n))).trans
      ((semilinearHomEquiv φ P (Cofree.cofree (shiftForget M n))).trans
        ((postcompEquiv (pushforwardCofreeIso φ M n) P).trans
          ((Cofree.homEquiv P (shiftForget (pushforwardObj φ M) n)).symm.trans
            (homogeneousMapEquivShift A' P (pushforwardObj φ M) n).symm))))

/-- The identification of the differential graded Hom objects in every degree is precomposition
with the unit of the pullback. -/
theorem homogeneousMapEquiv_val (PD : PullbackData φ)
    (P : DifferentialGradedModule.{z, a', m} A') (w : HomogeneousMap A (PD.obj P) M n) :
    (homogeneousMapEquiv φ M n PD P w).val = precompCochain (PD.unit P) w.val := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain rfl : p + n = q := hpq
  ext V x
  rw [precompCochain_v_app]
  refine Eq.trans (shiftCochain_v_app _ p (p + n) rfl V x) ?_
  exact (coordFst_sitePushforwardBiprodHom_cofree φ M n p V _).trans
    (Cofree.coordFst_lift (shiftForget M n) p _ _ (u.op.obj V) ((PD.unit P).app p V x))

/-- The identification of the differential graded Hom objects is compatible with the
differentials of the two Hom complexes. -/
theorem delta_homogeneousMapEquiv (PD : PullbackData φ)
    (P : DifferentialGradedModule.{z, a', m} A') (w : HomogeneousMap A (PD.obj P) M n) :
    δ n (n + 1) ((homogeneousMapEquiv φ M n PD P w).val)
      = precompCochain (PD.unit P) (δ n (n + 1) w.val) := by
  rw [homogeneousMapEquiv_val]
  exact (precompCochain_delta (PD.unit P) rfl w.val).symm

/-- A pullback of right differential graded modules in the sense of degree-zero morphisms is a
pullback in all degrees. -/
noncomputable def toGradedPullbackData (PD : PullbackData φ) : GradedPullbackData φ where
  obj P := PD.obj P
  unit P := PD.unit P
  homEquiv P M' n' := homogeneousMapEquiv φ M' n' PD P
  homEquiv_val P M' n' w := homogeneousMapEquiv_val φ M' n' PD P w

end PullbackData

end PushPull

end Homogeneous


end DifferentialGradedModule

end SheafOfModules

end
