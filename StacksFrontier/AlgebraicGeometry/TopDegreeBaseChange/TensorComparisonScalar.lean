module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPushforwardLinear
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonOpen

/-!
# Linearity of the tensor comparison of [Stacks, Tag 0EX3] (b) in the section of `G`

The canonical map of conclusion (b) of [Stacks, Tag 0EX3] is, by the sheafification adjunction of
[Stacks, Tag 01CB], a bilinear family on sections, and the field of that family which carries the
`𝒪`-linearity of a right derived functor is linearity in the section of the module on the base:
multiplying the section `s` of `G` by a function `r` on `U` must multiply the resulting section of
`R^n f_*(F ⊗ f^* G)` by `r`.

That is `Stacks.AlgebraicGeometry.SchemeHigherDirectImage`
`.rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ` applied to `f ∣_ U`, and this file carries
it out.  Both multiplications in that statement are `AlgebraicGeometry.baseScalar` *morphisms*, so
everything below is routed through composition of morphisms and not through a module action on a
`Hom`: the tensor identity `x ⊗ (r • t) = (r • x) ⊗ t` appears only in
`tensorSectionLinear_smul_section`, where it is the semilinearity of `TensorProduct.mk` and needs
no `TensorProduct.CompatibleSMul` instance.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openScalar` and `...preimageScalar`:
  multiplication by a function on `U`, on the modules over `U` and — through `f ∣_ U` — on the
  modules over `f⁻¹(U)`.  These are the two `AlgebraicGeometry.baseScalar` morphisms the linearity
  of the derived pushforward relates.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `tensorSectionLinear_smul_section`: **`x ⊗ (r • t) = (r • x) ⊗ t` on sections.**
* `tensorLocalSection_smul`: **tensoring with `r • t` is multiplication by `r` followed by
  tensoring with `t`**, for any morphism acting as multiplication by `r` on sections.
* `appTop_morphismRestrict_eq`: **`(f ∣_ U)^♯` is `f^♯` on `U`**, which is what identifies the
  function `preimageScalar` multiplies by with the pullback of the function `openScalar`
  multiplies by.
* `tensorLocalSection_unit_smul`: tensoring with the pullback of `r • s` is `preimageScalar r`
  followed by tensoring with the pullback of `s`.
* `higherDirectImageTensorSection_smul`: **the bilinear family is linear in the section of `G`**,
  as an identity of morphisms of sheaves.
* `tensorTopSection_smul`: the same read on sections, which is the `map_smul_right` field of the
  bilinear family.

## Implementation notes

`openScalar` and `preimageScalar` are both `AlgebraicGeometry.baseScalar` for the base ring
`Γ(U, ⊤)`; the second is for the structure morphism `(f ∣_ U) ≫ U.toSpecΓ`, which is the one
`rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ` consumes, so no two multiplication operators
have to be compared.

`appTop_morphismRestrict_eq` is proved from `AlgebraicGeometry.morphismRestrict_ι` rather than
from `AlgebraicGeometry.morphismRestrict_appTop`: rewriting with the latter leaves a goal whose
type mentions `(f ∣_ U) ⁻¹ᵁ ⊤` where `⊤` is expected — definitionally equal, but `rw` then cannot
build a motive, and reports a goal it plainly displays as not found.  Composing the two
`AlgebraicGeometry.Scheme.Hom.appLE`s of the commuting square keeps every open syntactically
fixed.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open SchemeHigherDirectImage (rightDerivedPlusRestrictObjIso baseRingToSections_toSpecΓ
  baseRingToSections_comp_toSpecΓ rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ)

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

/-! ### The pure tensor and a scalar -/

/-- **`x ⊗ (r • t) = (r • x) ⊗ t` on sections.**  Both sides are `r • (x ⊗ t)`, each by the
linearity of `TensorProduct.mk` in one of its two variables; no
`TensorProduct.CompatibleSMul` instance is involved, because the scalar is in the ring the tensor
product is formed over. -/
theorem tensorSectionLinear_smul_section {Z : Scheme.{u}} (A B : Z.Modules)
    (W : (Opens Z.carrier)ᵒᵖ) (c : Z.presheaf.obj W) (t : B.val.obj W) (x : A.val.obj W) :
    tensorSectionLinear Z A B W (c • t) x = tensorSectionLinear Z A B W t (c • x) := by
  show (toTensorSheafLinear Z A B W) (x ⊗ₜ[↑(Z.presheaf.obj W)] (c • t)) =
    (toTensorSheafLinear Z A B W) ((c • x) ⊗ₜ[↑(Z.presheaf.obj W)] t)
  refine congrArg (toTensorSheafLinear Z A B W) ?_
  refine Eq.trans
    (map_smul (TensorProduct.mk ↑(Z.presheaf.obj W) ↑(A.val.obj W) ↑(B.val.obj W) x) c t) ?_
  exact (map_smul
    ((TensorProduct.mk ↑(Z.presheaf.obj W) ↑(A.val.obj W) ↑(B.val.obj W)).flip t) c x).symm

/-- **Tensoring with `c • t` is multiplication by `c` followed by tensoring with `t`.**  The
multiplication is given as a morphism `μ` of modules over `V` together with its action on
sections, so that no scaling of a morphism occurs. -/
theorem tensorLocalSection_smul {Z : Scheme.{u}} (A B : Z.Modules) (V : Z.Opens)
    (c : Γ(Z, V)) (t : Γ(B, V))
    (μ : Scheme.Modules.restrict A V.ι ⟶ Scheme.Modules.restrict A V.ι)
    (hμ : ∀ (S : V.toScheme.Opens) (x : Γ(A, V.ι ''ᵁ S)),
      Scheme.Modules.Hom.app μ S x = Z.presheaf.map (homOfLE (V.ι_image_le S)).op c • x) :
    tensorLocalSection Z A B V (c • t) = μ ≫ tensorLocalSection Z A B V t := by
  refine Scheme.Modules.hom_ext _ _ fun S => ?_
  have key : ∀ x : Γ(A, V.ι ''ᵁ S),
      (tensorLocalSection Z A B V (c • t)).app S x =
        (tensorLocalSection Z A B V t).app S (μ.app S x) := fun x => by
    rw [← ModuleLimits.imageSections_rfl_app (tensorLocalSection Z A B V (c • t)) S x,
      imageSections_tensorLocalSection A B (c • t) rfl (V.ι_image_le S) x,
      Scheme.Modules.map_smul B (homOfLE (V.ι_image_le S)) c t, hμ S x,
      ← ModuleLimits.imageSections_rfl_app (tensorLocalSection Z A B V t) S _,
      imageSections_tensorLocalSection A B t rfl (V.ι_image_le S) _]
    exact tensorSectionLinear_smul_section A B (op (V.ι ''ᵁ S)) _ _ x
  ext x
  exact key x

/-! ### Multiplication by a function on an open, and its pullback -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- **Multiplication by a global function on `U`, on a module over `U`.**  This is
`AlgebraicGeometry.baseScalar` for the canonical structure morphism `U.toSpecΓ`. -/
abbrev openScalar (r : Γ(U.toScheme, ⊤)) (M : U.toScheme.Modules) : M ⟶ M :=
  (AlgebraicGeometry.baseScalar ↑Γ(U.toScheme, ⊤)
    (Over.mk U.toScheme.toSpecΓ :
      Over (Spec (CommRingCat.of ↑Γ(U.toScheme, ⊤)))) r).app M

/-- **Multiplication by the pullback of a global function on `U`, on a module over `f⁻¹(U)`.**
This is `AlgebraicGeometry.baseScalar` for the structure morphism `(f ∣_ U) ≫ U.toSpecΓ`, which
is the one the linearity of the derived pushforward relates to `openScalar`. -/
abbrev preimageScalar (r : Γ(U.toScheme, ⊤)) (M : (f ⁻¹ᵁ U).toScheme.Modules) : M ⟶ M :=
  (AlgebraicGeometry.baseScalar ↑Γ(U.toScheme, ⊤)
    (Over.mk ((f ∣_ U) ≫ U.toScheme.toSpecΓ) :
      Over (Spec (CommRingCat.of ↑Γ(U.toScheme, ⊤)))) r).app M

/-- **`(f ∣_ U)^♯` is `f^♯` on `U`.**  Read on global functions of `U` and conjugated by the two
restriction maps along `U.ι ''ᵁ ⊤ = U` and `(f⁻¹U).ι ''ᵁ ⊤ = f⁻¹U`.  Both sides are the
`AlgebraicGeometry.Scheme.Hom.appLE` of the two factorisations of the commuting square
`AlgebraicGeometry.morphismRestrict_ι`. -/
theorem appTop_morphismRestrict_comp :
    Y.presheaf.map (eqToHom U.ι_image_top).op ≫ Scheme.Hom.appTop (f ∣_ U) =
      f.app U ≫ X.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top).op := by
  simp only [Scheme.Hom.app_eq_appLE, morphismRestrict_appLE, Scheme.Hom.appLE_map]
  exact Scheme.Hom.map_appLE f _ _

/-- `appTop_morphismRestrict_comp` read on an element. -/
private theorem appTop_morphismRestrict_apply (r : Γ(Y, U)) :
    Scheme.Hom.appTop (f ∣_ U) (Y.presheaf.map (eqToHom U.ι_image_top).op r) =
      X.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top).op (f.app U r) :=
  ConcreteCategory.congr_hom (appTop_morphismRestrict_comp f U) r

/-- **`(f ∣_ U)^♯` is `f^♯` on `U`, read on an element.** -/
theorem appTop_morphismRestrict_eq (r : Γ(Y, U)) :
    X.presheaf.map (eqToHom (f ⁻¹ᵁ U).ι_image_top.symm).op
        (Scheme.Hom.appTop (f ∣_ U) (Y.presheaf.map (eqToHom U.ι_image_top).op r)) =
      f.app U r := by
  rw [appTop_morphismRestrict_apply]
  exact presheaf_map_eqToHom_cancel (f ⁻¹ᵁ U).ι_image_top (f.app U r)

/-! ### The two multiplication operators on sections -/

/-- **The action of `openScalar` on sections**: multiplication by the restriction of the
function. -/
theorem openScalar_app (r : Γ(Y, U)) (M : Y.Modules) (S : U.toScheme.Opens)
    (x : Γ(M, U.ι ''ᵁ S)) :
    Scheme.Modules.Hom.app
        (openScalar U (Y.presheaf.map (eqToHom U.ι_image_top).op r)
          (Scheme.Modules.restrict M U.ι)) S x =
      Y.presheaf.map (homOfLE (U.ι_image_le S)).op r • x := by
  have hc : (Scheme.Hom.appIso U.ι S).inv
        (AlgebraicGeometry.baseRingToSections ↑Γ(U.toScheme, ⊤)
          (Over.mk U.toScheme.toSpecΓ :
            Over (Spec (CommRingCat.of ↑Γ(U.toScheme, ⊤)))) (op S)
          (Y.presheaf.map (eqToHom U.ι_image_top).op r)) =
      Y.presheaf.map (homOfLE (U.ι_image_le S)).op r := by
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    refine Eq.trans (baseRingToSections_toSpecΓ U.toScheme (op S)
      (Y.presheaf.map (eqToHom U.ι_image_top).op r)) ?_
    exact presheaf_map_structure_comp (homOfLE (Scheme.Hom.image_mono U.ι le_top))
      (eqToHom U.ι_image_top) (homOfLE (U.ι_image_le S)) r
  refine Eq.trans ?_ (congrArg (fun c : ↑Γ(Y, U.ι ''ᵁ S) => c • x) hc)
  exact Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M S _ x

/-- **The action of `preimageScalar` on sections**: multiplication by the restriction of the
pullback `f^♯ r` of the function. -/
theorem preimageScalar_app (r : Γ(Y, U)) (M : X.Modules) (S : (f ⁻¹ᵁ U).toScheme.Opens)
    (x : Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ S)) :
    Scheme.Modules.Hom.app
        (preimageScalar f U (Y.presheaf.map (eqToHom U.ι_image_top).op r)
          (Scheme.Modules.restrict M (f ⁻¹ᵁ U).ι)) S x =
      X.presheaf.map (homOfLE ((f ⁻¹ᵁ U).ι_image_le S)).op (f.app U r) • x := by
  have hc : (Scheme.Hom.appIso (f ⁻¹ᵁ U).ι S).inv
        (AlgebraicGeometry.baseRingToSections ↑Γ(U.toScheme, ⊤)
          (Over.mk ((f ∣_ U) ≫ U.toScheme.toSpecΓ) :
            Over (Spec (CommRingCat.of ↑Γ(U.toScheme, ⊤)))) (op S)
          (Y.presheaf.map (eqToHom U.ι_image_top).op r)) =
      X.presheaf.map (homOfLE ((f ⁻¹ᵁ U).ι_image_le S)).op (f.app U r) := by
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    refine Eq.trans (baseRingToSections_comp_toSpecΓ (f ∣_ U) (op S)
      (Y.presheaf.map (eqToHom U.ι_image_top).op r)) ?_
    rw [appTop_morphismRestrict_apply]
    exact presheaf_map_structure_comp
      (homOfLE (Scheme.Hom.image_mono (f ⁻¹ᵁ U).ι le_top))
      (eqToHom (f ⁻¹ᵁ U).ι_image_top) (homOfLE ((f ⁻¹ᵁ U).ι_image_le S)) (f.app U r)
  refine Eq.trans ?_ (congrArg (fun c : ↑Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ S) => c • x) hc)
  exact Scheme.Modules.smul_restrictAppIso_hom_apply (f ⁻¹ᵁ U).ι M S _ x

/-! ### Linearity of the bilinear family in the section of `G` -/

variable (F : X.Modules) (G : Y.Modules) (n : ℕ)

/-- **Tensoring with the pullback of `r • s` is multiplication by `f^♯ r` followed by tensoring
with the pullback of `s`.** -/
theorem tensorLocalSection_unit_smul (r : Γ(Y, U)) (s : Γ(G, U)) :
    tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U (r • s)) =
      preimageScalar f U (Y.presheaf.map (eqToHom U.ι_image_top).op r)
          (Scheme.Modules.restrict F (f ⁻¹ᵁ U).ι) ≫
        tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app U s) := by
  refine Eq.trans (congrArg
    (tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U))
    (Scheme.Modules.Hom.app_smul
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) r s)) ?_
  exact tensorLocalSection_smul F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ U)
    (f.app U r) _ _ (preimageScalar_app f U r F)

/-- **The degree-`n` right derived pushforward along `f ∣_ U`, conjugated by the restriction
comparison of [Stacks, Tag 01E5], carries multiplication by `f^♯ r` to multiplication by `r`.**
The module `H` downstairs and the two local morphisms are variables, so that the statement
mentions no tensor product; this is the discipline of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.conjugateRestrict_add`.

The local morphisms are typed in the `_.restrict` spelling, the spelling of the type of
`tensorLocalSection`, so that at `H` the tensor product this statement elaborates to the same
term as `higherDirectImageTensorSection_eq`: the kernel then never compares the two spellings of
a restriction of the tensor product, which it does only by unfolding the tensor product. -/
theorem conjugateRestrict_scalar (H : X.Modules) (r : Γ(U.toScheme, ⊤))
    (τ τ' : Scheme.Modules.restrict F (f ⁻¹ᵁ U).ι ⟶ Scheme.Modules.restrict H (f ⁻¹ᵁ U).ι)
    (hτ : τ' = preimageScalar f U r (Scheme.Modules.restrict F (f ⁻¹ᵁ U).ι) ≫ τ) :
    (rightDerivedPlusRestrictObjIso f U n F).inv ≫
        ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).map τ' ≫
          (rightDerivedPlusRestrictObjIso f U n H).hom =
      openScalar U r ((Scheme.Modules.restrictFunctor U.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)) ≫
        ((rightDerivedPlusRestrictObjIso f U n F).inv ≫
          ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).map τ ≫
            (rightDerivedPlusRestrictObjIso f U n H).hom) := by
  have hlin : ((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).map
        (preimageScalar f U r ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F)) =
      openScalar U r (((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F)) :=
    rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ (f ∣_ U) n r _
  have hnat : (rightDerivedPlusRestrictObjIso f U n F).inv ≫
        openScalar U r (((Scheme.Modules.pushforward (f ∣_ U)).rightDerivedPlus (n : ℤ)).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F)) =
      openScalar U r ((Scheme.Modules.restrictFunctor U.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)) ≫
        (rightDerivedPlusRestrictObjIso f U n F).inv :=
    (AlgebraicGeometry.baseScalar ↑Γ(U.toScheme, ⊤)
      (Over.mk U.toScheme.toSpecΓ :
        Over (Spec (CommRingCat.of ↑Γ(U.toScheme, ⊤)))) r).naturality
      (rightDerivedPlusRestrictObjIso f U n F).inv
  rw [hτ, Functor.map_comp, hlin]
  simp only [Category.assoc]
  rw [reassoc_of% hnat]

/-- **The bilinear family of conclusion (b) of [Stacks, Tag 0EX3] is linear in the section of
`G`.** Tensoring with the pullback of `r • s`, taking the degree-`n` higher direct image and
transporting back along the restriction comparison of [Stacks, Tag 01E5] is multiplication by
`r` followed by the same for `s`.

This is an application: `conjugateRestrict_scalar` receives the `𝒪`-linearity of the right
derived functor and `tensorLocalSection_unit_smul` as proof terms. -/
theorem higherDirectImageTensorSection_smul (r : Γ(Y, U)) (s : Γ(G, U)) :
    higherDirectImageTensorSection f F G n U (r • s) =
      @CategoryStruct.comp _ _
        ((Scheme.Modules.restrictFunctor U.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))
        ((Scheme.Modules.restrictFunctor U.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))
        ((Scheme.Modules.restrictFunctor U.ι).obj
          (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
            (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
              X.toRingedSpace.IsSheaf⟩).obj F).obj ((Scheme.Modules.pullback f).obj G))))
        (openScalar U (Y.presheaf.map (eqToHom U.ι_image_top).op r)
          ((Scheme.Modules.restrictFunctor U.ι).obj
            (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)))
        (higherDirectImageTensorSection f F G n U s) := by
  rw [higherDirectImageTensorSection_eq f F G n U (r • s),
    higherDirectImageTensorSection_eq f F G n U s]
  exact conjugateRestrict_scalar f U F n _ _ _ _ (tensorLocalSection_unit_smul f U F G r s)

/-- **The reading at the top open of multiplication by a function is multiplication by that
function.** -/
theorem topReading_openScalar {M : Y.Modules} (r : Γ(Y, U)) (a : Γ(M, U)) :
    topReading U (openScalar U (Y.presheaf.map (eqToHom U.ι_image_top).op r)
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) a = r • a := by
  show M.presheaf.map (eqToHom U.ι_image_top.symm).op
      (Scheme.Modules.Hom.app
        (openScalar U (Y.presheaf.map (eqToHom U.ι_image_top).op r)
          (Scheme.Modules.restrict M U.ι)) ⊤
        (M.presheaf.map (eqToHom U.ι_image_top).op a)) = _
  rw [openScalar_app U r M ⊤ (M.presheaf.map (eqToHom U.ι_image_top).op a),
    Scheme.Modules.map_smul M (eqToHom U.ι_image_top.symm) _ _,
    presheaf_map_structure_comp (eqToHom U.ι_image_top.symm)
      (homOfLE (U.ι_image_le ⊤)) (𝟙 U) r,
    presheaf_map_ι_image_top_cancel U a, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The `map_smul_right` field of the bilinear family of conclusion (b) of [Stacks, Tag
0EX3]**: the candidate value on sections over `U` is linear in the section of `G`. -/
theorem tensorTopSection_smul (r : Γ(Y, U)) (s : Γ(G, U))
    (a : Γ(topDirectImage f F n, U)) :
    tensorTopSection f F G n U (r • s) a = r • tensorTopSection f F G n U s a := by
  rw [tensorTopSection, tensorTopSection, higherDirectImageTensorSection_smul f U F G n r s,
    topReading_comp, topReading_openScalar, topReading_smul]

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
