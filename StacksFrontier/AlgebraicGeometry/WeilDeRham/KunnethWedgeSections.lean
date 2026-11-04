module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethDeRhamWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxComparisonSections
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxRelativeTensorExtensionality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTargetFromStep

/-!
# The wedge product of pulled-back forms, on local sections

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y` with projections `p`,
`q`, and `f = p ≫ a`. The isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{W/S}` of
[Stacks, Tag 0FMA] is, on the summand `Ω^i_{X/S} ⊠ Ω^j_{Y/S}`, the wedge product of the pulled-back
forms. This file proves the corresponding identity on the source of the comparison
`p^{-1}Ω^i_{X/S} ⊗_{f^{-1}𝒪_S} q^{-1}Ω^j_{Y/S} ⟶ Ω^i_{X/S} ⊠ Ω^j_{Y/S}` of step (5) of
[Stacks, Tag 0G4A]: the comparison followed by the summand of Tag 0FMA is the tensor product of the
two canonical maps `p^{-1}Ω^i_{X/S} ⟶ Ω^i_{W/S}`, `q^{-1}Ω^j_{Y/S} ⟶ Ω^j_{W/S}` of
[Stacks, Tag 0FL5] followed by the wedge product of [Stacks, Tag 0FM2]. Both sides are evaluated on
pure tensors of pulled-back unit sections, which determine morphisms out of the tensor product.

## Main definitions

* `Stacks.WeilDeRham.pullbackFormsNatOfEq`: the canonical map `h^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` of
  `ℕ`-indexed de Rham complexes, along a morphism `h` of inverse-image ringed spaces equal to the
  one attached to a commutative square.

## Main results

* `Stacks.WeilDeRham.relativeBoxComparison_deRhamBoxWedgeHom`: **the comparison of step (5)
  followed by the summand of Tag 0FMA is the wedge product of the pulled-back forms.**

## References

* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open Stacks.Cohomology.BoxKunneth
open RingedSpaceModuleAdjunction AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open scoped TensorProduct Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.WeilDeRham

section OfEqNat

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The canonical map `h^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` of `ℕ`-indexed de Rham complexes, along a
morphism `h` of inverse-image ringed spaces equal to the one attached to the square. -/
def pullbackFormsNatOfEq (h : inverseImageBase f' ⟶ inverseImageBase f)
    (e : inverseImageBaseMap g' f' f g w = h) :
    ((_root_.pullback h).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Scheme.Hom.deRhamComplex f) ⟶ Scheme.Hom.deRhamComplex f' := by
  subst e
  exact deRhamPullbackChain g' f' f g w

/-- `pullbackFormsNatOfEq` on a pullback-unit section is the pullback of the differential form,
up to the identification of the opens `h⁻¹U` and `g'⁻¹U`. -/
theorem pullbackFormsNatOfEq_f_pullbackUnitSection (h : inverseImageBase f' ⟶ inverseImageBase f)
    (e : inverseImageBaseMap g' f' f g w = h) (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (s : ((Scheme.Hom.deRhamComplex f).X p).val.obj U) :
    HEq (((pullbackFormsNatOfEq g' f' f g w h e).f p).val.app ((opensMap h).op.obj U)
        (Stacks.PullbackUnitGenerators.pullbackUnitSection h
          ((Scheme.Hom.deRhamComplex f).X p) U s))
      (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) U.unop s) := by
  subst e
  exact heq_of_eq (SheafOfModules.GradedAlgebra.homEquiv_symm_val_app_unit
    (inverseImageBaseMap g' f' f g w) (formsPushforward g' f' f g w p) U s)

end OfEqNat

section Sections

/-- A morphism applied to a restricted section, given its value on the section. -/
theorem app_map_apply_of_eq {Z : RingedSpace.{u, u}} {M N : Modules Z} (g : M ⟶ N)
    {U V : (Opens Z.carrier)ᵒᵖ} (i : U ⟶ V) {m : M.val.obj U} {n : N.val.obj U}
    (h : (g.val.app U).hom m = n) :
    (g.val.app V).hom ((M.val.map i).hom m) = (N.val.map i).hom n :=
  (Stacks.BoxKunnethSections.app_map_apply g i m).trans (congrArg _ h)

/-- Restrictions of two heterogeneously equal sections over equal opens agree. -/
theorem map_apply_eq_of_heq {Z : RingedSpace.{u, u}} {N : Modules Z} {O₁ O₂ U : (Opens Z.carrier)ᵒᵖ}
    (e : O₁ = O₂) (i₁ : O₁ ⟶ U) (i₂ : O₂ ⟶ U) {n₁ : N.val.obj O₁} {n₂ : N.val.obj O₂}
    (h : HEq n₁ n₂) : (N.val.map i₁).hom n₁ = (N.val.map i₂).hom n₂ := by
  subst e
  cases eq_of_heq h
  rw [Subsingleton.elim i₁ i₂]

/-- A morphism out of a tensor product sheaf on equal pure tensors. -/
theorem tensorEvalMap_tmul_congr {Z : RingedSpace.{u, u}} {M N C : Modules Z}
    (u : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩).obj M).obj N ⟶ C)
    (U : (Opens Z.carrier)ᵒᵖ) {m m' : M.val.obj U} {n n' : N.val.obj U} (hm : m = m')
    (hn : n = n') :
    Stacks.PullbackUnitGenerators.tensorEvalMap u U (m ⊗ₜ[Z.presheaf.obj U] n) =
      Stacks.PullbackUnitGenerators.tensorEvalMap u U (m' ⊗ₜ[Z.presheaf.obj U] n') := by
  subst hm hn
  rfl

end Sections

section Summand

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The comparison map of `p`-forms along the first projection of `X ×_S Y` sends the pullback
unit section of a relative `p`-form `s` of `X / S` to its pullback
`Scheme.Hom.deRhamBoxLeftPullback a b p U s`. -/
theorem fstFormsNat_pullbackUnitSection (p : ℕ) (U : X.Opens)
    (s : ((Scheme.Hom.deRhamComplex a).X p).val.obj (op U)) :
    ((pullbackFormsNatOfEq (pullback.fst a b) (pullback.fst a b ≫ a) a (𝟙 S) (fst_comp_eq a b)
          (fstProjection a b)
          (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b))).f p).val.app
        ((opensMap (fstProjection a b)).op.obj (op U))
      (Stacks.PullbackUnitGenerators.pullbackUnitSection (fstProjection a b)
        ((Scheme.Hom.deRhamComplex a).X p) (op U) s) =
    Scheme.Hom.deRhamBoxLeftPullback a b (p : ℤ) U s :=
  eq_of_heq (pullbackFormsNatOfEq_f_pullbackUnitSection _ _ _ _ _ _ _ p (op U) s)

/-- The comparison map of `q`-forms along the second projection of `X ×_S Y` sends the pullback
unit section of a relative `q`-form `t` of `Y / S` to its pullback
`Scheme.Hom.deRhamBoxRightPullback a b q V t`, as a heterogeneous equality. -/
theorem sndFormsNat_pullbackUnitSection (q : ℕ) (V : Y.Opens)
    (t : ((Scheme.Hom.deRhamComplex b).X q).val.obj (op V)) :
    HEq (((pullbackFormsNatOfEq (pullback.snd a b) (pullback.fst a b ≫ a) b (𝟙 S)
          (snd_comp_eq a b) (sndProjection a b)
          (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b))).f q).val.app
        ((opensMap (sndProjection a b)).op.obj (op V))
      (Stacks.PullbackUnitGenerators.pullbackUnitSection (sndProjection a b)
        ((Scheme.Hom.deRhamComplex b).X q) (op V) t))
    (Scheme.Hom.deRhamBoxRightPullback a b (q : ℤ) V t) :=
  pullbackFormsNatOfEq_f_pullbackUnitSection _ _ _ _ _ _ _ q (op V) t


/-- **The wedge product of the pulled-back forms, on the pure tensor of the two pulled-back
unit sections.** -/
theorem formProduct_heq_tensorEvalMap_wedgeProduct (p q : ℕ) (W : (pullback a b).Opens)
    (V : X.Opens) (V' : Y.Opens) (s : ((Scheme.Hom.deRhamComplex a).X p).val.obj (op V))
    (t : ((Scheme.Hom.deRhamComplex b).X q).val.obj (op V'))
    (h₁ : W ≤ pullback.fst a b ⁻¹ᵁ V) (h₂ : W ≤ pullback.snd a b ⁻¹ᵁ V')
    (i' : (opensMap (sndProjection a b)).op.obj (op V') ⟶ op W) :
    HEq (AlgebraicGeometry.SheafOfModules.formProduct
        (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a)) p q (op W)
        (((Scheme.Hom.relativeDifferentialForms (pullback.fst a b ≫ a) (p : ℤ)).presheaf.map
          (homOfLE h₁).op).hom (Scheme.Hom.deRhamBoxLeftPullback a b (p : ℤ) V s))
        (((Scheme.Hom.relativeDifferentialForms (pullback.fst a b ≫ a) (q : ℤ)).presheaf.map
          (homOfLE h₂).op).hom (Scheme.Hom.deRhamBoxRightPullback a b (q : ℤ) V' t)))
      (Stacks.PullbackUnitGenerators.tensorEvalMap (Z := inverseImageBase (pullback.fst a b ≫ a))
        (M := (Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X p)
        (N := (Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X q)
        (C := (Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X (p + q))
        (HomologicalComplex.ιMapBifunctor
          (AlgebraicGeometry.SheafOfModules.deRhamComplex
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))
          (AlgebraicGeometry.SheafOfModules.deRhamComplex
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} _) (ComplexShape.up ℕ)
          p q (p + q) rfl ≫
        (AlgebraicGeometry.SheafOfModules.wedgeProduct
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential
              (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a)))).f (p + q)) (op W)
        ((((pullbackFormsNatOfEq (pullback.fst a b) (pullback.fst a b ≫ a) a (𝟙 S)
            (fst_comp_eq a b) (fstProjection a b)
            (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b))).f p).val.app
            (op W)).hom
          ((((modulePullback (fstProjection a b)).obj ((Scheme.Hom.deRhamComplex a).X p)).val.map
            (homOfLE h₁).op).hom
            (Stacks.PullbackUnitGenerators.pullbackUnitSection (fstProjection a b)
              ((Scheme.Hom.deRhamComplex a).X p) (op V) s)) ⊗ₜ
        (((pullbackFormsNatOfEq (pullback.snd a b) (pullback.fst a b ≫ a) b (𝟙 S)
            (snd_comp_eq a b) (sndProjection a b)
            (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b))).f q).val.app
            (op W)).hom
          ((((modulePullback (sndProjection a b)).obj ((Scheme.Hom.deRhamComplex b).X q)).val.map
            i').hom
            (Stacks.PullbackUnitGenerators.pullbackUnitSection (sndProjection a b)
              ((Scheme.Hom.deRhamComplex b).X q) (op V') t)))) := by
  have e₁ := app_map_apply_of_eq ((pullbackFormsNatOfEq (pullback.fst a b) (pullback.fst a b ≫ a) a
      (𝟙 S) (fst_comp_eq a b) (fstProjection a b)
      (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b))).f p) (homOfLE h₁).op
    (fstFormsNat_pullbackUnitSection a b p V s)
  have e₂ := (Stacks.BoxKunnethSections.app_map_apply ((pullbackFormsNatOfEq (pullback.snd a b)
      (pullback.fst a b ≫ a) b (𝟙 S) (snd_comp_eq a b) (sndProjection a b)
      (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b))).f q) i' _).trans
    (map_apply_eq_of_heq (congrArg op
      (Stacks.BoxKunnethSections.opensMap_relativeInverseImageProjectionOfFactors (pullback.snd a b)
        b (pullback.fst a b ≫ a) pullback.condition.symm V')) i' (homOfLE h₂).op
      (sndFormsNat_pullbackUnitSection a b q V' t))
  refine HEq.trans ?_ (heq_of_eq (tensorEvalMap_tmul_congr _ _ e₁ e₂).symm)
  exact (AlgebraicGeometry.SheafOfModules.wedgeProduct_summand_unit_apply _ _ p q (op W) _ _).symm

/-- For `p + q = m`, the relative box comparison followed by `Scheme.Hom.deRhamBoxWedgeHom`
equals the tensor product of the comparison maps of `p`-forms and `q`-forms along the two
projections, followed by the wedge product into `m`-forms of `X ×_S Y` over `S`. -/
theorem relativeBoxComparison_deRhamBoxWedgeHom (p q m : ℕ) (h : p + q = m) :
    relativeBoxComparison a b ((Scheme.Hom.deRhamDiffOpComplex a).X p)
        ((Scheme.Hom.deRhamDiffOpComplex b).X q) ≫
      (toInverseImageModules (pullback.fst a b ≫ a)).map
        (Scheme.Hom.deRhamBoxWedgeHom a b m p q h) =
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).map
        ((pullbackFormsNatOfEq (pullback.fst a b) (pullback.fst a b ≫ a) a (𝟙 S) (fst_comp_eq a b)
          (fstProjection a b)
          (inverseImageBaseMap_eq_fstProjection a b (fst_comp_eq a b))).f p)).app
        ((rightRelativeInverseImage a b).obj ((Scheme.Hom.deRhamDiffOpComplex b).X q)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          ((Scheme.Hom.deRhamComplex (pullback.fst a b ≫ a)).X p)).map
        ((pullbackFormsNatOfEq (pullback.snd a b) (pullback.fst a b ≫ a) b (𝟙 S) (snd_comp_eq a b)
          (sndProjection a b) (inverseImageBaseMap_eq_sndProjection a b (snd_comp_eq a b))).f q)) ≫
      (HomologicalComplex.ιMapBifunctor
        (AlgebraicGeometry.SheafOfModules.deRhamComplex
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.deRhamComplex
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} _) (ComplexShape.up ℕ)
        p q m h ≫
      (AlgebraicGeometry.SheafOfModules.wedgeProduct
          (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (Scheme.Hom.deRhamAlgebras (pullback.fst a b ≫ a)))).f m) := by
  subst h
  refine relativeInverseImageTensor_hom_ext a b _ _ (fun U x y hx hy => ?_)
  obtain ⟨V, i, s, rfl⟩ := hx
  obtain ⟨V', i', t, rfl⟩ := hy
  obtain ⟨W⟩ := U
  obtain ⟨V⟩ := V
  obtain ⟨V'⟩ := V'
  have h₁ : W ≤ pullback.fst a b ⁻¹ᵁ V := i.unop.le
  have h₂ : W ≤ pullback.snd a b ⁻¹ᵁ V' :=
    (Stacks.BoxKunnethSections.opensMap_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
      (pullback.fst a b ≫ a) pullback.condition.symm V') ▸ i'.unop.le
  have hi : ((homOfLE h₁).op : op (pullback.fst a b ⁻¹ᵁ V) ⟶ op W) = i := Subsingleton.elim _ _
  subst hi
  have hL₁ := relativeBoxComparison_tmul a b ((Scheme.Hom.deRhamDiffOpComplex a).X p)
    ((Scheme.Hom.deRhamDiffOpComplex b).X q) V s V' t W h₁ h₂ i' _ _ rfl
    rfl _ _ HEq.rfl HEq.rfl _ HEq.rfl
  have hL₂ := Scheme.Hom.deRhamBoxWedgeHom_externalTensorSection a b (p + q) p q rfl s t W h₁ h₂
  have hL := (Stacks.BoxKunnethSections.tensorEvalMap_comp_tmul _ _ W _ _).trans
    ((congrArg (fun z => (((toInverseImageModules (pullback.fst a b ≫ a)).map
      (Scheme.Hom.deRhamBoxWedgeHom a b (p + q) p q rfl)).val.app (op W)).hom z) hL₁).trans hL₂)
  refine hL.trans (Eq.trans ?_
    (Stacks.BoxKunnethSections.tensorEvalMap_tensorSheafMap_comp _ _ _ W _ _).symm)
  exact eq_of_heq ((Stacks.DeRhamSmooth.sheafOfModules_eqToHom_val_app_heq _ _ _).trans
    (formProduct_heq_tensorEvalMap_wedgeProduct a b p q W V V' s t h₁ h₂ i'))

end Summand

end Stacks.WeilDeRham
