module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTargetFromStep
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationExteriorStep
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The step summand's source read in the target complex, then into `Ω^n_{X/S}/F^{k+1}`

For `f : X ⟶ Y` over `S`, a cut `k` and `n = k + 1 + j`, the morphism
`Stacks.DeRhamSmooth.stepSummandToGradedTarget` (`E_j`) reads
`f^{-1}Ω^k_{Y/S} ⊗_{(f∘g)^{-1}𝒪_S} Ω^{j+1}_{X/S}` in the degree-`n` term of the target complex of
Section 0FMK. Read further into the quotient `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}` through
`Stacks.DeRhamSmooth.gradedTargetXToStepQuotient`, it is the `(k, j + 1)` summand of the wedge map
followed by the projection.

The triangle of [Stacks, Tag 08DE] on the pulled-back forms
(`Stacks.DeRhamSmooth.pulledBackFormsToTarget_tensor_comp_mixedTensor`) states that `θ ⊗ 1`
followed by the change of rings to `f^{-1}𝒪_Y` and the identification
`Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso` is the comparison
`f^{-1}Ω^k_{Y/S} ⟶ f^*Ω^k_{Y/S}` tensored with `1`, followed by the change of rings to `𝒪_X`.

## Main results

* `Stacks.DeRhamSmooth.pulledBackFormsToTarget_tensor_comp_mixedTensor`: the triangle of
  [Stacks, Tag 08DE].
* `Stacks.DeRhamSmooth.stepSummandToGradedTarget_comp_toStepQuotient` (`(★_j)`): `E_j` read
  into `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}` is the `(k, j + 1)` summand of the wedge map followed by the
  projection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.DeRhamDirectImage
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap)
open scoped TensorProduct

universe u

namespace Stacks.CategoryTheory

/-- A composite of four morphisms of sheaves of modules on a local section, with the one-step
evaluations supplied as hypotheses. -/
theorem sheafOfModules_comp4_val_app_apply_of {C : Type*} [_root_.CategoryTheory.Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {A B C' D E : _root_.SheafOfModules.{u} R} (a : A ⟶ B) (k : B ⟶ C') (l : C' ⟶ D) (m : D ⟶ E)
    (V : Cᵒᵖ) (s : A.val.obj V)
    {b : B.val.obj V} (hb : (a.val.app V).hom s = b)
    {c : C'.val.obj V} (hc : (k.val.app V).hom b = c)
    {d : D.val.obj V} (hd : (l.val.app V).hom c = d) :
    ((a ≫ k ≫ l ≫ m).val.app V).hom s = (m.val.app V).hom d := by
  subst hb hc hd
  rfl

/-- A composite of two morphisms of sheaves of modules on a local section, with the one-step
evaluations supplied as hypotheses. -/
theorem sheafOfModules_comp2_val_app_apply_of {C : Type*} [_root_.CategoryTheory.Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {A B C' : _root_.SheafOfModules.{u} R} (a : A ⟶ B) (k : B ⟶ C')
    (V : Cᵒᵖ) (s : A.val.obj V)
    {b : B.val.obj V} (hb : (a.val.app V).hom s = b)
    {c : C'.val.obj V} (hc : (k.val.app V).hom b = c) :
    ((a ≫ k).val.app V).hom s = c := by
  subst hb hc
  rfl

end Stacks.CategoryTheory

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The left-hand side of `Stacks.DeRhamSmooth.pulledBackFormsToTarget_tensor_comp_mixedTensor`
on a pure tensor, up to its last factor: `x ⊗ a ↦ θ(x) ⊗ a`, the last two of the four steps
being the triangle of restrictions of scalars on `a` and the lax comparison. -/
theorem mixedTensor_lhs_val_app_tensorSheafUnit (k : ℕ) (F : Modules X.toRingedSpace)
    (U : (Opens X.carrier)ᵒᵖ) (x : ((pulledBackDeRhamComplex f g).X k).val.obj U)
    (ω : ((pushforward (toInverseImageBase (f ≫ g))).obj F).val.obj U) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map (pulledBackFormsToTarget f g k)).app
        ((pushforward (toInverseImageBase (f ≫ g))).obj F) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).obj ((coefficientRestriction f g).obj (pulledBackTargetForms f g
          k))).map
        ((coefficientRestrictionToInverseImageBaseIso f g).inv.app F) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
          g.toLRSHom.toShHom) (pulledBackTargetForms f g k) ((pushforward (toInverseImageBase
          f)).obj F) ≫
      (gradedSourceMixedTensorCoefficientIso f g k F).hom).val.app U).hom
        ((PresheafOfModules.tensorSheafUnit (Osharp := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫
            g).base).obj S.sheaf)) ((pulledBackDeRhamComplex f g).X k)
          ((pushforward (toInverseImageBase (f ≫ g))).obj F)).app U (x ⊗ₜ[((TopCat.Sheaf.pullback
              CommRingCat.{u} (f ≫ g).base).obj S.sheaf).obj.obj U] ω))) =
      ((gradedSourceMixedTensorCoefficientIso f g k F).hom.val.app U).hom
        ((PresheafOfModules.tensorSheafUnit (Osharp := (inverseImageBase f).sheaf)
            (pulledBackTargetForms f g k)
          ((pushforward (toInverseImageBase f)).obj F)).app U
            (((pulledBackFormsToTarget f g k).val.app U).hom x ⊗ₜ[(inverseImageBase f).sheaf.obj.obj
                U]
              (((coefficientRestrictionToInverseImageBaseIso f g).inv.app F).val.app
                  U).hom ω)) := by
  have L1 := AlgebraicGeometry.SheafOfModules.tensorFunctor_map_unit_apply (X := X.toRingedSpace)
    (A := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)) (pulledBackFormsToTarget f g k) U x ω
  have L2 := AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_map_unit_apply
    (X := X.toRingedSpace) (A := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf))
    ((coefficientRestrictionToInverseImageBaseIso f g).inv.app F) U
    (((pulledBackFormsToTarget f g k).val.app U).hom x) ω
  have L3 := AlgebraicGeometry.SheafOfModules.laxComparison_val_app_tensorSheafUnit
    (X := inverseImageBase f) (A := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)) (φ := (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom))
    (pulledBackTargetForms f g k) ((pushforward (toInverseImageBase f)).obj F) U
    (((pulledBackFormsToTarget f g k).val.app U).hom x)
    ((((coefficientRestrictionToInverseImageBaseIso f g).inv.app F).val.app U).hom ω)
  exact Stacks.CategoryTheory.sheafOfModules_comp4_val_app_apply_of _ _ _ _ U _ L1 L2 L3

/-- The right-hand side of `Stacks.DeRhamSmooth.pulledBackFormsToTarget_tensor_comp_mixedTensor`
on a pure tensor: `x ⊗ a ↦ c(x) ⊗ a`. -/
theorem mixedTensor_rhs_val_app_tensorSheafUnit (k : ℕ) (F : Modules X.toRingedSpace)
    (U : (Opens X.carrier)ᵒᵖ) (x : ((pulledBackDeRhamComplex f g).X k).val.obj U)
    (ω : ((pushforward (toInverseImageBase (f ≫ g))).obj F).val.obj U) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app
        ((pushforward (toInverseImageBase (f ≫ g))).obj F) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) F).val.app U).hom
        ((PresheafOfModules.tensorSheafUnit (Osharp := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫
            g).base).obj S.sheaf)) ((pulledBackDeRhamComplex f g).X k)
          ((pushforward (toInverseImageBase (f ≫ g))).obj F)).app U (x ⊗ₜ[((TopCat.Sheaf.pullback
              CommRingCat.{u} (f ≫ g).base).obj S.sheaf).obj.obj U] ω))) =
      (PresheafOfModules.tensorSheafUnit (Osharp := X.sheaf) ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) F).app U
        (((relativeInverseImageToPullback f g
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k :
              ℤ))).val.app U).hom x ⊗ₜ[X.sheaf.obj.obj U]
            ω) := by
  have R1 := AlgebraicGeometry.SheafOfModules.tensorFunctor_map_unit_apply (X := X.toRingedSpace)
    (A := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)) (relativeInverseImageToPullback f g
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) U x ω
  have R2 := AlgebraicGeometry.SheafOfModules.laxComparison_val_app_tensorSheafUnit
    (X := X.toRingedSpace) (A := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)) (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
    ((Scheme.Modules.pullback f).obj
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) F U
    (((relativeInverseImageToPullback f g
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))).val.app U).hom x) ω
  exact Stacks.CategoryTheory.sheafOfModules_comp2_val_app_apply_of _ _ U _ R1 R2

/-- **`Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso` on a pure tensor**:
`y ⊗ a ↦ c(y) ⊗ a`, up to the heterogeneous equality the change of base requires. -/
theorem gradedSourceMixedTensorCoefficientIso_hom_val_app_tensorSheafUnit (k : ℕ)
    (F : Modules X.toRingedSpace) (U : (Opens X.carrier)ᵒᵖ)
    (y : (pulledBackTargetForms f g k).val.obj U)
    (a : ((pushforward (toInverseImageBase f)).obj F).val.obj U) :
    HEq (((gradedSourceMixedTensorCoefficientIso f g k F).hom.val.app U).hom
        ((PresheafOfModules.tensorSheafUnit (Osharp := (inverseImageBase f).sheaf)
          (pulledBackTargetForms f g k) ((pushforward (toInverseImageBase f)).obj F)).app U
            (y ⊗ₜ[(inverseImageBase f).sheaf.obj.obj U] a)))
      ((PresheafOfModules.tensorSheafUnit (Osharp := X.sheaf) ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) F).app U
        (((targetFormsToPullback f g k).val.app U).hom y ⊗ₜ[X.sheaf.obj.obj U] a)) := by
  have h₁ := coefficientRestrictionToInverseImageBaseIso_hom_app_val_app_heq f g
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
      ((Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)), F)) U
    (((gradedSourceMixedTensorIso f g k F).hom.val.app U).hom
      ((PresheafOfModules.tensorSheafUnit (Osharp := (inverseImageBase f).sheaf)
          (pulledBackTargetForms f g k) ((pushforward (toInverseImageBase f)).obj F)).app U
            (y ⊗ₜ[(inverseImageBase f).sheaf.obj.obj U] a)))
  exact h₁.trans (heq_of_eq (gradedSourceMixedTensorIso_hom_val_app_toSheafifyVal f g k F U y a))

/-- **The triangle of [Stacks, Tag 08DE] on the pulled-back forms of the target.** For a sheaf
`F` of `𝒪_X`-modules, the composite

`f^{-1}Ω^k_{Y/S} ⊗_A F| ⟶ (f^{-1}Ω^k_{Y/S})| ⊗_A F| ⟶ (f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} F|)|
  ≅ (f^*Ω^k_{Y/S} ⊗_{𝒪_X} F)|`

(`θ ⊗ 1`, the triangle of restrictions of scalars on `F`, the lax comparison along
`A = (f∘g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`, and `Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso`)
is `c ⊗ 1` for `c : f^{-1}Ω^k_{Y/S} ⟶ f^*Ω^k_{Y/S}` the comparison
`Stacks.DeRhamDirectImage.relativeInverseImageToPullback`, followed by the lax comparison along
`A ⟶ 𝒪_X`. -/
theorem pulledBackFormsToTarget_tensor_comp_mixedTensor (k : ℕ) (F : Modules X.toRingedSpace) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map (pulledBackFormsToTarget f g k)).app
        ((pushforward (toInverseImageBase (f ≫ g))).obj F) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).obj ((coefficientRestriction f g).obj (pulledBackTargetForms f g
          k))).map
        ((coefficientRestrictionToInverseImageBaseIso f g).inv.app F) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom
          g.toLRSHom.toShHom) (pulledBackTargetForms f g k) ((pushforward (toInverseImageBase
          f)).obj F) ≫
      (gradedSourceMixedTensorCoefficientIso f g k F).hom =
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app
        ((pushforward (toInverseImageBase (f ≫ g))).obj F) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((Scheme.Modules.pullback f).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) F := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := ((TopCat.Sheaf.pullback CommRingCat.{u} (f
      ≫ g).base).obj S.sheaf)) fun U x ω => ?_
  refine (mixedTensor_lhs_val_app_tensorSheafUnit f g k F U x ω).trans ?_
  refine Eq.trans ?_ (mixedTensor_rhs_val_app_tensorSheafUnit f g k F U x ω).symm
  refine eq_of_heq ((gradedSourceMixedTensorCoefficientIso_hom_val_app_tensorSheafUnit
    f g k F U _ _).trans ?_)
  have hθ : HEq (((targetFormsToPullback f g k).val.app U).hom
      (((pulledBackFormsToTarget f g k).val.app U).hom x))
      (((relativeInverseImageToPullback f g
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))).val.app U).hom x) :=
    (coefficientRestrictionToInverseImageBaseIso_hom_app_val_app_heq f g _ U _).symm.trans
      (heq_of_eq (congrArg (fun t => (t.val.app U).hom x)
        (pulledBackFormsToTarget_comp_targetFormsToPullback f g k)))
  rw [eq_of_heq hθ,
    eq_of_heq (coefficientRestrictionToInverseImageBaseIso_inv_app_val_app_heq f g F U ω)]
  exact HEq.rfl

end Stacks.DeRhamSmooth

namespace Stacks.CategoryTheory

/-- A morphism followed by a functor applied to an identity is the morphism. -/
theorem comp_map_id_eq {D E : Type*} [_root_.CategoryTheory.Category D]
    [_root_.CategoryTheory.Category E] (F : D ⥤ E) {Z : E} {N : D} (u : Z ⟶ F.obj N) :
    u ≫ F.map (𝟙 N) = u := by
  simp

/-- A morphism followed by a composite of two functors applied to an identity is the morphism. -/
theorem comp_map_map_id_eq {C D E : Type*} [_root_.CategoryTheory.Category C]
    [_root_.CategoryTheory.Category D] [_root_.CategoryTheory.Category E] (F : D ⥤ E)
    (G : C ⥤ D) {Z : E} {N : C} (u : Z ⟶ F.obj (G.obj N)) :
    u ≫ F.map (G.map (𝟙 N)) = u := by
  simp

end Stacks.CategoryTheory

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}

/-- **The lax comparison along `A ⟶ 𝒪_X` is natural in the first variable.** -/
theorem laxComparison_naturality_left
    {M M' : _root_.SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf)}
    (N : _root_.SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf)) (a : M ⟶ M') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).map
        ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).map a)).app
        ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj N) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison A X.sheaf φ M' N =
    Stacks.SheafOfModules.TensorRestrictScalars.laxComparison A X.sheaf φ M N ≫
      (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map a).app N) := by
  have h := Stacks.SheafOfModules.TensorRestrictScalars.laxComparison_naturality A X.sheaf φ a (𝟙 N)
  simp only [Functor.uncurry_obj_map] at h
  refine Eq.trans ?_ (h.trans ?_)
  · exact congrArg (· ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison A X.sheaf φ M' N)
      (Stacks.CategoryTheory.comp_map_map_id_eq _ _ _).symm
  · exact congrArg (fun t => Stacks.SheafOfModules.TensorRestrictScalars.laxComparison A X.sheaf φ M
      N ≫
      (Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf A X.sheaf φ).map t)
      (Stacks.CategoryTheory.comp_map_id_eq _ _)

end AlgebraicGeometry.SheafOfModules

namespace Stacks.CategoryTheory

/-- **The comparison read into the quotient, precomposed with `1 ⊗ φ`, at generic objects**: a
naturality square of `F.map e`, a defining equation `hG` for `G` after `1 ⊗ φ`, and a transport
`hT` give `(1 ⊗ φ) ≫ (e ⊗ 1) ≫ G = (e ⊗ 1) ≫ P' ≫ π`. -/
theorem tensor_map_comp_app_comp_of_eq {C : Type*} [_root_.CategoryTheory.Category C]
    (F : C ⥤ C ⥤ C) {M M' N N' N'' W W' Q : C} (φ : N ⟶ N') (e : M ⟶ M')
    (G : (F.obj M').obj N' ⟶ Q) (t : N ⟶ N'') (P : (F.obj M').obj N'' ⟶ W') (ε : W' ⟶ W)
    (π : W ⟶ Q) (P' : (F.obj M').obj N ⟶ W)
    (hG : (F.obj M').map φ ≫ G = (F.obj M').map t ≫ P ≫ ε ≫ π)
    (hT : (F.obj M').map t ≫ P ≫ ε = P') :
    (F.obj M).map φ ≫ (F.map e).app N' ≫ G = (F.map e).app N ≫ P' ≫ π := by
  rw [NatTrans.naturality_assoc, hG, ← hT]
  simp only [Category.assoc]

end Stacks.CategoryTheory

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F H : _root_.SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

/-- **The wedge product commutes with the transport of the degree of its second factor**: for
`q = q'`, transporting `⋀^{q'}H` to `⋀^qH`, wedging, and transporting the total degree is the
wedge product in degree `(k, q')` with its total degree transported. -/
theorem tensorObj_map_eqToHom_comp_prodWedgeHom_comp_eqToHom (iF : F ⟶ H) (k q q' n : ℕ)
    (hq : q = q') (h : k + q' = n) (e₁ : A.exteriorPower q' = A.exteriorPower q)
    (e₂ : A.exteriorPower (k + q) = A.exteriorPower n) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (AF.exteriorPower k)).map
          (eqToHom e₁) ≫ prodWedgeHom AF A A iF (𝟙 H) k q ≫ eqToHom e₂ =
      prodWedgeHomOfEq AF A A iF (𝟙 H) k q' n h := by
  subst hq h
  refine Eq.trans (congrArg (· ≫ prodWedgeHom AF A A iF (𝟙 H) k q ≫ eqToHom e₂)
    ((congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
      (AF.exteriorPower k)).map) (show eqToHom e₁ = 𝟙 _ from rfl)).trans
      (CategoryTheory.Functor.map_id _ _))) ?_
  exact Category.id_comp _

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The comparison of [Stacks, Section 0FMK] read into `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`, on the
forms of `X` over `S`**: for `n = k + 1 + m`, precomposed with
`1 ⊗ q : f^*Ω^k_{Y/S} ⊗ Ω^{m+1}_{X/S} ⟶ f^*Ω^k_{Y/S} ⊗ Ω^{m+1}_{X/Y}` it is the comparison of
[Stacks, Tag 01CI] tensored with `1`, the `(k, m + 1)` wedge product into `Ω^n_{X/S}` and the
projection. -/
theorem tensor_map_deRhamFormsToRelativeHom_comp_pullbackGradedQuotientHom [Smooth f] (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
        ((Scheme.Modules.pullback f).obj (relativeDifferentialForms g (k : ℤ)))).map
        ((deRhamFormsToRelativeHom f g).app ((m + 1 : ℕ) : ℤ)) ≫
      relativeDifferentialsPullbackGradedQuotientHom f g k m =
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
        (Stacks.DeRhamSmooth.pulledBackFormsIso f g k).hom).app
        (relativeDifferentialForms (f ≫ g) ((m + 1 : ℕ) : ℤ)) ≫
      _root_.SheafOfModules.prodWedgeHomOfEq
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₁)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₂)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₂)
        (relativeDifferentialsShortComplex f g).f (𝟙 _) k (m + 1) (k + 1 + m) (by omega) ≫
      cokernel.π (_root_.SheafOfModules.prodWedgeHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₁)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₂)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₂)
        (relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) m) := by
  have hS := shortExact_relativeDifferentialsShortComplex f g
    (Stacks.Smooth.formallySmoothScheme_of_smooth f)
  have hG := _root_.SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace (relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f
        g).X₃) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₂) hS.exact hS.epi_g k m
  have hT := _root_.SheafOfModules.tensorObj_map_eqToHom_comp_prodWedgeHom_comp_eqToHom
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace (relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f
        g).X₂) (relativeDifferentialsShortComplex f g).f k (1 + m) (m + 1) (k + 1 + m)
    (by omega) (by omega) (_root_.SheafOfModules.exteriorPiece_one_add_eq
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₂) m).symm
    (congrArg (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₂).exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m :
        ℤ)).symm)
  have h := Stacks.CategoryTheory.tensor_map_comp_app_comp_of_eq
    (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)
    ((deRhamFormsToRelativeHom f g).app ((m + 1 : ℕ) : ℤ))
    (Stacks.DeRhamSmooth.pulledBackFormsIso f g k).hom
    (relativeDifferentialsExteriorGradedQuotientHom f g k m) _ _ _ _ _ hG hT
  exact (congrArg _ (relativeDifferentialsPullbackGradedQuotientHom_eq f g k m)).trans h

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.CategoryTheory

/-- **A composite through an isomorphism and its inverse, with one square and one triangle
supplied**, at generic objects. -/
theorem comp_inv_comp_hom_comp_of_square {C : Type*} [_root_.CategoryTheory.Category C]
    {P₀ P₁ P₂ P₃ T T' Q₁ Q₂ Q₃ M : C} (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (a₃ : P₂ ⟶ P₃)
    (a₄ : P₃ ⟶ T') (i : T ≅ T') (b : T' ⟶ Q₁) (c : Q₁ ⟶ Q₂)
    (b' : P₃ ⟶ Q₃) (r : Q₃ ⟶ Q₁) (L : P₀ ⟶ M) (R : M ⟶ Q₃)
    (hn : a₄ ≫ b = b' ≫ r) (ht : a₁ ≫ a₂ ≫ a₃ ≫ b' = L ≫ R) :
    (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ i.inv) ≫ i.hom ≫ b ≫ c = L ≫ R ≫ r ≫ c := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn, reassoc_of% ht]

end Stacks.CategoryTheory

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **`E_j` read into `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`**: for `n = k + 1 + j`,

`E_j ≫ M_j = (c ⊗ 1) ≫ lax_{A → 𝒪_X} ≫ (1 ⊗ q ≫ the comparison of Section 0FMK read into the
quotient)|_A`,

`c : f^{-1}Ω^k_{Y/S} ⟶ f^*Ω^k_{Y/S}` the comparison and `q : Ω^{j+1}_{X/S} ⟶ Ω^{j+1}_{X/Y}`. -/
theorem stepSummandToGradedTarget_comp_toStepQuotient_eq [Smooth f] (k j : ℕ) :
    stepSummandToGradedTarget f g k j ≫ gradedTargetXToStepQuotient f g k j =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app
          ((pushforward (toInverseImageBase (f ≫ g))).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
        Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
            CommRingCat.{u} (f ≫
            g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
          ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)) ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
            ((Scheme.Modules.pullback f).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map
            ((AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom f g).app ((j + 1 : ℕ) : ℤ))) ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom f g k
              j) := by
  have hn := gradedSourceMixedTensorCoefficientIso_naturality f g k
      ((AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom f g).app ((j + 1 : ℕ) : ℤ))
  have ht := pulledBackFormsToTarget_tensor_comp_mixedTensor f g k
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))
  have h := Stacks.CategoryTheory.comp_inv_comp_hom_comp_of_square
    (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)))
    _ _ _ _ (gradedTargetXIso f g k (j + 1) (k + 1 + j) (by omega))
    ((gradedSourceMixedTensorCoefficientIso f g k
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j + 1 : ℕ) : ℤ))).hom)
    ((pushforward (toInverseImageBase (f ≫ g))).map
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom f g k j))
    _ _ _ _ hn ht
  exact h

/-- `Stacks.DeRhamSmooth.stepSummandToGradedTarget_comp_toStepQuotient_eq` with the restriction of
scalars along `(f∘g)^{-1}𝒪_S ⟶ 𝒪_X` spelled as `SheafOfModules.restrictScalars`. -/
theorem stepSummandToGradedTarget_comp_toStepQuotient_eq' [Smooth f] (k j : ℕ) :
    stepSummandToGradedTarget f g k j ≫ gradedTargetXToStepQuotient f g k j =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app
          ((pushforward (toInverseImageBase (f ≫ g))).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
        Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
            CommRingCat.{u} (f ≫
            g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
          ((Scheme.Modules.pullback f).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)) ≫
        (_root_.SheafOfModules.restrictScalars.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
            AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
            ((Scheme.Modules.pullback f).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).map
            ((AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom f g).app ((j + 1 : ℕ) : ℤ))) ≫
        (_root_.SheafOfModules.restrictScalars.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
            AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom f g k j) :=
  stepSummandToGradedTarget_comp_toStepQuotient_eq f g k j

end Stacks.DeRhamSmooth

namespace Stacks.CategoryTheory

/-- From a reduction `h₁` of `lhs`, a factorization `h₂` of `R.map u ≫ R.map v`, a factorization
`h₃` of `c` and a commutative square `h₄`, `lhs = (c ≫ b' ≫ R.map w) ≫ R.map π`. -/
theorem eq_of_reduction_of_factorization {C D : Type*} [_root_.CategoryTheory.Category C]
    [_root_.CategoryTheory.Category D] (R : D ⥤ C) {P₀ P₁ P₂' : C} {Q₁ Q₂ Q₃ Q₄ Q₅ : D}
    (lhs : P₀ ⟶ R.obj Q₅) (a : P₀ ⟶ P₁) (b : P₁ ⟶ R.obj Q₁) (u : Q₁ ⟶ Q₂) (v : Q₂ ⟶ Q₅)
    (c : P₀ ⟶ P₂') (y : P₁ ⟶ P₂') (b' : P₂' ⟶ R.obj Q₃) (e : Q₁ ⟶ Q₃) (w : Q₃ ⟶ Q₄)
    (π : Q₄ ⟶ Q₅)
    (h₁ : lhs = a ≫ b ≫ R.map u ≫ R.map v)
    (h₂ : R.map u ≫ R.map v = R.map e ≫ R.map w ≫ R.map π)
    (h₃ : c = a ≫ y) (h₄ : y ≫ b' = b ≫ R.map e) :
    lhs = (c ≫ b' ≫ R.map w) ≫ R.map π := by
  rw [h₁, h₃, h₂]
  simp only [Category.assoc, reassoc_of% h₄]

end Stacks.CategoryTheory

namespace Stacks.CategoryTheory

/-- **A functor carries a factorization of a composite of two morphisms to a factorization of
the composite of their images**: `u ≫ v = e ≫ w ≫ π` gives
`R.map u ≫ R.map v = R.map e ≫ R.map w ≫ R.map π`. -/
theorem functor_map_comp_map_eq_of_comp_eq {C D : Type*} [_root_.CategoryTheory.Category C]
    [_root_.CategoryTheory.Category D] (R : D ⥤ C) {Q₁ Q₂ Q₃ Q₄ Q₅ : D}
    (u : Q₁ ⟶ Q₂) (v : Q₂ ⟶ Q₅) (e : Q₁ ⟶ Q₃) (w : Q₃ ⟶ Q₄) (π : Q₄ ⟶ Q₅)
    (h : u ≫ v = e ≫ w ≫ π) : R.map u ≫ R.map v = R.map e ≫ R.map w ≫ R.map π := by
  rw [← R.map_comp, h, R.map_comp, R.map_comp]

/-- An equation of morphisms out of `Q₁`, precomposed with `a ≫ b`. -/
theorem comp_comp_eq_comp_comp_of_eq {C : Type*} [_root_.CategoryTheory.Category C]
    {P₀ P₁ Q₁ Q : C} (a : P₀ ⟶ P₁) (b : P₁ ⟶ Q₁) {u u' : Q₁ ⟶ Q} (h : u = u') :
    a ≫ b ≫ u = a ≫ b ≫ u' := by
  rw [h]

/-- A commutative square `y ≫ b' = b ≫ e`, precomposed with `a` and followed by `x`. -/
theorem comp_comp_comp_eq_of_square {C : Type*} [_root_.CategoryTheory.Category C]
    {P₀ P₁ P₂ Q₁ Q₃ Q : C} (a : P₀ ⟶ P₁) (b : P₁ ⟶ Q₁) (e : Q₁ ⟶ Q₃) (y : P₁ ⟶ P₂)
    (b' : P₂ ⟶ Q₃) (x : Q₃ ⟶ Q) (h : y ≫ b' = b ≫ e) : a ≫ b ≫ e ≫ x = a ≫ y ≫ b' ≫ x := by
  rw [reassoc_of% h]

/-- A factorization `c = a ≫ y`, followed by `z`. -/
theorem comp_comp_eq_of_eq_comp_left {C : Type*} [_root_.CategoryTheory.Category C]
    {P₀ P₁ P₂ Q : C} (a : P₀ ⟶ P₁) (y : P₁ ⟶ P₂) (c : P₀ ⟶ P₂) (z : P₂ ⟶ Q)
    (h : c = a ≫ y) : a ≫ y ≫ z = c ≫ z := by
  rw [h, Category.assoc]

/-- A factorization `S = c ≫ b ≫ w`, followed by `π`. -/
theorem comp_comp_comp_comp_eq_of_eq {C : Type*} [_root_.CategoryTheory.Category C]
    {P₀ P₁ P₂ P₃ Q : C} (S : P₀ ⟶ P₃) (c : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (w : P₂ ⟶ P₃) (π : P₃ ⟶ Q)
    (h : S = c ≫ b ≫ w) : c ≫ b ≫ w ≫ π = S ≫ π := by
  rw [h]
  simp only [Category.assoc]

end Stacks.CategoryTheory

namespace Stacks.DeRhamSmooth

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- `k + (j + 1) = k + 1 + j`: the degree equation of the `(k, j + 1)` summand in degree
`k + 1 + j`. -/
theorem add_add_one_eq_add_one_add (k j : ℕ) : k + (j + 1) = k + 1 + j := by omega

/-! ### The assembly of `(★_j)` -/

/-- `(1 ⊗ q)` followed by the comparison of Section 0FMK read into the quotient, restricted to
`(f∘g)^{-1}𝒪_S`, is the restriction of the comparison of [Stacks, Tag 01CI] tensored with `1`, the
`(k, j + 1)` wedge product and the projection. -/
theorem restrictScalars_map_tensor_map_deRhamFormsToRelativeHom_comp [Smooth f] (k j : ℕ) :
    (_root_.SheafOfModules.restrictScalars.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ)))).map ((Scheme.Hom.deRhamFormsToRelativeHom f g).app ((j + 1 : ℕ) : ℤ))) ≫
        (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom f g k j) =
        (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
        (pulledBackFormsIso f g k).hom).app (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 :
        ℕ) : ℤ))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq (_root_.SheafOfModules.ringedSpaceAlgebras
        X.toRingedSpace (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j) (by
        omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  Stacks.CategoryTheory.functor_map_comp_map_eq_of_comp_eq
      (_root_.SheafOfModules.restrictScalars.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))) _ _ _ _ _
    (AlgebraicGeometry.Scheme.Hom.tensor_map_deRhamFormsToRelativeHom_comp_pullbackGradedQuotientHom
      f g k j)

/-- **The comparison `c` tensored with `1` splits**: `c = (f^{-1}Ω^k_{Y/S} ⟶ f^*Ω^k_{Y/S})`
followed by the restriction of the comparison of [Stacks, Tag 01CI], tensored with
`Ω^{j+1}_{X/S}` over `(f∘g)^{-1}𝒪_S`. -/
theorem sheafTensor_map_pulledBackFormsComparison_app (k j : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1))) = (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf)).map (relativeInverseImageToPullback f g (Scheme.Hom.relativeDifferentialForms g (k
        : ℤ)))).app ((pushforward (toInverseImageBase (f ≫ g))).obj
        (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) :
        ℤ)))) ≫ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map ((_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (pulledBackFormsIso f g k).hom)).app ((_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)))) :=
  (congrArg (fun t => NatTrans.app t _) (Functor.map_comp _ _ _)).trans (NatTrans.comp_app _ _ _)

/-- **The lax comparison along `(f∘g)^{-1}𝒪_S ⟶ 𝒪_X` crosses the comparison of
[Stacks, Tag 01CI].** -/
theorem laxComparison_pulledBackFormsIso_naturality (k j : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map ((_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (pulledBackFormsIso f g k).hom)).app ((_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)))) ≫
        (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
        g)).exteriorPower (j + 1))) = (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)) ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ))) (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
        (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
        (pulledBackFormsIso f g k).hom).app (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 :
        ℕ) : ℤ))) :=
  AlgebraicGeometry.SheafOfModules.laxComparison_naturality_left (X := X.toRingedSpace)
    (A := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)) (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
    (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)) (pulledBackFormsIso f g k).hom

/-- After the change of rings, `(1 ⊗ q)` followed by the comparison read into the quotient is the
comparison of Tag 01CI tensored with `1`, the wedge product and the projection. -/
theorem laxComparison_comp_restrictScalars_map_eq_wedge [Smooth f] (k j : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
        (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app ((pushforward (toInverseImageBase (f
        ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)))) ≫
        (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ))) (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
        (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ)))).map ((Scheme.Hom.deRhamFormsToRelativeHom f g).app ((j + 1 : ℕ) : ℤ))) ≫
        (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom f g k j) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
          (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app ((pushforward (toInverseImageBase
          (f ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 :
          ℕ) : ℤ)))) ≫ (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
          S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)) ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
          ℤ))) (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
          (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
          (pulledBackFormsIso f g k).hom).app (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1
          : ℕ) : ℤ))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j)
          (by omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  Stacks.CategoryTheory.comp_comp_eq_comp_comp_of_eq _ _
    (restrictScalars_map_tensor_map_deRhamFormsToRelativeHom_comp f g k j)

/-- The comparison of Tag 01CI crosses the lax comparison. -/
theorem laxComparison_comp_wedge_eq_pulledBackFormsIso_comp (k j : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
        (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app ((pushforward (toInverseImageBase (f
        ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)))) ≫
        (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
        ℤ))) (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
        (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
        (pulledBackFormsIso f g k).hom).app (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 :
        ℕ) : ℤ))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq (_root_.SheafOfModules.ringedSpaceAlgebras
        X.toRingedSpace (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j) (by
        omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
          (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app ((pushforward (toInverseImageBase
          (f ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 :
          ℕ) : ℤ)))) ≫ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
          S.sheaf)).map ((_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (pulledBackFormsIso f g k).hom)).app ((_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)))) ≫
          (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
          ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
          g)).exteriorPower (j + 1))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j)
          (by omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  Stacks.CategoryTheory.comp_comp_comp_eq_of_square _ _ _ _ _ _
    (laxComparison_pulledBackFormsIso_naturality f g k j)

/-- The comparison `relativeInverseImageToPullback` followed by the restriction of the comparison
of Tag 01CI, tensored with `1`, is `pulledBackFormsComparison f g k` tensored with `1`. -/
theorem pulledBackFormsIso_comp_wedge_eq_comparison_comp (k j : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
        (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app ((pushforward (toInverseImageBase (f
        ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)))) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map ((_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (pulledBackFormsIso f g k).hom)).app ((_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)))) ≫
        (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
        ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
        g)).exteriorPower (j + 1))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq (_root_.SheafOfModules.ringedSpaceAlgebras
        X.toRingedSpace (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j) (by
        omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
          g)))).X (j + 1))) ≫ (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
          S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)) ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f
          ≫ g)).exteriorPower (j + 1))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j)
          (by omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  Stacks.CategoryTheory.comp_comp_eq_of_eq_comp_left _ _ _ _
    (sheafTensor_map_pulledBackFormsComparison_app f g k j)

/-- `(c ⊗ 1)`, the lax comparison and the wedge product are the `(k, j + 1)` summand of the wedge
map. -/
theorem comparison_comp_wedge_eq_summand_comp (k j : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1))) ≫ (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
        S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)) ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
        g)).exteriorPower (j + 1))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq (_root_.SheafOfModules.ringedSpaceAlgebras
        X.toRingedSpace (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j) (by
        omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
        AlgebraicGeometry.inverseImageStructureMap (f ≫
        g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (Scheme.Hom.relativeDifferentialsShortComplex f
        g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) =
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
        CommRingCat.{u} (f ≫
        g).base).obj S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
        ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
        g)))).X (j + 1)) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (add_add_one_eq_add_one_add k j)).hom) ≫
              (_root_.SheafOfModules.restrictScalars.{u}
              (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
              AlgebraicGeometry.inverseImageStructureMap (f ≫
              g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  Stacks.CategoryTheory.comp_comp_comp_comp_eq_of_eq _ _ _ _ _
    (AlgebraicGeometry.SheafOfModules.summandOfEq_eq_laxComparison_comp (Scheme.Hom.deRhamAlgebras
        (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
      (pulledBackDifferentialsAlgebras f g) (Scheme.Hom.relativeDifferentialsShortComplex f
          g).f (pulledBackDeRhamComplex f g) (Stacks.DeRhamPullback.deRhamPullbackChain f g)
      (pulledBackFormsComparison f g) (deRhamPullbackChain_f_eq_pulledBackFormsComparison_comp f g)
      k (j + 1) (k + 1 + j) (add_add_one_eq_add_one_add k j))

/-- `E_j ≫ M_j` is `c ⊗ 1`, the lax comparison, the restriction of the comparison of Tag 01CI
tensored with `1`, the `(k, j + 1)` wedge product and the projection. -/
theorem stepSummandToGradedTarget_comp_toStepQuotient_eq_wedge [Smooth f] (k j : ℕ) :
    stepSummandToGradedTarget f g k j ≫ gradedTargetXToStepQuotient f g k j =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
          (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app ((pushforward (toInverseImageBase
          (f ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 :
          ℕ) : ℤ)))) ≫ (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
          S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)) ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentialForms g (k :
          ℤ))) (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ))) ≫
          (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map
          (pulledBackFormsIso f g k).hom).app (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1
          : ℕ) : ℤ))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j)
          (by omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  laxComparison_comp_restrictScalars_map_eq_wedge f g k j ▸
    stepSummandToGradedTarget_comp_toStepQuotient_eq' f g k j

/-- `E_j ≫ M_j` is `c ⊗ 1`, the comparison of Tag 01CI tensored with `1`, the lax comparison, the
`(k, j + 1)` wedge product and the projection. -/
theorem stepSummandToGradedTarget_comp_toStepQuotient_eq_pulledBackFormsIso [Smooth f]
    (k j : ℕ) :
    stepSummandToGradedTarget f g k j ≫ gradedTargetXToStepQuotient f g k j =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map (relativeInverseImageToPullback f g
          (Scheme.Hom.relativeDifferentialForms g (k : ℤ)))).app ((pushforward (toInverseImageBase
          (f ≫ g))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 :
          ℕ) : ℤ)))) ≫ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
          S.sheaf)).map ((_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (pulledBackFormsIso f g k).hom)).app ((_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).obj (Scheme.Hom.relativeDifferentialForms (f ≫ g) ((j + 1 : ℕ) : ℤ)))) ≫
          (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫ g))
          ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f ≫
          g)).exteriorPower (j + 1))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j)
          (by omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  laxComparison_comp_wedge_eq_pulledBackFormsIso_comp f g k j ▸
    stepSummandToGradedTarget_comp_toStepQuotient_eq_wedge f g k j

/-- `E_j ≫ M_j` is `pulledBackFormsComparison f g k` tensored with `1`, the lax comparison, the
`(k, j + 1)` wedge product and the projection. -/
theorem stepSummandToGradedTarget_comp_toStepQuotient_eq_comparison [Smooth f] (k j : ℕ) :
    stepSummandToGradedTarget f g k j ≫ gradedTargetXToStepQuotient f g k j =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map (pulledBackFormsComparison f g k)).app
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
          g)))).X (j + 1))) ≫ (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj
          S.sheaf) X.sheaf (AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)) ((pulledBackDifferentialsAlgebras f g).exteriorPower k) ((Scheme.Hom.deRhamAlgebras (f
          ≫ g)).exteriorPower (j + 1))) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (_root_.SheafOfModules.prodWedgeHomOfEq
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) k (j + 1) (k + 1 + j)
          (by omega)) ≫ (_root_.SheafOfModules.restrictScalars.{u}
          (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
          AlgebraicGeometry.inverseImageStructureMap (f ≫
          g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f
          g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  pulledBackFormsIso_comp_wedge_eq_comparison_comp f g k j ▸
    stepSummandToGradedTarget_comp_toStepQuotient_eq_pulledBackFormsIso f g k j

/-- **(★_j) The step summand's source, read in the target complex and then into
`Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`, is the `(k, j + 1)` summand of the wedge map followed by the
projection**, `n = k + 1 + j`:

`E_j ≫ M_j = S_j ≫ π`. -/
theorem stepSummandToGradedTarget_comp_toStepQuotient [Smooth f] (k j : ℕ) :
    stepSummandToGradedTarget f g k j ≫ gradedTargetXToStepQuotient f g k j =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ((TopCat.Sheaf.pullback
          CommRingCat.{u} (f ≫
          g).base).obj S.sheaf)).map ((Stacks.DeRhamPullback.deRhamPullbackChain f g).f k)).app
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
          g)))).X (j + 1)) ≫
        AlgebraicGeometry.SheafOfModules.exteriorProductComponent (Scheme.Hom.deRhamAlgebras (f ≫
            g)) k (j + 1) ≫
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫
              g)))).XIsoOfEq (add_add_one_eq_add_one_add k j)).hom) ≫
              (_root_.SheafOfModules.restrictScalars.{u}
              (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ :=
              AlgebraicGeometry.inverseImageStructureMap (f ≫
              g)))).map (cokernel.π (_root_.SheafOfModules.prodWedgeHom
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₁) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₂) (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f
              g).X₂) (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  comparison_comp_wedge_eq_summand_comp f g k j ▸
    stepSummandToGradedTarget_comp_toStepQuotient_eq_comparison f g k j

end Stacks.DeRhamSmooth

end
