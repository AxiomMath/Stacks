module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.Tautological
import all StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyRelativelyAmple
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso

/-!
# The multiplication of the twists on a relative `Proj`

Let `A` be a quasi-coherent graded algebra on a scheme `S` whose section rings over the affine
opens are generated in degree one, and let `𝒪(n)` be the twists on its relative `Proj`, given by a
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`. The multiplication of the glued graded
algebra descends to the tensor product, `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)`, and this map is an
isomorphism: on the affine charts it is the multiplication of the absolute twists, which is an
isomorphism by [Stacks, Tag 01MT].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistMul`: `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isIso_twistMul`: it is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (D : TwistData A)

/-- **The multiplication `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)` of the twists on a relative `Proj`.** -/
public def twistMul (i j : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (relativeProj A).scheme.sheaf).obj
        (D.algebra.piece i)).obj (D.algebra.piece j) ⟶
      D.algebra.piece (i + j) :=
  SheafOfModules.GradedAlgebra.mulSheaf (J := Opens.grothendieckTopology (relativeProj A).scheme)
    (Osharp := (relativeProj A).scheme.sheaf) D.algebra i j

/-- The multiplication of the twists on the germ of a pure tensor of sections. -/
public theorem twistMul_germ (i j : ℤ) (x : (relativeProj A).scheme)
    (W : (relativeProj A).scheme.Opens)
    (hx : x ∈ W) (a : (D.algebra.piece i).val.obj (op W)) (b : (D.algebra.piece j).val.obj (op W)) :
    ((SheafOfModules.stalkFunctor (relativeProj A).scheme.ringCatSheaf x).map (twistMul D i j)).hom
        ((TopCat.Presheaf.germ (PresheafOfModules.tensorSheafVal (relativeProj A).scheme.sheaf
          (D.algebra.piece i) (D.algebra.piece j)).presheaf W x hx).hom
          ((PresheafOfModules.tensorSheafUnit (D.algebra.piece i) (D.algebra.piece j)).app (op W)
            (a ⊗ₜ b))) =
      (TopCat.Presheaf.germ (D.algebra.piece (i + j)).val.presheaf W x hx).hom
        ((D.algebra.mul i j).app (op W) a b) :=
  (AlgebraicGeometry.stalk_map_germ (twistMul D i j) x W hx _).trans
    (congrArg (TopCat.Presheaf.germ (D.algebra.piece (i + j)).val.presheaf W x hx).hom
      (SheafOfModules.GradedAlgebra.mulSheaf_unit (J := Opens.grothendieckTopology _)
        (Osharp := (relativeProj A).scheme.sheaf) D.algebra i j (op W) a b))

/-- Every element of the stalk of a tensor product of sheaves of modules on a ringed space is a
sum of germs of pure tensors of sections. -/
public theorem mem_closure_tensorGerm (X : RingedSpace.{u, u})
    (F G : SheafOfModules.{u} (structureSheafRing X)) (x : X)
    (w : Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})).obj F).obj
          G).val x) :
    w ∈ AddSubgroup.closure {z | ∃ (V : Opens X) (hx : x ∈ V) (a : F.val.obj (op V))
      (b : G.val.obj (op V)), z = Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})).obj F).obj
          G).val x V hx
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G (op V)
          (a ⊗ₜ b))} := by
  set e := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X x F G
  obtain ⟨t, rfl⟩ := e.symm.surjective w
  induction t using TensorProduct.inductionOn with
  | tmul α β =>
    obtain ⟨V₁, hx₁, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf α
    obtain ⟨V₂, hx₂, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf β
    have hx : x ∈ V₁ ⊓ V₂ := ⟨hx₁, hx₂⟩
    refine AddSubgroup.subset_closure ⟨V₁ ⊓ V₂, hx,
      F.val.presheaf.map (homOfLE inf_le_left).op a,
      G.val.presheaf.map (homOfLE inf_le_right).op b, ?_⟩
    refine (LinearEquiv.symm_apply_eq e).2 ?_
    refine Eq.trans ?_ (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ X x F G
      (V₁ ⊓ V₂) hx _ _).symm
    exact congrArg₂ (fun p q => p ⊗ₜ q)
      (TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE inf_le_left) x hx a).symm
      (TopCat.Presheaf.germ_res_apply G.val.presheaf (homOfLE inf_le_right) x hx b).symm
  | add t₁ t₂ h₁ h₂ => rw [map_add]; exact AddSubgroup.add_mem _ h₁ h₂

/-- On the germ of a canonical product of absolute twist sections, the composite of the
stalk of the absolute multiplication, the inverse chart identification and the comparison of
stalks along the chart is the stalk of `twistMul` on a germ of a pure tensor. -/
private theorem restrictStalkHom_chartIso_inv_twistMultiplicationMap_germ (U : S.Opens)
    (hU : IsAffineOpen U) (i j : ℤ) (x' : AlgebraicGeometry.Proj (A.grading U))
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens) (hx : x' ∈ V)
    (a : (twistingSheaf (A.grading U) i).val.obj (op V))
    (b : (twistingSheaf (A.grading U) j).val.obj (op V)) :
    letI := D.chartData.chart_isOpenImmersion U hU
    ∀ hxV : ((relativeProj A).chart U hU).base x' ∈ (relativeProj A).chart U hU ''ᵁ V,
    AlgebraicGeometry.restrictStalkHom ((relativeProj A).chart U hU) x' (D.algebra.piece (i + j))
        (((SheafOfModules.stalkFunctor (AlgebraicGeometry.Proj (A.grading U)).ringCatSheaf x').map
          (D.chartData.chartIso U hU (i + j)).inv).hom
          (((SheafOfModules.stalkFunctor (AlgebraicGeometry.Proj (A.grading U)).ringCatSheaf x').map
            (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
              (A.grading U) i j)).hom
            (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm
              (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ⟨(AlgebraicGeometry.Proj (A.grading U)).toRingedSpace.presheaf,
                  (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace.IsSheaf⟩).obj
                (twistingSheaf (A.grading U) i)).obj (twistingSheaf (A.grading U) j)).val x' V hx
              (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
                (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace
                (twistingSheaf (A.grading U) i) (twistingSheaf (A.grading U) j) (op V)
                (a ⊗ₜ b))))) =
      ((SheafOfModules.stalkFunctor (relativeProj A).scheme.ringCatSheaf
          (((relativeProj A).chart U hU).base x')).map (twistMul D i j)).hom
        ((TopCat.Presheaf.germ (PresheafOfModules.tensorSheafVal (relativeProj A).scheme.sheaf
          (D.algebra.piece i) (D.algebra.piece j)).presheaf ((relativeProj A).chart U hU ''ᵁ V)
            (((relativeProj A).chart U hU).base x') hxV).hom
          ((PresheafOfModules.tensorSheafUnit (D.algebra.piece i) (D.algebra.piece j)).app
            (op ((relativeProj A).chart U hU ''ᵁ V))
            (D.chartData.mapSection U hU i V a ⊗ₜ D.chartData.mapSection U hU j V b))) := by
  let := D.chartData.chart_isOpenImmersion U hU
  intro hxV
  have h1 := AlgebraicGeometry.stalk_map_germ
    (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap (A.grading U) i j) x' V hx
    (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
      (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace
      (twistingSheaf (A.grading U) i) (twistingSheaf (A.grading U) j) (op V) (a ⊗ₜ b))
  have h2 := AlgebraicGeometry.stalk_map_germ (D.chartData.chartIso U hU (i + j)).inv x' V hx
    (absoluteTwistProduct (A.grading U) i j V a b)
  have h3 := AlgebraicGeometry.restrictStalkHom_germ ((relativeProj A).chart U hU) x'
    (D.algebra.piece (i + j)) V hx
    ((D.chartData.chartIso U hU (i + j)).inv.app V (absoluteTwistProduct (A.grading U) i j V a b))
  have h4 := D.chartIso_mul U hU i j V a b
  have h5 := twistMul_germ D i j (((relativeProj A).chart U hU).base x')
    ((relativeProj A).chart U hU ''ᵁ V) hxV (D.chartData.mapSection U hU i V a)
    (D.chartData.mapSection U hU j V b)
  refine (congrArg (fun z => AlgebraicGeometry.restrictStalkHom ((relativeProj A).chart U hU) x'
    (D.algebra.piece (i + j))
    (((SheafOfModules.stalkFunctor (AlgebraicGeometry.Proj (A.grading U)).ringCatSheaf x').map
      (D.chartData.chartIso U hU (i + j)).inv).hom z)) h1).trans ?_
  refine (congrArg (fun z => AlgebraicGeometry.restrictStalkHom ((relativeProj A).chart U hU) x'
    (D.algebra.piece (i + j)) z) h2).trans ?_
  refine h3.trans ?_
  refine Eq.trans ?_ h5.symm
  exact congrArg (TopCat.Presheaf.germ (D.algebra.piece (i + j)).val.presheaf
    ((relativeProj A).chart U hU ''ᵁ V) (((relativeProj A).chart U hU).base x') hxV).hom h4

/-- **The multiplication of the twists is surjective on the stalk at a point of a chart**, the
multiplication of the absolute twists on that chart being surjective on stalks. -/
public theorem surjective_stalk_twistMul_chart (U : S.Opens) (hU : IsAffineOpen U)
    (hgen : Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (i j : ℤ) (x' : AlgebraicGeometry.Proj (A.grading U)) :
    letI := D.chartData.chart_isOpenImmersion U hU
    Function.Surjective ((SheafOfModules.stalkFunctor (relativeProj A).scheme.ringCatSheaf
      (((relativeProj A).chart U hU).base x')).map (twistMul D i j)).hom := by
  let := D.chartData.chart_isOpenImmersion U hU
  set c := (relativeProj A).chart U hU with hc
  have hiso := Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin
    (A.grading U) hgen i j
  have hbij : ∀ {M N : Scheme.Modules (AlgebraicGeometry.Proj (A.grading U))} (e : M ≅ N),
      Function.Bijective ((SheafOfModules.stalkFunctor
        (AlgebraicGeometry.Proj (A.grading U)).ringCatSheaf x').map e.hom).hom :=
    fun e => ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.stalkFunctor (AlgebraicGeometry.Proj (A.grading U)).ringCatSheaf x').mapIso
        e).hom
  have hsurj := (hbij (@asIso _ _ _ _
    (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap (A.grading U) i j)
    hiso)).2
  have hchart := hbij (D.chartData.chartIso U hU (i + j)).symm
  intro y
  obtain ⟨y₁, rfl⟩ := (AlgebraicGeometry.bijective_restrictStalkHom c x' _).2 y
  obtain ⟨y₂, rfl⟩ := hchart.2 y₁
  obtain ⟨w, rfl⟩ := hsurj y₂
  have hw := mem_closure_tensorGerm (AlgebraicGeometry.Proj (A.grading U)).toRingedSpace
    (twistingSheaf (A.grading U) i) (twistingSheaf (A.grading U) j) x' w
  let Φ := (((Scheme.Modules.restrictStalkNatIso c x').hom.app
      (D.algebra.piece (i + j))).hom.comp
    ((((SheafOfModules.stalkFunctor (AlgebraicGeometry.Proj (A.grading U)).ringCatSheaf x').map
      (D.chartData.chartIso U hU (i + j)).inv).hom.toAddMonoidHom).comp
    (((SheafOfModules.stalkFunctor (AlgebraicGeometry.Proj (A.grading U)).ringCatSheaf x').map
      (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
        (A.grading U) i j)).hom.toAddMonoidHom)))
  let μ := ((SheafOfModules.stalkFunctor (relativeProj A).scheme.ringCatSheaf
      (c.base x')).map (twistMul D i j)).hom.toAddMonoidHom
  refine ((AddSubgroup.closure_le ((μ.range).comap Φ)).2 ?_) hw
  rintro _ ⟨V, hx, a, b, rfl⟩
  exact ⟨_, (restrictStalkHom_chartIso_inv_twistMultiplicationMap_germ D U hU i j x' V hx a b
    (by simpa using hx)).symm⟩

/-- The stalk map of a morphism of modules on a scheme, in the two spellings of the stalk. -/
public theorem stalkFunctor_map_hom_eq_stalkMapL {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (x : X) (z : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map φ).hom z =
      PresheafOfModules.stalkMapL x φ.val z := by
  obtain ⟨W, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf z
  exact (AlgebraicGeometry.stalk_map_germ φ x W hx t).trans
    (PresheafOfModules.stalkMapL_germ x φ.val W hx t).symm

variable (hgen : ∀ U : S.Opens, IsAffineOpen U →
  Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
include hgen

/-- **The multiplication of the twists is surjective on every stalk.** -/
public theorem surjective_stalk_twistMul (i j : ℤ) (x : (relativeProj A).scheme) :
    Function.Surjective ((SheafOfModules.stalkFunctor (relativeProj A).scheme.ringCatSheaf x).map
      (twistMul D i j)).hom := by
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show (relativeProj A).toBase.base x ∈ (⊤ : S.Opens) from trivial)
  have hVa : IsAffineOpen V := hV
  let := D.chartData.chart_isOpenImmersion V hVa
  have hx : x ∈ (relativeProj A).chart V hVa ''ᵁ ⊤ := by
    rw [D.chartData.chart_range V hVa]; exact hxV
  obtain ⟨x', -, rfl⟩ := hx
  exact surjective_stalk_twistMul_chart D V hVa (hgen V hVa) i j x'

/-- The stalks of the twists are free of rank one. -/
public theorem nonempty_basis_stalk_piece (n : ℤ) (x : (relativeProj A).scheme) :
    Nonempty (Module.Basis (Fin 1)
      ↑(TopCat.Presheaf.stalk (relativeProj A).scheme.presheaf x)
      ↑(TopCat.Presheaf.stalk (D.algebra.piece n).val.presheaf x)) := by
  have := Stacks.AlgebraicGeometry.TwistMapsInvertible.isInvertibleModule_piece D.chartData hgen n
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (relativeProj A).scheme)
        (relativeProj A).scheme.sheaf) (D.algebra.piece n) 1 :=
    Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule _ _
  exact ⟨Stacks.SheafOfModules.TopWedge.stalkBasis (D.algebra.piece n) 1 x⟩

omit hgen in
/-- A morphism `F ⊗ G ⟶ H` of sheaves of modules whose source factors and target have stalks free
of rank one is an isomorphism as soon as it is surjective on stalks. -/
public theorem isIso_of_surjective_of_basis {Y : TopCat.{u}}
    {Osharp : Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u}}
    {F G H : _root_.SheafOfModules.{u}
      (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology ↥Y) Osharp)}
    (φ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G ⟶ H)
    (hF : ∀ y : Y, Nonempty (Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj y)
      ↑(TopCat.Presheaf.stalk F.val.presheaf y)))
    (hG : ∀ y : Y, Nonempty (Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj y)
      ↑(TopCat.Presheaf.stalk G.val.presheaf y)))
    (hH : ∀ y : Y, Nonempty (Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj y)
      ↑(TopCat.Presheaf.stalk H.val.presheaf y)))
    (hsurj : ∀ y : Y, Function.Surjective (PresheafOfModules.stalkMapL y φ.val)) : IsIso φ := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap φ).2 fun y => ?_
  obtain ⟨bF⟩ := hF y
  obtain ⟨bG⟩ := hG y
  obtain ⟨bH⟩ := hH y
  have hinj := Stacks.ExteriorPower.injective_of_surjective_of_basis_fin_one
    (((bF.tensorProduct bG).reindex Stacks.ExteriorPower.finOneProdEquiv).map
      (PresheafOfModules.tensorSheafStalkEquiv Osharp F G y).symm) bH _ (hsurj y)
  refine ⟨fun a c hac => hinj ?_, fun z => ?_⟩
  · exact (Stacks.SheafOfModules.TopWedge.stalkMap_hom_apply _ y a).symm.trans
      (hac.trans (Stacks.SheafOfModules.TopWedge.stalkMap_hom_apply _ y c))
  · obtain ⟨w, hw⟩ := hsurj y z
    exact ⟨w, (Stacks.SheafOfModules.TopWedge.stalkMap_hom_apply _ y w).trans hw⟩

/-- **The multiplication `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)` of the twists on a relative `Proj` is an
isomorphism**, for a graded algebra generated in degree one over the affine opens. -/
public theorem isIso_twistMul (i j : ℤ) : IsIso (twistMul D i j) :=
  isIso_of_surjective_of_basis (twistMul D i j) (nonempty_basis_stalk_piece D hgen i)
    (nonempty_basis_stalk_piece D hgen j) (nonempty_basis_stalk_piece D hgen (i + j))
    fun x y => by
      obtain ⟨z, hz⟩ := surjective_stalk_twistMul D hgen i j x y
      exact ⟨z, (stalkFunctor_map_hom_eq_stalkMapL _ x z).symm.trans hz⟩

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
