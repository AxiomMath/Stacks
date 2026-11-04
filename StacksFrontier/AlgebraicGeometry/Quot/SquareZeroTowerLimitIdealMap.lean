module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitSolution
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison
public import StacksFrontier.Deformation.ToposThickening.KernelPushoutAlgebraExtension

/-!
# The map from `f^*𝒞_{Y₀/Y}` to the ideal of `𝒜 = lim 𝒪_{Xₙ}`

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] views `𝒜 = lim Aₙ` as an extension of `f⁻¹𝒪_Y`-algebras of `𝒪_{X₀}`
by `lim 𝒪_{X₀} ⊗ Iₙ`. The thickened base carries its ideal `f⁻¹𝒞_{Y₀/Y}` into that ideal, and the
`f⁻¹𝒪_{Y₀}`-linear map so obtained has an `𝒪_{X₀}`-linear adjunct
`φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ`. Along this `φ` the solution
`AlgebraicGeometry.ProperFlatFibre.towerLimitSolution` exists unconditionally.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerLimitAlgebraExtension`: `𝒜` as an extension of
  `f⁻¹𝒪_Y`-algebras.
* `AlgebraicGeometry.ProperFlatFibre.towerLimitIdealMap`: the induced `f⁻¹𝒞_{Y₀/Y} ⟶ lim 𝒪 ⊗ Iₙ`.
* `AlgebraicGeometry.ProperFlatFibre.towerLimitKernelMap`: its adjunct
  `φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪 ⊗ Iₙ`.
* `AlgebraicGeometry.ProperFlatFibre.towerLimitSolutionOfKernelMap`: the solution `𝒜` of the
  problem changed along `φ`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Deformation.ToposThickening

universe u v w v' u' u'' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

variable {X : RingedTopos.{v, u', w}} {B' : RingedTopos.{v', u'', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B'.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})]
  (S : RingedToposExtensionProblem X B')
  [Presheaf.IsLocallySurjective X.J S.baseReductionInverseImagePresheafHom]

/-- **A map `φ : 𝒢 ⟶ ℳ` whose composite with `c` is the map induced on the base ideal by an
extension `𝒪'` of `f⁻¹𝒪_{B'}`-algebras carries the base ideal to the kernel**: the image in `𝒪'`
of a section of `f⁻¹𝒥` is the image of its value under `φ ∘ c`. -/
theorem algebraMap_idealInclusion_of_c_comp_eq_idealMap
    {M : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (Q : AlgebraExtension ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
      S.f.fSharpInverseImage) M) (φ : S.G ⟶ M)
    (hφ : S.c ≫ (SheafOfModules.restrictScalars ((sheafCompose X.J
        (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map φ =
      S.idealMap (Iso.refl _) (Category.id_comp _) Q)
    (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    Q.algebraMap.hom.app U
        (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
          S.idealInclusion.val.app U x) =
      (show Q.extension.obj.obj U from
        Q.kernelInclusion.val.app U (φ.val.app U (S.c.val.app U x))) :=
  (S.incl_idealMap (Iso.refl _) (Category.id_comp _) Q U x).symm.trans
    (congrArg Q.incl (congrArg (fun k => k.val.app U x) hφ).symm)

end Deformation.ToposThickening.RingedToposExtensionProblem

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

/-- **`𝒜 = lim Aₙ` as an extension of `f⁻¹𝒪_Y`-algebras** of `𝒪_{X₀}` by `lim 𝒪_{X₀} ⊗ Iₙ`, the
algebra structure being the map from the inverse image of the thickened base. -/
abbrev towerLimitAlgebraExtension :
    Deformation.AlgebraExtension (J := Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.toToposHom).map
          (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseReduction ≫
        (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.fSharpInverseImage)
      (limit (towerIdealSystem ξ hsurj hsq e he)) where
  extension := towerRingLimit ξ
  reduction := towerRingLimitReduction ξ
  locallySurjective := isLocallySurjective_towerRingLimitReduction ξ hsurj hsq e he
  squareZero := towerRingLimitReduction_squareZero ξ hsurj hsq e he
  algebraMap := towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc
  algebraMap_reduction := towerProblemLimitBaseMap_reduction ξ c hsurj hsq e cR hcR eLimit hc
  kernelInclusion := Deformation.AlgebraExtension.InverseLimit.kernelInclusion.{u, u + 1, u}
    (J := Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (towerRingSystem ξ)
    (towerRingReduction ξ) (fun n => towerExtension ξ hsurj hsq e he n (𝟙 _))
    (fun n => towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _))
    (fun n => towerRingSystemExtensionIso_hom_comp_reduction ξ hsurj hsq e he n (𝟙 _))
  kernelZero := Deformation.AlgebraExtension.InverseLimit.kernelZero.{u, u + 1, u} _ _ _ _ _
  kernelUniversal :=
    Deformation.AlgebraExtension.InverseLimit.kernelUniversal.{u, u + 1, u} _ _ _ _ _

/-- The inverse image of the reduction of the thickened base is locally surjective. -/
theorem isLocallySurjective_towerProblem_baseReductionInverseImage :
    Presheaf.IsLocallySurjective (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseReductionInverseImagePresheafHom :=
  Space.isLocallySurjective_inverseImage_map B S hS (towerStructureMap ξ 0)
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseReduction
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseLocallySurjective

attribute [local instance] isLocallySurjective_towerProblem_baseReductionInverseImage

/-- **The map `f⁻¹𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` induced by `𝒜`**: a section of the base ideal is
carried by the thickened base into the kernel of `𝒜 ⟶ 𝒪_{X₀}`, which is `lim 𝒪_{X₀} ⊗ Iₙ`. -/
def towerLimitIdealMap :=
  (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).idealMap (Iso.refl _) (Category.id_comp _)
    (towerLimitAlgebraExtension ξ hsurj hsq e he cR hcR c eLimit hc)

/-- **`φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ`**, the `𝒪_{X₀}`-linear adjunct of
`towerLimitIdealMap`. -/
def towerLimitKernelMap :
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G ⟶ limit (towerIdealSystem ξ hsurj hsq e he) :=
  ((Space.extendScalarsFSharpAdjunction B S hS (towerStructureMap ξ 0)).homEquiv _ _).symm
    (towerLimitIdealMap ξ hsurj hsq e he cR hcR c eLimit hc)

/-- `φ` composed with the canonical `f⁻¹𝒞_{Y₀/Y} ⟶ f^*𝒞_{Y₀/Y}` is `towerLimitIdealMap`. -/
theorem towerProblem_c_comp_towerLimitKernelMap :
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).c ≫
        (SheafOfModules.restrictScalars ((sheafCompose
          (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map
            (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.fSharpInverseImage)).map
          (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc) =
      towerLimitIdealMap ξ hsurj hsq e he cR hcR c eLimit hc :=
  ((Space.extendScalarsFSharpAdjunction B S hS
    (towerStructureMap ξ 0)).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **`φ` carries the base ideal to the kernel**: the image in `𝒜` of a section of `f⁻¹𝒞_{Y₀/Y}`
is the image of its value under `φ`. -/
theorem towerLimitKernelMap_ideal (U : (Space.SmallEtale B S hS (towerSpace ξ 0).1)ᵒᵖ)
    (a : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).I.val.obj U) :
    (towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc).hom.app U
        ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).idealInclusion.val.app U a) =
      (Deformation.AlgebraExtension.InverseLimit.kernelInclusion.{u, u + 1, u}
        (J := Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (towerRingSystem ξ)
        (towerRingReduction ξ) (fun n => towerExtension ξ hsurj hsq e he n (𝟙 _))
        (fun n => towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _))
        (fun n => towerRingSystemExtensionIso_hom_comp_reduction ξ hsurj hsq e he n
          (𝟙 _))).val.app U
        ((towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc).val.app U
          ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).c.val.app U a)) :=
  (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).algebraMap_idealInclusion_of_c_comp_eq_idealMap
    (towerLimitAlgebraExtension ξ hsurj hsq e he cR hcR c eLimit hc) _
    (towerProblem_c_comp_towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc) U a

/-- **`𝒜 = lim 𝒪_{Xₙ}` solves the tower problem changed along `φ = towerLimitKernelMap`.** -/
def towerLimitSolutionOfKernelMap :
    ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).changeKernel
      (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)).CompatibleFirstOrderThickening :=
  towerLimitSolution ξ hsurj hsq e he cR hcR c eLimit hc _
    (towerLimitKernelMap_ideal ξ hsurj hsq e he cR hcR c eLimit hc)

end AlgebraicGeometry.ProperFlatFibre

end
