module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblem
public import StacksFrontier.Deformation.Artin.Obstruction.ObstructionBoundaryRestriction
public import StacksFrontier.Deformation.ToposThickening.SolutionClassChangeOfBase

/-!
# Condition (iv) of Stacks 07YY for `Spaces'_{fp, flat, proper}` at a chart

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart. For a
square-zero thickening `D : Spec A ⊂ Spec A'` of Situation 07YX with ideal `I`, the extension
problem of [Stacks, Section 08V3] of `x` along `D`, posed over `Spec A`, is
`AlgebraicGeometry.Space.ProperFlatLift.problemOnChart x hx D`. Its morphism is `X → Spec A` and
its prescribed module is `𝒪_X ⊗_A I`, so its obstruction class of [Stacks, Tag 08V5]
(`canonicalObstructionClass`) lies in `T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)`.

This file proves condition (iv) of [Stacks, Tag 07YY] for these obstruction classes. Take a short
exact sequence of deformation situations `A₃' → A₂' → A₁'` (Remark 07YE) and a lift `x'₂` of `x`
over `A₂'`, read over `A₃'` as a solution `Q` of the problem of `A₃'` with target `𝒪_X ⊗_A I₂`.
Its restriction to `A[I₁]` is an extension `E₁` of `f⁻¹𝒪_A`-algebras by `𝒪_X ⊗_A I₁` receiving a
map from `Q`, and the tangent class of the restricted lift is `−(cmp ≫ ε(E₁))`. Then the
obstruction of `A₃'` is the connecting map `T¹(I₁) ⟶ T²(I₃)` applied to this tangent class.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.chartObstruction_eq_chartExtConnecting`: the
  identity for one short exact sequence.
* `AlgebraicGeometry.Space.ProperFlatLift.chartObstruction_boundary`: the `boundary` field of
  `Deformation.Artin.FunctorDeformationTheory` for the obstruction classes `chartObstruction`.

## References

* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
* [Stacks Project, Tag 07YE](https://stacks.math.columbia.edu/tag/07YE)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin Deformation.ToposThickening RingedToposExtensionProblem
open Deformation.Artin.ObstructionBoundaryRestriction

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

variable {x hx}

variable {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
  {D₁ : SquareZeroThickening A B S hS toS hA A₁}
  {D₂ : SquareZeroThickening A B S hS toS hA A₂}
  {D₃ : SquareZeroThickening A B S hS toS hA A₃}
  {g₂₁ : SquareZeroThickening.Hom D₂ D₁} {g₃₂ : SquareZeroThickening.Hom D₃ D₂}

omit [HasDerivedCategory.{t} (modelModules x.obj.obj.left)] in
/-- The image of the kernel sequence `0 → I₃ → I₂ → I₁ → 0` under `𝒪_X ⊗_A −` is short exact. -/
theorem shortExact_tensor_kernelSequence
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom) :
    ((ShortComplex.mk g₃₂.kernelMap g₂₁.kernelMap (kernelMap_comp_eq_zero hses)).map
      (modelTensorFunctor (chartBaseRingHom x hx))).ShortExact :=
  shortExact_map_modelTensorFunctor_chartBaseRingHom x hx (kernelSequenceShortExact hses)

/-- **Condition (iv) for one short exact sequence.** Let `A₃' → A₂' → A₁'` be a short exact
sequence of deformation situations, `Q` a solution of the problem of `A₃'` with target changed to
`𝒪_X ⊗_A I₂`, `E₁` an extension of `f⁻¹𝒪_A`-algebras by `𝒪_X ⊗_A I₁` and `h` a map from `Q` to
`E₁` over `𝒪_X`, under `f⁻¹𝒪_{A₃'}`, inducing `𝒪_X ⊗ (I₂ → I₁)` on the kernels. If
`θ ∈ T¹(I₁)` is `−(cmp ≫ ε(E₁))`, then the obstruction class of `A₃'` is the connecting map
applied to `θ`. -/
theorem chartObstruction_eq_chartExtConnecting
    (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom)
    (Q : ((problemOnChart x hx D₃).mapTarget
      ((modelTensorFunctor (chartBaseRingHom x hx)).map
        g₃₂.kernelMap)).CompatibleFirstOrderThickening)
    (E₁ : Deformation.AlgebraExtension (J := (modelTopos x.obj.obj.left).J)
      (modelRingedToposHom (chartStructureMap x hx)).fSharpInverseImage
      ((modelTensorFunctor (chartBaseRingHom x hx)).obj D₁.kernel))
    (h : Q.extension ⟶ E₁.extension) (hred : h ≫ E₁.reduction = Q.reduction)
    (halg : Q.baseMap ≫ h = (problemOnChart x hx D₃).baseReductionInverseImage ≫ E₁.algebraMap)
    (hker : ∀ (U : (modelTopos x.obj.obj.left).Cᵒᵖ)
      (m : ((modelTensorFunctor (chartBaseRingHom x hx)).obj D₂.kernel).val.obj U),
      h.hom.app U (Q.kernelInclusion.val.app U m) =
        E₁.incl ((((modelTensorFunctor (chartBaseRingHom x hx)).map g₂₁.kernelMap).val.app U m :
          ((modelTensorFunctor (chartBaseRingHom x hx)).obj D₁.kernel).val.obj U)))
    (θ : (cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).obj D₁.kernel)
    (hθ : cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 1
        D₁.kernel θ =
      -(DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} _
          (modelRingedToposHom (chartStructureMap x hx)).fSharpInverseImage) ≫
        Deformation.AlgebraExtension.extClass.{t, u} E₁)) :
    chartObstruction x hx D₃ = chartExtConnecting x hx (kernelSequenceShortExact hses) θ := by
  have key := (problemOnChart x hx D₃).canonicalObstructionClass_eq_neg_extClass_comp_singleδ
    ((modelTensorFunctor (chartBaseRingHom x hx)).map g₃₂.kernelMap)
    ((modelTensorFunctor (chartBaseRingHom x hx)).map g₂₁.kernelMap)
    ((ShortComplex.mk g₃₂.kernelMap g₂₁.kernelMap (kernelMap_comp_eq_zero hses)).map
      (modelTensorFunctor (chartBaseRingHom x hx))).zero
    (shortExact_tensor_kernelSequence hses) Q E₁ h hred halg hker
  refine (cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 2
    D₃.kernel).injective ?_
  refine (cotangentExtFunctorObjEquiv_chartObstruction x hx D₃).trans (key.trans ?_)
  refine Eq.trans ?_ (cotangentExtFunctorObjEquiv_cotangentExtConnecting (chartStructureMap x hx)
    (chartBaseRingHom x hx) (shortExact_tensor_kernelSequence hses) θ).symm
  exact congrArg (fun ξ => ShiftedHom.comp (a := (1 : ℤ)) ξ
    (shortExact_tensor_kernelSequence hses).singleδ (show (1 : ℤ) + 1 = 2 by norm_num)) hθ.symm

variable (x hx) (fibered : (cartesianProperFlatProjection B S hS).IsFiberedInGroupoids)
  (rsStar : SatisfiesRSStar B S hS (cartesianProperFlatProjection B S hS) fibered)

/-- **The `boundary` field (condition (iv) of [Stacks, Tag 07YY]) for the obstruction classes
`chartObstruction`.** Let `τ` be a tangent map `T_x(M) ⟶ T¹(M)`, and set
`o(D) = chartObstruction x hx D ∈ T²(I)`, the class `canonicalObstructionClass` of
`problemOnChart x hx D`. Suppose that for every short exact sequence of deformation situations
`A₃' → A₂' → A₁'` and every lift `x'₂` over `A₂'`, the tangent class under `τ` of the
restriction of `x'₂` to `A₁' = A[I₁]` is `−(cmp ≫ ε(E₁))` for some extension `E₁` of
`f⁻¹𝒪_A`-algebras by `𝒪_X ⊗_A I₁` receiving a map from a solution of the problem of `A₃'` with
target `𝒪_X ⊗_A I₂` (`restrictedLiftExtension`, the restriction of `x'₂` read through the
splitting `A → A₁'`, with `x'₂` read over `A₃'`). Then the `boundary` field of
`Deformation.Artin.FunctorDeformationTheory` holds for `τ`, `o` and the connecting map
`chartExtConnecting x hx`. -/
theorem chartObstruction_boundary
    (τ : ∀ M : SiteModule A B,
      ((tangentFunctor A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx fibered
          rsStar).functor.obj M : Type _) →ₗ[A]
        ((cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx)).obj M.obj : Type _))
    (restrictedLiftExtension : ∀ (A₁ A₂ A₃ : Type u) [CommRing A₁] [CommRing A₂] [CommRing A₃]
      (D₁ : SquareZeroThickening A B S hS toS hA A₁)
      (D₂ : SquareZeroThickening A B S hS toS hA A₂)
      (D₃ : SquareZeroThickening A B S hS toS hA A₃)
      (g₂₁ : SquareZeroThickening.Hom D₂ D₁) (g₃₂ : SquareZeroThickening.Hom D₃ D₂)
      (hses : IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom)
      (lift₂ : (Under.post (cartesianProperFlatProjection B S hS)).Fiber
        (Under.mk (eqToHom hx ≫ D₂.arrow))),
      ∃ (Q : ((problemOnChart x hx D₃).mapTarget
          ((modelTensorFunctor (chartBaseRingHom x hx)).map
            g₃₂.kernelMap)).CompatibleFirstOrderThickening)
        (E₁ : Deformation.AlgebraExtension (J := (modelTopos x.obj.obj.left).J)
          (modelRingedToposHom (chartStructureMap x hx)).fSharpInverseImage
          ((modelTensorFunctor (chartBaseRingHom x hx)).obj D₁.kernel))
        (h : Q.extension ⟶ E₁.extension),
        h ≫ E₁.reduction = Q.reduction ∧
        Q.baseMap ≫ h = (problemOnChart x hx D₃).baseReductionInverseImage ≫ E₁.algebraMap ∧
        (∀ (U : (modelTopos x.obj.obj.left).Cᵒᵖ)
          (m : ((modelTensorFunctor (chartBaseRingHom x hx)).obj D₂.kernel).val.obj U),
          h.hom.app U (Q.kernelInclusion.val.app U m) =
            E₁.incl ((((modelTensorFunctor (chartBaseRingHom x hx)).map g₂₁.kernelMap).val.app U
              m : ((modelTensorFunctor (chartBaseRingHom x hx)).obj D₁.kernel).val.obj U))) ∧
        cotangentExtFunctorObjEquiv (chartStructureMap x hx) (chartBaseRingHom x hx) 1 D₁.kernel
            (τ (kernelSiteModule D₁)
              (((tangentFunctor A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx
                fibered rsStar).liftEquiv (kernelSiteModule D₁)).symm
                  (restrictedLiftClass fibered hses lift₂))) =
          -(DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} _
              (modelRingedToposHom (chartStructureMap x hx)).fSharpInverseImage) ≫
            Deformation.AlgebraExtension.extClass.{t, u} E₁)) :
    ∀ (A₁ A₂ A₃ : Type u) [CommRing A₁] [CommRing A₂] [CommRing A₃]
      (D₁ : SquareZeroThickening A B S hS toS hA A₁)
      (D₂ : SquareZeroThickening A B S hS toS hA A₂)
      (D₃ : SquareZeroThickening A B S hS toS hA A₃)
      (g₂₁ : SquareZeroThickening.Hom D₂ D₁) (g₃₂ : SquareZeroThickening.Hom D₃ D₂),
      IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom →
      ∀ lift₂ : (Under.post (cartesianProperFlatProjection B S hS)).Fiber
        (Under.mk (eqToHom hx ≫ D₂.arrow)),
      ∃ (hzero : g₃₂.kernelMap ≫ g₂₁.kernelMap = 0)
        (hSq : (ShortComplex.mk g₃₂.kernelMap g₂₁.kernelMap hzero).ShortExact)
        (hmem : B.Contains (Spec (squareZeroRing A D₁.kernel)))
        (s : A →+* A₁) (ψ : A₂ →+* (squareZeroRing A D₁.kernel : Type u))
        (_hs : g₂₁.ringHom.comp g₃₂.ringHom = s.comp D₃.q)
        (_hψfst : ∀ y : A₂, (ψ y).fst = D₂.q y)
        (_hψsnd : ∀ y : A₂, ((ψ y).snd).1 = g₂₁.ringHom y - s (D₂.q y)),
        letI M₁ : SiteModule A B := ⟨D₁.kernel, hmem⟩
        ∃ (dMap : squareZeroOver A B S hS toS M₁ ⟶ (Over.mk D₂.toS' : BigFppfOver B S hS))
          (lift₁ : (Under.post (cartesianProperFlatProjection B S hS)).Fiber
            (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M₁)))
          (φ : lift₁.1.right ⟶ lift₂.1.right),
          B.inclusion.map dMap.left = Spec.map (CommRingCat.ofHom ψ) ∧
          squareZeroArrow A B S hS toS hA M₁ ≫ dMap = D₂.arrow ∧
          (cartesianProperFlatProjection B S hS).IsStronglyCartesian dMap φ ∧
          lift₁.1.hom ≫ φ = lift₂.1.hom ∧
            chartObstruction x hx D₃ =
              chartExtConnecting x hx hSq (τ M₁
                (((tangentFunctor A B S hS toS hA (cartesianProperFlatProjection B S hS) x hx
                    fibered rsStar).liftEquiv M₁).symm (Quotient.mk _ lift₁))) :=
  boundary_of_restrictedLiftClass A B S hS toS hA (CartesianProperFlatSpaces B S hS)
    (cartesianProperFlatProjection B S hS) x hx fibered rsStar
    (cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx))
    (cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx))
    (fun hSq => chartExtConnecting x hx hSq) τ
    (fun _ _ D => chartObstruction x hx D)
    (fun A₁ A₂ A₃ _ _ _ D₁ D₂ D₃ g₂₁ g₃₂ hses lift₂ => by
      obtain ⟨Q, E₁, h, hred, halg, hker, hθ⟩ :=
        restrictedLiftExtension A₁ A₂ A₃ D₁ D₂ D₃ g₂₁ g₃₂ hses lift₂
      exact chartObstruction_eq_chartExtConnecting hses Q E₁ h hred halg hker _ hθ)

end AlgebraicGeometry.Space.ProperFlatLift

end
