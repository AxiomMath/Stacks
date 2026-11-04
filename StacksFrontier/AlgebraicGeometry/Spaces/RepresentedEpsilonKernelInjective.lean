module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonKernelSurjective

/-!
# Stacks 0D0X: the generators `m_h` of the degree `-1` cohomology sheaf of `NL_{X₀/Y₀}`

Step M4 of the proof of Stacks 0D0X checks that the model
`AlgebraicGeometry.Space.representedEpsilonKernelModel` of the adjunct `ε^*𝒦₀ ⟶ 𝒦` of
`κ_{-1}` is locally injective by rewriting a local section of `𝒪_X ⊗ 𝒦₀` through the sections
`m_h` of `𝒦₀` attached to the chart classes `h ∈ H₁(L_{𝒪_X(ε Z)/𝒪_Y(ε W)})` of an affine Zariski
square `Z ⊆ f_0^{-1}W`.  This file proves that `h ↦ m_h` is additive and semilinear over the
identification `𝒪_X(ε Z) = 𝒪_{X₀}(Z)`.

## Main results

* `Stacks.SheafOfModules.sectionsH1NaiveCotangent_add`,
  `Stacks.SheafOfModules.sectionsH1NaiveCotangent_smul`: the image of `H₁` of the sections in
  `NL^{-1}_{B/A}` is additive and `B`-linear.
* `AlgebraicGeometry.Space.representedZariskiKernelSection_add`,
  `AlgebraicGeometry.Space.representedZariskiKernelSection_smul`: `m_{h₁ + h₂} = m_{h₁} + m_{h₂}`
  and `m_{a • h} = a • m_h`.
* `AlgebraicGeometry.Space.representedTransposeRingHom_map_topIso`: the transposed ring map of
  `ε^♯` at a chart `V` over `ε Z` sends `a|_{L V}` to `a|_V`, for `a ∈ 𝒪_X(ε Z) = 𝒪_{X₀}(Z)`.
* `AlgebraicGeometry.Space.representedKernelTensorModel`: the map
  `ρ : 𝒪_X(V) ⊗_A H ⟶ 𝒪_X(V) ⊗_{𝒪_{X₀}(L V)} 𝒦₀(L V)`, `s ⊗ h ↦ s ⊗ m_h|`, well defined by the
  two previous results.
* `AlgebraicGeometry.Space.representedEpsilonKernelModel_app_representedKernelTensorModel`: the
  model of the adjunct of `κ_{-1}` after `ρ` is the comparison of the chart, through `e`.
* `AlgebraicGeometry.Space.representedKernelTensorModel_restrict`: `ρ` commutes with restriction.
* `AlgebraicGeometry.Space.chartTensorVanishingSieve_mem_of_representedEpsilonKernelModel` and
  `AlgebraicGeometry.Space.representedKernelTensorModel_restrict_eq_zero`: an element `t` with
  `c(ρ t) = 0` restricts to `0` on a covering, and so does `ρ t`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sheaves.ToposPushforward

universe u

namespace Stacks.SheafOfModules

universe v₁ u₁ w₁ z₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w₁}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

/-- The image of `H₁` of the sections in `NL^{-1}_{B/A}` is additive. -/
theorem sectionsH1NaiveCotangent_add (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B) (U : Cᵒᵖ)
    (z₁ z₂ : @Algebra.H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a U (z₁ + z₂) =
      sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a U z₁ +
        sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a U z₂ :=
  (congrArg _ (map_add (sectionsH1Comparison.{v₁, u₁, w₁, z₁} J A B a U) z₁ z₂)).trans
    (map_add _ _ _)

/-- The image of `H₁` of the sections in `NL^{-1}_{B/A}` is linear over the sections of `B`. -/
theorem sectionsH1NaiveCotangent_smul (A B : Sheaf J CommRingCat.{w₁}) (a : A ⟶ B) (U : Cᵒᵖ)
    (b : ToType (B.obj.obj U))
    (z : @Algebra.H1Cotangent (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) _ _
      (algebraSections J A B a U)) :
    letI := algebraSections J A B a U
    sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a U (b • z) =
      b • sectionsH1NaiveCotangent.{v₁, u₁, w₁, z₁} J A B a U z :=
  (congrArg _ (sectionsH1Comparison_smul.{v₁, u₁, w₁, z₁} J A B a U b z)).trans
    (map_smul _ _ _)

end Stacks.SheafOfModules

namespace Stacks.UniverseLift

universe v₅ u₅ r₅ m₅ z₅

variable {C : Type u₅} [Category.{v₅} C] {J : GrothendieckTopology C}

/-- **Restriction of a multiple, read in the transport to the lifted ring**: the scalar is
restricted and lifted. -/
theorem ringTransportEquivalence_map_smul (O : Sheaf J CommRingCat.{r₅})
    (N : _root_.SheafOfModules.{m₅} (Stacks.SheafOfModules.Tensor.ringSheaf O)) {X X' : Cᵒᵖ}
    (f : X ⟶ X') (r : ToType ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X))
    (m : ToType (N.val.obj X)) :
    ((ringTransportEquivalence.{m₅, z₅} O).functor.obj N).val.map f (r • m) =
      (show ToType ((Stacks.SheafOfModules.Tensor.ringSheaf (sheafRingULift.{z₅} O)).obj.obj X')
        from ULift.up.{z₅} ((O.obj.map f).hom r)) •
        ((ringTransportEquivalence.{m₅, z₅} O).functor.obj N).val.map f m :=
  N.val.map_smul f r m

end Stacks.UniverseLift

namespace Stacks.PresheafOfModules

universe v₆ u₆ w₆

/-- Two successive restrictions are the restriction along any composite. -/
theorem map_map_of_comp_eq {C : Type u₆} [Category.{v₆} C] {R : Cᵒᵖ ⥤ RingCat.{w₆}}
    (M : _root_.PresheafOfModules.{w₆} R) {X Y Z : Cᵒᵖ} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ b = c) (m : M.obj X) : M.map b (M.map a m) = M.map c m := by
  rw [← h, _root_.PresheafOfModules.map_comp_apply]

end Stacks.PresheafOfModules

namespace Stacks.PullbackModel

universe w₄

variable {A' B' : Type w₄} [CommRing A'] [CommRing B'] (f : A' →+* B') {M : ModuleCat.{w₄} A'}

/-- The pure tensor `b ⊗ m` is additive in `m`. -/
theorem tmul_add_right (b : B') (m₁ m₂ : M) : tmul f b (m₁ + m₂) = tmul f b m₁ + tmul f b m₂ :=
  TensorProduct.tmul_add _ _ _

/-- The pure tensor `b ⊗ 0` vanishes. -/
theorem tmul_zero_right (b : B') : tmul f b (0 : M) = 0 :=
  TensorProduct.tmul_zero _ _

/-- The pure tensor `b ⊗ m` is additive in `b`. -/
theorem tmul_add_left (b₁ b₂ : B') (m : M) : tmul f (b₁ + b₂) m = tmul f b₁ m + tmul f b₂ m :=
  TensorProduct.add_tmul _ _ _

/-- The pure tensor `0 ⊗ m` vanishes. -/
theorem tmul_zero_left (m : M) : tmul f 0 m = 0 :=
  TensorProduct.zero_tmul _ _

/-- A scalar of `A'` moves across the pure tensor through `f`. -/
theorem tmul_smul_right (b : B') (a : A') (m : M) : tmul f b (a • m) = tmul f (f a * b) m :=
  let : Module A' B' := Module.compHom B' f
  (TensorProduct.smul_tmul (R := A') (M := B') (N := M) a b m).symm

/-- Two additive maps out of a tensor product agree as soon as they agree on pure tensors. -/
theorem addMonoidHom_tensor_ext {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] {g h : TensorProduct R M N →+ P}
    (H : ∀ m n, g (m ⊗ₜ[R] n) = h (m ⊗ₜ[R] n)) : g = h :=
  AddMonoidHom.ext fun t => by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m n => exact H m n
    | add x y hx hy => rw [map_add, map_add, hx, hy]

end Stacks.PullbackModel

namespace Stacks.PullbackLeftAdjoint

universe v₂ u₂ v₃ u₃ w₂

variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
  {F : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ F)
  {O₀ : Cᵒᵖ ⥤ CommRingCat.{w₂}} {O : Dᵒᵖ ⥤ CommRingCat.{w₂}} (φ : O₀ ⟶ F.op ⋙ O)

/-- **The transposed ring map on a restricted section**: for `g : V ⟶ F Z` and `r ∈ O₀(Z)`, the
transpose of `φ` at `V` sends `r|_{L V}` to `φ(r)|_V`, restriction being along the adjunct
`L V ⟶ Z` of `g` and along `g`. -/
theorem transposeRingHom_app_map {V : D} {Z : C} (g : V ⟶ F.obj Z) (r : ToType (O₀.obj (op Z))) :
    ((transposeRingHom adj φ).app (op V)).hom
        ((O₀.map ((adj.homEquiv V Z).symm g).op).hom r) =
      (O.map g.op).hom ((φ.app (op Z)).hom r) := by
  rw [transposeRingHom_app]
  have hn := ConcreteCategory.congr_hom (φ.naturality ((adj.homEquiv V Z).symm g).op) r
  change (φ.app (op (L.obj V))).hom ((O₀.map ((adj.homEquiv V Z).symm g).op).hom r) =
    (O.map (F.map ((adj.homEquiv V Z).symm g)).op).hom ((φ.app (op Z)).hom r) at hn
  show (O.map (adj.unit.app V).op).hom ((φ.app (op (L.obj V))).hom
    ((O₀.map ((adj.homEquiv V Z).symm g).op).hom r)) = _
  rw [hn, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  have e : adj.unit.app V ≫ F.map ((adj.homEquiv V Z).symm g) = g :=
    (adj.homEquiv_unit V Z _).symm.trans ((adj.homEquiv V Z).apply_symm_apply g)
  rw [e]

end Stacks.PullbackLeftAdjoint

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V) {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
  {W : ((BigFppfOver.toScheme B S hS).obj V).Opens}

/-- **`h ↦ m_h` is additive.** -/
theorem representedZariskiKernelSection_add
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (h₁ h₂ : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    representedZariskiKernelSection B S hS φ hZW (h₁ + h₂) =
      representedZariskiKernelSection B S hS φ hZW h₁ +
        representedZariskiKernelSection B S hS φ hZW h₂ := by
  apply Stacks.SheafOfModules.injective_app_kernel_ι _ (op Z)
  refine (kernel_ι_representedZariskiKernelSection B S hS φ hZW _).trans ?_
  refine Eq.trans ?_ (map_add ((kernel.ι
    ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app (op Z)).hom
      _ _).symm
  refine (congrArg _ (map_add _ h₁ h₂)).trans
    ((Stacks.SheafOfModules.sectionsH1NaiveCotangent_add.{u, u, u, u + 1} _ _ _ _ _ _ _).trans ?_)
  exact congrArg₂ (· + ·) (kernel_ι_representedZariskiKernelSection B S hS φ hZW h₁).symm
    (kernel_ι_representedZariskiKernelSection B S hS φ hZW h₂).symm

/-- **`h ↦ m_h` is semilinear** over the identification `𝒪_X(ε Z) = 𝒪_{X₀}(Z)`. -/
theorem representedZariskiKernelSection_smul
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (a : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op (representedEpsilonChartDiagram B S hS φ hZW).U)))
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    letI := chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)
    representedZariskiKernelSection B S hS φ hZW (a • h) =
      (show ToType ((Stacks.SheafOfModules.Tensor.ringSheaf
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).obj.obj (op Z)) from
        (Scheme.Opens.topIso Z).hom.hom a) • representedZariskiKernelSection B S hS φ hZW h := by
  let := chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)
  let := representedZariskiAlgebra B S hS φ Z
  apply Stacks.SheafOfModules.injective_app_kernel_ι _ (op Z)
  refine (kernel_ι_representedZariskiKernelSection B S hS φ hZW _).trans ?_
  refine Eq.trans ?_ (map_smul ((kernel.ι
    ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0)).val.app (op Z)).hom
      _ _).symm
  refine (congrArg _ (Stacks.NaiveCotangent.h1CotangentMapOfSquare_smul _ _ _ a h)).trans
    ((Stacks.SheafOfModules.sectionsH1NaiveCotangent_smul.{u, u, u, u + 1} _ _ _ _ _ _ _).trans ?_)
  exact congrArg (_ • ·) (kernel_ι_representedZariskiKernelSection B S hS φ hZW h).symm

/-- **The transposed ring map of `ε^♯` on the restriction of a function on `Z`**, over the
lifted rings: for a chart `V` over `ε Z`, the function `a ∈ 𝒪_X(ε Z) = 𝒪_{X₀}(Z)` restricted to
`L V` is sent to `a|_V`. -/
theorem representedTransposeRingHom_map_topIso (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (a : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op (representedEpsilonChartDiagram B S hS φ hZW).U))) :
    ((Stacks.PullbackLeftAdjoint.transposeRingHom (representedImageOpenEpsilonAdjunction B S hS U)
        (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).app (op V.left)).hom
      (((Stacks.UniverseLift.sheafRingULift.{u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).obj.map
        (((representedImageOpenEpsilonAdjunction B S hS U).homEquiv V.left Z).symm V.hom).op).hom
        (ULift.up ((Scheme.Opens.topIso Z).hom.hom a))) =
      ULift.up (chartDiagramRestrictO B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V a) := by
  refine (Stacks.PullbackLeftAdjoint.transposeRingHom_app_map _ _ V.hom _).trans ?_
  have h1 := representedToZariskiRingedToposSiteHom_fSharp_app_apply B S hS U Z
    ((Scheme.Opens.topIso Z).hom.hom a)
  show ULift.up (((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map
    V.hom.op).hom (((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom.app (op Z)).hom
      ((Scheme.Opens.topIso Z).hom.hom a))) = _
  rw [h1]
  exact congrArg (fun x => ULift.up (((smallEtaleRingedTopos B S hS
    (representedAlgebraicSpace B S hS U)).O.obj.map V.hom.op).hom x))
    (ConcreteCategory.congr_hom (Scheme.Opens.topIso Z).hom_inv_id a)

/-- `m_h` restricted to the image open `L V` of a chart `V` over `ε Z`, in the lifted spelling. -/
abbrev representedZariskiKernelSectionAt (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :=
  ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
      (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val.map
    (((representedImageOpenEpsilonAdjunction B S hS U).homEquiv V.left Z).symm V.hom).op
    (representedZariskiKernelSection B S hS φ hZW h)

/-- The section `m_h` attached to `h = 0` is zero. -/
theorem representedZariskiKernelSection_zero
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :
    representedZariskiKernelSection B S hS φ hZW 0 = 0 := by
  have e := representedZariskiKernelSection_add B S hS φ hZW 0 0
  rw [add_zero] at e
  exact (add_eq_left.mp e.symm)

/-- The transposed ring map `𝒪_{X₀}(L V)↑ ⟶ 𝒪_X(V)↑` of `ε^♯` at a chart `V`, over the lifted
rings. -/
abbrev representedLiftedTranspose (V : SmallEtale B S hS (yoneda.obj U)) :=
  ((Stacks.PullbackLeftAdjoint.transposeRingHom (representedImageOpenEpsilonAdjunction B S hS U)
    (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).app (op V)).hom

/-- The restriction of `m_h` to `L V` vanishes for `h = 0`. -/
theorem representedZariskiKernelSectionAt_zero
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U) :
    representedZariskiKernelSectionAt B S hS φ hZW V 0 = 0 :=
  (congrArg _ (representedZariskiKernelSection_zero B S hS φ hZW)).trans (map_zero _)

/-- The restriction of `m_h` to `L V` is additive in `h`. -/
theorem representedZariskiKernelSectionAt_add
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (h₁ h₂ : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    representedZariskiKernelSectionAt B S hS φ hZW V (h₁ + h₂) =
      representedZariskiKernelSectionAt B S hS φ hZW V h₁ +
        representedZariskiKernelSectionAt B S hS φ hZW V h₂ :=
  (congrArg _ (representedZariskiKernelSection_add B S hS φ hZW h₁ h₂)).trans (map_add _ _ _)

/-- **The tensor model `ρ : 𝒪_X(V) ⊗_A H ⟶ 𝒪_X(V) ⊗_{𝒪_{X₀}(L V)} 𝒦₀(L V)`**,
`s ⊗ h ↦ s ⊗ m_h|_{L V}`, for a chart `V` over `ε Z` of an affine Zariski square. -/
def representedKernelTensorModel (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U) :
    chartLocalTensor B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V →+
      ToType (((Stacks.PullbackLeftAdjoint.pullbackModel
        (representedImageOpenEpsilonAdjunction B S hS U)
        (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).obj
        ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
          (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val).obj
        (op V.left)) :=
  letI := chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)
  letI := chartDiagramRestrictAlgebra B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW) V
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun h => Stacks.PullbackModel.tmul (representedLiftedTranspose B S hS V.left)
            (ULift.up.{u + 1} s) (representedZariskiKernelSectionAt B S hS φ hZW V h)
          map_zero' := (congrArg (Stacks.PullbackModel.tmul
              (representedLiftedTranspose B S hS V.left) (ULift.up.{u + 1} s))
              (representedZariskiKernelSectionAt_zero B S hS φ hZW V)).trans
            (Stacks.PullbackModel.tmul_zero_right _ _)
          map_add' := fun h₁ h₂ => (congrArg (Stacks.PullbackModel.tmul
              (representedLiftedTranspose B S hS V.left) (ULift.up.{u + 1} s))
              (representedZariskiKernelSectionAt_add B S hS φ hZW V h₁ h₂)).trans
            (Stacks.PullbackModel.tmul_add_right _ _ _ _) }
      map_zero' := AddMonoidHom.ext fun h => Stacks.PullbackModel.tmul_zero_left _ _
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun h =>
        Stacks.PullbackModel.tmul_add_left (representedLiftedTranspose B S hS V.left)
          (ULift.up.{u + 1} s₁) (ULift.up.{u + 1} s₂) _ }
    (fun a s h => by
      change Stacks.PullbackModel.tmul (representedLiftedTranspose B S hS V.left)
          (ULift.up.{u + 1} (chartDiagramRestrictO B S hS (representedSpaceMap B S hS φ)
            (representedEpsilonChartDiagram B S hS φ hZW) V a * s))
          (representedZariskiKernelSectionAt B S hS φ hZW V h) =
        Stacks.PullbackModel.tmul (representedLiftedTranspose B S hS V.left) (ULift.up.{u + 1} s)
          (representedZariskiKernelSectionAt B S hS φ hZW V (a • h))
      refine Eq.trans ?_ (congrArg (fun m => Stacks.PullbackModel.tmul
        (representedLiftedTranspose B S hS V.left) (ULift.up.{u + 1} s)
        (((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
          (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val.map
          (((representedImageOpenEpsilonAdjunction B S hS U).homEquiv V.left Z).symm V.hom).op m))
        (representedZariskiKernelSection_smul B S hS φ hZW a h)).symm
      refine Eq.trans ?_ (congrArg (Stacks.PullbackModel.tmul
        (representedLiftedTranspose B S hS V.left) (ULift.up.{u + 1} s))
        (Stacks.UniverseLift.ringTransportEquivalence_map_smul.{u, u, u, u + 1, u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O
          (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))
          (((representedImageOpenEpsilonAdjunction B S hS U).homEquiv V.left Z).symm V.hom).op
          ((Scheme.Opens.topIso Z).hom.hom a)
          (representedZariskiKernelSection B S hS φ hZW h))).symm
      refine Eq.trans ?_ (Stacks.PullbackModel.tmul_smul_right _ _ _ _).symm
      refine congrArg (fun b => Stacks.PullbackModel.tmul (representedLiftedTranspose B S hS V.left)
        b (representedZariskiKernelSectionAt B S hS φ hZW V h)) ?_
      exact (congrArg (· * ULift.up.{u + 1} s)
        (representedTransposeRingHom_map_topIso B S hS φ hZW V a)).symm)

/-- **The model map on `s ⊗ m_h|`** is the comparison of the chart on `s ⊗ h`, through `e`. -/
theorem representedEpsilonKernelModel_app_tmul_representedZariskiKernelSectionAt
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (s : ToType ((chartSliceRing B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)).obj.obj (op V)))
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    (representedEpsilonKernelModel B S hS φ).app (op V.left)
        (Stacks.PullbackModel.tmul (representedLiftedTranspose B S hS V.left) (ULift.up.{u + 1} s)
          (representedZariskiKernelSectionAt B S hS φ hZW V h)) =
      (representedNaiveCotangentKernelIso B S hS φ).hom.val.app (op V.left)
        (((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW)).app (op V)).hom
          (s ⊗ₜ[chartGlobalRing B S hS (representedSpaceMap B S hS φ)
            (representedEpsilonChartDiagram B S hS φ hZW)]
              chartH1Up B S hS (representedSpaceMap B S hS φ)
                (representedEpsilonChartDiagram B S hS φ hZW) h)) := by
  let T := representedLiftedTranspose B S hS V.left
  let x := representedZariskiKernelSectionAt B S hS φ hZW V h
  refine (congrArg ((representedEpsilonKernelModel B S hS φ).app (op V.left))
    ((congrArg (Stacks.PullbackModel.tmul T · x) (mul_one _).symm).trans
      (Stacks.PullbackModel.smul_tmul T _ 1 x).symm)).trans ?_
  refine (((representedEpsilonKernelModel B S hS φ).app (op V.left)).hom.map_smul _ _).trans ?_
  refine (congrArg (@HSMul.hSMul _ _ _ _ _)
    (representedEpsilonKernelModel_app_tmul_one_representedZariskiKernelSection B S hS φ hZW
      h V.left V.hom)).trans ?_
  refine Eq.trans ?_ (congrArg ((representedNaiveCotangentKernelIso B S hS φ).hom.val.app
    (op V.left)).hom (chartKernelPresheafHom_app_tmul B S hS
      (representedSpaceMap B S hS φ) (representedEpsilonChartDiagram B S hS φ hZW) V s
        (chartH1Up B S hS _ _ h)).symm)
  refine Eq.trans ?_ (((representedNaiveCotangentKernelIso B S hS φ).hom.val.app
    (op V.left)).hom.map_smul _ _).symm
  exact congrArg (@HSMul.hSMul _ _ _ _ _) (PresheafOfModules.naturality_apply
    (representedNaiveCotangentKernelIso B S hS φ).hom.val V.hom.op _).symm

/-- **`c ∘ ρ = e ∘ (comparison of the chart)`** on `𝒪_X(V) ⊗_A H`. -/
theorem representedEpsilonKernelModel_app_representedKernelTensorModel
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (V : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (t : chartLocalTensor B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V) :
    (representedEpsilonKernelModel B S hS φ).app (op V.left)
        (representedKernelTensorModel B S hS φ hZW V t) =
      (representedNaiveCotangentKernelIso B S hS φ).hom.val.app (op V.left)
        (((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW)).app (op V)).hom
          (chartTensorOfLocal B S hS (representedSpaceMap B S hS φ)
            (representedEpsilonChartDiagram B S hS φ hZW) V t)) := by
  let := chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)
  let := chartDiagramRestrictAlgebra B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW) V
  exact DFunLike.congr_fun (Stacks.PullbackModel.addMonoidHom_tensor_ext
    (g := ((representedEpsilonKernelModel B S hS φ).app (op V.left)).hom.toAddMonoidHom.comp
      (representedKernelTensorModel B S hS φ hZW V))
    (h := (((representedNaiveCotangentKernelIso B S hS φ).hom.val.app
      (op V.left)).hom.toAddMonoidHom.comp
        ((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW)).app (op V)).hom.toAddMonoidHom).comp
      (chartTensorOfLocal B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V))
    fun s h => representedEpsilonKernelModel_app_tmul_representedZariskiKernelSectionAt B S hS φ
      hZW V s h) t

/-- `m_h|_{L V}` restricted along a morphism of charts over `ε Z` is `m_h|_{L V'}`. -/
theorem representedZariskiKernelSectionAt_map (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    {V₁ V₂ : Over (representedEpsilonChartDiagram B S hS φ hZW).U} (g : V₂ ⟶ V₁)
    (h : chartH1 B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)) :
    ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
        (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val.map
      ((representedImageOpenFunctor B S hS U).map g.left).op
      (representedZariskiKernelSectionAt B S hS φ hZW V₁ h) =
      representedZariskiKernelSectionAt B S hS φ hZW V₂ h :=
  Stacks.PresheafOfModules.map_map_of_comp_eq
    ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
      (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val _ _ _
    rfl _

/-- **`ρ` commutes with restriction.** -/
theorem representedKernelTensorModel_restrict
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    {V₁ V₂ : Over (representedEpsilonChartDiagram B S hS φ hZW).U} (g : V₂ ⟶ V₁)
    (t : chartLocalTensor B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V₁) :
    ((Stacks.PullbackLeftAdjoint.pullbackModel
        (representedImageOpenEpsilonAdjunction B S hS U)
        (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).obj
        ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
          (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val).map
        g.left.op (representedKernelTensorModel B S hS φ hZW V₁ t) =
      representedKernelTensorModel B S hS φ hZW V₂
        (chartRestrictTensor B S hS (representedSpaceMap B S hS φ)
          (representedEpsilonChartDiagram B S hS φ hZW) g t) := by
  let := chartDiagramAlgebraInst B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW)
  let := chartDiagramRestrictAlgebra B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW) V₁
  have key := Stacks.PullbackModel.addMonoidHom_tensor_ext
    (g := (((Stacks.PullbackLeftAdjoint.pullbackModel
        (representedImageOpenEpsilonAdjunction B S hS U)
        (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).obj
        ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
          (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val).map
        g.left.op).hom.toAddMonoidHom.comp (representedKernelTensorModel B S hS φ hZW V₁))
    (h := (representedKernelTensorModel B S hS φ hZW V₂).comp
      (chartRestrictTensor B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) g).toAddMonoidHom)
    (fun s h => congrArg (Stacks.PullbackModel.tmul (representedLiftedTranspose B S hS V₂.left) _)
      (representedZariskiKernelSectionAt_map B S hS φ hZW g h))
  exact DFunLike.congr_fun key t

/-- **An element of `𝒪_X(V) ⊗_A H` whose image under `c ∘ ρ` vanishes vanishes locally**: it
restricts to `0` on a covering of `V`. -/
theorem chartTensorVanishingSieve_mem_of_representedEpsilonKernelModel
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) (hZ : IsAffineOpen Z)
    (hW : IsAffineOpen W) (V' : Over (representedEpsilonChartDiagram B S hS φ hZW).U)
    (t : chartLocalTensor B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V')
    (ht : (representedEpsilonKernelModel B S hS φ).app (op V'.left)
        (representedKernelTensorModel B S hS φ hZW V' t) = 0) :
    chartTensorVanishingSieve B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V' t ∈
      (SmallEtale.topology B S hS (yoneda.obj U)).over
        (representedEpsilonChartDiagram B S hS φ hZW).U V' := by
  let o := chartTensorOfLocal B S hS (representedSpaceMap B S hS φ)
    (representedEpsilonChartDiagram B S hS φ hZW) V' t
  have h0 : ((chartKernelPresheafHom B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW)).app (op V')).hom o = 0 := by
    have e1 := (representedEpsilonKernelModel_app_representedKernelTensorModel B S hS φ hZW V'
      t).symm.trans ht
    have e2 := congrArg ((representedNaiveCotangentKernelIso B S hS φ).inv.val.app
      (op V'.left)).hom e1
    refine (ConcreteCategory.congr_hom (congrArg (fun a => a.val.app (op V'.left))
      (representedNaiveCotangentKernelIso B S hS φ).hom_inv_id) _).symm.trans
      (e2.trans (map_zero _))
  have hmem := chartTensorVanishingSieve_mem_of_chartKernelPresheafHom B S hS
    (representedSpaceMap B S hS φ) (representedEpsilonChartDiagram B S hS φ hZW)
    (isAffine_representedEpsilonFunctor_obj B S hS U hZ)
    (isAffine_representedEpsilonFunctor_obj B S hS V hW) V' o h0
  have e3 : chartTensorToLocal B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW) V' o = t :=
    (chartTensorEquiv B S hS (representedSpaceMap B S hS φ)
      (representedEpsilonChartDiagram B S hS φ hZW) V').apply_symm_apply t
  rwa [e3] at hmem

/-- On the vanishing sieve of `t`, the restriction of `ρ t` is `ρ 0`. -/
theorem representedKernelTensorModel_restrict_eq_zero
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    {V₁ V₂ : Over (representedEpsilonChartDiagram B S hS φ hZW).U} (g : V₂ ⟶ V₁)
    (t : chartLocalTensor B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V₁)
    (hg : chartTensorVanishingSieve B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW) V₁ t g) :
    ((Stacks.PullbackLeftAdjoint.pullbackModel
        (representedImageOpenEpsilonAdjunction B S hS U)
        (Stacks.PullbackLeftAdjoint.commRingHom (Stacks.UniverseLift.liftedRingHom.{u + 1}
          (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing))).obj
        ((Stacks.UniverseLift.ringTransportEquivalence.{u + 1, u + 1}
          ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).functor.obj
          (kernel ((representedZariskiToposNaiveCotangentComplex B S hS φ).d (-1) 0))).val).map
        g.left.op (representedKernelTensorModel B S hS φ hZW V₁ t) =
      representedKernelTensorModel B S hS φ hZW V₂ 0 :=
  (representedKernelTensorModel_restrict B S hS φ hZW g t).trans
    (congrArg (representedKernelTensorModel B S hS φ hZW V₂) hg)

end AlgebraicGeometry.Space

end
