module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealPushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a tensor product on a proper scheme of dimension at most one

For `ℰ` and `𝒱` locally free of constant finite ranks `n` and `m` on a scheme `X` proper of
dimension at most one over a field `k`,

`deg(ℰ ⊗ 𝒱) = m · deg(ℰ) + n · deg(𝒱)`.

More generally, for every coherent `𝒪_X`-module `ℱ`,

`χ((ℰ ⊗ 𝒱) ⊗ ℱ) + nm·χ(ℱ) = m·χ(ℰ ⊗ ℱ) + n·χ(𝒱 ⊗ ℱ)`.  (⋆)

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `isCurve_of_topologicalKrullDim_eq_one`: a proper integral scheme of dimension one over a field
  is a curve over it.
* `eulerCharacteristic_tensorSheaf_add_of_shortExact_of_isProper`: additivity of `χ(X, 𝒲 ⊗ −)` on
  a proper scheme over a field, for `𝒲` finite locally free of constant rank.
* `eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_isCurve` and
  `eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_supp_le_zero`: the identity (⋆) on a proper
  curve, and for a module with zero-dimensional support on any proper scheme.
* `eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_pushforward`: (⋆) at the direct image of a
  coherent module from an integral closed subscheme.
* `eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_isCoherent`: (⋆) for every coherent module.
* `curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`:
  `deg(ℰ ⊗ 𝒱) = m · deg(ℰ) + n · deg(𝒱)`.

## References

* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Integral curves, and additivity of `χ(X, 𝒲 ⊗ −)` -/

/-- **A proper integral scheme of dimension one over a field is a curve over that field.** -/
theorem isCurve_of_topologicalKrullDim_eq_one (k : Type u) [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k))
    [IsIntegral Z] [IsProper g] (h : topologicalKrullDim Z = 1) : IsCurve k g :=
  (isCurve_iff k g).2
    ⟨{ toIsIntegral := ‹_›
       toIsSeparated := inferInstance
       toLocallyOfFiniteType := inferInstance
       toQuasiCompact := inferInstance }, h⟩

/-- **Additivity of `χ(X, 𝒲 ⊗ −)` along a short exact sequence of coherent modules on a proper
scheme over a field**, for `𝒲` finite locally free of constant rank. -/
theorem eulerCharacteristic_tensorSheaf_add_of_shortExact_of_isProper (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (W : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} W r]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : SheafOfModules.IsCoherent S.X₁) (h₂ : SheafOfModules.IsCoherent S.X₂)
    (h₃ : SheafOfModules.IsCoherent S.X₃)
    (c₁ : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (W)).obj (S.X₁))))
    (c₂ : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (W)).obj (S.X₂))))
    (c₃ : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (W)).obj (S.X₃)))) :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (W)).obj (S.X₂))) c₂ =
      @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (W)).obj (S.X₁))) c₁ +
        @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (W)).obj (S.X₃))) c₃ := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hW : SheafOfModules.IsCoherent W := isCoherent_of_isFiniteLocallyFreeOfRank W r
  have hfl :=
    @Stacks.InvertibleLocallyFree.finiteLocallyFree_isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      _ _ _ X.presheaf X.ringCatSheaf.2 _ _ W r (by assumption)
  have hflat : Stacks.SheafOfModules.IsFlat
      (C := TopologicalSpace.Opens X.toTopCat)
      (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) W :=
    @Scheme.Modules.isFlat_of_isFiniteLocallyFree X W hfl
  obtain ⟨hz, hse⟩ :=
    Stacks.SheafOfModules.sheafTensorRight_shortExact_of_flat_factor S W hS hflat
  let d₁ := @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace S.X₁ W h₁ hW
  let d₂ := @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace S.X₂ W h₂ hW
  let d₃ := @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace S.X₃ W h₃ hW
  have hχ := @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hse
    d₁ d₂ d₃
    (forall_finiteDimensional_cohomologyOverField_of_isProper k f _ d₁)
    (forall_finiteDimensional_cohomologyOverField_of_isProper k f _ d₃)
  exact (@eulerCharacteristic_tensorSheaf_comm k _ X f _ S.X₂ W h₂ hW).symm.trans <| hχ.trans <|
    congrArg₂ (· + ·) (@eulerCharacteristic_tensorSheaf_comm k _ X f _ S.X₁ W h₁ hW)
      (@eulerCharacteristic_tensorSheaf_comm k _ X f _ S.X₃ W h₃ hW)

/-! ### The tensor Euler identity in dimension one and in dimension zero -/

/-- **The tensor Euler identity on a proper curve.** For `ℰ` and `𝒱` finite locally free of
constant ranks `n` and `m` and `ℱ` coherent on a proper curve over a field,

`χ((ℰ ⊗ 𝒱) ⊗ ℱ) + nm·χ(ℱ) = m·χ(ℰ ⊗ ℱ) + n·χ(𝒱 ⊗ ℱ)`. -/
theorem eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_isCurve (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f] (E V G : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m]
    (hG : SheafOfModules.IsCoherent G)
    (hEG : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))))
    (hVG : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (G))))
    (hEVG : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj (G)))) :
    @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj
              (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj (G)))
          hEVG +
        ((n * m : ℕ) : ℤ) * @eulerCharacteristic k _ X f _ G hG =
      (m : ℤ) * @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hEG +
        (n : ℤ) * @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (G))) hVG := by
  have hdim : topologicalKrullDim X ≤ 1 :=
    le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))
  let hEV : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m
  let := hG
  obtain ⟨hT1, h1⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6
      k _ X f _ _ ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V)))
      (n * m) hEV
      (fun G' _ _ _ _ hG' p =>
        forall_finiteDimensional_cohomologyOverField_of_isProper k f G' hG' p)
      (fun p => forall_finiteDimensional_cohomologyOverField_of_isProper k f _
        (SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1) p)
      G hG
  obtain ⟨hT2, h2⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6
      k _ X f _ _ E n _
      (fun G' _ _ _ _ hG' p =>
        forall_finiteDimensional_cohomologyOverField_of_isProper k f G' hG' p)
      (fun p => forall_finiteDimensional_cohomologyOverField_of_isProper k f _
        (SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1) p)
      G hG
  obtain ⟨hT3, h3⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6
      k _ X f _ _ V m _
      (fun G' _ _ _ _ hG' p =>
        forall_finiteDimensional_cohomologyOverField_of_isProper k f G' hG' p)
      (fun p => forall_finiteDimensional_cohomologyOverField_of_isProper k f _
        (SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1) p)
      G hG
  have hdeg : @curveDegree k _ X f _ hdim
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m) hEV =
      (m : ℤ) * curveDegree k f hdim E n + (n : ℤ) * curveDegree k f hdim V m :=
    curveDegree_tensorSheaf_eq_add k f hdim E V n m
  have h1' : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj
              (G)))
          hEVG =
        (Scheme.Modules.fiberRank G (genericPoint X) : ℤ) *
            @curveDegree k _ X f _ hdim
              ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
                  ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V)))
              (n * m) hEV +
          ((n * m : ℕ) : ℤ) * @eulerCharacteristic k _ X f _ G hG := h1
  have h2' : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hEG =
        (Scheme.Modules.fiberRank G (genericPoint X) : ℤ) * @curveDegree k _ X f _ hdim E n ‹_› +
          (n : ℤ) * @eulerCharacteristic k _ X f _ G hG := h2
  have h3' : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (G))) hVG =
        (Scheme.Modules.fiberRank G (genericPoint X) : ℤ) * @curveDegree k _ X f _ hdim V m ‹_› +
          (m : ℤ) * @eulerCharacteristic k _ X f _ G hG := h3
  rw [h1', h2', h3', hdeg]
  push_cast
  ring

/-- **The tensor Euler identity for a coherent module with zero-dimensional support**, on any
proper scheme over a field and with no dimension hypothesis on the scheme:

`χ((ℰ ⊗ 𝒱) ⊗ 𝒢) + nm·χ(𝒢) = m·χ(ℰ ⊗ 𝒢) + n·χ(𝒱 ⊗ 𝒢)`. -/
theorem eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_supp_le_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (E V G : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m]
    (hG : SheafOfModules.IsCoherent G)
    (hsupp : topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0)
    (hEG : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))))
    (hVG : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (G))))
    (hEVG : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj (G)))) :
    @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj
              (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj (G)))
          hEVG +
        ((n * m : ℕ) : ℤ) * @eulerCharacteristic k _ X f _ G hG =
      (m : ℤ) * @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hEG +
        (n : ℤ) * @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (G))) hVG := by
  let hEV : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m
  obtain ⟨hT1, h1⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank X k _ f _
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) G (n * m)
      hEV hG hsupp
  obtain ⟨hT2, h2⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank X k _ f _ E G n
      ‹_› hG hsupp
  obtain ⟨hT3, h3⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank X k _ f _ V G m
      ‹_› hG hsupp
  have h1' : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj
              (G)))
          hEVG = ((n * m : ℕ) : ℤ) * @eulerCharacteristic k _ X f _ G hG := h1
  have h2' : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hEG =
        (n : ℤ) * @eulerCharacteristic k _ X f _ G hG := h2
  have h3' : @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (G))) hVG =
        (m : ℤ) * @eulerCharacteristic k _ X f _ G hG := h3
  rw [h1', h2', h3']
  push_cast
  ring

/-! ### The tensor Euler identity for coherent modules -/

/-- Finite locally free modules `ℰ`, `𝒱` on a locally Noetherian scheme, and `ℰ ⊗ 𝒱`, are
coherent. -/
private theorem isCoherent_and_isCoherent_and_isCoherent_tensorSheaf (X : Scheme.{u})
    [IsLocallyNoetherian X] (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m] :
    SheafOfModules.IsCoherent E ∧ SheafOfModules.IsCoherent V ∧ SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) :=
  ⟨isCoherent_of_isFiniteLocallyFreeOfRank E n, isCoherent_of_isFiniteLocallyFreeOfRank V m,
    @isCoherent_of_isFiniteLocallyFreeOfRank X _ _ (n * m)
      (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m)⟩

/-- **The tensor Euler identity at a module pushed forward from an integral closed subscheme** of
a proper scheme of dimension at most one over a field. -/
theorem eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_pushforward (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdimX : topologicalKrullDim X ≤ 1) (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m]
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (G : Z.Modules) (hG : SheafOfModules.IsCoherent G)
    (hF : SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj G))
    (hEF : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (((Scheme.Modules.pushforward i).obj G)))))
    (hVF : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (((Scheme.Modules.pushforward i).obj G)))))
    (hEVF : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj
          (((Scheme.Modules.pushforward i).obj G))))) :
    @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj
              (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj
              (((Scheme.Modules.pushforward i).obj G)))) hEVF +
        ((n * m : ℕ) : ℤ) * @eulerCharacteristic k _ X f _
          ((Scheme.Modules.pushforward i).obj G) hF =
      (m : ℤ) * @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
              (((Scheme.Modules.pushforward i).obj G)))) hEF +
        (n : ℤ) * @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj
              (((Scheme.Modules.pushforward i).obj G)))) hVF := by
  have hXLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hZLN : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have hproper : IsProper (i ≫ f) := inferInstance
  have hdimZ : topologicalKrullDim Z ≤ 1 :=
    le_trans (IsClosedImmersion.isClosedEmbedding i).isInducing.topologicalKrullDim_le hdimX
  let hEV : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m
  let hEp : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj E) n := isFiniteLocallyFreeOfRank_pullback i E n
  let hVp : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i).obj V) m := isFiniteLocallyFreeOfRank_pullback i V m
  obtain ⟨hEpc, hVpc, -⟩ := isCoherent_and_isCoherent_and_isCoherent_tensorSheaf Z
    ((Scheme.Modules.pullback i).obj E) ((Scheme.Modules.pullback i).obj V) n m
  obtain ⟨hEc, hVc, hEVc⟩ := isCoherent_and_isCoherent_and_isCoherent_tensorSheaf X E V n m
  have hEVpc : SheafOfModules.IsCoherent
      ((Scheme.Modules.pullback i).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V)))) :=
    @isCoherent_of_isFiniteLocallyFreeOfRank Z hZLN _ (n * m)
      (@isFiniteLocallyFreeOfRank_pullback Z X i
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m)
        hEV)
  have hZid : @eulerCharacteristic k _ Z (i ≫ f) hproper
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z.toRingedSpace)).presheaf,
              ((Z.toRingedSpace)).IsSheaf⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩).obj
              (((Scheme.Modules.pullback i).obj E))).obj (((Scheme.Modules.pullback i).obj
              V)))))).obj (G)))
          (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ G
            (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ _ hEpc hVpc) hG) +
        ((n * m : ℕ) : ℤ) * @eulerCharacteristic k _ Z (i ≫ f) hproper G hG =
      (m : ℤ) * @eulerCharacteristic k _ Z (i ≫ f) hproper
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z.toRingedSpace)).presheaf,
              ((Z.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback i).obj E))).obj (G)))
          (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ G hEpc hG) +
        (n : ℤ) * @eulerCharacteristic k _ Z (i ≫ f) hproper
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z.toRingedSpace)).presheaf,
              ((Z.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback i).obj V))).obj (G)))
          (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ G hVpc hG) := by
    by_cases hc : topologicalKrullDim Z = 1
    · have hcurve : IsCurve k (i ≫ f) :=
        @isCurve_of_topologicalKrullDim_eq_one k _ Z (i ≫ f) ‹_› hproper hc
      exact @eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_isCurve k _ Z (i ≫ f) hcurve
        hproper _ _ G n m hEp hVp hG _ _ _
    · have h0 : topologicalKrullDim Z ≤ 0 :=
        StacksTag09NX.le_zero_of_lt_one (lt_of_le_of_ne hdimZ hc)
      have hsupp : topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0 :=
        le_trans Topology.IsInducing.subtypeVal.topologicalKrullDim_le h0
      exact @eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_supp_le_zero k _ Z (i ≫ f)
        hproper _ _ G n m hEp hVp hG hsupp _ _ _
  have t4 : @eulerCharacteristic k _ X f _ ((Scheme.Modules.pushforward i).obj G) hF =
      @eulerCharacteristic k _ Z (i ≫ f) hproper G hG :=
    eulerCharacteristic_pushforward_of_isClosedImmersion k i f G hG hF
  have t2 : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (((Scheme.Modules.pushforward i).obj G))))
            hEF =
      @eulerCharacteristic k _ Z (i ≫ f) hproper
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z.toRingedSpace)).presheaf,
            ((Z.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback i).obj E))).obj (G)))
        (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ G hEpc hG) :=
    (@eulerCharacteristic_tensorSheaf_comm k _ X f _ E ((Scheme.Modules.pushforward i).obj G)
        hEc hF).trans
      ((eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion k i f G E hG hEc hF
          hEpc).trans
        (@eulerCharacteristic_tensorSheaf_comm k _ Z (i ≫ f) hproper G
          ((Scheme.Modules.pullback i).obj E) hG hEpc))
  have t3 : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (((Scheme.Modules.pushforward i).obj G))))
            hVF =
      @eulerCharacteristic k _ Z (i ≫ f) hproper
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z.toRingedSpace)).presheaf,
            ((Z.toRingedSpace)).IsSheaf⟩).obj (((Scheme.Modules.pullback i).obj V))).obj (G)))
        (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ G hVpc hG) :=
    (@eulerCharacteristic_tensorSheaf_comm k _ X f _ V ((Scheme.Modules.pushforward i).obj G)
        hVc hF).trans
      ((eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion k i f G V hG hVc hF
          hVpc).trans
        (@eulerCharacteristic_tensorSheaf_comm k _ Z (i ≫ f) hproper G
          ((Scheme.Modules.pullback i).obj V) hG hVpc))
  have t1 : @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj
            (((Scheme.Modules.pushforward i).obj G)))) hEVF =
      @eulerCharacteristic k _ Z (i ≫ f) hproper
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z.toRingedSpace)).presheaf,
            ((Z.toRingedSpace)).IsSheaf⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩).obj
            (((Scheme.Modules.pullback i).obj E))).obj (((Scheme.Modules.pullback i).obj V)))))).obj
            (G)))
        (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ G
          (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ _ hEpc hVpc) hG) :=
    (@eulerCharacteristic_tensorSheaf_comm k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V)))
          ((Scheme.Modules.pushforward i).obj G) hEVc hF).trans
      ((eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion k i f G
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
                ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) hG hEVc
            hF hEVpc).trans
        ((@eulerCharacteristic_tensorSheaf_comm k _ Z (i ≫ f) hproper G
              ((Scheme.Modules.pullback i).obj
                ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
                    ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))
              hG hEVpc).trans
          (@eulerCharacteristic_eq_of_iso k _ Z (i ≫ f) hproper _ _
            (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ G hEVpc hG)
            (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ G
              (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ _ hEpc hVpc) hG)
            (Stacks.Tag01VSPullbackTensor.tensorSheafMapIso
              (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso i E V) (Iso.refl G)))))
  rwa [t1, t2, t3, t4]

/-- **The tensor Euler identity for every coherent module**, on a proper scheme of dimension at
most one over a field:

`χ((ℰ ⊗ 𝒱) ⊗ ℱ) + nm·χ(ℱ) = m·χ(ℰ ⊗ ℱ) + n·χ(𝒱 ⊗ ℱ)`. -/
@[sga "6 X 4.4" "special case"]
theorem eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_isCoherent (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdimX : topologicalKrullDim X ≤ 1) (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m]
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F)
    (hEF : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))))
    (hVF : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (F))))
    (hEVF : SheafOfModules.IsCoherent
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj (F)))) :
    @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj
              (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj (F)))
          hEVF +
        ((n * m : ℕ) : ℤ) * @eulerCharacteristic k _ X f _ F hF =
      (m : ℤ) * @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F))) hEF +
        (n : ℤ) * @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (F))) hVF := by
  have hXN : IsNoetherian X :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k f
  have hXLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let hEV : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m
  obtain ⟨hEc, hVc, hEVc⟩ := isCoherent_and_isCoherent_and_isCoherent_tensorSheaf X E V n m
  refine Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent X
    (fun F' => ∀ (hF' : _root_.SheafOfModules.IsCoherent F')
      (hEF' : _root_.SheafOfModules.IsCoherent
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F'))))
      (hVF' : _root_.SheafOfModules.IsCoherent
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (F'))))
      (hEVF' : _root_.SheafOfModules.IsCoherent
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))))).obj
            (F')))),
      @eulerCharacteristic k _ X f _
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
                ((X.toRingedSpace)).IsSheaf⟩).obj (((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
                (V))))).obj (F')))
            hEVF' +
          ((n * m : ℕ) : ℤ) * @eulerCharacteristic k _ X f _ F' hF' =
        (m : ℤ) * @eulerCharacteristic k _ X f _
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
                ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F'))) hEF' +
          (n : ℤ) * @eulerCharacteristic k _ X f _
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
                ((X.toRingedSpace)).IsSheaf⟩).obj (V)).obj (F'))) hVF')
    ?_ ?_ ?_ F hF hF hEF hVF hEVF
  · intro hF' hEF' hVF' hEVF'
    have hz : IsZero (⊤_ X.Modules) := IsTerminal.isZero terminalIsTerminal
    have hzero : ∀ (W : X.Modules) (hW : SheafOfModules.IsCoherent
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (W)).obj ((⊤_ X.Modules))))),
        @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (W)).obj ((⊤_ X.Modules)))) hW = 0 := by
      intro W hW
      refine eulerCharacteristic_eq_zero_of_isZero k f _ hW (IsZero.of_iso ?_
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace W
          (⊤_ X.Modules)))
      have := Stacks.SheafOfModules.TensorLocalProperties.preservesZeroMorphisms_tensorSheafLeft
        (Opens.grothendieckTopology ↥X) X.sheaf W
      exact (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
        (Opens.grothendieckTopology ↥X) X.sheaf W).map_isZero hz
    rw [hzero _ hEF', hzero _ hVF', hzero _ hEVF',
      eulerCharacteristic_eq_zero_of_isZero k f _ hF' hz]
    ring
  · intro S hS h1 h2 h3 hP1 hP3 hF' hEF' hVF' hEVF'
    have a1 := @eulerCharacteristic_tensorSheaf_add_of_shortExact_of_isProper k _ X f _
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m) hEV
      S hS h1 h2 h3
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₁ hEVc h1)
      hEVF'
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₃ hEVc h3)
    have a2 := @eulerCharacteristic_tensorSheaf_add_of_shortExact_of_isProper k _ X f _ E n ‹_›
      S hS h1 h2 h3
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₁ hEc h1) hEF'
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₃ hEc h3)
    have a3 := @eulerCharacteristic_tensorSheaf_add_of_shortExact_of_isProper k _ X f _ V m ‹_›
      S hS h1 h2 h3
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₁ hVc h1) hVF'
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₃ hVc h3)
    have a4 : @eulerCharacteristic k _ X f _ S.X₂ hF' =
        @eulerCharacteristic k _ X f _ S.X₁ h1 + @eulerCharacteristic k _ X f _ S.X₃ h3 :=
      @eulerCharacteristic_add_of_shortExact_of_finiteDimensional k _ X f _ _ hS h1 hF' h3
        (forall_finiteDimensional_cohomologyOverField_of_isProper k f _ h1)
        (forall_finiteDimensional_cohomologyOverField_of_isProper k f _ h3)
    have e1 := hP1 h1
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₁ hEc h1)
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₁ hVc h1)
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₁ hEVc h1)
    have e3 := hP3 h3
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₃ hEc h3)
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₃ hVc h3)
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ S.X₃ hEVc h3)
    rw [a1, a2, a3, a4]
    linarith [e1, e3]
  · intro Z i hi hZint I hI hF' hEF' hVF' hEVF'
    have hZLN : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    have hmono : Mono I.ι := SheafOfModules.Submodule.instMonoι I
    have hGc : _root_.SheafOfModules.IsCoherent I.toSheafOfModules :=
      @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono Z hZLN
        (SheafOfModules.unit Z.ringCatSheaf) I.toSheafOfModules
        (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z) hI I.ι hmono
    exact eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_pushforward k f hdimX E V n m i
      I.toSheafOfModules hGc hF' hEF' hVF' hEVF'

/-! ### [Stacks, Tag 0AYX] -/

/-- For `ℰ` and `𝒱` finite locally free of constant ranks `n` and `m` on a scheme `X` proper of
dimension at most one over a field `k`,

`deg(ℰ ⊗ 𝒱) = m · deg(ℰ) + n · deg(𝒱)`. -/
@[stacks 0AYX]
theorem curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E V : X.Modules) (n m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V m] :
    @curveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m)
        (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m) =
      (m : ℤ) * curveDegree k f hdim E n + (n : ℤ) * curveDegree k f hdim V m := by
  let hEV : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (V))) (n * m) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E V n m
  have hXLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hO : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  obtain ⟨hEc, hVc, hEVc⟩ := isCoherent_and_isCoherent_and_isCoherent_tensorSheaf X E V n m
  have key := eulerCharacteristic_tensorSheaf_tensorSheaf_add_of_isCoherent k f hdim E V n m
    (SheafOfModules.unit X.ringCatSheaf) hO
    (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace E _ hEc hO)
    (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace V _ hVc hO)
    (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ _ hEVc hO)
  rw [@eulerCharacteristic_tensor_unit k _ X f _ E hEc hO,
    @eulerCharacteristic_tensor_unit k _ X f _ V hVc hO,
    @eulerCharacteristic_tensor_unit k _ X f _ _ hEVc hO] at key
  rw [@curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim _ (n * m) hEV hEVc hO,
    @curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim E n ‹_› hEc hO,
    @curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim V m ‹_› hVc hO]
  push_cast at key ⊢
  linarith [key]

end AlgebraicGeometry

end
