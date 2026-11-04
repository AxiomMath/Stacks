module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseRankCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModuleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear

/-!
# The surjection `π_*ℐᵃ ⊗ π_*ℐᵇ ⟶ π_*ℐ^(a+b)` and quotients of finite locally free modules

Let `π : Y ⟶ X` be an affine morphism of algebraic spaces and `ℐ ⊆ 𝒪_Y` a quasi-coherent sheaf of
ideals.  The proof of Stacks 0GV0 uses that the multiplication

`π_*ℐ ⊗_{𝒪_X} π_*(ℐⁿ) ⟶ π_*(ℐ^(n+1))`

is surjective, so that a surjection `ℰ ⟶ π_*ℐ` from a finite locally free `ℰ` propagates to
surjections `ℰ^{⊗ n} ⟶ π_*(ℐⁿ)` for all `n ≥ 1`.  This file proves that, in the form: if
`π_*(ℐᵃ)` and `π_*(ℐᵇ)` are quotients of finite locally free modules then so is `π_*(ℐ^(a+b))`.

## Main definitions

* `AlgebraicGeometry.Space.idealSheafPowChartPushforward`: `π_*(ℐⁿ)` in the base-change spelling
  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, whose sections over an étale chart
  `U` of `X` are the sections of `ℐⁿ` over the chart `U ×_X Y`.
* `AlgebraicGeometry.Space.chartPowMul`: the product of a section of `π_*(ℐᵃ)` and one of
  `π_*(ℐᵇ)`, a section of `π_*(ℐ^(a+b))`.
* `AlgebraicGeometry.Space.chartPowTensorHom`: for `p : ℰ ⟶ π_*(ℐᵃ)` and `q : ℰ' ⟶ π_*(ℐᵇ)`, the
  morphism `ℰ ⊗ ℰ' ⟶ π_*(ℐ^(a+b))`, `e ⊗ e' ↦ p(e) q(e')`, out of the tensor product sheaf.

## Main results

* `AlgebraicGeometry.Space.epi_chartPowTensorHom`: **`ℰ ⊗ ℰ' ⟶ π_*(ℐ^(a+b))` is an
  epimorphism when `p` and `q` are.**
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_epi_idealSheafPowPushforward_add`:
  quotients of finite locally free modules onto `π_*(ℐᵃ)` and `π_*(ℐᵇ)` give one onto
  `π_*(ℐ^(a+b))`.
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_epi_idealSheafPowPushforward_of_one`:
  if `π_*ℐ` is a quotient of a finite locally free module, so is every `π_*(ℐⁿ)`, `n ≥ 1`.

## Implementation notes

**Surjectivity is checked over affine charts.**  A section of `π_*(ℐ^(a+b))` over an affine
étale chart `U` of `X` is a function on the affine chart `U ×_X Y` lying in `I^(a+b)`, with
`I = ℐ(U ×_X Y)` — that is the computation of the sections of a power of a quasi-coherent ideal
over an affine chart,
`AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_pow_chartSectionIdeal_smul_top`,
the chart `U ×_X Y` being affine because `π` is
(`AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`).
So it is a finite sum of products `x w` with `x ∈ Iᵃ`, `w ∈ Iᵇ`; each factor lifts along `p`,
resp. `q`, locally on `U`, and on the common refinement the product is the image of `e ⊗ e'`.
The local image of a morphism of sheaves of modules is a sheaf of submodules
(`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule`), so the sum lies in it, and the affine
charts generate a covering sieve.  It matters that the localization happens on `X`: a section of
`ℐ^(a+b)` over `U ×_X Y` is locally a sum of products only on a covering of `U ×_X Y`, which need
not come from a covering of `U`; on an affine chart no localization is needed at all.

**No tensor product of epimorphisms.**  The morphism `ℰ ⊗ ℰ' ⟶ π_*(ℐ^(a+b))` is built directly
from the bilinear map `(e, e') ↦ p(e) q(e')` on sections, through the universal property of the
sheafified tensor product (`Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom`), rather than
as the multiplication precomposed with `p ⊗ q`; so its surjectivity needs only the local lifts
along `p` and `q`, and not that a tensor product of epimorphisms is one.

## References

* [Stacks Project, Tag 0GV0](https://stacks.math.columbia.edu/tag/0GV0), the surjection
  `π_*ℐ ⊗ π_*ℐⁿ ⟶ π_*ℐ^(n+1)` of its proof.
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6), part (2): a tensor
  product of finite locally free modules is finite locally free.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)

/-- The direct image `f_*(ℐⁿ)` along small-chart base change. -/
abbrev idealSheafPowChartPushforward (n : ℕ) : Modules.{u, u} B S hS X.1 X.2 :=
  (smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj
    (SheafOfModules.idealSheafPow I n).toSheafOfModules

/-- The value in `𝒪_Y` of a section of `f_*(ℐⁿ)`. -/
abbrev chartPowVal {n : ℕ} {V : SmallEtale B S hS X.1}
    (x : (idealSheafPowChartPushforward B S hS f hf I n).val.obj (op V)) :
    chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS f hf).obj V) :=
  (show ↥((SheafOfModules.idealSheafPow I n).obj (op ((smallBaseChange B S hS f hf).obj V)))
    from x).1

/-- The product of sections of `f_*(ℐᵃ)` and `f_*(ℐᵇ)`, a section of `f_*(ℐ^(a+b))`. -/
def chartPowMul {a b : ℕ} {V : SmallEtale B S hS X.1}
    (x : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op V))
    (y : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op V)) :
    (idealSheafPowChartPushforward B S hS f hf I (a + b)).val.obj (op V) :=
  (⟨chartPowVal B S hS f hf I x * chartPowVal B S hS f hf I y,
    mul_mem_idealAt_idealSheafPow_add B S hS Y I a b
      (show ↥((SheafOfModules.idealSheafPow I a).obj (op ((smallBaseChange B S hS f hf).obj V)))
        from x).2
      (show ↥((SheafOfModules.idealSheafPow I b).obj (op ((smallBaseChange B S hS f hf).obj V)))
        from y).2⟩ :
    ↥((SheafOfModules.idealSheafPow I (a + b)).obj (op ((smallBaseChange B S hS f hf).obj V))))

/-- The value of the product of two sections is the product of their values. -/
theorem chartPowVal_chartPowMul {a b : ℕ} {V : SmallEtale B S hS X.1}
    (x : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op V))
    (y : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op V)) :
    chartPowVal B S hS f hf I (chartPowMul B S hS f hf I x y) =
      chartPowVal B S hS f hf I x * chartPowVal B S hS f hf I y := rfl

/-- The value of a sum of sections of `f_*(ℐⁿ)` is the sum of their values. -/
theorem chartPowVal_add {n : ℕ} {V : SmallEtale B S hS X.1}
    (x y : (idealSheafPowChartPushforward B S hS f hf I n).val.obj (op V)) :
    chartPowVal B S hS f hf I (x + y) =
      chartPowVal B S hS f hf I x + chartPowVal B S hS f hf I y := rfl

/-- The value of `r • x` is the image of `r` in the functions on the chart times the value of
`x`. -/
theorem chartPowVal_smul {n : ℕ} {V : SmallEtale B S hS X.1}
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      (op V))
    (x : (idealSheafPowChartPushforward B S hS f hf I n).val.obj (op V)) :
    chartPowVal B S hS f hf I (r • x) =
      (show chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS f hf).obj V) from
        ((smallBaseChangeSharp B S hS f hf).hom.app (op V)).hom r) *
        chartPowVal B S hS f hf I x := rfl

/-- The value of the restriction of a section of `f_*(ℐⁿ)` along `g : W ⟶ V` is the restriction
of its value along the base change of `g`. -/
theorem chartPowVal_map {n : ℕ} {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (x : (idealSheafPowChartPushforward B S hS f hf I n).val.obj (op V)) :
    chartPowVal B S hS f hf I (n := n) (V := W)
        (show (idealSheafPowChartPushforward B S hS f hf I n).val.obj (op W) from
          ((idealSheafPowChartPushforward B S hS f hf I n).val.map g.op).hom x) =
      chartRestrict ((smallBaseChange B S hS f hf).map g) (chartPowVal B S hS f hf I x) :=
  rfl

/-- A section of `f_*(ℐⁿ)` is determined by its value. -/
theorem chartPowVal_injective {n : ℕ} {V : SmallEtale B S hS X.1} :
    Function.Injective (chartPowVal B S hS f hf I (n := n) (V := V)) :=
  fun _ _ h => Subtype.ext h

/-- The section of `f_*(ℐⁿ)` given by a function lying in `ℐⁿ`. -/
abbrev chartPowMk {n : ℕ} {V : SmallEtale B S hS X.1}
    (z : chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS f hf).obj V))
    (hz : z ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I n)
      (op ((smallBaseChange B S hS f hf).obj V))) :
    (idealSheafPowChartPushforward B S hS f hf I n).val.obj (op V) :=
  (⟨z, hz⟩ : ↥((SheafOfModules.idealSheafPow I n).obj (op ((smallBaseChange B S hS f hf).obj V))))

/-- The value of a section of `f_*(ℐⁿ)` lies in `ℐⁿ`. -/
theorem chartPowVal_mem {n : ℕ} {V : SmallEtale B S hS X.1}
    (x : (idealSheafPowChartPushforward B S hS f hf I n).val.obj (op V)) :
    chartPowVal B S hS f hf I x ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I n)
      (op ((smallBaseChange B S hS f hf).obj V)) :=
  (show ↥((SheafOfModules.idealSheafPow I n).obj (op ((smallBaseChange B S hS f hf).obj V)))
    from x).2

/-- The section of `f_*(ℐⁿ)` given by the value of `x` is `x`. -/
theorem chartPowMk_chartPowVal {n : ℕ} {V : SmallEtale B S hS X.1}
    (x : (idealSheafPowChartPushforward B S hS f hf I n).val.obj (op V)) :
    chartPowMk B S hS f hf I (chartPowVal B S hS f hf I x) (chartPowVal_mem B S hS f hf I x) = x :=
  rfl

/-! ### The product is bilinear -/

/-- The product of sections is additive in the first factor. -/
theorem chartPowMul_add_left {a b : ℕ} {V : SmallEtale B S hS X.1}
    (x x' : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op V))
    (y : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op V)) :
    chartPowMul B S hS f hf I (x + x') y =
      chartPowMul B S hS f hf I x y + chartPowMul B S hS f hf I x' y :=
  chartPowVal_injective B S hS f hf I
    (add_mul (R := chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS f hf).obj V)) _ _ _)

/-- The product of sections is additive in the second factor. -/
theorem chartPowMul_add_right {a b : ℕ} {V : SmallEtale B S hS X.1}
    (x : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op V))
    (y y' : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op V)) :
    chartPowMul B S hS f hf I x (y + y') =
      chartPowMul B S hS f hf I x y + chartPowMul B S hS f hf I x y' :=
  chartPowVal_injective B S hS f hf I
    (mul_add (R := chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS f hf).obj V)) _ _ _)

/-- The product of sections commutes with scalars in the first factor. -/
theorem chartPowMul_smul_left {a b : ℕ} {V : SmallEtale B S hS X.1}
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      (op V))
    (x : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op V))
    (y : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op V)) :
    chartPowMul B S hS f hf I (r • x) y = r • chartPowMul B S hS f hf I x y :=
  chartPowVal_injective B S hS f hf I
    (mul_assoc (G := chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS f hf).obj V)) _ _ _)

/-- The product of sections commutes with scalars in the second factor. -/
theorem chartPowMul_smul_right {a b : ℕ} {V : SmallEtale B S hS X.1}
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      (op V))
    (x : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op V))
    (y : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op V)) :
    chartPowMul B S hS f hf I x (r • y) = r • chartPowMul B S hS f hf I x y := by
  refine chartPowVal_injective B S hS f hf I ?_
  show chartPowVal B S hS f hf I x * (_ * chartPowVal B S hS f hf I y) =
    _ * (chartPowVal B S hS f hf I x * chartPowVal B S hS f hf I y)
  exact mul_left_comm
    (G := chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS f hf).obj V)) _ _ _

/-- The product of sections commutes with restriction along `g : W ⟶ V`. -/
theorem chartPowMul_map {a b : ℕ} {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (x : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op V))
    (y : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op V))
    (x' : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op W))
    (y' : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op W))
    (hx : x' = ((idealSheafPowChartPushforward B S hS f hf I a).val.map g.op).hom x)
    (hy : y' = ((idealSheafPowChartPushforward B S hS f hf I b).val.map g.op).hom y) :
    chartPowMul B S hS f hf I x' y' =
      ((idealSheafPowChartPushforward B S hS f hf I (a + b)).val.map g.op).hom
        (chartPowMul B S hS f hf I x y) := by
  subst hx hy
  exact Subtype.ext (map_mul (chartRestrict ((smallBaseChange B S hS f hf).map g))
    (chartPowVal B S hS f hf I x) (chartPowVal B S hS f hf I y)).symm

/-! ### The product morphism out of a tensor product -/

variable {B S hS f hf I}

section TensorHom

variable {E E' : Modules.{u, u} B S hS X.1 X.2} {a b : ℕ}
    (p : E ⟶ idealSheafPowChartPushforward B S hS f hf I a)
    (q : E' ⟶ idealSheafPowChartPushforward B S hS f hf I b)

/-- The multiplication `f_*(ℐᵃ) ⊗ f_*(ℐᵇ) ⟶ f_*(ℐ^(a+b))` of presheaves of modules. -/
def chartPowMulPresheafHom (a b : ℕ) :
    (idealSheafPowChartPushforward B S hS f hf I a).val ⊗
        (idealSheafPowChartPushforward B S hS f hf I b).val ⟶
      (idealSheafPowChartPushforward B S hS f hf I (a + b)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun x y => chartPowMul B S hS f hf I (V := U.unop) x y)
    (fun x₁ x₂ y => chartPowMul_add_left B S hS f hf I x₁ x₂ y)
    (fun (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U) x y =>
      chartPowMul_smul_left B S hS f hf I r x y)
    (fun x y₁ y₂ => chartPowMul_add_right B S hS f hf I x y₁ y₂)
    (fun (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U) x y =>
      chartPowMul_smul_right B S hS f hf I r x y)
  naturality {_ _} g := ModuleCat.MonoidalCategory.tensor_ext fun x y =>
    chartPowMul_map B S hS f hf I g.unop x y _ _ rfl rfl

/-- The morphism `E ⊗ E' ⟶ f_*(ℐ^(a+b))` of presheaves of modules, `e ⊗ e' ↦ p(e) q(e')`. -/
def chartPowTensorPresheafHom :
    E.val ⊗ E'.val ⟶ (idealSheafPowChartPushforward B S hS f hf I (a + b)).val :=
  (p.val ⊗ₘ q.val) ≫ chartPowMulPresheafHom (f := f) (hf := hf) (I := I) a b

/-- **The product morphism** `E ⊗ E' ⟶ f_*(ℐ^(a+b))` out of the tensor product sheaf,
`e ⊗ e' ↦ p(e) q(e')`. -/
def chartPowTensorHom :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
      E).obj E' ⟶ idealSheafPowChartPushforward B S hS f hf I (a + b) :=
  Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom.symm (chartPowTensorPresheafHom p q)

/-- **Every product `p(e) q(e')` of sections is a value of the product morphism.** -/
theorem exists_chartPowTensorHom_app_eq (U : (SmallEtale B S hS X.1)ᵒᵖ) (e : E.val.obj U)
    (e' : E'.val.obj U) :
    ∃ z : (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj E).obj E').val.obj U,
      (chartPowTensorHom p q).val.app U z =
        chartPowMul B S hS f hf I (V := U.unop) (p.val.app U e) (q.val.app U e') := by
  have h := congrArg (fun φ => φ.app U (e ⊗ₜ[(smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj U] e'))
    (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj) (chartPowTensorHom p q))
  refine ⟨_, h.symm.trans ?_⟩
  have h2 : PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj) (chartPowTensorHom p q) =
      chartPowTensorPresheafHom p q :=
    Equiv.apply_symm_apply Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom _
  simp only [h2]
  rfl

end TensorHom

section Epi

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModulesPowProduct
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

variable {E E' : Modules.{u, u} B S hS X.1 X.2} {a b : ℕ}
    (p : E ⟶ idealSheafPowChartPushforward B S hS f hf I a)
    (q : E' ⟶ idealSheafPowChartPushforward B S hS f hf I b)

/-- A product of two sections lies locally in the image of the product morphism. -/
theorem chartPowMul_mem_imageSubmodule [Epi p] [Epi q] {V : SmallEtale B S hS X.1}
    (x : (idealSheafPowChartPushforward B S hS f hf I a).val.obj (op V))
    (y : (idealSheafPowChartPushforward B S hS f hf I b).val.obj (op V)) :
    chartPowMul B S hS f hf I x y ∈
      (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (chartPowTensorHom p q)).obj (op V) := by
  obtain ⟨S1, hS1, h1⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi p x
  obtain ⟨S2, hS2, h2⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi q y
  refine (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (chartPowTensorHom p q)).isSheaf _ ?_
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    ((SmallEtale.topology B S hS X.1).intersection_covering hS1 hS2)
  rintro W k ⟨hk1, hk2⟩
  obtain ⟨e, he⟩ := h1 k hk1
  obtain ⟨e', he'⟩ := h2 k hk2
  obtain ⟨z, hz⟩ := exists_chartPowTensorHom_app_eq p q (op W) e e'
  have he₁ : p.val.app (op W) e =
      ((idealSheafPowChartPushforward B S hS f hf I a).val.map k.op).hom x := he
  have he₂ : q.val.app (op W) e' =
      ((idealSheafPowChartPushforward B S hS f hf I b).val.map k.op).hom y := he'
  show ((idealSheafPowChartPushforward B S hS f hf I (a + b)).val.map k.op).hom
      (chartPowMul B S hS f hf I x y) ∈ _
  rw [← chartPowMul_map B S hS f hf I k x y _ _ he₁ he₂]
  have hmem := Stacks.SheafOfModules.ImageSubsheaf.apply_mem_imageSubmodule
    (chartPowTensorHom p q) z
  rw [hz] at hmem
  exact hmem

/-- **Over an affine chart every section of `f_*(ℐ^(a+b))` lies in the image of the product
morphism.**  Its value is a function on the affine chart `V ×_X Y` lying in `I^(a+b) = Iᵃ Iᵇ`,
`I` the ideal of sections there, so it is a finite sum of products. -/
theorem mem_imageSubmodule_chartPowTensorHom_of_isAffine [Epi p] [Epi q]
    (haff : IsAffineHom B S hS f.hom) (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    {V : SmallEtale B S hS X.1}
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (z : (idealSheafPowChartPushforward B S hS f hf I (a + b)).val.obj (op V)) :
    z ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (chartPowTensorHom p q)).obj
      (op V) := by
  have hW := isAffine_smallBaseChange_obj B S hS f hf haff V hV
  have hEq := chartSubmodule_idealPowSubmodule_eq_pow_chartSectionIdeal_smul_top B S hS Y.1 Y.2 I
    (a + b) (SheafOfModules.unit (structureRingSheaf B S hS Y))
    (isCartesianOnAffineCharts_unit (hF := Y.2))
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 I.toSheafOfModules hI)
    ((smallBaseChange B S hS f hf).obj V) hW
  replace hEq := (congrArg (fun N => N.obj (op ((smallBaseChange B S hS f hf).obj V)))
    (idealSheafPow_eq_idealPowSubmodule B S hS Y I (a + b))).trans hEq
  have hz := chartPowVal_mem B S hS f hf I z
  change chartPowVal B S hS f hf I z ∈ (SheafOfModules.idealSheafPow I (a + b)).obj
    (op ((smallBaseChange B S hS f hf).obj V)) at hz
  rw [hEq] at hz
  have hmemPow : ∀ t, t ∈ chartSectionIdeal B S hS Y.1 Y.2 I
      ((smallBaseChange B S hS f hf).obj V) ^ (a + b) • ⊤ →
      t ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I (a + b))
        (op ((smallBaseChange B S hS f hf).obj V)) := fun t ht => by
    show t ∈ (SheafOfModules.idealSheafPow I (a + b)).obj
      (op ((smallBaseChange B S hS f hf).obj V))
    rw [hEq]
    exact ht
  suffices H : ∀ s : (idealSheafPowChartPushforward B S hS f hf I (a + b)).val.obj (op V),
      chartPowVal B S hS f hf I s = chartPowVal B S hS f hf I z →
      s ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (chartPowTensorHom p q)).obj
        (op V) from H z rfl
  generalize chartPowVal B S hS f hf I z = w at hz ⊢
  induction hz using Submodule.smul_induction_on' with
  | smul r hr m _ =>
    let m' : chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS f hf).obj V) := m
    rw [pow_add] at hr
    have hmul : ∀ t ∈ chartSectionIdeal B S hS Y.1 Y.2 I ((smallBaseChange B S hS f hf).obj V) ^ a *
        chartSectionIdeal B S hS Y.1 Y.2 I ((smallBaseChange B S hS f hf).obj V) ^ b,
        t * m' ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I (a + b))
          (op ((smallBaseChange B S hS f hf).obj V)) :=
      fun t ht => SheafOfModules.mem_idealSheafPow_of_mem_pow I (a + b)
        (show t * m' ∈ chartSectionIdeal B S hS Y.1 Y.2 I
            ((smallBaseChange B S hS f hf).obj V) ^ (a + b) by
          rw [pow_add]
          exact Ideal.mul_mem_right m' _ ht)
    induction hr using Submodule.mul_induction_on' with
    | mem_mul_mem x hx w hw =>
      intro s hs
      have hx1 : x ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I a)
          (op ((smallBaseChange B S hS f hf).obj V)) :=
        SheafOfModules.mem_idealSheafPow_of_mem_pow I a hx
      have hw1 : w * m' ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I b)
          (op ((smallBaseChange B S hS f hf).obj V)) :=
        SheafOfModules.mem_idealSheafPow_of_mem_pow I b
          (show w * m' ∈ chartSectionIdeal B S hS Y.1 Y.2 I
            ((smallBaseChange B S hS f hf).obj V) ^ b from Ideal.mul_mem_right m' _ hw)
      obtain rfl : s = chartPowMul B S hS f hf I (chartPowMk B S hS f hf I (V := V) x hx1)
          (chartPowMk B S hS f hf I (V := V) (w * m') hw1) :=
        chartPowVal_injective B S hS f hf I (hs.trans (mul_assoc x w m'))
      exact chartPowMul_mem_imageSubmodule p q _ _
    | add x hx y hy Cx Cy =>
      intro s hs
      obtain rfl : s = chartPowMk B S hS f hf I (V := V) (x * m') (hmul x hx) +
          chartPowMk B S hS f hf I (V := V) (y * m') (hmul y hy) :=
        chartPowVal_injective B S hS f hf I (hs.trans (add_mul x y m'))
      exact Submodule.add_mem _ (Cx _ rfl) (Cy _ rfl)
  | add x hx y hy Cx Cy =>
    intro s hs
    obtain rfl : s = chartPowMk B S hS f hf I (V := V) x (hmemPow x hx) +
        chartPowMk B S hS f hf I (V := V) y (hmemPow y hy) :=
      chartPowVal_injective B S hS f hf I hs
    exact Submodule.add_mem _ (Cx _ rfl) (Cy _ rfl)

/-- **The product morphism `E ⊗ E' ⟶ f_*(ℐ^(a+b))` is an epimorphism** when `p` and `q` are, for
an affine `f` and a quasi-coherent `ℐ`.  Every section of `f_*(ℐ^(a+b))` lies in the image over
every affine chart, by
`AlgebraicGeometry.Space.mem_imageSubmodule_chartPowTensorHom_of_isAffine`, and the affine charts
generate a covering sieve. -/
theorem epi_chartPowTensorHom [Epi p] [Epi q] (haff : IsAffineHom B S hS f.hom)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) : Epi (chartPowTensorHom p q) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {V} y => ?_⟩
  have hmem : y ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
      (chartPowTensorHom p q)).obj (op V) := by
    refine (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule _).isSheaf y ?_
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_
      (affineChartSieve_mem_topology B S hS X.1 V)
    exact (Sieve.generate_le_iff _ _).2 fun W k hW =>
      mem_imageSubmodule_chartPowTensorHom_of_isAffine p q haff hI hW _
  exact (SmallEtale.topology B S hS X.1).superset_covering (fun W g hg => hg) hmem

end Epi

/-! ### Quotients of finite locally free modules -/

section FiniteLocallyFree

variable (B S hS)

/-- An epimorphism composed with the forward map of an isomorphism is an epimorphism. -/
private theorem epi_comp_hom_of_iso {C : Type (u + 1)} [Category.{u + 1} C] {X Y Z : C}
    (p : X ⟶ Y) [Epi p] (i : Y ≅ Z) : Epi (p ≫ i.hom) :=
  inferInstance

/-- **If `π_*(ℐᵃ)` and `π_*(ℐᵇ)` are quotients of finite locally free modules, so is
`π_*(ℐ^(a+b))`**, for an affine morphism `π : Y ⟶ X` of algebraic spaces and a quasi-coherent
sheaf of ideals `ℐ ⊆ 𝒪_Y`.

If `E ⟶ π_*(ℐᵃ)` and `E' ⟶ π_*(ℐᵇ)` are surjective, then so is `E ⊗ E' ⟶ π_*(ℐ^(a+b))`,
`e ⊗ e' ↦ p(e) q(e')` (`AlgebraicGeometry.Space.epi_chartPowTensorHom`), and `E ⊗ E'` is finite
locally free (Stacks 03L6 (2)).  This is the surjection
`π_*ℐ ⊗_{𝒪_X} π_*ℐⁿ ⟶ π_*ℐ^(n+1)` of the proof of Stacks 0GV0, composed with the given
surjections. -/
theorem exists_isFiniteLocallyFreeOnSite_epi_idealSheafPowPushforward_add (π : Y ⟶ X)
    (haff : IsAffineHom B S hS π.hom)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) {a b : ℕ}
    (ha : ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ idealSheafPowPushforward B S hS π I a), Epi p)
    (hb : ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ idealSheafPowPushforward B S hS π I b), Epi p) :
    ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ idealSheafPowPushforward B S hS π I (a + b)), Epi p := by
  obtain ⟨E, hE, p, hp⟩ := ha
  obtain ⟨E', hE', q, hq⟩ := hb
  have hf := relativelyRepresentable_of_isAffineHom B S hS π haff
  let e := fun n : ℕ => (modulePushforwardChartIso B S hS π hf).app
    (SheafOfModules.idealSheafPow I n).toSheafOfModules
  have := epi_comp_hom_of_iso p (e a)
  have := epi_comp_hom_of_iso q (e b)
  let _ := (smallEtaleRingedSite B S hS X.1 X.2).hasSheafCompose_forget₂_ringCat
  exact ⟨_, Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite
    (smallEtaleRingedSite B S hS X.1 X.2) E E' hE hE',
    chartPowTensorHom (p ≫ (e a).hom) (q ≫ (e b).hom) ≫ (e (a + b)).inv,
    @epi_comp_hom_of_iso _ _ _ _ _ _
      (epi_chartPowTensorHom (p ≫ (e a).hom) (q ≫ (e b).hom) haff hI) (e (a + b)).symm⟩

/-- **If `π_*ℐ` is a quotient of a finite locally free module, so is every `π_*(ℐⁿ)`, `n ≥ 1`**,
for an affine morphism `π : Y ⟶ X` of algebraic spaces and a quasi-coherent sheaf of ideals
`ℐ ⊆ 𝒪_Y`.  A surjection `ℰ ⟶ π_*ℐ` propagates to surjections `ℰ^{⊗ n} ⟶ π_*(ℐⁿ)` through the
surjections `π_*ℐ ⊗ π_*ℐⁿ ⟶ π_*ℐ^(n+1)`; this is the second paragraph of the proof of
Stacks 0GV0. -/
theorem exists_isFiniteLocallyFreeOnSite_epi_idealSheafPowPushforward_of_one (π : Y ⟶ X)
    (haff : IsAffineHom B S hS π.hom)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (h1 : ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ (modulePushforward B S hS π).obj I.toSheafOfModules), Epi p) :
    ∀ n : ℕ, 0 < n → ∃ (E : Modules.{u, u} B S hS X.1 X.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ idealSheafPowPushforward B S hS π I n), Epi p := by
  have hone : ∃ (E : Modules.{u, u} B S hS X.1 X.2)
      (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ idealSheafPowPushforward B S hS π I 1), Epi p := by
    obtain ⟨E, hE, p, hp⟩ := h1
    exact ⟨E, hE, p ≫ eqToHom (idealSheafPowPushforward_one B S hS π I).symm,
      epi_comp_hom_of_iso p (eqToIso (idealSheafPowPushforward_one B S hS π I).symm)⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hone
  | succ n _ ih =>
    exact exists_isFiniteLocallyFreeOnSite_epi_idealSheafPowPushforward_add B S hS π haff I hI ih
      hone

end FiniteLocallyFree

end AlgebraicGeometry.Space

end
