module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushTransitionNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeAdjunction

/-!
# Products of sections along an affine direct image, as maps out of a tensor product

Let `π : Y ⟶ X` be a representable morphism of algebraic spaces over a scheme `S`, and write `π_*`
for the direct image of modules along small-chart base change
(`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`), whose sections over an étale chart
`V` of `X` are the sections over the base-changed chart `V ×_X Y`.  A family of
`𝒪_Y`-bilinear maps `β : ℳ₁(W) × ℳ₂(W) ⟶ ℳ₃(W)` compatible with restriction gives a morphism

`π_*ℳ₁ ⊗_{𝒪_X} π_*ℳ₂ ⟶ π_*ℳ₃`

out of the tensor product of `𝒪_X`-modules (`Stacks.SheafOfModules.Tensor.sheafTensor`): on pure
tensors of sections over `V` it is `β` over `V ×_X Y`.  When `π` is affine and the images of `β`
span the sections of `ℳ₃` over every affine chart, this morphism is an **epimorphism**.

The two instances used for Stacks 0GV1 are the products of sections of powers of a sheaf of
ideals `ℐ ⊆ 𝒪_Y`,

* `π_*ℐ ⊗ π_*ℐⁿ ⟶ π_*ℐⁿ⁺¹`, the step of the proof of Stacks 0GV0 by which a surjection onto
  `π_*ℐ` from a finite locally free module produces surjections onto every `π_*ℐⁿ`, and
* `π_*ℐᵃ ⊗ π_*𝒬 ⟶ π_*(ℐᵃ𝒬)`, the action of `ℐᵃ` on a quasi-coherent module `𝒬`.

Both are epimorphisms for an affine `π` and quasi-coherent data, because over an affine chart the
sections of `ℐⁿ𝒬` are `ℐ(U)ⁿ · 𝒬(U)`
(`AlgebraicGeometry.Space.chartSubmodule_idealPowSubmodule_eq_of_isAffine`).

## Main definitions

* `AlgebraicGeometry.Space.modulesTensor`: the tensor product of `𝒪_X`-modules, as the sheaf
  tensor product.
* `AlgebraicGeometry.Space.pushforwardTensorPairing`: the morphism induced by `β`.
* `AlgebraicGeometry.Space.idealSheafPowMulPairing` and
  `AlgebraicGeometry.Space.idealPowSmulPairing`: the two instances.

## Main results

* `AlgebraicGeometry.Space.epi_pushforwardTensorPairing`: the epimorphism criterion.
* `AlgebraicGeometry.Space.epi_idealSheafPowMulPairing` and
  `AlgebraicGeometry.Space.epi_idealPowSmulPairing`.
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_epi_bcPushforward_idealSheafPow`: a
  surjection onto `π_*ℐ` from a finite locally free module gives one onto every `π_*ℐⁿ`, `n ≥ 1`.

## References

* [Stacks Project, Tag 0GV0](https://stacks.math.columbia.edu/tag/0GV0)
* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The tensor product of `𝒪_X`-modules**, as the sheafification of the objectwise tensor
product (`Stacks.SheafOfModules.Tensor.sheafTensor`). -/
abbrev modulesTensor (X : AlgebraicSpaces B S hS) (M N : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS X.1 X.2 :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).obj N

variable {X Y : AlgebraicSpaces B S hS} (π : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable π.hom)

/-- The direct image `π_*ℳ` along small-chart base change, read as an `𝒪_X`-module. -/
abbrev bcPushforward (M : Modules.{u, u} B S hS Y.1 Y.2) : Modules.{u, u} B S hS X.1 X.2 :=
  (smallBaseChangeModulePushforward.{u, u} B S hS π hrep).obj M

/-- The structure map `𝒪_X(V) ⟶ 𝒪_Y(V ×_X Y)` of small-chart base change on sections. -/
abbrev bcSharp (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      V) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj
      (op ((smallBaseChange B S hS π hrep).obj V.unop)) :=
  ((smallBaseChangeSharp B S hS π hrep).hom.app V).hom r

/-- A section of `π_*ℳ` over `V`, read as a section of `ℳ` over `V ×_X Y`. -/
abbrev bcSection {M : Modules.{u, u} B S hS Y.1 Y.2} {V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ}
    (x : (bcPushforward B S hS π hrep M).val.obj V) :
    M.val.obj (op ((smallBaseChange B S hS π hrep).obj V.unop)) := x

/-- A section of `ℳ` over `V ×_X Y`, read as a section of `π_*ℳ` over `V`. -/
abbrev bcSectionInv {M : Modules.{u, u} B S hS Y.1 Y.2}
    {V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ}
    (x : M.val.obj (op ((smallBaseChange B S hS π hrep).obj V.unop))) :
    (bcPushforward B S hS π hrep M).val.obj V := x

/-- The sheafification adjunction for `𝒪_X`-modules, with its right adjoint the forgetful
functor on the nose (the restriction of scalars along the identity in
`PresheafOfModules.sheafificationAdjunction` is the identity definitionally). -/
def modulesSheafifyForgetAdjunction (X : AlgebraicSpaces B S hS) :
    PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj) ⊣
      SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)

section Pairing

variable (M₁ M₂ M₃ : Modules.{u, u} B S hS Y.1 Y.2)
    (β : ∀ W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ,
      M₁.val.obj W → M₂.val.obj W → M₃.val.obj W)
    (add_left : ∀ W x x' y, β W (x + x') y = β W x y + β W x' y)
    (smul_left : ∀ W (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W) x y,
      β W (r • x) y = r • β W x y)
    (add_right : ∀ W x y y', β W x (y + y') = β W x y + β W x y')
    (smul_right : ∀ W (r : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W) x y,
      β W x (r • y) = r • β W x y)
    (naturality : ∀ ⦃W W' : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ⦄ (f : W ⟶ W') x y,
      M₃.val.restrictₛₗ f (β W x y) =
        β W' (M₁.val.restrictₛₗ f x) (M₂.val.restrictₛₗ f y))

/-- The presheaf-level pairing `π_*ℳ₁ ⊗ π_*ℳ₂ ⟶ π_*ℳ₃` before sheafification. -/
def pushforwardPresheafTensorPairing :
    PresheafOfModules.tensorObj (O := (smallEtaleRingedSite B S hS X.1 X.2).O.obj)
        (bcPushforward B S hS π hrep M₁).val (bcPushforward B S hS π hrep M₂).val ⟶
      (bcPushforward B S hS π hrep M₃).val :=
  PresheafOfModules.tensorMk
    (fun V x y => bcSectionInv B S hS π hrep (β (op ((smallBaseChange B S hS π hrep).obj V.unop))
      (bcSection B S hS π hrep x) (bcSection B S hS π hrep y)))
    (fun _ _ _ _ => add_left _ _ _ _)
    (fun V r _ _ => smul_left _ (bcSharp B S hS π hrep V r) _ _)
    (fun _ _ _ _ => add_right _ _ _ _)
    (fun V r _ _ => smul_right _ (bcSharp B S hS π hrep V r) _ _)
    (fun _ _ f _ _ => naturality ((smallBaseChange B S hS π hrep).map f.unop).op _ _)

/-- The presheaf-level pairing sends `x ⊗ₜ y` to the image of `β x y` under the base-change
identification of sections. -/
theorem pushforwardPresheafTensorPairing_tmul (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ)
    (x : (bcPushforward B S hS π hrep M₁).val.obj V)
    (y : (bcPushforward B S hS π hrep M₂).val.obj V) :
    PresheafOfModules.Hom.app (pushforwardPresheafTensorPairing B S hS π hrep M₁ M₂ M₃ β add_left
      smul_left add_right smul_right naturality) V (x ⊗ₜ y) =
      bcSectionInv B S hS π hrep (β (op ((smallBaseChange B S hS π hrep).obj V.unop))
        (bcSection B S hS π hrep x) (bcSection B S hS π hrep y)) :=
  PresheafOfModules.tensorMk_tmul _ _ _ _ _ _ _ _ _

/-- **The pairing `π_*ℳ₁ ⊗ π_*ℳ₂ ⟶ π_*ℳ₃`** induced by a family of bilinear maps of sections
compatible with restriction: the presheaf-level pairing extended across sheafification. -/
def pushforwardTensorPairing :
    modulesTensor B S hS X (bcPushforward B S hS π hrep M₁) (bcPushforward B S hS π hrep M₂) ⟶
      bcPushforward B S hS π hrep M₃ :=
  ((modulesSheafifyForgetAdjunction B S hS X).homEquiv _ _).symm
    (pushforwardPresheafTensorPairing B S hS π hrep M₁ M₂ M₃ β add_left smul_left add_right
      smul_right naturality)

/-- The pairing is the presheaf-level pairing after the unit of sheafification. -/
theorem sheafificationUnit_comp_pushforwardTensorPairing :
    (modulesSheafifyForgetAdjunction B S hS X).unit.app _ ≫
      (pushforwardTensorPairing B S hS π hrep M₁ M₂ M₃ β add_left smul_left add_right smul_right
        naturality).val =
    pushforwardPresheafTensorPairing B S hS π hrep M₁ M₂ M₃ β add_left smul_left add_right
      smul_right naturality :=
  ((modulesSheafifyForgetAdjunction B S hS X).homEquiv_unit _ _ _).symm.trans
    (((modulesSheafifyForgetAdjunction B S hS X).homEquiv _ _).apply_symm_apply _)

/-- **The pairing is an epimorphism once every section of `ℳ₃` over the base change of every
affine étale chart of `X` is a finite sum of values of `β`.**

A morphism `d` killing the pairing kills every value of `β` over such a chart, those values being
the images of pure tensors under the unit of sheafification; so `d` vanishes on the sections over
the affine charts, which cover every chart, and the target of `d` is separated. -/
theorem epi_pushforwardTensorPairing
    (hspan : ∀ V : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
        ∀ z : M₃.val.obj (op ((smallBaseChange B S hS π hrep).obj V)),
          z ∈ AddSubmonoid.closure {w | ∃ x y, w = β (op ((smallBaseChange B S hS π hrep).obj V))
            x y}) :
    Epi (pushforwardTensorPairing B S hS π hrep M₁ M₂ M₃ β add_left smul_left add_right
      smul_right naturality) := by
  refine Preadditive.epi_of_cancel_zero _ fun {Z} d hd => ?_
  have key : ∀ (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ)
      (t : (PresheafOfModules.tensorObj (O := (smallEtaleRingedSite B S hS X.1 X.2).O.obj)
        (bcPushforward B S hS π hrep M₁).val (bcPushforward B S hS π hrep M₂).val).obj V),
      (d.val.app V).hom (PresheafOfModules.Hom.app (pushforwardPresheafTensorPairing B S hS π
        hrep M₁ M₂ M₃ β add_left smul_left add_right smul_right naturality) V t) = 0 := by
    intro V t
    rw [← sheafificationUnit_comp_pushforwardTensorPairing]
    have h2 := congrArg (fun ψ => (ψ.val.app V).hom
      ((((modulesSheafifyForgetAdjunction B S hS X).unit.app _).app V).hom t)) hd
    exact h2
  -- `d` vanishes on the sections over affine charts
  have haff : ∀ (V : SmallEtale B S hS X.1),
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
        ∀ z : (bcPushforward B S hS π hrep M₃).val.obj (op V), (d.val.app (op V)).hom z = 0 := by
    intro V hV z
    have hmem := hspan V hV (bcSection B S hS π hrep z)
    show (d.val.app (op V)).hom (bcSectionInv B S hS π hrep (bcSection B S hS π hrep z)) = 0
    generalize bcSection B S hS π hrep z = z' at hmem ⊢
    induction hmem using AddSubmonoid.closure_induction with
    | mem w hw =>
      obtain ⟨x, y, rfl⟩ := hw
      have := key (op V) ((bcSectionInv B S hS π hrep x) ⊗ₜ (bcSectionInv B S hS π hrep y))
      rwa [pushforwardPresheafTensorPairing_tmul] at this
    | zero => exact map_zero _
    | add w w' _ _ hw hw' =>
      exact (map_add (d.val.app (op V)).hom (bcSectionInv B S hS π hrep w)
        (bcSectionInv B S hS π hrep w')).trans (by rw [hw, hw', add_zero])
  refine Stacks.SheafOfModules.hom_ext_val_app_apply fun W z => ?_
  obtain ⟨I, Yc, a, hYaff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X.1 W.unop
  refine Stacks.SheafOfModules.val_app_eq_of_isSeparated d 0 z hcov fun T f hf => ?_
  obtain ⟨j, g, rfl⟩ := Sieve.mem_ofArrows_iff _ _ _ |>.1 hf
  have e1 := chartRestrictLinear_comp (bcPushforward B S hS π hrep M₃) (a j) g z
  have h0 : (d.val.app (op (Yc j))).hom (chartRestrictLinear (bcPushforward B S hS π hrep M₃) (a j)
      z) = 0 := haff (Yc j) (hYaff j) _
  have h1 : (d.val.app (op T)).hom (chartRestrictLinear (bcPushforward B S hS π hrep M₃) (g ≫ a j)
      z) = 0 := by
    rw [e1]
    show (d.val.app (op T)).hom (((bcPushforward B S hS π hrep M₃).val.map g.op).hom
      (chartRestrictLinear (bcPushforward B S hS π hrep M₃) (a j) z)) = 0
    rw [PresheafOfModules.naturality_apply, h0]
    exact map_zero _
  exact h1.trans rfl

end Pairing


/-! ### Products of sections of powers of a sheaf of ideals -/

section IdealPowers

variable (I : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).Submodule)

/-- The sections of `ℐⁿ` over an affine chart are the `n`-th power of the ideal of sections of
`ℐ`, for a quasi-coherent sheaf of ideals `ℐ`. -/
theorem idealSheafPow_obj_eq_pow_smul_top_of_isAffine
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (n : ℕ) {W : SmallEtale B S hS Y.1} (hW : IsAffine (chartScheme W)) :
    (SheafOfModules.idealSheafPow I n).obj (op W) =
      chartSectionIdeal B S hS Y.1 Y.2 I W ^ n •
        (⊤ : Submodule (chartRing B S hS Y.1 Y.2 W) ((SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O)).val.obj (op W))) := by
  have h1 : SheafOfModules.idealSheafPow I n =
      idealPowSubmodule I n (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)) :=
    Eq.trans (idealSheafPow_eq_idealPow B S hS Y I n)
      (Stacks.Sites.idealSmul_top_eq.{u, u + 1, u} _).symm
  rw [h1]
  exact chartSubmodule_idealPowSubmodule_eq_of_isAffine B S hS Y.1 Y.2 I
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _
      (SheafOfModules.isQuasicoherentOnSite_unit _))
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hI) n hW


/-- A section of the unit module of `𝒪_Y`, read as a section of the ring `𝒪_Y`. -/
abbrev unitSectionToRing {W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ}
    (x : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).val.obj W) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W :=
  x

/-- A section of `ℐᵃ` times a section of `𝒬` is a section of `ℐᵃ𝒬`. -/
theorem smul_mem_idealPowSubmodule_of_mem_idealSheafPow (a : ℕ) (Q : Modules.{u, u} B S hS Y.1 Y.2)
    {W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ}
    {r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W}
    (hr : r ∈ (SheafOfModules.idealSheafPow I a).obj W) (q : Q.val.obj W) :
    r • q ∈ (idealPowSubmodule I a Q).obj W := by
  have h := idealSheafPow_eq_idealPow B S hS Y I a
  have hr' : r ∈ (Stacks.Sites.idealPow I a).obj W := h ▸ hr
  exact Stacks.Sites.smul_mem_idealSmul _ hr' (Stacks.SheafOfModules.mem_top_obj q)

/-- A section of the sheaf of modules attached to a submodule, read as an element of the
submodule of sections. -/
abbrev submoduleSection {M : Modules.{u, u} B S hS Y.1 Y.2} {N : M.Submodule}
    {W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ} (x : N.toSheafOfModules.val.obj W) :
    N.obj W :=
  x

/-- The ring element underlying a section of `ℐᵃ`. -/
abbrev idealPowSectionVal (a : ℕ) {W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ}
    (x : (SheafOfModules.idealSheafPow I a).toSheafOfModules.val.obj W) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj W :=
  unitSectionToRing B S hS (submoduleSection B S hS x).1

/-- The action `ℐᵃ(W) × 𝒬(W) ⟶ (ℐᵃ𝒬)(W)`. -/
def idealPowSmulSection (a : ℕ) (Q : Modules.{u, u} B S hS Y.1 Y.2)
    (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
    (r : (SheafOfModules.idealSheafPow I a).toSheafOfModules.val.obj W) (q : Q.val.obj W) :
    (idealPowModule I a Q).val.obj W :=
  ⟨idealPowSectionVal B S hS I a r • q,
    smul_mem_idealPowSubmodule_of_mem_idealSheafPow B S hS I a Q
      (submoduleSection B S hS r).2 q⟩

/-- The underlying section of `idealPowSmulSection r q` is `r • q`. -/
theorem idealPowSmulSection_val (a : ℕ) (Q : Modules.{u, u} B S hS Y.1 Y.2)
    (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
    (r : (SheafOfModules.idealSheafPow I a).toSheafOfModules.val.obj W) (q : Q.val.obj W) :
    (submoduleSection B S hS (idealPowSmulSection B S hS I a Q W r q)).1 =
      idealPowSectionVal B S hS I a r • q := rfl

variable {I} in
/-- Two sections of `ℐᵃ𝒬` are equal if their underlying sections of `𝒬` are equal. -/
theorem idealPowSmulSection_ext {a : ℕ} {Q : Modules.{u, u} B S hS Y.1 Y.2}
    {W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ} {z z' : (idealPowModule I a Q).val.obj W}
    (h : (submoduleSection B S hS z).1 = (submoduleSection B S hS z').1) : z = z' :=
  Subtype.ext h

/-- Sections of the `k`-th power of the ideal of chart sections lie in `ℐᵏ`. -/
private theorem mem_idealSheafPow_of_mem_pow_chartSectionIdeal (k : ℕ)
    (V : SmallEtale B S hS Y.1)
    {ρ : (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj (op V)}
    (hρ : ρ ∈ chartSectionIdeal B S hS Y.1 Y.2 I V ^ k) :
    ρ ∈ (SheafOfModules.idealSheafPow I k).obj (op V) :=
  idealSheafPow_eq_idealPow B S hS Y I k ▸
    pow_chartSectionIdeal_le_chartIdealPow B S hS Y.1 Y.2 I k V hρ

/-- **The action `π_*ℐᵃ ⊗ π_*𝒬 ⟶ π_*(ℐᵃ𝒬)`.** -/
def idealPowSmulPairing (a : ℕ) (Q : Modules.{u, u} B S hS Y.1 Y.2) :
    modulesTensor B S hS X
        (bcPushforward B S hS π hrep (SheafOfModules.idealSheafPow I a).toSheafOfModules)
        (bcPushforward B S hS π hrep Q) ⟶
      bcPushforward B S hS π hrep (idealPowModule I a Q) :=
  pushforwardTensorPairing B S hS π hrep _ _ _ (idealPowSmulSection B S hS I a Q)
    (fun W x x' y => idealPowSmulSection_ext B S hS (add_smul _ _ _))
    (fun W r x y => idealPowSmulSection_ext B S hS (mul_smul _ _ _))
    (fun W x y y' => idealPowSmulSection_ext B S hS (smul_add _ _ _))
    (fun W r x y => idealPowSmulSection_ext B S hS (by
      change idealPowSectionVal B S hS I a x • r • y = r • idealPowSectionVal B S hS I a x • y
      rw [← mul_smul, ← mul_smul]
      exact congrArg (· • y) (structureRingSheaf_mul_comm B S hS Y W _ _)))
    (fun W W' f x y => idealPowSmulSection_ext B S hS (Q.val.map_smul f _ _))

/-- **The action `π_*ℐᵃ ⊗ π_*𝒬 ⟶ π_*(ℐᵃ𝒬)` is an epimorphism** for an affine `π`, a
quasi-coherent sheaf of ideals `ℐ` and a quasi-coherent `𝒬`: over an affine chart the sections of
`ℐᵃ𝒬` are `ℐ(U)ᵃ · 𝒬(U)`. -/
theorem epi_idealPowSmulPairing (hπ : IsAffineHom B S hS π.hom)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) (a : ℕ) (Q : Modules.{u, u} B S hS Y.1 Y.2)
    (hQ : Q.IsQuasicoherentOnSite) :
    Epi (idealPowSmulPairing B S hS π hrep I a Q) := by
  refine epi_pushforwardTensorPairing B S hS π hrep _ _ _ _ _ _ _ _ _ fun V hV z => ?_
  have hV' : IsAffine (chartScheme ((smallBaseChange B S hS π hrep).obj V)) :=
    isAffine_smallBaseChange_obj B S hS π hrep hπ V hV
  have h2 := chartSubmodule_idealPowSubmodule_eq_of_isAffine B S hS Y.1 Y.2 I Q
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hQ)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hI) a hV'
  have hz : (submoduleSection B S hS z).1 ∈ chartSectionIdeal B S hS Y.1 Y.2 I
      ((smallBaseChange B S hS π hrep).obj V) ^ a •
        (⊤ : Submodule (chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS π hrep).obj V))
          (Q.val.obj (op ((smallBaseChange B S hS π hrep).obj V)))) := by
    rw [← h2]
    exact (submoduleSection B S hS z).2
  have key : ∀ (m : Q.val.obj (op ((smallBaseChange B S hS π hrep).obj V)))
      (hm : m ∈ chartSectionIdeal B S hS Y.1 Y.2 I ((smallBaseChange B S hS π hrep).obj V) ^ a •
        (⊤ : Submodule (chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS π hrep).obj V))
          (Q.val.obj (op ((smallBaseChange B S hS π hrep).obj V))))),
      (⟨m, (show m ∈ chartSubmodule B S hS Y.1 Y.2 (idealPowSubmodule I a Q)
          ((smallBaseChange B S hS π hrep).obj V) by rw [h2]; exact hm)⟩ :
        (idealPowSubmodule I a Q).obj (op ((smallBaseChange B S hS π hrep).obj V)))
        ∈ AddSubmonoid.closure {w | ∃ x y, w = idealPowSmulSection B S hS I a Q
          (op ((smallBaseChange B S hS π hrep).obj V)) x y} := by
    intro m hm
    induction hm using Submodule.smul_induction_on' with
    | smul ρ hρ q hq =>
      exact AddSubmonoid.subset_closure
        ⟨⟨ρ, mem_idealSheafPow_of_mem_pow_chartSectionIdeal B S hS I a _ hρ⟩, q, rfl⟩
    | add m₁ hm₁ m₂ hm₂ ih₁ ih₂ =>
      exact AddSubmonoid.add_mem _ ih₁ ih₂
  exact key _ hz

/-- The product `ℐⁿ(W) × ℐᵐ(W) ⟶ ℐⁿ⁺ᵐ(W)`. -/
def idealSheafPowMulSection (n m : ℕ) (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
    (x : (SheafOfModules.idealSheafPow I n).toSheafOfModules.val.obj W)
    (y : (SheafOfModules.idealSheafPow I m).toSheafOfModules.val.obj W) :
    (SheafOfModules.idealSheafPow I (n + m)).toSheafOfModules.val.obj W :=
  ⟨idealPowSectionVal B S hS I n x • (submoduleSection B S hS y).1,
    mul_mem_idealAt_idealSheafPow_add B S hS Y I n m (submoduleSection B S hS x).2
      (submoduleSection B S hS y).2⟩

variable {I} in
/-- Two sections of `ℐⁿ` are equal if their underlying sections of the structure sheaf are
equal. -/
theorem idealSheafPowSection_ext {n : ℕ} {W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ}
    {z z' : (SheafOfModules.idealSheafPow I n).toSheafOfModules.val.obj W}
    (h : (submoduleSection B S hS z).1 = (submoduleSection B S hS z').1) : z = z' :=
  Subtype.ext h

/-- **The product `π_*ℐⁿ ⊗ π_*ℐᵐ ⟶ π_*ℐⁿ⁺ᵐ`.** -/
def idealSheafPowMulPairing (n m : ℕ) :
    modulesTensor B S hS X
        (bcPushforward B S hS π hrep (SheafOfModules.idealSheafPow I n).toSheafOfModules)
        (bcPushforward B S hS π hrep (SheafOfModules.idealSheafPow I m).toSheafOfModules) ⟶
      bcPushforward B S hS π hrep (SheafOfModules.idealSheafPow I (n + m)).toSheafOfModules :=
  pushforwardTensorPairing B S hS π hrep _ _ _ (idealSheafPowMulSection B S hS I n m)
    (fun W x x' y => idealSheafPowSection_ext B S hS (add_smul _ _ _))
    (fun W r x y => idealSheafPowSection_ext B S hS (mul_smul _ _ _))
    (fun W x y y' => idealSheafPowSection_ext B S hS (smul_add _ _ _))
    (fun W r x y => idealSheafPowSection_ext B S hS (by
      change idealPowSectionVal B S hS I n x • r • (submoduleSection B S hS y).1 =
        r • idealPowSectionVal B S hS I n x • (submoduleSection B S hS y).1
      rw [← mul_smul, ← mul_smul]
      exact congrArg (· • (submoduleSection B S hS y).1)
        (structureRingSheaf_mul_comm B S hS Y W _ _)))
    (fun W W' f x y => idealSheafPowSection_ext B S hS
      ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).val.map_smul f _ _))

/-- **The product `π_*ℐⁿ ⊗ π_*ℐᵐ ⟶ π_*ℐⁿ⁺ᵐ` is an epimorphism** for an affine `π` and a
quasi-coherent `ℐ`: over an affine chart the sections of `ℐᵏ` are `ℐ(U)ᵏ`. -/
theorem epi_idealSheafPowMulPairing (hπ : IsAffineHom B S hS π.hom)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) (n m : ℕ) :
    Epi (idealSheafPowMulPairing B S hS π hrep I n m) := by
  refine epi_pushforwardTensorPairing B S hS π hrep _ _ _ (idealSheafPowMulSection B S hS I n m)
    _ _ _ _ _ fun V hV z => ?_
  have hV' : IsAffine (chartScheme ((smallBaseChange B S hS π hrep).obj V)) :=
    isAffine_smallBaseChange_obj B S hS π hrep hπ V hV
  have hmem : ∀ k (w : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).val.obj
        (op ((smallBaseChange B S hS π hrep).obj V))),
      w ∈ chartSectionIdeal B S hS Y.1 Y.2 I ((smallBaseChange B S hS π hrep).obj V) ^ k •
        (⊤ : Submodule (chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS π hrep).obj V)) _) →
      w ∈ (SheafOfModules.idealSheafPow I k).obj (op ((smallBaseChange B S hS π hrep).obj V)) := by
    intro k w hw
    rw [idealSheafPow_obj_eq_pow_smul_top_of_isAffine B S hS I hI k hV']
    exact hw
  have key2 : ∀ ρ ∈ chartSectionIdeal B S hS Y.1 Y.2 I ((smallBaseChange B S hS π hrep).obj V) ^ n *
      chartSectionIdeal B S hS Y.1 Y.2 I ((smallBaseChange B S hS π hrep).obj V) ^ m,
      ∀ (q : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).val.obj
          (op ((smallBaseChange B S hS π hrep).obj V)))
        (h : ρ • q ∈ (SheafOfModules.idealSheafPow I (n + m)).obj
          (op ((smallBaseChange B S hS π hrep).obj V))),
      (⟨ρ • q, h⟩ : (SheafOfModules.idealSheafPow I (n + m)).toSheafOfModules.val.obj
          (op ((smallBaseChange B S hS π hrep).obj V))) ∈
        AddSubmonoid.closure {w | ∃ x y, w = idealSheafPowMulSection B S hS I n m
          (op ((smallBaseChange B S hS π hrep).obj V)) x y} := by
    intro ρ hρ q
    induction hρ using Submodule.mul_induction_on' with
    | mem_mul_mem x hx y hy =>
      intro h
      exact AddSubmonoid.subset_closure
        ⟨⟨x, mem_idealSheafPow_of_mem_pow_chartSectionIdeal B S hS I n _ hx⟩,
        ⟨y • q, hmem m _ (Submodule.smul_mem_smul hy Submodule.mem_top)⟩,
        Subtype.ext (mul_smul x y q)⟩
    | add ρ₁ h₁ ρ₂ h₂ ih₁ ih₂ =>
      intro h
      have h₁' : ρ₁ • q ∈ (SheafOfModules.idealSheafPow I (n + m)).obj
          (op ((smallBaseChange B S hS π hrep).obj V)) :=
        hmem _ _ (Submodule.smul_mem_smul (by rw [pow_add]; exact h₁) Submodule.mem_top)
      have h₂' : ρ₂ • q ∈ (SheafOfModules.idealSheafPow I (n + m)).obj
          (op ((smallBaseChange B S hS π hrep).obj V)) :=
        hmem _ _ (Submodule.smul_mem_smul (by rw [pow_add]; exact h₂) Submodule.mem_top)
      have := AddSubmonoid.add_mem _ (ih₁ h₁') (ih₂ h₂')
      have e : (⟨(ρ₁ + ρ₂) • q, h⟩ :
          (SheafOfModules.idealSheafPow I (n + m)).toSheafOfModules.val.obj
          (op ((smallBaseChange B S hS π hrep).obj V))) =
          (⟨ρ₁ • q, h₁'⟩ : (SheafOfModules.idealSheafPow I (n + m)).toSheafOfModules.val.obj
            (op ((smallBaseChange B S hS π hrep).obj V))) + ⟨ρ₂ • q, h₂'⟩ :=
        idealSheafPowSection_ext B S hS (add_smul ρ₁ ρ₂ q)
      rw [e]
      exact this
  have key : ∀ (w : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).val.obj
        (op ((smallBaseChange B S hS π hrep).obj V)))
      (hw : w ∈ chartSectionIdeal B S hS Y.1 Y.2 I
          ((smallBaseChange B S hS π hrep).obj V) ^ (n + m) •
        (⊤ : Submodule (chartRing B S hS Y.1 Y.2 ((smallBaseChange B S hS π hrep).obj V)) _)),
      (⟨w, hmem _ w hw⟩ : (SheafOfModules.idealSheafPow I (n + m)).toSheafOfModules.val.obj
          (op ((smallBaseChange B S hS π hrep).obj V))) ∈
        AddSubmonoid.closure {w | ∃ x y, w = idealSheafPowMulSection B S hS I n m
          (op ((smallBaseChange B S hS π hrep).obj V)) x y} := by
    intro w hw
    induction hw using Submodule.smul_induction_on' with
    | smul ρ hρ q _ => exact key2 ρ (by rw [← pow_add]; exact hρ) q _
    | add w₁ _ w₂ _ ih₁ ih₂ => exact AddSubmonoid.add_mem _ ih₁ ih₂
  have hz := (SetLike.ext_iff.1 (idealSheafPow_obj_eq_pow_smul_top_of_isAffine B S hS I hI (n + m)
    hV') _).1 (submoduleSection B S hS z).2
  exact key _ hz

/-- **A surjection onto `π_*ℐ` from a finite locally free module gives one onto every `π_*ℐⁿ`,
`n ≥ 1`**, for an affine `π` and a quasi-coherent `ℐ`: this is the step of the proof of
Stacks 0GV0 by which `ℰ^{⊗ n}` surjects onto `π_*ℐⁿ`, the surjection
`π_*ℐⁿ ⊗ π_*ℐ ⟶ π_*ℐⁿ⁺¹` being `AlgebraicGeometry.Space.epi_idealSheafPowMulPairing`. -/
theorem exists_isFiniteLocallyFreeOnSite_epi_bcPushforward_idealSheafPow
    (hπ : IsAffineHom B S hS π.hom) (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (e : E ⟶ bcPushforward B S hS π hrep I.toSheafOfModules) (he : Epi e) (n : ℕ) :
    ∃ (P : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite P)
      (p : P ⟶ bcPushforward B S hS π hrep
        (SheafOfModules.idealSheafPow I (n + 1)).toSheafOfModules),
      Epi p := by
  have h1 : (SheafOfModules.idealSheafPow I 1).toSheafOfModules = I.toSheafOfModules :=
    congrArg SheafOfModules.Submodule.toSheafOfModules (SheafOfModules.idealSheafPow_one I)
  let e' : E ⟶ bcPushforward B S hS π hrep (SheafOfModules.idealSheafPow I 1).toSheafOfModules :=
    e ≫ eqToHom (congrArg (bcPushforward B S hS π hrep) h1.symm)
  have he' : Epi e' := epi_comp _ _
  induction n with
  | zero => exact ⟨E, hE, e', he'⟩
  | succ k ih =>
    obtain ⟨P, hP, p, hp⟩ := ih
    refine ⟨modulesTensor B S hS X P E,
      Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite
        (smallEtaleRingedSite B S hS X.1 X.2) P E hP hE,
      (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
        p).app E ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj _).map e') ≫
        idealSheafPowMulPairing B S hS π hrep I (k + 1) 1, ?_⟩
    have : Epi (idealSheafPowMulPairing B S hS π hrep I (k + 1) 1) :=
      epi_idealSheafPowMulPairing B S hS π hrep I hπ hI (k + 1) 1
    have : PreservesColimitsOfSize.{0, 0}
        (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
          (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).O E) :=
      preservesColimitsOfSize_shrink.{0, u, 0, u} _
    have : PreservesColimitsOfSize.{0, 0}
        (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
          (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).O
          (bcPushforward B S hS π hrep
            (SheafOfModules.idealSheafPow I (k + 1)).toSheafOfModules)) :=
      preservesColimitsOfSize_shrink.{0, u, 0, u} _
    have h₁ : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS X.1 X.2).O).map p).app E) :=
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
        (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).O E).map_epi p
    have h₂ : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj
          (bcPushforward B S hS π hrep
            (SheafOfModules.idealSheafPow I (k + 1)).toSheafOfModules)).map
            e') :=
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
        (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).O
          _).map_epi e'
    exact epi_comp _ _

end IdealPowers


/-! ### Morphisms out of the tensor product, tested on pure tensors -/

section PureTensors

/-- The image of a pure tensor of sections in the tensor product of `𝒪_X`-modules. -/
abbrev modulesTensorTmul {M N : Modules.{u, u} B S hS X.1 X.2}
    {V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ} (x : M.val.obj V) (y : N.val.obj V) :
    (modulesTensor B S hS X M N).val.obj V :=
  (((modulesSheafifyForgetAdjunction B S hS X).unit.app
    (PresheafOfModules.tensorObj (O := (smallEtaleRingedSite B S hS X.1 X.2).O.obj) M.val
      N.val)).app V).hom (x ⊗ₜ y)

/-- **A morphism out of the tensor product of `𝒪_X`-modules vanishing on pure tensors of sections
vanishes.** -/
theorem modulesTensor_hom_eq_zero {M N Z : Modules.{u, u} B S hS X.1 X.2}
    (f : modulesTensor B S hS X M N ⟶ Z)
    (h : ∀ (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
      (f.val.app V).hom (modulesTensorTmul B S hS x y) = 0) : f = 0 := by
  let P := PresheafOfModules.tensorObj (O := (smallEtaleRingedSite B S hS X.1 X.2).O.obj) M.val
    N.val
  have h1 : (modulesSheafifyForgetAdjunction B S hS X).unit.app P ≫ f.val = 0 :=
    PresheafOfModules.tensorObj_hom_ext fun V x y => (h V x y).trans rfl
  have h0 : (modulesSheafifyForgetAdjunction B S hS X).unit.app P ≫
      (SheafOfModules.forget _).map (0 : (PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj)).obj
          P ⟶ Z) = 0 := by
    rw [Functor.map_zero, comp_zero]
  have h3 : (modulesSheafifyForgetAdjunction B S hS X).homEquiv P Z f =
      (modulesSheafifyForgetAdjunction B S hS X).homEquiv P Z 0 :=
    ((modulesSheafifyForgetAdjunction B S hS X).homEquiv_unit P Z f).trans
      (h1.trans (((modulesSheafifyForgetAdjunction B S hS X).homEquiv_unit P Z 0).trans h0).symm)
  exact ((modulesSheafifyForgetAdjunction B S hS X).homEquiv P Z).injective h3

/-- **Tensoring a morphism on the right, on pure tensors.** -/
theorem tensorSheafRight_map_tmul (A : Modules.{u, u} B S hS X.1 X.2)
    {M N : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ) (x : A.val.obj V) (y : M.val.obj V) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
        A).map g).val.app V).hom (modulesTensorTmul B S hS x y) =
      modulesTensorTmul B S hS x ((g.val.app V).hom y) := by
  have h := congrArg (fun φ : PresheafOfModules.tensorObj
      (O := (smallEtaleRingedSite B S hS X.1 X.2).O.obj) A.val M.val ⟶ _ =>
        (PresheafOfModules.Hom.app φ V).hom (x ⊗ₜ y))
    ((modulesSheafifyForgetAdjunction B S hS X).unit.naturality
      (PresheafOfModules.tensorHom (𝟙 A.val) g.val))
  exact h.symm

/-- The pairing on pure tensors of sections. -/
theorem pushforwardTensorPairing_tmul {M₁ M₂ M₃ : Modules.{u, u} B S hS Y.1 Y.2}
    (β : ∀ W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ,
      M₁.val.obj W → M₂.val.obj W → M₃.val.obj W)
    (add_left smul_left add_right smul_right naturality)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ)
    (x : (bcPushforward B S hS π hrep M₁).val.obj V)
    (y : (bcPushforward B S hS π hrep M₂).val.obj V) :
    ((pushforwardTensorPairing B S hS π hrep M₁ M₂ M₃ β add_left smul_left add_right smul_right
        naturality).val.app V).hom (modulesTensorTmul B S hS x y) =
      bcSectionInv B S hS π hrep (β (op ((smallBaseChange B S hS π hrep).obj V.unop))
        (bcSection B S hS π hrep x) (bcSection B S hS π hrep y)) := by
  have h := congrArg (fun φ : PresheafOfModules.tensorObj
      (O := (smallEtaleRingedSite B S hS X.1 X.2).O.obj) (bcPushforward B S hS π hrep M₁).val
        (bcPushforward B S hS π hrep M₂).val ⟶ _ => (PresheafOfModules.Hom.app φ V).hom (x ⊗ₜ y))
    (sheafificationUnit_comp_pushforwardTensorPairing B S hS π hrep M₁ M₂ M₃ β add_left smul_left
      add_right smul_right naturality)
  exact h.trans (pushforwardPresheafTensorPairing_tmul B S hS π hrep M₁ M₂ M₃ β add_left smul_left
    add_right smul_right naturality V x y)

end PureTensors

end AlgebraicGeometry.Space

end
