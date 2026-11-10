module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsPresheafCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelSheafData
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineTripleOverlap
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianSheafCondition

/-!
# Descent for a presheaf quotient of cartesian modules on the small étale site

Let `F` be an algebraic space, let `a : K ⟶ P` be a morphism of `𝒪_F`-modules on the small étale
site of `F`, and let `π : P.val ⟶ C` exhibit a presheaf of modules `C` as the cokernel of `a`
computed object by object.  This file proves that `C` satisfies the sheaf condition for a finite
family of affine étale charts covering an affine chart flatly in schemes, provided `K` and `P` are
cartesian on affine charts.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isPullback_toScheme_of_isPullback_charts` and
  `AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback_charts`: **the fibre product of two
  affine étale charts over an affine étale chart is again affine**, for charts rather than for
  objects of a slice.
* `AlgebraicGeometry.Space.SmallEtale.faithfullyFlat_pi_chartRing`: **the product of the rings of
  sections of the members of a finite family of affine charts covering an affine chart flatly in
  schemes is faithfully flat over the ring of sections of the chart covered.**
* `AlgebraicGeometry.Space.SmallEtale.exists_tensorEquiv_chartRing_of_isPullback`: **the ring of
  sections over a fibre product of two affine charts over an affine chart is the tensor product of
  the rings of sections of the two factors.**
* `AlgebraicGeometry.Space.isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian`: **the sheaf
  condition for a presheaf quotient of modules cartesian on affine charts, for a finite family
  of affine charts covering an affine chart flatly in schemes.**

## Implementation notes

The descent is `Stacks.Sites.isSheafFor_of_finite_tensor_descent`, which takes all of the
identifications as data; the cartesian condition is therefore needed only at the arrows of the
covering family and at the arrows out of the pairwise fibre products, and never at a morphism
between non-affine charts, where it is false.  That is why
`Stacks.PresheafOfModules.isSheafFor_of_cartesian`, which asks for the cartesian condition at
*every* arrow of the site, is not what is applied.

The ring of sections of the structure sheaf of the small étale ringed site over a chart *is* the
ring of global functions on its underlying scheme, and `AlgebraicGeometry.Space.chartRestrict`
*is* the induced map of global functions; but the first spelling reaches the second only through
the projections of `AlgebraicGeometry.Space.smallEtaleRingedSite` and
`CategoryTheory.forget₂ CommRingCat RingCat`, which instance search does not unfold.  So the two
geometric inputs are restated here in the spelling the sections of a module carry — faithful
flatness of the product of the rings of the members and the tensor identification of the ring of
an overlap — each proved by introducing the algebra structures in the other spelling, where they
are the hypotheses of the scheme-level statement, and crossing between the two once, in a place
where the elaborator is checking a definitional equality rather than searching for an instance.

No slice of the site occurs.  The descent machinery of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineCokernelDescent` is stated for the slices
`Over V`, and the statement wanted here is about the site itself; the geometric inputs it rests on
are scheme-level and are reused, while the overlaps are taken in the site, where
`AlgebraicGeometry.Space.SmallEtale.instHasPullbacks` provides them.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### Fibre products of charts -/

/-- **A fibre product square of étale charts of `F` maps to a fibre product square of schemes.**
This is `AlgebraicGeometry.Space.SmallEtale.isPullback_toScheme_of_isPullback` for charts rather
than for objects of a slice: both functors to schemes preserve fibre products. -/
theorem SmallEtale.isPullback_toScheme_of_isPullback_charts
    {W Y Z Pb : SmallEtale B S hS F} {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback fst snd f g) :
    IsPullback
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map fst)
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map snd)
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map f)
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map g) :=
  (h.map (SmallEtale.toOver B S hS F)).map (BigFppfOver.toScheme B S hS)

/-- **The fibre product of two affine étale charts of `F` over an affine étale chart is again
affine.**  This is `AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback` for charts rather
than for objects of a slice. -/
theorem SmallEtale.isAffine_of_isPullback_charts
    {W Y Z Pb : SmallEtale B S hS F} {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback fst snd f g)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hY : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Y))
    (hZ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Z)) :
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Pb) := by
  have _ := hW
  have _ := hY
  have _ := hZ
  exact IsAffine.of_isIso (SmallEtale.isPullback_toScheme_of_isPullback_charts h).isoPullback.hom

/-! ### The two geometric inputs, in the spelling of the rings of sections -/

/-- **The product of the rings of sections of the members of a finite family of affine étale
charts covering an affine chart flatly in schemes is faithfully flat over the ring of sections of
the chart covered.**

This is `AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage` restated for
`AlgebraicGeometry.Space.chartRing`, which is the ring of global functions on the underlying
scheme but is not recognized as such by instance search; the algebra structures are
`AlgebraicGeometry.Space.chartAlgebra`, whose `algebraMap` is the induced map of global functions
by `rfl`. -/
theorem SmallEtale.faithfullyFlat_pi_chartRing
    {W : SmallEtale B S hS F} {ι : Type*} [Finite ι] (Y : ι → SmallEtale B S hS F)
    (g : ∀ i, Y i ⟶ W)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hY : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i)))
    (hfppf : Presieve.ofArrows
        (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i))
        (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (g i)) ∈
      Scheme.fppfPrecoverage
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    letI : ∀ i, Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (Y i)) :=
      fun i ↦ chartAlgebra (hF := hF) (g i)
    Module.FaithfullyFlat (chartRing B S hS F hF W)
      (∀ i, chartRing B S hS F hF (Y i)) := by
  have _ := hW
  have _ : ∀ i, IsAffine
    ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i)) := hY
  let : ∀ i, Algebra
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W, ⊤)
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i), ⊤) := fun i ↦
    chartAlgebra (hF := hF) (g i)
  exact AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage
    (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (g i))
    hfppf fun _ ↦ rfl

/-- Restricting along the two sides of a commuting square of charts agrees on the ring of the
corner. -/
private theorem chartRestrict_chartRestrict_eq_of_comp_eq
    {W Y Z Pb : SmallEtale B S hS F} {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : fst ≫ f = snd ≫ g) (c : chartRing B S hS F hF W) :
    chartRestrict (hF := hF) snd (chartRestrict (hF := hF) g c) =
      chartRestrict (hF := hF) (fst ≫ f) c := by
  rw [h]
  exact (RingHom.congr_fun (chartRestrict_comp (hF := hF) g snd) c).symm

/-- **The ring of sections over a fibre product of two affine étale charts over an affine chart is
the tensor product of the rings of sections of the two factors.**

This is `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback` restated for
`AlgebraicGeometry.Space.chartRing`, with the identification given as a linear equivalence over
the ring of the chart covered together with its value on a pure tensor, which is the product of
the two restrictions along the projections. -/
theorem SmallEtale.exists_tensorEquiv_chartRing_of_isPullback
    {W Y Z Pb : SmallEtale B S hS F} {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback fst snd f g)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hY : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Y))
    (hZ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Z)) :
    letI := chartAlgebra (hF := hF) f
    letI := chartAlgebra (hF := hF) g
    letI := chartAlgebra (hF := hF) (fst ≫ f)
    ∃ e : TensorProduct (chartRing B S hS F hF W) (chartRing B S hS F hF Y)
          (chartRing B S hS F hF Z) ≃ₗ[chartRing B S hS F hF W] chartRing B S hS F hF Pb,
      ∀ x y, e (TensorProduct.tmul _ x y) =
        chartRestrict (hF := hF) fst x * chartRestrict (hF := hF) snd y := by
  have _ := hW
  have _ := hY
  have _ := hZ
  have hcfst : ∀ c, chartRestrict (hF := hF) fst (chartRestrict (hF := hF) f c) =
      chartRestrict (hF := hF) (fst ≫ f) c := fun c ↦
    (RingHom.congr_fun (chartRestrict_comp (hF := hF) f fst) c).symm
  let : Algebra
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W, ⊤)
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
    chartAlgebra (hF := hF) f
  let : Algebra
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W, ⊤)
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Z, ⊤) :=
    chartAlgebra (hF := hF) g
  let : Algebra
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W, ⊤)
      Γ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Pb, ⊤) :=
    chartAlgebra (hF := hF) (fst ≫ f)
  exact ⟨(AlgebraicGeometry.algEquivTensorAppTopOfIsPullback
      (SmallEtale.isPullback_toScheme_of_isPullback_charts h) rfl rfl hcfst
      (chartRestrict_chartRestrict_eq_of_comp_eq h.w)).toLinearEquiv,
    fun x y ↦ AlgebraicGeometry.algEquivTensorAppTopOfIsPullback_tmul
      (SmallEtale.isPullback_toScheme_of_isPullback_charts h) rfl rfl hcfst
      (chartRestrict_chartRestrict_eq_of_comp_eq h.w) x y⟩

/-! ### The sheaf condition for a presheaf quotient of cartesian modules -/

/-- A semilinear map compatible with two base-change identifications is the base change of the
ring map, as a map of tensor products. -/
private theorem semilinear_tensorEquiv_eq_map {R A B N M₁ M₂ : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [AddCommGroup N] [Module R N] [AddCommGroup M₁]
    {_ : Module A M₁} [AddCommGroup M₂] {_ : Module B M₂} (l : A →ₐ[R] B)
    (ρ : M₁ →ₛₗ[(l : A →+* B)] M₂) (e₁ : A ⊗[R] N ≃ₗ[A] M₁) (e₂ : B ⊗[R] N ≃ₗ[B] M₂)
    (h : ∀ n, ρ (e₁ (1 ⊗ₜ n)) = e₂ (1 ⊗ₜ n)) (x : A ⊗[R] N) :
    ρ (e₁ x) = e₂ (TensorProduct.map l.toLinearMap LinearMap.id x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c n =>
    rw [TensorProduct.map_tmul, ← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul',
      map_smul, map_smulₛₗ, h, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul]
    simp
  | add x y hx hy => simp [hx, hy]

/-- **The sheaf condition for a presheaf quotient of `𝒪_F`-modules cartesian on affine charts, for
a finite family of affine charts covering an affine chart flatly in schemes.**

Let `a : K ⟶ P` be a morphism of `𝒪_F`-modules with `K` and `P` cartesian on affine charts, and
let `π : P.val ⟶ C` exhibit `C` as the cokernel of `a` computed object by object.  Then `C`
satisfies the sheaf condition for a finite family `g i : Y i ⟶ W` of affine charts whose image in
schemes is an fppf covering family of the affine chart `W`.

The sections of `C` over each member and over each pairwise fibre product are base changes of its
sections over `W`, by
`AlgebraicGeometry.Space.exists_baseChangeEquiv_sections_of_isPresheafCokernel` — the fibre
products being affine by
`AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback_charts`; the ring of an overlap is the
tensor product of the rings of the two members, and the product of the rings of the members is
faithfully flat over the ring of `W`.  Descent of elements along that faithfully flat algebra is
`Stacks.Sites.isSheafFor_of_finite_tensor_descent`. -/
theorem isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian
    {K P : Modules.{u, u} B S hS F hF}
    {C : PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj}
    (a : K ⟶ P) (π : P.val ⟶ C) (hπ : PresheafOfModules.IsPresheafCokernel a.val π)
    (hK : IsCartesianOnAffineCharts K) (hP : IsCartesianOnAffineCharts P)
    {W : SmallEtale B S hS F}
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    {ι : Type*} [Finite ι] (Y : ι → SmallEtale B S hS F) (g : ∀ i, Y i ⟶ W)
    (hY : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i)))
    (hfppf : Presieve.ofArrows
        (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Y i))
        (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (g i)) ∈
      Scheme.fppfPrecoverage
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Presieve.IsSheafFor (C.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u})
      (Presieve.ofArrows Y g) := by
  classical
  obtain ⟨Pb, pr₁, pr₂, hpb⟩ : ∃ (Pb : ι → ι → SmallEtale B S hS F)
      (pr₁ : ∀ i j, Pb i j ⟶ Y i) (pr₂ : ∀ i j, Pb i j ⟶ Y j),
      ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (g i) (g j) :=
    ⟨fun i j ↦ pullback (g i) (g j), fun i j ↦ pullback.fst (g i) (g j),
      fun i j ↦ pullback.snd (g i) (g j), fun i j ↦ IsPullback.of_hasPullback (g i) (g j)⟩
  have hpq : ∀ i j, pr₁ i j ≫ g i = pr₂ i j ≫ g j := fun i j ↦ (hpb i j).w
  have hPbaff : ∀ i j, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Pb i j)) := fun i j ↦
    SmallEtale.isAffine_of_isPullback_charts (hpb i j) hW (hY i) (hY j)
  let algY : ∀ i, Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (Y i)) := fun i ↦
    chartAlgebra (hF := hF) (g i)
  let algPb : ∀ i j, Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (Pb i j)) :=
    fun i j ↦ chartAlgebra (hF := hF) (pr₁ i j ≫ g i)
  let : Module.FaithfullyFlat (chartRing B S hS F hF W)
      (∀ i, chartRing B S hS F hF (Y i)) :=
    SmallEtale.faithfullyFlat_pi_chartRing (hF := hF) Y g hW hY hfppf
  have hu : ∀ (i j : ι) (c : chartRing B S hS F hF W),
      chartRestrict (hF := hF) (pr₁ i j) (chartRestrict (hF := hF) (g i) c) =
        chartRestrict (hF := hF) (pr₁ i j ≫ g i) c := fun i j c ↦
    (RingHom.congr_fun (chartRestrict_comp (hF := hF) (g i) (pr₁ i j)) c).symm
  have hv : ∀ (i j : ι) (c : chartRing B S hS F hF W),
      chartRestrict (hF := hF) (pr₂ i j) (chartRestrict (hF := hF) (g j) c) =
        chartRestrict (hF := hF) (pr₁ i j ≫ g i) c := fun i j c ↦
    chartRestrict_chartRestrict_eq_of_comp_eq (hpq i j) c
  let l : ∀ i j, chartRing B S hS F hF (Y i) →ₐ[chartRing B S hS F hF W]
      chartRing B S hS F hF (Pb i j) := fun i j ↦
    AlgHom.mk (chartRestrict (hF := hF) (pr₁ i j)) (hu i j)
  let r : ∀ i j, chartRing B S hS F hF (Y j) →ₐ[chartRing B S hS F hF W]
      chartRing B S hS F hF (Pb i j) := fun i j ↦
    AlgHom.mk (chartRestrict (hF := hF) (pr₂ i j)) (hv i j)
  obtain ⟨eP, heP⟩ : ∃ eP : ∀ i j, TensorProduct (chartRing B S hS F hF W)
      (chartRing B S hS F hF (Y i)) (chartRing B S hS F hF (Y j))
        ≃ₗ[chartRing B S hS F hF W] chartRing B S hS F hF (Pb i j),
      ∀ i j x y, eP i j (TensorProduct.tmul _ x y) = l i j x * r i j y := by
    choose e he using fun (i j : ι) ↦ SmallEtale.exists_tensorEquiv_chartRing_of_isPullback
      (hF := hF) (hpb i j) hW (hY i) (hY j)
    exact ⟨e, fun i j x y ↦ he i j x y⟩
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ∀ i, TensorProduct (chartRing B S hS F hF W)
      (chartRing B S hS F hF (Y i)) (C.obj (op W)) ≃ₗ[chartRing B S hS F hF (Y i)]
        (C.obj (op (Y i)) : Type u),
      ∀ i n, e₁ i (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Y i)) n) =
        C.restrictₛₗ (g i).op n := by
    choose e he using fun i ↦ exists_baseChangeEquiv_sections_of_isPresheafCokernel a π hπ (g i)
      (hK W (Y i) hW (hY i) (g i)) (hP W (Y i) hW (hY i) (g i))
    exact ⟨e, he⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : ∀ i j, TensorProduct (chartRing B S hS F hF W)
      (chartRing B S hS F hF (Pb i j)) (C.obj (op W)) ≃ₗ[chartRing B S hS F hF (Pb i j)]
        (C.obj (op (Pb i j)) : Type u),
      ∀ i j n, e₂ i j (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Pb i j)) n) =
        C.restrictₛₗ (pr₁ i j ≫ g i).op n := by
    choose e he using fun (i j : ι) ↦
      exists_baseChangeEquiv_sections_of_isPresheafCokernel a π hπ (pr₁ i j ≫ g i)
        (hK W (Pb i j) hW (hPbaff i j) (pr₁ i j ≫ g i))
        (hP W (Pb i j) hW (hPbaff i j) (pr₁ i j ≫ g i))
    exact ⟨e, fun i j n ↦ he i j n⟩
  have he₂₁ : ∀ (i j : ι) (n : C.obj (op W)),
      e₂ i j (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Pb i j)) n) =
        C.restrictₛₗ (pr₁ i j).op (C.restrictₛₗ (g i).op n) := fun i j n ↦
    (he₂ i j n).trans (C.map_comp_apply (g i).op (pr₁ i j).op n)
  have he₂₂ : ∀ (i j : ι) (n : C.obj (op W)),
      e₂ i j (TensorProduct.tmul _ (1 : chartRing B S hS F hF (Pb i j)) n) =
        C.restrictₛₗ (pr₂ i j).op (C.restrictₛₗ (g j).op n) := fun i j n ↦
    (he₂ i j n).trans (by
      rw [show (pr₁ i j ≫ g i).op = (g j).op ≫ (pr₂ i j).op from
        congrArg Quiver.Hom.op (hpq i j)]
      exact C.map_comp_apply (g j).op (pr₂ i j).op n)
  refine Stacks.Sites.isSheafFor_of_finite_tensor_descent _ Y g Pb pr₁ pr₂ hpq
    (chartRing B S hS F hF W) (fun i ↦ chartRing B S hS F hF (Y i))
    (fun i j ↦ chartRing B S hS F hF (Pb i j)) (C.obj (op W)) eP l r heP (Equiv.refl _)
    (fun i ↦ (e₁ i).toEquiv) (fun i j ↦ (e₂ i j).toEquiv) (fun i n ↦ (he₁ i n).symm)
    (fun i j x ↦ ?_) (fun i j x ↦ ?_)
  · exact semilinear_tensorEquiv_eq_map (l i j) (C.restrictₛₗ (pr₁ i j).op) (e₁ i) (e₂ i j)
      (fun n ↦ (congrArg _ (he₁ i n)).trans (he₂₁ i j n).symm) x
  · exact semilinear_tensorEquiv_eq_map (r i j) (C.restrictₛₗ (pr₂ i j).op) (e₁ j) (e₂ i j)
      (fun n ↦ (congrArg _ (he₁ j n)).trans (he₂₂ i j n).symm) x


/-! ### Separatedness of the presheaf quotient over an affine chart -/

/-- **A presheaf quotient of `𝒪_F`-modules cartesian on affine charts is separated for every
covering sieve of an affine étale chart.**

A covering sieve of an affine chart contains a finite family of affine charts which is still
covering and is étale, hence flat, in schemes
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`); the sheaf
condition for that family is
`AlgebraicGeometry.Space.isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian`, and
separatedness for a sieve follows from separatedness for one family of its arrows. -/
theorem isSeparatedFor_of_isPresheafCokernel_of_cartesian
    {K P : Modules.{u, u} B S hS F hF}
    {C : PresheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj}
    (a : K ⟶ P) (π : P.val ⟶ C) (hπ : PresheafOfModules.IsPresheafCokernel a.val π)
    (hK : IsCartesianOnAffineCharts K) (hP : IsCartesianOnAffineCharts P)
    (Z : SmallEtale B S hS F)
    (hZ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Z))
    (T : Sieve Z) (hT : T ∈ SmallEtale.topology B S hS F Z) :
    Presieve.IsSeparatedFor (C.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u})
      (T : Presieve Z) := by
  obtain ⟨k, V, φ, hVaff, hmem, hcov, het⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hZ hT
  exact Presheaf.isSeparatedFor_of_exists_isSeparatedFor_le _ T φ hmem
    (isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian a π hπ hK hP hZ V φ hVaff
      (Scheme.etalePrecoverage_le_fppfPrecoverage _ het)).isSeparatedFor

/-- **The chosen fibre product of two affine étale charts over an affine étale chart is
affine.**  This is `AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback_charts` at the
chosen fibre product of the site, which is the form the separatedness side of the surjectivity
criterion asks for: the pairwise fibre products of a covering family of affine charts are again
affine, so nothing is ever asked of the presheaf quotient at a non-affine chart. -/
theorem SmallEtale.isAffine_pullback_charts {W Y Z : SmallEtale B S hS F} (f : Y ⟶ W) (g : Z ⟶ W)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hY : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Y))
    (hZ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj Z)) :
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
      (CategoryTheory.Limits.pullback f g)) :=
  SmallEtale.isAffine_of_isPullback_charts (IsPullback.of_hasPullback f g) hW hY hZ

/-- **The arrows along which a section of the target of an epimorphism of `𝒪_F`-modules lifts
form a covering sieve of the chart it lives over.**

This is `CategoryTheory.Presheaf.imageSieve_mem` for the local surjectivity of an epimorphism of
sheaves of modules
(`Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi`), restated for the topology
`AlgebraicGeometry.Space.SmallEtale.topology` and for a chart of
`AlgebraicGeometry.Space.SmallEtale`, rather than for the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite` which the sheaves of modules are indexed by.  The
two are the same topology on the same category, by `rfl`; what the restatement does is cross
between the two spellings once, here, instead of inside the proof that consumes it. -/
theorem mem_topology_imageSieve_of_epi
    {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q) [Epi q] (W : SmallEtale B S hS F)
    (n : Q.val.obj (op W)) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj).map
          q.val) n ∈
      SmallEtale.topology B S hS F W := by
  have hsf : HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u})
  have hwb : (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{u})
  have hls := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi
    (J := (smallEtaleRingedSite B S hS F hF).J) q
  exact Presheaf.imageSieve_mem (smallEtaleRingedSite B S hS F hF).J
    ((PresheafOfModules.toPresheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj).map
        q.val) (U := op W) n

/-- **A section of the target of an epimorphism of `𝒪_F`-modules lifts over the members of a
finite covering family of affine charts of an affine chart which is flat in schemes.**

An epimorphism of sheaves of modules is locally surjective, so the arrows along which a given
section of the target restricts into the image form a covering sieve of the chart it lives over
(`AlgebraicGeometry.Space.mem_topology_imageSieve_of_epi`); over an affine chart that sieve
contains a finite covering family of affine charts which is étale, hence flat, in schemes
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`). -/
theorem exists_finite_affine_ofArrows_lift_of_epi
    {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q) [Epi q] (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (n : Q.val.obj (op W)) :
    ∃ (k : ℕ) (Z : Fin k → SmallEtale B S hS F) (φ : ∀ i, Z i ⟶ W),
      (∀ i, IsAffine
        ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Z i))) ∧
        Sieve.ofArrows Z φ ∈ SmallEtale.topology B S hS F W ∧
        Presieve.ofArrows
            (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (Z i))
            (fun i ↦ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (φ i)) ∈
          Scheme.fppfPrecoverage
            ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) ∧
        ∀ i, ∃ s : P.val.obj (op (Z i)),
          q.val.app (op (Z i)) s = Q.val.map (φ i).op n := by
  obtain ⟨k, Z, φ, hZaff, hφS, hφcov, hφet⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hW
      (mem_topology_imageSieve_of_epi q W n)
  exact ⟨k, Z, φ, hZaff, hφcov,
    Scheme.etalePrecoverage_le_fppfPrecoverage _ hφet, fun i ↦ hφS i⟩

/-- **A section of the target of an epimorphism of `𝒪_F`-modules which is a value of it over a
chart is a value of the morphism out of the presheaf quotient there.**  The projection onto a
cokernel of presheaves of modules is surjective on the sections over every object, and composing
it with the morphism out of that cokernel gives the morphism itself
(`SheafOfModules.cokernelDesc_app_π_app`). -/
theorem exists_cokernelDesc_app_eq_of_exists_val_app_eq
    {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q)
    (hab' : (kernel.ι q).val ≫ q.val = 0) (X : SmallEtale B S hS F) (m : Q.val.obj (op X))
    (h : ∃ s : P.val.obj (op X), q.val.app (op X) s = m) :
    ∃ t : (cokernel (kernel.ι q).val).obj (op X),
      (cokernel.desc (kernel.ι q).val q.val hab').app (op X) t = m := by
  obtain ⟨s, hs⟩ := h
  exact ⟨(cokernel.π (kernel.ι q).val).app (op X) s,
    (SheafOfModules.cokernelDesc_app_π_app (kernel.ι q) q hab' (op X) s).trans hs⟩

/-! ### Surjectivity on affine-chart sections -/

/-- **An epimorphism of `𝒪_F`-modules whose source and whose kernel are cartesian on affine charts
is surjective on the sections over every affine étale chart.**

This is Descent, Proposition 03DW for the small étale site of an algebraic space, with the one
extra hypothesis that the *source* be cartesian on affine charts.  The argument never touches a
first cohomology group: the quotient of `P` by the kernel of `q` computed in presheaves of modules
is again cartesian on affine charts, by right exactness of the tensor product
(`AlgebraicGeometry.Space.exists_baseChangeEquiv_sections_of_isPresheafCokernel`), hence satisfies
the sheaf condition for the finite affine covering families of an affine chart by degree-zero
descent of modules along a faithfully flat algebra; so it agrees with the sheaf quotient there,
and the sheaf quotient's sections over an affine chart are the quotient of the sections.

The reduction of surjectivity to that sheaf condition is
`SheafOfModules.surjective_val_app_of_forall_exists_isSheafFor_arrows`, whose three remaining
inputs are discharged here: local injectivity of the comparison from the presheaf quotient by
`SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq`, separatedness over the pairwise
fibre products by `AlgebraicGeometry.Space.isSeparatedFor_of_isPresheafCokernel_of_cartesian`
— those fibre products being affine by
`AlgebraicGeometry.Space.SmallEtale.isAffine_of_isPullback_charts` — and the lifts of a section
over the members of a covering family by local surjectivity of an epimorphism of sheaves of
modules.

No `@[stacks]` attribute is claimed.  Stacks 03DW is the comparison of the cohomology of a
quasi-coherent module computed in several topologies and in all degrees, of which this is the
degree-zero surjectivity statement for the small étale site, and the hypothesis on the source is
not in the source. -/
theorem surjective_val_app_of_epi_of_cartesian
    {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q) [Epi q]
    (hP : IsCartesianOnAffineCharts P)
    (hker : IsCartesianOnAffineCharts (kernel q))
    (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (q.val.app (op W)) := by
  have hab' : (kernel.ι q).val ≫ q.val = 0 := by
    rw [← SheafOfModules.comp_val, kernel.condition q]
    rfl
  have hπ := PresheafOfModules.isPresheafCokernel_cokernelπ (kernel.ι q).val
  have hpb : HasPullbacks (smallEtaleRingedSite B S hS F hF).C :=
    SmallEtale.instHasPullbacks B S hS F
  refine SheafOfModules.surjective_val_app_of_forall_exists_isSheafFor_arrows (kernel.ι q) q hab'
    (fun Z s t hst => SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq
      (kernel.ι q) q _ (Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι q) (kernel.condition q)) (kernelIsKernel q)) hab' Z s t hst)
    fun n => ?_
  obtain ⟨k, Z, φ, hZaff, hφcov, hφppf, hlift⟩ :=
    exists_finite_affine_ofArrows_lift_of_epi q W hW n
  exact ⟨Fin k, Z, φ, ⟨fun _ _ ↦ have := hpb; inferInstance⟩,
    isSheafFor_ofArrows_of_isPresheafCokernel_of_cartesian (kernel.ι q)
      (cokernel.π (kernel.ι q).val) hπ hker hP hW Z φ hZaff hφppf,
    hφcov, (fun i j T hT => isSeparatedFor_of_isPresheafCokernel_of_cartesian (kernel.ι q)
      (cokernel.π (kernel.ι q).val) hπ hker hP _
      (SmallEtale.isAffine_pullback_charts (φ i) (φ j) hW (hZaff i) (hZaff j)) T hT),
    fun i ↦ exists_cokernelDesc_app_eq_of_exists_val_app_eq q hab' (Z i) _ (hlift i)⟩

end AlgebraicGeometry.Space

end
